from __future__ import annotations

from dataclasses import dataclass
from json import dumps, loads
from math import cos, isfinite, pi, sin, sqrt
import os
from random import Random
from secrets import randbelow #for multiplayer room code generation
import socket
import threading
from time import monotonic
from uuid import uuid4

import pygame

from VPYrender import (
	Mesh,
	HybridRenderer,
	Renderer,
	Scene,
	SceneObject,
	look_at,
	multiply,
	perspective,
	scale,
	translation,
)


OUTPUT_SIZE = (720, 480)
HUD_SIZE = (960, 540)
RENDER_SIZE = (270, 140)
MAGAZINE_SIZE = 12
ARENA_LIMIT = 9.0
MOUSE_SENSITIVITY = 0.0022

BOX_INDICES = (
	0, 2, 1, 0, 3, 2,
	4, 5, 6, 4, 6, 7,
	0, 1, 5, 0, 5, 4,
	3, 7, 6, 3, 6, 2,
	0, 4, 7, 0, 7, 3,
	1, 2, 6, 1, 6, 5,
)

BOX_MESHES: dict[tuple[int, int, int], Mesh] = {}
Crate = tuple[float, float, float, float, float]


@dataclass
class Target:
	base_x: float
	base_z: float
	phase: float
	x: float
	z: float
	alive: bool = True
	respawn_timer: float = 0.0


@dataclass(frozen=True)
class LanPlayer:
	player_id: str
	name: str
	x: float
	y: float
	z: float
	yaw: float


class LanSession:
	PORT = 27815

	def __init__(self, hosting: bool, room_code: str = "") -> None:
		self.hosting = hosting
		self.room_code = f"{randbelow(10_000):04d}" if hosting else ""
		self.player_id = uuid4().hex[:8]
		self.name = socket.gethostname()[:16] or "Player"
		self.address = ""
		spawn_x, spawn_z, spawn_yaw = (0.0, 9.0, 0.0) if hosting else (0.0, 7.0, pi)
		self._local_state = {"id": self.player_id, "name": self.name, "x": spawn_x, "y": 0.0, "z": spawn_z, "yaw": spawn_yaw}
		self._players: tuple[LanPlayer, ...] = ()
		self._blocks: tuple[tuple[float, float, float, float], ...] = ()
		self._outgoing_blocks: tuple[tuple[float, float, float, float], ...] = ()
		self._pending_blocks: tuple[tuple[float, float, float, float], ...] | None = None
		self._blocks_revision = 0
		self._applied_blocks_revision = 0
		self._peers: dict[tuple[str, int], tuple[dict[str, object], float]] = {}
		self._lock = threading.Lock()
		self._stopping = threading.Event()
		self._socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
		if hosting:
			self._socket.bind(("0.0.0.0", self.PORT))
			self.address = self._local_address()
		else:
			if len(room_code) != 4 or not room_code.isascii() or not room_code.isdigit():
				self._socket.close()
				raise OSError("Enter a 4-digit room code")
			try:
				self._socket.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
				self._socket.settimeout(0.5)
				discovery = dumps({"type": "discover", "code": room_code}, separators=(",", ":")).encode("utf-8")
				broadcast_addresses = ["255.255.255.255"]
				try:
					local_addresses = socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET, socket.SOCK_DGRAM)
				except OSError:
					local_addresses = ()
				for address_info in local_addresses:
					local_ip = address_info[4][0]
					octets = local_ip.split(".")
					if len(octets) == 4 and not local_ip.startswith(("127.", "169.254.")):
						directed_broadcast = ".".join((*octets[:3], "255"))
						if directed_broadcast not in broadcast_addresses:
							broadcast_addresses.append(directed_broadcast)
				for _ in range(5):
					for broadcast_address in broadcast_addresses:
						self._socket.sendto(discovery, (broadcast_address, self.PORT))
					try:
						payload, endpoint = self._socket.recvfrom(8192)
					except socket.timeout:
						continue
					try:
						response = loads(payload.decode("utf-8"))
					except ValueError:
						continue
					if (
						isinstance(response, dict)
						and response.get("code") == room_code
						and isinstance(response.get("players"), list)
					):
						self.address = endpoint[0]
						break
				else:
					self._socket.close()
					raise OSError("No party found; check same LAN and UDP 27815 firewall")
			except OSError:
				self._socket.close()
				raise
		self._socket.settimeout(0.05)
		self._thread = threading.Thread(target=self._run, daemon=True)
		self._thread.start()

	@staticmethod
	def _local_address() -> str:
		try:
			return socket.gethostbyname(socket.gethostname())
		except OSError:
			return "<LAN IP>"

	@staticmethod
	def _decode_player(value: object) -> LanPlayer | None:
		if not isinstance(value, dict):
			return None
		try:
			player_id = str(value["id"])[:16]
			name = str(value["name"])[:16] or "Player"
			x, y, z, yaw = (float(value[key]) for key in ("x", "y", "z", "yaw"))
		except (KeyError, TypeError, ValueError):
			return None
		if not player_id or not all(isfinite(item) and abs(item) <= 100 for item in (x, y, z, yaw)):
			return None
		return LanPlayer(player_id, name, x, y, z, yaw)

	@staticmethod
	def _decode_blocks(value: object) -> tuple[tuple[float, float, float, float], ...] | None:
		if not isinstance(value, list) or len(value) != 3:
			return None
		try:
			blocks = tuple(tuple(float(item) for item in block) for block in value)
		except (TypeError, ValueError):
			return None
		if any(
			len(block) != 4 or not all(isfinite(item) and abs(item) <= 100 for item in block)
			for block in blocks
		):
			return None
		return blocks

	def set_local_state(self, x: float, y: float, z: float, yaw: float) -> None:
		with self._lock:
			self._local_state.update(x=x, y=y, z=z, yaw=yaw)

	def set_blocks(self, blocks: tuple[tuple[float, float, float, float], ...]) -> None:
		with self._lock:
			if self.hosting:
				self._blocks = blocks
			else:
				self._outgoing_blocks = blocks

	def take_block_update(self) -> tuple[tuple[float, float, float, float], ...] | None:
		with self._lock:
			if self.hosting:
				blocks = self._pending_blocks
				self._pending_blocks = None
				return blocks
			if self._blocks_revision == self._applied_blocks_revision:
				return None
			self._applied_blocks_revision = self._blocks_revision
			return self._blocks

	@property
	def players(self) -> tuple[LanPlayer, ...]:
		with self._lock:
			return self._players

	def _run(self) -> None:
		server_address = (self.address, self.PORT)
		while not self._stopping.is_set():
			if self.hosting:
				try:
					payload, endpoint = self._socket.recvfrom(2048)
					message = loads(payload.decode("utf-8"))
					if isinstance(message, dict) and message.get("type") == "discover":
						if message.get("code") == self.room_code:
							with self._lock:
								states = [dict(self._local_state)]
							response = dumps(
								{"code": self.room_code, "players": states},
								separators=(",", ":"),
							).encode("utf-8")
							self._socket.sendto(response, endpoint)
						continue
					player = self._decode_player(message)
					if player is not None and player.player_id != self.player_id:
						block_state = self._decode_blocks(message.get("blocks")) if isinstance(message, dict) else None
						with self._lock:
							peer_state = {"id": player.player_id, "name": player.name, "x": player.x, "y": player.y, "z": player.z, "yaw": player.yaw}
							self._peers[endpoint] = (peer_state, monotonic())
							if block_state is not None:
								self._pending_blocks = block_state
				except socket.timeout:
					pass
				except (OSError, ValueError):
					break
				now = monotonic()
				with self._lock:
					self._peers = {endpoint: peer for endpoint, peer in self._peers.items() if now - peer[1] < 5.0}
					states = [dict(self._local_state), *(dict(peer[0]) for peer in self._peers.values())]
					block_state = [list(block) for block in self._blocks]
					endpoints = tuple(self._peers)
					players = tuple(player for state in states if (player := self._decode_player(state)) is not None)
					self._players = tuple(player for player in players if player.player_id != self.player_id)
				packet = dumps({"players": states, "blocks": block_state}, separators=(",", ":")).encode("utf-8")
				for endpoint in endpoints:
					try:
						self._socket.sendto(packet, endpoint)
					except OSError:
						pass
			else:
				try:
					with self._lock:
						local_state = dict(self._local_state)
						local_state["blocks"] = [list(block) for block in self._outgoing_blocks]
					self._socket.sendto(dumps(local_state, separators=(",", ":")).encode("utf-8"), server_address)
					payload, _ = self._socket.recvfrom(8192)
					response = loads(payload.decode("utf-8"))
					states = response.get("players", []) if isinstance(response, dict) else []
					players = tuple(player for state in states if (player := self._decode_player(state)) is not None)
					block_state = self._decode_blocks(response.get("blocks")) if isinstance(response, dict) else None
					with self._lock:
						self._players = tuple(player for player in players if player.player_id != self.player_id)
						if block_state is not None:
							self._blocks = block_state
							self._blocks_revision += 1
				except socket.timeout:
					pass
				except (OSError, ValueError):
					break

	def close(self) -> None:
		self._stopping.set()
		self._socket.close()
		self._thread.join(timeout=0.5)


def choose_party_mode() -> tuple[LanSession | None, bool]:
	os.environ["SDL_VIDEO_WINDOW_POS"] = "0,0"
	pygame.init()
	display_info = pygame.display.Info()
	display_size = (display_info.current_w or 960, display_info.current_h or 540)
	screen = pygame.display.set_mode(display_size, pygame.NOFRAME | pygame.SCALED, vsync=1)
	menu_surface = pygame.Surface((960, 540))
	pygame.display.set_caption("VPY // LAN Party")
	font = pygame.font.SysFont("consolas", 28, bold=True)
	small_font = pygame.font.SysFont("consolas", 18, bold=True)
	clock = pygame.time.Clock()
	joining = False
	room_code = ""
	status = ""
	while True:
		for event in pygame.event.get():
			if event.type == pygame.QUIT:
				pygame.quit()
				return None, True
			if event.type != pygame.KEYDOWN:
				continue
			if event.key == pygame.K_ESCAPE:
				if joining:
					joining = False
					status = ""
				else:
					pygame.quit()
					return None, True
			elif not joining and event.key == pygame.K_h:
				try:
					session = LanSession(hosting=True)
					pygame.quit()
					return session, False
				except OSError as error:
					status = f"Could not start host: {error}"
			elif not joining and event.key == pygame.K_j:
				joining = True
				room_code = ""
				status = "Enter the host's 4-digit room code"
			elif not joining and event.key == pygame.K_s:
				pygame.quit()
				return None, False
			elif joining and event.key == pygame.K_RETURN:
				try:
					session = LanSession(hosting=False, room_code=room_code)
					pygame.quit()
					return session, False
				except OSError as error:
					status = f"FAILED TO CONNECT ({error})"
			elif joining and event.key == pygame.K_BACKSPACE:
				room_code = room_code[:-1]
			elif joining and event.unicode in "0123456789" and len(room_code) < 4:
				room_code += event.unicode

		menu_surface.fill((13, 21, 22))
		pygame.draw.rect(menu_surface, (35, 67, 65), (0, 0, 960, 8))
		draw_text(menu_surface, font, "VPY  /  LAN PARTY", (72, 82), (111, 224, 193))
		if joining:
			draw_text(menu_surface, small_font, "JOIN A PARTY  /  ROOM CODE", (74, 184), (208, 216, 201))
			draw_text(menu_surface, font, room_code + "_", (74, 230), (238, 226, 193))
			draw_text(menu_surface, small_font, "4 DIGITS  /  ENTER JOIN  /  ESC BACK", (74, 286), (146, 166, 158))
		else:
			draw_text(menu_surface, small_font, "H  HOST PARTY", (74, 194), (238, 226, 193))
			draw_text(menu_surface, small_font, "J  JOIN PARTY", (74, 240), (238, 226, 193))
			draw_text(menu_surface, small_font, "S  SOLO PLAY", (74, 286), (238, 226, 193))
			draw_text(menu_surface, small_font, f"HOSTS USE UDP PORT {LanSession.PORT}", (74, 354), (146, 166, 158))
		if status:
			draw_text(menu_surface, small_font, status[:90], (74, 420), (232, 143, 111))
		pygame.transform.scale(menu_surface, screen.get_size(), screen)
		pygame.display.flip()
		clock.tick(30)


def generate_map(randomizer: Random) -> tuple[int, list[Crate], list[Target]]:
	seed = randomizer.randrange(1000, 1_000_000)
	layout_random = Random(seed)
	spawn = (0.0, 7.0)
	target_sites = [
		(x, z)
		for z in (-8.0, -5.0, -2.0, 1.0)
		for x in (-7.0, -3.5, 0.0, 3.5, 7.0)
		if sqrt(x * x + (z - spawn[1]) ** 2) > 4.0
	]
	layout_random.shuffle(target_sites)
	targets = [
		Target(x, z, layout_random.uniform(0.0, 6.28), x, z)
		for x, z in target_sites[:5]
	]

	crate_sites = [
		(x, z)
		for z in (-7.5, -4.5, -1.5, 1.5, 4.5)
		for x in (-6.0, -3.0, 0.0, 3.0, 6.0)
		if sqrt(x * x + (z - spawn[1]) ** 2) > 3.2
		and all(sqrt((x - target.x) ** 2 + (z - target.z) ** 2) > 2.3 for target in targets)
	]
	layout_random.shuffle(crate_sites)
	crates = [
		(
			x,
			z,
			layout_random.choice((0.72, 0.9, 1.05)),
			layout_random.choice((0.72, 0.9, 1.05)),
			layout_random.choice((0.8, 1.0, 1.2)),
		)
		for x, z in crate_sites[:8]
	]
	return seed, crates, targets


def box_mesh(color: tuple[int, int, int]) -> Mesh:
	mesh = BOX_MESHES.get(color)
	if mesh is not None:
		return mesh

	red, green, blue = (component / 255.0 for component in color)
	positions = (
		(-1, -1, -1), (1, -1, -1), (1, 1, -1), (-1, 1, -1),
		(-1, -1, 1), (1, -1, 1), (1, 1, 1), (-1, 1, 1),
	)
	vertices = tuple(
		component
		for position in positions
		for component in (*position, red, green, blue)
	)
	mesh = Mesh(vertices, BOX_INDICES)
	BOX_MESHES[color] = mesh
	return mesh


def make_floor() -> Mesh:
	vertices = (
		-10, 0, -12, 0.21, 0.25, 0.26,
		 10, 0, -12, 0.21, 0.25, 0.26,
		 10, 0,  10, 0.16, 0.20, 0.21,
		-10, 0,  10, 0.16, 0.20, 0.21,
	)
	return Mesh(vertices, (0, 2, 1, 0, 3, 2))


def add_box(
	objects: list[SceneObject],
	color: tuple[int, int, int],
	center: tuple[float, float, float],
	half_size: tuple[float, float, float],
) -> None:
	model = multiply(translation(*center), scale(*half_size))
	objects.append(SceneObject(box_mesh(color), model))


def make_scene(targets: list[Target], crates: list[Crate]) -> Scene:
	objects = [SceneObject(make_floor(), translation(0, 0, 0))]
	wall_color = (62, 76, 77)
	trim_color = (185, 129, 69)
	crate_color = (104, 91, 69)

	add_box(objects, wall_color, (-9.5, 1.5, -1.0), (0.5, 1.5, 11.0))
	add_box(objects, wall_color, (9.5, 1.5, -1.0), (0.5, 1.5, 11.0))
	add_box(objects, wall_color, (0, 1.5, -11.5), (10.0, 1.5, 0.5))
	add_box(objects, trim_color, (0, 0.15, -11.0), (9.0, 0.12, 0.12))

	for center_x, center_z, half_x, half_z, height in crates:
		add_box(objects, crate_color, (center_x, height, center_z), (half_x, height, half_z))
		add_box(objects, trim_color, (center_x, height * 1.35, center_z), (half_x * 0.72, 0.08, half_z * 0.72))

	for target in targets:
		if not target.alive:
			continue
		uniform_color = (50, 160, 151)
		armor_color = (75, 104, 108)
		add_box(objects, armor_color, (target.x, 0.92, target.z), (0.38, 0.56, 0.27))
		add_box(objects, uniform_color, (target.x, 1.62, target.z), (0.26, 0.26, 0.26))
		add_box(objects, armor_color, (target.x, 1.04, target.z), (0.56, 0.14, 0.18))
		add_box(objects, (43, 53, 55), (target.x, 0.31, target.z), (0.33, 0.31, 0.25))

	return Scene(tuple(objects))


def ray_box_distance(
	origin: tuple[float, float, float],
	direction: tuple[float, float, float],
	minimum: tuple[float, float, float],
	maximum: tuple[float, float, float],
) -> float | None:
	near_distance = 0.0
	fare_distance = float("inf")
	for axis in range(3):
		if abs(direction[axis]) < 1e-8:
			if origin[axis] < minimum[axis] or origin[axis] > maximum[axis]:
				return None
			continue
		first = (minimum[axis] - origin[axis]) / direction[axis]
		second = (maximum[axis] - origin[axis]) / direction[axis]
		near_distance = max(near_distance, min(first, second))
		fare_distance = min(fare_distance, max(first, second))
		if near_distance > fare_distance:
			return None
	return near_distance if fare_distance >= 0 else None


def draw_text(
	screen: pygame.Surface,
	font: pygame.font.Font,
	label: str,
	position: tuple[int, int],
	color: tuple[int, int, int] = (224, 232, 226),
) -> None:
	screen.blit(font.render(label, True, color), position)


def draw_hud(
	screen: pygame.Surface,
	font: pygame.font.Font,
	small_font: pygame.font.Font,
	player_x: float,
	player_z: float,
	targets: list[Target],
	map_seed: int,
	ammo: int,
	reserve: int,
	kills: int,
	streak: int,
	reload_timer: float,
	hitmarker_timer: float,
	muzzle_timer: float,
	recoil: float,
	paused: bool,
) -> None:
	width, height = screen.get_size()
	center_x, center_y = width // 2, height // 2

	pygame.draw.rect(screen, (12, 18, 19), (24, 22, 176, 62), border_radius=3)
	pygame.draw.rect(screen, (70, 94, 86), (24, 22, 176, 62), 1, border_radius=3)
	draw_text(screen, small_font, "RANGE  /  LIVE FIRE", (36, 30), (197, 157, 99))
	draw_text(screen, font, f"ELIMS  {kills:03d}", (36, 49))
	draw_text(screen, small_font, f"MAP {map_seed:06d}  /  N NEW", (36, 70), (153, 170, 160))
	if streak >= 3:
		draw_text(screen, small_font, f"STREAK x{streak}", (125, 56), (236, 190, 114))

	map_rect = pygame.Rect(width - 148, 22, 124, 108)
	pygame.draw.rect(screen, (12, 18, 19), map_rect, border_radius=3)
	pygame.draw.rect(screen, (70, 94, 86), map_rect, 1, border_radius=3)
	draw_text(screen, small_font, "RADAR", (map_rect.x + 9, map_rect.y + 6), (197, 157, 99))
	for target in targets:
		if target.alive:
			dot_x = int(map_rect.centerx + target.x * 5.2)
			dot_y = int(map_rect.centery + target.z * 3.5 + 8)
			pygame.draw.circle(screen, (222, 103, 76), (dot_x, dot_y), 3)
	player_dot = (int(map_rect.centerx + player_x * 5.2), int(map_rect.centery + player_z * 3.5 + 8))
	pygame.draw.circle(screen, (106, 205, 171), player_dot, 4)

	weapon_y = height - 130 + int(recoil * 30)
	pygame.draw.polygon(screen, (36, 47, 48), ((width - 255, weapon_y + 76), (width - 138, weapon_y + 53), (width - 42, height + 25), (width - 258, height + 25)))
	pygame.draw.polygon(screen, (116, 127, 116), ((width - 212, weapon_y + 48), (width - 129, weapon_y + 43), (width - 79, weapon_y + 85), (width - 232, weapon_y + 90)))
	pygame.draw.polygon(screen, (58, 69, 65), ((width - 184, weapon_y + 76), (width - 115, weapon_y + 69), (width - 108, height + 10), (width - 181, height + 10)))
	pygame.draw.rect(screen, (29, 37, 37), (width - 116, weapon_y + 52, 105, 17), border_radius=3)
	pygame.draw.line(screen, (185, 129, 69), (width - 196, weapon_y + 47), (width - 125, weapon_y + 44), 2)

	panel = pygame.Rect(24, height - 91, 230, 67)
	pygame.draw.rect(screen, (12, 18, 19), panel, border_radius=3)
	pygame.draw.rect(screen, (70, 94, 86), panel, 1, border_radius=3)
	if reload_timer > 0:
		draw_text(screen, small_font, "RELOADING", (38, height - 79), (236, 190, 114))
	else:
		draw_text(screen, small_font, "9MM  /  SEMI-AUTO", (38, height - 79), (197, 157, 99))
	draw_text(screen, font, f"{ammo:02d}  /  {reserve:02d}", (38, height - 57))
	draw_text(screen, small_font, "R  RELOAD", (145, height - 54), (153, 170, 160))
	draw_text(screen, small_font, "WASD MOVE   SHIFT SPRINT   CTRL CROUCH", (280, height - 34), (169, 183, 175))

	cross_color = (233, 228, 207)
	if hitmarker_timer > 0:
		cross_color = (245, 177, 106)
	for offset in (-1, 1):
		pygame.draw.line(screen, cross_color, (center_x + offset * 10, center_y), (center_x + offset * 17, center_y), 2)
		pygame.draw.line(screen, cross_color, (center_x, center_y + offset * 10), (center_x, center_y + offset * 17), 2)
	pygame.draw.circle(screen, cross_color, (center_x, center_y), 2)
	if hitmarker_timer > 0:
		for direction_x, direction_y in ((-1, -1), (1, -1), (-1, 1), (1, 1)):
			pygame.draw.line(screen, (247, 222, 181), (center_x + direction_x * 7, center_y + direction_y * 7), (center_x + direction_x * 12, center_y + direction_y * 12), 2)
	if muzzle_timer > 0:
		pygame.draw.polygon(screen, (255, 203, 115), ((width - 62, weapon_y + 55), (width - 44, weapon_y + 13), (width - 33, weapon_y + 54), (width - 8, weapon_y + 38), (width - 23, weapon_y + 75)))

	if paused:
		shade = pygame.Surface((width, height), pygame.SRCALPHA)
		shade.fill((4, 8, 9, 190))
		screen.blit(shade, (0, 0))
		draw_text(screen, font, "PAUSED", (center_x - 39, center_y - 28), (238, 223, 192))
		draw_text(screen, small_font, "CLICK TO RESUME  /  ESC TO QUIT", (center_x - 117, center_y + 7), (183, 196, 186))


def main() -> None:
	os.environ["SDL_VIDEO_WINDOW_POS"] = "0,0"
	pygame.init()
	display_info = pygame.display.Info()
	desktop_width = display_info.current_w or OUTPUT_SIZE[0]
	desktop_height = display_info.current_h or OUTPUT_SIZE[1]
	window_size = (desktop_width, desktop_height)
	hybrid_renderer: HybridRenderer | None = None
	software_renderer: Renderer | None = None
	frame_surface: pygame.Surface | None = None
	try:
		screen = pygame.display.set_mode(window_size, pygame.OPENGL | pygame.DOUBLEBUF | pygame.NOFRAME, vsync=1)
		hybrid_renderer = HybridRenderer(window_size, window_size, backend="auto")
	except (ImportError, pygame.error, RuntimeError):
		pygame.display.quit()
		pygame.display.init()
		screen = pygame.display.set_mode(window_size, pygame.NOFRAME | pygame.SCALED, vsync=1)
		software_renderer = Renderer(RENDER_SIZE)
		frame_surface = pygame.image.frombuffer(software_renderer.pixels, RENDER_SIZE, "RGB")
	pygame.display.set_caption("VPY // Live Fire")
	clock = pygame.time.Clock()
	font = pygame.font.SysFont("consolas", 20, bold=True)
	small_font = pygame.font.SysFont("consolas", 12, bold=True)
	hud_surface = pygame.Surface(HUD_SIZE, pygame.SRCALPHA)
	scaled_hud_surface = pygame.Surface(window_size, pygame.SRCALPHA)
	randomizer = Random()
	map_seed, crates, targets = generate_map(randomizer)

	player_x, player_z = 0.0, 7.0
	yaw, pitch = 0.0, -0.02
	ammo, reserve = MAGAZINE_SIZE, 60
	kills = streak = 0
	reload_timer = shot_cooldown = hitmarker_timer = muzzle_timer = recoil = 0.0
	paused = False
	running = True
	pygame.event.set_grab(True)
	pygame.mouse.set_visible(False)

	try:
		while running:
			delta = min(clock.tick(60) / 1000.0, 0.05)
			shot_cooldown = max(0.0, shot_cooldown - delta)
			hitmarker_timer = max(0.0, hitmarker_timer - delta)
			muzzle_timer = max(0.0, muzzle_timer - delta)
			recoil = max(0.0, recoil - delta * 4.5)

			for event in pygame.event.get():
				if event.type == pygame.QUIT:
					running = False
				elif event.type == pygame.KEYDOWN:
					if event.key == pygame.K_ESCAPE:
						running = False
					elif event.key == pygame.K_TAB:
						paused = not paused
						pygame.event.set_grab(not paused)
						pygame.mouse.set_visible(paused)
					elif event.key == pygame.K_n and not paused:
						map_seed, crates, targets = generate_map(randomizer)
						player_x, player_z = 0.0, 7.0
						yaw, pitch = 0.0, -0.02
						ammo, reserve = MAGAZINE_SIZE, 60
						kills = streak = 0
						reload_timer = hitmarker_timer = muzzle_timer = 0.0
					elif event.key == pygame.K_r and not paused and reload_timer <= 0 and ammo < MAGAZINE_SIZE and reserve > 0:
						reload_timer = 1.15
				elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
					if paused:
						paused = False
						pygame.event.set_grab(True)
						pygame.mouse.set_visible(False)
					elif reload_timer <= 0 and shot_cooldown <= 0:
						shot_cooldown = 0.19
						muzzle_timer = 0.07
						recoil = 1.0
						if ammo > 0:
							ammo -= 1
							direction = (
								sin(yaw) * cos(pitch),
								sin(pitch),
								-cos(yaw) * cos(pitch),
							)
							origin = (player_x, 1.58, player_z)
							cover_distance = float("inf")
							for center_x, center_z, half_x, half_z, height in crates:
								obstacle_distance = ray_box_distance(
									origin,
									direction,
									(center_x - half_x, 0.0, center_z - half_z),
									(center_x + half_x, height * 2.0, center_z + half_z),
								)
								if obstacle_distance is not None:
									cover_distance = min(cover_distance, obstacle_distance)

							nearest_target: Target | None = None
							nearest_distance = float("inf")
							for target in targets:
								if not target.alive:
									continue
								target_distance = ray_box_distance(
									origin,
									direction,
									(target.x - 0.42, 0.08, target.z - 0.33),
									(target.x + 0.42, 2.08, target.z + 0.33),
								)
								if target_distance is not None and target_distance < nearest_distance:
									nearest_distance = target_distance
									nearest_target = target

							if nearest_target is not None and nearest_distance < cover_distance and nearest_distance < 35.0:
								hitmarker_timer = 0.18
								hit_height = origin[1] + direction[1] * nearest_distance
								if hit_height > 1.38:
									streak += 1
								else:
									streak = 0
								kills += 1
								nearest_target.alive = False
								nearest_target.respawn_timer = 2.0
						elif reserve > 0:
							reload_timer = 1.15
				elif event.type == pygame.MOUSEMOTION and not paused:
					yaw += event.rel[0] * MOUSE_SENSITIVITY
					pitch = max(-0.82, min(0.82, pitch - event.rel[1] * MOUSE_SENSITIVITY))

			if not paused:
				keys = pygame.key.get_pressed()
				forward_x, forward_z = sin(yaw), -cos(yaw)
				right_x, right_z = cos(yaw), sin(yaw)
				move_x = (float(keys[pygame.K_d]) - float(keys[pygame.K_a])) * right_x
				move_z = (float(keys[pygame.K_d]) - float(keys[pygame.K_a])) * right_z
				move_x += (float(keys[pygame.K_w]) - float(keys[pygame.K_s])) * forward_x
				move_z += (float(keys[pygame.K_w]) - float(keys[pygame.K_s])) * forward_z
				move_length = sqrt(move_x * move_x + move_z * move_z)
				if move_length > 0:
					speed = 3.5 if keys[pygame.K_LCTRL] else (7.1 if keys[pygame.K_LSHIFT] else 5.0)
					move_x = move_x / move_length * speed * delta
					move_z = move_z / move_length * speed * delta
					for axis in (0, 1):
						candidate_x = player_x + move_x if axis == 0 else player_x
						candidate_z = player_z + move_z if axis == 1 else player_z
						blocked = abs(candidate_x) > ARENA_LIMIT - 0.35 or candidate_z < -10.8 or candidate_z > 9.4
						for center_x, center_z, half_x, half_z, _ in crates:
							if abs(candidate_x - center_x) < half_x + 0.36 and abs(candidate_z - center_z) < half_z + 0.36:
								blocked = True
								break
						if not blocked:
							player_x, player_z = candidate_x, candidate_z

				for target in targets:
					if target.alive:
						target.phase += delta * 0.85
						target.x = target.base_x + sin(target.phase) * 0.72
						target.z = target.base_z + cos(target.phase * 0.7) * 0.32
					elif target.respawn_timer > 0:
						target.respawn_timer -= delta
						if target.respawn_timer <= 0:
							target.x = target.base_x + randomizer.uniform(-0.35, 0.35)
							target.z = target.base_z
							target.alive = True

				if reload_timer > 0:
					reload_timer -= delta
					if reload_timer <= 0:
						loaded = min(MAGAZINE_SIZE - ammo, reserve)
						ammo += loaded
						reserve -= loaded

			keys = pygame.key.get_pressed()
			eye_height = 1.12 if keys[pygame.K_LCTRL] and not paused else 1.58
			look_direction = (
				sin(yaw) * cos(pitch),
				sin(pitch),
				-cos(yaw) * cos(pitch),
			)
			eye = (player_x, eye_height, player_z)
			view = look_at(eye, tuple(eye[index] + look_direction[index] for index in range(3)))
			projection = perspective(1.05, window_size[0] / window_size[1], 0.1, 50.0)
			view_projection = multiply(projection, view)
			scene = make_scene(targets, crates)
			hud_surface.fill((0, 0, 0, 0))

			draw_hud(
				hud_surface, font, small_font, player_x, player_z, targets, map_seed,
				ammo, reserve, kills, streak, reload_timer, hitmarker_timer,
				muzzle_timer, recoil, paused,
			)
			pygame.transform.scale(hud_surface, window_size, scaled_hud_surface)
			if hybrid_renderer is not None:
				overlay = pygame.image.tobytes(scaled_hud_surface, "RGBA", True)
				hybrid_renderer.render_all(scene, view_projection, "Vertex", (overlay, window_size, (0, 0)))
			else:
				assert software_renderer is not None and frame_surface is not None
				software_renderer.render_all(scene, view_projection, "Vertex")
				screen.blit(pygame.transform.scale(frame_surface, window_size), (0, 0))
				screen.blit(scaled_hud_surface, (0, 0))
			pygame.display.flip()
	finally:
		pygame.event.set_grab(False)
		pygame.mouse.set_visible(True)
		pygame.quit()


@dataclass
class PuzzleBlock:
	x: float
	z: float
	color: tuple[int, int, int]
	half_size: float = 0.58
	y: float = 0.0
	vertical_velocity: float = 0.0


@dataclass(frozen=True)
class LevelLayout:
	name: str
	walls: tuple[tuple[float, float, float, float, float, tuple[int, int, int]], ...]
	boxes: tuple[tuple[float, float, float, float, float, tuple[int, int, int]], ...]
	platforms: tuple[tuple[float, float, float, float, float], ...]
	pads: tuple[tuple[float, float, float], tuple[float, float, float], tuple[float, float, float]]
	block_starts: tuple[tuple[float, float], tuple[float, float], tuple[float, float]]


LEVEL_BOUNDS = (8.0, -16.0, 10.0)
LEVEL_NAMES = (
	"Vector Lab", "Voxel Run", "Prism Fork", "Phase Maze", "Core Relay",
	"Quantum Hall", "Tesseract", "Neon Circuit", "Singularity",
)
GAP_PATTERNS = (
	(1, -1, 1), (-1, 1, -1), (1, 1, -1), (-1, -1, 1),
	(1, -1, -1), (-1, 1, 1), (1, 1, 1), (-1, -1, -1), (1, -1, 1),
)
PAD_Z = (0.8, -4.6, -9.7)
INITIAL_BLOCKS = ((-2.0, 7.0), (0.0, 5.6), (2.0, 7.0))
BLOCK_COLORS = ((37, 197, 188), (237, 158, 76), (124, 164, 245))
BLOCK_COLOR_NAMES = ("CYAN", "AMBER", "BLUE")
EXIT_GATE = (0.0, -13.7, 1.3, 0.18)
PLAYER_RADIUS = 0.3
PLAYER_HEIGHT = 1.6


def build_levels() -> tuple[LevelLayout, ...]:
	layouts = []
	barrier_z = (3.4, -2.0, -7.2)
	box_sites = tuple(
		(x, z)
		for z in (7.8, 4.8, 1.0, -2.0, -5.8, -9.0, -11.8)
		for x in (-6.3, -3.2, 0.0, 3.2, 6.3)
	)
	platform_sites = (
		(-5.5, 1.25, 5.7, 1.0, 0.9),
		(5.5, 1.7, 2.0, 1.0, 0.9),
		(-5.4, 2.1, -2.7, 1.0, 0.9),
		(5.4, 2.55, -7.5, 1.0, 0.9),
		(-3.0, 3.0, -11.5, 1.15, 0.85),
		(3.0, 3.45, -12.6, 1.0, 0.85),
	)
	bonus_obstacles = (
		(0.0, 2.25, 0.85, 0.42, 1.05),
		(0.0, -3.95, 0.85, 0.42, 1.05),
		(0.0, -9.05, 0.85, 0.42, 1.05),
		(-2.6, 1.4, 0.48, 0.72, 0.8),
		(2.6, -5.35, 0.48, 0.72, 0.8),
		(-2.6, -10.2, 0.48, 0.72, 0.8),
	)
	for level_index, pattern in enumerate(GAP_PATTERNS):
		walls = [
			(-4.8 if gap_side > 0 else 4.8, z, 3.2, 0.32, 1.65, (48, 78, 83))
			for gap_side, z in zip(pattern, barrier_z)
		]
		for x, z, half_x, half_z, height in bonus_obstacles[:min(level_index, len(bonus_obstacles))]:
			walls.append((x, z, half_x, half_z, height, (80, 94, 91)))
		pads = [(4.3 * side, 0.0, z) for side, z in zip(pattern, PAD_Z)]
		box_candidates = list(box_sites[level_index:] + box_sites[:level_index])
		boxes = []
		for x, z in box_candidates:
			if any(sqrt((x - start_x) ** 2 + (z - start_z) ** 2) < 1.9 for start_x, start_z in INITIAL_BLOCKS):
				continue
			if any(sqrt((x - pad_x) ** 2 + (z - pad_z) ** 2) < 1.5 for pad_x, _, pad_z in pads):
				continue
			if any(abs(x - wall_x) < 0.65 + wall_half_x and abs(z - wall_z) < 0.65 + wall_half_z for wall_x, wall_z, wall_half_x, wall_half_z, _, _ in walls):
				continue
			boxes.append((x, z, 0.42, 0.42, 0.9 + (level_index % 3) * 0.12, (78, 91, 89)))
			if len(boxes) >= level_index + 2:
				break
		platform_count = min(2 + level_index // 2, len(platform_sites))
		platforms = tuple(platform_sites[(index + level_index) % len(platform_sites)] for index in range(platform_count))
		level_random = Random(8461 + level_index * 101)
		platform_pad_count = level_random.randint(1, min(len(pads), len(platforms)))
		pad_indices = level_random.sample(range(len(pads)), platform_pad_count)
		selected_platforms = level_random.sample(platforms, platform_pad_count)
		for pad_index, platform in zip(pad_indices, selected_platforms):
			center_x, top_y, center_z, _, _ = platform
			pads[pad_index] = (center_x, top_y, center_z)
		layouts.append(LevelLayout(LEVEL_NAMES[level_index], tuple(walls), tuple(boxes), platforms, pads, INITIAL_BLOCKS))
	return tuple(layouts)


LEVELS = build_levels()


SolidBox = tuple[float, float, float, float, float, float]


def level_solids(layout: LevelLayout, gate_open: bool) -> tuple[SolidBox, ...]:
	solids: list[SolidBox] = [
		(-8.35, 0.0, -3.0, 0.35, 20.0, 13.0),
		(8.35, 0.0, -3.0, 0.35, 20.0, 13.0),
		(0.0, 0.0, 10.15, 8.5, 20.0, 0.35),
		(0.0, 0.0, -15.75, 8.5, 20.0, 0.35),
	]
	solids.extend((x, 0.0, z, half_x, height, half_z) for x, z, half_x, half_z, height, _ in (*layout.walls, *layout.boxes))
	solids.extend((x, top_y - 0.28, z, half_x, 0.28, half_z) for x, top_y, z, half_x, half_z in layout.platforms)
	if not gate_open:
		solids.append((EXIT_GATE[0], 0.0, EXIT_GATE[1], EXIT_GATE[2], 2.4, EXIT_GATE[3]))
	return tuple(solids)


def overlaps_box(x: float, z: float, half_x: float, half_z: float, obstacle: tuple[float, float, float, float]) -> bool:
	center_x, center_z, obstacle_half_x, obstacle_half_z = obstacle
	return abs(x - center_x) < half_x + obstacle_half_x and abs(z - center_z) < half_z + obstacle_half_z


def overlaps_volume(
	x: float,
	y: float,
	z: float,
	half_x: float,
	half_y: float,
	half_z: float,
	solid: SolidBox,
) -> bool:
	center_x, bottom_y, center_z, solid_half_x, solid_height, solid_half_z = solid
	return (
		abs(x - center_x) < half_x + solid_half_x
		and y < bottom_y + solid_height
		and y + half_y * 2 > bottom_y
		and abs(z - center_z) < half_z + solid_half_z
	)


def volume_collides(
	x: float,
	y: float,
	z: float,
	half_x: float,
	half_y: float,
	half_z: float,
	solids: tuple[SolidBox, ...],
) -> bool:
	return any(overlaps_volume(x, y, z, half_x, half_y, half_z, solid) for solid in solids)


def can_move_block(
	block_index: int,
	x: float,
	z: float,
	blocks: list[PuzzleBlock],
	solids: tuple[SolidBox, ...],
	y: float | None = None,
) -> bool:
	block = blocks[block_index]
	candidate_y = block.y if y is None else y
	world_width, world_min_z, world_max_z = LEVEL_BOUNDS
	if candidate_y < 0 or abs(x) + block.half_size > world_width or not world_min_z + block.half_size < z < world_max_z - block.half_size:
		return False
	if volume_collides(x, candidate_y, z, block.half_size, block.half_size, block.half_size, solids):
		return False
	for other_index, other in enumerate(blocks):
		if (
			other_index != block_index
			and candidate_y < other.y + other.half_size * 2
			and candidate_y + block.half_size * 2 > other.y
			and abs(x - other.x) < block.half_size + other.half_size
			and abs(z - other.z) < block.half_size + other.half_size
		):
			return False
	return True


def move_held_block_vertically(
	block_index: int,
	target_y: float,
	blocks: list[PuzzleBlock],
	layout: LevelLayout,
	gate_open: bool,
) -> None:
	block = blocks[block_index]
	solids = level_solids(layout, gate_open)
	distance = target_y - block.y
	steps = max(1, int(abs(distance) / 0.06) + 1)
	step_y = distance / steps
	for _ in range(steps):
		candidate_y = block.y + step_y
		if not can_move_block(block_index, block.x, block.z, blocks, solids, candidate_y):
			block.vertical_velocity = 0.0
			return
		block.y = candidate_y


def powered_pads(blocks: list[PuzzleBlock], layout: LevelLayout) -> tuple[bool, bool, bool]:
	return tuple(
		any(
			block.color == BLOCK_COLORS[pad_index]
			and abs(block.y - pad_y) < 0.2
			and sqrt((block.x - pad_x) ** 2 + (block.z - pad_z) ** 2) < 0.82
			for block in blocks
		)
		for pad_index, (pad_x, pad_y, pad_z) in enumerate(layout.pads)
	)

def landing_height(
	previous_y: float,
	next_y: float,
	x: float,
	z: float,
	layout: LevelLayout,
	half_extent: float = PLAYER_RADIUS,
	blocks: list[PuzzleBlock] | None = None,
	ignored_block: int | None = None,
) -> float | None:
	landings = [0.0] if previous_y >= 0.0 and next_y <= 0.0 else []
	landings.extend(
		bottom_y + height
		for center_x, bottom_y, center_z, half_x, height, half_z in (
			*((wall_x, 0.0, wall_z, half_x, wall_height, half_z) for wall_x, wall_z, half_x, half_z, wall_height, _ in layout.walls),
			*((box_x, 0.0, box_z, half_x, box_height, half_z) for box_x, box_z, half_x, half_z, box_height, _ in layout.boxes),
			*((platform_x, top_y - 0.28, platform_z, half_x, 0.28, half_z) for platform_x, top_y, platform_z, half_x, half_z in layout.platforms),
		)
		if abs(x - center_x) < half_x + half_extent
		and abs(z - center_z) < half_z + half_extent
		and previous_y >= bottom_y + height
		and next_y <= bottom_y + height
	)
	if blocks is not None:
		landings.extend(
			block.y + block.half_size * 2
			for block_index, block in enumerate(blocks)
			if block_index != ignored_block
			and abs(x - block.x) < half_extent + block.half_size
			and abs(z - block.z) < half_extent + block.half_size
			and previous_y >= block.y + block.half_size * 2
			and next_y <= block.y + block.half_size * 2
		)
	return max(landings) if landings else None


def ceiling_height(
	previous_y: float,
	next_y: float,
	x: float,
	z: float,
	layout: LevelLayout,
	blocks: list[PuzzleBlock],
) -> float | None:
	ceilings = [
		bottom_y
		for center_x, bottom_y, center_z, half_x, _, half_z in level_solids(layout, all(powered_pads(blocks, layout)))
		if abs(x - center_x) < PLAYER_RADIUS + half_x
		and abs(z - center_z) < PLAYER_RADIUS + half_z
		and previous_y + PLAYER_HEIGHT <= bottom_y
		and next_y + PLAYER_HEIGHT > bottom_y
	]
	ceilings.extend(
		block.y
		for block in blocks
		if abs(x - block.x) < PLAYER_RADIUS + block.half_size
		and abs(z - block.z) < PLAYER_RADIUS + block.half_size
		and previous_y + PLAYER_HEIGHT <= block.y
		and next_y + PLAYER_HEIGHT > block.y
	)
	return min(ceilings) - PLAYER_HEIGHT if ceilings else None


def make_level_floor() -> Mesh:
	vertices = (
		-8, 0, -16, 0.12, 0.19, 0.21,
		 8, 0, -16, 0.12, 0.19, 0.21,
		 8, 0,  10, 0.17, 0.24, 0.25,
		-8, 0,  10, 0.17, 0.24, 0.25,
	)
	return Mesh(vertices, (0, 2, 1, 0, 3, 2))


def add_player_model(objects: list[SceneObject], player: LanPlayer) -> None:
	add_box(objects, (245, 255, 62), (player.x, player.y + 1.0, player.z), (0.32, 1.0, 0.32))


def make_level_scene(
	blocks: list[PuzzleBlock],
	powered: tuple[bool, bool, bool],
	held_index: int | None,
	layout: LevelLayout,
	remote_players: tuple[LanPlayer, ...] = (),
) -> Scene:
	objects = [SceneObject(make_level_floor(), translation(0, 0, 0))]
	wall_color = (48, 78, 83)
	neon = (33, 135, 137)
	add_box(objects, (31, 65, 70), (-8.0, 0.035, -3.0), (0.035, 0.025, 12.8))
	add_box(objects, (31, 65, 70), (8.0, 0.035, -3.0), (0.035, 0.025, 12.8))
	for stripe_z in (7.0, 2.0, -3.0, -8.0, -13.0):
		add_box(objects, (34, 79, 81), (0.0, 0.018, stripe_z), (7.6, 0.012, 0.018))

	for center_x, center_z, half_x, half_z, height, color in layout.walls:
		add_box(objects, color, (center_x, height * 0.5, center_z), (half_x, height * 0.5, half_z))
		add_box(objects, neon, (center_x, height + 0.035, center_z), (half_x, 0.035, half_z + 0.04))
	for center_x, center_z, half_x, half_z, height, color in layout.boxes:
		add_box(objects, color, (center_x, height * 0.5, center_z), (half_x, height * 0.5, half_z))
		add_box(objects, neon, (center_x, height + 0.025, center_z), (half_x * 0.72, 0.025, half_z * 0.72))
	for center_x, top_y, center_z, half_x, half_z in layout.platforms:
		add_box(objects, (65, 110, 113), (center_x, top_y - 0.14, center_z), (half_x, 0.14, half_z))
		add_box(objects, (73, 220, 190), (center_x, top_y + 0.025, center_z), (half_x * 0.9, 0.025, 0.045))

	for index, ((pad_x, pad_y, pad_z), is_powered) in enumerate(zip(layout.pads, powered)):
		pad_color = (39, 190, 151) if is_powered else (61, 93, 91)
		add_box(objects, pad_color, (pad_x, pad_y + 0.035, pad_z), (0.78, 0.035, 0.78))
		add_box(objects, (79, 126, 126), (pad_x, pad_y + 0.078, pad_z), (0.48, 0.012, 0.035))
		add_box(objects, (79, 126, 126), (pad_x, pad_y + 0.078, pad_z), (0.035, 0.012, 0.48))

	for index, block in enumerate(blocks):
		add_box(objects, block.color, (block.x, block.y + block.half_size, block.z), (block.half_size, block.half_size, block.half_size))
		add_box(objects, (185, 231, 220), (block.x, block.y + block.half_size * 2.0 + 0.025, block.z), (block.half_size * 0.55, 0.025, 0.045))
		if index == held_index:
			add_box(objects, (226, 249, 227), (block.x, block.y + block.half_size * 2.0 + 0.07, block.z), (block.half_size * 0.72, 0.018, block.half_size * 0.72))

	for player in remote_players:
		add_player_model(objects, player)

	gate_open = all(powered)
	add_box(objects, (38, 178, 168) if gate_open else (196, 72, 67), (-1.32, 1.35, -13.7), (0.11, 1.35, 0.12))
	add_box(objects, (38, 178, 168) if gate_open else (196, 72, 67), (1.32, 1.35, -13.7), (0.11, 1.35, 0.12))
	add_box(objects, (38, 178, 168) if gate_open else (196, 72, 67), (0, 2.7, -13.7), (1.42, 0.11, 0.12))
	if not gate_open:
		add_box(objects, (188, 74, 71), (0, 1.2, -13.7), (1.2, 1.2, 0.14))
	else:
		add_box(objects, (62, 204, 168), (0, 0.02, -15.05), (1.0, 0.02, 0.035))
	return Scene(tuple(objects))


def find_grab_target(player_x: float, player_z: float, yaw: float, blocks: list[PuzzleBlock]) -> int | None:
	forward_x, forward_z = sin(yaw), -cos(yaw)
	nearest_index = None
	nearest_distance = 2.8
	for index, block in enumerate(blocks):
		delta_x, delta_z = block.x - player_x, block.z - player_z
		distance = sqrt(delta_x * delta_x + delta_z * delta_z)
		if distance > nearest_distance or distance == 0:
			continue
		forward_distance = delta_x * forward_x + delta_z * forward_z
		lateral_distance = abs(delta_x * forward_z - delta_z * forward_x)
		if forward_distance > 0 and lateral_distance < 0.9:
			nearest_index = index
			nearest_distance = distance
	return nearest_index


def project_pad_to_hud(
	view_projection: tuple[float, ...],
	point: tuple[float, float, float],
	player_x: float,
	player_z: float,
	yaw: float,
	screen_size: tuple[int, int],
) -> tuple[int, int]:
	x, y, z = point
	clip_x = view_projection[0] * x + view_projection[4] * y + view_projection[8] * z + view_projection[12]
	clip_y = view_projection[1] * x + view_projection[5] * y + view_projection[9] * z + view_projection[13]
	clip_w = view_projection[3] * x + view_projection[7] * y + view_projection[11] * z + view_projection[15]
	width, height = screen_size
	margin = 24
	if clip_w > 0.05:
		screen_x = (clip_x / clip_w * 0.5 + 0.5) * width
		screen_y = (0.5 - clip_y / clip_w * 0.5) * height
		return (
			int(max(margin, min(width - margin, screen_x))),
			int(max(margin, min(height - margin, screen_y))),
		)

	delta_x, delta_z = x - player_x, z - player_z
	direction_x = delta_x * cos(yaw) + delta_z * sin(yaw)
	direction_y = -(delta_x * sin(yaw) - delta_z * cos(yaw))
	length = max(abs(direction_x), abs(direction_y), 1e-6)
	travel = min((width * 0.5 - margin) / length, (height * 0.5 - margin) / length)
	return (
		int(width * 0.5 + direction_x * travel),
		int(height * 0.5 + direction_y * travel),
	)


def draw_pad_wall_markers(
	screen: pygame.Surface,
	small_font: pygame.font.Font,
	layout: LevelLayout,
	powered: tuple[bool, bool, bool],
	view_projection: tuple[float, ...],
	player_x: float,
	player_z: float,
	yaw: float,
) -> None:
	width, height = screen.get_size()
	for pad_index, (pad_x, pad_y, pad_z) in enumerate(layout.pads):
		position = project_pad_to_hud(
			view_projection,
			(pad_x, pad_y + 0.18, pad_z),
			player_x,
			player_z,
			yaw,
			(width, height),
		)
		pygame.draw.circle(screen, (6, 13, 15), position, 17)
		pygame.draw.circle(screen, BLOCK_COLORS[pad_index], position, 13, 3)
		badge = small_font.render(f"P{pad_index + 1}", True, (239, 244, 231))
		screen.blit(badge, badge.get_rect(center=position))
		label = f"{BLOCK_COLOR_NAMES[pad_index]} CORE" + ("  OK" if powered[pad_index] else "")
		label_surface = small_font.render(label, True, BLOCK_COLORS[pad_index])
		label_x = min(max(4, position[0] + 20), width - label_surface.get_width() - 8)
		label_y = min(max(4, position[1] - label_surface.get_height() // 2), height - label_surface.get_height() - 4)
		label_rect = pygame.Rect(label_x - 4, label_y - 2, label_surface.get_width() + 8, label_surface.get_height() + 4)
		pygame.draw.rect(screen, (6, 13, 15), label_rect, border_radius=3)
		screen.blit(label_surface, (label_x, label_y))


def draw_level_hud(
	screen: pygame.Surface,
	font: pygame.font.Font,
	small_font: pygame.font.Font,
	level_number: int,
	level_name: str,
	blocks: list[PuzzleBlock],
	powered: tuple[bool, bool, bool],
	held_index: int | None,
	jetpack_uses: int,
	color_guide: bool,
	layout: LevelLayout,
	view_projection: tuple[float, ...],
	player_x: float,
	player_z: float,
	yaw: float,
	paused: bool,
	won: bool,
	final_level: bool,
	party_status: str = "",
) -> None:
	width, height = screen.get_size()
	pygame.draw.rect(screen, (11, 20, 22), (22, 20, 240, 108), border_radius=3)
	pygame.draw.rect(screen, (57, 126, 127), (22, 20, 240, 108), 1, border_radius=3)
	draw_text(screen, small_font, f"LEVEL {level_number:02d}  /  {level_name.upper()}", (34, 28), (91, 219, 197))
	draw_text(screen, font, f"GATE POWER   {sum(powered)} / 3", (34, 48), (226, 235, 219))

	for index, is_powered in enumerate(powered):
		color = (77, 222, 172) if is_powered else (87, 105, 104)
		pygame.draw.rect(screen, color, (34 + index * 27, 73, 18, 5), border_radius=2)
	draw_text(screen, small_font, f"JETPACK  {jetpack_uses} / 3", (126, 69), (112, 230, 196))
	if party_status:
		draw_text(screen, small_font, party_status, (34, 91), (183, 202, 191))

	center_x, center_y = width // 2, height // 2
	for offset in (-1, 1):
		pygame.draw.line(screen, (203, 236, 220), (center_x + offset * 9, center_y), (center_x + offset * 15, center_y), 2)
		pygame.draw.line(screen, (203, 236, 220), (center_x, center_y + offset * 9), (center_x, center_y + offset * 15), 2)
	pygame.draw.circle(screen, (203, 236, 220), (center_x, center_y), 2)

	panel = pygame.Rect(width - 231, 20, 209, 70)
	pygame.draw.rect(screen, (11, 20, 22), panel, border_radius=3)
	pygame.draw.rect(screen, (57, 126, 127), panel, 1, border_radius=3)
	draw_text(screen, small_font, "CARGO", (panel.x + 12, panel.y + 9), (91, 219, 197))
	for index, block in enumerate(blocks):
		pygame.draw.rect(screen, block.color, (panel.x + 12 + index * 28, panel.y + 33, 18, 18), border_radius=2)
		if index == held_index:
			pygame.draw.rect(screen, (238, 238, 207), (panel.x + 9 + index * 28, panel.y + 30, 24, 24), 1, border_radius=3)
		draw_text(screen, small_font, f"{sum(1 for active in powered if active)} / 3 PADS", (panel.x + 107, panel.y + 35), (187, 203, 191))

	draw_text(screen, small_font, "WASD MOVE   C COLOR KEY   SPACE BOOST   WALK INTO BLOCK TO PUSH   E / RMB GRAB   R RESTART", (width // 2 - 310, height - 32), (183, 202, 191))
	if held_index is not None:
		draw_text(screen, small_font, "LINK ACTIVE", (center_x - 40, center_y + 28), (98, 231, 194))
	if color_guide:
		draw_pad_wall_markers(screen, small_font, layout, powered, view_projection, player_x, player_z, yaw)
		guide_rect = pygame.Rect(center_x - 200, 18, 400, 92)
		pygame.draw.rect(screen, (10, 20, 23), guide_rect, border_radius=5)
		pygame.draw.rect(screen, (66, 159, 150), guide_rect, 2, border_radius=5)
		draw_text(screen, small_font, "PAD COLOR KEY  /  MARKERS SHOW THROUGH WALLS", (guide_rect.x + 18, guide_rect.y + 10), (112, 235, 204))
		for pad_index, is_powered in enumerate(powered):
			column_x = guide_rect.x + 20 + pad_index * 124
			pygame.draw.rect(screen, BLOCK_COLORS[pad_index], (column_x, guide_rect.y + 42, 18, 18), border_radius=3)
			draw_text(screen, small_font, f"P{pad_index + 1}  {BLOCK_COLOR_NAMES[pad_index]}", (column_x + 26, guide_rect.y + 45), BLOCK_COLORS[pad_index])
			if is_powered:
				draw_text(screen, small_font, "OK", (column_x + 91, guide_rect.y + 45), (112, 235, 204))
		draw_text(screen, small_font, "C  CLOSE", (guide_rect.x + 18, guide_rect.bottom - 21), (164, 185, 175))
	if paused or won:
		shade = pygame.Surface((width, height), pygame.SRCALPHA)
		shade.fill((4, 10, 12, 190))
		screen.blit(shade, (0, 0))
		label = ("YOU WIN!" if final_level else f"LEVEL {level_number:02d} COMPLETE") if won else "PAUSED"
		draw_text(screen, font, label, (center_x - 83, center_y - 25), (141, 244, 211) if won else (231, 235, 219))
		if won:
			prompt = "R  RESTART THIS LEVEL" if final_level else "R  RESTART   /   SPACE  NEXT LEVEL"
		else:
			prompt = "R  RESTART LEVEL   /   P OR TAB RESUME   /   ESC QUIT"
		draw_text(screen, small_font, prompt, (center_x - 107, center_y + 8), (178, 215, 194))


def play_campaign(session: LanSession | None = None) -> None:
	os.environ["SDL_VIDEO_WINDOW_POS"] = "0,0"
	pygame.init()
	display_info = pygame.display.Info()
	desktop_width = display_info.current_w or OUTPUT_SIZE[0]
	desktop_height = display_info.current_h or OUTPUT_SIZE[1]
	window_size = (desktop_width, desktop_height)
	hybrid_renderer: HybridRenderer | None = None
	software_renderer: Renderer | None = None
	frame_surface: pygame.Surface | None = None
	try:
		screen = pygame.display.set_mode(window_size, pygame.OPENGL | pygame.DOUBLEBUF | pygame.NOFRAME, vsync=1)
		hybrid_renderer = HybridRenderer(window_size, window_size, backend="auto")
	except (ImportError, pygame.error, RuntimeError):
		pygame.display.quit()
		pygame.display.init()
		screen = pygame.display.set_mode(window_size, pygame.NOFRAME | pygame.SCALED, vsync=1)
		software_renderer = Renderer(RENDER_SIZE)
		frame_surface = pygame.image.frombuffer(software_renderer.pixels, RENDER_SIZE, "RGB")

	current_level = 1
	layout = LEVELS[current_level - 1]
	pygame.display.set_caption(f"VECTOR LAB // Level {current_level:02d}")
	clock = pygame.time.Clock()
	font = pygame.font.SysFont("consolas", 20, bold=True)
	small_font = pygame.font.SysFont("consolas", 12, bold=True)
	hud_surface = pygame.Surface(HUD_SIZE, pygame.SRCALPHA)
	scaled_hud = pygame.Surface(window_size, pygame.SRCALPHA)
	blocks = [PuzzleBlock(x, z, BLOCK_COLORS[index]) for index, (x, z) in enumerate(layout.block_starts)]
	spawn_x, spawn_z = (0.0, 7.0) if session is not None and not session.hosting else (0.0, 9.0)
	spawn_yaw = pi if session is not None and not session.hosting else 0.0
	player_x, player_z = spawn_x, spawn_z
	player_y = 0.0
	vertical_velocity = 0.0
	jetpack_uses = 3
	jetpack_burst = 0.0
	yaw, pitch = spawn_yaw, -0.02
	held_index: int | None = None
	paused = won = False
	color_guide = False
	running = True
	scene_state: tuple[object, ...] | None = None
	scene: Scene | None = None
	pygame.event.set_grab(True)
	pygame.mouse.set_visible(False)

	try:
		while running:
			delta = min(clock.tick(60) / 1000.0, 0.05)
			if session is not None:
				block_update = session.take_block_update()
				if block_update is not None and len(block_update) == len(blocks):
					for block, (block_x, block_y, block_z, vertical_speed) in zip(blocks, block_update):
						block.x, block.y, block.z = block_x, block_y, block_z
						block.vertical_velocity = vertical_speed
			for event in pygame.event.get():
				if event.type == pygame.QUIT:
					running = False
				elif event.type == pygame.KEYDOWN:
					if event.key == pygame.K_ESCAPE:
						running = False
					elif event.key in (pygame.K_TAB, pygame.K_p) and not won:
						paused = not paused
						pygame.event.set_grab(not paused)
						pygame.mouse.set_visible(paused)
					elif event.key == pygame.K_e and not paused and not won:
						held_index = None if held_index is not None else find_grab_target(player_x, player_z, yaw, blocks)
					elif event.key == pygame.K_c:
						color_guide = not color_guide
					elif event.key == pygame.K_SPACE:
						if won and current_level < len(LEVELS):
							current_level += 1
							layout = LEVELS[current_level - 1]
							blocks = [PuzzleBlock(x, z, BLOCK_COLORS[index]) for index, (x, z) in enumerate(layout.block_starts)]
							player_x, player_y, player_z = spawn_x, 0.0, spawn_z
							vertical_velocity = jetpack_burst = 0.0
							jetpack_uses = 3
							yaw, pitch = spawn_yaw, -0.02
							held_index = None
							won = False
							scene_state = None
							pygame.display.set_caption(f"VECTOR LAB // Level {current_level:02d}")
						elif not won and not paused and jetpack_uses > 0:
							jetpack_uses -= 1
							jetpack_burst = 0.35
							vertical_velocity = max(vertical_velocity, 2.0)
					elif event.key == pygame.K_r:
						blocks = [PuzzleBlock(x, z, BLOCK_COLORS[index]) for index, (x, z) in enumerate(layout.block_starts)]
						player_x, player_y, player_z = spawn_x, 0.0, spawn_z
						vertical_velocity = jetpack_burst = 0.0
						jetpack_uses = 3
						yaw, pitch = spawn_yaw, -0.02
						held_index = None
						paused = won = False
						scene_state = None
						pygame.event.set_grab(True)
						pygame.mouse.set_visible(False)
				elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 3 and not paused and not won:
					held_index = None if held_index is not None else find_grab_target(player_x, player_z, yaw, blocks)
				elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1 and paused:
					paused = False
					pygame.event.set_grab(True)
					pygame.mouse.set_visible(False)
				elif event.type == pygame.MOUSEMOTION and not paused and not won:
					yaw += event.rel[0] * MOUSE_SENSITIVITY
					pitch = max(-0.82, min(0.82, pitch - event.rel[1] * MOUSE_SENSITIVITY))

			if not paused and not won:
				keys = pygame.key.get_pressed()
				forward_x, forward_z = sin(yaw), -cos(yaw)
				right_x, right_z = cos(yaw), sin(yaw)
				move_x = (float(keys[pygame.K_d]) - float(keys[pygame.K_a])) * right_x
				move_z = (float(keys[pygame.K_d]) - float(keys[pygame.K_a])) * right_z
				move_x += (float(keys[pygame.K_w]) - float(keys[pygame.K_s])) * forward_x
				move_z += (float(keys[pygame.K_w]) - float(keys[pygame.K_s])) * forward_z
				move_length = sqrt(move_x * move_x + move_z * move_z)
				if move_length > 0:
					speed = 4.0 if keys[pygame.K_LSHIFT] else 3.1
					move_x = move_x / move_length * speed * delta
					move_z = move_z / move_length * speed * delta
					gate_is_open = all(powered_pads(blocks, layout))
					solids = level_solids(layout, gate_is_open)
					for axis in (0, 1):
						step_x = move_x if axis == 0 else 0.0
						step_z = move_z if axis == 1 else 0.0
						candidate_x, candidate_z = player_x + step_x, player_z + step_z
						player_blocked = volume_collides(candidate_x, player_y, candidate_z, PLAYER_RADIUS, PLAYER_HEIGHT * 0.5, PLAYER_RADIUS, solids)
						if player_blocked:
							continue
						block_hit = next((index for index, block in enumerate(blocks) if index != held_index and overlaps_volume(candidate_x, player_y, candidate_z, PLAYER_RADIUS, PLAYER_HEIGHT * 0.5, PLAYER_RADIUS, (block.x, block.y, block.z, block.half_size, block.half_size * 2, block.half_size))), None)
						if block_hit is not None:
							block = blocks[block_hit]
							if not can_move_block(block_hit, block.x + step_x, block.z + step_z, blocks, solids):
								continue
							block.x += step_x
							block.z += step_z
						player_x, player_z = candidate_x, candidate_z

				if held_index is not None:
					held_block = blocks[held_index]
					solids = level_solids(layout, all(powered_pads(blocks, layout)))
					pull_x = player_x + forward_x * 1.35
					pull_z = player_z + forward_z * 1.35
					if can_move_block(held_index, pull_x, pull_z, blocks, solids):
						blocks[held_index].x = pull_x
						blocks[held_index].z = pull_z

				previous_player_y = player_y
				if jetpack_burst > 0.0:
					jetpack_burst = max(0.0, jetpack_burst - delta)
					vertical_velocity = min(8.0, vertical_velocity + 13.0 * delta)
				else:
					vertical_velocity -= 15.0 * delta
				next_player_y = max(-1.0, player_y + vertical_velocity * delta)
				if vertical_velocity > 0:
					ceiling = ceiling_height(previous_player_y, next_player_y, player_x, player_z, layout, blocks)
					if ceiling is not None:
						player_y = ceiling
						vertical_velocity = 0.0
						jetpack_burst = 0.0
					else:
						player_y = next_player_y
				else:
					landing = landing_height(previous_player_y, next_player_y, player_x, player_z, layout, PLAYER_RADIUS, blocks)
					if landing is not None:
						player_y = landing
						vertical_velocity = 0.0
						jetpack_burst = 0.0
					else:
						player_y = next_player_y

				if jetpack_burst == 0.0 and player_y == 0.0:
					vertical_velocity = 0.0

				if held_index is not None:
					move_held_block_vertically(
						held_index,
						player_y,
						blocks,
						layout,
						all(powered_pads(blocks, layout)),
					)
				else:
					for block_index, block in enumerate(blocks):
						previous_block_y = block.y
						block.vertical_velocity -= 15.0 * delta
						next_block_y = max(0.0, block.y + block.vertical_velocity * delta)
						block_landing = landing_height(previous_block_y, next_block_y, block.x, block.z, layout, block.half_size, blocks, block_index)
						if block_landing is not None:
							block.y = block_landing
							block.vertical_velocity = 0.0
						else:
							block.y = max(0.0, next_block_y)

			if session is not None:
				session.set_local_state(player_x, player_y, player_z, yaw)
				session.set_blocks(tuple(
					(block.x, block.y, block.z, block.vertical_velocity)
					for block in blocks
				))
			remote_players = session.players if session is not None else ()
			powered = powered_pads(blocks, layout)
			gate_open = all(powered)
			won = gate_open and player_z < -14.6 and abs(player_x) < 1.45

			block_state = tuple((round(block.x, 4), round(block.y, 4), round(block.z, 4)) for block in blocks)
			player_state = tuple((player.player_id, round(player.x, 1), round(player.y, 1), round(player.z, 1)) for player in remote_players)
			new_scene_state = (current_level, block_state, powered, held_index, gate_open, player_state)
			if new_scene_state != scene_state:
				scene = make_level_scene(blocks, powered, held_index, layout, remote_players)
				scene_state = new_scene_state
			assert scene is not None

			eye = (player_x, player_y + 1.58, player_z)
			direction = (sin(yaw) * cos(pitch), sin(pitch), -cos(yaw) * cos(pitch))
			view = look_at(eye, tuple(eye[index] + direction[index] for index in range(3)))
			projection = perspective(1.05, window_size[0] / window_size[1], 0.1, 60.0)
			view_projection = multiply(projection, view)
			hud_surface.fill((0, 0, 0, 0))
			draw_level_hud(
				hud_surface, font, small_font, current_level, layout.name, blocks,
				powered, held_index, jetpack_uses, color_guide, layout,
				view_projection, player_x, player_z, yaw, paused, won,
				current_level == len(LEVELS),
				(
					f"ROOM CODE {session.room_code}  {len(remote_players) + 1}P"
					if session is not None and session.hosting
					else f"LAN PARTY  /  {len(remote_players) + 1} PLAYERS" if session is not None else ""
				),
			)
			pygame.transform.scale(hud_surface, window_size, scaled_hud)
			if hybrid_renderer is not None:
				overlay = pygame.image.tobytes(scaled_hud, "RGBA", True)
				hybrid_renderer.render_all(scene, view_projection, "Vertex", (overlay, window_size, (0, 0)))
			else:
				assert software_renderer is not None and frame_surface is not None
				software_renderer.render_all(scene, view_projection, "Vertex")
				screen.blit(pygame.transform.scale(frame_surface, window_size), (0, 0))
				screen.blit(scaled_hud, (0, 0))
			pygame.display.flip()
	finally:
		pygame.event.set_grab(False)
		pygame.mouse.set_visible(True)
		if hybrid_renderer is not None:
			hybrid_renderer.close()
		if session is not None:
			session.close()
		pygame.quit()


if __name__ == "__main__":
	party_session, quit_requested = choose_party_mode()
	if not quit_requested:
		play_campaign(party_session)
