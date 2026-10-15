package com.compost;

import java.awt.Color;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import javax.inject.Inject;
import javax.inject.Singleton;
import lombok.extern.slf4j.Slf4j;
import net.runelite.api.Client;
import net.runelite.api.Constants;
import net.runelite.api.DynamicObject;
import net.runelite.api.GameObject;
import net.runelite.api.GameState;
import net.runelite.api.GroundObject;
import net.runelite.api.JagexColor;
import net.runelite.api.Model;
import net.runelite.api.Point;
import net.runelite.api.Renderable;
import net.runelite.api.RuneLiteObject;
import net.runelite.api.Scene;
import net.runelite.api.SceneTilePaint;
import net.runelite.api.Tile;
import net.runelite.api.TileObject;
import net.runelite.api.WorldView;
import net.runelite.api.coords.LocalPoint;
import net.runelite.api.hooks.DrawCallbacks;
import net.runelite.client.callback.RenderCallback;

/**
 * Colours the soil of composted patches.
 * <p>
 * What you see of most patches' soil is a dirt mound decoration on each of their tiles; a few
 * patches show soil in their own model instead. Those models are shared by every object in the
 * same state, so they can't simply be recoloured. Instead, as the renderer is about to read one
 * for a composted patch, the soil faces of the shared model are given that patch's colour, and
 * the model's own colours are put back as soon as the renderer moves on. The soil keeps any
 * texture the renderer gives it.
 * <p>
 * Renderers read models on several threads at once. Threads reading a model share the colours it
 * holds: they can read it together if they want the same colours, and otherwise one waits, briefly,
 * for the others to finish. Rather than wait longer, it skips the object, and the zone is read again,
 * as often as it takes for one reading to start after the skip. The renderer can drop a request to
 * read a zone again, so the request is repeated until then.
 * <p>
 * Once planted, the soil of patches without mounds is the terrain, which is recoloured directly,
 * except where 117HD would blend it away: there, a flat quad of the soil's colour is laid over it.
 */
@Slf4j
@Singleton
class SoilRecolourer implements RenderCallback
{
	/**
	 * The dirt mounds on every tile of most patches.
	 */
	private static final int MOUNDS = 7517;
	/**
	 * Hue and saturation (hsl >> 7) of soil faces, and the lightness of that soil: the usual soil,
	 * and the soil mound of the Troll Stronghold and Weiss herb patches.
	 */
	private static final short SOIL = 8724;
	private static final int[][] SOIL_SHADES = {{SOIL >> 7, SOIL & 127}, {7050 >> 7, 7050 & 127}};

	/**
	 * Patches without mounds, whose soil is drawn by the patch's own model.
	 */
	private static final Set<FarmingPatches> SOIL_IN_PATCH_MODEL = EnumSet.of(
		FarmingPatches.TROLL_HERB,
		FarmingPatches.WEISS_HERB,
		FarmingPatches.VARROCK_TREE,
		FarmingPatches.AUBURNVALE_BELL,
		FarmingPatches.HARMONY_ALLOTMENT
	);
	/**
	 * Patches without mounds whose planted soil is the terrain.
	 */
	private static final Set<FarmingPatches> SOIL_IN_TERRAIN = EnumSet.of(FarmingPatches.VARROCK_TREE);
	/**
	 * Patches without mounds whose planted soil is terrain 117HD blends with its surroundings when
	 * the scene loads, so can't be recoloured, and is covered with a flat quad instead.
	 */
	private static final Set<FarmingPatches> SOIL_UNDER_QUAD = EnumSet.of(
		FarmingPatches.AUBURNVALE_BELL,
		FarmingPatches.HARMONY_ALLOTMENT
	);
	/**
	 * Roughly the middle of the lightness of soil terrain, which varies from corner to corner.
	 */
	private static final int TERRAIN_LIGHTNESS = 11;
	/**
	 * The raked soil model covering one tile, lifted just clear of the terrain, and kept within its
	 * tile; one that reaches into neighbouring tiles can end up not drawn at all.
	 */
	private static final int QUAD_MODEL = 8223;
	private static final int QUAD_LIFT = 3;
	private static final int QUAD_RADIUS = 60;

	/**
	 * How long a thread may share a model's colours. The renderer reads it straight away, but its
	 * thread only comes back to let go at its next callback, which can be much later; after this long
	 * it's let go for it.
	 */
	private static final long STALE_NANOS = 20_000_000;
	/**
	 * How long a thread waits for others to finish with a model before skipping it.
	 */
	private static final long WAIT_NANOS = 500_000;
	/**
	 * How long a thread reading a zone goes without reading anything before it's taken to have
	 * finished with the zone; its next read of that zone is a new reading of it.
	 */
	private static final long READING_IDLE_NANOS = 50_000_000;
	/**
	 * How long to keep asking for a zone to be read again before giving up.
	 */
	private static final long REREAD_TIMEOUT_NANOS = 10_000_000_000L;

	/**
	 * How far from a patch's tile to look for the objects making it up.
	 */
	private static final int SEARCH_RADIUS = 8;
	private static final int EXTENDED_OFFSET = (Constants.EXTENDED_SCENE_SIZE - Constants.SCENE_SIZE) / 2;

	private final Client client;

	private final Map<FarmingPatches, Soil> soils = new EnumMap<>(FarmingPatches.class);
	/**
	 * The scene tiles {@link #soils} was found in; a new scene has fresh tiles.
	 */
	private Tile[][][] sceneTiles;
	private Scene scene;
	private boolean coloursChanged;
	/**
	 * Each patch's compost, as last given to the renderers.
	 */
	private final int[] compost = new int[FarmingPatches.values().length];

	// used by the renderers, off the client thread

	/**
	 * The soil colours (compost, supercompost, ultracompost) as HSL.
	 */
	private volatile short[] soilColours;
	/**
	 * Compost (1-3) of each composted patch, keyed by object id. It doesn't depend on the scene, so
	 * a patch has its colour from the first time a renderer reads it.
	 */
	private volatile Map<Integer, Integer> compostByPatch = Collections.emptyMap();
	/**
	 * Each model seen, with its own colours and its colours for each compost.
	 */
	private final Map<Model, ModelColours> models = Collections.synchronizedMap(new WeakHashMap<>());
	/**
	 * Object ids of every patch, any of whose models might be coloured.
	 */
	private static final Set<Integer> PATCH_OBJECTS = new HashSet<>();
	/**
	 * Object ids of the patches whose soil is in their own model.
	 */
	private static final Set<Integer> SOIL_IN_PATCH_MODEL_OBJECTS = new HashSet<>();

	static
	{
		for (FarmingPatches patch : FarmingPatches.values())
		{
			PATCH_OBJECTS.add(patch.getPatchId());
			if (SOIL_IN_PATCH_MODEL.contains(patch))
			{
				SOIL_IN_PATCH_MODEL_OBJECTS.add(patch.getPatchId());
			}
		}
	}

	/**
	 * What this thread last read, to check once the renderer has finished with it.
	 */
	private final ThreadLocal<Read> lastRead = new ThreadLocal<>();
	/**
	 * Each renderer thread's reading of a zone.
	 */
	private final Map<Thread, Reading> readings = Collections.synchronizedMap(new WeakHashMap<>());
	private final ThreadLocal<Reading> reading = ThreadLocal.withInitial(() ->
	{
		Reading r = new Reading();
		readings.put(Thread.currentThread(), r);
		return r;
	});
	/**
	 * Zones to be read again, as the renderer may have read the wrong colours into them, with when
	 * the latest reading that may have done so started: only a reading starting after it will do.
	 */
	private final Map<SceneZone, Suspect> suspects = new ConcurrentHashMap<>();

	/**
	 * A model being read by the renderer, whose colours this thread shares until it's finished.
	 */
	private static final class Read
	{
		final ModelColours model;
		final long generation;
		final SceneZone zone;
		final long readingStart;

		Read(ModelColours model, long generation, SceneZone zone, long readingStart)
		{
			this.model = model;
			this.generation = generation;
			this.zone = zone;
			this.readingStart = readingStart;
		}
	}

	/**
	 * A renderer thread reading one zone, tile by tile.
	 */
	private static final class Reading
	{
		volatile Scene scene;
		volatile int zone;
		volatile long start;
		volatile long last;
	}

	/**
	 * A zone of a particular scene; a zone of an older scene can't be read again.
	 */
	private static final class SceneZone
	{
		final Scene scene;
		final int zone;

		SceneZone(Scene scene, int zone)
		{
			this.scene = scene;
			this.zone = zone;
		}

		@Override
		public boolean equals(Object o)
		{
			return o instanceof SceneZone && ((SceneZone) o).scene == scene && ((SceneZone) o).zone == zone;
		}

		@Override
		public int hashCode()
		{
			return System.identityHashCode(scene) * 31 + zone;
		}
	}

	private static final class Suspect
	{
		/**
		 * When the latest reading that may have read the wrong colours started, or the colours
		 * changed.
		 */
		final long readingStart;
		/**
		 * When the zone was first to be read again.
		 */
		final long since;

		Suspect(long readingStart, long since)
		{
			this.readingStart = readingStart;
			this.since = since;
		}
	}

	private static final class Soil
	{
		/**
		 * The zones the patch is in, packed as {@code zx << 16 | zz}.
		 */
		final Set<Integer> zones = new HashSet<>();
		/**
		 * The patch's soil terrain, and its own corner colours.
		 */
		final Map<SceneTilePaint, int[]> terrain = new IdentityHashMap<>();
		/**
		 * Tiles to cover with a flat quad, with their plane, and the quads covering them.
		 */
		final Map<LocalPoint, Integer> quadTiles = new HashMap<>();
		final Map<LocalPoint, RuneLiteObject> quads = new HashMap<>();
		int compost;
	}

	/**
	 * A model's face colours.
	 */
	private static final class Colours
	{
		final int[] colours1;
		final int[] colours2;
		final int[] colours3;
		final short[] unlit;

		Colours(Model model)
		{
			this(model.getFaceColors1().clone(), model.getFaceColors2().clone(), model.getFaceColors3().clone(),
				model.getUnlitFaceColors() == null ? null : model.getUnlitFaceColors().clone());
		}

		private Colours(int[] colours1, int[] colours2, int[] colours3, short[] unlit)
		{
			this.colours1 = colours1;
			this.colours2 = colours2;
			this.colours3 = colours3;
			this.unlit = unlit;
		}

		void writeTo(Model model)
		{
			copy(colours1, model.getFaceColors1());
			copy(colours2, model.getFaceColors2());
			copy(colours3, model.getFaceColors3());
			short[] u = model.getUnlitFaceColors();
			if (unlit != null && u != null)
			{
				System.arraycopy(unlit, 0, u, 0, Math.min(unlit.length, u.length));
			}
		}

		/**
		 * These colours with every soil face recoloured, keeping its shading. Null if there are no
		 * soil faces.
		 */
		Colours withSoil(short colour)
		{
			int[] c1 = colours1.clone();
			int[] c2 = colours2.clone();
			int[] c3 = colours3.clone();
			short[] u = unlit == null ? null : unlit.clone();
			boolean any = false;
			for (int face = 0; face < c1.length; face++)
			{
				int[] shade = soilShade(c1[face]);
				if (c3[face] == -2 || shade == null)
				{
					continue;
				}
				any = true;
				c1[face] = recolour(c1[face], shade[1], colour);
				if (c3[face] != -1)
				{
					c2[face] = recolour(c2[face], shade[1], colour);
					c3[face] = recolour(c3[face], shade[1], colour);
				}
				if (u != null)
				{
					u[face] = (short) recolour(u[face] & 0xFFFF, shade[1], colour);
				}
			}
			return any ? new Colours(c1, c2, c3, u) : null;
		}

		private static int[] soilShade(int hsl)
		{
			for (int[] shade : SOIL_SHADES)
			{
				if (hsl >= 0 && hsl >> 7 == shade[0])
				{
					return shade;
				}
			}
			return null;
		}

		private static void copy(int[] from, int[] to)
		{
			System.arraycopy(from, 0, to, 0, Math.min(from.length, to.length));
		}
	}

	/**
	 * A model's colours with its soil recoloured for each compost.
	 */
	private static final class SoilColours
	{
		final short[] soil;
		final Colours[] colours = new Colours[3];

		SoilColours(Colours original, short[] soil)
		{
			this.soil = soil;
			for (int c = 0; c < 3; c++)
			{
				colours[c] = original.withSoil(soil[c]);
			}
		}
	}

	/**
	 * A model, its own colours, and those colours with its soil recoloured for each compost, with
	 * the threads sharing its colours.
	 * <p>
	 * Its state packs how many threads are sharing its colours (bits 0-15), which colours they are
	 * (bits 16-17: its own, or a compost's), a bit set while its colours are being changed, and a
	 * generation (bits 19 up) changed with its colours. With no threads, it has its own colours.
	 */
	private static final class ModelColours
	{
		static final long READERS = 0xFFFF;
		static final int MODE_SHIFT = 16;
		static final long WRITING = 1L << 18;
		static final int GENERATION_SHIFT = 19;

		final Model model;
		final Colours original;
		final AtomicLong state = new AtomicLong();
		volatile long sharedAt;
		/**
		 * This model's colours with each set of soil colours, by compost, most recent only.
		 */
		volatile SoilColours byCompost;
		/**
		 * The soil colours the model's colours were last changed to.
		 */
		volatile short[] sharedSoil;

		ModelColours(Model model)
		{
			this.model = model;
			this.original = new Colours(model);
		}

		/**
		 * This model's colours with its soil recoloured for a compost, or null if it has no soil.
		 */
		Colours withSoil(int compost, short[] soilColours)
		{
			SoilColours byCompost = this.byCompost;
			if (byCompost == null || byCompost.soil != soilColours)
			{
				byCompost = new SoilColours(original, soilColours);
				this.byCompost = byCompost;
			}
			return byCompost.colours[compost - 1];
		}

		static long pack(long generation, int mode, long readers)
		{
			return generation << GENERATION_SHIFT | (long) mode << MODE_SHIFT | readers;
		}

		static int mode(long s)
		{
			return (int) (s >> MODE_SHIFT) & 3;
		}

		static long generation(long s)
		{
			return s >>> GENERATION_SHIFT;
		}

		/**
		 * Share this model's colours for a compost (0 for its own), changing them if no thread is
		 * sharing it. Waits at most {@link #WAIT_NANOS} for threads sharing other colours to finish.
		 *
		 * @return the generation shared, or -1 if it's still in use
		 */
		long share(int mode, Colours colours, short[] soil)
		{
			long deadline = 0;
			for (;;)
			{
				long s = state.get();
				if ((s & WRITING) == 0)
				{
					if (mode(s) == mode && (mode == 0 || sharedSoil == soil))
					{
						if (state.compareAndSet(s, s + 1))
						{
							sharedAt = System.nanoTime();
							return generation(s);
						}
						continue;
					}
					if ((s & READERS) == 0 && state.compareAndSet(s, s | WRITING))
					{
						// with no threads sharing it, it has its own colours
						colours.writeTo(model);
						sharedSoil = soil;
						long generation = generation(s) + 1;
						sharedAt = System.nanoTime();
						state.set(pack(generation, mode, 1));
						return generation;
					}
				}

				long now = System.nanoTime();
				if (deadline == 0)
				{
					deadline = now + WAIT_NANOS;
				}
				else if (now > deadline)
				{
					return -1;
				}
				Thread.onSpinWait();
			}
		}

		/**
		 * Stop sharing this model's colours, putting its own colours back if it was the last thread
		 * sharing a compost's.
		 *
		 * @return false if they were taken from this thread before it had finished with them
		 */
		boolean release(long generation)
		{
			for (;;)
			{
				long s = state.get();
				if ((s & WRITING) != 0)
				{
					// another thread is changing its colours, which only takes a moment
					Thread.onSpinWait();
					continue;
				}
				if (generation(s) != generation)
				{
					return false;
				}
				if ((s & READERS) == 1 && mode(s) != 0)
				{
					if (state.compareAndSet(s, pack(generation, mode(s), 0) | WRITING))
					{
						original.writeTo(model);
						state.set(pack(generation + 1, 0, 0));
						return true;
					}
				}
				else if (state.compareAndSet(s, s - 1))
				{
					return true;
				}
			}
		}

		/**
		 * Take this model's colours from the threads sharing them, if they have for too long or
		 * {@code all}, and put its own back.
		 *
		 * @return whether any were taken
		 */
		boolean revoke(boolean all)
		{
			for (;;)
			{
				long s = state.get();
				if ((s & WRITING) != 0 || (s & READERS) == 0 || !all && System.nanoTime() - sharedAt <= STALE_NANOS)
				{
					return false;
				}
				if (state.compareAndSet(s, s | WRITING))
				{
					original.writeTo(model);
					state.set(pack(generation(s) + 1, 0, 0));
					return true;
				}
			}
		}
	}

	@Inject
	SoilRecolourer(Client client)
	{
		this.client = client;
	}

	/**
	 * Set the soil colour for compost, supercompost and ultracompost. Must run on the client thread.
	 */
	void setColours(Color compost, Color supercompost, Color ultracompost)
	{
		soilColours = new short[]{hsl(compost), hsl(supercompost), hsl(ultracompost)};
		coloursChanged = true;
	}

	private static short hsl(Color colour)
	{
		return JagexColor.rgbToHSL(colour.getRGB(), 1.0);
	}

	/**
	 * A colour, lightened or darkened as much as {@code hsl} is from {@code lightness}.
	 */
	private static int recolour(int hsl, int lightness, short colour)
	{
		int l = Math.max(0, Math.min(127, (colour & 127) + (hsl & 127) - lightness));
		return (colour & 0xFF80) | l;
	}

	/**
	 * Bring each patch's soil in line with its compost. Must run on the client thread, every client
	 * tick, so a new scene's terrain and quads follow as soon as it's shown.
	 */
	void update(boolean enabled)
	{
		if (soilColours == null)
		{
			return;
		}

		Set<FarmingPatches> changed = EnumSet.noneOf(FarmingPatches.class);
		for (FarmingPatches patch : FarmingPatches.values())
		{
			int c = enabled ? client.getVarbitValue(patch.getCompostVarbit()) : 0;
			if (compost[patch.ordinal()] != c)
			{
				compost[patch.ordinal()] = c;
				changed.add(patch);
			}
		}
		if (!changed.isEmpty())
		{
			Map<Integer, Integer> byPatch = new HashMap<>();
			for (FarmingPatches patch : FarmingPatches.values())
			{
				if (compost[patch.ordinal()] != 0)
				{
					byPatch.put(patch.getPatchId(), compost[patch.ordinal()]);
				}
			}
			compostByPatch = byPatch;
		}

		WorldView wv = client.getTopLevelWorldView();
		if (wv == null || client.getGameState() != GameState.LOGGED_IN)
		{
			return;
		}

		if (wv.getScene().getTiles() != sceneTiles)
		{
			soils.values().forEach(SoilRecolourer::removeQuads);
			soils.clear();
			if (scene != null)
			{
				carryOverSuspects(scene, wv.getScene());
			}
			sceneTiles = wv.getScene().getTiles();
			scene = wv.getScene();
		}

		Set<Integer> zones = new HashSet<>();
		for (FarmingPatches patch : FarmingPatches.values())
		{
			int c = compost[patch.ordinal()];
			Soil soil = soils.get(patch);
			if (soil == null)
			{
				if (c == 0 || (soil = find(wv, patch)) == null)
				{
					continue;
				}
				soils.put(patch, soil);
				// the renderer has given the patch its colour unless its compost has only just
				// changed, but its terrain and quads are still to do
				soil.compost = c;
				colourTerrain(soil);
				placeQuads(soil);
				if (!soil.terrain.isEmpty() || changed.contains(patch))
				{
					zones.addAll(soil.zones);
				}
			}
			else if (soil.compost != c || coloursChanged)
			{
				soil.compost = c;
				colourTerrain(soil);
				placeQuads(soil);
				zones.addAll(soil.zones);
			}
		}
		coloursChanged = false;

		// have the renderer read the patches again
		long now = System.nanoTime();
		for (int zone : zones)
		{
			reread(new SceneZone(wv.getScene(), zone), now);
		}
	}

	/**
	 * The renderer can carry a zone over from the last scene as it was, so have zones of the last
	 * scene still to be read again read again in this one.
	 */
	private void carryOverSuspects(Scene from, Scene to)
	{
		int dx = (from.getBaseX() - to.getBaseX()) >> 3;
		int dy = (from.getBaseY() - to.getBaseY()) >> 3;
		int zones = Constants.EXTENDED_SCENE_SIZE >> 3;
		long now = System.nanoTime();
		for (SceneZone zone : suspects.keySet())
		{
			if (zone.scene != from)
			{
				continue;
			}
			suspects.remove(zone);
			int zx = (zone.zone >> 16) + dx;
			int zz = (zone.zone & 0xFFFF) + dy;
			if (zx >= 0 && zx < zones && zz >= 0 && zz < zones)
			{
				reread(new SceneZone(to, zx << 16 | zz), now);
			}
		}
	}

	/**
	 * Put back the original soil. Must run on the client thread.
	 */
	void clear()
	{
		compostByPatch = Collections.emptyMap();
		Arrays.fill(compost, 0);
		WorldView wv = client.getTopLevelWorldView();
		if (wv != null && wv.getScene().getTiles() == sceneTiles)
		{
			Set<Integer> zones = new HashSet<>();
			for (Soil soil : soils.values())
			{
				soil.compost = 0;
				colourTerrain(soil);
				zones.addAll(soil.zones);
			}
			invalidate(wv.getScene(), zones);
		}
		soils.values().forEach(SoilRecolourer::removeQuads);
		soils.clear();
		sceneTiles = null;
		scene = null;

		// a renderer thread may not have come back to put its colours right
		revoke(true);
		suspects.clear();
	}

	/**
	 * Give a patch's soil terrain its compost's colour, or its own colours back.
	 */
	private void colourTerrain(Soil soil)
	{
		short colour = soil.compost == 0 ? 0 : soilColours[soil.compost - 1];
		soil.terrain.forEach((paint, original) ->
		{
			paint.setSwColor(terrainColour(original[0], soil.compost, colour));
			paint.setSeColor(terrainColour(original[1], soil.compost, colour));
			paint.setNeColor(terrainColour(original[2], soil.compost, colour));
			paint.setNwColor(terrainColour(original[3], soil.compost, colour));
		});
	}

	private static int terrainColour(int original, int compost, short colour)
	{
		return compost == 0 || original < 0 || original > 0xFFFF ? original : recolour(original, TERRAIN_LIGHTNESS, colour);
	}

	/**
	 * Cover a patch's soil with flat quads of its compost's colour, or remove them.
	 */
	private void placeQuads(Soil soil)
	{
		removeQuads(soil);
		if (soil.compost == 0)
		{
			return;
		}
		short colour = soilColours[soil.compost - 1];
		soil.quadTiles.forEach((location, plane) ->
		{
			// every quad gets its own model; the renderers keep per-model state
			Model model = client.loadModelData(QUAD_MODEL)
				.cloneVertices()
				.cloneColors()
				// the model faces down, so would be lit from below; mirroring turns it over
				.scale(-128, 128, 128)
				.recolor(SOIL, colour)
				.light();
			model.calculateBoundsCylinder();

			RuneLiteObject quad = client.createRuneLiteObject();
			quad.setModel(model);
			quad.setLocation(location, plane);
			quad.setZ(quad.getZ() - QUAD_LIFT);
			quad.setRadius(QUAD_RADIUS);
			quad.setActive(true);
			soil.quads.put(location, quad);
		});
	}

	private static void removeQuads(Soil soil)
	{
		soil.quads.values().forEach(quad -> quad.setActive(false));
		soil.quads.clear();
	}

	private void invalidate(Scene scene, Set<Integer> zones)
	{
		DrawCallbacks dc = client.getDrawCallbacks();
		if (dc == null)
		{
			return;
		}
		for (int zone : zones)
		{
			dc.invalidateZone(scene, zone >> 16, zone & 0xFFFF);
		}
	}

	/**
	 * Put back colours a renderer thread has left in a model too long, and ask again for zones
	 * that may have been read with the wrong colours to be read again. Must run on the client
	 * thread, every client tick.
	 */
	void tick()
	{
		revoke(false);

		long now = System.nanoTime();
		synchronized (readings)
		{
			for (Reading r : readings.values())
			{
				if (r.scene != null && now - r.last > READING_IDLE_NANOS)
				{
					r.scene = null;
				}
			}
		}

		WorldView wv = client.getTopLevelWorldView();
		DrawCallbacks dc = client.getDrawCallbacks();
		Scene current = wv == null ? null : wv.getScene();
		suspects.forEach((zone, suspect) ->
		{
			if (now - suspect.since > REREAD_TIMEOUT_NANOS)
			{
				log.debug("Gave up having zone {},{} read again", zone.zone >> 16, zone.zone & 0xFFFF);
				suspects.remove(zone, suspect);
			}
			else if (zone.scene == current && dc != null)
			{
				// the renderer ignores this while the zone is already to be read again
				dc.invalidateZone(current, zone.zone >> 16, zone.zone & 0xFFFF);
			}
		});
	}

	@Override
	public boolean drawTile(Scene scene, Tile tile)
	{
		// the renderer has finished with the previous tile's objects
		finishRead();

		Reading r = reading.get();
		long now = System.nanoTime();
		Point p = tile.getSceneLocation();
		int zone = zone(p.getX(), p.getY());
		if (r.scene != scene || r.zone != zone)
		{
			// a new reading of this zone, which is all it takes for it to have been read again
			r.scene = scene;
			r.zone = zone;
			r.start = now;
			if (!suspects.isEmpty())
			{
				suspects.computeIfPresent(new SceneZone(scene, zone), (z, s) -> s.readingStart < now ? null : s);
			}
		}
		r.last = now;
		return true;
	}

	@Override
	public boolean drawObject(Scene scene, TileObject object)
	{
		finishRead();

		Integer compost;
		Renderable renderable;
		int zone;
		if (object instanceof GameObject && PATCH_OBJECTS.contains(object.getId()))
		{
			compost = SOIL_IN_PATCH_MODEL_OBJECTS.contains(object.getId()) ? compostByPatch.get(object.getId()) : null;
			renderable = ((GameObject) object).getRenderable();
			// it's in the zone of the tile it's drawn from
			Point min = ((GameObject) object).getSceneMinLocation();
			zone = zone(min.getX(), min.getY());
		}
		else if (object instanceof GroundObject && object.getId() == MOUNDS)
		{
			LocalPoint lp = object.getLocalLocation();
			compost = moundCompost(scene, lp.getSceneX(), lp.getSceneY(), object.getPlane());
			renderable = ((GroundObject) object).getRenderable();
			zone = zone(lp.getSceneX(), lp.getSceneY());
		}
		else
		{
			return true;
		}

		// never getModel() off the client thread: for a patch it rebuilds the model from the
		// patch's state, which isn't safe to read here
		Model model = renderable instanceof Model ? (Model) renderable
			: renderable instanceof DynamicObject ? ((DynamicObject) renderable).getModelZbuf()
			: null;
		short[] soilColours = this.soilColours;
		if (model == null || soilColours == null)
		{
			return true;
		}

		ModelColours colours;
		synchronized (models)
		{
			// a model's first seen while no thread shares it, so with its own colours
			colours = models.computeIfAbsent(model, ModelColours::new);
		}
		Colours soil = compost == null ? null : colours.withSoil(compost, soilColours);
		int mode = soil == null ? 0 : compost;

		SceneZone sceneZone = new SceneZone(scene, zone);
		long readingStart = reading.get().start;
		long generation = colours.share(mode, soil, soilColours);
		if (generation < 0)
		{
			// rather than read it with the wrong colours, skip it and read the zone again
			reread(sceneZone, readingStart);
			return false;
		}
		lastRead.set(new Read(colours, generation, sceneZone, readingStart));
		return true;
	}

	/**
	 * Take every model's colours from threads that have shared them too long, or from all threads.
	 */
	private void revoke(boolean all)
	{
		synchronized (models)
		{
			for (ModelColours colours : models.values())
			{
				colours.revoke(all);
			}
		}
	}

	/**
	 * The compost of the patch a mound is part of, if it's composted.
	 */
	private Integer moundCompost(Scene scene, int sceneX, int sceneY, int plane)
	{
		Tile[][][] tiles = scene.getExtendedTiles();
		int x = sceneX + EXTENDED_OFFSET;
		int y = sceneY + EXTENDED_OFFSET;
		if (plane < 0 || plane >= tiles.length || x < 0 || x >= tiles[plane].length || y < 0 || y >= tiles[plane][x].length
			|| tiles[plane][x][y] == null)
		{
			return null;
		}

		Map<Integer, Integer> compostByPatch = this.compostByPatch;
		for (GameObject object : tiles[plane][x][y].getGameObjects())
		{
			Integer compost = object == null ? null : compostByPatch.get(object.getId());
			if (compost != null)
			{
				return compost;
			}
		}
		return null;
	}

	/**
	 * Have a zone read again, by a reading starting after {@code readingStart}.
	 */
	private void reread(SceneZone zone, long readingStart)
	{
		long now = System.nanoTime();
		suspects.merge(zone, new Suspect(readingStart, now),
			(old, s) -> new Suspect(Math.max(old.readingStart, s.readingStart), old.since));
	}

	/**
	 * Now the renderer has finished with what this thread last read, stop sharing its colours; if
	 * they were taken first, have it read again.
	 */
	private void finishRead()
	{
		Read read = lastRead.get();
		if (read == null)
		{
			return;
		}
		lastRead.remove();

		if (!read.model.release(read.generation))
		{
			reread(read.zone, read.readingStart);
		}
	}

	/**
	 * The zone a scene tile is in, packed as {@code zx << 16 | zz}.
	 */
	private static int zone(int sceneX, int sceneY)
	{
		return (((sceneX + EXTENDED_OFFSET) >> 3) << 16) | ((sceneY + EXTENDED_OFFSET) >> 3);
	}

	/**
	 * Find the zones a patch is in (it's sometimes several objects sharing an id), and for a patch
	 * without mounds, its soil terrain.
	 */
	private static Soil find(WorldView wv, FarmingPatches patch)
	{
		LocalPoint centre = LocalPoint.fromWorld(wv, patch.getTile());
		if (centre == null || patch.getTile().getPlane() != wv.getPlane())
		{
			return null;
		}

		int plane = patch.getTile().getPlane();
		Tile[][] tiles = wv.getScene().getTiles()[plane];
		short[][] overlays = wv.getScene().getOverlayIds()[plane];
		Soil soil = new Soil();
		boolean found = false;
		int cx = centre.getSceneX();
		int cy = centre.getSceneY();
		for (int x = Math.max(0, cx - SEARCH_RADIUS); x <= Math.min(tiles.length - 1, cx + SEARCH_RADIUS); x++)
		{
			for (int y = Math.max(0, cy - SEARCH_RADIUS); y <= Math.min(tiles[x].length - 1, cy + SEARCH_RADIUS); y++)
			{
				Tile tile = tiles[x][y];
				if (tile == null || !hasObject(tile, patch.getPatchId()))
				{
					continue;
				}
				found = true;
				int zone = zone(x, y);

				if (SOIL_IN_PATCH_MODEL.contains(patch))
				{
					soil.zones.add(zone);
					SceneTilePaint paint = tile.getSceneTilePaint();
					boolean dirt = overlays[x + EXTENDED_OFFSET][y + EXTENDED_OFFSET] != 0;
					if (SOIL_UNDER_QUAD.contains(patch) && dirt)
					{
						soil.quadTiles.put(tile.getLocalLocation(), plane);
					}
					else if (SOIL_IN_TERRAIN.contains(patch) && dirt && paint != null)
					{
						soil.terrain.put(paint, new int[]{paint.getSwColor(), paint.getSeColor(), paint.getNeColor(), paint.getNwColor()});
					}
					continue;
				}

				GroundObject ground = tile.getGroundObject();
				if (ground != null && ground.getId() == MOUNDS)
				{
					soil.zones.add(zone);
				}
			}
		}
		if (!found)
		{
			// not loaded yet, so look again later
			return null;
		}
		log.debug("{}: {} terrain tiles, {} quad tiles, in {} zones", patch, soil.terrain.size(), soil.quadTiles.size(), soil.zones.size());
		return soil;
	}

	private static boolean hasObject(Tile tile, int id)
	{
		for (GameObject go : tile.getGameObjects())
		{
			if (go != null && go.getId() == id)
			{
				return true;
			}
		}
		return false;
	}
}
