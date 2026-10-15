package com.compost;

import com.google.inject.Provides;
import javax.inject.Inject;
import net.runelite.api.events.ClientTick;
import net.runelite.client.callback.ClientThread;
import net.runelite.client.callback.RenderCallbackManager;
import net.runelite.client.config.ConfigManager;
import net.runelite.client.eventbus.Subscribe;
import net.runelite.client.events.ConfigChanged;
import net.runelite.client.plugins.Plugin;
import net.runelite.client.plugins.PluginDescriptor;
import net.runelite.client.ui.overlay.OverlayManager;

@PluginDescriptor(
	name = "Did I Compost?"
)
public class DidICompostPlugin extends Plugin
{
	@Inject
	private PatchOverlay patchOverlay;

	@Inject
	private OverlayManager overlayManager;

	@Inject
	private SoilRecolourer soilRecolourer;

	@Inject
	private ClientThread clientThread;

	@Inject
	private RenderCallbackManager renderCallbackManager;

	@Inject
	private DidICompostConfig config;

	private boolean soil;

	@Subscribe
	public void onConfigChanged(ConfigChanged event)
	{
		if (event.getNewValue() == null || !"didICompost".equals(event.getGroup()))
		{
			return;
		}

		if ("iconSize".equals(event.getKey()))
		{
			patchOverlay.updateImages();
		}
		else if ("displayMode".equals(event.getKey()) || event.getKey().endsWith("Colour"))
		{
			clientThread.invokeLater(() ->
			{
				loadSoilConfig();
				soilRecolourer.update(soil);
			});
		}
	}

	@Subscribe
	public void onClientTick(ClientTick event)
	{
		soilRecolourer.update(soil);
		soilRecolourer.tick();
	}

	private void loadSoilConfig()
	{
		soil = config.displayMode().isSoil();
		soilRecolourer.setColours(config.compostColour(), config.supercompostColour(), config.ultracompostColour());
	}

	@Override
	protected void startUp()
	{
		overlayManager.add(patchOverlay);
		patchOverlay.updateImages();
		renderCallbackManager.register(soilRecolourer);
		clientThread.invokeLater(this::loadSoilConfig);
	}

	@Override
	protected void shutDown()
	{
		overlayManager.remove(patchOverlay);
		patchOverlay.reset();
		clientThread.invokeLater(() ->
		{
			soilRecolourer.clear();
			renderCallbackManager.unregister(soilRecolourer);
		});
	}

	@Provides
	DidICompostConfig provideConfig(ConfigManager configManager)
	{
		return configManager.getConfig(DidICompostConfig.class);
	}
}
