const EMPTY_PAGE_URL = GetTestWebBasedURL("file_empty.html");

/**
 * When web audio changes its audible state, the sound indicator should be
 * updated as well, which should appear only when web audio is audible.
 */
add_task(
  async function testWebAudioAudibilityWouldAffectTheAppearenceOfTabSoundIndicator() {
    info(`sound indicator should appear when web audio plays audible sound`);
    const tab = await BrowserTestUtils.openNewForegroundTab(
      gBrowser,
      EMPTY_PAGE_URL
    );
    await initWebAudioDocument(tab);
    await waitForTabSoundIndicatorAppears(tab);

    info(`sound indicator should disappear when suspending web audio`);
    await suspendWebAudio(tab);
    await waitForTabSoundIndicatorDisappears(tab);

    info(`sound indicator should appear when resuming web audio`);
    await resumeWebAudio(tab);
    await waitForTabSoundIndicatorAppears(tab);

    info(`sound indicator should disappear when muting web audio by docShell`);
    await muteWebAudioByDocShell(tab);
    await waitForTabSoundIndicatorDisappears(tab);

    info(`sound indicator should appear when unmuting web audio by docShell`);
    await unmuteWebAudioByDocShell(tab);
    await waitForTabSoundIndicatorAppears(tab);

    info(`sound indicator should disappear when muting web audio by gain node`);
    await muteWebAudioByGainNode(tab);
    await waitForTabSoundIndicatorDisappears(tab);

    info(`sound indicator should appear when unmuting web audio by gain node`);
    await unmuteWebAudioByGainNode(tab);
    await waitForTabSoundIndicatorAppears(tab);

    info("remove tab");
    BrowserTestUtils.removeTab(tab);
  }
);

/**
 * Following are helper functions
 */
function initWebAudioDocument(tab) {
  return SpecialPowers.spawn(tab.linkedBrowser, [], async _ => {
    content.ac = new content.AudioContext();
    const ac = content.ac;
    const dest = ac.destination;
    const source = new content.OscillatorNode(ac);
    source.start(ac.currentTime);
    // create a gain node for future muting/unmuting
    content.gainNode = ac.createGain();
    source.connect(content.gainNode);
    content.gainNode.connect(dest);
    while (ac.state != "running") {
      info(`wait until web audio starts running`);
      await new Promise(r => (ac.onstatechange = r));
    }
  });
}

function suspendWebAudio(tab) {
  return SpecialPowers.spawn(tab.linkedBrowser, [], async _ => {
    await content.ac.suspend();
  });
}

function resumeWebAudio(tab) {
  return SpecialPowers.spawn(tab.linkedBrowser, [], async _ => {
    await content.ac.resume();
  });
}

function muteWebAudioByDocShell(tab) {
  return SpecialPowers.spawn(tab.linkedBrowser, [], _ => {
    content.docShell.allowMedia = false;
  });
}

function unmuteWebAudioByDocShell(tab) {
  return SpecialPowers.spawn(tab.linkedBrowser, [], _ => {
    content.docShell.allowMedia = true;
  });
}

function muteWebAudioByGainNode(tab) {
  return SpecialPowers.spawn(tab.linkedBrowser, [], _ => {
    content.gainNode.gain.setValueAtTime(0, content.ac.currentTime);
  });
}

function unmuteWebAudioByGainNode(tab) {
  return SpecialPowers.spawn(tab.linkedBrowser, [], _ => {
    content.gainNode.gain.setValueAtTime(1.0, content.ac.currentTime);
  });
}
