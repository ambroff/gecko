/* Any copyright is dedicated to the Public Domain.
   http://creativecommons.org/publicdomain/zero/1.0/ */

/**
 * Tests that we exit search mode when the search mode engine is removed.
 */

"use strict";

add_task(async function init() {
  await SpecialPowers.pushPrefEnv({
    set: [
      ["browser.urlbar.update2", true],
      ["browser.urlbar.update2.oneOffsRefresh", true],
    ],
  });
});

// Tests that we exit search mode in the active tab when the search mode engine
// is removed.
add_task(async function activeTab() {
  let engine = await Services.search.addEngineWithDetails("Test", {
    template: "http://example.com/?search={searchTerms}",
  });
  await Services.search.moveEngine(engine, 0);

  await UrlbarTestUtils.promiseAutocompleteResultPopup({
    window,
    value: "ex",
  });
  await UrlbarTestUtils.enterSearchMode(window);
  // Sanity check: we are in the correct search mode.
  await UrlbarTestUtils.assertSearchMode(window, {
    engineName: engine.name,
    entry: "oneoff",
  });
  await Services.search.removeEngine(engine);
  // Check that we are no longer in search mode.
  await UrlbarTestUtils.assertSearchMode(window, null);
});

// Tests that we exit search mode in a background tab when the search mode
// engine is removed.
add_task(async function backgroundTab() {
  let engine = await Services.search.addEngineWithDetails("Test", {
    template: "http://example.com/?search={searchTerms}",
  });
  await Services.search.moveEngine(engine, 0);

  await UrlbarTestUtils.promiseAutocompleteResultPopup({
    window,
    value: "ex",
  });
  await UrlbarTestUtils.enterSearchMode(window);
  let tab1 = gBrowser.selectedTab;
  let tab2 = await BrowserTestUtils.openNewForegroundTab(gBrowser);

  // Sanity check: tab1 is still in search mode.
  await BrowserTestUtils.switchTab(gBrowser, tab1);
  await UrlbarTestUtils.assertSearchMode(window, {
    engineName: engine.name,
    entry: "oneoff",
  });

  // Switch back to tab2 so tab1 is in the background when the engine is
  // removed.
  await BrowserTestUtils.switchTab(gBrowser, tab2);
  // tab2 shouldn't be in search mode.
  await UrlbarTestUtils.assertSearchMode(window, null);
  await Services.search.removeEngine(engine);

  // tab1 should have exited search mode.
  await BrowserTestUtils.switchTab(gBrowser, tab1);
  await UrlbarTestUtils.assertSearchMode(window, null);
  BrowserTestUtils.removeTab(tab2);
});

// Tests that we exit search mode in a background window when the search mode
// engine is removed.
add_task(async function backgroundWindow() {
  let engine = await Services.search.addEngineWithDetails("Test", {
    template: "http://example.com/?search={searchTerms}",
  });
  await Services.search.moveEngine(engine, 0);

  let win1 = window;
  await UrlbarTestUtils.promiseAutocompleteResultPopup({
    window: win1,
    value: "ex",
  });
  await UrlbarTestUtils.enterSearchMode(win1);
  let win2 = await BrowserTestUtils.openNewBrowserWindow();

  // Sanity check: win1 is still in search mode.
  win1.focus();
  await UrlbarTestUtils.assertSearchMode(win1, {
    engineName: engine.name,
    entry: "oneoff",
  });

  // Switch back to win2 so win1 is in the background when the engine is
  // removed.
  win2.focus();
  // win2 shouldn't be in search mode.
  await UrlbarTestUtils.assertSearchMode(win2, null);
  await Services.search.removeEngine(engine);

  // win1 should not be in search mode.
  win1.focus();
  await UrlbarTestUtils.assertSearchMode(win1, null);
  await BrowserTestUtils.closeWindow(win2);
});
