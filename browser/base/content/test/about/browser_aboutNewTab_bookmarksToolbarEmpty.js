/* Any copyright is dedicated to the Public Domain.
 * http://creativecommons.org/publicdomain/zero/1.0/ */

"use strict";

const bookmarksInfo = [
  {
    title: "firefox",
    url: "http://example.com",
  },
  {
    title: "rules",
    url: "http://example.com/2",
  },
  {
    title: "yo",
    url: "http://example.com/2",
  },
];

add_task(async function setup() {
  // Move all existing bookmarks in the Bookmarks Toolbar and
  // Other Bookmarks to the Bookmarks Menu so they don't affect
  // the visibility of the Bookmarks Toolbar. Restore them at
  // the end of the test.
  let Bookmarks = PlacesUtils.bookmarks;
  let toolbarBookmarks = [];
  let unfiledBookmarks = [];
  let guidBookmarkTuples = [
    [Bookmarks.toolbarGuid, toolbarBookmarks],
    [Bookmarks.unfiledGuid, unfiledBookmarks],
  ];
  for (let [parentGuid, arr] of guidBookmarkTuples) {
    await Bookmarks.fetch({ parentGuid }, bookmark => arr.push(bookmark));
  }
  await Promise.all(
    [...toolbarBookmarks, ...unfiledBookmarks].map(async bookmark => {
      bookmark.parentGuid = Bookmarks.menuGuid;
      return Bookmarks.update(bookmark);
    })
  );
  registerCleanupFunction(async () => {
    for (let [parentGuid, arr] of guidBookmarkTuples) {
      await Promise.all(
        arr.map(async bookmark => {
          bookmark.parentGuid = parentGuid;
          return Bookmarks.update(bookmark);
        })
      );
    }
  });
});

add_task(async function bookmarks_toolbar_shown_on_newtab() {
  for (let featureEnabled of [true, false]) {
    info(
      "Testing with the feature " + (featureEnabled ? "enabled" : "disabled")
    );
    await SpecialPowers.pushPrefEnv({
      set: [["browser.toolbars.bookmarks.2h2020", featureEnabled]],
    });
    let bookmarks = await PlacesUtils.bookmarks.insertTree({
      guid: PlacesUtils.bookmarks.toolbarGuid,
      children: bookmarksInfo,
    });
    let example = await BrowserTestUtils.openNewForegroundTab({
      gBrowser,
      opening: "https://example.com",
    });
    let newtab = await BrowserTestUtils.openNewForegroundTab({
      gBrowser,
      opening: "about:newtab",
      waitForLoad: false,
    });

    // 1: Test that the toolbar is shown in a newly opened foreground about:newtab
    if (featureEnabled) {
      await waitForBookmarksToolbarVisibility({
        visible: true,
        message: "Toolbar should be visible on newtab if enabled",
      });
    }

    // 2: Toolbar should get hidden when switching tab to example.com
    await BrowserTestUtils.switchTab(gBrowser, example);
    await waitForBookmarksToolbarVisibility({
      visible: false,
      message: "Toolbar should be hidden on example.com",
    });

    // 3: Remove all children of the Bookmarks Toolbar and confirm that
    // the toolbar should not become visible when switching to newtab
    CustomizableUI.addWidgetToArea(
      "personal-bookmarks",
      CustomizableUI.AREA_TABSTRIP
    );
    CustomizableUI.removeWidgetFromArea("import-button");
    await BrowserTestUtils.switchTab(gBrowser, newtab);
    await waitForBookmarksToolbarVisibility({
      visible: false,
      message:
        "Toolbar is not visible when there are no items in the toolbar area",
    });

    // 4: Put personal-bookmarks back in the toolbar and confirm the toolbar is visible now
    CustomizableUI.addWidgetToArea(
      "personal-bookmarks",
      CustomizableUI.AREA_BOOKMARKS
    );
    await BrowserTestUtils.switchTab(gBrowser, example);
    await BrowserTestUtils.switchTab(gBrowser, newtab);
    if (featureEnabled) {
      await waitForBookmarksToolbarVisibility({
        visible: true,
        message:
          "Toolbar should be visible with Bookmarks Toolbar Items restored",
      });
    }

    // 5: Remove all the bookmarks in the toolbar and confirm that the toolbar
    // is hidden on the New Tab now
    await PlacesUtils.bookmarks.remove(bookmarks);
    await BrowserTestUtils.switchTab(gBrowser, example);
    await BrowserTestUtils.switchTab(gBrowser, newtab);
    await waitForBookmarksToolbarVisibility({
      visible: false,
      message:
        "Toolbar is not visible when there are no items or nested bookmarks in the toolbar area",
    });

    await BrowserTestUtils.removeTab(newtab);
    await BrowserTestUtils.removeTab(example);
  }
});
