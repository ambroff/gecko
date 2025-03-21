/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*- */
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef __LookAndFeel
#define __LookAndFeel

#ifndef MOZILLA_INTERNAL_API
#  error "This header is only usable from within libxul (MOZILLA_INTERNAL_API)."
#endif

#include "nsDebug.h"
#include "nsColor.h"
#include "nsString.h"
#include "nsTArray.h"
#include "mozilla/widget/ThemeChangeKind.h"

struct gfxFontStyle;

struct LookAndFeelCache;

namespace mozilla {

enum class StyleSystemColor : uint8_t;

class LookAndFeel {
 public:
  using ColorID = StyleSystemColor;

  // When modifying this list, also modify nsXPLookAndFeel::sIntPrefs
  // in widget/xpwidgts/nsXPLookAndFeel.cpp.
  enum class IntID {
    // default, may be overriden by OS
    CaretBlinkTime,
    // pixel width of caret
    CaretWidth,
    // show the caret when text is selected?
    ShowCaretDuringSelection,
    // select textfields when focused via tab/accesskey?
    SelectTextfieldsOnKeyFocus,
    // delay before submenus open
    SubmenuDelay,
    // can popups overlap menu/task bar?
    MenusCanOverlapOSBar,
    // should overlay scrollbars be used?
    UseOverlayScrollbars,
    // allow H and V overlay scrollbars to overlap?
    AllowOverlayScrollbarsOverlap,
    // show/hide scrollbars based on activity
    ShowHideScrollbars,
    // skip navigating to disabled menu item?
    SkipNavigatingDisabledMenuItem,
    // begin a drag if the mouse is moved further than the threshold while the
    // button is down
    DragThresholdX,
    DragThresholdY,
    // Accessibility theme being used?
    UseAccessibilityTheme,

    // position of scroll arrows in a scrollbar
    ScrollArrowStyle,
    // is scroll thumb proportional or fixed?
    ScrollSliderStyle,

    // each button can take one of four values:
    ScrollButtonLeftMouseButtonAction,
    // 0 - scrolls one  line, 1 - scrolls one page
    ScrollButtonMiddleMouseButtonAction,
    // 2 - scrolls to end, 3 - button ignored
    ScrollButtonRightMouseButtonAction,

    // delay for opening spring loaded folders
    TreeOpenDelay,
    // delay for closing spring loaded folders
    TreeCloseDelay,
    // delay for triggering the tree scrolling
    TreeLazyScrollDelay,
    // delay for scrolling the tree
    TreeScrollDelay,
    // the maximum number of lines to be scrolled at ones
    TreeScrollLinesMax,
    // What type of tab-order to use
    TabFocusModel,
    // Should menu items blink when they're chosen?
    ChosenMenuItemsShouldBlink,

    /*
     * A Boolean value to determine whether the Windows accent color
     * should be applied to the title bar.
     *
     * The value of this metric is not used on other platforms. These platforms
     * should return NS_ERROR_NOT_IMPLEMENTED when queried for this metric.
     */
    WindowsAccentColorInTitlebar,

    /*
     * A Boolean value to determine whether the Windows default theme is
     * being used.
     *
     * The value of this metric is not used on other platforms. These platforms
     * should return NS_ERROR_NOT_IMPLEMENTED when queried for this metric.
     */
    WindowsDefaultTheme,

    /*
     * A Boolean value to determine whether the DWM compositor is being used
     *
     * This metric is not used on non-Windows platforms. These platforms
     * should return NS_ERROR_NOT_IMPLEMENTED when queried for this metric.
     */
    DWMCompositor,

    /*
     * A Boolean value to determine whether Windows is themed (Classic vs.
     * uxtheme)
     *
     * This is Windows-specific and is not implemented on other platforms
     * (will return the default of NS_ERROR_FAILURE).
     */
    WindowsClassic,

    /*
     * A Boolean value to determine whether the current Windows desktop theme
     * supports Aero Glass.
     *
     * This is Windows-specific and is not implemented on other platforms
     * (will return the default of NS_ERROR_FAILURE).
     */
    WindowsGlass,

    /*
     * A Boolean value to determine whether the device is a touch enabled
     * device. Currently this is only supported by the Windows 7 Touch API.
     *
     * Platforms that do not support this metric should return
     * NS_ERROR_NOT_IMPLEMENTED when queried for this metric.
     */
    TouchEnabled,

    /*
     * A Boolean value to determine whether the Mac graphite theme is
     * being used.
     *
     * The value of this metric is not used on other platforms. These platforms
     * should return NS_ERROR_NOT_IMPLEMENTED when queried for this metric.
     */
    MacGraphiteTheme,

    /*
     * A Boolean value to determine whether the Mac OS X Yosemite-specific
     * theming should be used.
     *
     * The value of this metric is not used on non-Mac platforms. These
     * platforms should return NS_ERROR_NOT_IMPLEMENTED when queried for this
     * metric.
     */
    MacYosemiteTheme,

    /*
     * AlertNotificationOrigin indicates from which corner of the
     * screen alerts slide in, and from which direction (horizontal/vertical).
     * 0, the default, represents bottom right, sliding vertically.
     * Use any bitwise combination of the following constants:
     * NS_ALERT_HORIZONTAL (1), NS_ALERT_LEFT (2), NS_ALERT_TOP (4).
     *
     *       6       4
     *     +-----------+
     *    7|           |5
     *     |           |
     *    3|           |1
     *     +-----------+
     *       2       0
     */
    AlertNotificationOrigin,

    /**
     * If true, clicking on a scrollbar (not as in dragging the thumb) defaults
     * to scrolling the view corresponding to the clicked point. Otherwise, we
     * only do so if the scrollbar is clicked using the middle mouse button or
     * if shift is pressed when the scrollbar is clicked.
     */
    ScrollToClick,

    /**
     * IME and spell checker underline styles, the values should be
     * NS_DECORATION_LINE_STYLE_*.  They are defined below.
     */
    IMERawInputUnderlineStyle,
    IMESelectedRawTextUnderlineStyle,
    IMEConvertedTextUnderlineStyle,
    IMESelectedConvertedTextUnderline,
    SpellCheckerUnderlineStyle,

    /**
     * If this metric != 0, support window dragging on the menubar.
     */
    MenuBarDrag,
    /**
     * Return the appropriate WindowsThemeIdentifier for the current theme.
     */
    WindowsThemeIdentifier,
    /**
     * Return an appropriate os version identifier.
     */
    OperatingSystemVersionIdentifier,
    /**
     * 0: scrollbar button repeats to scroll only when cursor is on the button.
     * 1: scrollbar button repeats to scroll even if cursor is outside of it.
     */
    ScrollbarButtonAutoRepeatBehavior,
    /**
     * Delay before showing a tooltip.
     */
    TooltipDelay,
    /*
     * A Boolean value to determine whether Mac OS X Lion style swipe animations
     * should be used.
     */
    SwipeAnimationEnabled,

    /*
     * Controls whether overlay scrollbars display when the user moves
     * the mouse in a scrollable frame.
     */
    ScrollbarDisplayOnMouseMove,

    /*
     * Overlay scrollbar animation constants.
     */
    ScrollbarFadeBeginDelay,
    ScrollbarFadeDuration,

    /**
     * Distance in pixels to offset the context menu from the cursor
     * on open.
     */
    ContextMenuOffsetVertical,
    ContextMenuOffsetHorizontal,

    /*
     * A boolean value indicating whether client-side decorations are
     * supported by the user's GTK version.
     */
    GTKCSDAvailable,

    /*
     * A boolean value indicating whether GTK+ system titlebar should be
     * disabled by default.
     */
    GTKCSDHideTitlebarByDefault,

    /*
     * A boolean value indicating whether client-side decorations should
     * have transparent background.
     */
    GTKCSDTransparentBackground,

    /*
     * A boolean value indicating whether client-side decorations should
     * contain a minimize button.
     */
    GTKCSDMinimizeButton,

    /*
     * A boolean value indicating whether client-side decorations should
     * contain a maximize button.
     */
    GTKCSDMaximizeButton,

    /*
     * A boolean value indicating whether client-side decorations should
     * contain a close button.
     */
    GTKCSDCloseButton,

    /*
     * A boolean value indicating whether titlebar buttons are located
     * in left titlebar corner.
     */
    GTKCSDReversedPlacement,

    /*
     * A boolean value indicating whether or not the OS is using a dark theme,
     * which we may want to switch to as well if not overridden by the user.
     */
    SystemUsesDarkTheme,

    /**
     * Corresponding to prefers-reduced-motion.
     * https://drafts.csswg.org/mediaqueries-5/#prefers-reduced-motion
     * 0: no-preference
     * 1: reduce
     */

    PrefersReducedMotion,
    /**
     * Corresponding to PointerCapabilities in ServoTypes.h
     * 0: None
     * 1: Coarse
     * 2: Fine
     * 4: Hover
     */
    PrimaryPointerCapabilities,
    /**
     * Corresponding to union of PointerCapabilities values in ServoTypes.h
     * E.g. if there is a mouse and a digitizer, the value will be
     * 'Coarse | Fine | Hover'.
     */
    AllPointerCapabilities,
    /**
     * An Integer value that will represent the position of the Close button
     * in GTK Client side decoration header. Its value will be between 0 and 2
     * if it is on the left side of the tabbar, otherwise it will be between
     * 3 and 5.
     */
    GTKCSDCloseButtonPosition,

    /**
     * An Integer value that will represent the position of the Minimize button
     * in GTK Client side decoration header. Its value will be between 0 and 2
     * if it is on the left side of the tabbar, otherwise it will be between
     * 3 and 5.
     */
    GTKCSDMinimizeButtonPosition,

    /**
     * An Integer value that will represent the position of the Maximize button
     * in GTK Client side decoration header. Its value will be between 0 and 2
     * if it is on the left side of the tabbar, otherwise it will be between
     * 3 and 5.
     */
    GTKCSDMaximizeButtonPosition,
  };

  /**
   * Windows themes we currently detect.
   */
  enum WindowsTheme {
    eWindowsTheme_Generic = 0,  // unrecognized theme
    eWindowsTheme_Classic,
    eWindowsTheme_Aero,
    eWindowsTheme_LunaBlue,
    eWindowsTheme_LunaOlive,
    eWindowsTheme_LunaSilver,
    eWindowsTheme_Royale,
    eWindowsTheme_Zune,
    eWindowsTheme_AeroLite
  };

  /**
   * Operating system versions.
   */
  enum class OperatingSystemVersion {
    Windows7 = 2,
    Windows8,
    Windows10,
    Unknown
  };

  enum {
    eScrollArrow_None = 0,
    eScrollArrow_StartBackward = 0x1000,
    eScrollArrow_StartForward = 0x0100,
    eScrollArrow_EndBackward = 0x0010,
    eScrollArrow_EndForward = 0x0001
  };

  enum {
    // single arrow at each end
    eScrollArrowStyle_Single =
        eScrollArrow_StartBackward | eScrollArrow_EndForward,
    // both arrows at bottom/right, none at top/left
    eScrollArrowStyle_BothAtBottom =
        eScrollArrow_EndBackward | eScrollArrow_EndForward,
    // both arrows at both ends
    eScrollArrowStyle_BothAtEachEnd =
        eScrollArrow_EndBackward | eScrollArrow_EndForward |
        eScrollArrow_StartBackward | eScrollArrow_StartForward,
    // both arrows at top/left, none at bottom/right
    eScrollArrowStyle_BothAtTop =
        eScrollArrow_StartBackward | eScrollArrow_StartForward
  };

  enum { eScrollThumbStyle_Normal, eScrollThumbStyle_Proportional };

  // When modifying this list, also modify nsXPLookAndFeel::sFloatPrefs
  // in widget/nsXPLookAndFeel.cpp.
  enum class FloatID {
    IMEUnderlineRelativeSize,
    SpellCheckerUnderlineRelativeSize,

    // The width/height ratio of the cursor. If used, the CaretWidth int metric
    // should be added to the calculated caret width.
    CaretAspectRatio,
  };

  // These constants must be kept in 1:1 correspondence with the
  // NS_STYLE_FONT_* system font constants.
  enum class FontID {
    Caption = 1,  // css2
    MINIMUM = Caption,
    Icon,
    Menu,
    MessageBox,
    SmallCaption,
    StatusBar,

    Window,  // css3
    Document,
    Workspace,
    Desktop,
    Info,
    Dialog,
    Button,
    PullDownMenu,
    List,
    Field,

    Tooltips,  // moz
    Widget,
    MAXIMUM = Widget,
  };

  /**
   * GetColor() return a native color value (might be overwritten by prefs) for
   * aID.  Some platforms don't return an error even if the index doesn't
   * match any system colors.  And also some platforms may initialize the
   * return value even when it returns an error.  Therefore, if you want to
   * use a color for the default value, you should use the other GetColor()
   * which returns nscolor directly.
   *
   * NOTE:
   *   ColorID::TextSelectForeground might return NS_DONT_CHANGE_COLOR.
   *   ColorID::IME* might return NS_TRANSPARENT, NS_SAME_AS_FOREGROUND_COLOR or
   *   NS_40PERCENT_FOREGROUND_COLOR.
   *   These values have particular meaning.  Then, they are not an actual
   *   color value.
   */
  static nsresult GetColor(ColorID aID, nscolor* aResult);

  /**
   * This variant of GetColor() takes an extra Boolean parameter that allows
   * the caller to ask that hard-coded color values be substituted for
   * native colors (used when it is desireable to hide system colors to
   * avoid system fingerprinting).
   */
  static nsresult GetColor(ColorID aID, bool aUseStandinsForNativeColors,
                           nscolor* aResult);

  /**
   * GetInt() and GetFloat() return a int or float value for aID.  The result
   * might be distance, time, some flags or a int value which has particular
   * meaning.  See each document at definition of each ID for the detail.
   * The result is always 0 when they return error.  Therefore, if you want to
   * use a value for the default value, you should use the other method which
   * returns int or float directly.
   */
  static nsresult GetInt(IntID aID, int32_t* aResult);
  static nsresult GetFloat(FloatID aID, float* aResult);

  static nscolor GetColor(ColorID aID, nscolor aDefault = NS_RGB(0, 0, 0)) {
    nscolor result = NS_RGB(0, 0, 0);
    if (NS_FAILED(GetColor(aID, &result))) {
      return aDefault;
    }
    return result;
  }

  static nscolor GetColorUsingStandins(ColorID aID,
                                       nscolor aDefault = NS_RGB(0, 0, 0)) {
    nscolor result = NS_RGB(0, 0, 0);
    if (NS_FAILED(GetColor(aID,
                           true,  // aUseStandinsForNativeColors
                           &result))) {
      return aDefault;
    }
    return result;
  }

  static int32_t GetInt(IntID aID, int32_t aDefault = 0) {
    int32_t result;
    if (NS_FAILED(GetInt(aID, &result))) {
      return aDefault;
    }
    return result;
  }

  static float GetFloat(FloatID aID, float aDefault = 0.0f) {
    float result;
    if (NS_FAILED(GetFloat(aID, &result))) {
      return aDefault;
    }
    return result;
  }

  /**
   * Retrieve the name and style of a system-theme font.  Returns true
   * if the system theme specifies this font, false if a default should
   * be used.  In the latter case neither aName nor aStyle is modified.
   *
   * Size of the font should be in CSS pixels, not device pixels.
   *
   * @param aID    Which system-theme font is wanted.
   * @param aName  The name of the font to use.
   * @param aStyle Styling to apply to the font.
   */
  static bool GetFont(FontID aID, nsString& aName, gfxFontStyle& aStyle);

  /**
   * GetPasswordCharacter() returns a unicode character which should be used
   * for a masked character in password editor.  E.g., '*'.
   */
  static char16_t GetPasswordCharacter();

  /**
   * If the latest character in password field shouldn't be hidden by the
   * result of GetPasswordCharacter(), GetEchoPassword() returns TRUE.
   * Otherwise, FALSE.
   */
  static bool GetEchoPassword();

  /**
   * The millisecond to mask password value.
   * This value is only valid when GetEchoPassword() returns true.
   */
  static uint32_t GetPasswordMaskDelay();

  /**
   * When system look and feel is changed, Refresh() must be called.  Then,
   * cached data would be released.
   */
  static void Refresh();

  /**
   * GTK's initialization code can't be run off main thread, call this
   * if you plan on using LookAndFeel off main thread later.
   *
   * This initialized state may get reset due to theme changes, so it
   * must be called prior to each potential off-main-thread LookAndFeel
   * call, not just once.
   */
  static void NativeInit();

  /**
   * If the implementation is caching values, these accessors allow the
   * cache to be exported and imported.
   */
  static LookAndFeelCache GetCache();
  static void SetCache(const LookAndFeelCache& aCache);
  static void NotifyChangedAllWindows(widget::ThemeChangeKind);
};

}  // namespace mozilla

struct LookAndFeelInt {
  mozilla::LookAndFeel::IntID id;
  int32_t value;
};

struct LookAndFeelFont {
  bool haveFont;
  nsString fontName;
  float pixelHeight;
  bool italic;
  bool bold;
};

struct LookAndFeelColor {
  mozilla::LookAndFeel::ColorID id;
  nscolor color;
};

struct LookAndFeelCache {
  void Clear() {
    mInts.Clear();
    mFonts.Clear();
    mColors.Clear();
  }
  nsTArray<LookAndFeelInt> mInts;
  nsTArray<LookAndFeelFont> mFonts;
  nsTArray<LookAndFeelColor> mColors;
};

// On the Mac, GetColor(ColorID::TextSelectForeground, color) returns this
// constant to specify that the foreground color should not be changed
// (ie. a colored text keeps its colors  when selected).
// Of course if other plaforms work like the Mac, they can use it too.
#define NS_DONT_CHANGE_COLOR NS_RGB(0x01, 0x01, 0x01)

// Similar with NS_DONT_CHANGE_COLOR, except NS_DONT_CHANGE_COLOR would returns
// complementary color if fg color is same as bg color.
// NS_CHANGE_COLOR_IF_SAME_AS_BG would returns
// ColorID::TextSelectForegroundCustom if fg and bg color are the same.
#define NS_CHANGE_COLOR_IF_SAME_AS_BG NS_RGB(0x02, 0x02, 0x02)

// ---------------------------------------------------------------------
//  Special colors for ColorID::IME* and ColorID::SpellCheckerUnderline
// ---------------------------------------------------------------------

// For background color only.
#define NS_TRANSPARENT NS_RGBA(0x01, 0x00, 0x00, 0x00)
// For foreground color only.
#define NS_SAME_AS_FOREGROUND_COLOR NS_RGBA(0x02, 0x00, 0x00, 0x00)
#define NS_40PERCENT_FOREGROUND_COLOR NS_RGBA(0x03, 0x00, 0x00, 0x00)

#define NS_IS_SELECTION_SPECIAL_COLOR(c)                          \
  ((c) == NS_TRANSPARENT || (c) == NS_SAME_AS_FOREGROUND_COLOR || \
   (c) == NS_40PERCENT_FOREGROUND_COLOR)

// ------------------------------------------
//  Bits for IntID::AlertNotificationOrigin
// ------------------------------------------

#define NS_ALERT_HORIZONTAL 1
#define NS_ALERT_LEFT 2
#define NS_ALERT_TOP 4

#endif /* __LookAndFeel */
