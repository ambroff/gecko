/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*- */
/* vim: set ts=8 sts=2 et sw=2 tw=80: */
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
#include "nsPageContentFrame.h"

#include "mozilla/PresShell.h"
#include "mozilla/StaticPrefs_layout.h"

#include "nsCSSFrameConstructor.h"
#include "nsPresContext.h"
#include "nsGkAtoms.h"
#include "nsPageSequenceFrame.h"

using namespace mozilla;

nsPageContentFrame* NS_NewPageContentFrame(PresShell* aPresShell,
                                           ComputedStyle* aStyle) {
  return new (aPresShell)
      nsPageContentFrame(aStyle, aPresShell->GetPresContext());
}

NS_IMPL_FRAMEARENA_HELPERS(nsPageContentFrame)

void nsPageContentFrame::Reflow(nsPresContext* aPresContext,
                                ReflowOutput& aReflowOutput,
                                const ReflowInput& aReflowInput,
                                nsReflowStatus& aStatus) {
  MarkInReflow();
  DO_GLOBAL_REFLOW_COUNT("nsPageContentFrame");
  DISPLAY_REFLOW(aPresContext, this, aReflowInput, aReflowOutput, aStatus);
  MOZ_ASSERT(aStatus.IsEmpty(), "Caller should pass a fresh reflow status!");
  MOZ_ASSERT(mPD, "Need a pointer to nsSharedPageData before reflow starts");

  if (GetPrevInFlow() && HasAnyStateBits(NS_FRAME_FIRST_REFLOW)) {
    nsresult rv =
        aPresContext->PresShell()->FrameConstructor()->ReplicateFixedFrames(
            this);
    if (NS_FAILED(rv)) {
      return;
    }
  }

  // Set our size up front, since some parts of reflow depend on it
  // being already set.  Note that the computed height may be
  // unconstrained; that's ok.  Consumers should watch out for that.
  nsSize maxSize(aReflowInput.ComputedWidth(), aReflowInput.ComputedHeight());
  SetSize(maxSize);

  // A PageContentFrame must always have one child: the canvas frame.
  // Resize our frame allowing it only to be as big as we are
  // XXX Pay attention to the page's border and padding...
  if (mFrames.NotEmpty()) {
    nsIFrame* frame = mFrames.FirstChild();
    WritingMode wm = frame->GetWritingMode();
    LogicalSize logicalSize(wm, maxSize);
    ReflowInput kidReflowInput(aPresContext, aReflowInput, frame, logicalSize);
    kidReflowInput.SetComputedBSize(logicalSize.BSize(wm));

    // Reflow the page content area
    // XXXdholbert It's weird that we're passing down our own aReflowOutput
    // outparam to be used for the child frame's reflow here. See bug 1655856.
    ReflowChild(frame, aPresContext, aReflowOutput, kidReflowInput, 0, 0,
                ReflowChildFlags::Default, aStatus);

    // The document element's background should cover the entire canvas, so
    // take into account the combined area and any space taken up by
    // absolutely positioned elements
    nsMargin padding(0, 0, 0, 0);

    // XXXbz this screws up percentage padding (sets padding to zero
    // in the percentage padding case)
    kidReflowInput.mStylePadding->GetPadding(padding);

    // This is for shrink-to-fit, and therefore we want to use the
    // scrollable overflow, since the purpose of shrink to fit is to
    // make the content that ought to be reachable (represented by the
    // scrollable overflow) fit in the page.
    if (frame->HasOverflowAreas()) {
      // The background covers the content area and padding area, so check
      // for children sticking outside the child frame's padding edge
      nscoord xmost = aReflowOutput.ScrollableOverflow().XMost();
      if (xmost > aReflowOutput.Width()) {
        nscoord widthToFit =
            xmost + padding.right +
            kidReflowInput.mStyleBorder->GetComputedBorderWidth(eSideRight);
        float ratio = float(maxSize.width) / widthToFit;
        NS_ASSERTION(ratio >= 0.0 && ratio < 1.0,
                     "invalid shrink-to-fit ratio");
        mPD->mShrinkToFitRatio = std::min(mPD->mShrinkToFitRatio, ratio);
      }
    }

    // Place and size the child
    FinishReflowChild(frame, aPresContext, aReflowOutput, &kidReflowInput, 0, 0,
                      ReflowChildFlags::Default);

    NS_ASSERTION(aPresContext->IsDynamic() || !aStatus.IsFullyComplete() ||
                     !frame->GetNextInFlow(),
                 "bad child flow list");
  }

  // Reflow our fixed frames
  nsReflowStatus fixedStatus;
  ReflowAbsoluteFrames(aPresContext, aReflowOutput, aReflowInput, fixedStatus);
  NS_ASSERTION(fixedStatus.IsComplete(),
               "fixed frames can be truncated, but not incomplete");

  // Return our desired size
  WritingMode wm = aReflowInput.GetWritingMode();
  aReflowOutput.ISize(wm) = aReflowInput.ComputedISize();
  if (aReflowInput.ComputedBSize() != NS_UNCONSTRAINEDSIZE) {
    aReflowOutput.BSize(wm) = aReflowInput.ComputedBSize();
  }
  FinishAndStoreOverflow(&aReflowOutput);

  if (StaticPrefs::layout_display_list_improve_fragmentation() &&
      mFrames.NotEmpty()) {
    auto* previous = static_cast<nsPageContentFrame*>(GetPrevContinuation());
    const nscoord previousPageOverflow =
        previous ? previous->mRemainingOverflow : 0;

    const nscoord overflowHeight = InkOverflowRect().YMost();
    const nscoord pageHeight = GetRect().Height();
    const nscoord currentPageOverflow = overflowHeight - pageHeight;

    nscoord remainingOverflow =
        std::max(currentPageOverflow, previousPageOverflow - pageHeight);
    if (aStatus.IsFullyComplete() && remainingOverflow > 0) {
      // If we have InkOverflow off the end of our page, then we report
      // ourselves as overflow-incomplete in order to produce an additional
      // content-less page, which we expect to draw our InkOverflow on our
      // behalf.
      aStatus.SetOverflowIncomplete();
    }

    mRemainingOverflow = std::max(remainingOverflow, 0);
  }

  NS_FRAME_SET_TRUNCATION(aStatus, aReflowInput, aReflowOutput);
}

void nsPageContentFrame::AppendDirectlyOwnedAnonBoxes(
    nsTArray<OwnedAnonBox>& aResult) {
  MOZ_ASSERT(mFrames.FirstChild(),
             "pageContentFrame must have a canvasFrame child");
  aResult.AppendElement(mFrames.FirstChild());
}

#ifdef DEBUG_FRAME_DUMP
nsresult nsPageContentFrame::GetFrameName(nsAString& aResult) const {
  return MakeFrameName(u"PageContent"_ns, aResult);
}
#endif
