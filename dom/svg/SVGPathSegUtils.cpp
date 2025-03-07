/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*- */
/* vim: set ts=8 sts=2 et sw=2 tw=80: */
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "SVGPathSegUtils.h"

#include "mozilla/ArrayUtils.h"  // MOZ_ARRAY_LENGTH
#include "gfx2DGlue.h"
#include "SVGPathDataParser.h"
#include "nsTextFormatter.h"

using namespace mozilla::dom::SVGPathSeg_Binding;
using namespace mozilla::gfx;

namespace mozilla {

static const float PATH_SEG_LENGTH_TOLERANCE = 0.0000001f;
static const uint32_t MAX_RECURSION = 10;

/* static */
void SVGPathSegUtils::GetValueAsString(const float* aSeg, nsAString& aValue) {
  // Adding new seg type? Is the formatting below acceptable for the new types?
  static_assert(
      NS_SVG_PATH_SEG_LAST_VALID_TYPE == PATHSEG_CURVETO_QUADRATIC_SMOOTH_REL,
      "Update GetValueAsString for the new value.");
  static_assert(NS_SVG_PATH_SEG_MAX_ARGS == 7,
                "Add another case to the switch below.");

  uint32_t type = DecodeType(aSeg[0]);
  char16_t typeAsChar = GetPathSegTypeAsLetter(type);

  // Special case arcs:
  if (IsArcType(type)) {
    bool largeArcFlag = aSeg[4] != 0.0f;
    bool sweepFlag = aSeg[5] != 0.0f;
    nsTextFormatter::ssprintf(aValue, u"%c%g,%g %g %d,%d %g,%g", typeAsChar,
                              aSeg[1], aSeg[2], aSeg[3], largeArcFlag,
                              sweepFlag, aSeg[6], aSeg[7]);
  } else {
    switch (ArgCountForType(type)) {
      case 0:
        aValue = typeAsChar;
        break;

      case 1:
        nsTextFormatter::ssprintf(aValue, u"%c%g", typeAsChar, aSeg[1]);
        break;

      case 2:
        nsTextFormatter::ssprintf(aValue, u"%c%g,%g", typeAsChar, aSeg[1],
                                  aSeg[2]);
        break;

      case 4:
        nsTextFormatter::ssprintf(aValue, u"%c%g,%g %g,%g", typeAsChar, aSeg[1],
                                  aSeg[2], aSeg[3], aSeg[4]);
        break;

      case 6:
        nsTextFormatter::ssprintf(aValue, u"%c%g,%g %g,%g %g,%g", typeAsChar,
                                  aSeg[1], aSeg[2], aSeg[3], aSeg[4], aSeg[5],
                                  aSeg[6]);
        break;

      default:
        MOZ_ASSERT(false, "Unknown segment type");
        aValue = u"<unknown-segment-type>";
        return;
    }
  }
}

static float CalcDistanceBetweenPoints(const Point& aP1, const Point& aP2) {
  return NS_hypot(aP2.x - aP1.x, aP2.y - aP1.y);
}

static void SplitQuadraticBezier(const Point* aCurve, Point* aLeft,
                                 Point* aRight) {
  aLeft[0].x = aCurve[0].x;
  aLeft[0].y = aCurve[0].y;
  aRight[2].x = aCurve[2].x;
  aRight[2].y = aCurve[2].y;
  aLeft[1].x = (aCurve[0].x + aCurve[1].x) / 2;
  aLeft[1].y = (aCurve[0].y + aCurve[1].y) / 2;
  aRight[1].x = (aCurve[1].x + aCurve[2].x) / 2;
  aRight[1].y = (aCurve[1].y + aCurve[2].y) / 2;
  aLeft[2].x = aRight[0].x = (aLeft[1].x + aRight[1].x) / 2;
  aLeft[2].y = aRight[0].y = (aLeft[1].y + aRight[1].y) / 2;
}

static void SplitCubicBezier(const Point* aCurve, Point* aLeft, Point* aRight) {
  Point tmp;
  tmp.x = (aCurve[1].x + aCurve[2].x) / 4;
  tmp.y = (aCurve[1].y + aCurve[2].y) / 4;
  aLeft[0].x = aCurve[0].x;
  aLeft[0].y = aCurve[0].y;
  aRight[3].x = aCurve[3].x;
  aRight[3].y = aCurve[3].y;
  aLeft[1].x = (aCurve[0].x + aCurve[1].x) / 2;
  aLeft[1].y = (aCurve[0].y + aCurve[1].y) / 2;
  aRight[2].x = (aCurve[2].x + aCurve[3].x) / 2;
  aRight[2].y = (aCurve[2].y + aCurve[3].y) / 2;
  aLeft[2].x = aLeft[1].x / 2 + tmp.x;
  aLeft[2].y = aLeft[1].y / 2 + tmp.y;
  aRight[1].x = aRight[2].x / 2 + tmp.x;
  aRight[1].y = aRight[2].y / 2 + tmp.y;
  aLeft[3].x = aRight[0].x = (aLeft[2].x + aRight[1].x) / 2;
  aLeft[3].y = aRight[0].y = (aLeft[2].y + aRight[1].y) / 2;
}

static float CalcBezLengthHelper(const Point* aCurve, uint32_t aNumPts,
                                 uint32_t aRecursionCount,
                                 void (*aSplit)(const Point*, Point*, Point*)) {
  Point left[4];
  Point right[4];
  float length = 0, dist;
  for (uint32_t i = 0; i < aNumPts - 1; i++) {
    length += CalcDistanceBetweenPoints(aCurve[i], aCurve[i + 1]);
  }
  dist = CalcDistanceBetweenPoints(aCurve[0], aCurve[aNumPts - 1]);
  if (length - dist > PATH_SEG_LENGTH_TOLERANCE &&
      aRecursionCount < MAX_RECURSION) {
    aSplit(aCurve, left, right);
    ++aRecursionCount;
    return CalcBezLengthHelper(left, aNumPts, aRecursionCount, aSplit) +
           CalcBezLengthHelper(right, aNumPts, aRecursionCount, aSplit);
  }
  return length;
}

static inline float CalcLengthOfCubicBezier(const Point& aPos,
                                            const Point& aCP1,
                                            const Point& aCP2,
                                            const Point& aTo) {
  Point curve[4] = {aPos, aCP1, aCP2, aTo};
  return CalcBezLengthHelper(curve, 4, 0, SplitCubicBezier);
}

static inline float CalcLengthOfQuadraticBezier(const Point& aPos,
                                                const Point& aCP,
                                                const Point& aTo) {
  Point curve[3] = {aPos, aCP, aTo};
  return CalcBezLengthHelper(curve, 3, 0, SplitQuadraticBezier);
}

static void TraverseClosePath(const float* aArgs,
                              SVGPathTraversalState& aState) {
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    aState.length += CalcDistanceBetweenPoints(aState.pos, aState.start);
    aState.cp1 = aState.cp2 = aState.start;
  }
  aState.pos = aState.start;
}

static void TraverseMovetoAbs(const float* aArgs,
                              SVGPathTraversalState& aState) {
  aState.start = aState.pos = Point(aArgs[0], aArgs[1]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    // aState.length is unchanged, since move commands don't affect path length.
    aState.cp1 = aState.cp2 = aState.start;
  }
}

static void TraverseMovetoRel(const float* aArgs,
                              SVGPathTraversalState& aState) {
  aState.start = aState.pos += Point(aArgs[0], aArgs[1]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    // aState.length is unchanged, since move commands don't affect path length.
    aState.cp1 = aState.cp2 = aState.start;
  }
}

static void TraverseLinetoAbs(const float* aArgs,
                              SVGPathTraversalState& aState) {
  Point to(aArgs[0], aArgs[1]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    aState.length += CalcDistanceBetweenPoints(aState.pos, to);
    aState.cp1 = aState.cp2 = to;
  }
  aState.pos = to;
}

static void TraverseLinetoRel(const float* aArgs,
                              SVGPathTraversalState& aState) {
  Point to = aState.pos + Point(aArgs[0], aArgs[1]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    aState.length += CalcDistanceBetweenPoints(aState.pos, to);
    aState.cp1 = aState.cp2 = to;
  }
  aState.pos = to;
}

static void TraverseLinetoHorizontalAbs(const float* aArgs,
                                        SVGPathTraversalState& aState) {
  Point to(aArgs[0], aState.pos.y);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    aState.length += std::fabs(to.x - aState.pos.x);
    aState.cp1 = aState.cp2 = to;
  }
  aState.pos = to;
}

static void TraverseLinetoHorizontalRel(const float* aArgs,
                                        SVGPathTraversalState& aState) {
  aState.pos.x += aArgs[0];
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    aState.length += std::fabs(aArgs[0]);
    aState.cp1 = aState.cp2 = aState.pos;
  }
}

static void TraverseLinetoVerticalAbs(const float* aArgs,
                                      SVGPathTraversalState& aState) {
  Point to(aState.pos.x, aArgs[0]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    aState.length += std::fabs(to.y - aState.pos.y);
    aState.cp1 = aState.cp2 = to;
  }
  aState.pos = to;
}

static void TraverseLinetoVerticalRel(const float* aArgs,
                                      SVGPathTraversalState& aState) {
  aState.pos.y += aArgs[0];
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    aState.length += std::fabs(aArgs[0]);
    aState.cp1 = aState.cp2 = aState.pos;
  }
}

static void TraverseCurvetoCubicAbs(const float* aArgs,
                                    SVGPathTraversalState& aState) {
  Point to(aArgs[4], aArgs[5]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    Point cp1(aArgs[0], aArgs[1]);
    Point cp2(aArgs[2], aArgs[3]);
    aState.length += (float)CalcLengthOfCubicBezier(aState.pos, cp1, cp2, to);
    aState.cp2 = cp2;
    aState.cp1 = to;
  }
  aState.pos = to;
}

static void TraverseCurvetoCubicSmoothAbs(const float* aArgs,
                                          SVGPathTraversalState& aState) {
  Point to(aArgs[2], aArgs[3]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    Point cp1 = aState.pos - (aState.cp2 - aState.pos);
    Point cp2(aArgs[0], aArgs[1]);
    aState.length += (float)CalcLengthOfCubicBezier(aState.pos, cp1, cp2, to);
    aState.cp2 = cp2;
    aState.cp1 = to;
  }
  aState.pos = to;
}

static void TraverseCurvetoCubicRel(const float* aArgs,
                                    SVGPathTraversalState& aState) {
  Point to = aState.pos + Point(aArgs[4], aArgs[5]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    Point cp1 = aState.pos + Point(aArgs[0], aArgs[1]);
    Point cp2 = aState.pos + Point(aArgs[2], aArgs[3]);
    aState.length += (float)CalcLengthOfCubicBezier(aState.pos, cp1, cp2, to);
    aState.cp2 = cp2;
    aState.cp1 = to;
  }
  aState.pos = to;
}

static void TraverseCurvetoCubicSmoothRel(const float* aArgs,
                                          SVGPathTraversalState& aState) {
  Point to = aState.pos + Point(aArgs[2], aArgs[3]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    Point cp1 = aState.pos - (aState.cp2 - aState.pos);
    Point cp2 = aState.pos + Point(aArgs[0], aArgs[1]);
    aState.length += (float)CalcLengthOfCubicBezier(aState.pos, cp1, cp2, to);
    aState.cp2 = cp2;
    aState.cp1 = to;
  }
  aState.pos = to;
}

static void TraverseCurvetoQuadraticAbs(const float* aArgs,
                                        SVGPathTraversalState& aState) {
  Point to(aArgs[2], aArgs[3]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    Point cp(aArgs[0], aArgs[1]);
    aState.length += (float)CalcLengthOfQuadraticBezier(aState.pos, cp, to);
    aState.cp1 = cp;
    aState.cp2 = to;
  }
  aState.pos = to;
}

static void TraverseCurvetoQuadraticSmoothAbs(const float* aArgs,
                                              SVGPathTraversalState& aState) {
  Point to(aArgs[0], aArgs[1]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    Point cp = aState.pos - (aState.cp1 - aState.pos);
    aState.length += (float)CalcLengthOfQuadraticBezier(aState.pos, cp, to);
    aState.cp1 = cp;
    aState.cp2 = to;
  }
  aState.pos = to;
}

static void TraverseCurvetoQuadraticRel(const float* aArgs,
                                        SVGPathTraversalState& aState) {
  Point to = aState.pos + Point(aArgs[2], aArgs[3]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    Point cp = aState.pos + Point(aArgs[0], aArgs[1]);
    aState.length += (float)CalcLengthOfQuadraticBezier(aState.pos, cp, to);
    aState.cp1 = cp;
    aState.cp2 = to;
  }
  aState.pos = to;
}

static void TraverseCurvetoQuadraticSmoothRel(const float* aArgs,
                                              SVGPathTraversalState& aState) {
  Point to = aState.pos + Point(aArgs[0], aArgs[1]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    Point cp = aState.pos - (aState.cp1 - aState.pos);
    aState.length += (float)CalcLengthOfQuadraticBezier(aState.pos, cp, to);
    aState.cp1 = cp;
    aState.cp2 = to;
  }
  aState.pos = to;
}

static void TraverseArcAbs(const float* aArgs, SVGPathTraversalState& aState) {
  Point to(aArgs[5], aArgs[6]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    float dist = 0;
    Point radii(aArgs[0], aArgs[1]);
    if (radii.x == 0.0f || radii.y == 0.0f) {
      dist = CalcDistanceBetweenPoints(aState.pos, to);
    } else {
      Point bez[4] = {aState.pos, Point(0, 0), Point(0, 0), Point(0, 0)};
      SVGArcConverter converter(aState.pos, to, radii, aArgs[2], aArgs[3] != 0,
                                aArgs[4] != 0);
      while (converter.GetNextSegment(&bez[1], &bez[2], &bez[3])) {
        dist += CalcBezLengthHelper(bez, 4, 0, SplitCubicBezier);
        bez[0] = bez[3];
      }
    }
    aState.length += dist;
    aState.cp1 = aState.cp2 = to;
  }
  aState.pos = to;
}

static void TraverseArcRel(const float* aArgs, SVGPathTraversalState& aState) {
  Point to = aState.pos + Point(aArgs[5], aArgs[6]);
  if (aState.ShouldUpdateLengthAndControlPoints()) {
    float dist = 0;
    Point radii(aArgs[0], aArgs[1]);
    if (radii.x == 0.0f || radii.y == 0.0f) {
      dist = CalcDistanceBetweenPoints(aState.pos, to);
    } else {
      Point bez[4] = {aState.pos, Point(0, 0), Point(0, 0), Point(0, 0)};
      SVGArcConverter converter(aState.pos, to, radii, aArgs[2], aArgs[3] != 0,
                                aArgs[4] != 0);
      while (converter.GetNextSegment(&bez[1], &bez[2], &bez[3])) {
        dist += CalcBezLengthHelper(bez, 4, 0, SplitCubicBezier);
        bez[0] = bez[3];
      }
    }
    aState.length += dist;
    aState.cp1 = aState.cp2 = to;
  }
  aState.pos = to;
}

using TraverseFunc = void (*)(const float*, SVGPathTraversalState&);

static TraverseFunc gTraverseFuncTable[NS_SVG_PATH_SEG_TYPE_COUNT] = {
    nullptr,  //  0 == PATHSEG_UNKNOWN
    TraverseClosePath,
    TraverseMovetoAbs,
    TraverseMovetoRel,
    TraverseLinetoAbs,
    TraverseLinetoRel,
    TraverseCurvetoCubicAbs,
    TraverseCurvetoCubicRel,
    TraverseCurvetoQuadraticAbs,
    TraverseCurvetoQuadraticRel,
    TraverseArcAbs,
    TraverseArcRel,
    TraverseLinetoHorizontalAbs,
    TraverseLinetoHorizontalRel,
    TraverseLinetoVerticalAbs,
    TraverseLinetoVerticalRel,
    TraverseCurvetoCubicSmoothAbs,
    TraverseCurvetoCubicSmoothRel,
    TraverseCurvetoQuadraticSmoothAbs,
    TraverseCurvetoQuadraticSmoothRel};

/* static */
void SVGPathSegUtils::TraversePathSegment(const float* aData,
                                          SVGPathTraversalState& aState) {
  static_assert(
      MOZ_ARRAY_LENGTH(gTraverseFuncTable) == NS_SVG_PATH_SEG_TYPE_COUNT,
      "gTraverseFuncTable is out of date");
  uint32_t type = DecodeType(aData[0]);
  gTraverseFuncTable[type](aData + 1, aState);
}

}  // namespace mozilla
