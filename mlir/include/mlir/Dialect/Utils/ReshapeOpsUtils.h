//===- RehshapeOpsUtils.h - Utilities used by reshape ops --*- C++ -*------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This header file defines utilities and common canonicalization patterns for
// reshape operations.
//
//===----------------------------------------------------------------------===//

#ifndef MLIR_DIALECT_UTILS_RESHAPEOPSUTILS_H
#define MLIR_DIALECT_UTILS_RESHAPEOPSUTILS_H

#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/Support/LLVM.h"
#include "llvm/ADT/StringRef.h"

namespace mlir {

using ReassociationIndices = SmallVector<int64_t, 2>;
using ReassociationIndicesRef = ArrayRef<int64_t>;
using ReassociationExprs = SmallVector<AffineExpr, 2>;

/// Attribute name for the ArrayAttr which encodes reassociation indices.
constexpr StringRef getReassociationAttrName();

/// Compose reassociation maps that are used in pair of reshape ops where one
/// is a producer and other is the consumer. Only valid to use this method when
/// both the producer and consumer are collapsing dimensions or both are
/// expanding dimensions.
///
/// For example,
///   producerReassociation = [[0, 1], [2], [3, 4]]
///   consumerReassociation = [[0, 1], [2]]
///
/// is folded into
///
///   result = [[0, 1, 2], [3, 4]].
Optional<SmallVector<ReassociationIndices>> composeReassociationIndices(
    ArrayRef<ReassociationIndices> producerReassociations,
    ArrayRef<ReassociationIndices> consumerReassociations,
    MLIRContext *context);

/// Return the reassociations maps to use to reshape given the source type and
/// the target type when possible. Return llvm::None when this computation
/// failed.
Optional<SmallVector<ReassociationIndices>>
getReassociationIndicesForReshape(ShapedType sourceType, ShapedType targetType);

/// Return true if the reassociation specification is valid, false otherwise.
/// When false, the `invalidIndex` integer pointer is optionally filled with the
/// index of the offending reassociation map.
bool isReassociationValid(ArrayRef<AffineMap> reassociation,
                          int *invalidIndex = nullptr);

/// Parse a reshape-like op, i.e. linalg::(Tensor)ExpandShapeOp,
/// linalg::(Tensor)CollapseShapeOp.
ParseResult parseReshapeLikeOp(OpAsmParser &parser, OperationState &result);

/// Print a reshape-like op, i.e. linalg::(Tensor)ExpandShapeOp,
/// linalg::(Tensor)CollapseShapeOp.
template <typename ReshapeLikeOp>
void printReshapeOp(OpAsmPrinter &p, ReshapeLikeOp op) {
  p << op.getOperationName() << ' ' << op.src() << " [";

  llvm::interleaveComma(op.reassociation(), p, [&](const Attribute &attr) {
    p << '[';
    auto arrayAttr = attr.template cast<ArrayAttr>();
    llvm::interleaveComma(arrayAttr, p, [&](const Attribute &attr) {
      p << attr.cast<IntegerAttr>().getInt();
    });
    p << ']';
  });

  p << "] ";
  p.printOptionalAttrDict(op->getAttrs(),
                          /*elidedAttrs=*/{op.getReassociationAttrName()});
  p << ": " << op.src().getType() << " into " << op.getType();
}

template <typename ReshapeOpTy, typename InverseReshapeOpTy>
static OpFoldResult foldReshapeOp(ReshapeOpTy reshapeOp,
                                  ArrayRef<Attribute> operands) {
  // Fold producer-consumer reshape ops that where the operand type of the
  // producer is same as the return type of the consumer.
  auto reshapeSrcOp =
      reshapeOp.src().template getDefiningOp<InverseReshapeOpTy>();
  if (reshapeSrcOp && reshapeSrcOp.getSrcType() == reshapeOp.getResultType())
    return reshapeSrcOp.src();
  // Reshape of a constant can be replaced with a new constant.
  if (auto elements = operands.front().dyn_cast_or_null<DenseElementsAttr>()) {
    return elements.reshape(
        reshapeOp.getResult().getType().template cast<ShapedType>());
  }
  return nullptr;
}

/// Common verifier for reshape-like types. Fills `expandedType` and
///`collapsedType` with the proper `src` or `result` type.
template <typename Op, typename T>
static LogicalResult verifyReshapeLikeTypes(Op op, T expandedType,
                                            T collapsedType, bool isExpansion) {
  unsigned expandedRank = expandedType.getRank();
  unsigned collapsedRank = collapsedType.getRank();
  if (expandedRank < collapsedRank)
    return op.emitOpError("expected the type ")
           << expandedType
           << " to have higher rank than the type = " << collapsedType;
  if (expandedRank == 0)
    return op.emitOpError("expected non-zero memref ranks");
  if (expandedRank == collapsedRank)
    return op.emitOpError("expected to collapse or expand dims");

  if (collapsedRank == 0) {
    // If collapsed rank is 0, then expanded type must be static shaped and of
    // sizes 1.
    if (llvm::any_of(expandedType.getShape(),
                     [](int64_t dim) -> bool { return dim != 1; }))
      return op.emitOpError("invalid to reshape tensor/memref with non-unit "
                            "extent dimensions to zero-rank tensor/memref");
    return success();
  }
  if (collapsedRank != op.reassociation().size())
    return op.emitOpError("expected rank of the collapsed type(")
           << collapsedRank << ") to be the number of reassociation maps("
           << op.reassociation().size() << ")";
  auto maps = op.getReassociationMaps();
  for (auto it : llvm::enumerate(maps))
    if (it.value().getNumDims() != expandedRank)
      return op.emitOpError("expected reassociation map #")
             << it.index() << " of same rank as expanded memref("
             << expandedRank << "), but got " << it.value().getNumDims();
  int invalidIdx = 0;
  if (!isReassociationValid(maps, &invalidIdx))
    return op.emitOpError("expected reassociation map #")
           << invalidIdx << " to be valid and contiguous";
  return verifyReshapeLikeShapes(op, collapsedType, expandedType, isExpansion);
}

/// Verify that shapes of the reshaped types using following rules
/// 1) if a dimension in the collapsed type is static, then the corresponding
///    dimensions in the expanded shape should be
///    a) static
///    b) the product should be same as the collaped shape.
/// 2) if a dimension in the collaped type is dynamic, one and only one of the
///    corresponding dimensions in the expanded type should be dynamic. This
///    rule is only needed with reshape operations that are expanding.
template <typename OpTy>
static LogicalResult verifyReshapeLikeShapes(OpTy op, ShapedType collapsedType,
                                             ShapedType expandedType,
                                             bool isExpandingReshape) {
  ArrayRef<int64_t> collapsedShape = collapsedType.getShape();
  ArrayRef<int64_t> expandedShape = expandedType.getShape();
  unsigned expandedDimStart = 0;
  for (auto map : llvm::enumerate(op.getReassociationMaps())) {
    Optional<int64_t> dynamicShape;
    int64_t linearizedStaticShape = 1;
    for (auto dim : llvm::enumerate(expandedShape.slice(
             expandedDimStart, map.value().getNumResults()))) {
      if (ShapedType::isDynamic(dim.value())) {
        if (isExpandingReshape && dynamicShape) {
          return op->emitOpError("invalid to have a single dimension (")
                 << map.index() << ") expanded into multiple dynamic dims ("
                 << expandedDimStart + dynamicShape.getValue() << ","
                 << expandedDimStart + dim.index() << ")";
        }
        dynamicShape = dim.index();
      } else {
        linearizedStaticShape *= dim.value();
      }
    }
    if (dynamicShape) {
      if (!ShapedType::isDynamic(collapsedShape[map.index()])) {
        return op->emitOpError("expected dimension ")
               << map.index()
               << " of collapsed type to be dynamic since one or more of the "
                  "corresponding dimensions in the expanded type is dynamic";
      }
    } else {
      if (collapsedShape[map.index()] != linearizedStaticShape) {
        return op->emitOpError("expected dimension ")
               << map.index() << " of collapsed type to be static value of "
               << linearizedStaticShape << " ";
      }
    }
    expandedDimStart += map.value().getNumResults();
  }
  return success();
}

/// Pattern to collapse producer/consumer reshape ops that are both collapsing
/// dimensions or are both expanding dimensions.
template <typename ReshapeOpTy>
struct CollapseReshapeOps : public OpRewritePattern<ReshapeOpTy> {
  using OpRewritePattern<ReshapeOpTy>::OpRewritePattern;
  LogicalResult matchAndRewrite(ReshapeOpTy reshapeOp,
                                PatternRewriter &rewriter) const override {
    auto srcReshapeOp = reshapeOp.src().template getDefiningOp<ReshapeOpTy>();
    if (!srcReshapeOp)
      return failure();

    ShapedType resultType = reshapeOp.getResultType();
    Optional<SmallVector<ReassociationIndices>> reassociationIndices =
        composeReassociationIndices(srcReshapeOp.getReassociationIndices(),
                                     reshapeOp.getReassociationIndices(),
                                     rewriter.getContext());
    if (!reassociationIndices)
      return failure();
    rewriter.replaceOpWithNewOp<ReshapeOpTy>(
        reshapeOp, resultType, srcReshapeOp.src(), *reassociationIndices);
    return success();
  }
};

/// Pattern to collapse producer/consumer reshape ops that are both collapsing
/// dimensions or are both expanding dimensions.
template <typename ReshapeOpTy, typename InverseReshapeOpTy>
struct CollapseMixedReshapeOps : public OpRewritePattern<ReshapeOpTy> {
  using OpRewritePattern<ReshapeOpTy>::OpRewritePattern;
  LogicalResult matchAndRewrite(ReshapeOpTy reshapeOp,
                                PatternRewriter &rewriter) const override {
    auto srcReshapeOp =
        reshapeOp.src().template getDefiningOp<InverseReshapeOpTy>();
    if (!srcReshapeOp)
      return failure();

    ShapedType srcReshapeSrcType = srcReshapeOp.getSrcType();
    ShapedType intermediateType = reshapeOp.getSrcType();
    ShapedType resultType = reshapeOp.getResultType();

    // If the source reshape can be collapsed/expanded into the target reshape
    // they can still be folded. This can only be reasoned about statically
    // for cases where
    // - either all shapes are static, or
    // - The number of dynamic dimensions matches in the source of source and
    //   result with all other dimensions being 1.
    Optional<SmallVector<ReassociationIndices>> reassociationIndices =
        getReassociationIndicesForReshape(srcReshapeSrcType, resultType);
    if (!reassociationIndices)
      return failure();
    bool originalOpExpands =
        intermediateType.getRank() > srcReshapeSrcType.getRank();
    bool resultingOpExpands =
        resultType.getRank() > srcReshapeSrcType.getRank();
    if (!(resultingOpExpands ^ originalOpExpands))
      rewriter.replaceOpWithNewOp<InverseReshapeOpTy>(
          reshapeOp, resultType, srcReshapeOp.src(), *reassociationIndices);
    else
      rewriter.replaceOpWithNewOp<ReshapeOpTy>(
          reshapeOp, resultType, srcReshapeOp.src(), *reassociationIndices);
    return success();
  }
};

} // namespace mlir

#endif // MLIR_DIALECT_UTILS_RESHAPEOPSUTILS_H
