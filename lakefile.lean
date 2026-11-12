import Lake
open Lake DSL

package nine_axiom_bz where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.20.0"

@[default_target]
lean_lib NineAxiomBZProof where
  roots := #[
    `AtomicTruthFromRelations,
    `BoundedSeparationFinalDraft,
    `BoundedZermeloReverse,
    `DeltaZeroSyntax,
    `DepthBound,
    `DiagonalFilter,
    `EquivalenceMain,
    `FamilyAtomicEdges,
    `FamilyMatchingEdges,
    `FiniteAssignmentFrame,
    `FiniteAtomicTruth,
    `FiniteFoundation,
    `FiniteFrameAllAtomic,
    `FiniteFrameCoordinateImage,
    `FiniteFrameDecoding,
    `FiniteSupport,
    `FiniteTaggedDomains,
    `FiniteTupleCoordinateLift,
    `FixedFrameCylindrification,
    `FrameAtomicBridge,
    `FreshPrefixStep,
    `FreshSupportDisjoint,
    `FreshTag,
    `FreshTupleDisjoint,
    `MainProof,
    `NineAxiomCore,
    `PrefixGraph,
    `RelationProjection,
    `TagUniqueness,
    `TaggedRawMembership,
    `TaggingGraph,
    `TypedComposition,
    `TypedCompositionFiltered,
    `TypedRelationalImage,
    `UniformBoundedTruth
  ]
