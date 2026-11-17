import Megaera
import Lean

/-! Run with `lake env lean Audit.lean` after `lake build`.
Check every theorem declaration in the project, including private lemmas
and generated equations, against Lean's three standard logical axioms.
Hypotheses of conditional theorems are part of their types, visible in the
checks below. Compiler-generated runtime code is outside the proof audit. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut roots := #[`Megaera.Paper.Theorem_1_10, `Megaera.Paper.Theorem_1_12]
  let mut modules := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if Name.isPrefixOf `Megaera mod then
      modules := modules + 1
      for decl in data.constants do
        if decl.isTheorem then roots := roots.push decl.name
  if modules < 2 then throwError "The project modules were not found"
  let (_, state) := ((roots.forM CollectAxioms.collect).run env).run {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for ax in state.axioms do
    unless allowed.contains ax do throwError "Unexpected axiom {ax}"
  logInfo m!"Checked theorem dependencies in {modules} project modules. Logical axioms used: {state.axioms.qsort Name.lt}."

#check Megaera.Finite.diamond_integer
#check Megaera.Finite.unrestricted_diamond_implies_one_eq_zero
#check Megaera.BinaryOperators.bcp_pair_from_factors
#check Megaera.ScalarKernel.coefficient_kernel_iff_at_weight
#check Megaera.Singletons.rowSpan_prepend_one_iff
#check Megaera.Convolution.theorem_2_11
#check Megaera.BCPRows.bcp_in_H_ker_L
#check Megaera.CoordinateKernel.H_kernel_generated
#check Megaera.SectionThreeSpaces.projection_kernel
#check Megaera.RowEvaluation.theorem_1_10_from_rows
#check Megaera.TTSpanning.canonical_spanning_of_theorem_1_2
#check Megaera.SingletonClosure.lemma_2_14_ii
#check Megaera.CompletenessProof.kerH_image
#check Megaera.CompletenessProof.theorem_1_10
#check Megaera.SectionThreeSpaces.dimension_from_spaces
#check Megaera.RevisedProducts.theorem_1_5
#check Megaera.RevisionTwo.theorem_1_10
#check Megaera.FourReduction.legal_iff_shape
#check Megaera.FourReduction.normalize
#check Megaera.FourCases.case_I_coefficient
#check Megaera.FourBoundary.case_II_bounds
#check Megaera.FourLambda.tuple_cancellations
#check Megaera.FourInvariant.typeIII_obstruction
#check Megaera.RevisionTwo.page_24_obstruction
#check Megaera.RevisionTwo.obstruction_outside_image
#check Megaera.FourReduction.completeness_at_weight
#check Megaera.FourCaseIProof.case_I_survives
#check Megaera.FourReduction.section_four_at_weight
#check Megaera.RevisionFour.shorter_stem_value
#check Megaera.RevisionFour.shorter_stem_obstruction
#check Megaera.RevisionFour.shorter_stem_outside_image
#check Megaera.RevisionFour.selected_row_reduced
#check Megaera.Rev4Indices.transfers_wellFounded
#check Megaera.Rev4Indices.typeIII_terminal_second_zero
#check Megaera.Rev4Selection.bounds_of_reduced
#check Megaera.Rev4Readout.initial_sum
#check Megaera.Rev4Survival.special_zero
#check Megaera.Rev4Completeness.case_II_survives
#check Megaera.Rev4Completeness.theorem_1_10
#check Megaera.Rev4Completeness.theorem_1_10_from_binary

/-! Independence of the Section 4 deduction is checked on its transitive
proof dependencies, down to private declarations. The tests above also
elaborate the input hypotheses of the alternative binary-lift statement. -/
run_cmd do
  let env ← getEnv
  let (_, state) := ((CollectAxioms.collect `Megaera.EditionOneFour.theorem_1_10).run env).run {}
  let excluded := #[
    `Megaera.FinalKernelL.theorem_2_13, `Megaera.FinalKernelL.H_ker_L_in_bcp,
    `Megaera.FinalKernelH.theorem_2_17, `Megaera.FinalBinary.theorem_1_10_section_two,
    `Megaera.BCPRows.bcp_in_H_ker_L, `Megaera.BCPRows.generator_mem, `Megaera.BCPRows.primitive_mem,
    `Megaera.HKernelPivot.kernel_from_reflection, `Megaera.SingletonClosure.lemma_2_14_ii,
    `Megaera.CompletenessProof.kerH_image, `Megaera.CompletenessProof.theorem_1_10,
    `Megaera.RowEvaluation.completeness_from_row_identity, `Megaera.RowEvaluation.theorem_1_10_from_rows,
    `Megaera.Paper.completeness_at_weight, `Megaera.RevisionTwo.theorem_1_10,
    `Megaera.Rev4Completeness.theorem_1_10, `Megaera.FinalBinary.theorem_1_10_section_four]
  for decl in excluded do
    unless env.contains decl do throwError "Unknown dependency checked by the Section 4 audit: {decl}"
    if state.visited.contains decl then throwError "Earlier kernel-image or completeness proof used: {decl}"
  for decl in #[`Megaera.EditionOneFour.least_steps_end, `Megaera.Rev4Completeness.case_II_survives,
      `Megaera.Rev4Readout.initial_sum,
      `Megaera.Rev4Survival.special_zero, `Megaera.FourCaseIProof.case_I_survives] do
    unless state.visited.contains decl do throwError "Missing Section 4 proof dependency: {decl}"
  logInfo "Verified that the Section 4 theorem uses both case proofs and excludes the earlier kernel-image and completeness theorems."

#check Megaera.FinalBinary.lemma_2_1_constants
#check Megaera.FinalBinary.theorem_2_2
#check Megaera.FinalBinary.lifted_row_identity
#check Megaera.FinalInduction.lemma_2_6
#check Megaera.FinalInduction.theorem_2_7
#check Megaera.FinalCanonical.theorem_2_8
#check Megaera.FinalOperatorSpan.corollary_2_12
#check Megaera.FinalKernelL.theorem_2_13
#check Megaera.FinalBlocks.exists_blocks_2_10
#check Megaera.FinalDecomposition.nonunique_2_10
#check Megaera.FinalDecomposition.terminal_multiple
#check Megaera.FinalKernelH.theorem_2_17
#check Megaera.FinalKernelH.read_iff_marked
#check Megaera.FinalBinary.theorem_1_10_section_two
#check Megaera.FinalBinary.theorem_1_10_section_four
#check Megaera.FinalRemarkBPrimitives.remark_1_11
#check Megaera.FinalFixedSpan.fixed_iff_prefixed
#check Megaera.FinalValueSpace.value_rank_nullity
#check Megaera.FinalValueSpace.value_dimension_from_series
#check Megaera.FinalDegreeOne.fundamental_row
#check Megaera.FinalDegreeOne.lemma_3_1
#check Megaera.FinalCor32.corollary_3_2
#check Megaera.FinalFixedRanks.theorem_3_3_R
#check Megaera.FinalFixedRanks.theorem_3_3_U
#check Megaera.FinalQuotientSpaces.quotient_linear_isomorphism
#check Megaera.FinalQuotientRank.lemma_3_4
#check Megaera.FinalDimension.theorem_1_12
#check Megaera.FinalDimension.relation_dimension_at
#check Megaera.FinalDimension.first_relation_dimension
#check Megaera.FinalValueSpace.value_generating_series
#check Megaera.EditionOneSectionTwo.signed_normal_form
#check Megaera.EditionOneSectionTwo.positive_remainder_unique
#check Megaera.EditionOneSectionTwo.image_sectionRows
#check Megaera.EditionOneSectionTwo.image_sectionRows_field
#check Megaera.EditionOneSectionTwo.commuting_double_split
#check Megaera.EditionOneSectionTwo.equation_2_4_split
#check Megaera.EditionOneSectionTwo.equation_2_4_terminal
#check Megaera.EditionOneCarry.lemma_1_8
#check Megaera.EditionOneCarry.remark_2_14
#check Megaera.EditionOneCarry.relation_iff_carry
#check Megaera.EditionOneThree.theorem_3_3_R
#check Megaera.EditionOneThree.theorem_3_3_U
#check Megaera.EditionOneThree.theorem_1_12
#check Megaera.EditionOneFour.case_II_pivot_depth
#check Megaera.EditionOneFour.theorem_1_10
#check Megaera.EditionOneZeta.elements_spec
#check Megaera.EditionOneZeta.zeta_completeness
#check Megaera.EditionOneZeta.transfer_basis
#check Megaera.EditionOneZeta.zeta_relation_dimension
#check Megaera.EditionOneZeta.zeta_value_series

run_cmd do
  let env ← getEnv
  let (_, carry) := ((CollectAxioms.collect `Megaera.EditionOneCarry.remark_2_14).run env).run {}
  for decl in #[`Megaera.PrimitiveRows.bStar_generalP_row_certificate,
      `Megaera.Convolution.read_convolution, `Megaera.FinalKernelL.theorem_2_13] do
    unless carry.visited.contains decl do throwError "Missing quadruple-carry dependency: {decl}"
  let (_, values) := ((CollectAxioms.collect `Megaera.FinalValueSpace.value_generating_series).run env).run {}
  for decl in #[`Megaera.EditionOneThree.theorem_1_12, `Megaera.FinalValueSpace.value_rank_nullity] do
    unless values.visited.contains decl do throwError "Missing value dimension dependency: {decl}"
  let (_, zeta) := ((CollectAxioms.collect `Megaera.EditionOneZeta.zeta_relation_dimension).run env).run {}
  for decl in #[`Megaera.EditionOneZeta.transfer_basis, `Megaera.EditionOneThree.theorem_1_12] do
    unless zeta.visited.contains decl do throwError "Missing zeta relation dimension dependency: {decl}"
  logInfo "Verified the quadruple-carry span proof, the deduction of the value series, and the basis transfer for the MZV relation dimension."

run_cmd do
  let env ← getEnv
  let (_, state) := ((CollectAxioms.collect `Megaera.EditionOneThree.theorem_1_12).run env).run {}
  if state.visited.contains `Megaera.FinalDimension.theorem_1_12 then
    throwError "The revised dimension proof invokes the preceding edition's dimension formula"
  for decl in #[`Megaera.FinalRanks.ranks, `Megaera.FinalLRank.image_dimension,
      `Megaera.FinalDegreeOne.lemma_3_1, `Megaera.FinalBasisRanks.corollary_3_2,
      `Megaera.EditionOneThree.theorem_3_3_R, `Megaera.EditionOneThree.theorem_3_3_U,
      `Megaera.FinalQuotientRank.natural_rank, `Megaera.FinalQuotient.fixed_image_iff,
      `Megaera.FinalQuotientSpaces.same_profiles, `Megaera.FinalBinary.lifted_row_identity,
      `Megaera.Dimension.relation_dimension_series] do
    unless state.visited.contains decl do throwError "Missing dimension proof dependency: {decl}"
  logInfo "Verified the concrete row identity, canonical rank, fixed-space ranks, quotient ranks, and generating series in the dependency tree of Theorem 1.12."
