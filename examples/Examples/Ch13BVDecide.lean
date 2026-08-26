import SubVerso.Examples
import Std.Tactic.BVDecide

namespace tacticbook_bvdecide

-- ANCHOR: bv_normalization_only
theorem bvNormalizationOnly (x : BitVec 8) : x + 0 = x := by
  bv_decide
-- ANCHOR_END: bv_normalization_only

-- ANCHOR: bv_full_pipeline
set_option trace.Meta.Tactic.bv true in
set_option trace.Meta.Tactic.sat true in
theorem bvFullPipeline (x y : BitVec 8) : x * y = y * x := by
  bv_decide
-- ANCHOR_END: bv_full_pipeline

-- ANCHOR: bv_small_preprocessed
theorem bvSmallAdderPreprocessed (x y : BitVec 4) : x + y = y + x := by
  bv_decide
-- ANCHOR_END: bv_small_preprocessed

-- ANCHOR: bv_offline_replay
set_option sat.solver "/definitely/not/a/solver" in
theorem bvOfflineReplay (x y : BitVec 4) : x * y = y * x := by
  bv_check (binaryProofs := false) "Fixtures/ch13-mul4.lrat"

#print axioms bvOfflineReplay
-- ANCHOR_END: bv_offline_replay

-- ANCHOR: bv_reject_bad_certificates
/--
error: SAT solver produced invalid LRAT: offset 0: digit expected
-/
#guard_msgs in
example (x y : BitVec 4) : x * y = y * x := by
  bv_check (binaryProofs := false) "Fixtures/ch13-malformed.lrat"

/--
error: Tactic `bv_decide` failed: The LRAT certificate could not be verified; evaluating the following term returned `false`:
  Std.Tactic.BVDecide.Reflect.verifyBVExpr _example._expr_def_1 _example._cert_def_1
-/
#guard_msgs in
example (x y : BitVec 4) : x * y = y * x := by
  bv_check (binaryProofs := false) "Fixtures/ch13-invalid-proof.lrat"
-- ANCHOR_END: bv_reject_bad_certificates

-- ANCHOR: bv_axiom_probe
#print axioms bvNormalizationOnly
#print axioms bvFullPipeline
#print axioms bvSmallAdderPreprocessed
-- ANCHOR_END: bv_axiom_probe

end tacticbook_bvdecide
