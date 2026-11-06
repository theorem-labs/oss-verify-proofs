(* seg_D4 hand d4h_kill (LLVMFuzzerTestOneInput_seg_D4_hand_stmt.v): branch_taken of BC_NE / BC_EQ / BC_LTU /
   BC_GEU over two symbolic values is the Z comparison of their unsigned values U. Each of the four is definitional
   (branch_taken unfolds to bv_eqb / bv_ltu on the two words, which compare bv_unsigned, which is U). *)
From Stdlib Require Import ZArith Bool.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0m YP0e.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_D4_hand_stmt.
Open Scope Z_scope.

Lemma d4h_kill : d4h_kill_stmt.
Proof.
unfold d4h_kill_stmt. intros E a b va vb Ha Hb. subst va vb.
split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

Check (d4h_kill : d4h_kill_stmt).
