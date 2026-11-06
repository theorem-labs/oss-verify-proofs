(* seg_D4 hand piece d4h_uoff: the unsigned value of an atom's offset, U E (SOff n c) = v + c, when the atom's
   value v and v + c are both in [0, 2^64). *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_D4_hand_stmt.
Open Scope Z_scope.

Lemma d4h_uoff : d4h_uoff_stmt.
Proof.
unfold d4h_uoff_stmt. intros E n c v H Hv Hc. exact (YI04.U_atom_off E n v c H Hv Hc).
Qed.

Check (d4h_uoff : d4h_uoff_stmt).
