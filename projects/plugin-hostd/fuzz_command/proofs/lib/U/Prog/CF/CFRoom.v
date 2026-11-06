From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import SlotAgree.
Local Open Scope Z_scope.

(* The agreement cap's size, until the frame's lib/AgreeCap.v CAP_AG_ge lands. The only place that computes
   CAP_AG; every bound on it in the cut-free copies is derived from this lemma by lia. *)
Lemma CAP_AG_ge : 512 <= CAP_AG.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
