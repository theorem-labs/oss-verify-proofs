(* identb_prog_sig_ok for fuzz_identity.asan-ubsan: every program function's call name is its start, BASE + AF_<f>, in the image
   instance PI_identb. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSyms IdentBList IdentBPa IdentBImg IdentBProgSig.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma identb_prog_sig : identb_prog_sig_ok (PI:=PI_identb).
Proof. intros s af H. destruct s; cbn in H; try discriminate H; injection H as <-; vm_compute; reflexivity. Qed.
End a.
