(* Theorem Labs, 2026-10: fuzz_decode image A, the fact behind lib/A/DecodeClose.v's Hypothesis H_CALLOC_TP
   (`as_tp B = DEC_A_TP`), proved by computation from image A's symbol record PcapSyms (lib/A/AF0m.v):
   ts_tp gives as_tp B = TFIB_TP = 0x631c10, and DEC_A_TP = DEC_A_builtin_tls + PTHREAD_SIZE = 0x631b48 + 200 = 0x631c10
   (lib/A/DecodeCallocRt.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m DecodeCallocRt.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import DecodeCallocKit.
Open Scope Z_scope.

Lemma H_CALLOC_TP_holds : forall B : asyms, PcapSyms B -> as_tp B = DEC_A_TP.
Proof.
  intros B HB. rewrite (@ts_tp B HB).
  unfold TFIB_TP, DEC_A_TP, DEC_A_builtin_tls, PTHREAD_SIZE. reflexivity.
Qed.
