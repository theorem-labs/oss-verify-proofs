(* Theorem Labs, 2026-10: fuzz_decode image B (asan-ubsan), the fact behind lib/B/DecodeBClose.v's Hypothesis
   H_CALLOC_TP (`as_tp B = DEC_B_TP`), proved by computation from image B's symbol record TfibSyms (lib/B/YF0m.v):
   ts_tp gives as_tp B = TFIB_TP = 0x5d42d8, and DEC_B_TP = DEC_B_builtin_tls + PTHREAD_SIZE = 0x5d4210 + 200 = 0x5d42d8
   (lib/A/DecodeCallocRt.v).  The same fact at image B's own record TfibB (lib/B/YD2l.v, TfibB_syms).
   Rule 24: no function is proved here; both lemmas are instance facts. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YF0m YD2l.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCallocRt.
Open Scope Z_scope.

Lemma H_CALLOC_TP_holds : forall B, TfibSyms B -> as_tp B = DEC_B_TP.
Proof.
  intros B HB. rewrite (ts_tp B HB).
  unfold TFIB_TP, DEC_B_TP, DEC_B_builtin_tls, PTHREAD_SIZE. reflexivity.
Qed.

Lemma H_CALLOC_TP_TfibB : as_tp TfibB = DEC_B_TP.
Proof. exact (H_CALLOC_TP_holds TfibB TfibB_syms). Qed.
