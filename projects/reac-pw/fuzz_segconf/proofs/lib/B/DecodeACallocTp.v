(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/DecodeACallocTp.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B; lib/Lib/DecodeCallocKit.v to its image-B copy lib/B/DecodeCallocKit.v) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* Theorem Labs, 2026-10: fuzz_decode image A, the fact behind lib/A/DecodeClose.v's Hypothesis H_CALLOC_TP
   (`as_tp B = DEC_A_TP`), proved by computation from image A's symbol record GrantSyms (lib/A/AF0m.v):
   ts_tp gives as_tp B = TFIB_TP = 0x5d3d58, and DEC_A_TP = DEC_A_builtin_tls + PTHREAD_SIZE = 0x5d3c90 + 200 = 0x5d3d58
   (lib/A/DecodeCallocRt.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YF0m DecodeCallocRt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import DecodeCallocKit.
Open Scope Z_scope.

Lemma H_CALLOC_TP_holds : forall B : asyms, SegBSyms B -> as_tp B = DEC_A_TP.
Proof.
  intros B HB. rewrite (@ts_tp B HB).
  unfold TFIB_TP, DEC_A_TP, DEC_A_builtin_tls, PTHREAD_SIZE. reflexivity.
Qed.
