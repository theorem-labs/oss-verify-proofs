(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: fuzz_ctrl's ASan+UBSan (image B) statements closed by applying the closed theorems
   named below to each other; module paths are full. *)
(* fuzz_ctrl image B (asan-ubsan build): the closed theorems of the released statements Statements.asan_ubsan_agrees and
   Statements.asan_ubsan_halts.
   rule 24: no function proved (composition only).  No Axiom, no Parameter, no Admitted, no admit.  No Section, no
   Hypothesis, no Variable, no Context.

   INGREDIENTS (all under proofs/libreac/fuzz_ctrl/):
   - lib/B/ACtlAll.v:931 ctl_lib_x_CtrlB_all (written on a working branch 40856734ff709730b1aad3c76886eacfd0aa430b):
     after End CtlAll its arguments are fx rc LS (Context, :175) and LS_LEAF (:287), the lib shape's one-leaf law; its
     conclusion is the core's lib contract at CtrlB, ameter_triv, B.ACtl.XL0, B.ACtl.XL0, 0x9f1a0, 0xa15e8.
   - lib/B/CtrlClose_B.v (a working branch a0b9549b16b590a98b566cb95f5fe70d5a4feeea, taken
     by path): ctrl_lib_x_at (:104-106, LS_LEAF -> the core's lib contract at CtrlB, ameter_triv, ctrl_XL0, ctrl_XL0,
     ctrl_RLO = 0x9f1a0, ctrl_RHI = 0xa15e8) and ctrl_TFIB_T_B_closed (:186, TFIB_T_B; after End ctrl_close_b it takes
     the Section hypothesis ctl_lib_x : forall fx rc, ctrl_lib_x_at fx rc (:132) as its argument).
   - lib/B/AsanUbsanTop.v (base a working branch bd2174446541542a3e259619ef2678c52d1883d7):
     ctrl_asan_ubsan_agrees_of_tfib (:96) and ctrl_asan_ubsan_halts_of_tfib (:112); after End b each takes the Section
     hypothesis TFIB : TFIB_T_B (:94) as its argument.
   ctrl_lib_x_closed: ctrl_lib_x_at's contract and ctl_lib_x_CtrlB_all's agree by conversion (XL0 and ctrl_XL0 are both
   fun _ => 0; the bounds are the same numerals). *)
From OSSVerify.libreac.fuzz_ctrl Require Statements.
Require
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZTraceSpec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AgreeShape
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ACtlAll
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.CtrlTFIB_B OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.CtrlClose_B
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanUbsanTop.

(* The closing's shape (B/CtrlClose_B.v LS; B/CtrlTFIB_B.v ag_shape checksum_shape). *)
Local Notation LS := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AgreeShape.ag_shape
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZTraceSpec.checksum_shape).

(* The walk top at the closing's shape: CtrlClose_B.v's ctl_lib_x, for every fx rc. *)
Lemma ctrl_lib_x_closed :
  forall (fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState)
         (rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.CtrlClose_B.ctrl_lib_x_at fx rc.
Proof.
  intros fx rc HLS.
  exact (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ACtlAll.ctl_lib_x_CtrlB_all fx rc LS HLS).
Qed.

(* The ASan+UBSan side TFIB_T_B, closed. *)
Lemma ctrl_TFIB_T_B_final : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.CtrlTFIB_B.TFIB_T_B.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.CtrlClose_B.ctrl_TFIB_T_B_closed ctrl_lib_x_closed).
Qed.

Theorem ctrl_asan_ubsan_agrees_closed : Statements.asan_ubsan_agrees.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanUbsanTop.ctrl_asan_ubsan_agrees_of_tfib
    ctrl_TFIB_T_B_final).
Qed.

Theorem ctrl_asan_ubsan_halts_closed : Statements.asan_ubsan_halts.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanUbsanTop.ctrl_asan_ubsan_halts_of_tfib
    ctrl_TFIB_T_B_final).
Qed.
