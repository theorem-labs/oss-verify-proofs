(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 554 of its 593 lines of code are new or changed and 357 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F7.v; 14 of its 49 lines of code are new or changed and 558 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F7F.v, with its module names and addresses changed; 6 of its 35 lines of code are new or changed and 20 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17; measured against this image only;
   source runs: lib/B/Prog/Seg/F8.v f8_evt (:301) at a working branch 3803efccea0
     (blob b165baee6c1e379a3efa10590bb71761c711c93f);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   split: f8_evt calls reac_ctrl_kind_name at 0x8217c (parent 23:50Z: split at EVERY call, never state a callee
     contract locally).  f8_pre_F re-runs F8.v lines 324-327 (0x82174 -> the callee entry 0x83d98, ra = 0x82180);
     the callee's return pc 0x82180 IS the run's exit cut (Inv_B82180_at), so the post stretch is empty and no
     f8_post_F exists: the walk composes reac_ctrl_kind_name itself and lands on f8_evt's own Q.
   compare: no <run>_of_F (the source statement f8_evt runs through the callee; the split stretch is cited above). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot F8.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11.
Open Scope Z_scope.

(* The footprint twin of F8's run 0x82174 -> 0x8217c (up to the reac_ctrl_kind_name entry 0x83d98): the branch to
   the fail block not taken and the argument move.  The stretch touches no memory at all (no load, no store, no
   instrumented check), so it carries no rng premise. *)
Lemma f8_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z),
    bv_eqb a0 (Z_to_bv 64 0) = false -> s8v = Z_to_bv 64 v ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82180) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v)
                              a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 0x83d98) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82174) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m v Hnz ->.
  (* 0x82174 beqz a0 : a0 <> 0, not taken *)
  step. rewrite Hnz. cbv iota.
  (* 0x82178 mv a0,s8 ; 0x8217c jal reac_ctrl_kind_name *)
  step. step.
  apply evtF_done. reflexivity.
Qed.
