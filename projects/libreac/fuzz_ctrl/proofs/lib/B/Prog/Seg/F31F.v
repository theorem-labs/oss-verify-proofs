(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 754 of its 794 lines of code are new or changed and 356 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F31.v; 86 of its 170 lines of code are new or changed and 710 lines of the source are left out. *)
(* Footprint (ExecF.evtF) twins of the segment-F31 machine runs of lib/B/Prog/Seg/F31.v (fuzz_ctrl
   LLVMFuzzerTestOneInput, asan-ubsan image B). Bridge input for the cgif-form walk only.
   rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F31.v f31n_evt (:170), f31c_evt (:206), f31c_evt_ro (:322) at
     a working branch 3803efccea0 (blob 14939e90cc5dd7199128869f82d6a8dafeb78a8f);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f31n_evt_of_F (evtF_evt + rng_all) re-derives F31.f31n_evt verbatim. f31c_evt and f31c_evt_ro call
     wrapper_bcmp (jal at 0x82b34), so each is split: f31c_evt_pre_F re-runs F31.v:264-272 (0x82af8 up to the
     callee entry 0x42aac, ra = 0x82b38) and f31c_evt_post_F re-runs F31.v:307-315 (from the return pc 0x82b38 to
     the exit cut 0x82b38, no step); f31c_evt_ro_pre_F / f31c_evt_ro_post_F are the same split of f31c_evt_ro.
     No callee contract is stated here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcClassify RcClassifyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro F31.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.

Local Definition BCMP_WRAP_K := 4560.
Local Notation memcmp_model := SF.memcmp_model.

(* 0x82af8 with a0 = -1 (classify = None): bnez a0 is taken to 0x82b5c (F31.v:170-181). No memory access. *)
Lemma f31n_evt_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (RNG : footprint),
    a0 = Z_to_bv 64 (-1) ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) Fr (Z_to_bv 64 0x82b5c) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82af8) fc None m (seg_rom rsegs)).
Proof.
  intros. subst a0. step. try if_true. apply evtF_done. reflexivity.
Qed.

Lemma f31n_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 (-1) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) Fr (Z_to_bv 64 0x82b5c) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82af8) fc None m (seg_rom rsegs)).
Proof. intros. apply (evtF_evt rsegs RNG_all). apply f31n_evt_F. assumption. Qed.
Definition f31n_evt_src_check : ltac:(let T := type of F31.f31n_evt in exact T) := f31n_evt_of_F.

(* 0x82af8 with a0 = 0: the three byte checks of the source field (00 40 ab) are not taken, then the call
   0x82b34 jal wrapper_bcmp. This stretch stops AT the callee entry 0x42aac with ra = 0x82b38
   (F31.v:264-272; the ro twin f31c_evt_ro runs the same instructions and reads the same bytes). *)
Lemma f31c_evt_pre_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (RNG : footprint),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 216) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 264) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    rng RNG (A + 144) 8 -> rng RNG (A + 216) 8 -> rng RNG (A + 264) 8 -> rng RNG (O + 4) 3 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82b38) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                             (Z_to_bv 64 (O + 4)) (Z_to_bv 64 R) (Z_to_bv 64 6) a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x42aac) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82af8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A O R c9 c10 c11 RNG -> -> [HO0 HO1] HR0 H144 H216 H264 HBL R144 R216 R264 RO4.
  assert (HL144 : ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 (O + 4)))).
  { pose proof (bytes_at_ov_read rsegs m (A + 144) _ 0 8 H144 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL216 : ov_read_bytes rsegs m (wa (A + 216)) 8 = Some (le8 (Z_to_bv 64 O))).
  { pose proof (bytes_at_ov_read rsegs m (A + 216) _ 0 8 H216 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL264 : ov_read_bytes rsegs m (wa (A + 264)) 8 = Some (le8 (Z_to_bv 64 R))).
  { pose proof (bytes_at_ov_read rsegs m (A + 264) _ 0 8 H264 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HB4 : ov_read_bytes rsegs m (wa (O + 4)) 1 = Some [Z_to_bv 8 0]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 0 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 0) with (O + 4) in HH by lia. exact HH. }
  assert (HB5 : ov_read_bytes rsegs m (wa (O + 5)) 1 = Some [Z_to_bv 8 64]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 1 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 1) with (O + 5) in HH by lia. exact HH. }
  assert (HB6 : ov_read_bytes rsegs m (wa (O + 6)) 1 = Some [Z_to_bv 8 171]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 2 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 2) with (O + 6) in HH by lia. exact HH. }
  (* 0x82af8 bnez a0 (a0 = 0): not taken *)
  step. try if_false.
  (* 0x82afc ld a0,144(s1); lbu a0,0(a0) = 0x00; bnez a0 (to 0x82fa4): not taken *)
  step. step. step. try if_false.
  (* 0x82b08 ld a0,216(s1); lbu a0,5(a0) = 0x40; li a1,64; bne a0,a1 (to 0x82fa4): not taken *)
  step. step. step. step. try if_false.
  (* 0x82b18 ld a0,216(s1); lbu a0,6(a0) = 0xab; li a1,171; bne a0,a1 (to 0x82fa4): not taken *)
  step. step. step. step. try if_false.
  (* 0x82b28 li a2,6; ld a0,144(s1); ld a1,264(s1); jal wrapper_bcmp *)
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

Lemma f31c_evt_ro_pre_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (RNG : footprint),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 216) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 264) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    rng RNG (A + 144) 8 -> rng RNG (A + 216) 8 -> rng RNG (A + 264) 8 -> rng RNG (O + 4) 3 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82b38) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                             (Z_to_bv 64 (O + 4)) (Z_to_bv 64 R) (Z_to_bv 64 6) a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x42aac) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82af8) fc None m (seg_rom rsegs)).
Proof. intros. eapply f31c_evt_pre_F; eassumption. Qed.

(* From the return pc 0x82b38 to the exit cut 0x82b38 (F31.v:307-315): no step. The premises are the bcmp
   wrapper's post facts the proved run uses at that point. *)
Lemma f31c_evt_post_F :
  forall (ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3' t4' t5' t6' : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (A vcmp lo : Z) (RNG : footprint),
    munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
    asan_cells m' -> shadow_rw m' ->
    evtF rsegs RNG
      (fun ms' => exists (ra'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word)
                         (m'' : word -> option byte),
         ms' = MS (mkR ra'' sp gp tp t0'' t1'' t2'' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3'' t4'' t5'' t6'')
                  Fr (Z_to_bv 64 0x82b38) fc None m'' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m''
         /\ wmono rsegs m m'' /\ mem_inv rsegs m'' /\ stk rsegs m'' lo (bv_unsigned sp)
         /\ asan_cells m'' /\ shadow_rw m'')
      (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
               (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          Fr (Z_to_bv 64 0x82b38) fc None m' (seg_rom rsegs)).
Proof.
  intros ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3' t4' t5' t6' Fr fc m m' A vcmp lo RNG MU WM MI ST AC SW.
  apply evtF_done.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact AC | exact SW].
Qed.

(* The ro twin of the post (F31.v:380-386): ro_agree and ro_same in place of mem_inv, no runtime cells. *)
Lemma f31c_evt_ro_post_F :
  forall (ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3' t4' t5' t6' : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (A vcmp lo : Z) (RNG : footprint),
    munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m' ->
    wmono rsegs m m' -> ro_agree rsegs m' -> ro_same rsegs m m' -> stk rsegs m' lo (bv_unsigned sp) ->
    evtF rsegs RNG
      (fun ms' => exists (ra'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word)
                         (m'' : word -> option byte),
         ms' = MS (mkR ra'' sp gp tp t0'' t1'' t2'' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3'' t4'' t5'' t6'')
                  Fr (Z_to_bv 64 0x82b38) fc None m'' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m''
         /\ wmono rsegs m m'' /\ ro_agree rsegs m'' /\ ro_same rsegs m m''
         /\ stk rsegs m'' lo (bv_unsigned sp))
      (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
               (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          Fr (Z_to_bv 64 0x82b38) fc None m' (seg_rom rsegs)).
Proof.
  intros ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3' t4' t5' t6' Fr fc m m' A vcmp lo RNG MU WM RO RS ST.
  apply evtF_done.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO|]. split; [exact RS | exact ST].
Qed.
