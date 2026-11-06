(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 756 of its 937 lines of code are new or changed and 2376 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F18.v; 70 of its 133 lines of code are new or changed and 874 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F18F.v, with its addresses and numbers changed; 69 of its 116 lines of code are new or changed and 86 lines of the source are left out. *)
(* Footprint (ExecF.evtF) twins of the segment-F35 machine runs of lib/B/Prog/Seg/F35.v (fuzz_ctrl
   LLVMFuzzerTestOneInput, asan-ubsan image B). Bridge input for the cgif-form walk only.
   rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F35.v f35_evt (:187), f35_evt_ro (:279) at
     a working branch 3803efccea0 (blob cc6ce088e25cd712bb2687c0f2dc8296a121ed0b);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: both runs call wrapper_bcmp (jal at 0x82c34), so each is split: f35_evt_pre_F re-runs F35.v:226-228
     (0x82c24 up to the callee entry 0x42aac, ra = 0x82c38) and f35_evt_post_F re-runs F35.v:267-271 (from the
     return pc 0x82c38 to the exit cut 0x82c38, no step); f35_evt_ro_pre_F / f35_evt_ro_post_F are the same split
     of f35_evt_ro. No callee contract is stated here, so there is no _of_F. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro F35.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

Local Definition BCMP_WRAP_K := 4560.

(* 0x82c24 beqz a0,82c5c (a0 = 1, not taken); 0x82c28 li a2,32; 0x82c2c ld a0,312(s1); 0x82c30 mv a1,s6;
   0x82c34 jal wrapper_bcmp: stops AT the callee entry 0x42aac with ra = 0x82c38 (F35.v:226-228). *)
Lemma f35_evt_pre_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A L R : Z) (RNG : footprint),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 R ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 312) (le8 (Z_to_bv 64 L)) ->
    rng RNG (A + 312) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82c38) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                             (Z_to_bv 64 L) (Z_to_bv 64 R) (Z_to_bv 64 32) a3 a4 a5 a6 a7
                             s2 s3 s4 s5 (Z_to_bv 64 R) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x42aac) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c24) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A L R RNG -> -> -> HL0 HR0 H312 R312.
  assert (HL312 : ov_read_bytes rsegs m (wa (A + 312)) 8 = Some (le8 (Z_to_bv 64 L))).
  { pose proof (bytes_at_ov_read rsegs m (A + 312) _ 0 8 H312 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step. try if_false.
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

Lemma f35_evt_ro_pre_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A L R : Z) (RNG : footprint),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 R ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 312) (le8 (Z_to_bv 64 L)) ->
    rng RNG (A + 312) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82c38) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                             (Z_to_bv 64 L) (Z_to_bv 64 R) (Z_to_bv 64 32) a3 a4 a5 a6 a7
                             s2 s3 s4 s5 (Z_to_bv 64 R) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x42aac) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c24) fc None m (seg_rom rsegs)).
Proof. intros. eapply f35_evt_pre_F; eassumption. Qed.

(* From the return pc 0x82c38 to the exit cut 0x82c38 (F35.v:267-271): no step. The premises are the bcmp
   wrapper's post facts the proved run uses at that point. *)
Lemma f35_evt_post_F :
  forall (ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s7 s8 s9 s10 s11
          t3' t4' t5' t6' : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (A R vcmp lo : Z) (RNG : footprint),
    munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
    asan_cells m' -> shadow_rw m' ->
    evtF rsegs RNG
      (fun ms' => exists (ra'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word)
                         (m'' : word -> option byte),
         ms' = MS (mkR ra'' sp gp tp t0'' t1'' t2'' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 (Z_to_bv 64 R) s7 s8 s9
                       s10 s11 t3'' t4'' t5'' t6'')
                  Fr (Z_to_bv 64 0x82c38) fc None m'' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m''
         /\ wmono rsegs m m'' /\ mem_inv rsegs m'' /\ stk rsegs m'' lo (bv_unsigned sp)
         /\ asan_cells m'' /\ shadow_rw m'')
      (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
               (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 R) s7 s8 s9 s10 s11
               t3' t4' t5' t6')
          Fr (Z_to_bv 64 0x82c38) fc None m' (seg_rom rsegs)).
Proof.
  intros ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s7 s8 s9 s10 s11
    t3' t4' t5' t6' Fr fc m m' A R vcmp lo RNG MU WM MI ST AC SW.
  apply evtF_done.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact AC | exact SW].
Qed.

(* The ro twin of the post (F35.v:298-305): ro_agree in place of mem_inv, and no runtime-cell conjuncts. *)
Lemma f35_evt_ro_post_F :
  forall (ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s7 s8 s9 s10 s11
          t3' t4' t5' t6' : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (A R vcmp lo : Z) (RNG : footprint),
    munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m' ->
    wmono rsegs m m' -> ro_agree rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
    evtF rsegs RNG
      (fun ms' => exists (ra'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word)
                         (m'' : word -> option byte),
         ms' = MS (mkR ra'' sp gp tp t0'' t1'' t2'' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 (Z_to_bv 64 R) s7 s8 s9
                       s10 s11 t3'' t4'' t5'' t6'')
                  Fr (Z_to_bv 64 0x82c38) fc None m'' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m''
         /\ wmono rsegs m m'' /\ ro_agree rsegs m'' /\ stk rsegs m'' lo (bv_unsigned sp))
      (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
               (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 R) s7 s8 s9 s10 s11
               t3' t4' t5' t6')
          Fr (Z_to_bv 64 0x82c38) fc None m' (seg_rom rsegs)).
Proof.
  intros ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s7 s8 s9 s10 s11
    t3' t4' t5' t6' Fr fc m m' A R vcmp lo RNG MU WM RO ST.
  apply evtF_done.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO | exact ST].
Qed.
