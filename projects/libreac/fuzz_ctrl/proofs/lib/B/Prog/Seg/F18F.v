(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 756 of its 937 lines of code are new or changed and 2376 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F18.v; 70 of its 133 lines of code are new or changed and 874 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F18.v f18_evt (:342), f18_evt_skip (:439) at a working branch
     3803efccea0 (blob ca8603bbf018e24b9743a220b9c834f200d5d15f);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f18_evt_skip_of_F (evtF_evt + rng_all) re-derives F18.f18_evt_skip verbatim.  f18_evt has one call
     (jal wrapper_bcmp at 0x82648), so it is split: f18_pre_F re-runs F18.v:385-393 (0x82634 -> the callee entry
     0x42aac) and f18_post_F re-runs F18.v:425-434 (the return pc 0x8264c -> the run's end, no step), with the
     bcmp wrapper post facts as premises.  f18_pre_F is taken by path from lib/B/Prog/Seg/F18F.v at dba073859bd
     and keeps its name. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* The wrapper's stack scratch (F18.v's Local Notation of bcmp_wrap_c's constant). *)
Local Notation BCMP_WRAP_K := BW.BCMP_WRAP_K.

(* The footprint twin of F18's run 0x82634 -> 0x82648 (up to the wrapper_bcmp entry 0x42aac): ld a0,272(s1) (w272 <> 0,
   the beqz falls through), li a2,6, ld a0,112(s1), mv a1,s2, jal. *)
Lemma f18_pre_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A L R w272 : Z) (RNG : footprint),
    s1v = Z_to_bv 64 A -> s2v = Z_to_bv 64 R ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 w272)) -> w272 <> 0 -> 0 <= w272 < 2 ^ 64 ->
    bytes_at rsegs m (A + 112) (le8 (Z_to_bv 64 L)) ->
    rng RNG (A + 272) 8 -> rng RNG (A + 112) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x8264c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                               (Z_to_bv 64 L) (Z_to_bv 64 R) (Z_to_bv 64 6) a3 a4 a5 a6 a7 (Z_to_bv 64 R)
                               s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          Fr (Z_to_bv 64 0x42aac) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82634) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A L R w272 RNG -> -> H272 Hw272nz Hw272b H112 R272 R112.
  assert (HL272 : ov_read_bytes rsegs m (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 w272))).
  { pose proof (bytes_at_ov_read rsegs m (A + 272) (le8 (Z_to_bv 64 w272)) 0 8 H272 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL112 : ov_read_bytes rsegs m (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 L))).
  { pose proof (bytes_at_ov_read rsegs m (A + 112) (le8 (Z_to_bv 64 L)) 0 8 H112 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step.
  step.
  replace (bv_eqb (Z_to_bv 64 w272) (Z_to_bv 64 0)) with false
    by (symmetry; apply bv_eqb_neq; intro Eq; apply Hw272nz;
        apply (f_equal bv_unsigned) in Eq; rewrite !unsigned_lit in Eq by lia; exact Eq).
  cbv iota.
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* The post half of f18_evt: from the wrapper's return pc 0x8264c there is no further instruction before the run's
   exit cut, so the run's post is the wrapper post facts themselves (F18.v:425-434).  Premises = exactly the clauses
   f18_evt reads out of BW.bcmp_wrap_contract at that point, stated over the post-call machine state. *)
Lemma f18_post_F :
  forall (ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte)
         (A R vcmp lo : Z) (RNG : footprint),
    munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
    asan_cells m' -> shadow_rw m' ->
    evtF rsegs RNG
      (fun ms' => exists (ra'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word)
                         (m'' : word -> option byte),
         ms' = MS (mkR ra'' sp gp tp t0'' t1'' t2'' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1'' a2'' a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 R) s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3'' t4'' t5'' t6'')
                  Fr (Z_to_bv 64 0x8264c) fc None m'' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m''
         /\ wmono rsegs m m'' /\ mem_inv rsegs m'' /\ stk rsegs m'' lo (bv_unsigned sp)
         /\ asan_cells m'' /\ shadow_rw m'')
      (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
               (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 R) s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3' t4' t5' t6')
          Fr (Z_to_bv 64 0x8264c) fc None m' (seg_rom rsegs)).
Proof.
  intros ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
    Fr fc m m' A R vcmp lo RNG MU WM MI ST AC SW.
  apply evtF_done.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact ST|]. split; [exact AC | exact SW].
Qed.

(* The footprint twin of F18.f18_evt_skip (the t_8819 j = false arm, 0x82634 -> 0x82abc): the run reads only the
   word [A + 272, A + 280). *)
Lemma f18_evt_skip_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (RNG : footprint),
    s1v = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 0)) ->
    rng RNG (A + 272) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                              (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 0x82abc) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82634) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A RNG -> H272 R272.
  assert (HL272 : ov_read_bytes rsegs m (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 0))).
  { pose proof (bytes_at_ov_read rsegs m (A + 272) (le8 (Z_to_bv 64 0)) 0 8 H272 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step. step.
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let v := eval vm_compute in cnd in replace cnd with v by (vm_compute; reflexivity); cbv iota
  | _ => idtac
  end.
  apply evtF_done. reflexivity.
Qed.

(* The auditor's compare lemma: f18_evt_skip_F at RNG_all is F18.f18_evt_skip verbatim. *)
Lemma f18_evt_skip_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z),
    s1v = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 0)) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                              (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 0x82abc) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82634) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A HA H272.
  apply (evtF_evt rsegs RNG_all).
  apply (f18_evt_skip_F ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A RNG_all HA H272).
  pose proof (bytes_at_bound rsegs m (A + 272) (le8 (Z_to_bv 64 0)) H272) as Hb.
  rewrite length_le8 in Hb.
  apply rng_all; lia.
Qed.
Definition f18_evt_skip_src_check : ltac:(let T := type of F18.f18_evt_skip in exact T) := f18_evt_skip_of_F.
