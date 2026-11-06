(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OSSVerify.Proofs.openssl.pem.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Layout Fz_iface Driver_iface Drv_kit InitMem Fz_kit Fz_cimg Fz_I1_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Rnd.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition ERR_FNS : lh_fns := mkFns 0xe3bd0 0xe3b6c 0xe3c04 0xe3c24.
(* [comment removed for export] *)
Definition DVERR (d : Z) : Prop := forall x, d <= x < d + 16 -> cimg_addr x.

(* [comment removed for export] *)
Definition cb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition cb_arg (m : mem) (sp : word) (lo d : Z) : Prop := (exists w : word, rw_cells psegs m d [C8 w]) /\ (d + 8 <= lo \/ bv_unsigned sp <= d).

Definition lh_hash_ok (f : lh_fns) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (d lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (lf_hash f) -> cb_arg m sp lo d ->
  stk psegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv psegs m ->
  evt psegs (cb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (lf_hashw f)) fc None m (seg_rom psegs)).

Definition lh_comp_ok (f : lh_fns) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (d1 d2 lo : Z),
  a0 = Z_to_bv 64 d1 -> a1 = Z_to_bv 64 d2 -> a2 = Z_to_bv 64 (lf_comp f) -> cb_arg m sp lo d1 -> cb_arg m sp lo d2 ->
  stk psegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv psegs m ->
  evt psegs (cb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (lf_compw f)) fc None m (seg_rom psegs)).

Lemma DVERR_cell : forall m d k, cimg m -> DVERR d -> 0 <= k <= 8 -> exists w : word, rw_cells psegs m (d + k) [C8 w].
Proof. intros m d k C H Hk. apply cimg_C8; [exact C|]. intros x Hx. apply H. lia. Qed.

Lemma cb_arg_dv : forall m sp lo d, cimg m -> DVERR d -> GLOBALS_TOP <= lo -> cb_arg m sp lo d.
Proof.
  intros m sp lo d C H GLO. split.
  - destruct (DVERR_cell m d 0 C H ltac:(lia)) as [w CELL]. rewrite Z.add_0_r in CELL. exists w. exact CELL.
  - left. pose proof (H (d + 15) ltac:(lia)) as Y. unfold cimg_addr, RMallocRep.RGOT_SSP in Y. unfold GLOBALS_TOP in GLO. lia.
Qed.

Theorem err_hash_ok : lh_hash_ok ERR_FNS.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d lo A0 A1 ([w CELL] & DR) ST GLO SLO MI. subst a0 a1.
  pose proof (rw_cells_bound _ _ _ _ CELL) as DB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in DB.
  unfold ERR_FNS, lf_hash, lf_hashw, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST. do 6 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  step.
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST. do 4 step.
  assert (TAIL : forall (y11 : word) (mc : mem),
    rw_cells psegs mc (bv_unsigned sp + -16) [C8 s0; C8 ra] -> stk psegs mc lo (bv_unsigned sp + -16) ->
    munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m mc -> wmono psegs m mc -> mem_inv psegs mc ->
    evt psegs (cb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp s1 w y11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe3b94) fc None mc (seg_rom psegs))).
  { intros y11 mc FRc STc MUc WMc MIc.
    do 14 step.
    release_frame FRc STc (bv_unsigned sp).
    step.
    apply evt_done. unfold cb_post. do 15 eexists. exists mc. split; [reflexivity|]. auto. }
  step. step. if_cases K0.
  - do 1 step. eapply TAIL; eassumption.
  - do 2 step. eapply TAIL; eassumption.
Qed.

Theorem err_comp_ok : lh_comp_ok ERR_FNS.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d1 d2 lo A0 A1 A2 ([w1 CELL1] & DR1) ([w2 CELL2] & DR2) ST GLO SLO MI. subst a0 a1 a2.
  pose proof (rw_cells_bound _ _ _ _ CELL1) as DB1. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in DB1.
  pose proof (rw_cells_bound _ _ _ _ CELL2) as DB2. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in DB2.
  unfold ERR_FNS, lf_comp, lf_compw, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST. do 6 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  step.
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST. do 11 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  step.
  apply evt_done. unfold cb_post. do 15 eexists. eexists. split; [reflexivity|]. auto.
Qed.
End WithCeiling0.
