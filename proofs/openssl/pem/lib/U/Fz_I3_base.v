(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_I1_insert1. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_atomic Fz_T_once.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition IC_S : Z := 0x32de20.
Definition FZ_INIT_CRYPTO : Z := 0xe1d58.
Definition IC_BASE_STACK : Z := 80 + 16.

Definition init_crypto_short_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp).
    (* [comment removed for export] *)

Definition init_crypto_base_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (od : word),
  rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] ->
  rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] ->
  rw_cells usegs m (IC_S + 96) [C8 od] ->
  a0 = Z_to_bv 64 0x40000 ->
  stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - IC_BASE_STACK -> mem_inv usegs m ->
  evt usegs (init_crypto_short_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_INIT_CRYPTO) fc None m (seg_rom usegs)).

Theorem init_crypto_base_spec : init_crypto_base_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo od STOP ONCE OD -> ST GLO SLO MI.
  unfold IC_S, FZ_INIT_CRYPTO, IC_BASE_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] with ([C4 (Z_to_bv 64 2)] ++ [C4 (Z_to_bv 64 1)]) in ONCE.
  apply (proj1 (rw_cells_app usegs m _ _ _)) in ONCE. destruct ONCE as [ONC ONR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ONR.
  change (3333664 + 32 + Z.of_nat 4) with 3333700 in ONR. change (3333664 + 32) with 0x32de40 in ONC. change (3333664 + 8) with 3333672 in STOP. change (3333664 + 96) with 3333760 in OD.
  pose proof T_atomic_load_proof as AL. unfold T_atomic_load_stmt in AL.
  pose proof T_run_once_done_proof as RO. unfold T_run_once_done_stmt in RO.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  step. carve_frame 80%nat ST. do 8 step. do 4 step. step. step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 4 step. step.
  apply (rw_cells_split_CB usegs _ _ [] 16 _ _ [8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  apply (cb8_c8_in' _ _ [CB 8 _] _ _) in FR. cbn [app] in FR.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: C8 ?tv :: ?rest) =>
    change (CB 8 j :: C8 tv :: rest) with ([CB 8 j] ++ [C8 tv] ++ rest) in FR end.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in FR. destruct FR as [FR0 FR]. apply (proj1 (rw_cells_app usegs _ _ _ _)) in FR. destruct FR as [FRT FRS].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRT, FRS.
  replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in * by lia. replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) in * by lia.
  (* [comment removed for export] *)
  assert (EPI : forall (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 tv : word) (mc : mem) (jj : list byte),
    rw_cells usegs mc (bv_unsigned sp + -80) [CB 8 jj] -> rw_cells usegs mc (bv_unsigned sp + -72) [C8 tv] ->
    rw_cells usegs mc (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -80) -> munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    evt usegs (init_crypto_short_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 (Z_to_bv 64 1) z16 z17 s7 s8 s9 s10 s11 z18 z19 z20 z21)
          F (Z_to_bv 64 0xe20b4) fc None mc (seg_rom usegs))).
  { intros z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 tv mc jj F0 FT FS STc MUc WMc MIc.
    assert (FJ : rw_cells usegs mc (bv_unsigned sp + -80) ([CB 8 jj] ++ [C8 tv] ++ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split; [exact F0|]. apply rw_cells_app. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by lia. replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) by lia. auto. }
    cbn [app] in FJ. clear F0 FT FS.
    do 9 step. release_frame FJ STc (bv_unsigned sp). step. step.
    apply evt_done. unfold init_crypto_short_post. do 14 eexists. exists mc. split; [reflexivity|]. auto. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (proj1 OD : ro_cells usegs mm 3333760 [C8 od]) as ODro end.
  calle (eapply AL with (lo := lo)); try lia.
  clear AL.
  step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  step. step. step. if_cases K2.
  - (* [comment removed for export] *)
    do 3 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (proj1 ONC : ro_cells usegs mm 0x32de40 [C4 (Z_to_bv 64 2)]) as ONro end.
    calle (eapply RO with (lo := lo)); try lia.
    step. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
    step. step. if_cases K4; zify_cond K4. { exfalso. revert K4. vm_compute. intros X. discriminate X. }
    do 2 step. step. if_cases K5; zify_cond K5. 2:{ exfalso. revert K5. vm_compute. intros X. first [discriminate X | apply X; reflexivity]. }
    eapply EPI; eassumption.
  - (* [comment removed for export] *)
    do 2 step. eapply EPI; eassumption.
Qed.

(* [comment removed for export] *)
Definition init_crypto_fast_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (od : word) (opts : Z),
  rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] ->
  rw_cells usegs m (IC_S + 96) [C8 od] ->
  a0 = Z_to_bv 64 opts -> 0 <= opts < 2^64 -> Z.land (bv_unsigned od) opts = opts ->
  stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - IC_BASE_STACK -> mem_inv usegs m ->
  evt usegs (init_crypto_short_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_INIT_CRYPTO) fc None m (seg_rom usegs)).

Theorem init_crypto_fast_spec : init_crypto_fast_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo od opts STOP OD -> OPTS DONE ST GLO SLO MI.
  unfold IC_S, FZ_INIT_CRYPTO, IC_BASE_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  change (3333664 + 8) with 3333672 in STOP. change (3333664 + 96) with 3333760 in OD.
  pose proof T_atomic_load_proof as AL. unfold T_atomic_load_stmt in AL.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  step. carve_frame 80%nat ST. do 8 step. do 4 step. step. step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 4 step. step.
  apply (rw_cells_split_CB usegs _ _ [] 16 _ _ [8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  apply (cb8_c8_in' _ _ [CB 8 _] _ _) in FR. cbn [app] in FR.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: C8 ?tv :: ?rest) =>
    change (CB 8 j :: C8 tv :: rest) with ([CB 8 j] ++ [C8 tv] ++ rest) in FR end.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in FR. destruct FR as [FR0 FR]. apply (proj1 (rw_cells_app usegs _ _ _ _)) in FR. destruct FR as [FRT FRS].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRT, FRS.
  replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in * by lia. replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) in * by lia.
  (* [comment removed for export] *)
  assert (EPI : forall (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 tv : word) (mc : mem) (jj : list byte),
    rw_cells usegs mc (bv_unsigned sp + -80) [CB 8 jj] -> rw_cells usegs mc (bv_unsigned sp + -72) [C8 tv] ->
    rw_cells usegs mc (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -80) -> munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    evt usegs (init_crypto_short_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 (Z_to_bv 64 1) z16 z17 s7 s8 s9 s10 s11 z18 z19 z20 z21)
          F (Z_to_bv 64 0xe20b4) fc None mc (seg_rom usegs))).
  { intros z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 tv mc jj F0 FT FS STc MUc WMc MIc.
    assert (FJ : rw_cells usegs mc (bv_unsigned sp + -80) ([CB 8 jj] ++ [C8 tv] ++ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split; [exact F0|]. apply rw_cells_app. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by lia. replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) by lia. auto. }
    cbn [app] in FJ. clear F0 FT FS.
    do 9 step. release_frame FJ STc (bv_unsigned sp). step. step.
    apply evt_done. unfold init_crypto_short_post. do 14 eexists. exists mc. split; [reflexivity|]. auto. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (proj1 OD : ro_cells usegs mm 3333760 [C8 od]) as ODro end.
  calle (eapply AL with (lo := lo)); try lia.
  clear AL.
  step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  step. step. step. if_cases K2; zify_cond K2.
  - (* [comment removed for export] *)
    exfalso. apply K2. rewrite ?(unsigned_lit opts) by lia. rewrite DONE. reflexivity.
  - do 2 step. eapply EPI; eassumption.
Qed.

End WithCeiling0.
