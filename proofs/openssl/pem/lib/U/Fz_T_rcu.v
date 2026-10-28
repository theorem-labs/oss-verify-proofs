(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_calloc.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex Th_mutex_init Th_cond. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_lock_new.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_ctx_concrete_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    bv_unsigned a0 <> 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe409c) fc None m (seg_rom usegs)).

Theorem T_ctx_concrete_proof : T_ctx_concrete_stmt.
Proof.
  unfold T_ctx_concrete_stmt. intros until lo. intros HA ST LO0 LO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  ths. th_frame 16%nat [8; 8]%nat ST. do 3 ths.
  ths. if_cases K0; zify_cond K0. { exfalso. lia. }
  do 2 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths. finish.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_RCU_NEW : Z := 0xe34f4.
Definition RCU_STACK : Z := 80 + CZ_STACK.

(* [comment removed for export] *)
Definition rcu_head (ctx q : word) : list cell := [CB 8 (zeros 8); C8 ctx; C8 q; CB 4 (zeros 4); C4 (Z_to_bv 64 2); CB 16 (zeros 16)].

Definition rcu_new_res (ctx : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists pq Q pr A,
       v = Z_to_bv 64 A /\ LBall' = (pq, Q, 16) :: (pr, A, 264) :: LBall /\ L' = (pq, 16) :: (pr, 264) :: L
    /\ rblock_range A 264 /\ rblock_range Q 16
    /\ rw_cells usegs m' A (rcu_head ctx (Z_to_bv 64 Q))
    /\ rw_cells usegs m' (A + 48) (mutex_cells z64 z64) /\ rw_cells usegs m' (A + 88) (mutex_cells z64 z64)
    /\ rw_cells usegs m' (A + 128) cond_cells
    /\ rw_cells usegs m' (A + 176) (mutex_cells z64 z64) /\ rw_cells usegs m' (A + 216) cond_cells
    /\ rw_cells usegs m' Q [CB 16 (zeros 16)].

Definition T_rcu_new_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (2 <= f)%nat -> croom L (wA 264 + wA 16) (wB 264 + wB 16) (wBig 264 + wBig 16) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - RCU_STACK ->
  a0 = Z_to_bv 64 1 -> bv_unsigned a1 <> 0 ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_RCU_NEW) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) [] 2
                (wA 264 + wA 16) (wB 264 + wB 16) (wBig 264 + wBig 16) (rcu_new_res a1 LBall L)).

Theorem T_rcu_new_spec : crypto_zalloc_stmt -> crypto_calloc_stmt -> T_rcu_new_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ CC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         Hf ROOM CST SLO -> HCTX.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold RCU_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_RCU_NEW, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (w_bounds 264 ltac:(lia)) as W264. pose proof (w_bounds 16 ltac:(lia)) as W16.
  assert (SPHI : bv_unsigned sp <= 2^64 - 160)
    by (destruct CST as (_ & _ & (? & (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & ? & ? & ? & _) & ? & _) & _); lia).
  (* [comment removed for export] *)
  cprefix. step. th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 8 step. do 2 step. ths. ths. ths.
  step. th_if_lit. step. do 2 step.
  tcall T_ctx_concrete_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  step. if_cases K1; zify_cond K1. { exfalso. lia. }
  do 6 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  lazymatch goal with H : stk usegs m0 _ _ |- _ => rename H into ST0 end.
  lazymatch goal with H : mem_inv usegs m0 |- _ => rename H into MI0' end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MI0'| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST0.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply CZ with (n := 264); [lia| eapply croom_weaken; [exact ROOM| lia..]| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (pr & A & -> & -> & -> & RNGA & ABLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNGA as (A0 & A16 & _ & AC & AIMG).
  destruct (rheap_ssp _ _ _ HP1) as [GOT GU]. unfold got_ssp, ssp_guard in GOT, GU.
  (* [comment removed for export] *)
  change (Z.to_nat 264) with 264%nat in ABLK.
  apply (rw_cells_split_CB usegs _ _ [] 264%nat _ _ [8; 8; 8; 4; 4; 16; 40; 40; 48; 40; 48]%nat) in ABLK; [|reflexivity].
  cbn [mk_CB_cells app] in ABLK.
  lazymatch type of ABLK with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: nil) =>
    change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: nil) with ([c1; c2; c3; c4; c5; c6] ++ [c7] ++ [c8] ++ [c9] ++ [c10] ++ [c11]) in ABLK end.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in ABLK. destruct ABLK as [HD ABLK]. cbn [cells_size csize Nat.add] in ABLK.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in ABLK. destruct ABLK as [M1 ABLK]. cbn [cells_size csize Nat.add] in ABLK.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in ABLK. destruct ABLK as [M2 ABLK]. cbn [cells_size csize Nat.add] in ABLK.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in ABLK. destruct ABLK as [C1 ABLK]. cbn [cells_size csize Nat.add] in ABLK.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in ABLK. destruct ABLK as [M3 C2]. cbn [cells_size csize Nat.add] in C2.
  replace (A + Z.of_nat 48) with (A + 48) in * by lia.
  replace (A + 48 + Z.of_nat 40) with (A + 88) in * by lia.
  replace (A + 88 + Z.of_nat 40) with (A + 128) in * by lia.
  replace (A + 128 + Z.of_nat 48) with (A + 176) in * by lia.
  replace (A + 176 + Z.of_nat 40) with (A + 216) in * by lia.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 264)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  pose proof mutex_init_null_proof as MIN. unfold mutex_init_null_stmt, ssp_cells, got_ssp, ssp_guard, mutex_cells in MIN.
  pose proof cond_init_null_proof as CIN. unfold cond_init_null_stmt, ssp_cells, got_ssp, ssp_guard, cond_cells in CIN.
  (* [comment removed for export] *)
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  step. step. step. ubs_if. step. do 3 step. step.
  tcall (MIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo _ rr_guard).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  cbv beta delta [mkR]. lazymatch goal with H : rw_cells _ _ 0x31c468 _ /\ _ |- _ => clear H end.
  do 3 step. ths. step. th_if_lit.
  (* [comment removed for export] *)
  do 3 step. step.
  tcall (MIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo _ rr_guard).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  cbv beta delta [mkR]. lazymatch goal with H : rw_cells _ _ 0x31c468 _ /\ _ |- _ => clear H end.
  step. step. step. if_cases K6; zify_cond K6. { exfalso. lia. }
  do 3 step. ths. step. th_if_lit.
  (* [comment removed for export] *)
  do 3 step. step.
  tcall (MIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo _ rr_guard).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  cbv beta delta [mkR]. lazymatch goal with H : rw_cells _ _ 0x31c468 _ /\ _ |- _ => clear H end.
  step. step. step. if_cases K7; zify_cond K7. { exfalso. lia. }
  do 4 step. ths. step. if_cases K8; zify_cond K8. { exfalso. lia. }
  step. th_if_lit.
  (* [comment removed for export] *)
  do 3 step. step.
  tcall (CIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo _ rr_guard).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  cbv beta delta [mkR]. lazymatch goal with H : rw_cells _ _ 0x31c468 _ /\ _ |- _ => clear H end.
  do 3 step. step. th_if_lit.
  do 3 step. step.
  tcall (CIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo _ rr_guard).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  cbv beta delta [mkR]. lazymatch goal with H : rw_cells _ _ 0x31c468 _ /\ _ |- _ => clear H end.
  do 3 step. step. th_if_lit.
  clear MIN CIN.
  (* [comment removed for export] *)
  do 6 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mb end.
  lazymatch goal with H : rw_cells usegs mb A _ |- _ => rename H into HDb end.
  lazymatch goal with H : rw_cells usegs mb (A + 48) _ |- _ => rename H into OB1 end.
  lazymatch goal with H : rw_cells usegs mb (A + 88) _ |- _ => rename H into OB2 end.
  lazymatch goal with H : rw_cells usegs mb (A + 128) _ |- _ => rename H into OB3 end.
  lazymatch goal with H : rw_cells usegs mb (A + 176) _ |- _ => rename H into OB4 end.
  lazymatch goal with H : rw_cells usegs mb (A + 216) _ |- _ => rename H into OB5 end.
  lazymatch goal with H : stk usegs mb _ _ |- _ => rename H into STb end.
  lazymatch goal with H : mem_inv usegs mb |- _ => rename H into MIb end.
  assert (INA : In (pr, A, 264) ((pr, A, 264) :: LBall)) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (CSTb : cstate st1 ((pr, A, 264) :: LBall) LB ((pr, 264) :: L) mb (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 mb _ _ tp lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIb| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pr, A, 264)); [exact INA| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact STb.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRb : cframe (fun _ => False) [] (bv_unsigned sp) st LBall L m st1 ((pr, A, 264) :: LBall) ((pr, 264) :: L) mb).
  { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (pr, A, 264)); [exact INA| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    destruct FR0 as (_ & KP0 & _). exact (cfresh_new _ _ _ _ _ _ KP0 ND1). }
  assert (ROOM2 : croom ((pr, 264) :: L) (wA (2 * 8)) (wB (2 * 8)) (wBig (2 * 8))).
  { change (2 * 8) with 16. eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| lia..]. }
  eapply climpl_seq.
  { eapply CC with (num := 2) (sz := 8); [lia| exact ROOM2| lia| lia| lia| exact CSTb| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  change (2 * 8) with 16.
  intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pq & Q & -> & -> & -> & RNGQ & QBLK)).
  destruct RET2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pr, A, 264) CFR2 HDb INA ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HD2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pr, A, 264) CFR2 OB1 INA ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as OB1b.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pr, A, 264) CFR2 OB2 INA ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as OB2b.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pr, A, 264) CFR2 OB3 INA ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as OB3b.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pr, A, 264) CFR2 OB4 INA ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as OB4b.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pr, A, 264) CFR2 OB5 INA ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as OB5b.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RNGQ as (Q0 & Q16 & _ & QC & QIMG).
  assert (INA2 : In (pr, A, 264) ((pq, Q, 16) :: (pr, A, 264) :: LBall)) by (right; left; reflexivity).
  assert (INQ2 : In (pq, Q, 16) ((pq, Q, 16) :: (pr, A, 264) :: LBall)) by (left; reflexivity).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INA2 INQ2 ltac:(eapply cstate_head_fresh; [exact CST2| exact INA])) as APAQ.
  change (Z.to_nat 16) with 16%nat in QBLK.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 264)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. ths. ths. step. if_cases K5; zify_cond K5. { exfalso. rewrite ?unsigned_lit in K5 by lia. lia. }
  step. step. do 7 step.
  th_release FR2 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  exists (Z_to_bv 64 A), m3, ((pq, Q, 16) :: (pr, A, 264) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2)|].
  split. { eapply (cstate_seg _ _ _ _ _ m2 m3 _ sp tp lo B (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| eassumption| | lia| lia| | eassumption| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pr, A, 264)); [exact INA2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRb| exact FRM2| lia| intros a X; exact X| intros q0 _ X; exact X]| exact MU2| exact WM2| exact HP2| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (pr, A, 264)); [exact INA2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    destruct FR0 as (_ & KP0 & _). exact (cfresh_new _ _ _ _ _ _ KP0 ND1). }
  exists pq, Q, pr, A. unfold rcu_head, mutex_cells, cond_cells.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNGA|]. split; [exact RNGQ|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.
End WithCeiling0.
