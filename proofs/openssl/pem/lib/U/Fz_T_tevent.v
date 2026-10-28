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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_lock_new Fz_T_sk.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TEV_RET := (0x32de94)%Z (only parsing).      (* [comment removed for export] *)
Notation TEV_CMP := (0xe2d48)%Z (only parsing).
Notation TEV_COPY := (0xe2d74)%Z (only parsing).
Notation TEV_FREE := (0xe2d20)%Z (only parsing).

Definition FZ_TEVENT_REG : Z := 0xe2c10.
Definition TEVENT_STACK : Z := 32 + LOCK_NEW_STACK.

Definition tevent_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists pg G psk SK plk LK,
       v = Z_to_bv 64 1
    /\ LBall' = (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: LBall /\ L' = (plk, 40) :: (psk, 56) :: (pg, 16) :: L
    /\ rblock_range G 16 /\ rblock_range SK 56 /\ rblock_range LK 40
    /\ rw_cells usegs m' TEV_RET [C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 G)]
    /\ rw_cells usegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]
    /\ rw_cells usegs m' SK (sk_cells z64 z64 z64 (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 TEV_CMP) (Z_to_bv 64 TEV_FREE) (Z_to_bv 64 TEV_COPY))
    /\ rw_cells usegs m' LK (mutex_cells z64 z64).

Definition T_tevent_reg_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z) (r0 g0 : word),
  (3 <= f)%nat -> croom L (wA 16 + wA 56 + wA 40) (wB 16 + wB 56 + wB 40) (wBig 16 + wBig 56 + wBig 40) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - TEVENT_STACK ->
  rw_cells usegs m TEV_RET [C4 r0; C8 g0] ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_TEVENT_REG) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) [(TEV_RET, TEV_RET + 12)] 3
                (wA 16 + wA 56 + wA 40) (wB 16 + wB 56 + wB 40) (wBig 16 + wBig 56 + wBig 40) (tevent_res LBall L)).

Theorem T_tevent_reg_spec : crypto_zalloc_stmt -> T_tevent_reg_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B r0 g0
         Hf ROOM CST SLO REG.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold TEVENT_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_TEVENT_REG, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (w_bounds 16 ltac:(lia)) as W16. pose proof (w_bounds 56 ltac:(lia)) as W56. pose proof (w_bounds 40 ltac:(lia)) as W40.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 32%nat ST. do 5 step. do 5 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun _ => False) [(TEV_RET, TEV_RET + 12)]%Z (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply CZ with (n := 16); [lia| eapply croom_weaken; [exact ROOM| lia..]| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (pg & G & -> & -> & -> & RNGG & GBLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  cst_static CFR1 REG REG1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNGG as (G0 & G16 & _ & GC & GIMG).
  change (Z.to_nat 16) with 16%nat in GBLK.
  apply (th_cells_congr usegs m1 G _ [C8 z64; C8 z64]) in GBLK; [| reflexivity | reflexivity | cbn; tauto].
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (TEV_RET, TEV_RET + 12)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. do 2 step. ths. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma end.
  assert (ING : In (pg, G, 16) ((pg, G, 16) :: LBall)) by (left; reflexivity).
  assert (CSTa : cstate st1 ((pg, G, 16) :: LBall) LB ((pg, 16) :: L) ma (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 ma _ _ tp lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MI1| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply cwin_bss; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST1.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRa : cframe (fun _ => False) [(TEV_RET, TEV_RET + 12)]%Z (bv_unsigned sp) st LBall L m st1 ((pg, G, 16) :: LBall) ((pg, 16) :: L) ma).
  { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; destruct X| intros q0 _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; cbn [rin_ivs fst snd]; lia]| apply Forall_nil]. }
  assert (ROOM2 : croom ((pg, 16) :: L) (wA 56) (wB 56) (wBig 56)).
  { eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| lia..]. }
  eapply climpl_seq.
  { eapply (T_sk_new_null_spec CZ); [lia| exact ROOM2| exact CSTa| rewrite unsigned_lit by lia; unfold SK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f2 L2 st2 ms2 (v2 & mb0 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (psk & SK & -> & -> & -> & RNGS & SKC)).
  destruct RET2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  cst_static CFR2 REG1 REG2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pg, G, 16) CFR2 GBLK ING ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as GBLK2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RNGS as (S0 & S16 & _ & SC & SIMG).
  assert (ING2 : In (pg, G, 16) ((psk, SK, 56) :: (pg, G, 16) :: LBall)) by (right; left; reflexivity).
  assert (INS2 : In (psk, SK, 56) ((psk, SK, 56) :: (pg, G, 16) :: LBall)) by (left; reflexivity).
  assert (NEGS : pg <> psk) by (eapply cstate_head_fresh; [exact CST2| left; reflexivity]).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 ING2 INS2 NEGS) as APGS.
  unfold sk_cells in SKC.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (G, G + 16); (SK, SK + 56)]%Z mb0) as MU2. pose proof (wmono_refl usegs mb0) as WM2.
  (* [comment removed for export] *)
  cprefix. do 5 step.
  tcallr T_sk_set_cmp_thunks_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. unfold sk_cells in *. cbn [fst snd] in *.
  do 3 step. step.
  tcallr T_sk_set_copy_thunks_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. unfold sk_cells in *. cbn [fst snd] in *.
  do 3 step. step.
  tcallr T_sk_set_thunks_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. unfold sk_cells in *. cbn [fst snd] in *.
  step. step. ubs_if. step. step. ubs_if. step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mb end.
  lazymatch goal with H : rw_cells usegs mb SK _ |- _ => rename H into SKb end.
  lazymatch goal with H : stk usegs mb _ _ |- _ => rename H into STb end.
  lazymatch goal with H : mem_inv usegs mb |- _ => rename H into MIb end.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _].
  assert (CSTb : cstate st2 ((psk, SK, 56) :: (pg, G, 16) :: LBall) LB ((psk, 56) :: (pg, 16) :: L) mb (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb0 mb _ _ tp lo B (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MIb| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pg, G, 16)); [exact ING2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (psk, SK, 56)); [exact INS2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact STb.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRb : cframe (fun _ => False) [(TEV_RET, TEV_RET + 12)]%Z (bv_unsigned sp) st LBall L m
                       st2 ((psk, SK, 56) :: (pg, G, 16) :: LBall) ((psk, 56) :: (pg, 16) :: L) mb).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa| exact FRM2| lia| intros a X; destruct X| intros q0 _ X; exact X]| exact MU2| exact WM2| exact HP2| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    - apply (cseg_ok_block _ _ _ _ _ (pg, G, 16)); [exact ING2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      destruct FR0 as (_ & KP0 & _). exact (cfresh_new _ _ _ _ _ _ KP0 ND1).
    - apply (cseg_ok_block _ _ _ _ _ (psk, SK, 56)); [exact INS2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      destruct FRa as (_ & KPa & _). exact (cfresh_new _ _ _ _ _ _ KPa ND2). }
  assert (ROOM3 : croom ((psk, 56) :: (pg, 16) :: L) (wA 40) (wB 40) (wBig 40)).
  { eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2))| lia..]. }
  eapply climpl_seq.
  { eapply (T_lock_new_spec CZ); [lia| exact ROOM3| exact CSTb| rewrite unsigned_lit by lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f3 L3 st3 ms3 (v3 & mc0 & LB3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (plk & LK & -> & -> & -> & RNGL & LKC)).
  destruct RET3 as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM3 as (CFR3 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FR2 ltac:(lia)) as FR3.
  cst_static CFR3 REG2 REG3.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pg, G, 16) CFR3 GBLK2 ING2 ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as GBLK3.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (psk, SK, 56) CFR3 SKb INS2 ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as SKC3.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  rewrite unsigned_lit in ST3 by lia.
  pose proof RNGL as (K0 & K16 & _ & KC & KIMG).
  assert (ING3 : In (pg, G, 16) ((plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: LBall)) by (right; right; left; reflexivity).
  assert (INS3 : In (psk, SK, 56) ((plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: LBall)) by (right; left; reflexivity).
  assert (INL3 : In (plk, LK, 40) ((plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: LBall)) by (left; reflexivity).
  assert (NEGL : pg <> plk) by (eapply cstate_head_fresh; [exact CST3| right; left; reflexivity]).
  assert (NESL : psk <> plk) by (eapply cstate_head_fresh; [exact CST3| left; reflexivity]).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST3 ING3 INL3 NEGL) as APGL.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST3 INS3 INL3 NESL) as APSL.
  unfold mutex_cells in LKC.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (TEV_RET, TEV_RET + 12); (G, G + 16)]%Z mc0) as MU3. pose proof (wmono_refl usegs mc0) as WM3.
  (* [comment removed for export] *)
  cprefix. step. step. ubs_if. step. step. ubs_if. step. ths.
  step. if_cases K4; zify_cond K4. { exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  step. if_cases K5; zify_cond K5. { exfalso. rewrite ?unsigned_lit in K5 by lia. lia. }
  step. step. ths. do 4 step.
  release_frame FR3 ST3 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [ND3 _].
  exists (Z_to_bv 64 1), mc, ((plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) GR3)|].
  split. { eapply (cstate_seg _ _ _ _ _ mc0 mc _ sp tp lo B (bv_unsigned sp)); [exact CST3| exact MU3| exact WM3| eassumption| | lia| lia| | exact ST3| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply cwin_bss; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pg, G, 16)); [exact ING3| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRb| exact FRM3| lia| intros a X; destruct X| intros q0 _ X; exact X]| exact MU3| exact WM3| exact HP3| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; cbn [rin_ivs fst snd]; lia]|].
    apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (pg, G, 16)); [exact ING3| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    destruct FR0 as (_ & KP0 & _). exact (cfresh_new _ _ _ _ _ _ KP0 ND1). }
  exists pg, G, psk, SK, plk, LK.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNGG|]. split; [exact RNGS|]. split; [exact RNGL|].
  split; [exact REG3|]. split; [exact GBLK3|]. split; eassumption.
Qed.
End WithCeiling0.
