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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex Th_once. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_lock Fz_T_local Fz_T_once Fz_T_lock_new Fz_T_sk Fz_T_tevent.
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
Notation DTOR_KEY := (0x31d4d0)%Z (only parsing).      (* [comment removed for export] *)
Notation TEV_ONCE := (0x32de90)%Z (only parsing).      (* [comment removed for export] *)
Notation TEV_CMP := (0xe2d48)%Z (only parsing).
Notation TEV_COPY := (0xe2d74)%Z (only parsing).
Notation TEV_FREE := (0xe2d20)%Z (only parsing).

Definition FZ_MTL : Z := 0xe2a7c.
Definition MTL_STACK : Z := 192 + TEVENT_STACK.

Definition mtl_W (tp : word) (T k : Z) : list (Z * Z) :=
  [(T + 8 * k, T + 8 * k + 8); (bv_unsigned tp + -150, bv_unsigned tp + -149); (TEV_ONCE, TEV_ONCE + 16); (bv_unsigned tp + -96, bv_unsigned tp + -88)].

Definition mtl_first_res (tp : word) (T k : Z) (oldcb : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists ph H pg G psk SK plk LK pd D (u' : byte),
       v = Z_to_bv 64 H
    /\ LBall' = (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall
    /\ L' = (pd, 32) :: (plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: L
    /\ rblock_range H 8 /\ rblock_range G 16 /\ rblock_range SK 56 /\ rblock_range LK 40 /\ rblock_range D 32
    /\ rw_cells usegs m' (T + 8 * k) [C8 (Z_to_bv 64 H)] /\ rw_cells usegs m' (bv_unsigned tp + -150) [C1 u']
    /\ rw_cells usegs m' TEV_ONCE [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 G)]
    /\ rw_cells usegs m' (bv_unsigned tp + -96) [C8 oldcb]
    /\ rw_cells usegs m' H [C8 z64]
    /\ rw_cells usegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]
    /\ rw_cells usegs m' SK (sk_cells (Z_to_bv 64 1) z64 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) z64 (Z_to_bv 64 TEV_CMP) (Z_to_bv 64 TEV_FREE) (Z_to_bv 64 TEV_COPY))
    /\ rw_cells usegs m' LK (mutex_cells z64 z64)
    /\ rw_cells usegs m' D [C8 (Z_to_bv 64 H); CB 24 (zeros 24)].

Definition T_mtl_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B T k : Z) (u : byte) (r0 g0 oldcb : word),
  (5 <= f)%nat ->
  croom L (wA 8 + wA 16 + wA 56 + wA 40 + wA 32) (wB 8 + wB 16 + wB 56 + wB 40 + wB 32) (wBig 8 + wBig 16 + wBig 56 + wBig 40 + wBig 32) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - MTL_STACK ->
  a0 = Z_to_bv 64 1 -> a1 = z64 ->
  rw_cells usegs m DTOR_KEY [C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 0xffffffff)] -> 0 <= k < 128 ->
  rw_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] ->
  rw_cells usegs m (T + 8 * k) [C8 z64] -> 0x351010 <= T + 8 * k -> T + 8 * k + 8 <= 0x3520d0 -> 0 <= T ->
  rw_cells usegs m (bv_unsigned tp + -150) [C1 u] ->
  rw_cells usegs m TEV_ONCE [C4 z64; C4 r0; C8 g0] ->
  rw_cells usegs m (bv_unsigned tp + -96) [C8 oldcb] ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_MTL) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) (mtl_W tp T k) 5
                (wA 8 + wA 16 + wA 56 + wA 40 + wA 32) (wB 8 + wB 16 + wB 56 + wB 40 + wB 32) (wBig 8 + wBig 16 + wBig 56 + wBig 40 + wBig 32)
                (mtl_first_res tp T k oldcb LBall L)).

Theorem T_mtl_first_spec : crypto_zalloc_stmt -> crypto_calloc_stmt -> T_mtl_first_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ CC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B T k u r0 g0 oldcb
         Hf ROOM CST SLO -> -> DK4 HK TSDP SLOT SL1 SL2 HT USED ONCE CBC.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & TPE) & _ & _ & _ & GLO).
  subst tp. unfold mtl_W, RATP in *. rewrite unsigned_lit in * by lia.
  unfold MTL_STACK, TEVENT_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_MTL, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (w_bounds 8 ltac:(lia)) as W8. pose proof (w_bounds 16 ltac:(lia)) as W16. pose proof (w_bounds 56 ltac:(lia)) as W56.
  pose proof (w_bounds 40 ltac:(lia)) as W40. pose proof (w_bounds 32 ltac:(lia)) as W32.
  pose proof (proj1 (t_cells_halves usegs m DTOR_KEY k 0xffffffff ltac:(lia) ltac:(lia)) DK4) as DK8.
  change [C4 z64; C4 r0; C8 g0] with ([C4 z64] ++ [C4 r0; C8 g0]) in ONCE.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in ONCE. destruct ONCE as [ONCE REG]. cbn [cells_size csize Nat.add] in REG.
  change (3333776 + Z.of_nat 4) with 3333780 in REG.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 64%nat ST. do 7 step. do 3 step. step. do 2 step.
  step. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. lia. }
  do 4 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into ma end.
  assert (DKr : ro_cells usegs ma 3265744 [C4 (Z_to_bv 64 k)]).
  { pose proof DK4 as X. change [C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 4294967295)] with ([C4 (Z_to_bv 64 k)] ++ [C4 (Z_to_bv 64 4294967295)]) in X.
    apply (proj1 (rw_cells_app usegs _ _ _ _)) in X. exact (proj1 (proj1 X)). }
  assert (TSDPr : ro_cells usegs ma (3344744 + -88) [C8 (Z_to_bv 64 T)]) by exact (proj1 TSDP).
  assert (SLOTr : ro_cells usegs ma (T + 8 * k) [C8 (Z_to_bv 64 0)]) by exact (proj1 SLOT).
  tcalle T_get_local_proof.
  all: try first [eassumption | lia].
  clear DKr TSDPr SLOTr. cbv beta delta [mkR].
  step. step. th_if_lit. step. th_if_lit.
  do 5 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  lazymatch goal with H : stk usegs m0 _ _ |- _ => rename H into ST0 end.
  lazymatch goal with H : mem_inv usegs m0 |- _ => rename H into MI0' end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 3344744) lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ _ lo B (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MI0'| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST0.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun _ => False) [(T + 8 * k, T + 8 * k + 8); (3344744 + -150, 3344744 + -149); (TEV_ONCE, TEV_ONCE + 16); (3344744 + -96, 3344744 + -88)]%Z
                       (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply CZ with (n := 8); [lia| eapply croom_weaken; [exact ROOM| lia..]| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (ph & H & -> & -> & -> & RNGH & HBLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  cst_static CFR1 DK4 DK4a. cst_static CFR1 DK8 DK8a. cst_static CFR1 TSDP TSDPa. cst_static CFR1 SLOT SLOTa. cst_static CFR1 USED USEDa.
  cst_static CFR1 ONCE ONCEa. cst_static CFR1 REG REGa. cst_static CFR1 CBC CBCa.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNGH as (H0 & H16 & _ & HC & HIMG).
  destruct (rheap_ssp _ _ _ HP1) as [GOT GU]. unfold got_ssp, ssp_guard in GOT, GU.
  change (Z.to_nat 8) with 8%nat in HBLK.
  apply (th_cells_congr usegs m1 H _ [C8 z64]) in HBLK; [| reflexivity | reflexivity | cbn; tauto].
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp); (T + 8 * k, T + 8 * k + 8); (3344744 + -150, 3344744 + -149);
                           (TEV_ONCE, TEV_ONCE + 4); (3344744 + -96, 3344744 + -88)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  do 3 step.
  step. if_cases KD2; zify_cond KD2. { exfalso. rewrite ?unsigned_lit in KD2 by lia. lia. }
  do 5 step.
  assert (DKr : ro_cells usegs m1 3265744 [C4 (Z_to_bv 64 k)]).
  { pose proof DK4a as X. change [C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 4294967295)] with ([C4 (Z_to_bv 64 k)] ++ [C4 (Z_to_bv 64 4294967295)]) in X.
    apply (proj1 (rw_cells_app usegs _ _ _ _)) in X. exact (proj1 (proj1 X)). }
  assert (TSDPr : ro_cells usegs m1 (3344744 + -88) [C8 (Z_to_bv 64 T)]) by exact (proj1 TSDPa).
  tcalle T_set_local_proof.
  all: try first [eassumption | lia].
  clear DKr TSDPr. cbv beta delta [mkR].
  step. th_if_lit. do 6 step.
  pose proof T_run_once_enter_proof as OE. unfold T_run_once_enter_stmt, ssp_cells, got_ssp, ssp_guard in OE.
  tcall (OE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0xe2c10 oldcb rr_guard).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  clear OE. cbv beta delta [mkR]. try th_ret_lit. chere.
  unfold ONCE_RET_INIT, RUN_ONCE_RET, once_full_cells, ONCE_UNDO, ONCE_RET_FULL in *.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mi end.
  lazymatch goal with H : rw_cells usegs mi 3333776 _ |- _ => rename H into ONCE1 end.
  lazymatch goal with H : rw_cells usegs mi (3344744 + -96) _ |- _ => rename H into CB1 end.
  lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -64 + -128) _ |- _ => rename H into OF1 end.
  lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -64 + -32) _ |- _ => rename H into OF2 end.
  lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -64 + -16) _ |- _ => rename H into OF3 end.
  lazymatch goal with H : rw_cells usegs mi (T + 8 * k) _ |- _ => rename H into SLOT1 end.
  lazymatch goal with H : rw_cells usegs mi (3344744 + -150) [C1 ?ub] |- _ => rename H into USED1; rename ub into u1b end.
  lazymatch goal with H : stk usegs mi _ _ |- _ => rename H into STi end.
  lazymatch goal with H : mem_inv usegs mi |- _ => rename H into MIi end.
  assert (INH : In (ph, H, 8) ((ph, H, 8) :: LBall)) by (left; reflexivity).
  assert (CSTi : cstate st1 ((ph, H, 8) :: LBall) LB ((ph, 8) :: L) mi (Z_to_bv 64 (bv_unsigned sp + -64 + -128)) (Z_to_bv 64 3344744) lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 mi _ _ _ lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIi| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [unfold cwin; cbn [fst snd]; lia|].
      apply Forall_cons; [unfold cwin; cbn [fst snd]; lia|]. apply Forall_cons; [apply cwin_bss; lia|].
      apply Forall_cons; [unfold cwin; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact STi.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRa : cframe (fun _ => False) [(T + 8 * k, T + 8 * k + 8); (3344744 + -150, 3344744 + -149); (TEV_ONCE, TEV_ONCE + 16); (3344744 + -96, 3344744 + -88)]%Z
                       (bv_unsigned sp) st LBall L m st1 ((ph, H, 8) :: LBall) ((ph, 8) :: L) mi).
  { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; destruct X| intros q0 _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    repeat (apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; cbn [rin_ivs fst snd]; lia]|]). apply Forall_nil. }
  assert (ROOM2 : croom ((ph, 8) :: L) (wA 16 + wA 56 + wA 40) (wB 16 + wB 56 + wB 40) (wBig 16 + wBig 56 + wBig 40)).
  { eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| lia..]. }
  eapply climpl_seq.
  { eapply (T_tevent_reg_spec CZ) with (r0 := r0) (g0 := g0);
      [lia| exact ROOM2| exact CSTi| rewrite unsigned_lit by lia; unfold TEVENT_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| exact REGa]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pg & G & psk & SK & plk & LK & -> & -> & -> & RNGG & RNGS & RNGL & REG2 & GBLK & SKC & LKC)).
  destruct RET2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OF1 ltac:(lia)) as OF1b.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OF2 ltac:(lia)) as OF2b.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OF3 ltac:(lia)) as OF3b.
  cst_static CFR2 DK4a DK4b. cst_static CFR2 DK8a DK8b. cst_static CFR2 TSDPa TSDPb. cst_static CFR2 SLOT1 SLOTb. cst_static CFR2 USED1 USEDb.
  cst_static CFR2 ONCE1 ONCEb. cst_static CFR2 CB1 CBb.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ph, H, 8) CFR2 HBLK INH ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HBLKb.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RNGG as (G0 & G16 & _ & GC & GIMG). pose proof RNGS as (S0 & S16 & _ & SC & SIMG). pose proof RNGL as (K0 & K16 & _ & KC & KIMG).
  destruct (rheap_ssp _ _ _ HP2) as [GOT2 GU2]. unfold got_ssp, ssp_guard in GOT2, GU2.
  assert (INL2 : In (plk, LK, 40) ((plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (left; reflexivity).
  assert (INS2 : In (psk, SK, 56) ((plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (right; left; reflexivity).
  assert (ING2 : In (pg, G, 16) ((plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (right; right; left; reflexivity).
  assert (INH2 : In (ph, H, 8) ((plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (right; right; right; left; reflexivity).
  assert (NESL : psk <> plk) by (eapply cstate_head_fresh; [exact CST2| left; reflexivity]).
  assert (NEGL : pg <> plk) by (eapply cstate_head_fresh; [exact CST2| right; left; reflexivity]).
  assert (NEHL : ph <> plk) by (eapply cstate_head_fresh; [exact CST2| right; right; left; reflexivity]).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INS2 INL2 NESL) as APSL.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 ING2 INL2 NEGL) as APGL.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INH2 INL2 NEHL) as APHL.
  unfold sk_cells, mutex_cells in *.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (TEV_ONCE, TEV_ONCE + 4); (3344744 + -96, 3344744 + -88); (LK, LK + 40)]%Z m2) as MU2.
  pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix.
  pose proof (T_run_once_leave_proof) as OL. unfold T_run_once_leave_stmt, ssp_cells, got_ssp, ssp_guard, ONCE_RET_INIT, once_full_cells, ONCE_UNDO, ONCE_RET_FULL, RUN_ONCE_RET in OL.
  tcall (OL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -64) 3333776 (Z_to_bv 64 (bv_unsigned sp + -64 + -128)) oldcb rr_guard
              (Z_to_bv 64 928564) sp (Z_to_bv 64 H) (Z_to_bv 64 3265744) (Z_to_bv 64 3333776) (Z_to_bv 64 3265744) (Z_to_bv 64 3267236) s6).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  clear OL. cbv beta delta [mkR].
  step. th_if_lit. step. rewrite (t_sx32_small 1) by lia. step. th_if_lit.
  step. step. if_cases K5; zify_cond K5. { exfalso. rewrite ?unsigned_lit in K5 by lia. lia. }
  step. step. ubs_if. step. step.
  tcall T_write_lock_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. unfold mutex_cells in *.
  step. th_if_lit. do 3 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mp end.
  lazymatch goal with H : rw_cells usegs mp 3333776 _ |- _ => rename H into ONCE2 end.
  lazymatch goal with H : rw_cells usegs mp (3344744 + -96) _ |- _ => rename H into CB2 end.
  lazymatch goal with H : rw_cells usegs mp LK _ |- _ => rename H into LKL end.
  lazymatch goal with H : stk usegs mp _ _ |- _ => rename H into STp end.
  lazymatch goal with H : mem_inv usegs mp |- _ => rename H into MIp end.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 NDL2].
  change ((plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall) with ([(plk, LK, 40); (psk, SK, 56); (pg, G, 16); (ph, H, 8)] ++ LBall) in ND2.
  change ((plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: L) with ([(plk, 40); (psk, 56); (pg, 16); (ph, 8)] ++ L) in NDL2.
  assert (CSTp : cstate st2 ((plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall) LB ((plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: L)
                        mp (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 3344744) lo B).
  { eapply (cstate_seg _ _ _ _ _ m2 mp _ _ _ lo B (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MIp| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply cwin_bss; lia|].
      apply Forall_cons; [unfold cwin; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (plk, LK, 40)); [exact INL2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact STp.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRb : cframe (fun _ => False) [(T + 8 * k, T + 8 * k + 8); (3344744 + -150, 3344744 + -149); (TEV_ONCE, TEV_ONCE + 16); (3344744 + -96, 3344744 + -88)]%Z
                       (bv_unsigned sp) st LBall L m st2 ((plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)
                       ((plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: L) mp).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa| exact FRM2| lia| intros a X; cbn [rin_ivs fst snd] in *; lia| intros q0 _ X; exact X]| exact MU2| exact WM2| exact HP2| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    do 2 (apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; cbn [rin_ivs fst snd]; lia]|]).
    apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (plk, LK, 40)); [exact INL2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    apply (t_fresh_notin (fun _ => False)). apply (t_nodup_prefix blk_id _ _ _ ND2). left. reflexivity. }
  assert (ROOM5 : croom ((plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: L) (wA 32) (wB 32) (wBig 32)).
  { eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2))| lia..]. }
  eapply climpl_seq.
  { eapply (T_sk_push_first_spec CC) with (psk := psk) (A := SK);
      [lia| exact ROOM5| exact CSTp| rewrite unsigned_lit by lia; unfold SK_PUSH_STACK, SK_INSERT_STACK, SK_RESERVE_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia
      | reflexivity| exact INS2| exact SKC]. }
  intros f5 L5 st5 ms5 (v5 & m5 & LB5 & RET5 & FU5 & GR5 & CST5 & FRM5 & (pd & D & -> & -> & -> & RNGD & SKC5 & DBLK)).
  destruct RET5 as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM5 as (CFR5 & _).
  assert (NEHS : ph <> psk).
  { pose proof ND2 as X. cbn [app map] in X. inversion X as [|hd1 tl1 _ X1]. inversion X1 as [|hd2 tl2 NI _].
    intros E. apply NI. right. left. exact E. }
  assert (NEGS : pg <> psk).
  { pose proof ND2 as X. cbn [app map] in X. inversion X as [|hd1 tl1 _ X1]. inversion X1 as [|hd2 tl2 NI _].
    intros E. apply NI. left. exact E. }
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR5 FR2 ltac:(lia)) as FR5.
  cst_static CFR5 SLOTb SLOTc. cst_static CFR5 USEDb USEDc. cst_static CFR5 ONCE2 ONCEc. cst_static CFR5 CB2 CBc. cst_static CFR5 REG2 REGc.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ph, H, 8) CFR5 HBLKb INH2 ltac:(unfold blk_id; cbn [fst snd]; intros E; apply NEHS; symmetry; exact E)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HBLKc.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pg, G, 16) CFR5 GBLK ING2 ltac:(unfold blk_id; cbn [fst snd]; intros E; apply NEGS; symmetry; exact E)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as GBLKc.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (plk, LK, 40) CFR5 LKL INL2 ltac:(unfold blk_id; cbn [fst snd]; exact NESL)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as LKLc.
  pose proof CST5 as (HP5 & _ & (errv5 & _ & _ & ST5 & _ & _ & MI5 & _) & _).
  rewrite unsigned_lit in ST5 by lia.
  pose proof RNGD as (D0 & D16 & _ & DC & DIMG).
  assert (INL5 : In (plk, LK, 40) ((pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (right; left; reflexivity).
  assert (IND5 : In (pd, D, 32) ((pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (left; reflexivity).
  assert (NELD : plk <> pd) by (eapply cstate_head_fresh; [exact CST5| left; reflexivity]).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST5 INL5 IND5 NELD) as APLD.
  unfold sk_cells in SKC5.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (LK, LK + 40)]%Z m5) as MU5. pose proof (wmono_refl usegs m5) as WM5.
  (* [comment removed for export] *)
  cprefix. do 4 step.
  tcall T_unlock_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. unfold mutex_cells in *.
  step. th_if_lit. step. do 7 step.
  th_release FR5 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
  exists (Z_to_bv 64 H), m6, ((pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) GR5)| lia| lia| lia]. }
  split. { eapply (cstate_seg _ _ _ _ _ m5 m6 _ sp _ lo B (bv_unsigned sp)); [exact CST5| exact MU5| exact WM5| eassumption| | lia| lia| | eassumption| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (plk, LK, 40)); [exact INL5| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRb| exact FRM5| lia| intros a X; destruct X| ]| exact MU5| exact WM5| exact HP5| lia|].
    - intros q [Hq|Hq] _ E; subst q.
      + exact (t_nodup_prefix blk_id _ _ (psk, SK, 56) ND2 ltac:(right; left; reflexivity) Hq).
      + exact (t_nodup_prefix fst _ _ (psk, 56) NDL2 ltac:(right; left; reflexivity) Hq).
    - apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
      apply (cseg_ok_block _ _ _ _ _ (plk, LK, 40)); [exact INL5| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      apply (t_fresh_notin (fun _ => False)). apply (t_nodup_prefix blk_id _ _ _ ND2). left. reflexivity. }
  exists ph, H, pg, G, psk, SK, plk, LK, pd, D, u1b. rewrite ?unsigned_lit by lia.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact RNGH|]. split; [exact RNGG|]. split; [exact RNGS|]. split; [exact RNGL|]. split; [exact RNGD|].
  split; [eassumption|]. split; [eassumption|].
  split. { change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 G)] with ([C4 (Z_to_bv 64 2)] ++ [C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 G)]).
           apply (proj2 (rw_cells_app usegs _ _ _ _)). cbn [cells_size csize Nat.add]. change (3333776 + Z.of_nat 4) with 3333780. split; eassumption. }
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.
End WithCeiling0.
