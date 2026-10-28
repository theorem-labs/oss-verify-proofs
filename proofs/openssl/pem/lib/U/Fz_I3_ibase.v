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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex Th_key. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_local Fz_T_initthread Fz_T_lock_new Fz_I3_base Fz_G_OPENSSL_cpuid_setup.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition FZ_INIT_BASE : Z := 0xe20e0.
Definition IB_STACK : Z := 32 + LOCK_NEW_STACK.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IB_W : list (Z * Z) :=
  [(IC_S, IC_S + 1); (IC_S + 28, IC_S + 32); (IC_S + 36, IC_S + 40); (IC_S + 80, IC_S + 96);
   (0x31d4d0, 0x31d4d4); (0x351c90, 0x351c9c); (0x351890, 0x3518a0); (RATP + -88, RATP + -80)].

Definition ibase_res (sh : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun _ LBall' L' m' => exists (pk1 pk2 : bptr) (LK1 LK2 : Z),
       LBall' = (pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall /\ L' = (pk2, 40) :: (pk1, 40) :: L
    /\ rblock_range LK1 40 /\ rblock_range LK2 40
    /\ rw_cells usegs m' LK1 (mutex_cells z64 z64) /\ rw_cells usegs m' LK2 (mutex_cells z64 z64)
    /\ rw_cells usegs m' IC_S [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m' (IC_S + 28) [C4 (Z_to_bv 64 1)] /\ rw_cells usegs m' (IC_S + 36) [C4 (Z_to_bv 64 1)]
    /\ rw_cells usegs m' (IC_S + 80) [C8 (Z_to_bv 64 LK1); C8 (Z_to_bv 64 LK2)]
    /\ rw_cells usegs m' 0x31d4d0 [C4 z64] /\ rw_cells usegs m' (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)]
    /\ rw_cells usegs m' 0x351c90 [C4 (Z_to_bv 64 1)] /\ rw_cells usegs m' 0x351c98 [C4 z64; C4 z64; C4 sh]
    /\ rw_cells usegs m' 0x351890 [C8 (Z_to_bv 64 0xe2438)] /\ rw_cells usegs m' (0x351890 + 8 * 1) [C8 (Z_to_bv 64 0x2bdf1c)].

Definition init_base_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z) (o80 o88 r36 kold0 kold1 tsd sh : word) (b0 : byte),
  (2 <= f)%nat -> croom L 2 0 0 ->
  cstate s LBall LB L m sp tp lo Bd -> lo <= bv_unsigned sp - IB_STACK ->
  rw_cells usegs m IC_S [C1 b0] -> rw_cells usegs m (IC_S + 28) [C4 kold1] -> rw_cells usegs m (IC_S + 36) [C4 r36] -> rw_cells usegs m (IC_S + 80) [C8 o80; C8 o88] ->
  rw_cells usegs m 0x31d4d0 [C4 kold0] -> rw_cells usegs m (RATP + -88) [C8 tsd] -> (tsd = z64 \/ tsd = Z_to_bv 64 0x351cd0) ->
  rw_cells usegs m 0x351c90 [C4 z64] -> rw_cells usegs m 0x351c98 [C4 z64; C4 z64; C4 sh] ->
  rw_cells usegs m 0x351890 [C8 z64] -> rw_cells usegs m (0x351890 + 8 * 1) [C8 z64] ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_INIT_BASE) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun _ => False) IB_W 2 2 0 0 (ibase_res sh LBall L)).

Theorem init_base_spec : T_lock_new_stmt -> init_base_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LKN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd o80 o88 r36 kold0 kold1 tsd sh b0
         Hf ROOM CST SLO BI K1C R36 LKC DK TC TV NK KL KY0 KY1.
  unfold T_lock_new_stmt in LKN.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  subst tp.
  unfold IB_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_INIT_BASE, RATP, IC_S in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  change (3333664 + 28) with 0x32de3c in K1C. change (3333664 + 36) with 3333700 in R36. change (3333664 + 80) with 3333744 in LKC.
  destruct ROOM as (RA & RB & RC).
  destruct (wA_small 40 ltac:(unfold TIER_A_MAX; lia)) as (WA1 & WA2 & WA3).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 32%nat ST. do 3 step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 3344744) lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe (fun _ : bptr => False) IB_W (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  chere. eapply climpl_seq.
  { eapply LKN with (lo := lo) (B := Bd); [lia| rewrite WA1, WA2, WA3; unfold croom; lia| exact CSTa| rewrite unsigned_lit by lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pk1 & LK1 & -> & -> & -> & RNG1 & MC1)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). rewrite WA1, WA2, WA3 in GR1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  lazymatch goal with FRh : rw_cells _ ma (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  cst_static CFR1 BI BI1. cst_static CFR1 K1C K1C1. cst_static CFR1 R36 R361. cst_static CFR1 LKC LKC1. cst_static CFR1 DK DK1. cst_static CFR1 TC TC1.
  cst_static CFR1 NK NK1. cst_static CFR1 KL KL1. cst_static CFR1 KY0 KY01. cst_static CFR1 KY1 KY11.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG1 as (LK1P & _ & _ & LK1C & LK1IMG).
  unfold mutex_cells in MC1.
  assert (FRM0 : cframe (fun _ : bptr => False) IB_W (bv_unsigned sp) s LBall L m st1 ((pk1, LK1, 40) :: LBall) ((pk1, 40) :: L) m1).
  { eapply cframe_call; [exact FRa| exact FRM1| lia| intros a X; destruct X| intros q _ X; exact X]. }
  clear FRa CSTa CFR1 FRM1.
  pose proof (munch_refl [(3333744, 3333752)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. step. step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mb end.
  lazymatch goal with H : mem_inv _ mb |- _ => rename H into MIb end.
  lazymatch goal with H : stk _ mb _ _ |- _ => rename H into STb end.
  assert (CSTb : cstate st1 ((pk1, LK1, 40) :: LBall) LB ((pk1, 40) :: L) mb (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 3344744) lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m1 mb _ _ _ lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIb| | lia| lia| | rewrite unsigned_lit by lia; exact STb| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_bss; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRb : cframe (fun _ : bptr => False) IB_W (bv_unsigned sp) s LBall L m st1 ((pk1, LK1, 40) :: LBall) ((pk1, 40) :: L) mb).
  { eapply cframe_seg; [exact FRM0| exact MU1| exact WM1| exact HP1| lia|].
    constructor; [| constructor]. apply cseg_ok_static; [lia| lia| intros a Ha; unfold IB_W, IC_S; cbn [rin_ivs fst snd]; lia]. }
  chere. eapply climpl_seq.
  { eapply LKN with (lo := lo) (B := Bd); [lia| rewrite WA1, WA2, WA3; unfold croom, cgrow in *; lia| exact CSTb| rewrite unsigned_lit by lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pk2 & LK2 & -> & -> & -> & RNG2 & MC2)).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM2 by lia). rewrite WA1, WA2, WA3 in GR2.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  lazymatch goal with H : rw_cells _ mb 3333744 _ |- _ => rename H into LKCb end.
  cst_static CFR2 BI1 BI2. cst_static CFR2 K1C1 K1C2. cst_static CFR2 R361 R362. cst_static CFR2 LKCb LKC2. cst_static CFR2 DK1 DK2. cst_static CFR2 TC1 TC2.
  cst_static CFR2 NK1 NK2. cst_static CFR2 KL1 KL2. cst_static CFR2 KY01 KY02. cst_static CFR2 KY11 KY12.
  assert (INK1 : In (pk1, LK1, 40) ((pk1, LK1, 40) :: LBall)) by (left; reflexivity).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk1, LK1, 40) CFR2 MC1 INK1 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as MC12.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RNG2 as (LK2P & _ & _ & LK2C & LK2IMG).
  unfold mutex_cells in MC2.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _].
  assert (NE21 : pk2 <> pk1). { intros E. cbn [map blk_id fst] in ND2. inversion ND2 as [|hd tl NI _]; subst. apply NI. left. reflexivity. }
  assert (INK12 : In (pk1, LK1, 40) ((pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall)) by (right; left; reflexivity).
  assert (INK22 : In (pk2, LK2, 40) ((pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall)) by (left; reflexivity).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INK22 INK12 NE21) as AP21.
  assert (FRc : cframe (fun _ : bptr => False) IB_W (bv_unsigned sp) s LBall L m st2 ((pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall) ((pk2, 40) :: (pk1, 40) :: L) m2).
  { eapply cframe_call; [exact FRb| exact FRM2| lia| intros a X; destruct X| intros q _ X; exact X]. }
  clear FRb CSTb CFR2 FRM2.
  assert (KY0r : ro_cells usegs m2 (3479696 + 8 * 0) [C8 z64]) by exact (proj1 KY02).
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp - 32); (3333752, 3333760); (0x31d4d0, 0x31d4d4); (0x351c90, 0x351c9c); (0x351890, 0x3518a0);
                           (3344744 + -88, 3344744 + -80); (0x32de3c, 0x32de40); (3333664, 3333665); (3333700, 3333704)]%Z m2) as MU2.
  pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. step. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  step. tcallr OPENSSL_cpuid_setup_s0_walk. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR]. try th_ret_lit.
  step. tcall (T_init_thread_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0 0 sh kold0 (Z_to_bv 64 0) tsd).
  all: try first [eassumption | reflexivity | lia | left; split; reflexivity].
  cbv beta delta [mkR]. try th_ret_lit.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  lazymatch goal with H : rw_cells usegs mc (3479696 + 8 * 0) _ |- _ => assert (KYr : ro_cells usegs mc (3479696 + 8 * 0) [C8 (Z_to_bv 64 926776)]) by exact (proj1 H) end.
  step. th_if_lit. step. step. step.
  tcall (T_init_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0 1 sh kold1 (Z_to_bv 64 926776) (Z_to_bv 64 3480784)).
  all: try first [eassumption | reflexivity | lia | right; reflexivity | right; split; [reflexivity| rewrite unsigned_lit by lia; lia]].
  cbv beta delta [mkR]. try th_ret_lit.
  change (if bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) then Z_to_bv 64 2875164 else Z_to_bv 64 0) with (Z_to_bv 64 2875164) in *.
  step. th_if_lit. step. cstep. step. cstep. do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk _ mf lo _ |- _ => rename H into ST3 end.
  lazymatch goal with H : rw_cells usegs mf (bv_unsigned sp + -32) _ |- _ => rename H into FR3 end.
  release_frame FR3 ST3 (bv_unsigned sp). step. step.
  lazymatch goal with H : stk _ mf lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv _ mf |- _ => rename H into MIf end.
  chere. apply climpl_done.
  eexists. exists mf, ((pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split; [pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) as GR; clear - GR; unfold cgrow in *; lia|].
  split. { eapply (cstate_seg _ _ _ _ _ m2 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - repeat apply Forall_cons; try apply Forall_nil; first [apply cwin_stack; lia | apply cwin_bss; lia | unfold cwin; cbn [fst snd]; lia].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [exact FRc| exact MU2| exact WM2| exact HP2| lia|].
    repeat apply Forall_cons; try apply Forall_nil; first [apply cseg_ok_stack; lia | apply cseg_ok_static; [lia| lia| intros a Ha; unfold IB_W, IC_S, RATP; cbn [rin_ivs fst snd]; lia]]. }
  unfold ibase_res, mutex_cells, IC_S, RATP. exists pk1, pk2, LK1, LK2.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG1|]. split; [exact RNG2|].
  change (3333664 + 28) with 0x32de3c. change (3333664 + 36) with 3333700. change (3333664 + 80) with 3333744.
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.
End WithCeiling0.
