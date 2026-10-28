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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_once Fz_T_local Fz_T_sa Fz_T_master Fz_T_sa_new Fz_T_sa_set.
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

Definition FZ_SET_LOCAL_EX : Z := 0xe3ddc.
Definition SLX_STACK : Z := 96 + CZ_STACK.

Definition slx_first_res (val tp : word) (T k : Z) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists pm MK psa SA pl P (u' : byte),
       v = Z_to_bv 64 1
    /\ LBall' = (pl, P, 128) :: (psa, SA, 32) :: (pm, MK, 72) :: LBall /\ L' = (pl, 128) :: (psa, 32) :: (pm, 72) :: L
    /\ rblock_range MK 72 /\ rblock_range SA 32 /\ rblock_range P 128
    /\ rw_cells usegs m' (T + 8 * k) [C8 (Z_to_bv 64 MK)] /\ rw_cells usegs m' (bv_unsigned tp + -150) [C1 u']
    /\ rw_cells usegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
    /\ rw_cells usegs m' SA (sa_hdr (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 (sa_delta val z64)) (Z_to_bv 64 P))
    /\ rw_cells usegs m' P [C8 val; CB 120 (zeros 120)].

Definition T_set_local_ex_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B T k : Z) (u : byte),
  (3 <= f)%nat -> croom L (wA 72 + wA 32 + wA 128) (wB 72 + wB 32 + wB 128) (wBig 72 + wBig 32 + wBig 128) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SLX_STACK ->
  a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 1 ->
  rw_cells usegs m MK_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells usegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
  rw_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] ->
  rw_cells usegs m (T + 8 * k) [C8 z64] -> 0x351010 <= T + 8 * k -> T + 8 * k + 8 <= 0x3520d0 -> 0 <= T ->
  rw_cells usegs m (bv_unsigned tp + -150) [C1 u] ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_SET_LOCAL_EX) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False)
                [(T + 8 * k, T + 8 * k + 8); (bv_unsigned tp + -150, bv_unsigned tp + -149)] 3
                (wA 72 + wA 32 + wA 128) (wB 72 + wB 32 + wB 128) (wBig 72 + wBig 32 + wBig 128)
                (slx_first_res a2 tp T k LBall L)).

Theorem T_set_local_ex_first_spec : crypto_calloc_stmt -> crypto_zalloc_stmt -> T_set_local_ex_first_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CC CZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B T k u
         Hf ROOM CST SLO -> -> ONCE KEY HK TSDP SLOT SL1 SL2 HT USED.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & TPE) & _ & _ & _ & GLO).
  subst tp. unfold RATP in *. rewrite unsigned_lit in * by lia.
  unfold SLX_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_SET_LOCAL_EX, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 64%nat ST. do 7 step. do 4 step.
  step. th_if_lit.
  do 7 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into ma end.
  assert (ONCEr : ro_cells usegs ma 3333796 [C4 (Z_to_bv 64 2)]) by exact (proj1 ONCE).
  tcall T_run_once_done_proof.
  all: try first [eassumption | lia].
  clear ONCEr. cbv beta delta [mkR].
  step. step. th_if_lit. step. th_if_lit. do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mb end.
  assert (KEYr : ro_cells usegs mb 0x32dea8 [C4 (Z_to_bv 64 k)]) by exact (proj1 KEY).
  assert (TSDPr : ro_cells usegs mb (3344744 + -88) [C8 (Z_to_bv 64 T)]) by exact (proj1 TSDP).
  assert (SLOTr : ro_cells usegs mb (T + 8 * k) [C8 (Z_to_bv 64 0)]) by exact (proj1 SLOT).
  tcall T_get_local_proof.
  all: try first [eassumption | lia].
  clear KEYr TSDPr SLOTr. cbv beta delta [mkR].
  step. step. th_if_lit. do 6 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 3344744) lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ _ lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. eassumption.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun _ => False) [(T + 8 * k, T + 8 * k + 8); (3344594, 3344595)]%Z (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| eassumption| eassumption| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  assert (ROOM1 : croom L (wA (9 * 8)) (wB (9 * 8)) (wBig (9 * 8))).
  { change (9 * 8) with 72. pose proof (w_bounds 32 ltac:(lia)). pose proof (w_bounds 128 ltac:(lia)). eapply croom_weaken; [exact ROOM| lia..]. }
  eapply climpl_seq.
  { eapply CC with (num := 9) (sz := 8); [lia| exact ROOM1| lia| lia| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  change (9 * 8) with 72.
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (pm & MK & -> & -> & -> & RNGM & BLKM)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  cst_static CFR1 ONCE ONCE1. cst_static CFR1 KEY KEY1. cst_static CFR1 TSDP TSDP1. cst_static CFR1 SLOT SLOT1. cst_static CFR1 USED USED1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNGM as (M0 & M16 & _ & MC & MIMG).
  change (Z.to_nat 72) with 72%nat in BLKM.
  apply (th_cells_congr usegs m1 MK _ [CB 24 (zeros 24); C8 z64; CB 40 (zeros 40)]) in BLKM; [| reflexivity | reflexivity | cbn; tauto].
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (T + 8 * k, T + 8 * k + 8); (3344594, 3344595)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  do 4 step.
  assert (KEYr : ro_cells usegs m1 0x32dea8 [C4 (Z_to_bv 64 k)]) by exact (proj1 KEY1).
  assert (TSDPr : ro_cells usegs m1 (3344744 + -88) [C8 (Z_to_bv 64 T)]) by exact (proj1 TSDP1).
  tcalle T_set_local_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  step. th_if_lit. do 2 step.
  step. if_cases K5; zify_cond K5. { exfalso. rewrite ?unsigned_lit in K5 by lia. lia. }
  step. step. ubs_if.
  step. step. th_if_lit. step. chere.
  clear KEYr TSDPr.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mb end.
  lazymatch goal with H : rw_cells usegs mb (T + 8 * k) _ |- _ => rename H into SLOTb end.
  lazymatch goal with H : rw_cells usegs mb (3344744 + -150) [C1 ?ub] |- _ => rename H into USEDb; rename ub into u1b end.
  lazymatch goal with H : stk usegs mb _ _ |- _ => rename H into STb end.
  lazymatch goal with H : mem_inv usegs mb |- _ => rename H into MIb end.
  assert (INM : In (pm, MK, 72) ((pm, MK, 72) :: LBall)) by (left; reflexivity).
  assert (CSTb : cstate st1 ((pm, MK, 72) :: LBall) LB ((pm, 72) :: L) mb (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 3344744) lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 mb _ _ _ lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIb| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [unfold cwin; cbn [fst snd]; lia|].
      apply Forall_cons; [unfold cwin; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact STb.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRa : cframe (fun _ => False) [(T + 8 * k, T + 8 * k + 8); (3344594, 3344595)]%Z (bv_unsigned sp) st LBall L m
                       st1 ((pm, MK, 72) :: LBall) ((pm, 72) :: L) m1).
  { eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; destruct X| intros q0 _ X; exact X]. }
  assert (FRb : cframe (fun _ => False) [(T + 8 * k, T + 8 * k + 8); (3344594, 3344595)]%Z (bv_unsigned sp) st LBall L m
                       st1 ((pm, MK, 72) :: LBall) ((pm, 72) :: L) mb).
  { eapply cframe_seg; [exact FRa| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; cbn [rin_ivs fst snd]; lia]|].
    apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; cbn [rin_ivs fst snd]; lia]| apply Forall_nil]. }
  assert (ROOM2 : croom ((pm, 72) :: L) (wA 32) (wB 32) (wBig 32)).
  { pose proof (w_bounds 128 ltac:(lia)). eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| lia..]. }
  eapply climpl_seq.
  { eapply (T_sa_new_spec CZ); [lia| exact ROOM2| exact CSTb| rewrite unsigned_lit by lia; unfold SA_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (psa & SA & -> & -> & -> & RNGS & BLKS)).
  destruct RET2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  cst_static CFR2 ONCE1 ONCE2. cst_static CFR2 KEY1 KEY2. cst_static CFR2 TSDP1 TSDP2. cst_static CFR2 SLOTb SLOT2. cst_static CFR2 USEDb USED2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pm, MK, 72) CFR2 BLKM INM ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BLKM2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RNGS as (S0 & S16 & _ & SC & SIMG).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 NDL2].
  assert (PSM : psa <> pm). { intros E. cbn [map blk_id fst] in ND2. inversion ND2 as [|hd tl NI _]; subst. apply NI. left. reflexivity. }
  assert (APART : SA + 32 <= MK \/ MK + 72 <= SA).
  { pose proof (RHEAP_blocks_disjoint_proof _ _ _ (psa, SA, 32) (pm, MK, 72) HP2 (or_introl eq_refl) (or_intror (or_introl eq_refl))) as D.
    unfold blk_id, blk_addr, blk_size in D. cbn [fst snd] in D. apply D. exact PSM. }
  change (Z.to_nat 32) with 32%nat in BLKS.
  apply (th_cells_congr usegs m2 SA _ (sa_hdr z64 z64 z64 z64 z64)) in BLKS; [| reflexivity | reflexivity | cbn; tauto].
  unfold sa_hdr in BLKS.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (MK, MK + 72)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  cprefix. step. ubs_if.
  ths. step. if_cases K4; zify_cond K4. { exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  do 2 step. do 7 step. step.
  release_frame FR2 ST2 (bv_unsigned sp).
  step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m3 end.
  assert (INS : In (psa, SA, 32) ((psa, SA, 32) :: (pm, MK, 72) :: LBall)) by (left; reflexivity).
  assert (INM2 : In (pm, MK, 72) ((psa, SA, 32) :: (pm, MK, 72) :: LBall)) by (right; left; reflexivity).
  assert (CSTc2 : cstate st2 ((psa, SA, 32) :: (pm, MK, 72) :: LBall) LB ((psa, 32) :: (pm, 72) :: L) m3 sp (Z_to_bv 64 3344744) lo B).
  { eapply (cstate_seg _ _ _ _ _ m2 m3 _ sp _ lo B (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MI2| | lia| lia| | exact ST2| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pm, MK, 72)); [exact INM2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRc : cframe (fun _ => False) [(T + 8 * k, T + 8 * k + 8); (3344594, 3344595)]%Z (bv_unsigned sp) st LBall L m
                       st2 ((psa, SA, 32) :: (pm, MK, 72) :: LBall) ((psa, 32) :: (pm, 72) :: L) m3).
  { eapply cframe_seg; [eapply cframe_call; [exact FRb| exact FRM2| lia| intros a X; destruct X| intros q0 _ X; exact X]| exact MU2| exact WM2| exact HP2| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (pm, MK, 72)); [exact INM2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    destruct FR0 as (_ & KP0 & _). exact (cfresh_new _ _ _ _ _ _ KP0 ND1). }
  assert (ROOM3 : croom ((psa, 32) :: (pm, 72) :: L) (wA 128) (wB 128) (wBig 128)).
  { eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2))| lia..]. }
  eapply climpl_mono.
  { eapply (T_sa_set_fresh_spec CC) with (psa := psa) (SA := SA);
      [lia| exact ROOM3| exact CSTc2| unfold SA_SET_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity| exact INS| exact BLKS]. }
  intros f' L' s' ms' (v & m4 & LB4 & RET4 & FU4 & GR4 & CST4 & FRM4 & (pl & P & -> & -> & -> & RNGP & HDR & PBLK)).
  pose proof FRM4 as (CFR4 & _).
  cst_static CFR4 SLOT2 SLOT4. cst_static CFR4 USED2 USED4.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pm, MK, 72) CFR4 BLKM2 INM2 ltac:(unfold blk_id; cbn [fst snd]; exact PSM)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BLKM4.
  exists (Z_to_bv 64 1), m4, ((pl, P, 128) :: (psa, SA, 32) :: (pm, MK, 72) :: LBall).
  split; [exact RET4|]. split; [lia|].
  split; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) GR4)|]. split; [exact CST4|].
  split. { eapply cframe_call; [exact FRc| exact FRM4| lia| intros a X; destruct X|].
    intros q [Hq|Hq] _ E; subst q.
    - cbn [map blk_id fst] in ND2. inversion ND2 as [|hd tl NI _]; subst. apply NI. right. exact Hq.
    - cbn [map fst] in NDL2. inversion NDL2 as [|hd tl NI _]; subst. apply NI. right. exact Hq. }
  exists pm, MK, psa, SA, pl, P, u1b. rewrite unsigned_lit by lia.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNGM|]. split; [exact RNGS|]. split; [exact RNGP|].
  split; [exact SLOT4|]. split; [exact USED4|]. split; [exact BLKM4|]. split; [exact HDR| exact PBLK].
Qed.
End WithCeiling0.
