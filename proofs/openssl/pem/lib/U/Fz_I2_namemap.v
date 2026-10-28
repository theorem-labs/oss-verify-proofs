(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_aligned_frame.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_kit_ra Fz_M_malloc Fz_M_zalloc Fz_M_calloc Fz_M_aligned F_memset.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_lock_new Fz_T_rcu Fz_T_sk Fz_I2_htnew.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nm_sk3_post (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (Q lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (Z_to_bv 64 0xf77a8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Q) (Z_to_bv 64 0xf868c) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 Q) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xf77a8) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (Q + 32, Q + 56)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' Q (sk_cells z64 z64 z64 (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 0xf86b4) (Z_to_bv 64 0xf868c) (Z_to_bv 64 0xf86e0)).

Lemma nm_sk3 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Q lo : Z),
  s2 = Z_to_bv 64 Q -> 0 < Q -> Q mod 8 = 0 -> Q + 56 <= alloc_ceiling ->
  rw_cells usegs m Q (sk_cells z64 z64 z64 (Z_to_bv 64 1) z64 z64 z64 z64 z64) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  evt usegs (nm_sk3_post sp gp tp t0 t1 t2 s0 s1 z64 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Q lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf7778) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros -> Q0 Q8 QC QCELLS ST LO SLO MI. unfold ceil_window in CEIL_RANGE__.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (Q + 32, Q + 56)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold sk_cells in QCELLS.
  do 3 step. step. tcallr T_sk_set_cmp_thunks_proof. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR]. cbn [fst snd] in *.
  do 3 step. step. tcallr T_sk_set_copy_thunks_proof. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR]. cbn [fst snd] in *.
  do 3 step. step. tcallr T_sk_set_thunks_proof. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR]. cbn [fst snd] in *.
  apply evt_done. unfold nm_sk3_post, sk_cells. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_NAMEMAP_NEW : Z := 0xf76e4.
Definition NMN_STACK : Z := 80 + HTN_STACK.

(* [comment removed for export] *)
Definition nm_cells (HT LK SK : Z) : list cell := [C8 z64; C8 (Z_to_bv 64 HT); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 SK); C8 z64].

Definition namemap_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (ps pk ph pka pmd pn pr pq pt : bptr) (S LK HT LKa MD NB R Q SK : Z),
       v = Z_to_bv 64 S
    /\ LBall' = (pt, SK, 56) :: (pq, Q, 16) :: (pr, R, 264) :: (pn, NB, 32768) :: (pmd, MD, 24) :: (pka, LKa, 40) :: (ph, HT, 96) :: (pk, LK, 40) :: (ps, S, 40) :: LBall
    /\ L' = (pt, 56) :: (pq, 16) :: (pr, 264) :: (pn, 32816) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: (pk, 40) :: (ps, 40) :: L
    /\ rblock_range S 40 /\ rblock_range LK 40 /\ rblock_range HT 96 /\ rblock_range LKa 40 /\ rblock_range MD 24 /\ rblock_range NB 32768
    /\ rblock_range R 264 /\ rblock_range Q 16 /\ rblock_range SK 56
    /\ rw_cells usegs m' S (nm_cells HT LK SK).

Definition namemap_new_fp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (9 <= f)%nat -> croom L 7 2 49464 -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - NMN_STACK -> bv_unsigned sp mod 16 = 0 ->
  a0 = Z_to_bv 64 0x32dec8 -> rw_cells usegs m 0x351010 [C4 (Z_to_bv 64 0)] ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_NAMEMAP_NEW) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 9 7 2 49464 (namemap_res LBall L)).

Theorem namemap_new_fp_spec : crypto_zalloc_stmt -> T_lock_new_stmt -> ht_new_fp_stmt -> T_sk_new_null_stmt -> namemap_new_fp_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ LKN HTN SKN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd
         Hf ROOM CST SLO SP16 -> REPL.
  unfold crypto_zalloc_stmt in CZ. unfold T_lock_new_stmt in LKN. unfold ht_new_fp_stmt, NB_BYTES in HTN. unfold T_sk_new_null_stmt in SKN.
  change (32768 + 48 + 8192 + (264 + 8192)) with 49464 in HTN. change (32768 + 48) with 32816 in HTN.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold NMN_STACK, HTN_STACK, RCU_STACK, SK_NEW_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_NAMEMAP_NEW, RMALLOC_REPLACED in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (rw_cells_bound _ _ _ _ REPL) as RB0. cbn [cells_size csize Nat.add] in RB0.
  destruct (wA_small 40 ltac:(unfold TIER_A_MAX; lia)) as (W40a & W40b & W40c). destruct (wA_small 56 ltac:(unfold TIER_A_MAX; lia)) as (W56a & W56b & W56c).
  destruct ROOM as (RA & RB & RC).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. th_frame 80%nat [8; 40; 8; 8; 8; 8]%nat ST. do 4 step. do 5 step. step.
  lazymatch goal with FRh : rw_cells _ ?mx (bv_unsigned sp + -80) (CB 8 ?j0 :: CB 40 ?j1 :: ?rest) |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    change (CB 8 j0 :: CB 40 j1 :: rest) with ([CB 8 j0] ++ [CB 40 j1] ++ rest) in FRh;
    apply (proj1 (rw_cells_app usegs mx _ _ _)) in FRh; destruct FRh as [FRa FRh];
    apply (proj1 (rw_cells_app usegs mx _ _ _)) in FRh; destruct FRh as [FRc FRr];
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in FRc, FRr end.
  replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in FRc by lia.
  replace (bv_unsigned sp + -80 + 8 + 40) with (bv_unsigned sp + -32) in FRr by lia.
  tcall (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (bv_unsigned sp + -72) 0 40 (take 40 (drop 8 junk))).
  all: try first [eassumption | lia]. cbv beta delta [mkR].
  lazymatch goal with H : rw_cells usegs ?mx (bv_unsigned sp + -72) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    apply (th_cells_congr usegs mx (bv_unsigned sp + -72) _ [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64]) in H; [| reflexivity | reflexivity | cbn; repeat split; exact I]; rename H into FRc end.
  do 4 step. cstep. cstep. cstep. do 4 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  lazymatch goal with H : rw_cells usegs ma (bv_unsigned sp + -80) _ |- _ => rename H into FRa0 end.
  lazymatch goal with H : rw_cells usegs ma (bv_unsigned sp + -72) _ |- _ => rename H into FRc0 end.
  lazymatch goal with H : rw_cells usegs ma (bv_unsigned sp + -32) _ |- _ => rename H into FRr0 end.
  lazymatch goal with H : rw_cells usegs ma 3477520 _ |- _ => rename H into REPLa end.
  assert (CONFa : rw_cells usegs ma (bv_unsigned sp + -80) ht_conf).
  { unfold ht_conf, HT_CTX. change ([?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7]) with ([c0] ++ [c1; c2; c3; c4; c5; c6; c7]). apply rw_cells_app. split; [exact FRa0|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by lia.
    apply (th_cells_congr usegs ma (bv_unsigned sp + -72) [C8 z64; C8 z64; C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 4294967297); C8 z64]); [| reflexivity| cbn; repeat split; exact I| exact FRc0].
    cbn [cells_bytes cbytes app]. change (Z_to_bv 64 4294967297) with (Z_to_bv 64 (1 + 2 ^ 32 * 1)). rewrite (t_le8_of_halves 1 1) by lia.
    change (le8 (Z_to_bv 64 0)) with (le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0)) at 3. reflexivity. }
  clear FRa0 FRc0.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRMa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply CZ with (n := 40) (lo := lo) (B := Bd); [lia| rewrite W40a, W40b, W40c; unfold croom; lia| lia| exact CSTa| rewrite unsigned_lit by lia; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (ps & S & -> & -> & -> & RS & SBLK)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). rewrite W40a, W40b, W40c in GR1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 CONFa ltac:(lia)) as CONF1.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRr0 ltac:(lia)) as FR1.
  cst_static CFR1 REPLa REPL1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RS as (S0 & _ & _ & SC & SIMG).
  change (Z.to_nat 40) with 40%nat in SBLK.
  apply (th_cells_congr usegs m1 S _ [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64]) in SBLK; [| reflexivity | reflexivity | cbn; repeat split; exact I].
  assert (INS1 : In (ps, S, 40) ((ps, S, 40) :: LBall)) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _]. cbn [map blk_id fst] in ND1.
  assert (NPS : forall b0, In b0 LBall -> ~ False -> blk_id b0 <> ps).
  { intros b0 Hb0 _ E. apply (proj1 (proj1 (NoDup_cons_iff _ _) ND1)). rewrite <- E. apply in_map. exact Hb0. }
  clear ND1.
  assert (FRM01 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st1 ((ps, S, 40) :: LBall) ((ps, 40) :: L) m1).
  { eapply cframe_call; [exact FRMa| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRMa CSTa CFR1 FRM1 CONFa FRr0 REPLa KP1.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. chere.
  eapply climpl_seq.
  { eapply LKN with (lo := lo) (B := Bd); [clear - Hf FU1; lia| rewrite W40a, W40b, W40c; clear - RA RB RC GR1; unfold croom, cgrow in *; lia| exact CST1
      | rewrite unsigned_lit by lia; lia]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pk & LK & -> & -> & -> & RK & MCk)).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM2 by lia). rewrite W40a, W40b, W40c in GR2. clear MCk.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 CONF1 ltac:(lia)) as CONF2.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  cst_static CFR2 REPL1 REPL2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 40) CFR2 SBLK INS1 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as SBLK2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RK as (LK0 & _ & _ & LKC & LKIMG).
  set (LB2 := (pk, LK, 40) :: (ps, S, 40) :: LBall) in *.
  assert (INS2 : In (ps, S, 40) LB2) by (subst LB2; right; left; reflexivity).
  assert (FRM02 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st2 LB2 ((pk, 40) :: (ps, 40) :: L) m2).
  { eapply cframe_call; [exact FRM01| exact FRM2| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRM01 CFR2 FRM2 CONF1 FR1 REPL1 SBLK KP2 MU1 WM1.
  pose proof (munch_refl [(S, S + 40)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. step. step. rewrite ?(unsigned_lit S) by lia. rewrite (ubs_land7 S) by (destruct RS as (_ & RS16 & _); lia).
  if_cases KS1; zify_cond KS1. { exfalso. apply KS1. reflexivity. } clear KS1.
  cstep. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into mc end.
  lazymatch goal with H : stk _ mc _ _ |- _ => rename H into STc end.
  lazymatch goal with H : mem_inv _ mc |- _ => rename H into MIc end.
  lazymatch goal with H : rw_cells usegs mc S _ |- _ => rename H into SBLKc end.
  lazymatch goal with H : rw_cells usegs mc (bv_unsigned sp + -80) _ |- _ => rename H into CONFc end.
  lazymatch goal with H : rw_cells usegs mc (bv_unsigned sp + -32) _ |- _ => rename H into FRc2 end.
  lazymatch goal with H : rw_cells usegs mc 3477520 _ |- _ => rename H into REPLc end.
  assert (CSTc : cstate st2 LB2 LB ((pk, 40) :: (ps, 40) :: L) mc (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m2 mc _ _ _ lo Bd (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MIc| | lia| lia| | rewrite unsigned_lit by lia; exact STc| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply (cwin_block _ _ _ (ps, S, 40)); [exact INS2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRMc : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st2 LB2 ((pk, 40) :: (ps, 40) :: L) mc).
  { eapply cframe_seg; [exact FRM02| exact MU2| exact WM2| exact HP2| lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (ps, S, 40)); [exact INS2| exact NPS| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil]. }
  clear FRM02 MU2 WM2.
  eapply climpl_seq.
  { eapply HTN with (CONF := bv_unsigned sp + -80) (lo := lo) (B := Bd); [clear - Hf FU1 FU2; lia| clear - RA RB RC GR1 GR2; unfold croom, cgrow in *; lia| exact CSTc
      | rewrite unsigned_lit by lia; lia| reflexivity| rewrite unsigned_lit by lia; lia| clear - SP16; lia| exact CONFc| unfold RMALLOC_REPLACED; exact REPLc]. }
  intros f3 L3 st3 ms3 (v3 & m3 & LBall3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (ph & pka & pmd & pn & pr & pq & HT & LKa & MD & NB & R & Q & -> & -> & -> & RH & RKa & RMD & RNB & RR & RQ)).
  destruct RET3 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). unfold NB_BYTES in *. change (32768 + 48) with 32816 in *.
  cret_lit. repeat (rewrite unsigned_lit in FRM3 by lia).
  pose proof FRM3 as (CFR3 & KP3 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FRc2 ltac:(lia)) as FR3.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 CONFc ltac:(lia)) as CONF3.
  cst_static CFR3 REPLc REPL3.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 40) CFR3 SBLKc INS2 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as SBLK3.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  rewrite unsigned_lit in ST3 by lia.
  pose proof RH as (HT0 & _ & _ & HTC & HTIMG).
  set (LB3 := (pq, Q, 16) :: (pr, R, 264) :: (pn, NB, 32768) :: (pmd, MD, 24) :: (pka, LKa, 40) :: (ph, HT, 96) :: LB2) in *.
  assert (INS3 : In (ps, S, 40) LB3) by (subst LB3 LB2; do 7 right; left; reflexivity).
  assert (FRM03 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st3 LB3
                    ((pq, 16) :: (pr, 264) :: (pn, 32816) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: (pk, 40) :: (ps, 40) :: L) m3).
  { eapply cframe_call; [exact FRMc| exact FRM3| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRMc CSTc CFR3 FRM3 CONFc FRc2 REPLc SBLKc KP3.
  pose proof (munch_refl [(S, S + 40)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
  (* [comment removed for export] *)
  cprefix. cstep. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. } clear K3.
  step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into md end.
  lazymatch goal with H : stk _ md _ _ |- _ => rename H into STd end.
  lazymatch goal with H : mem_inv _ md |- _ => rename H into MId end.
  lazymatch goal with H : rw_cells usegs md S _ |- _ => rename H into SBLKd end.
  lazymatch goal with H : rw_cells usegs md (bv_unsigned sp + -32) _ |- _ => rename H into FRd3 end.
  assert (CSTd : cstate st3 LB3 LB ((pq, 16) :: (pr, 264) :: (pn, 32816) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: (pk, 40) :: (ps, 40) :: L) md
                   (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m3 md _ _ _ lo Bd (bv_unsigned sp)); [exact CST3| exact MU3| exact WM3| exact MId| | lia| lia| | rewrite unsigned_lit by lia; exact STd| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply (cwin_block _ _ _ (ps, S, 40)); [exact INS3| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRMd : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st3 LB3 ((pq, 16) :: (pr, 264) :: (pn, 32816) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: (pk, 40) :: (ps, 40) :: L) md).
  { eapply cframe_seg; [exact FRM03| exact MU3| exact WM3| exact HP3| lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (ps, S, 40)); [exact INS3| exact NPS| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil]. }
  clear FRM03 MU3 WM3.
  eapply climpl_seq.
  { eapply SKN with (lo := lo) (B := Bd); [clear - Hf FU1 FU2 FU3; lia| rewrite W56a, W56b, W56c; clear - RA RB RC GR1 GR2 GR3; unfold croom, cgrow in *; lia| exact CSTd
      | rewrite unsigned_lit by lia; lia]. }
  intros f4 L4 st4 ms4 (v4 & m4 & LBall4 & RET4 & FU4 & GR4 & CST4 & FRM4 & (pt & SK & -> & -> & -> & RSK & SKC)).
  destruct RET4 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM4 by lia). rewrite W56a, W56b, W56c in GR4.
  pose proof FRM4 as (CFR4 & KP4 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 FRd3 ltac:(lia)) as FR4.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 CONF3 ltac:(lia)) as CONF4.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 40) CFR4 SBLKd INS3 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as SBLK4.
  pose proof CST4 as (HP4 & _ & (errv4 & _ & _ & ST4 & _ & _ & MI4 & _) & _).
  rewrite unsigned_lit in ST4 by lia.
  pose proof RSK as (SK0 & _ & _ & SKCe & SKIMG).
  set (LB4 := (pt, SK, 56) :: LB3) in *.
  assert (INS4 : In (ps, S, 40) LB4) by (subst LB4 LB3 LB2; do 8 right; left; reflexivity).
  assert (INT4 : In (pt, SK, 56) LB4) by (subst LB4; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST4) as [ND4 _].
  assert (NEts : ps <> pt) by (eapply cstate_head_fresh; [exact CST4|]; subst LB3 LB2; do 7 right; left; reflexivity).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST4 INS4 INT4 NEts) as APts.
  assert (NPT : forall b0, In b0 LBall -> ~ False -> blk_id b0 <> pt).
  { intros b0 Hb0 _. apply (t_fresh_notin (fun _ => False) LBall (pt, SK, 56)); [| exact Hb0| intros X; exact X].
    exact (t_nodup_prefix blk_id [(pt, SK, 56); (pq, Q, 16); (pr, R, 264); (pn, NB, 32768); (pmd, MD, 24); (pka, LKa, 40); (ph, HT, 96); (pk, LK, 40); (ps, S, 40)] LBall (pt, SK, 56) ND4 ltac:(left; reflexivity)). }
  hide NEts. clear ND4.
  assert (FRM04 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st4 LB4 ((pt, 56) :: (pq, 16) :: (pr, 264) :: (pn, 32816) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: (pk, 40) :: (ps, 40) :: L) m4).
  { eapply cframe_call; [exact FRMd| exact FRM4| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRMd CSTd CFR4 FRM4 FRd3 SBLKd KP4 CONF3.
  unfold sk_cells in SKC.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp - 80); (SK + 32, SK + 56); (S, S + 40)]%Z m4) as MU4. pose proof (wmono_refl usegs m4) as WM4.
  (* [comment removed for export] *)
  assert (SK8 : SK mod 8 = 0) by (destruct RSK as (_ & RSK16 & _); lia). cprefix. step.
  tcallr nm_sk3. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR].
  cstep. step. if_cases K4; zify_cond K4. 2: { exfalso. rewrite ?unsigned_lit in K4 by lia. lia. } clear K4.
  step. do 4 step.
  lazymatch goal with H : stk usegs ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into STz end.
  lazymatch goal with H : rw_cells usegs ?mx (bv_unsigned sp + -80) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into FRz0 end.
  lazymatch goal with H : rw_cells usegs ?mx (bv_unsigned sp + -32) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into FRz1 end.
  unfold ht_conf in FRz0. release_frame FRz0 STz (bv_unsigned sp - 32). release_frame FRz1 STz (bv_unsigned sp). step. step.
  chere. apply climpl_done.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mz end.
  lazymatch goal with H : stk usegs mz lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv usegs mz |- _ => rename H into MIf end.
  lazymatch goal with H : rw_cells usegs mz S _ |- _ => rename H into SBLKf end.
  exists (Z_to_bv 64 S), mz, LB4.
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear - Hf FU1 FU2 FU3 FU4; lia|]. split; [clear - GR1 GR2 GR3 GR4; unfold cgrow in *; lia|].
  split. { eapply (cstate_seg _ _ _ _ _ m4 mz _ sp _ lo Bd (bv_unsigned sp)); [exact CST4| exact MU4| exact WM4| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pt, SK, 56)); [exact INT4| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (ps, S, 40)); [exact INS4| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [exact FRM04| exact MU4| exact WM4| exact HP4| lia|]. apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (pt, SK, 56)); [exact INT4| exact NPT| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (ps, S, 40)); [exact INS4| exact NPS| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil]. }
  exists ps, pk, ph, pka, pmd, pn, pr, pq, pt, S, LK, HT, LKa, MD, NB, R, Q, SK. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact RS|]. split; [exact RK|]. split; [exact RH|]. split; [exact RKa|]. split; [exact RMD|]. split; [exact RNB|]. split; [exact RR|]. split; [exact RQ|]. split; [exact RSK|].
  exact SBLKf.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_STORED_NAMEMAP_NEW : Z := 0xf76a4.
Definition SNM_STACK : Z := 16 + NMN_STACK.

Definition stored_namemap_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (ps pk ph pka pmd pn pr pq pt : bptr) (S LK HT LKa MD NB R Q SK : Z),
       v = Z_to_bv 64 S
    /\ LBall' = (pt, SK, 56) :: (pq, Q, 16) :: (pr, R, 264) :: (pn, NB, 32768) :: (pmd, MD, 24) :: (pka, LKa, 40) :: (ph, HT, 96) :: (pk, LK, 40) :: (ps, S, 40) :: LBall
    /\ L' = (pt, 56) :: (pq, 16) :: (pr, 264) :: (pn, 32816) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: (pk, 40) :: (ps, 40) :: L
    /\ rblock_range S 40 /\ rblock_range LK 40 /\ rblock_range HT 96 /\ rblock_range LKa 40 /\ rblock_range MD 24 /\ rblock_range NB 32768
    /\ rblock_range R 264 /\ rblock_range Q 16 /\ rblock_range SK 56.

Definition ossl_stored_namemap_new_fp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (9 <= f)%nat -> croom L 7 2 49464 -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SNM_STACK -> bv_unsigned sp mod 16 = 0 ->
  a0 = Z_to_bv 64 0x32dec8 -> rw_cells usegs m 0x351010 [C4 (Z_to_bv 64 0)] ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_STORED_NAMEMAP_NEW) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 9 7 2 49464 (stored_namemap_res LBall L)).

Lemma stored_namemap_of_namemap : namemap_new_fp_stmt -> ossl_stored_namemap_new_fp_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros NMN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd
         Hf ROOM CST SLO SP16 -> REPL.
  unfold namemap_new_fp_stmt in NMN.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold SNM_STACK, NMN_STACK, HTN_STACK, RCU_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_STORED_NAMEMAP_NEW in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (rw_cells_bound _ _ _ _ REPL) as RB0. cbn [cells_size csize Nat.add] in RB0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. th_frame 16%nat [8; 8]%nat ST. do 3 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  lazymatch goal with H : rw_cells usegs ma 3477520 _ |- _ => rename H into REPLa end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -16)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRMa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply NMN with (lo := lo) (B := Bd); [exact Hf| exact ROOM| exact CSTa| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; clear - SP16; lia| reflexivity| exact REPLa]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (ps & pk & ph & pka & pmd & pn & pr & pq & pt & S & LK & HT & LKa & MD & NB & R & Q & SK
                          & -> & -> & -> & RS & RK & RH & RKa & RMD & RNB & RR & RQ & RSK & SBLK)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia).
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RS as (S0 & _ & _ & SC & SIMG).
  unfold nm_cells in SBLK.
  apply (th_cells_congr usegs m1 S _ (C1 (Z_to_bv 8 0) :: CB 7 (zeros 7) :: [C8 (Z_to_bv 64 HT); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 SK); C8 z64])) in SBLK; [| reflexivity | reflexivity | cbn; repeat split; reflexivity].
  set (LB1 := (pt, SK, 56) :: (pq, Q, 16) :: (pr, R, 264) :: (pn, NB, 32768) :: (pmd, MD, 24) :: (pka, LKa, 40) :: (ph, HT, 96) :: (pk, LK, 40) :: (ps, S, 40) :: LBall) in *.
  assert (INS1 : In (ps, S, 40) LB1) by (subst LB1; do 8 right; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (NPS : forall b0, In b0 LBall -> ~ False -> blk_id b0 <> ps).
  { intros b0 Hb0 _. apply (t_fresh_notin (fun _ => False) LBall (ps, S, 40)); [| exact Hb0| intros X; exact X].
    exact (t_nodup_prefix blk_id [(pt, SK, 56); (pq, Q, 16); (pr, R, 264); (pn, NB, 32768); (pmd, MD, 24); (pka, LKa, 40); (ph, HT, 96); (pk, LK, 40); (ps, S, 40)] LBall (ps, S, 40) ND1 ltac:(do 8 right; left; reflexivity)). }
  clear ND1.
  assert (FRM01 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st1 LB1 ((pt, 56) :: (pq, 16) :: (pr, 264) :: (pn, 32816) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: (pk, 40) :: (ps, 40) :: L) m1).
  { eapply cframe_call; [exact FRMa| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRMa CSTa CFR1 FRM1 KP1 REPLa.
  pose proof (munch_refl [(S, S + 1)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. rewrite ?(unsigned_lit S) by lia. rewrite (ubs_land7 S) by (destruct RS as (_ & RS16 & _); lia).
  if_cases KS2; zify_cond KS2. { exfalso. apply KS2. reflexivity. } clear KS2.
  step. step. cstep. do 2 step.
  lazymatch goal with H : stk usegs ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into STz end.
  release_frame FR1 STz (bv_unsigned sp). step. step.
  chere. apply climpl_done.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mz end.
  lazymatch goal with H : stk usegs mz lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv usegs mz |- _ => rename H into MIf end.
  exists (Z_to_bv 64 S), mz, LB1.
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear - Hf FU1; lia|]. split; [exact GR1|].
  split. { eapply (cstate_seg _ _ _ _ _ m1 mz _ sp _ lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [| apply Forall_nil]. apply (cwin_block _ _ _ (ps, S, 40)); [exact INS1| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [exact FRM01| exact MU1| exact WM1| exact HP1| lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (ps, S, 40)); [exact INS1| exact NPS| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia. }
  exists ps, pk, ph, pka, pmd, pn, pr, pq, pt, S, LK, HT, LKa, MD, NB, R, Q, SK. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact RS|]. split; [exact RK|]. split; [exact RH|]. split; [exact RKa|]. split; [exact RMD|]. split; [exact RNB|]. split; [exact RR|]. split; [exact RQ| exact RSK].
Qed.

(* [comment removed for export] *)
Theorem ossl_stored_namemap_new_fp_spec : crypto_zalloc_stmt -> crypto_aligned_alloc_stmt -> ossl_stored_namemap_new_fp_stmt.
Proof.
  intros CZ CAA. pose proof (crypto_calloc_spec CZ) as CC. apply stored_namemap_of_namemap.
  apply (namemap_new_fp_spec CZ (T_lock_new_spec CZ)); [| exact (T_sk_new_null_spec CZ)].
  apply (ht_new_fp_spec CZ (T_lock_new_spec CZ)); [exact (anl_spec (crypto_aligned_alloc_array_spec CAA))| exact (T_rcu_new_spec CZ CC)].
Qed.
End WithCeiling0.
