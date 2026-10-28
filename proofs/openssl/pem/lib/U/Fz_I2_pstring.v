(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_calloc Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_rep Fz_I1_new. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_lock_new Fz_T_sk.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition FZ_PROP_STRING_DATA_NEW : Z := 0xf08d0.
Definition PSD_STACK : Z := 96 + LHN_STACK.

Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

(* [comment removed for export] *)
Definition psd_sk3_post (sp gp tp t0 t1 t2 s0 s1 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (Q lo PC : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (Z_to_bv 64 PC) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Q) (Z_to_bv 64 0xf0b2c) a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0xf0ad8) (Z_to_bv 64 0xf0b04) (Z_to_bv 64 0xf0b2c) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PC) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (Q + 32, Q + 56)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' Q (sk_cells z64 z64 z64 (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 0xf0ad8) (Z_to_bv 64 0xf0b2c) (Z_to_bv 64 0xf0b04)).

Lemma psd_sk3a : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Q lo : Z),
  a0 = Z_to_bv 64 Q -> 0 < Q -> Q mod 8 = 0 -> Q + 56 <= alloc_ceiling ->
  rw_cells usegs m Q (sk_cells z64 z64 z64 (Z_to_bv 64 1) z64 z64 z64 z64 z64) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  evt usegs (psd_sk3_post sp gp tp t0 t1 t2 s0 s1 s5 s6 s7 s8 s9 s10 s11 z64 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc Q lo 0xf09d4 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf09a4) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros -> Q0 Q8 QC QCELLS ST LO SLO MI. unfold ceil_window in CEIL_RANGE__.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (Q + 32, Q + 56)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold sk_cells in QCELLS.
  do 3 step. step. tcallr T_sk_set_cmp_thunks_proof. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR]. cbn [fst snd] in *.
  do 3 step. step. tcallr T_sk_set_copy_thunks_proof. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR]. cbn [fst snd] in *.
  do 3 step. step. tcallr T_sk_set_thunks_proof. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR]. cbn [fst snd] in *.
  apply evt_done. unfold psd_sk3_post, sk_cells. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

Lemma psd_sk3b : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Q lo : Z),
  a0 = Z_to_bv 64 Q -> 0 < Q -> Q mod 8 = 0 -> Q + 56 <= alloc_ceiling ->
  rw_cells usegs m Q (sk_cells z64 z64 z64 (Z_to_bv 64 1) z64 z64 z64 z64 z64) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  evt usegs (psd_sk3_post sp gp tp t0 t1 t2 s0 s1 s5 s6 s7 s8 s9 s10 s11 z64 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc Q lo 0xf09f4 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0xf0ad8) (Z_to_bv 64 0xf0b04) (Z_to_bv 64 0xf0b2c) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xf09dc) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros -> Q0 Q8 QC QCELLS ST LO SLO MI. unfold ceil_window in CEIL_RANGE__.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (Q + 32, Q + 56)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold sk_cells in QCELLS.
  step. step. tcallr T_sk_set_cmp_thunks_proof. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR]. cbn [fst snd] in *.
  step. step. tcallr T_sk_set_copy_thunks_proof. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR]. cbn [fst snd] in *.
  step. step. tcallr T_sk_set_thunks_proof. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR]. cbn [fst snd] in *.
  apply evt_done. unfold psd_sk3_post, sk_cells. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

Definition pstring_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (ps pk pl1 pb1 pl2 pb2 pq1 pq2 : bptr) (S LK lh1 B1 lh2 B2 Q1 Q2 : Z),
    v = Z_to_bv 64 S
    /\ LBall' = (pq2, Q2, 56) :: (pq1, Q1, 56) :: (pb2, B2, 128) :: (pl2, lh2, 104) :: (pb1, B1, 128) :: (pl1, lh1, 104) :: (pk, LK, 40) :: (ps, S, 48) :: LBall
    /\ L' = (pq2, 56) :: (pq1, 56) :: (pb2, 128) :: (pl2, 104) :: (pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L
    /\ rblock_range S 48 /\ rblock_range LK 40 /\ rblock_range lh1 104 /\ rblock_range B1 128 /\ rblock_range lh2 104 /\ rblock_range B2 128
    /\ rblock_range Q1 56 /\ rblock_range Q2 56.

Definition ossl_property_string_data_new_fp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (8 <= f)%nat -> croom L 8 0 0 -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - PSD_STACK ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_PROP_STRING_DATA_NEW) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 8 8 0 0 (pstring_res LBall L)).

Theorem ossl_property_string_data_new_fp_spec :
  crypto_zalloc_stmt -> T_lock_new_stmt -> lh_new_stmt -> T_sk_new_null_stmt -> ossl_property_string_data_new_fp_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ LKN LHN SKN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd
         Hf ROOM CST SLO.
  unfold crypto_zalloc_stmt in CZ. unfold T_lock_new_stmt in LKN. unfold lh_new_stmt in LHN. unfold T_sk_new_null_stmt in SKN.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold PSD_STACK, LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_PROP_STRING_DATA_NEW in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  destruct (wA_small 48 ltac:(unfold TIER_A_MAX; lia)) as (W48a & W48b & W48c). destruct (wA_small 40 ltac:(unfold TIER_A_MAX; lia)) as (W40a & W40b & W40c).
  destruct (wA_small 56 ltac:(unfold TIER_A_MAX; lia)) as (W56a & W56b & W56c).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 9 step. step. do 4 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SPR GLO SLO LO. lia. }
  assert (FRa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply CZ with (n := 48) (lo := lo) (B := Bd); [lia| rewrite W48a, W48b, W48c; unfold croom in *; lia| lia| exact CSTa| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (ps & S & -> & -> & -> & RS & SBLK)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). rewrite W48a, W48b, W48c in GR1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RS as (S0 & _ & _ & SC & SIMG). hide RS. hide SIMG. hide FU1. hide GR1. hide Hf.
  change (Z.to_nat 48) with 48%nat in SBLK.
  apply (th_cells_congr usegs m1 S _ [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64]) in SBLK; [| reflexivity | reflexivity | cbn; tauto].
  assert (FRM0 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st1 ((ps, S, 48) :: LBall) ((ps, 48) :: L) m1).
  { eapply cframe_call; [exact FRa| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRa CSTa CFR1 FRM1.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. chere.
  eapply climpl_seq.
  { eapply LKN with (lo := lo) (B := Bd); [unfold hideP in *; lia| unfold hideP in *; rewrite W40a, W40b, W40c; unfold croom, cgrow in *; lia| exact CST1| rewrite unsigned_lit by lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pk & LK & -> & -> & -> & RK & MC2)).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM2 by lia). rewrite W40a, W40b, W40c in GR2.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  assert (INS1 : In (ps, S, 48) ((ps, S, 48) :: LBall)) by (left; reflexivity).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR2 SBLK INS1 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as SBLK2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RK as (LK0 & _ & _ & LKC & LKIMG). hide RK. hide LKIMG. hide FU2. hide GR2.
  set (LB2 := (pk, LK, 40) :: (ps, S, 48) :: LBall) in *.
  assert (INS2 : In (ps, S, 48) LB2) by (subst LB2; right; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _].
  assert (FRb : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st2 LB2 ((pk, 40) :: (ps, 48) :: L) m2).
  { eapply cframe_call; [exact FRM0| exact FRM2| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRM0 CFR2 FRM2 MU1 WM1.
  pose proof (munch_refl [(S, S + 8)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. step. step. rewrite ?(unsigned_lit S) by lia. rewrite (ubs_land7 S) by (unfold hideP in RS; destruct RS as (_ & RS16 & _); lia).
  if_cases KS1; zify_cond KS1. { exfalso. apply KS1. reflexivity. } clear KS1.
  step. do 4 step. do 2 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into mc end.
  lazymatch goal with H : stk _ mc _ _ |- _ => rename H into STc end.
  lazymatch goal with H : mem_inv _ mc |- _ => rename H into MIc end.
  lazymatch goal with H : rw_cells usegs mc S _ |- _ => rename H into SBLKc end.
  assert (CSTc : cstate st2 LB2 LB ((pk, 40) :: (ps, 48) :: L) mc (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m2 mc _ _ _ lo Bd (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MIc| | lia| lia| | rewrite unsigned_lit by lia; exact STc| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [| apply Forall_nil]. apply (cwin_block _ _ _ (ps, S, 48)); [exact INS2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in SIMG, S0. clear - SPR GLO SLO LO SIMG S0. lia. }
  assert (FRc : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st2 LB2 ((pk, 40) :: (ps, 48) :: L) mc).
  { eapply cframe_seg; [exact FRb| exact MU2| exact WM2| exact HP2| lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (ps, S, 48)); [exact INS2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pk, LK, 40); (ps, S, 48)] LBall (ps, S, 48) ND2 ltac:(right; left; reflexivity)) as NI.
    apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
  clear FRb.
  eapply climpl_seq.
  { eapply LHN with (DV := fun _ => True) (h := 0xf0a5c) (c := 0xf0a90) (lo := lo) (B := Bd);
      [unfold hideP in *; lia| unfold hideP in *; unfold croom, cgrow in *; lia| lia| lia| exact CSTc| rewrite unsigned_lit by lia; unfold LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  intros f3 L3 st3 ms3 (v3 & m3 & LBall3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (pl1 & pb1 & lh1 & B1 & -> & -> & -> & REP1)).
  destruct RET3 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM3 by lia).
  pose proof FRM3 as (CFR3 & KP3 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FR2 ltac:(lia)) as FR3.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR3 SBLKc INS2 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as SBLK3.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  rewrite unsigned_lit in ST3 by lia.
  pose proof REP1 as (_ & _ & _ & (y40 & y48 & err1 & pad1 & SC1) & _). clear REP1.
  set (LB3 := (pb1, B1, 128) :: (pl1, lh1, 104) :: LB2) in *.
  assert (INL1 : In (pl1, lh1, 104) LB3) by (subst LB3; right; left; reflexivity).
  assert (INB1 : In (pb1, B1, 128) LB3) by (subst LB3; left; reflexivity).
  assert (INS3 : In (ps, S, 48) LB3) by (subst LB3 LB2; do 3 right; left; reflexivity).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST3 INL1) as RL1. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST3 INB1) as RB1.
  pose proof RL1 as (L10 & L116 & _ & L1C & L1IMG). hide RL1. hide RB1. hide L1IMG. hide FU3. hide GR3.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [ND3 _].
  assert (NEls : pl1 <> ps). { intros E1. destruct (cown_block_eq _ _ _ _ _ _ ND3 INL1 ltac:(rewrite E1; exact INS3)) as [_ X]. discriminate X. }
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST3 INL1 INS3 NEls) as APLS. hide NEls.
  unfold lh_cells, wz in SC1. cbn [lf_comp lf_hash lf_hashw lf_compw g_nn g_na g_p g_pmax g_items] in SC1.
  assert (FRd : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st3 LB3 ((pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L) m3).
  { eapply cframe_call; [exact FRc| exact FRM3| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRc CSTc CFR3 FRM3 MU2 WM2.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp - 80); (lh1 + 24, lh1 + 56); (S + 8, S + 16)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
  (* [comment removed for export] *)
  cprefix. do 8 step. do 4 step. step.
  calle (eapply lh_set_thunks_spec with (f := mkFns 0xf0a90 0xf0a5c 0 0) (lh := lh1) (B := B1) (g := mkGeo 8 16 0 8 0) (lo := lo)); try lia.
  all: try (unfold lh_cells, wz; cbn [lf_comp lf_hash lf_hashw lf_compw g_nn g_na g_p g_pmax g_items]; exact SC1).
  step. do 2 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into md end.
  lazymatch goal with H : stk _ md _ _ |- _ => rename H into STd end.
  lazymatch goal with H : mem_inv _ md |- _ => rename H into MId end.
  lazymatch goal with H : rw_cells usegs md S _ |- _ => rename H into SBLKd end.
  assert (CSTd : cstate st3 LB3 LB ((pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L) md (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m3 md _ _ _ lo Bd (bv_unsigned sp)); [exact CST3| exact MU3| exact WM3| exact MId| | lia| lia| | rewrite unsigned_lit by lia; exact STd| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pl1, lh1, 104)); [exact INL1| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (ps, S, 48)); [exact INS3| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in L1IMG, L10, SIMG, S0. clear - SPR GLO SLO LO L1IMG L10 SIMG S0. lia. }
  assert (FRe : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st3 LB3 ((pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L) md).
  { eapply cframe_seg; [exact FRd| exact MU3| exact WM3| exact HP3| lia|]. apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (pl1, lh1, 104)); [exact INL1| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pb1, B1, 128); (pl1, lh1, 104); (pk, LK, 40); (ps, S, 48)] LBall (pl1, lh1, 104) ND3 ltac:(right; left; reflexivity)) as NI.
      apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
    apply Forall_cons; [| apply Forall_nil]. apply (cseg_ok_block _ _ _ _ _ (ps, S, 48)); [exact INS3| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pb1, B1, 128); (pl1, lh1, 104); (pk, LK, 40); (ps, S, 48)] LBall (ps, S, 48) ND3 ltac:(do 3 right; left; reflexivity)) as NI.
    apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
  clear FRd.
  eapply climpl_seq.
  { eapply LHN with (DV := fun _ => True) (h := 0xf0a5c) (c := 0xf0a90) (lo := lo) (B := Bd);
      [unfold hideP in *; lia| unfold hideP in *; unfold croom, cgrow in *; lia| lia| lia| exact CSTd| rewrite unsigned_lit by lia; unfold LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  intros f4 L4 st4 ms4 (v4 & m4 & LBall4 & RET4 & FU4 & GR4 & CST4 & FRM4 & (pl2 & pb2 & lh2 & B2 & -> & -> & -> & REP2)).
  destruct RET4 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM4 by lia).
  pose proof FRM4 as (CFR4 & KP4 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 FR3 ltac:(lia)) as FR4.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR4 SBLKd INS3 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as SBLK4.
  pose proof CST4 as (HP4 & _ & (errv4 & _ & _ & ST4 & _ & _ & MI4 & _) & _).
  rewrite unsigned_lit in ST4 by lia.
  pose proof REP2 as (_ & _ & _ & (z40 & z48 & err2 & pad2 & SC2) & _). clear REP2.
  set (LB4 := (pb2, B2, 128) :: (pl2, lh2, 104) :: LB3) in *.
  assert (INL2 : In (pl2, lh2, 104) LB4) by (subst LB4; right; left; reflexivity).
  assert (INB2 : In (pb2, B2, 128) LB4) by (subst LB4; left; reflexivity).
  assert (INS4 : In (ps, S, 48) LB4) by (subst LB4 LB3 LB2; do 5 right; left; reflexivity).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST4 INL2) as RL2. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST4 INB2) as RB2.
  pose proof RL2 as (L20 & L216 & _ & L2C & L2IMG). hide RL2. hide RB2. hide L2IMG. hide FU4. hide GR4. hide APLS. hide L10. hide L1C.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST4) as [ND4 _].
  assert (NEl2s : pl2 <> ps). { intros E1. destruct (cown_block_eq _ _ _ _ _ _ ND4 INL2 ltac:(rewrite E1; exact INS4)) as [_ X]. discriminate X. }
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST4 INL2 INS4 NEl2s) as APL2S. hide NEl2s.
  unfold lh_cells, wz in SC2. cbn [lf_comp lf_hash lf_hashw lf_compw g_nn g_na g_p g_pmax g_items] in SC2.
  assert (FRf : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st4 LB4 ((pb2, 128) :: (pl2, 104) :: (pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L) m4).
  { eapply cframe_call; [exact FRe| exact FRM4| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRe CSTd CFR4 FRM4 MU3 WM3.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp - 80); (lh2 + 24, lh2 + 56); (S + 16, S + 24)]%Z m4) as MU4. pose proof (wmono_refl usegs m4) as WM4.
  (* [comment removed for export] *)
  cprefix. do 4 step. step.
  calle (eapply lh_set_thunks_spec with (f := mkFns 0xf0a90 0xf0a5c 0 0) (lh := lh2) (B := B2) (g := mkGeo 8 16 0 8 0) (lo := lo)); try lia.
  all: try (unfold lh_cells, wz; cbn [lf_comp lf_hash lf_hashw lf_compw g_nn g_na g_p g_pmax g_items]; exact SC2).
  step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into me end.
  lazymatch goal with H : stk _ me _ _ |- _ => rename H into STe end.
  lazymatch goal with H : mem_inv _ me |- _ => rename H into MIe end.
  lazymatch goal with H : rw_cells usegs me S _ |- _ => rename H into SBLKe end.
  assert (CSTe : cstate st4 LB4 LB ((pb2, 128) :: (pl2, 104) :: (pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L) me (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m4 me _ _ _ lo Bd (bv_unsigned sp)); [exact CST4| exact MU4| exact WM4| exact MIe| | lia| lia| | rewrite unsigned_lit by lia; exact STe| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pl2, lh2, 104)); [exact INL2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (ps, S, 48)); [exact INS4| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in L2IMG, L20, SIMG, S0. clear - SPR GLO SLO LO L2IMG L20 SIMG S0. lia. }
  assert (FRg : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st4 LB4 ((pb2, 128) :: (pl2, 104) :: (pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L) me).
  { eapply cframe_seg; [exact FRf| exact MU4| exact WM4| exact HP4| lia|]. apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (pl2, lh2, 104)); [exact INL2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pb2, B2, 128); (pl2, lh2, 104); (pb1, B1, 128); (pl1, lh1, 104); (pk, LK, 40); (ps, S, 48)] LBall (pl2, lh2, 104) ND4 ltac:(right; left; reflexivity)) as NI.
      apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
    apply Forall_cons; [| apply Forall_nil]. apply (cseg_ok_block _ _ _ _ _ (ps, S, 48)); [exact INS4| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pb2, B2, 128); (pl2, lh2, 104); (pb1, B1, 128); (pl1, lh1, 104); (pk, LK, 40); (ps, S, 48)] LBall (ps, S, 48) ND4 ltac:(do 5 right; left; reflexivity)) as NI.
    apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
  clear FRf.
  eapply climpl_seq.
  { eapply SKN with (lo := lo) (B := Bd); [unfold hideP in *; lia| unfold hideP in *; rewrite W56a, W56b, W56c; unfold croom, cgrow in *; lia| exact CSTe| rewrite unsigned_lit by lia; unfold SK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f5 L5 st5 ms5 (v5 & m5 & LBall5 & RET5 & FU5 & GR5 & CST5 & FRM5 & (pq1 & Q1 & -> & -> & -> & RQ1 & QC1)).
  destruct RET5 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM5 by lia). rewrite W56a, W56b, W56c in GR5.
  pose proof FRM5 as (CFR5 & KP5 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR5 FR4 ltac:(lia)) as FR5.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR5 SBLKe INS4 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as SBLK5.
  pose proof CST5 as (HP5 & _ & (errv5 & _ & _ & ST5 & _ & _ & MI5 & _) & _).
  rewrite unsigned_lit in ST5 by lia.
  pose proof RQ1 as (Q10 & _ & _ & Q1C & Q1IMG). hide RQ1. hide Q1IMG. hide FU5. hide GR5. hide APL2S. hide L20. hide L2C.
  set (LB5 := (pq1, Q1, 56) :: LB4) in *.
  assert (INQ1 : In (pq1, Q1, 56) LB5) by (subst LB5; left; reflexivity).
  assert (INS5 : In (ps, S, 48) LB5) by (subst LB5 LB4 LB3 LB2; do 6 right; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST5) as [ND5 _].
  assert (NEq1s : pq1 <> ps). { intros E1. destruct (cown_block_eq _ _ _ _ _ _ ND5 INQ1 ltac:(rewrite E1; exact INS5)) as [_ X]. discriminate X. }
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST5 INQ1 INS5 NEq1s) as APQ1S. hide NEq1s.
  unfold sk_cells in QC1.
  assert (FRh : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st5 LB5 ((pq1, 56) :: (pb2, 128) :: (pl2, 104) :: (pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L) m5).
  { eapply cframe_call; [exact FRg| exact FRM5| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRg CSTe CFR5 FRM5 MU4 WM4.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp - 80); (Q1 + 32, Q1 + 56); (S + 32, S + 40)]%Z m5) as MU5. pose proof (wmono_refl usegs m5) as WM5.
  (* [comment removed for export] *)
  assert (Q18 : Q1 mod 8 = 0) by (unfold hideP in RQ1; destruct RQ1 as (_ & RQ16 & _); lia). cprefix.
  tcallr psd_sk3a. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR].
  step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into mg end.
  lazymatch goal with H : stk _ mg _ _ |- _ => rename H into STg end.
  lazymatch goal with H : mem_inv _ mg |- _ => rename H into MIg end.
  lazymatch goal with H : rw_cells usegs mg S _ |- _ => rename H into SBLKg end.
  assert (CSTg : cstate st5 LB5 LB ((pq1, 56) :: (pb2, 128) :: (pl2, 104) :: (pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L) mg (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m5 mg _ _ _ lo Bd (bv_unsigned sp)); [exact CST5| exact MU5| exact WM5| exact MIg| | lia| lia| | rewrite unsigned_lit by lia; exact STg| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pq1, Q1, 56)); [exact INQ1| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (ps, S, 48)); [exact INS5| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in Q1IMG, Q10, SIMG, S0. clear - SPR GLO SLO LO Q1IMG Q10 SIMG S0. lia. }
  assert (FRi : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st5 LB5 ((pq1, 56) :: (pb2, 128) :: (pl2, 104) :: (pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L) mg).
  { eapply cframe_seg; [exact FRh| exact MU5| exact WM5| exact HP5| lia|]. apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (pq1, Q1, 56)); [exact INQ1| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pq1, Q1, 56); (pb2, B2, 128); (pl2, lh2, 104); (pb1, B1, 128); (pl1, lh1, 104); (pk, LK, 40); (ps, S, 48)] LBall (pq1, Q1, 56) ND5 ltac:(left; reflexivity)) as NI.
      apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
    apply Forall_cons; [| apply Forall_nil]. apply (cseg_ok_block _ _ _ _ _ (ps, S, 48)); [exact INS5| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pq1, Q1, 56); (pb2, B2, 128); (pl2, lh2, 104); (pb1, B1, 128); (pl1, lh1, 104); (pk, LK, 40); (ps, S, 48)] LBall (ps, S, 48) ND5 ltac:(do 6 right; left; reflexivity)) as NI.
    apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
  clear FRh.
  eapply climpl_seq.
  { eapply SKN with (lo := lo) (B := Bd); [unfold hideP in *; lia| unfold hideP in *; rewrite W56a, W56b, W56c; unfold croom, cgrow in *; lia| exact CSTg| rewrite unsigned_lit by lia; unfold SK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f6 L6 st6 ms6 (v6 & m6 & LBall6 & RET6 & FU6 & GR6 & CST6 & FRM6 & (pq2 & Q2 & -> & -> & -> & RQ2 & QC2)).
  destruct RET6 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM6 by lia). rewrite W56a, W56b, W56c in GR6.
  pose proof FRM6 as (CFR6 & KP6 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR6 FR5 ltac:(lia)) as FR6.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR6 SBLKg INS5 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as SBLK6.
  pose proof CST6 as (HP6 & _ & (errv6 & _ & _ & ST6 & _ & _ & MI6 & _) & _).
  rewrite unsigned_lit in ST6 by lia.
  pose proof RQ2 as (Q20 & _ & _ & Q2C & Q2IMG). hide RQ2. hide Q2IMG. hide FU6. hide GR6. hide APQ1S. hide Q10. hide Q1C.
  set (LB6 := (pq2, Q2, 56) :: LB5) in *.
  assert (INQ2 : In (pq2, Q2, 56) LB6) by (subst LB6; left; reflexivity).
  assert (INS6 : In (ps, S, 48) LB6) by (subst LB6 LB5 LB4 LB3 LB2; do 7 right; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST6) as [ND6 _].
  assert (NEq2s : pq2 <> ps). { intros E1. destruct (cown_block_eq _ _ _ _ _ _ ND6 INQ2 ltac:(rewrite E1; exact INS6)) as [_ X]. discriminate X. }
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST6 INQ2 INS6 NEq2s) as APQ2S. hide NEq2s.
  assert (FRj : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st6 LB6 ((pq2, 56) :: (pq1, 56) :: (pb2, 128) :: (pl2, 104) :: (pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L) m6).
  { eapply cframe_call; [exact FRi| exact FRM6| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRi CSTg CFR6 FRM6 MU5 WM5.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp - 80); (Q2 + 32, Q2 + 56); (S + 40, S + 48)]%Z m6) as MU6. pose proof (wmono_refl usegs m6) as WM6.
  (* [comment removed for export] *)
  assert (Q28 : Q2 mod 8 = 0) by (unfold hideP in RQ2; destruct RQ2 as (_ & RQ16 & _); lia). cprefix.
  tcallr psd_sk3b. all: try first [eassumption | reflexivity | lia]. cbv beta delta [mkR].
  step. step.
  step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  unfold hideP in Q10, Q1C, L10, L1C, L20, L2C.
  step. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. } clear K3.
  step. if_cases K4; zify_cond K4. { exfalso. rewrite ?unsigned_lit in K4 by lia. lia. } clear K4.
  step. step. if_cases K5; zify_cond K5. { exfalso. rewrite ?unsigned_lit in K5 by lia. lia. } clear K5.
  step. step. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?unsigned_lit in K6 by lia. lia. } clear K6.
  step. do 9 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into ST7 end.
  lazymatch goal with H : rw_cells usegs mf (bv_unsigned sp + -80) _ |- _ => rename H into FR7 end.
  release_frame FR7 ST7 (bv_unsigned sp). step. step.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  unfold hideP in *.
  chere. apply climpl_done.
  eexists. exists mf, LB6.
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) GR3) GR4) GR5) GR6) as GR.
           clear - GR. unfold cgrow in *. lia. }
  split. { eapply (cstate_seg _ _ _ _ _ m6 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST6| exact MU6| exact WM6| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pq2, Q2, 56)); [exact INQ2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (ps, S, 48)); [exact INS6| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in Q2IMG, Q20, SIMG, S0. clear - SPR GLO SLO LO Q2IMG Q20 SIMG S0. lia. }
  split. { eapply cframe_seg; [exact FRj| exact MU6| exact WM6| exact HP6| lia|]. apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (pq2, Q2, 56)); [exact INQ2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pq2, Q2, 56); (pq1, Q1, 56); (pb2, B2, 128); (pl2, lh2, 104); (pb1, B1, 128); (pl1, lh1, 104); (pk, LK, 40); (ps, S, 48)] LBall (pq2, Q2, 56) ND6 ltac:(left; reflexivity)) as NI.
      apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
    apply Forall_cons; [| apply Forall_nil]. apply (cseg_ok_block _ _ _ _ _ (ps, S, 48)); [exact INS6| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 Hb0 _ E1. pose proof (t_nodup_prefix blk_id [(pq2, Q2, 56); (pq1, Q1, 56); (pb2, B2, 128); (pl2, lh2, 104); (pb1, B1, 128); (pl1, lh1, 104); (pk, LK, 40); (ps, S, 48)] LBall (ps, S, 48) ND6 ltac:(do 7 right; left; reflexivity)) as NI.
    apply NI. cbn [blk_id fst] in E1 |- *. rewrite <- E1. apply in_map. exact Hb0. }
  exists ps, pk, pl1, pb1, pl2, pb2, pq1, pq2, S, LK, lh1, B1, lh2, B2, Q1, Q2.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact RS|]. split; [exact RK|]. split; [exact RL1|]. split; [exact RB1|]. split; [exact RL2|]. split; [exact RB2|]. split; [exact RQ1| exact RQ2].
Qed.
End WithCeiling0.
