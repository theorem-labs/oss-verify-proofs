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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_kit_ra Fz_M_zalloc Fz_M_calloc. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_LH_NEW : Z := 0xe98d8.
Definition FZ_LH_SET_THUNKS : Z := 0xe9898.
Definition LHN_STACK : Z := 48 + CZ_STACK.

Ltac closed_bytes := vm_compute; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); reflexivity.

(* [comment removed for export] *)
Lemma cells_mid_congr : forall m A pre mid mid' post, cells_bytes mid = cells_bytes mid' -> cells_size mid = cells_size mid' -> cells_wf mid' ->
  rw_cells usegs m A (pre ++ mid ++ post) -> rw_cells usegs m A (pre ++ mid' ++ post).
Proof.
  intros m A pre mid mid' post EB ES WF H. eapply th_cells_congr; [| | | exact H].
  - rewrite !cells_bytes_app, EB. reflexivity.
  - rewrite !cells_size_app, ES. reflexivity.
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W3].
    apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [exact WF| exact W3].
Qed.

Lemma concat_repeat_nil' : forall {X} n, concat (repeat (@nil X) n) = [].
Proof. intros X n. induction n as [|n IH]; cbn; [reflexivity| exact IH]. Qed.

(* [comment removed for export] *)
Definition lh_zero : list cell :=
  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].

Lemma lh_zero_typed : forall m lh, rw_cells usegs m lh [CB 104 (repeat (Z_to_bv 8 0) 104)] -> rw_cells usegs m lh lh_zero.
Proof.
  intros m lh H. eapply th_cells_congr; [| | | exact H]; [closed_bytes| reflexivity| unfold lh_zero; cbn; tauto].
Qed.

Definition lh_new_res (DV : Z -> Prop) (h c : Z) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (pl pb : bptr) (lh B : Z), v = Z_to_bv 64 lh /\ LBall' = (pb, B, 128) :: (pl, lh, 104) :: LBall /\ L' = (pb, 128) :: (pl, 104) :: L
    /\ lh_rep DV m' LBall' L' (mkFns c h 0 0) lh pl pb B 128 (mkGeo 8 16 0 8 0) (repeat [] 16).

Definition lh_new_stmt : Prop :=
  forall (DV : Z -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (h c lo B : Z),
  (2 <= f)%nat -> croom L 2 0 0 -> 0 < h < 2^64 -> 0 < c < 2^64 ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - LHN_STACK -> a0 = Z_to_bv 64 h -> a1 = Z_to_bv 64 c ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_LH_NEW) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 2 2 0 0 (lh_new_res DV h c LBall L)).

Theorem lh_new_spec : crypto_zalloc_stmt -> crypto_calloc_stmt -> lh_new_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ CC DV ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f h c lo Bd
         Hf ROOM HH HC CST SLO -> ->.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_LH_NEW in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  destruct (wA_small 104 ltac:(unfold TIER_A_MAX; lia)) as (WA1 & WA2 & WA3).
  destruct (wA_small (16 * 8) ltac:(unfold TIER_A_MAX; lia)) as (WB1 & WB2 & WB3).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  cprefix. step. carve_frame 48%nat ST. do 5 step. do 3 step. do 4 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  chere.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ s LBall LB L m ma sp _ tp lo Bd (bv_unsigned sp)); try eassumption; try lia.
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  unfold crypto_zalloc_stmt in CZ.
  eapply climpl_seq.
  { eapply CZ with (n := 104); [lia| rewrite WA1, WA2, WA3; eapply croom_weaken; [exact ROOM| lia| lia| lia]| lia| exact CSTa
                               | rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (pl & lh & -> & -> & -> & RNG & BLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (LH0 & LH16 & _ & LHC & LHIMG).
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  step. do 5 step. step.
  chere. unfold crypto_calloc_stmt in CC.
  eapply climpl_seq.
  { eapply CC with (num := 16) (sz := 8); [lia| rewrite WB1, WB2, WB3; eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| rewrite WA1; lia| rewrite WA2; lia| rewrite WA3; lia]
                                          | lia| lia| lia| exact CST1| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pb & B & -> & -> & -> & RNGb & BLKb)).
  destruct RET2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  assert (INL1 : In (pl, lh, 104) ((pl, lh, 104) :: LBall)) by (left; reflexivity).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pl, lh, 104) CFR2 BLK INL1 (fun X => X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia)) as BLK2.
  change (Z.to_nat 104) with 104%nat in BLK2. apply lh_zero_typed in BLK2. unfold lh_zero in BLK2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RNGb as (B0 & _ & _ & BC & BIMG).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _].
  assert (APART : lh + 104 <= B \/ B + 16 * 8 <= lh).
  { pose proof (RHEAP_blocks_disjoint_proof _ _ _ (pl, lh, 104) (pb, B, 16 * 8) HP2 ltac:(right; left; reflexivity) ltac:(left; reflexivity)) as D.
    unfold blk_id, blk_addr, blk_size in D. cbn [fst snd] in D. apply D. intros E. cbn [map blk_id fst] in ND2. apply NoDup_cons_iff in ND2. destruct ND2 as [NI _]. apply NI. left. exact E. }
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (lh, lh + 104)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  cprefix. step. step. ubs_if. cstep. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  step. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  cstep. step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  do 5 step. cstep. cstep. cstep. cstep. step. cstep. step.
  step. do 5 step.
  release_frame FR2 ST2 (bv_unsigned sp). step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : rw_cells _ mf B [CB _ (repeat _ _)] |- _ => rename H into ZB end.
  chere. apply climpl_done.
  exists (Z_to_bv 64 lh), mf, ((pb, B, 16 * 8) :: (pl, lh, 104) :: LBall).
  assert (INL2 : In (pl, lh, 104) ((pb, B, 16 * 8) :: (pl, lh, 104) :: LBall)) by (right; left; reflexivity).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { rewrite WA1, WA2, WA3 in GR1. rewrite WB1, WB2, WB3 in GR2. eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2)| lia| lia| lia]. }
  split. { eapply (cstate_seg _ _ _ _ _ m2 mf _ sp tp lo Bd (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| eassumption| | lia| lia| | exact ST2| exact HB].
    - constructor; [apply cwin_stack; lia| constructor; [| constructor]]. apply (cwin_block _ _ _ (pl, lh, 104)); [exact INL2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ X; exact X]| exact FRM2| lia| intros a X; exact X| intros q0 _ X; exact X]
                              | exact MU2| exact WM2| exact HP2| lia|].
    constructor; [apply cseg_ok_stack; lia| constructor; [| constructor]].
    apply (cseg_ok_block _ _ _ _ _ (pl, lh, 104)); [exact INL2| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
    intros b0 Hb0 _ E. cbn [map blk_id fst] in ND2. apply NoDup_cons_iff in ND2. destruct ND2 as [_ ND2']. apply NoDup_cons_iff in ND2'. destruct ND2' as [NI _].
    apply NI. change pl with (blk_id (pl, lh, 104)). rewrite <- E. apply in_map. exact Hb0. }
  exists pl, pb, lh, B. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  unfold lh_rep. change (g_na (mkGeo 8 16 0 8 0)) with 16. change (g_nn (mkGeo 8 16 0 8 0)) with 8. change (8 * 16) with (16 * 8).
  split; [unfold lh_geo_ok, LH_KMAX; cbn [g_nn g_na g_p g_pmax g_items]; lia|].
  split; [split; [exact INL2| right; left; reflexivity]|]. split; [lia|].
  split. { exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). unfold lh_cells, lf_comp, lf_hash, lf_hashw, lf_compw, wz. cbn [g_nn g_na g_p g_pmax g_items].
    apply (cells_mid_congr mf lh [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
             [C8 (Z_to_bv 64 68719476744)] [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16)]
             [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]);
      [closed_bytes| reflexivity| cbn; tauto|]. cbn [app]. eassumption. }
  split; [split; [left; reflexivity| left; reflexivity]|]. split; [lia|].
  split; [rewrite repeat_length; reflexivity|].
  split. { intros i Hi. rewrite nth_repeat. exists (B + 8 * i). split; [reflexivity|].
    change (Z.to_nat (16 * 8)) with (8 * 16)%nat in ZB.
    pose proof (cells_zero mf B 16 (Z.to_nat i) ZB ltac:(lia)) as C0. rewrite Z2Nat.id in C0 by lia. unfold wz. exact C0. }
  split; [intros i _; apply nth_repeat|].
  rewrite concat_repeat_nil'. cbn [map]. cbn [map blk_id fst] in ND2. apply NoDup_cons_iff in ND2. destruct ND2 as [NI _].
  constructor; [intros [E|[]]; apply NI; left; symmetry; exact E| constructor; [intros []| constructor]].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lh_set_thunks_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    (lh : Z) (cs' : list cell) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lh) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (lh + 24, lh + 56)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' lh cs'.

Theorem lh_set_thunks_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (f : lh_fns) (lh B : Z) (g : lh_geo) (hw cw lo : Z) (x40 x48 err pad : word),
  rw_cells usegs m lh (lh_cells f B g x40 x48 err pad) -> 0 < lh -> lh mod 8 = 0 -> lh + 104 <= alloc_ceiling ->
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 hw -> a2 = Z_to_bv 64 cw ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  evt usegs (lh_set_thunks_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m lh
               (lh_cells (mkFns (lf_comp f) (lf_hash f) hw cw) B g a3 a4 err pad))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_LH_SET_THUNKS) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f lh B g hw cw lo x40 x48 err pad
         SC LH0 LH8 LHC -> -> -> ST CLO SLO MI.
  unfold lh_cells, wz, FZ_LH_SET_THUNKS in *. cbn [lf_comp lf_hash lf_hashw lf_compw].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (lh + 24, lh + 56)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  step. carve_frame 16%nat ST. do 3 step.
  step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
  step. step. ubs_if.
  do 4 cstep. do 2 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  step. step.
  apply evt_done. unfold lh_set_thunks_post. do 15 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.
End WithCeiling0.
