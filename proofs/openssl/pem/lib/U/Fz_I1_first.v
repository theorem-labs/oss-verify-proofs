(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_kit_ra Fz_M_realloc Fz_I1_insert Fz_I1_insert1 Fz_cimg_rom. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_T_once Fz_I1_load Fz_I1_retrieve Fz_I1_errload Fz_I1_reason Fz_M_zalloc Fz_M_calloc Fz_I1_new Fz_T_lock_new Fz_I3_base Fz_T_ekit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.


(* [comment removed for export] *)
Lemma lh_rep_fns : forall s DV m m' LBall L f f' lh pl pb B nmb g bks W,
  RHEAP s LBall m -> lh_rep DV m LBall L f lh pl pb B nmb g bks -> munch W m m' -> wmono usegs m m' ->
  (forall a, 0 < a < alloc_ceiling -> (a + 1 <= 0x10000 \/ 0x353000 <= a) -> (a + 1 <= lh \/ lh + 104 <= a) -> outside W a) ->
  (exists x40 x48 err pad, rw_cells usegs m' lh (lh_cells f' B g x40 x48 err pad)) ->
  lh_rep DV m' LBall L f' lh pl pb B nmb g bks.
Proof.
  intros s DV m m' LBall L f f' lh pl pb B nmb g bks W HP REP MU WM OUT SC'.
  destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HP REP) as (S_LB & S_N & _ & _).
  pose proof REP as (G & OL & RL & _ & OB & RB & LEN & CH & EMP & ND). pose proof (lh_geo_bounds g G) as GB.
  pose proof (RHEAP_block_range_proof _ _ _ (pb, B, 8 * g_na g) HP (proj1 OB)) as (B0 & _ & _ & BC & BIMG). unfold blk_addr, blk_size in B0, BC, BIMG. cbn [fst snd] in B0, BC, BIMG.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  split; [exact G|]. split; [exact OL|]. split; [exact RL|]. split; [exact SC'|]. split; [exact OB|]. split; [exact RB|]. split; [exact LEN|].
  split; [| split; [exact EMP| exact ND]].
  intros i Hi. eapply chain_agree; [exact (CH i Hi)| | intros p A _ X; exact X].
  eapply agree_on_mono; [exact AG|]. intros a [Ha|(q & A & Hq & Ha)].
  - apply OUT; clear - Ha Hi GB B0 BC BIMG S_LB; lia.
  - assert (LI : (Z.to_nat i < length bks)%nat) by lia.
    destruct (S_N _ q A LI Hq) as [X1 _].
    pose proof (chain_owns _ _ _ _ _ _ (CH i Hi) q A Hq) as [INA _].
    pose proof (RHEAP_block_range_proof _ _ _ (q, A, 24) HP INA) as (A0 & _ & _ & AC & AIMG). unfold blk_addr, blk_size in A0, AC, AIMG. cbn [fst snd] in A0, AC, AIMG.
    apply OUT; clear - Ha X1 A0 AC AIMG; lia.
Qed.

(* [comment removed for export] *)
Lemma lh_rep_offheap : forall s DV m m' LBall L f lh pl pb B nmb g bks W,
  RHEAP s LBall m -> lh_rep DV m LBall L f lh pl pb B nmb g bks -> munch W m m' -> wmono usegs m m' ->
  (forall a, 0 < a < alloc_ceiling -> (a + 1 <= 0x10000 \/ 0x353000 <= a) -> outside W a) ->
  lh_rep DV m' LBall L f lh pl pb B nmb g bks.
Proof.
  intros s DV m m' LBall L f lh pl pb B nmb g bks W HP REP MU WM OUT.
  pose proof (lh_rep_owned _ _ _ _ _ _ _ _ _ _ _ _ REP) as OWN.
  eapply lh_rep_agree; [exact REP| | intros q A n nm _ X; exact X].
  eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|].
  pose proof REP as (G & OL & _ & _ & OB & _).
  assert (BLK : forall (q : bptr) A n, In (q, A, n) LBall -> forall a, A <= a < A + n -> outside W a).
  { intros q A n IQ a Ha. pose proof (RHEAP_block_range_proof _ _ _ (q, A, n) HP IQ) as (C0 & _ & _ & C & CI). unfold blk_addr, blk_size in C0, C, CI. cbn [fst snd] in C0, C, CI.
    apply OUT; clear - Ha C0 C CI; lia. }
  intros a [Ha|[Ha|(p & A & Hp & Ha)]].
  - eapply (BLK pl lh 104); [exact (proj1 OL)| exact Ha].
  - eapply (BLK pb B (8 * g_na g)); [exact (proj1 OB)| exact Ha].
  - eapply (BLK p A 24); [exact (proj1 (OWN p A Hp))| exact Ha].
Qed.

Definition FZ_DO_ESI : Z := 0xe7df0.
Definition ESI_STACK : Z := 32 + 8320.      (* [comment removed for export] *)
Definition ESI_W : list (Z * Z) := [(0x32e014, 0x32e028)].      (* [comment removed for export] *)

Definition do_esi_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun _ LBall' L' m' => exists (pk pl pb : bptr) (LK lh B : Z),
    LBall' = (pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall /\ L' = (pb, 128) :: (pl, 104) :: (pk, 40) :: L
    /\ lh_rep DVERR m' LBall' L' ERR_FNS lh pl pb B 128 (mkGeo 8 16 0 8 0) (repeat [] 16)
    /\ rw_cells usegs m' LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
    /\ rw_cells usegs m' 0x32e014 [C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)].

Definition do_esi_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z) (od r0 l0 h0 : word),
  (3 <= f)%nat -> croom L 3 0 0 ->
  cstate s LBall LB L m sp tp lo Bd ->
  rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] -> rw_cells usegs m (IC_S + 96) [C8 od] ->
  rw_cells usegs m 0x32e014 [C4 r0; C8 l0; C8 h0] ->
  lo <= bv_unsigned sp - ESI_STACK ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_DO_ESI) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun _ => False) ESI_W 3 3 0 0 (do_esi_res LBall L)).

Theorem do_esi_spec : T_lock_new_stmt -> lh_new_stmt -> do_esi_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LKN LHN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd od r0 l0 h0
         Hf ROOM CST STOP ONCE OD HC SLO.
  unfold T_lock_new_stmt in LKN. unfold lh_new_stmt in LHN.
  pose proof CST as (HP & CO & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold ESI_STACK, GLOBALS_TOP, FZ_DO_ESI, IC_S in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  change (3333664 + 8) with 3333672 in STOP. change (3333664 + 32) with 0x32de40 in ONCE. change (3333664 + 96) with 3333760 in OD.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  cprefix. step. carve_frame 32%nat ST. do 3 step. step. do 2 step. step.
  calle (eapply init_crypto_base_spec with (lo := lo) (od := od)); try (unfold IC_S, IC_BASE_STACK, GLOBALS_TOP; lia).
  do 2 step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe (fun _ : bptr => False) ESI_W (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  destruct (wA_small 40 ltac:(unfold TIER_A_MAX; lia)) as (WA1 & WA2 & WA3).
  chere. eapply climpl_seq.
  { eapply LKN with (lo := lo) (B := Bd); [lia| rewrite WA1, WA2, WA3; unfold croom in *; lia| exact CSTa| rewrite unsigned_lit by lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pk & LK & -> & -> & -> & RGK & MC1)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit.
  pose proof FRM1 as (CFR1 & KP1 & _).
  lazymatch goal with FRh : rw_cells _ ma (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(rewrite unsigned_lit by lia; lia)) as FR1 end.
  i1_static CFR1 HC HC1. i1_static CFR1 STOP STOP1. i1_static CFR1 ONCE ONCE1. i1_static CFR1 OD OD1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RGK as (LK0 & _ & _ & LKC & LKIMG).
  unfold mutex_cells in MC1.
  pose proof (munch_refl [(3334168, 3334176)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 4 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mb end.
  lazymatch goal with H : mem_inv _ mb |- _ => rename H into MIb end.
  lazymatch goal with H : stk _ mb _ _ |- _ => rename H into STb end.
  assert (CSTb : cstate st1 ((pk, LK, 40) :: LBall) LB ((pk, 40) :: L) mb (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m1 mb _ _ tp lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIb| | lia| lia| | rewrite unsigned_lit by lia; exact STb| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_bss; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  destruct GR1 as (G1a & G1b & G1c). rewrite WA1 in G1a. rewrite WA2 in G1b. rewrite WA3 in G1c.
  chere. eapply climpl_seq.
  { eapply LHN with (DV := DVERR) (h := 0xe9010) (c := 0xe9084) (lo := lo) (B := Bd);
      [lia| unfold croom in *; lia| lia| lia| exact CSTb| rewrite unsigned_lit by lia; unfold LHN_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pl & pb & lh & B & -> & -> & -> & REP2)).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(rewrite unsigned_lit by lia; lia)) as FR2.
  i1_static CFR2 HC1 HC2.
  assert (INK1 : In (pk, LK, 40) ((pk, LK, 40) :: LBall)) by (left; reflexivity).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk, LK, 40) CFR2 MC1 INK1 (fun X => X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as MC2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof REP2 as (G2 & OL2 & RL2 & (y40 & y48 & yerr & ypad & SC2) & OB2 & RB2 & LEN2 & CH2 & EMP2 & ND2n).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _].
  assert (INL2 : In (pl, lh, 104) ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall)) by (right; left; reflexivity).
  assert (INK2 : In (pk, LK, 40) ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall)) by (right; right; left; reflexivity).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST2 INL2) as (LH0 & LH16 & _ & LHC & LHIMG).
  assert (NEKL : pk <> pl).
  { intros E. cbn [map blk_id fst] in ND2. apply NoDup_cons_iff in ND2. destruct ND2 as [_ ND2']. apply NoDup_cons_iff in ND2'. destruct ND2' as [NI _].
    apply NI. left. exact E. }
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INK2 INL2 NEKL) as APKL.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (lh + 24, lh + 56); (3334164, 3334184)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. do 8 step. step.
  calle (eapply lh_set_thunks_spec with (f := mkFns 0xe9084 0xe9010 0 0) (lh := lh) (B := B) (g := mkGeo 8 16 0 8 0) (hw := 0xe90d4) (cw := 0xe90f4) (lo := lo)); try lia.
  lazymatch goal with H : rw_cells _ _ lh (lh_cells _ _ _ _ _ _ _) |- _ => unfold lh_cells, wz in H; cbn [lf_comp lf_hash lf_hashw lf_compw g_nn g_na g_p g_pmax g_items] in H; rename H into SC3 end.
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  step. step. cstep.
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk _ mf _ _ |- _ => rename H into STf end.
  release_frame FR2 STf (bv_unsigned sp). step. step.
  lazymatch goal with H : mem_inv _ mf |- _ => rename H into MIf end.
  lazymatch goal with H : stk _ mf _ _ |- _ => rename H into STf2 end.
  lazymatch goal with H : rw_cells _ mf lh _ |- _ => rename H into SCf end.
  lazymatch goal with H : rw_cells _ mf LK _ |- _ => rename H into MCf end.
  lazymatch goal with H : rw_cells _ mf 3334164 _ |- _ => rename H into HCf end.
  chere. apply climpl_done.
  exists (Z_to_bv 64 1), mf, ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ (conj G1a (conj G1b G1c)) GR2) as GR. eapply cgrow_weaken; [exact GR| lia| lia| lia]. }
  split. { eapply (cstate_seg _ _ _ _ _ m2 mf _ sp tp lo Bd (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MIf| | lia| lia| | exact STf2| exact SPB].
    - constructor; [apply cwin_stack; lia| constructor; [| constructor; [apply cwin_bss; lia| constructor]]].
      apply (cwin_block _ _ _ (pl, lh, 104)); [exact INL2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { (* [comment removed for export] *)
    assert (FRb : cframe (fun _ : bptr => False) ESI_W (bv_unsigned sp) s LBall L m st1 ((pk, LK, 40) :: LBall) ((pk, 40) :: L) mb).
    { eapply cframe_seg; [eapply cframe_call; [exact FRa| exact FRM1| rewrite unsigned_lit by lia; lia| intros a X; destruct X| intros q0 _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
      constructor; [| constructor]. apply cseg_ok_static; [lia| lia| intros a Ha; unfold ESI_W; cbn [rin_ivs fst snd]; lia]. }
    eapply cframe_seg; [eapply cframe_call; [exact FRb| exact FRM2| rewrite unsigned_lit by lia; lia| intros a X; destruct X| intros q0 _ X; exact X]| exact MU2| exact WM2| exact HP2| lia|].
    constructor; [apply cseg_ok_stack; lia| constructor; [| constructor; [| constructor]]].
    - apply (cseg_ok_block _ _ _ _ _ (pl, lh, 104)); [exact INL2| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      intros b0 Hb0 _ E. cbn [map blk_id fst] in ND2. apply NoDup_cons_iff in ND2. destruct ND2 as [_ ND2']. apply NoDup_cons_iff in ND2'. destruct ND2' as [NI _].
      apply NI. right. change pl with (blk_id (pl, lh, 104)). rewrite <- E. apply in_map. exact Hb0.
    - apply cseg_ok_static; [lia| lia| intros a Ha; unfold ESI_W; cbn [rin_ivs fst snd]; lia]. }
  exists pk, pl, pb, LK, lh, B. split; [reflexivity|]. split; [reflexivity|].
  split. { eapply (lh_rep_fns st2 DVERR m2 mf); [exact HP2| exact REP2| exact MU2| exact WM2| |].
    - intros a Ha HIMG HLH. cbn [outside]. clear - Ha HIMG HLH LO SLO SPR. lia.
    - do 4 eexists. unfold ERR_FNS, lh_cells, wz. cbn [lf_comp lf_hash lf_hashw lf_compw g_nn g_na g_p g_pmax g_items]. exact SCf. }
  split; [unfold mutex_cells; exact MCf| exact HCf].
Qed.
End WithCeiling0.
