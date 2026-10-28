(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit X_aexdefs Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_hkit4A Atp_fzwA Atp_setcapA Atp_defsA Atp_activewA Atp_pid1A Atp_pidiA Pj_rtkA Pj_cpsA Pj_defsA Pj_hdefsA Imp_hdefsA Imp_ifaceA Imp_libifaceA Imp_ios_defsA Imp_lftoi1A Imp_lftoi2A Imp_lftoi3A Imp_lftoi4A Imp_segdefsA Imp_segA3a Imp_segA3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma rw_cells_asCB : forall (m : mem) A cs, rw_cells bsegs m A cs -> rw_cells bsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. pose proof H as [[WF _] _].
  eapply rw_cells_recastA; [exact H| cbn; split; [exact (cells_bytes_length cs WF)| exact I]| cbn; rewrite app_nil_r; reflexivity| cbn; lia].
Qed.

Lemma shz_ro1 : forall (m : mem) a, shz m a 8 -> a mod 8 = 0 -> 0 <= a < 2^64 -> ro_cells bsegs m (shad a) [C1 z8].
Proof.
  intros m a SZ A8 AR. pose proof (SZ a ltac:(lia)) as H. rewrite ov_rdn in H. cbn [rdn] in H.
  split; [cbn; repeat split; exact I|]. cbn [cells_bytes cbytes app]. unfold shad, SHB.
  split; [Z.div_mod_to_equations; lia|]. split; [cbn [length]; Z.div_mod_to_equations; lia|].
  intros i Hi. destruct i as [|i]; [| cbn [length] in Hi; lia]. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. unfold mrd.
  destruct (m (wa (a / 8 + 2147450880))) as [b|]; [| destruct (seg_rom bsegs (wa (a / 8 + 2147450880))) as [b|]]; cbn in H; try discriminate; injection H as ->; reflexivity.
Qed.

Definition imp_restA (A8 : Z) (m : mem) : Prop :=
  rw_cells bsegs m IMP_AVL_GUARD_A g11
  /\ rw_cells bsegs m IMP_AVP_SPAN_A [C8 (wz IMP_AVP_ARR_A); C8 (wz 1)] /\ rw_cells bsegs m IMP_AVP_GUARD_A g11 /\ rw_cells bsegs m IMP_AVP_ARR_A [C8 (wz SJ_SINGLETON)]
  /\ rw_cells bsegs m IMP_VEC_OBJ_A [C8 (wz A8); C8 (wz (A8 + 8)); C8 (wz (A8 + 8))] /\ rw_cells bsegs m IMP_GUARD_A g11
  /\ rw_cells bsegs m A8 [C8 (wz SJ_SINGLETON)] /\ 0 < A8 /\ A8 mod 16 = 0.

Lemma imp_staticsA_of_rest : forall A8 m, sj_lib m -> imp_restA A8 m -> imp_staticsA (Some A8) m.
Proof. intros A8 m L R. exact (conj L R). Qed.

Definition imp_rest_rng (A8 x : Z) : Prop :=
  (0x6bc000 <= x < 0x6bc018) \/ (0x6bc040 <= x < 0x6bc042) \/ (0x6bc100 <= x < 0x6bc102)
  \/ (0x6bc160 <= x < 0x6bc170) \/ (0x6bc180 <= x < 0x6bc182) \/ (0x6bc1a0 <= x < 0x6bc1a8) \/ (A8 <= x < A8 + 8).

Lemma imp_rest_rng_lib : forall A8 x, imp_rest_rng A8 x -> imp_lib_rng (Some A8) x.
Proof. intros A8 x H. unfold imp_rest_rng in H. unfold imp_lib_rng. lia. Qed.

Lemma imp_restA_agree : forall A8 m m', imp_restA A8 m -> agree_on (imp_rest_rng A8) m m' -> imp_restA A8 m'.
Proof.
  intros A8 m m' (S1 & S2 & S3 & S4 & S5 & S6 & S7 & P0 & P16) AG.
  unfold imp_restA, imp_rest_rng, IMP_AVL_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A, IMP_VEC_OBJ_A, IMP_GUARD_A, g11 in *.
  split; [apply (rw_cells_agree_nw bsegs m m' _ _ S1); intros a Ha; apply AG; cbn in Ha; lia|].
  split; [apply (rw_cells_agree_nw bsegs m m' _ _ S2); intros a Ha; apply AG; cbn in Ha; lia|].
  split; [apply (rw_cells_agree_nw bsegs m m' _ _ S3); intros a Ha; apply AG; cbn in Ha; lia|].
  split; [apply (rw_cells_agree_nw bsegs m m' _ _ S4); intros a Ha; apply AG; cbn in Ha; lia|].
  split; [apply (rw_cells_agree_nw bsegs m m' _ _ S5); intros a Ha; apply AG; cbn in Ha; lia|].
  split; [apply (rw_cells_agree_nw bsegs m m' _ _ S6); intros a Ha; apply AG; cbn in Ha; lia|].
  split; [apply (rw_cells_agree_nw bsegs m m' _ _ S7); intros a Ha; apply AG; cbn in Ha; lia|]. lia.
Qed.

Definition sj4_rng (x : Z) : Prop := (0x6bc120 <= x < 0x6bc128) \/ (0x6bc140 <= x < 0x6bc142) \/ (0x6bc1c0 <= x < 0x6bc1ec) \/ (0x6bc220 <= x < 0x6bc222).
Lemma libm_agree : forall m m', libm m -> agree_on sj4_rng m m' -> libm m'.
Proof.
  intros m m' (L1 & L2 & L3 & L4) AG. unfold libm, sj4_rng in *.
  repeat split;
    first [ apply (rw_cells_agree_nw bsegs m m' _ _ L1) | apply (rw_cells_agree_nw bsegs m m' _ _ L2) | apply (rw_cells_agree_nw bsegs m m' _ _ L3) | apply (rw_cells_agree_nw bsegs m m' _ _ L4) ];
    intros a Ha; apply AG; cbn [cells_size csize Nat.add length] in Ha; unfold one8 in *; lia.
Qed.

Lemma imp_sh_run : forall (m : mem) f i k, rw_cells bsegs m (shad f) (map C1 imp_sh_pro) -> 20 <= i -> (i + Z.of_nat k <= 88)%Z -> 0 <= shad f ->
  bytes_at bsegs m (shad f + i) (repeat z8 k).
Proof.
  intros m f i k SH I0 IK S0. pose proof (imp_sh_pro_run68 m f SH) as [[_ BY] _]. rewrite cells_bytes_map_C1' in BY.
  replace (repeat z8 68) with (repeat z8 (Z.to_nat (i - 20)) ++ repeat z8 k ++ repeat z8 (68 - Z.to_nat (i - 20) - k)) in BY
    by (rewrite <- !repeat_app; f_equal; lia).
  apply bytes_at_app in BY. destruct BY as [_ BY]. apply bytes_at_app in BY. destruct BY as [BY _].
  rewrite repeat_length in BY. replace (shad f + 20 + Z.of_nat (Z.to_nat (i - 20))) with (shad f + i) in BY by lia. exact BY.
Qed.

Section Body.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PDONE : rts RT -> mem -> Z -> list (Z * Z) -> Prop.
Hypothesis PDT : pdtor_cps RT PDONE.
Hypothesis PDFP : pdone_fpA RT PDONE.
Hypothesis PID : pj_pid_cpsA RT (pj_libA sj_lib) PDONE.
Hypothesis OKARM : forall PMc, imp_okarm_cpsA RT PMc.
Local Ltac ul := unfold FUZZ_STACK, PID_STACK, IMP_OKARM_STACK_A, PJ_SER_STACK_A, ser_needA, PJ_TC_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Lemma imp_parser_fobj : forall (Σ : rts RT) (m : mem) f, rw_cells bsegs m (shad f) (map C1 imp_sh_pro) -> rt_frames RT Σ = [(f, 5%nat)] -> 0 < f -> f mod 64 = 0 ->
  fobj RT Σ m (f + 168) 80.
Proof.
  intros Σ m f SH FRS F0 F64. assert (S0 : 0 <= shad f) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((80 + 7) / 8) with 10.
  split; [exists f, 5%nat; rewrite FRS; change (fs_size 5) with 2048; split; [left; reflexivity| lia]|].
  change (Z.to_nat 10) with 10%nat. replace (shad (f + 168)) with (shad f + 21) by (unfold shad; Z.div_mod_to_equations; lia).
  apply (imp_sh_run m f 21 10 SH); [lia| cbn; lia| exact S0].
Qed.

Definition imp_body_costA (n : Z) : Z := pj_pid_costA n + imp_okarm_costA (Z.max n 32 + 67).

Definition bodyB (m : mem) (usp sp' f n d A8 : Z) (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) : Prop :=
  (exists (j0 j8 j160 j192 : list byte), rw_cells bsegs m sp' (imp_localsL j0 j8 f (wz n) d 0 j160 j192))
  /\ stk bsegs m (sp' + 216) (usp - 104) /\ rw_cells bsegs m (usp - 104) (imp_savedA cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11)
  /\ (exists h3, rw_cells bsegs m f (fz_hdr (C8 (wz IMP_MAGIC0)) (C8 (wz IMP_HDR_DESC_A)) (C8 (wz e_fuzz)) h3))
  /\ rw_cells bsegs m (shad f) (map C1 imp_sh_pro)
  /\ ((libm m \/ sj_lib m) /\ imp_restA A8 m /\ LOCBA m /\ locx3 m /\ imp_tplocA m /\ lockwA m) /\ aex6A m.

Definition bodyF (m : mem) (f : Z) : Prop :=
  (exists j9 j25 j65 j108, rw_cells bsegs m (f + 160) (impl0A (wz SJ_SINGLETON) j9 j25 j65 j108))
  /\ slot0A m (f + 296) /\ slot0A m (f + 432) /\ slot0A m (f + 568)
  /\ (exists jsb, rw_cells bsegs m (f + 32) [CB 88 jsb]) /\ (exists jos, rw_cells bsegs m (f + 832) [CB 264 jos]) /\ (exists jtmp, rw_cells bsegs m (f + 1168) [CB 24 jtmp]).

Lemma bodyF_agree : forall m m' f, bodyF m f -> agree_on (fun x => f + 32 <= x < f + 1192) m m' -> bodyF m' f.
Proof.
  intros m m' f ((j9 & j25 & j65 & j108 & FI) & S1 & S2 & S3 & (jsb & FB) & (jos & FO) & (jtmp & FT)) AG.
  split; [exists j9, j25, j65, j108; apply (rw_cells_agree_nw bsegs m m' _ _ FI); intros a Ha; apply AG; rewrite impl0A_size in Ha; lia|].
  split; [apply (slot0A_agree m m' _ S1); intros a Ha; apply AG; lia|].
  split; [apply (slot0A_agree m m' _ S2); intros a Ha; apply AG; lia|].
  split; [apply (slot0A_agree m m' _ S3); intros a Ha; apply AG; lia|].
  split; [exists jsb; apply (rw_cells_agree_nw bsegs m m' _ _ FB); intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia|].
  split; [exists jos; apply (rw_cells_agree_nw bsegs m m' _ _ FO); intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia|].
  exists jtmp; apply (rw_cells_agree_nw bsegs m m' _ _ FT); intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia.
Qed.

Definition bodyZ (usp sp' f A8 : Z) (x : Z) : Prop :=
  (sp' <= x < usp) \/ (f <= x < f + 32) \/ (shad f <= x < shad f + 156) \/ imp_rest_rng A8 x
  \/ (PJ_LOC_LO_A <= x < PJ_LOC_LO_A + 3760) \/ (PJ_LOCKW_A <= x < PJ_LOCKW_A + 4) \/ (TPV_A - 48 <= x < TPV_A - 40) \/ in_ranges IMP_AEX_W x.

Lemma bodyZ_tailZ : forall usp sp' f A8 x, bodyZ usp sp' f A8 x -> tailZ usp sp' f A8 x.
Proof.
  intros usp sp' f A8 x H. unfold bodyZ, tailZ in *. destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; try tauto.
  - do 3 right. left. exact (imp_rest_rng_lib _ _ H).
  - do 3 right. left. unfold imp_lib_rng. do 10 right. left. exact H.
  - do 3 right. left. unfold imp_lib_rng. do 11 right. left. exact H.
  - do 3 right. left. unfold imp_lib_rng. do 12 right. left. exact H.
Qed.

Lemma bodyB_agree4 : forall m m' usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11,
  bodyB m usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 -> sp' + 216 <= usp - 104 ->
  agree_on (bodyZ usp sp' f A8) m m' -> (libm m' \/ sj_lib m') ->
  bodyB m' usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11.
Proof.
  intros until cs11. intros ((j0 & j8 & j160 & j192 & L1) & STp & SV & (h3 & HD) & SH & ((_ & RS & LB & LX & TP & LK) & AX)) LU AG L4. unfold bodyZ in AG.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - exists j0, j8, j160, j192. apply (rw_cells_agree_nw bsegs m m' _ _ L1). intros a Ha. apply AG. rewrite imp_localsL_size in Ha. left. lia.
  - apply (stk_agree_nw bsegs m m' _ _ STp). intros a Ha. apply AG. cbv beta in Ha. left. lia.
  - apply (rw_cells_agree_nw bsegs m m' _ _ SV). intros a Ha. apply AG. rewrite imp_savedA_size in Ha. left. lia.
  - exists h3. apply (rw_cells_agree_nw bsegs m m' _ _ HD). intros a Ha. apply AG. unfold fz_hdr in Ha. cbn [cells_size csize Nat.add] in Ha. right; left. lia.
  - apply (rw_cells_agree_nw bsegs m m' _ _ SH). intros a Ha. apply AG. rewrite cells_size_map_C1' in Ha. unfold imp_sh_pro in Ha. rewrite imp_sh_length in Ha. do 2 right. left. lia.
  - split; [exact L4|]. split; [apply (imp_restA_agree A8 m m' RS); intros a Ha; apply AG; do 3 right; left; exact Ha|]. split; [| split; [| split]].
    + apply (LOCBA_agree m m' LB). intros a Ha. apply AG. do 4 right. left. unfold PJ_LOC_HI_A, PJ_LOC_LO_A in *. lia.
    + destruct LX as (X1 & X2 & X3). unfold locx3, LOC_CVC, LOC_CVW in *. split; [| split];
        [apply (rw_cells_agree_nw bsegs m m' _ _ X1)| apply (rw_cells_agree_nw bsegs m m' _ _ X2)| apply (rw_cells_agree_nw bsegs m m' _ _ X3)];
        intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; do 4 right; left; unfold PJ_LOC_LO_A; lia.
    + unfold imp_tplocA in *. apply (rw_cells_agree_nw bsegs m m' _ _ TP). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. do 6 right. left. lia.
    + apply (lockwA_agree m m' LK). intros a Ha. apply AG. do 5 right. left. exact Ha.
  - apply (aex6A_agree m m' AX). intros a Ha. apply AG. do 7 right. exact Ha.
Qed.

Section WithPM.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Lemma imp_bodyA : forall (Σ0 Σ : rts RT) (K : config -> Prop) (v : option Z) (A8 usp sp' f lo d : Z) (bs : list byte)
    (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) Fr fc (m0 m : mem) (cb : Z),
  let n := Z.of_nat (length bs) in
  impG (rt_sp0 RT Σ0) usp sp' f lo ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo sp' ->
  rt_frames RT Σ = [(f, 5%nat)] -> rt_live RT Σ = xnewA v A8 ++ rt_live RT Σ0 -> rt_sp0 RT Σ = rt_sp0 RT Σ0 -> cb + imp_body_costA n <= rt_credit RT Σ -> 0 <= cb ->
  In (A8, 8) (rt_live RT Σ) -> (forall B, v = Some B -> A8 = B) -> (forall q k, In (q, k) (rt_live RT Σ) -> 0 < k) ->
  Z.of_nat (length (rt_live RT Σ)) + 13 <= LIVE_MAX ->
  0 < d -> n < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p k, In (p, k) (rt_live RT Σ0) /\ p <= d /\ d + n <= p + k) \/ (bs = [] /\ d < SEGTOP_A)) ->
  bodyB m usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 -> bodyF m f ->
  libc_nl m0 -> io_ssp m0 ->
  (forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m a = m0 a) ->
  frm0 fc ->
  imp_fin_k RT PMc K Σ0 v usp lo cra gp (wz TPV_A) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
  aevt Σ K (imp_regsA e_getact (wz IMP_GARET_A) sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz SJ_SINGLETON) (wz SHB) (wz 0) (wz (f + 160)) (wz n) (wz 0) (wz 0) (wz 136) t3 t4 t5 t6 Fr fc m).
Proof using AF RC PDT PDFP PID OKARM FDO MST.
  intros until cb. intros n G ARTx MIx STx FRSx LVx SPx CRx CB0 A8IN VA LVP LVB D0 NB BS INLV BB BF NL0 IOS0 PRES FRM KFIN.
  pose proof (impG_facts _ _ _ _ _ G) as (F0 & FLO & SH0 & SLO & SLO' & GLO & GLO' & LO64 & LSP & LUSP & SPH & SPH' & SP6 & F8).
  pose proof G as (FSEG & F64 & FTOP & SHB0 & SHT & SEP & LOW & LOR & UT & SPR & SPA & SPW & SPT).
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (INF : In (f, 5%nat) (rt_frames RT Σ)) by (rewrite FRSx; left; reflexivity).
  assert (LV0x : forall e, In e (rt_live RT Σ0) -> In e (rt_live RT Σ)) by (intros e He; rewrite LVx; apply in_or_app; right; exact He).
  pose proof (imp_csep RT AF Σ0 Σ m usp sp' f lo ARTx INF LV0x SPx G) as CSEP.
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity. unfold SHB in SHF0.
  pose proof (af_frames_range RT AF Σ m f 5%nat ARTx INF) as (_ & _ & _ & FLV). change (fs_size 5) with 2048 in FLV.
  pose proof (proj1 (af_fshadow_apart RT AF Σ m f 5%nat ARTx INF)) as FSL. change (fs_size 5) with 2048 in FSL.
  assert (SHF : shad (f + 2048) = shad f + 256) by (unfold shad; Z.div_mod_to_equations; lia). rewrite SHF in FSL.
  pose proof (af_live_range RT AF Σ m A8 8 ARTx A8IN) as (_ & A8LO & A8SG). rewrite SPx in A8LO.
  assert (N0 : 0 <= n < 2^26) by (subst n; lia).
  assert (DR : 0 <= d < 2^64).
  { destruct INLV as [(p & k & Hin & P1 & P2)|(E & DL)]; [| clear - D0 DL; ul].
    pose proof (af_live_range RT AF Σ m p k ARTx (LV0x _ Hin)) as (R0 & R1 & R2). pose proof (af_sp0_range RT AF Σ m ARTx). clear - D0 P1 P2 R1 N0 H. ul. }

  assert (NCL : forall x, (f <= x < f + 2048 \/ shad f <= x < shad f + 256 \/ sp' <= x < usp) -> client_static x \/ in_live (rt_live RT Σ) x -> False).
  { intros x Hx [H|H].
    - pose proof (client_static_range _ H) as R. clear - Hx R FSEG SHB0 SPR LOW LOR SPW. ul.
    - destruct H as (p & k & Hin & Hr). pose proof (FLV p k Hin) as Y1. pose proof (FSL p k Hin) as Y2.
      pose proof (af_live_range RT AF Σ m p k ARTx Hin) as (_ & Y3 & _). rewrite SPx in Y3. rewrite SHF0 in Y2, Hx. unfold shad, SHB in Y2. clear - Hx Hr Y1 Y2 Y3 LOW LOR SPR. ul. }
  assert (COK : forall mx, stk bsegs mx lo sp' -> call_ok RT Σ mx (Z_to_bv 64 sp') lo).
  { intros mx STm. unfold call_ok. rewrite EU, SPx. split; [exact STm|]. split; [lia|]. split; [ul|]. split; [ul| clear - SPA; Z.div_mod_to_equations; lia]. }

  assert (NLIOS : forall mx, (forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> mx a = m0 a) ->
            libc_nl mx /\ (forall Σy, ART RT Σy mx -> io_ssp mx)).
  { intros mx PR. split.
    - apply (libc_nl_agree m0 mx NL0). intros a Ha. apply PR; [right; left; apply client_static_intro; unfold LIBC_NL in Ha; lia|].
      unfold LIBC_NL in Ha. unfold IMP_XFP_A, LIB_FP, IMP_FP_A, IMP_AEX_W, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A. aex_lits. cbn [outside app]. repeat split; try exact I; lia.
    - intros Σy HAy. destruct IOS0 as (g & _ & Gc). exists g. split; [exact (proj1 (af_got_lib RT AF Σy mx HAy))|].
      apply (ro_cells_agree bsegs m0 mx _ _ Gc). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PR; [right; left; apply client_static_intro; lia|].
      unfold IMP_XFP_A, LIB_FP, IMP_FP_A, IMP_AEX_W, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A. aex_lits. cbn [outside app]. repeat split; try exact I; lia. }
  pose proof BB as (_ & _ & _ & _ & _ & ((L4 & _) & _)).
  assert (SL120 : rw_cells bsegs m (sp' + 120) [C8 (wz d)]).
  { destruct BB as ((j0 & j8 & j160 & j192 & L1) & _). unfold imp_localsL, imp_locals in L1. cbn [app] in L1.
    lazymatch type of L1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: rest)
        with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] ++ [c14] ++ rest) in L1 end.
    apply rw_cells_app in L1. destruct L1 as [_ L1]. apply rw_cells_app in L1. destruct L1 as [L1 _]. cbn [cells_size csize Nat.add] in L1.
    replace (sp' + Z.of_nat 120) with (sp' + 120) in L1 by lia. exact L1. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { destruct L4 as [L4|[L4|L4]].
    - apply (ga_walk_mid sp' lo _ gp _ t0 t1 t2 _ _ a0 a1 a2 a3 a4 a5 a6 a7 _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 Fr fc m STx ltac:(lia) GLO ltac:(lia) L4 MIx).
    - apply (ga_walk_fresh sp' lo _ gp _ t0 t1 t2 _ _ a0 a1 a2 a3 a4 a5 a6 a7 _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 Fr fc m STx ltac:(lia) GLO ltac:(lia) L4 MIx).
    - apply (ga_walk_init sp' lo _ gp _ t0 t1 t2 _ _ a0 a1 a2 a3 a4 a5 a6 a7 _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 Fr fc m STx ltac:(lia) GLO ltac:(lia) L4 MIx). }
  clear L4. cbv beta. intros ms1 (m1 & RS1 & FC1 & MU1 & WM1 & MI1 & ST1 & LIB1). apply evt_done. revert FC1.
  apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 ms1 (fun ms => ms_fcsr ms = fc -> aevt Σ K ms) RS1).
  intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 FC1. change (fc1 = fc) in FC1. subst fc1.
  rewrite (ret_pc_even IMP_GARET_A) by (unfold IMP_GARET_A; lia).
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (sp' - 32) ARTx ltac:(rewrite SPx; lia)); [| exact WM1].
    intros a Ha. apply MU1. unfold ga_W. cbn [outside]. assert (C1 : ~ (sp' - 32 <= bv_unsigned a < USTACK_TOP)) by (intros Hc; apply Ha; left; exact Hc).
    assert (C2 : ~ client_static (bv_unsigned a)) by (intros Hc; apply Ha; right; left; exact Hc).
    unfold USTACK_TOP in *. repeat split; try exact I; try lia; intros Hc; apply C2; apply client_static_intro; lia. }

  assert (SHA1 : ro_cells bsegs m1 SH_ACTIVE_A [C1 z8]).
  { rewrite SH_ACTIVE_eq. apply shz_ro1; [| reflexivity| unfold SJ_ACTIVE; lia].
    apply (shz_static RT AF Σ m1 _ _ ART1); [reflexivity| unfold SJ_ACTIVE; lia| reflexivity|]. intros i Hi. unfold SJ_ACTIVE. split; [apply client_static_intro; lia| lia]. }
  assert (SL1 : rw_cells bsegs m1 (sp' + 120) [C8 (wz d)]).
  { apply (rw_cells_agree_nw bsegs m m1 _ _ SL120). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    unfold ga_W. cbn [outside]. repeat split; try exact I; lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [apply (imp_walk7 usp sp' f d n gp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 _ _ _ _ u3 u4 u5 u6 _ F1 fc m1 F0 ltac:(lia) ltac:(unfold SJ_ACTIVE; lia) SPH' DR SHA1 (proj1 LIB1) SL1 MI1)|].
  cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & ACT2). apply evt_done.
  assert (ART2 : ART RT Σ m2).
  { apply (art_client_write RT AF Σ m1 m2 sp' ART1 ltac:(rewrite SPx; lia)); [| exact WM2].
    intros a Ha. apply MU2. cbn [outside]. split; [| exact I]. intros Hc. apply Ha. right; left. apply client_static_intro. unfold SJ_ACTIVE in Hc. lia. }
  assert (ST2 : stk bsegs m2 lo sp').
  { apply (stk_agree_nw bsegs m1 m2 _ _ ST1). apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [outside]. unfold SJ_ACTIVE. split; [lia| exact I]. }
  assert (L12 : lib1 m2).
  { destruct LIB1 as (_ & Q2 & Q3 & Q4). split; [exact ACT2|].
    split; [apply (rw_cells_agree_nw bsegs m1 m2 _ _ Q2)| split; [apply (rw_cells_agree_nw bsegs m1 m2 _ _ Q3)| apply (rw_cells_agree_nw bsegs m1 m2 _ _ Q4)]];
      apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbn [outside]; unfold SJ_ACTIVE; (split; [lia| exact I]). }

  assert (AG02 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' - 32 <= x < sp') /\ ~ sj4_rng x) -> agree_on P m m2).
  { intros P HP. eapply agree_trans.
    - apply (agree_of_munch _ _ _ _ MU1). intros x Hx. destruct (HP _ Hx) as [N1 N2]. unfold sj4_rng in N2. unfold ga_W. cbn [outside]. repeat split; try exact I; lia.
    - apply (agree_of_munch _ _ _ _ MU2). intros x Hx. destruct (HP _ Hx) as [N1 N2]. unfold sj4_rng in N2. unfold SJ_ACTIVE. cbn [outside]. split; [lia| exact I]. }
  assert (BB2 : bodyB m2 usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11).
  { apply (bodyB_agree4 m m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BB LUSP); [| right; right; exact L12]. apply AG02. intros x Hx. unfold bodyZ, imp_rest_rng, sj4_rng, PJ_LOC_LO_A, PJ_LOCKW_A in *.
    unfold TPV_A in Hx. destruct Hx as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; [lia| lia| rewrite SHF0 in H; clear - H SEP F0 SLO LO64 SHF0; unfold shad in *; lia| clear - H A8LO A8SG GLO LOW LOR SPR; ul| lia| lia| lia|].
    destruct H as (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R. destruct Hin as [E|[E|[]]]; injection E as <- <-; ul. }
  assert (BF2 : bodyF m2 f) by (apply (bodyF_agree m m2 f BF); apply AG02; intros x Hx; unfold sj4_rng; lia).
  assert (BS2 : bytes_at bsegs m2 d bs).
  { apply (bytes_at_agree bsegs m m2 _ _ BS). apply AG02. intros x Hx. cbv beta in Hx.
    destruct INLV as [(p & k & Hin & P1 & P2)| (E0 & DL)]; [| rewrite E0 in Hx; cbn [length] in Hx; lia].
    pose proof (af_live_range RT AF Σ m p k ARTx (LV0x _ Hin)) as (_ & Y3 & Y4). rewrite SPx in Y3. unfold sj4_rng. subst n. clear - Hx P1 P2 Y3 Y4 LOW LOR SPR. ul. }
  assert (PRES2 : forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m2 a = m0 a).
  { intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply (AG02 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. pose proof (CSEP _ Ha) as (C1 & C2 & C3).
    split; [lia|]. unfold IMP_XFP_A, LIB_FP in Ho. cbn [outside app] in Ho. unfold sj4_rng. clear - Ho. lia. }
  clear MU1 WM1 MI1 ST1 LIB1 ART1 SHA1 MU2 WM2 AG02 BB BF BS PRES ARTx MIx STx.
  destruct BB2 as ((j0 & j8 & j160 & j192 & L1) & STp & SV & (h3 & HD) & SH & ((_ & RS & LB & LX & TP & LK) & AX)).
  destruct BF2 as ((j9 & j25 & j65 & j108 & FI) & S1 & S2 & S3 & (jsb & FB) & (jos & FO) & (jtmp & FT)).

  unfold impl0A, implA_cells in FI.
  lazymatch type of FI with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: CB 36 z36 :: ?rest) =>
    apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] 36 z36 rest [16; 16; 4]%nat) in FI; [| reflexivity]; cbn [mk_CB_cells app] in FI end.
  change (firstn 16 z36) with (repeat z8 16) in FI. change (firstn 16 (skipn 16 z36)) with (repeat z8 16) in FI. change (firstn 4 (skipn 16 (skipn 16 z36))) with (repeat z8 4) in FI.
  lazymatch type of FI with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: rest) with ([c0] ++ [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ rest) in FI end.
  apply rw_cells_app in FI. destruct FI as [FW FI]. apply rw_cells_app in FI. destruct FI as [FP FE]. cbn [cells_size csize Nat.add] in FP, FE.
  replace (f + 160 + Z.of_nat 8) with (f + 168) in FP by lia. replace (f + 160 + Z.of_nat 8 + Z.of_nat 80) with (f + 248) in FE by lia.
  change (rw_cells bsegs m2 (f + 168) (parser_init j9 j25 j65)) in FP.
  pose proof L1 as LKR. rewrite imp_localsL_KR in LKR. apply rw_cells_app in LKR. destruct LKR as [LKc LR]. rewrite imp_localsK_size in LR.
  replace (sp' + Z.of_nat 192) with (sp' + 192) in LR by lia.
  pose proof (imp_parser_fobj Σ m2 f SH FRSx F0 F64) as FOBJ2.
  assert (LIB2 : pj_libA sj_lib m2) by (split; [right; exact L12| split; [right; exact LB| exact LK]]).
  pose proof (af_sp0_range RT AF Σ m2 ART2) as SP0R. rewrite SPx in SP0R.
  assert (OKC0 : 0 <= imp_okarm_costA (Z.max n 32 + 67)) by (unfold imp_okarm_costA, IMP_PUT_COST_A; lia).
  assert (CRP : pj_pid_costA n <= rt_credit RT Σ) by (unfold imp_body_costA in CRx; lia).

  replace (f + 192) with (f + 168 + 24) by lia.
  eapply (aevt_rt RT PMc Σ K _ _
           (PID Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc m2 (f + 168) (sp' + 192) d bs j9 j25 j65 j192 lo
                FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl D0 NB BS2 ltac:(rewrite LVx; destruct INLV as [(p & k & Hin & P12)|E0]; [left; exists p, k; split; [apply in_or_app; right; exact Hin| exact P12]| right; exact E0])
                FOBJ2 FP ltac:(rewrite EU; lia) ltac:(ul) ltac:(clear - SPA; Z.div_mod_to_equations; lia) LR
                LVP ltac:(lia) ltac:(rewrite FRSx; cbn; unfold PID_FRAMES, FRAMES_MAX; lia)
                CRP LIB2 ART2 MI2 ltac:(rewrite EU; exact ST2) ltac:(rewrite SPx; lia) ltac:(rewrite EU; ul)
                ltac:(rewrite EU; ul) ltac:(rewrite EU; clear - SPA; Z.div_mod_to_equations; lia) FRM)); [exact FRM|].
  intros c PP. cbv beta zeta in PP. destruct PP as (Σ2 & cp & impl & idx & oc & ia & tape & sbuf & HA & LV2 & CP & ALS & FRS2 & SP2 & CR2).
  fold n in LV2, CP, CR2. eexists Σ2, _. split; [exact HA|].
  intros ms' (vr & m3 & RS3 & (ART3 & MI3 & ST3) & PRES3 & (r & j20 & RESC3 & R64 & OKR & RZ) & LIB3 & PD3 & FOBJ3 & DOC3) FRM3.
  destruct RS3 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->). cbn [ms_fcsr] in FRM3.
  rewrite EU in ST3, PRES3. rewrite (ret_pc_even IMP_PARSE_RET_A) by (unfold IMP_PARSE_RET_A; lia). rewrite FRSx in FRS2, PRES3. rewrite SPx in SP2.
  replace (f + 168 + 24) with (f + 192) in * by lia. fold n in OKR, RZ.
  assert (INCL2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2; apply in_or_app; right; do 6 right; exact He).
  assert (A82 : In (A8, 8) (rt_live RT Σ2)) by (apply INCL2; exact A8IN).
  assert (INF2 : In (f, 5%nat) (rt_frames RT Σ2)) by (rewrite FRS2; left; reflexivity).
  pose proof (af_frames_range RT AF Σ2 m3 f 5%nat ART3 INF2) as (_ & _ & _ & FLV2). change (fs_size 5) with 2048 in FLV2.
  pose proof (proj1 (af_fshadow_apart RT AF Σ2 m3 f 5%nat ART3 INF2)) as FSL2. change (fs_size 5) with 2048 in FSL2. rewrite SHF in FSL2.
  assert (LVP2 : forall q k, In (q, k) (rt_live RT Σ2) -> 0 < k).
  { intros q k Hq. rewrite LV2 in Hq. apply in_app_or in Hq. destruct Hq as [Hq|Hq].
    - destruct CP as [(COPY & -> & _)| ->]; [| destruct Hq]. destruct Hq as [E|[]]. injection E as <- <-. lia.
    - pose proof (sc_idx_bounds (Z.max n 32) ltac:(lia)) as B3. pose proof (al_sbuf_bounds (Z.max n 32) ltac:(lia)) as B1. pose proof (al_tape_bounds (Z.max n 32) ltac:(lia)) as B2.
      cbn [In] in Hq. destruct Hq as [E|[E|[E|[E|[E|[E|Hq]]]]]]; [injection E as <- <-; subst n; lia ..| exact (LVP q k Hq)]. }

  assert (AG23 : forall P : Z -> Prop,
            (forall x, P x -> (sp' <= x < usp /\ ~ (sp' + 192 <= x < sp' + 216)) \/ (f <= x < f + 2040 /\ ~ (f + 168 <= x < f + 248)) \/ (shad f <= x < shad f + 256)
                              \/ imp_rest_rng A8 x \/ (PJ_LOC_LO_A <= x < PJ_LOC_LO_A + 3760) \/ (PJ_LOCKW_A <= x < PJ_LOCKW_A + 4) \/ (TPV_A - 48 <= x < TPV_A - 40) \/ in_ranges IMP_AEX_W x) ->
            agree_on P m2 m3).
  { intros P HP a Ha. apply PRES3.
    - destruct (HP _ Ha) as [[H _]|[[H _]|[H|[H|[H|[H|[H|H]]]]]]].
      + left. ul.
      + right; right; right; left. exists f, 5%nat. split; [left; reflexivity| change (fs_size 5) with 2048; lia].
      + right; right; right; right. exists f, 5%nat. split; [left; reflexivity| rewrite SHF0 in H |- *; unfold shad, SHB; change (fs_size 5) with 2048; Z.div_mod_to_equations; lia].
      + unfold imp_rest_rng in H. destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; [right; left; apply client_static_intro; lia ..|].
        right; right; left. exists A8, 8. split; [exact A8IN| lia].
      + right; left. apply client_static_intro. unfold PJ_LOC_LO_A in H. lia.
      + right; left. apply client_static_intro. unfold PJ_LOCKW_A in H. lia.
      + right; left. apply client_static_intro. unfold TPV_A in H. lia.
      + right; left. destruct H as (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R. destruct Hin as [E|[E|[]]]; injection E as <- <-; apply client_static_intro; lia.
    - unfold pid_XA, SJ_W. cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOCKW_A, TPV_A, imp_rest_rng in HP. rewrite SHF0 in HP.
      destruct (HP _ Ha) as [[H1 H2]|[[H1 H2]|[H|[H|[H|[H|[H|H]]]]]]]; try (repeat split; try exact I; clear - H1 H2 FSEG GLO LOW LOR SPR FLO; ul).
      + repeat split; try exact I; clear - H FSEG SEP GLO LOW LOR SPR FLO SLO SHF0; rewrite SHF0 in *; ul.
      + pose proof (FLV A8 8 A8IN) as Y1. destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; repeat split; try exact I; clear - H A8SG A8LO Y1 FSEG GLO LOW LOR SPR FLO; ul.
      + repeat split; try exact I; clear - H FSEG GLO LOW LOR SPR FLO; ul.
      + repeat split; try exact I; clear - H FSEG GLO LOW LOR SPR FLO; ul.
      + repeat split; try exact I; clear - H FSEG GLO LOW LOR SPR FLO; ul.
      + destruct H as (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R.
        destruct Hin as [E|[E|[]]]; injection E as <- <-; repeat split; try exact I; clear - R FSEG GLO LOW LOR SPR FLO; ul. }
  assert (LKc3 : rw_cells bsegs m3 sp' (imp_localsK j0 j8 f (Z_to_bv 64 n) d 0 j160)) by (apply (rw_cells_agree_nw bsegs m2 m3 _ _ LKc); apply AG23; intros x Hx; rewrite imp_localsK_size in Hx; left; lia).
  assert (STp3 : stk bsegs m3 (sp' + 216) (usp - 104)) by (apply (stk_agree_nw bsegs m2 m3 _ _ STp); apply AG23; intros x Hx; cbv beta in Hx; left; lia).
  assert (SV3 : rw_cells bsegs m3 (usp - 104) (imp_savedA cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11))
    by (apply (rw_cells_agree_nw bsegs m2 m3 _ _ SV); apply AG23; intros x Hx; rewrite imp_savedA_size in Hx; left; lia).
  assert (HD3 : rw_cells bsegs m3 f (fz_hdr (C8 (Z_to_bv 64 IMP_MAGIC0)) (C8 (Z_to_bv 64 IMP_HDR_DESC_A)) (C8 (Z_to_bv 64 e_fuzz)) h3))
    by (apply (rw_cells_agree_nw bsegs m2 m3 _ _ HD); apply AG23; intros x Hx; unfold fz_hdr in Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia).
  assert (SH3 : rw_cells bsegs m3 (shad f) (map C1 imp_sh_pro))
    by (apply (rw_cells_agree_nw bsegs m2 m3 _ _ SH); apply AG23; intros x Hx; rewrite cells_size_map_C1' in Hx; unfold imp_sh_pro in Hx; rewrite imp_sh_length in Hx; do 2 right; left; lia).
  assert (RS3 : imp_restA A8 m3) by (apply (imp_restA_agree A8 m2 m3 RS); apply AG23; intros x Hx; do 3 right; left; exact Hx).
  assert (LB3 : LOCBA m3) by (apply (LOCBA_agree m2 m3 LB); apply AG23; intros x Hx; do 4 right; left; unfold PJ_LOC_HI_A, PJ_LOC_LO_A in *; lia).
  assert (LX3 : locx3 m3).
  { destruct LX as (X1 & X2 & X3). unfold locx3, LOC_CVC, LOC_CVW in *. split; [| split];
      [apply (rw_cells_agree_nw bsegs m2 m3 _ _ X1)| apply (rw_cells_agree_nw bsegs m2 m3 _ _ X2)| apply (rw_cells_agree_nw bsegs m2 m3 _ _ X3)];
      apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; do 4 right; left; unfold PJ_LOC_LO_A; lia. }
  assert (TP3 : imp_tplocA m3) by (unfold imp_tplocA in *; apply (rw_cells_agree_nw bsegs m2 m3 _ _ TP); apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; do 6 right; left; lia).
  assert (AX3 : aex6A m3) by (apply (aex6A_agree m2 m3 AX); apply AG23; intros x Hx; do 7 right; exact Hx).
  assert (FW3 : rw_cells bsegs m3 (f + 160) [C8 (Z_to_bv 64 SJ_SINGLETON)]) by (apply (rw_cells_agree_nw bsegs m2 m3 _ _ FW); apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia).
  assert (FE3 : rw_cells bsegs m3 (f + 248) [CB 16 (repeat z8 16); CB 4 (repeat z8 4); CB 4 j108; CB 24 z24])
    by (apply (rw_cells_agree_nw bsegs m2 m3 _ _ FE); apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia).
  assert (S13 : slot0A m3 (f + 296)) by (apply (slot0A_agree m2 m3 _ S1); apply AG23; intros x Hx; right; left; lia).
  assert (S23 : slot0A m3 (f + 432)) by (apply (slot0A_agree m2 m3 _ S2); apply AG23; intros x Hx; right; left; lia).
  assert (S33 : slot0A m3 (f + 568)) by (apply (slot0A_agree m2 m3 _ S3); apply AG23; intros x Hx; right; left; lia).
  assert (FB3 : rw_cells bsegs m3 (f + 32) [CB 88 jsb]) by (apply (rw_cells_agree_nw bsegs m2 m3 _ _ FB); apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia).
  assert (FO3 : rw_cells bsegs m3 (f + 832) [CB 264 jos]) by (apply (rw_cells_agree_nw bsegs m2 m3 _ _ FO); apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia).
  assert (FT3 : rw_cells bsegs m3 (f + 1168) [CB 24 jtmp]) by (apply (rw_cells_agree_nw bsegs m2 m3 _ _ FT); apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia).
  assert (PRES3' : forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m3 a = m0 a).
  { intros a Ha Ho. rewrite <- (PRES2 a Ha Ho). apply PRES3.
    - apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact LV0x| intros e []| lia].
    - pose proof (CSEP _ Ha) as (C1 & C2 & C3). unfold pid_XA, SJ_W. cbn [outside]. split; [lia|]. split; [lia|].
      unfold IMP_XFP_A, LIB_FP in Ho. cbn [outside app] in Ho. clear - Ho. repeat split; try exact I; lia. }
  destruct (NLIOS m3 PRES3') as [NL3 IOS3].

  pose proof FE3 as FE3'.
  lazymatch type of FE3' with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: nil) => change (c0 :: c1 :: c2 :: c3 :: nil) with ([c0; c1; c2] ++ [c3]) in FE3' end.
  apply rw_cells_app in FE3'. destruct FE3' as [FEL3 OUT3]. cbn [cells_size csize Nat.add] in OUT3. replace (f + 248 + Z.of_nat 24) with (f + 272) in OUT3 by lia.
  clear LKc STp SV HD SH RS LB LX TP LK AX FW FE S1 S2 S3 FB FO FT L1 LR FP FOBJ2 LIB2 ST2 MI2 PRES2 BS2.

  destruct (Z.eq_dec (bv_unsigned r) 0) as [RZ0|RNZ].
  2: {
    assert (NZ : bv_eqb r (Z_to_bv 64 0) = false).
    { destruct (bv_eqb r (Z_to_bv 64 0)) eqn:E; [| reflexivity]. exfalso. apply bv_eqb_eq in E. subst r. rewrite unsigned_lit in RNZ by lia. lia. }
    pose proof FEL3 as ERR3.
    lazymatch type of ERR3 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: nil) => change (c0 :: c1 :: c2 :: nil) with ([c0] ++ [c1] ++ [c2]) in ERR3 end.
    apply rw_cells_app in ERR3. destruct ERR3 as [_ ERR3]. apply rw_cells_app in ERR3. destruct ERR3 as [ERR3 _]. cbn [cells_size csize Nat.add] in ERR3.
    replace (f + 248 + Z.of_nat 16) with (f + 264) in ERR3 by lia.
    assert (ERR3' : rw_cells bsegs m3 (f + 264) [C4 (Z_to_bv 64 0)]) by (eapply rw_cells_recastA; [exact ERR3| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]).
    pose proof (bv_unsigned_in_range 64 r) as RR.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (imp_walk8_err usp sp' f 0 _ gp w0 w1 w2 vr e1 e2 e3 e4 e5 e6 e7 _ _ _ _ _ _ w3 w4 w5 w6 r _ j20 F3 fc3 m3);
                     [lia| lia| lia| lia| lia| lia| lia| exact RESC3| exact ERR3'| exact MI3]|].
    cbv beta. intros ms4 (m4 & a0' & a1' & e1' & -> & MU4 & WM4 & MI4 & _). apply evt_done.
    assert (LK4 : rw_cells bsegs m4 sp' (imp_localsK j0 j8 f (Z_to_bv 64 n) d 0 j160)).
    { apply (rw_cells_agree_nw bsegs m3 m4 _ _ LKc3). apply (agree_of_munch _ _ _ _ MU4). intros x Hx. rewrite imp_localsK_size in Hx. cbn [outside]. repeat split; try exact I; lia. }
    assert (AG34 : forall P : Z -> Prop, (forall x, P x -> ~ (f + 264 <= x < f + 268) /\ ~ (sp' + 152 <= x < sp' + 160)) -> agree_on P m3 m4).
    { intros P HP a Ha. apply MU4. destruct (HP _ Ha) as [N1 N2]. cbn [outside]. repeat split; try exact I; lia. }
    assert (ART4 : ART RT Σ2 m4).
    { apply (art_client_write RT AF Σ2 m3 m4 sp' ART3 ltac:(rewrite SP2; lia)); [| exact WM4].
      intros a Ha. apply MU4. cbn [outside]. rewrite FRS2 in Ha.
      assert (C1 : ~ (sp' <= bv_unsigned a < USTACK_TOP)) by (intros Hc; apply Ha; left; exact Hc).
      assert (C2 : ~ (f <= bv_unsigned a < f + 2040)) by (intros Hc; apply Ha; right; right; right; left; exists f, 5%nat; split; [left; reflexivity| change (fs_size 5) with 2048; lia]).
      unfold USTACK_TOP in *. repeat split; try exact I; lia. }
    assert (ST4 : stk bsegs m4 lo sp') by (apply (stk_agree_nw bsegs m3 m4 _ _ ST3); apply AG34; intros x Hx; lia).
    pose proof RESC3 as JR3. unfold res_cellsA in JR3. rewrite NZ in JR3. apply rw_cells_asCB in JR3. cbn [cells_size csize Nat.add] in JR3.
    apply (imp_tailA RT AF RC PDONE PDT PDFP PMc FDO MST Σ0 Σ2 Σ2 K v A8 usp sp' f lo d n 1 _ gp w0 w1 w2 a0' a1' e2 e3 e4 e5 e6 e7 _ _ _ _ w3 w4 w5 w6
             cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 F3 fc3 m0 m3 m4 None
             (cp ++ [(ia, 1024); (oc, 8192); (idx, sc_idx (Z.max n 32)); (impl, 96); (tape, al_tape (Z.max n 32)); (sbuf, al_sbuf (Z.max n 32))]) cb G ART4 MI4 ST4 FRS2);
      [reflexivity| rewrite LV2, LVx, <- app_assoc; reflexivity| exact SP2| clear - CR2 CRx CB0 OKC0; unfold imp_body_costA in CRx; subst n; lia| rewrite <- LVx; exact A8IN| exact VA| exact LVP2
      | rewrite <- LVx; exact PD3| exact ART3| exact FRS2| | | | | | | | exact FRM3| exact KFIN| right; reflexivity].
    - intros a Ha. apply (AG34 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->.
      destruct Ha as [H|[H|(p & k & Hin & R)]]; [lia| clear - H SEP F0 SLO LO64; unfold shad, SHB in *; Z.div_mod_to_equations; lia|].
      pose proof (FLV2 p k Hin) as Y1. pose proof (af_live_range RT AF Σ2 m3 p k ART3 Hin) as (_ & Y3 & _). rewrite SP2 in Y3. clear - R Y1 Y3 LOW LOR SPR. ul.
    -
      split; [| split; [| split; [| split; [| split; [| split]]]]].
      + exists 1, j0, j8, j160, (cells_bytes [CB 16 (repeat z8 16); C4 r; CB 4 j20]). split; [right; reflexivity|]. split; [exact LK4|].
        apply (rw_cells_agree_nw bsegs m3 m4 _ _ JR3). apply AG34. intros x Hx. cbn [cells_size csize Nat.add] in Hx. lia.
      + apply (stk_agree_nw bsegs m3 m4 _ _ STp3). apply AG34. intros x Hx. cbv beta in Hx. lia.
      + apply (rw_cells_agree_nw bsegs m3 m4 _ _ SV3). apply AG34. intros x Hx. rewrite imp_savedA_size in Hx. lia.
      + exists h3. apply (rw_cells_agree_nw bsegs m3 m4 _ _ HD3). apply AG34. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. lia.
      + apply (rw_cells_agree_nw bsegs m3 m4 _ _ SH3). apply AG34. intros x Hx. rewrite cells_size_map_C1' in Hx. unfold imp_sh_pro in Hx. rewrite imp_sh_length in Hx.
        rewrite SHF0 in Hx. clear - Hx SEP F0 SLO LO64 SHF0. rewrite SHF0 in SEP. lia.
      + split; [| split; [| split; [| split]]].
        * apply imp_staticsA_of_rest.
          -- apply (sj_lib_agree m3 m4 (proj1 LIB3)). apply AG34. intros x Hx. clear - Hx GLO LOR SPR FSEG. ul.
          -- apply (imp_restA_agree A8 m3 m4 RS3). apply AG34. intros x Hx. unfold imp_rest_rng in Hx. pose proof (FLV A8 8 A8IN) as Y1. clear - Hx Y1 A8LO GLO LOW LOR SPR FSEG. ul.
        * apply (LOCBA_agree m3 m4 LB3). apply AG34. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. clear - Hx GLO LOR SPR FSEG. ul.
        * destruct LX3 as (X1 & X2 & X3). unfold locx3, LOC_CVC, LOC_CVW in *. split; [| split];
            [apply (rw_cells_agree_nw bsegs m3 m4 _ _ X1)| apply (rw_cells_agree_nw bsegs m3 m4 _ _ X2)| apply (rw_cells_agree_nw bsegs m3 m4 _ _ X3)];
            apply AG34; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx GLO LOR SPR FSEG; ul.
        * unfold imp_tplocA in *. apply (rw_cells_agree_nw bsegs m3 m4 _ _ TP3). apply AG34. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold TPV_A in Hx. clear - Hx GLO LOR SPR FSEG. ul.
        * apply (lockwA_agree m3 m4 (proj2 (proj2 LIB3))). apply AG34. intros x Hx. unfold PJ_LOCKW_A in Hx. clear - Hx GLO LOR SPR FSEG. ul.
      + apply (aex6A_agree m3 m4 AX3). apply AG34. intros x (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R.
        destruct Hin as [E|[E|[]]]; injection E as <- <-; clear - R GLO LOR SPR FSEG; ul.
    - apply (slot0A_agree m3 m4 _ S13). apply AG34. intros x Hx. lia.
    - apply (slot0A_agree m3 m4 _ S23). apply AG34. intros x Hx. lia.
    - apply (slot0A_agree m3 m4 _ S33). apply AG34. intros x Hx. lia.
    - exists z8, (repeat z8 23). split; [| reflexivity].
      assert (OUT3' : rw_cells bsegs m3 (f + 272) (out_shortA z8 (repeat z8 23))) by (unfold out_shortA; eapply rw_cells_recastA; [exact OUT3| cbn; repeat split; reflexivity| vm_compute; reflexivity| reflexivity]).
      apply (rw_cells_agree_nw bsegs m3 m4 _ _ OUT3'). apply AG34. intros x Hx. unfold out_shortA in Hx. cbn [cells_size csize Nat.add] in Hx. lia.
    - intros a Ha Ho. rewrite <- (PRES3' a Ha Ho). apply (AG34 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. pose proof (CSEP _ Ha) as (C1 & C2 & C3). lia. }

  assert (ER : r = Z_to_bv 64 0) by (rewrite <- (Z_to_bv_bv_unsigned r), RZ0; reflexivity). subst r.
  destruct OKR as [K64|(_ & tws & sbs & BT & BSB & WFS & SBR & NT & NS)]; [rewrite unsigned_lit in K64 by lia; exfalso; lia|].
  pose proof (RZ eq_refl) as NPAD.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (imp_walk8_ok usp sp' f _ gp w0 w1 w2 vr e1 e2 e3 e4 e5 e6 e7 _ _ _ _ _ _ _ _ w3 w4 w5 w6 j20 F3 fc3 m3 F0 ltac:(lia) ltac:(lia) SPH' RESC3 MI3)|].
  cbv beta. intros ms4 (a1' & ->). apply evt_done.

  set (cap := Z.max n 32) in *.
  assert (CAP : 32 <= cap <= 2^26) by (subst cap; change (2^26) with 67108864; lia).
  pose proof (al_sbuf_bounds _ CAP) as B1. pose proof (al_tape_bounds _ CAP) as B2.
  assert (INT : In (tape, al_tape cap) (rt_live RT Σ2)) by (rewrite LV2; apply in_or_app; right; do 4 right; left; reflexivity).
  assert (INS : In (sbuf, al_sbuf cap) (rt_live RT Σ2)) by (rewrite LV2; apply in_or_app; right; do 5 right; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m3 _ _ ART3 INT) as (TR0 & TR & _). pose proof (af_live_range RT AF Σ2 m3 _ _ ART3 INS) as (SR0 & SR & _). rewrite SP2 in TR, SR.
  pose (E := mkPJA lo f 5%nat (f + 32) (f + 192) tape (al_tape cap) sbuf (al_sbuf cap) tws sbs n (rt_live RT Σ2)).
  assert (EOK : pjenvA_ok E).
  { subst E. constructor; cbn [pa_lo pa_F pa_kF pa_SB pa_DOC pa_TAPE pa_NT pa_SBUF pa_NS pa_tws pa_sbs pa_len pa_L].
    - exact WFS. - exact SBR. - unfold SJ_PADMAX in *; lia.
    - unfold SJ_TAPE, SJ_SBUF, sj_cap. fold cap. unfold al_sbuf in NS. lia.
    - unfold al_tape in *. destruct ALS as (_ & _ & _ & _ & _ & _ & T16 & S16). split; [exact T16|]. split; [lia|]. split; [exact TR0|]. split; [clear - TR LOW; lia| exact INT].
    - destruct ALS as (_ & _ & _ & _ & _ & _ & T16 & S16). split; [exact S16|]. split; [lia|]. split; [exact SR0|]. split; [clear - SR LOW; lia| exact INS].
    - exact LVP2.
    - split; [exact F64|]. split; [exact FSEG| change (fs_size 5) with 2048; lia].
    - change (fs_size 5) with 2048. split; [clear - F64; Z.div_mod_to_equations; lia| lia].
    - change (fs_size 5) with 2048. split; [clear - F64; Z.div_mod_to_equations; lia| lia].
    - lia.
    - clear - LOW SPW. ul.
    - unfold al_sbuf, SjModel.roundup64. clear. Z.div_mod_to_equations. lia. }
  assert (ELIVE : pa_live RT Σ2 E (sbA0 (f + 32))) by (subst E; split; [reflexivity| split; [rewrite FRS2; left; reflexivity| cbn [pa_lo]; rewrite SP2; exact LOW]]).
  assert (EDOC : DOCREPA E m3).
  { subst E. split; [exact DOC3|]. split; [| split; [exact BT| exact BSB]]. cbn [pa_DOC].
    replace (shad (f + 192)) with (shad f + 24) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
    change [z8; z8] with (repeat z8 2). apply (imp_sh_run m3 f 24 2 SH3); [lia| cbn; lia| exact SH0]. }

  pose proof RESC3 as RES3. unfold res_cellsA in RES3. rewrite bv_eqb_refl in RES3.
  pose proof LKc3 as LOC3. unfold imp_localsK in LOC3.
  apply rw_cells_app in LOC3. destruct LOC3 as [_ LOC3]. apply rw_cells_app in LOC3. destruct LOC3 as [LOC3 _]. cbn [cells_size csize Nat.add] in LOC3.
  replace (sp' + Z.of_nat 64) with (sp' + 64) in LOC3 by lia.

  pose proof (rw_cells_asCB m3 _ _ FEL3) as FEL3'. cbn [cells_size csize Nat.add] in FEL3'.
  assert (OUT3' : rw_cells bsegs m3 (f + 272) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
    by (eapply rw_cells_recastA; [exact OUT3| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]).
  assert (NTB : Z.of_nat (length tws) < cap + 67) by (pose proof (roundup64_lt (cap + 3)); lia).
  assert (OKC : imp_okarm_costA (Z.of_nat (length tws)) <= imp_okarm_costA (Z.max n 32 + 67)) by (unfold imp_okarm_costA; subst cap; lia).
  eapply (OKARM PMc Σ2 K E sp' usp 1 d _ gp w0 w1 w2 a1' e2 e3 e4 e5 e6 e7 _ _ _ _ _ _ _ w3 w4 w5 w6 F3 fc3 m3 j20 jsb _ jos jtmp
            FDO MST EOK eq_refl eq_refl eq_refl ELIVE EDOC LB3 LX3 NL3 (proj2 (proj2 LIB3)) (IOS3 Σ2 ART3) RES3 LOC3 ltac:(lia) DR FB3 FEL3' OUT3' FO3 FT3 SH3 ART3 MI3);
    subst E; cbn [pa_lo pa_F pa_kF pa_SB pa_DOC pa_TAPE pa_NT pa_SBUF pa_NS pa_tws pa_sbs pa_len pa_L];
    [exact ST3| clear - LOR SPR; ul| clear - UT SPR; ul| exact SPA| clear - SPR; lia| exact FRM3| exact FRS2| | |].
  { rewrite LV2, length_app. cbn [length]. destruct CP as [(COPY & -> & _)| ->]; cbn [length]; unfold IMP_OKARM_LIVE_A; lia. }
  { clear - CR2 CRx CB0 OKC. unfold imp_body_costA in CRx. subst n. lia. }
  intros Σ3 ocp ra' z0 z1 z2 o0 o1 o2 o3 o4 o5 o6 o7 s2' s4' s7' s11' z3 z4 z5 z6 F9 fc9 m9 FRM9 ART9 MI9 ST9 LV3 FRS3 SP3 CR3 PRES9 LOCB9 LOCX9 OUT9 (jsb' & jel' & jos' & jtmp' & FB9 & FEL9 & FO9 & FT9) SH9.
  rewrite FRS2 in PRES9, FRS3. rewrite SP2 in SP3.

  assert (AG39 : forall P : Z -> Prop,
            (forall x, P x -> (sp' <= x < usp) \/ (f <= x < f + 32) \/ (f + 296 <= x < f + 832) \/ imp_rest_rng A8 x \/ sj4_rng x
                              \/ (PJ_LOCKW_A <= x < PJ_LOCKW_A + 4) \/ (TPV_A - 48 <= x < TPV_A - 40) \/ in_ranges IMP_AEX_W x) ->
            agree_on P m3 m9).
  { intros P HP a Ha. apply PRES9.
    - destruct (HP _ Ha) as [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left. ul.
      + right; right; right; left. exists f, 5%nat. split; [left; reflexivity| change (fs_size 5) with 2048; lia].
      + right; right; right; left. exists f, 5%nat. split; [left; reflexivity| change (fs_size 5) with 2048; lia].
      + unfold imp_rest_rng in H. destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; [right; left; apply client_static_intro; lia ..|].
        right; right; left. exists A8, 8. split; [exact A82| lia].
      + right; left. apply client_static_intro. unfold sj4_rng in H. lia.
      + right; left. apply client_static_intro. unfold PJ_LOCKW_A in H. lia.
      + right; left. apply client_static_intro. unfold TPV_A in H. lia.
      + right; left. destruct H as (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R. destruct Hin as [E|[E|[]]]; injection E as <- <-; apply client_static_intro; lia.
    - unfold imp_okarm_WA. cbn [pa_F outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A, PJ_LOCKW_A, TPV_A, imp_rest_rng, sj4_rng in *.
      destruct (HP _ Ha) as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; try (repeat split; try exact I; clear - H FSEG SEP SHB0 GLO LOW LOR SPR FLO SLO; ul).
      + pose proof (FLV2 A8 8 A82) as Y1. pose proof (FSL2 A8 8 A82) as Y2.
        destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; repeat split; try exact I; clear - H A8SG A8LO Y1 Y2 FSEG SEP SHB0 GLO LOW LOR SPR FLO SLO; ul.
      + destruct H as (l & h & Hin & R). unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R.
        destruct Hin as [Ee|[Ee|[]]]; injection Ee as <- <-; repeat split; try exact I; clear - R FSEG SHB0 GLO LOW LOR SPR FLO; ul. }
  assert (LVP3 : forall q k, In (q, k) (rt_live RT Σ3) -> 0 < k).
  { intros q k Hq. rewrite LV3 in Hq. apply in_app_or in Hq. destruct Hq as [Hq|Hq]; [| exact (LVP2 q k Hq)].
    destruct ocp as [[DATA SZ]|]; [| destruct Hq]. destruct OUT9 as (L & _ & _ & SZR & _). destruct Hq as [Ee|[]]. injection Ee as <- <-. lia. }
  pose proof (rw_cells_asCB m3 _ _ RES3) as JR3. cbn [cells_size csize Nat.add] in JR3.
  apply (imp_tailA RT AF RC PDONE PDT PDFP PMc FDO MST Σ0 Σ2 Σ3 K v A8 usp sp' f lo d n 0 ra' gp z0 z1 z2 o0 o1 o2 o3 o4 o5 o6 o7 s2' s4' s7' s11' z3 z4 z5 z6
           cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 F9 fc9 m0 m3 m9 ocp
           (cp ++ [(ia, 1024); (oc, 8192); (idx, sc_idx cap); (impl, 96); (tape, al_tape cap); (sbuf, al_sbuf cap)]) cb G ART9 MI9 ST9 FRS3 LV3);
    [rewrite LV2, LVx, <- app_assoc; reflexivity| exact SP3| clear - CR3 CR2 CRx CB0 OKC; unfold imp_body_costA in CRx; subst n; lia| rewrite <- LVx; exact A8IN| exact VA| exact LVP3
    | rewrite <- LVx; exact PD3| exact ART3| exact FRS2| | | | | | exact OUT9| | exact FRM9| exact KFIN| left; reflexivity].
  -
    intros a Ha. apply PRES9.
    + destruct Ha as [H|[H|H]]; [right; right; right; left| right; right; right; right| right; right; left; exact H];
        (exists f, 5%nat; split; [left; reflexivity| unfold shad, SHB in *; change (fs_size 5) with 2048; clear - H F64 F0; Z.div_mod_to_equations; lia]).
    + unfold imp_okarm_WA. cbn [pa_F outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A.
      destruct Ha as [H|[H|(p & k & Hin & Hr)]].
      * repeat split; try exact I; clear - H FSEG SEP SHB0 SLO FLO; ul.
      * rewrite SHF0 in SEP, SHB0 |- *. unfold shad, SHB in H. repeat split; try exact I; clear - H FSEG SEP SHB0 F0; ul.
      * pose proof (FLV2 p k Hin) as Y1. pose proof (FSL2 p k Hin) as Y2. pose proof (af_live_range RT AF Σ2 m3 p k ART3 Hin) as (_ & Y3 & Y4). rewrite SP2 in Y3.
        rewrite SHF0 in Y2, SHB0 |- *. unfold shad, SEGTOP_A, SHB in *. repeat split; try exact I; clear - Hr Y1 Y2 Y3 Y4 LOW LOR SPR; lia.
  -
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + exists 0, j0, j8, j160, (cells_bytes [C8 (Z_to_bv 64 (f + 192)); C8 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); CB 4 j20]). split; [left; reflexivity|]. split.
      * apply (rw_cells_agree_nw bsegs m3 m9 _ _ LKc3). apply AG39. intros x Hx. rewrite imp_localsK_size in Hx. left. lia.
      * apply (rw_cells_agree_nw bsegs m3 m9 _ _ JR3). apply AG39. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia.
    + apply (stk_agree_nw bsegs m3 m9 _ _ STp3). apply AG39. intros x Hx. cbv beta in Hx. left. lia.
    + apply (rw_cells_agree_nw bsegs m3 m9 _ _ SV3). apply AG39. intros x Hx. rewrite imp_savedA_size in Hx. left. lia.
    + exists h3. apply (rw_cells_agree_nw bsegs m3 m9 _ _ HD3). apply AG39. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. right; left. lia.
    + exact SH9.
    + split; [| split; [exact LOCB9| split; [exact LOCX9| split]]].
      * apply imp_staticsA_of_rest.
        -- apply (sj_lib_agree m3 m9 (proj1 LIB3)). apply AG39. intros x Hx. do 4 right. left. exact Hx.
        -- apply (imp_restA_agree A8 m3 m9 RS3). apply AG39. intros x Hx. do 3 right. left. exact Hx.
      * unfold imp_tplocA in *. apply (rw_cells_agree_nw bsegs m3 m9 _ _ TP3). apply AG39. intros x Hx. cbn [cells_size csize Nat.add] in Hx. do 6 right. left. lia.
      * apply (lockwA_agree m3 m9 (proj2 (proj2 LIB3))). apply AG39. intros x Hx. do 5 right. left. exact Hx.
    + apply (aex6A_agree m3 m9 AX3). apply AG39. intros x Hx. do 7 right. exact Hx.
  - apply (slot0A_agree m3 m9 _ S13). apply AG39. intros x Hx. right; right; left. lia.
  - apply (slot0A_agree m3 m9 _ S23). apply AG39. intros x Hx. right; right; left. lia.
  - apply (slot0A_agree m3 m9 _ S33). apply AG39. intros x Hx. right; right; left. lia.
  -
    intros a Ha Ho. rewrite <- (PRES3' a Ha Ho). apply PRES9.
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply INCL2; apply LV0x; exact He| intros e []| lia].
    + unfold imp_okarm_WA. cbn [pa_F outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A.
      destruct Ha as [H|[H|[H|[H|H]]]].
      * repeat split; try exact I; clear - H FLO LO64 SLO GLO LOR SPR; lia.
      * pose proof (client_static_range _ H) as R. unfold IMP_XFP_A, LIB_FP in Ho. cbn [outside app] in Ho. unfold SEGTOP_A in R.
        repeat split; try exact I; clear - R Ho FSEG SHB0; try ul.
      * destruct H as (p & k & Hin & Hr). pose proof (INCL2 _ (LV0x _ Hin)) as Hin2.
        pose proof (FLV2 p k Hin2) as Y1. pose proof (FSL2 p k Hin2) as Y2. pose proof (af_live_range RT AF Σ2 m3 p k ART3 Hin2) as (_ & Y3 & Y4).
        rewrite SHF0 in Y2 |- *. unfold shad, SEGTOP_A, SHB in *. repeat split; try exact I; clear - Hr Y1 Y2 Y4; lia.
      * destruct H as (? & ? & [] & _).
      * destruct H as (? & ? & [] & _).
Qed.

End WithPM.
End Body.
