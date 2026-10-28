(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_defsA Atp_h_defsA Atp_pidiA Atp_pdtorA Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_cpsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma cells_size_map_C1z : forall l : list Z, cells_size (map (fun z => C1 (Z_to_bv 8 z)) l) = length l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Section Front.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Local Ltac ul := unfold FUZZ_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma el_lib_fp_static : forall x, in_ranges EL_LIB_FP x -> client_static x /\ 0x16e988 <= x < 0x6c81dc.
Proof.
  intros x (l & h & Hin & Hr). unfold EL_LIB_FP in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - exact (lib_fp_static x (ex_intro _ l (ex_intro _ h (conj Hin Hr)))).
  - cbn [In] in Hin. unfold EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[]]]]; inversion Hin; subst l h; (split; [apply client_static_intro; lia| lia]).
Qed.

Definition sj_lib_rng (x : Z) : Prop :=
  0x6a6340 <= x < 0x6a6348 \/ 0x6a6360 <= x < 0x6a6362 \/ 0x6a63e0 <= x < 0x6a640c \/ 0x6a6440 <= x < 0x6a6442.
Lemma sj_lib_agree : forall m m', sj_lib m -> agree_on sj_lib_rng m m' -> sj_lib m'.
Proof.
  intros m m' [(A & B & C & D)|(A & B & C & D)] AG; [left| right]; unfold lib0, lib1, sj_lib_rng in *;
    (split; [| split; [| split]]; [eapply rw_cells_agree_nw; [exact A|] | eapply rw_cells_agree_nw; [exact B|] | eapply rw_cells_agree_nw; [exact C|] | eapply rw_cells_agree_nw; [exact D|]];
     intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia).
Qed.
Lemma sj_lib_rng_fp : forall x, sj_lib_rng x -> in_ranges EL_LIB_FP x.
Proof.
  intros x Hx. unfold sj_lib_rng, EL_LIB_FP, LIB_FP, in_ranges in *. cbn [app].
  destruct Hx as [H|[H|[H|H]]].
  - exists 0x6a6340, 0x6a6348. split; [cbn; tauto| lia].
  - exists 0x6a6360, 0x6a6368. split; [cbn; tauto| lia].
  - exists 0x6a63e0, 0x6a6410. split; [cbn; tauto| lia].
  - exists 0x6a6440, 0x6a6448. split; [cbn; tauto| lia].
Qed.
Lemma loc_rng_fp : forall x, PJ_LOC_LO_A <= x < PJ_LOC_HI_A -> in_ranges EL_LIB_FP x.
Proof. intros x Hx. exists PJ_LOC_LO_A, PJ_LOC_HI_A. split; [unfold EL_LIB_FP, LIB_FP, PJ_LOC_LO_A, PJ_LOC_HI_A; cbn; tauto| exact Hx]. Qed.
Lemma lock_rng_fp : forall x, PJ_LOCKW_A <= x < PJ_LOCKW_A + 4 -> in_ranges EL_LIB_FP x.
Proof. intros x Hx. exists PJ_LOCKW_A, (PJ_LOCKW_A + 4). split; [unfold EL_LIB_FP, LIB_FP, PJ_LOCKW_A; cbn; tauto| exact Hx]. Qed.
Lemma unw_rng_fp : forall x, EL_UNW_A <= x < EL_UNW_A + 8 -> in_ranges EL_LIB_FP x.
Proof. intros x Hx. exists EL_UNW_A, (EL_UNW_A + 8). split; [unfold EL_LIB_FP, LIB_FP, EL_UNW_A; cbn; tauto| exact Hx]. Qed.

Lemma libc_nl_static : forall x, LIBC_NL <= x < LIBC_NL + 1 -> client_static x.
Proof. intros x Hx. apply client_static_intro. unfold LIBC_NL in Hx. lia. Qed.

Definition el_lib_rng (x : Z) : Prop := in_ranges EL_LIB_FP x \/ (EL_EHG_A <= x < EL_EHG_A + 12) \/ (EL_TPLOC_A <= x < EL_TPLOC_A + 8).
Lemma el_lib_rng_static : forall x, el_lib_rng x -> client_static x /\ 0x16e988 <= x < 0x6c81dc.
Proof.
  intros x [H|[H|H]]; [exact (el_lib_fp_static x H)| |]; unfold EL_EHG_A, EL_TPLOC_A, TPV_A in H; (split; [apply client_static_intro; lia| lia]).
Qed.
Lemma el_libA_agree : forall m m', el_libA m -> agree_on el_lib_rng m m' -> el_libA m'.
Proof.
  intros m m' [(S & L & LW) (E & U & T)] AG. unfold el_lib_rng in AG. split; [split; [| split]| split; [| split]].
  - eapply sj_lib_agree; [exact S|]. intros a Ha. apply AG. left. exact (sj_lib_rng_fp _ Ha).
  - eapply pj_locA_agree; [exact L|]. intros a Ha. apply AG. left. exact (loc_rng_fp _ Ha).
  - eapply lockwA_agree; [exact LW|]. intros a Ha. apply AG. left. exact (lock_rng_fp _ Ha).
  - eapply rw_cells_agree_nw; [exact E|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. right; left. lia.
  - destruct U as [uw U]. exists uw. eapply rw_cells_agree_nw; [exact U|]. intros a Ha. apply AG. left. rewrite uw_cellsA_size in Ha. apply unw_rng_fp; lia.
  - eapply rw_cells_agree_nw; [exact T|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. right; right. lia.
Qed.

Lemma carve_CB : forall (m : mem) a n k, wr_at asegs m a n -> 0 <= k -> a + k + 0 <= a + n -> True.
Proof. intros; exact I. Qed.

Theorem el_front : forall (Σ0 : rts RT) (K : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m0 : mem) (d : Z) (bs : list byte) (lo : Z),
  a0 = wz d -> a1 = wz (Z.of_nat (length bs)) -> tp = wz TPV_A ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m0 d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ0) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ0 = [] -> (forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ0)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ0 ->
  el_libA m0 -> io_ssp m0 -> libc_nl m0 -> ART RT Σ0 m0 -> mem_inv asegs m0 ->
  stk asegs m0 lo (bv_unsigned sp) -> rt_sp0 RT Σ0 - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ0 -> frm0 fc ->
  (forall X, lf_usp X = bv_unsigned sp -> lf_lo X = lo -> lfA_ok X -> cutS RT PMc Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K) ->
  aevt RT PMc Σ0 K (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m0).
Proof using AF RC FDO MST.
  intros Σ PMcK ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 LIB0 IOS NL0 ART0 MI0 ST0 LOW LOR SPT SPA SPLE FRM CUTS.
  rename PMcK into K.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as CC0.
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length bs)) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (N0 : 0 <= n < 2^26) by (subst n; lia).
  assert (DR : 0 <= d < 2^64).
  { destruct INLV as [(p & k & Hin & P1 & P2)|(E & DL)]; [| clear - D0 DL; ul].
    pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (R0 & R1 & R2). clear - D0 P1 P2 R1 SP0R N0. ul. }
  subst a0 a1 tp. rewrite ESP. unfold entry_st.

  destruct (el_prologue usp lo d n ra gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
              ST0 ltac:(ul) ltac:(ul) ltac:(ul) SPA CC0 MI0) as (sp' & SPR & SPA' & W0).
  apply (aevt_evt RT AF PMc MST). eapply evt_cut; [exact W0|]. cbv beta.
  intros ms1 (m1 & a1' & a2' & j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & jr & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & STp1 & FRs1).
  apply evt_done. clear W0.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (LIB1 : el_libA m1).
  { apply (el_libA_agree m m1 LIB0). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. pose proof (el_lib_rng_static x Hx) as [_ R].
    cbn [outside]. split; [ul| exact I]. }
  assert (BS1 : bytes_at asegs m1 d bs).
  { apply (bytes_at_agree asegs m m1 _ _ BS). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbv beta in Hx. cbn [outside]. split; [| exact I].
    destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [| subst n; rewrite E in Hx; cbn [length] in Hx; lia].
    pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (R0 & R1 & R2). clear - Hx P1 P2 R1 SPR LOW LOR. subst n. ul. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> outside EL_LIB_FP (bv_unsigned a) -> m1 a = m a).
  { intros a Ha _. apply MU1. cbn [outside]. split; [| exact I]. rewrite <- FRS0 in Ha. destruct (aclient_split_c RT AF Σ m usp _ ART0 Ha); [lia| ul]. }
  assert (EU1 : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  clear MU1 WM1 ST0 MI0.

  eapply (aevt_smalloc4 RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo eq_refl);
    [rewrite FRS0; cbn; unfold FRAMES_MAX; lia| unfold FUZZ_COST in CR0; lia| exact ART1| exact MI1| | intros _; rewrite ?EU1; lia |].
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia]. }
  intros Σ1 f v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F1 m2 (ART2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SP1 CR1 FPOS F64 FTOP.
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even 0xb167c) by lia. rewrite FRS0 in FRS1.
  change (fs_size 4) with 1024 in *. change (1024 / 8) with 128 in WRS.
  assert (INF1 : In (f, 4%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (fframe_ranges RT AF Σ1 m2 f 4 ART2 INF1) as (_ & FR1' & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 4 ART2 INF1) as (FSL & FSF). pose proof (FSF f 4%nat INF1) as FSELF.
  pose proof (af_frames_align RT AF Σ1 m2 f 4 ART2 INF1) as (_ & FSEG). pose proof (af_frames_range RT AF Σ1 m2 f 4 ART2 INF1) as (_ & _ & _ & FLV).
  change (fs_size 4) with 1024 in *. rewrite SP1 in FR1', SHT.
  assert (SHF : shad (f + 1024) = shad f + 128) by (unfold shad; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSELF, FSL, FSF, WRS.
  assert (FD0 : 0 <= f / 8) by (apply Z.div_pos; lia).

  assert (AG12 : forall (P : Z -> Prop), (forall x, P x -> sp' <= x < usp) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. left. pose proof (HP _ Ha). ul. }
  assert (FRl2 : rw_cells asegs m2 sp' (el_locals0 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 jr)).
  { eapply rw_cells_agree_nw; [exact FRl1|]. apply AG12. intros x Hx. rewrite el_locals0_size in Hx. lia. }
  assert (FRs2 : rw_cells asegs m2 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_agree_nw; [exact FRs1|]. apply AG12. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  assert (STp2 : stk asegs m2 (sp' + 152) (usp - 104)) by (eapply stk_agree_nw; [exact STp1|]; apply AG12; intros x Hx; cbv beta in Hx; lia).
  assert (LIB2 : el_libA m2).
  { apply (el_libA_agree m1 m2 LIB1). apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. right; left. exact (proj1 (el_lib_rng_static x Hx)). }
  assert (BS2 : bytes_at asegs m2 d bs).
  { apply (bytes_at_agree asegs m1 m2 _ _ BS1). apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. cbv beta in Hx.
    destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [| subst n; rewrite E in Hx; cbn [length] in Hx; lia].
    right; right; left. exists p, k. split; [exact Hin| lia]. }
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> outside EL_LIB_FP (bv_unsigned a) -> m2 a = m a).
  { intros a Ha Ho. rewrite <- (PRES1 a Ha Ho). apply PRES2. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e []| lia]. }
  clear PRES1 PRES2 AG12 FRl1 FRs1 STp1 ST1 MI1 LIB1 BS1 ART1.

  destruct (wr_at_rw_CB m2 f 1016 WRF ltac:(lia)) as (jF & FF2). change (Z.to_nat 1016) with 1016%nat in FF2.
  apply (rw_cells_split_CB asegs _ _ [] 1016 _ [] [8; 8; 8; 8; 24; 40; 80; 32; 16; 16; 288; 488]%nat) in FF2; [| reflexivity]. cbn [mk_CB_cells app] in FF2.
  repeat match type of FF2 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "q" in set (j := t) in FF2; clearbody j end.
  lazymatch type of FF2 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: rest) with ([c0; c1; c2; c3] ++ rest) in FF2 end.
  apply rw_cells_app in FF2. destruct FF2 as [FH2 FF2]. cbn [cells_size csize Nat.add] in FF2.
  lazymatch type of FH2 with rw_cells _ _ _ [CB 8 ?x0; CB 8 ?x1; CB 8 ?x2; CB 8 ?x3] => change (rw_cells asegs m2 f (fz_hdr (CB 8 x0) (CB 8 x1) (CB 8 x2) x3)) in FH2 end.
  Ltac peel H name :=
    lazymatch type of H with rw_cells _ ?mx ?a (?c0 :: ?rest) =>
      change (c0 :: rest) with ([c0] ++ rest) in H; apply rw_cells_app in H; destruct H as [name H]; cbn [cells_size csize Nat.add] in H end.
  peel FF2 FV2. peel FF2 F56. peel FF2 FP2. peel FF2 F176. peel FF2 FE2. peel FF2 F224. peel FF2 FO2. rename FF2 into F528.
  replace (f + Z.of_nat 32) with (f + 32) in FV2 by lia.
  replace (f + Z.of_nat 32 + Z.of_nat 24) with (f + 56) in F56 by lia.
  replace (f + Z.of_nat 32 + Z.of_nat 24 + Z.of_nat 40) with (f + 96) in FP2 by lia.
  replace (f + Z.of_nat 32 + Z.of_nat 24 + Z.of_nat 40 + Z.of_nat 80) with (f + 176) in F176 by lia.
  replace (f + Z.of_nat 32 + Z.of_nat 24 + Z.of_nat 40 + Z.of_nat 80 + Z.of_nat 32) with (f + 208) in FE2 by lia.
  replace (f + Z.of_nat 32 + Z.of_nat 24 + Z.of_nat 40 + Z.of_nat 80 + Z.of_nat 32 + Z.of_nat 16) with (f + 224) in F224 by lia.
  replace (f + Z.of_nat 32 + Z.of_nat 24 + Z.of_nat 40 + Z.of_nat 80 + Z.of_nat 32 + Z.of_nat 16 + Z.of_nat 16) with (f + 240) in FO2 by lia.
  replace (f + Z.of_nat 32 + Z.of_nat 24 + Z.of_nat 40 + Z.of_nat 80 + Z.of_nat 32 + Z.of_nat 16 + Z.of_nat 16 + Z.of_nat 288) with (f + 528) in F528 by lia.
  destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 128 WRS ltac:(lia)) as (jS & FS2). change (Z.to_nat 128) with 128%nat in FS2.
  apply (rw_cells_split_CB asegs _ _ [] 128 _ []
           [1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1; 52]%nat) in FS2; [| reflexivity].
  cbn [mk_CB_cells app] in FS2.
  lazymatch type of FS2 with rw_cells _ _ _ ?cs =>
    lazymatch eval cbv in (rev (tl (rev cs))) with ?cs76 =>
    lazymatch eval cbv in (last cs (CB 0 [])) with CB 52 ?t =>
      let ls := constr:(map (fun c => match c with CB _ l => l | _ => [] end) cs76) in
      let ls' := eval cbv in ls in
      change (rw_cells asegs m2 (f / 8 + 2147450880) (el_shadow0 ls' t)) in FS2; set (tS := t) in FS2; clearbody tS; set (lS := ls') in FS2;
      assert (LS : length lS = 76%nat) by reflexivity; clearbody lS
    end end end.

  lazymatch type of FH2 with rw_cells _ _ _ (fz_hdr (CB 8 ?h0) (CB 8 ?h1) (CB 8 ?h2) ?h3) =>
    pose proof (el_walk1 usp sp' f lo d n gp (Z_to_bv 64 TPV_A) v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 s2 s3 s6 s8 s9 s10 s11 v3 v4 v5 v6
                  j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 jr h0 h1 h2 h3 tS lS F1 fc m2 LS
                  FPOS ltac:(ul) ltac:(unfold shad, SHB; ul) FD0 ltac:(unfold shad, SHB; exact FSELF) ltac:(ul) ltac:(ul) ltac:(lia) ltac:(ul) DR ltac:(lia) FRl2 FH2
                  ltac:(unfold shad, SHB; exact FS2) MI2) as W1;
    set (H3 := h3) in *; clearbody H3
  end.
  apply (aevt_evt RT AF PMc MST). eapply evt_cut; [exact W1|]. cbv beta. clear W1.
  intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FRl3 & FH3 & FS3). apply evt_done. unfold lf0_st.

  assert (CLW : forall mx my W, munch W mx my -> Forall (fun iv => (sp' <= fst iv /\ snd iv <= usp) \/ (f <= fst iv /\ snd iv <= f + 1016)
                                                                 \/ (f / 8 + 2147450880 <= fst iv /\ snd iv <= f / 8 + 2147450880 + 128)) W ->
                 agree_on (fun a => ~ aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' a) mx my).
  { intros mx my W MU HW a Ha. apply MU. clear - HW Ha FRS1 SPR SPT FD0. induction W as [|[lo' hi'] W IH]; [exact I|].
    apply Forall_cons_iff in HW. destruct HW as [H1 HW]. cbn [outside fst snd] in *. split; [| exact (IH HW)].
    intros Hin. apply Ha. destruct H1 as [H1|[H1|H1]].
    - left. unfold USTACK_TOP in *. lia.
    - right; right; right; left. exists f, 4%nat. rewrite FRS1. split; [left; reflexivity| change (fs_size 4) with 1024; lia].
    - right; right; right; right. exists f, 4%nat. rewrite FRS1. split; [left; reflexivity| unfold shad, SHB; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]. }
  assert (ART3 : ART RT Σ1 m3).
  { apply (art_client_write RT AF Σ1 m2 m3 sp' ART2 ltac:(rewrite SP1; ul)); [| exact WM3]. eapply CLW; [exact MU3|].
    unfold el_W1. unfold shad, SHB. repeat constructor; cbn [fst snd]; lia. }
  assert (ST3 : stk asegs m3 lo sp').
  { apply (stk_agree asegs m2 m3 _ _ ST2); [| exact WM3]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. unfold el_W1, shad, SHB. cbn [outside]. repeat split; lia. }

  assert (NCL : forall x, (f <= x < f + 1024 \/ f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 128 \/ sp' <= x < usp) ->
                 client_static x \/ in_live (rt_live RT Σ) x -> False).
  { intros x Hx [H|H].
    - pose proof (client_static_range _ H) as R. clear - Hx R FSEG SHB0 SPR LOW LOR SP0R. unfold SEGTOP_A, SHB in *. ul.
    - destruct H as (p & k & Hin & Hr). rewrite <- LV1 in Hin. pose proof (FLV p k Hin) as Y1. pose proof (FSL p k Hin) as Y2.
      pose proof (af_live_range RT AF Σ1 m2 p k ART2 Hin) as (_ & Y3 & _). rewrite SP1 in Y3. clear - Hx Hr Y1 Y2 Y3 LOW LOR SPR. ul. }
  assert (PLV : forall x, d <= x < d + n -> in_live (rt_live RT Σ) x).
  { intros x Hx. destruct INLV as [(p & k & Hin & P1 & P2)| (E0 & DL)]; [| subst n; rewrite E0 in Hx; cbn [length] in Hx; lia].
    exists p, k. split; [exact Hin| lia]. }
  assert (BS3 : bytes_at asegs m3 d bs).
  { apply (bytes_at_agree asegs m2 m3 _ _ BS2). apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbv beta in Hx.
    pose proof (PLV x ltac:(subst n; lia)) as IL. unfold el_W1, shad, SHB. cbn [outside].
    repeat split; intros E; apply (NCL x); [lia| right; exact IL| lia| right; exact IL| lia| right; exact IL| lia| right; exact IL]. }
  assert (APART : d + n <= sp' \/ usp <= d).
  { destruct INLV as [(p & k & Hin & P1 & P2)| (E0 & DL)]; [| left; subst n; rewrite E0; cbn [length Z.of_nat]; clear - DL SPR LOW LOR SP0R; ul].
    pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (R0 & R1 & R2). left. clear - P2 R1 LOW LOR SPR. ul. }
  assert (SHD : shad (d + n) < sp').
  { unfold shad, SHB. destruct INLV as [(p & k & Hin & P1 & P2)| (E0 & DL)].
    - pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (R0 & R1 & R2). clear - P2 R1 R0 P1 LOW LOR SPR SP0W D0 N0. unfold SEGTOP_A, STACK_WIN, USTACK_TOP, FUZZ_STACK in *.
      Z.div_mod_to_equations. lia.
    - subst n. rewrite E0. cbn [length Z.of_nat]. clear - DL D0 SPR LOW LOR SP0W. unfold SEGTOP_A, STACK_WIN, FUZZ_STACK in *. Z.div_mod_to_equations. lia. }
  assert (ACC0 : bs = [] \/ acc asegs m3 d n).
  { destruct INLV as [(p & k & Hin & P1 & P2)| (E0 & DL)]; [right| left; exact E0].
    rewrite <- LV1 in Hin. destruct (af_acc_live RT AF Σ1 m3 p k ART3 Hin) as [_ AC]. apply (acc_sub asegs m3 p k d n AC); lia. }
  assert (DH : d + n < 2^63).
  { destruct INLV as [(p & k & Hin & P1 & P2)| (E0 & DL)].
    - pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (R0 & R1 & R2). clear - P2 R1 SP0R. ul.
    - subst n. rewrite E0. cbn [length Z.of_nat]. clear - DL. ul. }

  pose proof FRl3 as FRl3'. unfold el_locals1 in FRl3'.
  lazymatch type of FRl3' with rw_cells _ _ _ [CB 8 ?x0; CB 8 ?x1; CB 8 ?x2; CB 8 ?x3; CB 8 ?x4; CB 8 ?x5; CB 8 ?x6; CB 8 ?x7; CB 24 ?x8; C8 _; CB 24 ?xr; CB 4 ?x10;
                                               CB 4 ?x11; CB 8 ?x12; CB 8 ?x13; C1 _; CB 7 ?x15] =>
    pose proof (el_hdr usp sp' f d n bs gp (Z_to_bv 64 TPV_A) v0 v1 v2 e5 e6 e7 s6 s9 s10 s11 v3 v4 v5 v6 x0 x1 x2 x3 x4 x6 x8 x10 x15 xr F1 fc m3
                  eq_refl ltac:(lia) DH FPOS ltac:(ul) ltac:(lia) ltac:(ul) APART ACC0 SHD x5 x7 x11 x12 x13 m3
                  BS3 (munch_refl _ m3) (wmono_refl asegs m3) MI3 FRl3') as WH
  end.
  apply (aevt_evt RT AF PMc MST). eapply evt_cut; [exact WH|]. cbv beta. clear WH FRl3'.
  intros ms4 (m4 & idx & act & sel & s5v & t0x & a2x & a3x & a4x & a5x & a6x & a7x & j12x & j13x & -> & MU4 & WM4 & MI4 & FRl4 & ACT & SEL). apply evt_done. unfold lf0_st.
  assert (ART4 : ART RT Σ1 m4).
  { apply (art_client_write RT AF Σ1 m3 m4 sp' ART3 ltac:(rewrite SP1; ul)); [| exact WM4]. eapply CLW; [exact MU4|].
    unfold el_W2. repeat constructor; cbn [fst snd]; lia. }
  assert (ST4 : stk asegs m4 lo sp').
  { apply (stk_agree asegs m3 m4 _ _ ST3); [| exact WM4]. apply (agree_of_munch _ _ _ _ MU4). intros x Hx. unfold el_W2. cbn [outside]. repeat split; lia. }
  assert (FS4 : rw_cells asegs m4 (f / 8 + 2147450880) (el_shadowA (-8) (-8) (-8) (-8) tS)).
  { eapply rw_cells_agree_nw; [exact FS3|]. apply (agree_of_munch _ _ _ _ MU4). intros x Hx. rewrite el_shadowA_size in Hx. unfold el_W2. cbn [outside]. repeat split; ul. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (el_walkV0 usp sp' f (el_fddA d n) (el_fdsA n) n s5v gp (Z_to_bv 64 TPV_A) t0x v1 v2 a2x a3x a4x a5x a6x a7x s6 s9 s10 s11 v3 v4 v5 v6
                             _ _ _ _ _ idx _ act _ _ sel _ _ _ _ tS F1 fc m4 FPOS ltac:(ul) ltac:(unfold shad, SHB; lia) ltac:(unfold shad, SHB; ul) ltac:(ul) ltac:(ul)
                             ltac:(unfold el_fddA; destruct (Z.leb_spec 10 n); lia) ltac:(unfold el_fdsA; destruct (Z.leb_spec 10 n); lia) FRl4 ltac:(unfold shad, SHB; exact FS4) MI4)|].
  cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & FRl5 & FS5). apply evt_done.
  assert (ART5 : ART RT Σ1 m5).
  { apply (art_client_write RT AF Σ1 m4 m5 sp' ART4 ltac:(rewrite SP1; ul)); [| exact WM5]. eapply CLW; [exact MU5|].
    unfold el_W3, shad, SHB. repeat constructor; cbn [fst snd]; lia. }
  assert (ST5 : stk asegs m5 lo sp').
  { apply (stk_agree asegs m4 m5 _ _ ST4); [| exact WM5]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. unfold el_W3, shad, SHB. cbn [outside]. repeat split; lia. }

  assert (AG25 : forall (P : Z -> Prop), (forall x, P x -> ~ (sp' <= x < sp' + 152) /\ ~ (f <= x < f + 24) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 76)) -> agree_on P m2 m5).
  { intros P HP. eapply agree_trans; [| apply (agree_of_munch _ _ _ _ MU5); intros x Hx; destruct (HP _ Hx) as (A1 & A2 & A3); unfold el_W3, shad, SHB; cbn [outside]; repeat split; ul].
    eapply agree_trans; [| apply (agree_of_munch _ _ _ _ MU4); intros x Hx; destruct (HP _ Hx) as (A1 & A2 & A3); unfold el_W2; cbn [outside]; repeat split; ul].
    apply (agree_of_munch _ _ _ _ MU3). intros x Hx. destruct (HP _ Hx) as (A1 & A2 & A3). unfold el_W1, shad, SHB. cbn [outside]. repeat split; ul. }
  assert (FRs5 : rw_cells asegs m5 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_agree_nw; [exact FRs2|]. apply AG25. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. repeat split; ul. }
  assert (STp5 : stk asegs m5 (sp' + 152) (usp - 104)) by (eapply stk_agree_nw; [exact STp2|]; apply AG25; intros x Hx; cbv beta in Hx; repeat split; ul).
  assert (FH5 : rw_cells asegs m5 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x126fb)) (C8 (Z_to_bv 64 0xb1608)) H3)).
  { eapply rw_cells_agree_nw; [exact FH3|]. eapply agree_trans; [| apply (agree_of_munch _ _ _ _ MU5); intros x Hx; unfold fz_hdr in Hx; cbn [cells_size csize Nat.add] in Hx; unfold el_W3, shad, SHB; cbn [outside]; repeat split; ul].
    apply (agree_of_munch _ _ _ _ MU4). intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. unfold el_W2. cbn [outside]. repeat split; ul. }
  Ltac xfer25 H AG25 := eapply rw_cells_agree_nw; [exact H|]; apply AG25; intros x Hx; cbn [cells_size csize Nat.add] in Hx; repeat split; ul.
  assert (FV5 : rw_cells asegs m5 (f + 32) [CB 24 q3]) by (xfer25 FV2 AG25).
  assert (F56' : rw_cells asegs m5 (f + 56) [CB 40 q4]) by (xfer25 F56 AG25).
  assert (FP5 : rw_cells asegs m5 (f + 96) [CB 80 q5]) by (xfer25 FP2 AG25).
  assert (F176' : rw_cells asegs m5 (f + 176) [CB 32 q6]) by (xfer25 F176 AG25).
  assert (FE5 : rw_cells asegs m5 (f + 208) [CB 16 q7]) by (xfer25 FE2 AG25).
  assert (F224' : rw_cells asegs m5 (f + 224) [CB 16 q8]) by (xfer25 F224 AG25).
  assert (FO5 : rw_cells asegs m5 (f + 240) [CB 288 q9]) by (xfer25 FO2 AG25).
  assert (F528' : rw_cells asegs m5 (f + 528) [CB 488 q10]) by (xfer25 F528 AG25).
  assert (LIB5 : el_libA m5).
  { apply (el_libA_agree m2 m5 LIB2). apply AG25. intros x Hx. pose proof (el_lib_rng_static x Hx) as [CS R].
    repeat split; intros E; apply (NCL x); [lia| left; exact CS| lia| left; exact CS| lia| left; exact CS]. }
  assert (BS5 : bytes_at asegs m5 d bs).
  { apply (bytes_at_agree asegs m2 m5 _ _ BS2). apply AG25. intros x Hx. cbv beta in Hx. pose proof (PLV x ltac:(subst n; lia)) as IL.
    repeat split; intros E; apply (NCL x); [lia| right; exact IL| lia| right; exact IL| lia| right; exact IL]. }
  assert (PRES5 : forall a : word, aclient (rt_live RT Σ) [] usp (bv_unsigned a) -> outside EL_LIB_FP (bv_unsigned a) -> m5 a = m a).
  { intros a Ha Ho. rewrite <- (PRES2' a Ha Ho). apply (AG25 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->.
    destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H FR1' SHT LOW LOR SPR; repeat split; ul| | | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)];
    (repeat split; intros E; apply (NCL (bv_unsigned a)); [| | | | |]; [lia| | lia| | lia|]); try (left; exact H); try (right; exact H). }

  set (X := mkLF usp sp' f lo).
  assert (LK : lfA_ok X).
  { subst X. constructor; cbn [lf_usp lf_S1 lf_F lf_lo].
    - split; [exact SPR| exact SPA'].
    - split; [exact SPT| exact SPA].
    - split; [clear - SP0W LOW; ul| exact LOR].
    - split; [exact FPOS|]. split; [exact F64|]. split; [exact FSEG| clear - FR1' LOW; ul].
    - unfold shad, SHB. split; [exact FSELF|]. split; [exact SHB0| clear - SHT LOW; ul]. }
  specialize (CUTS X eq_refl eq_refl LK). unfold cutS in CUTS. subst X. cbn [lf_usp lf_S1 lf_F lf_lo] in CUTS.
  unfold EL_SPLITRET_A in *.
  eapply (CUTS Σ1 m5 t0x v1 v2 _ a3x a4x a5x a6x a7x s9 s10 s11 v3 v4 v5 v6 F1 fc _ _ _ _ _ _ _ H3 tS q3 q4 q5 q6 q7 q8 q9 q10 idx act sel);
    [| exact FRl5| exact ACT| exact SEL| exact FS5| exact FV5| exact F56'| exact FP5| exact F176'| exact FE5| exact F224'| exact FO5| exact F528'| exact LV1| rewrite CR1; lia| exact FRM].
  unfold el_baseA. cbn [lf_usp lf_S1 lf_F lf_lo].
  split; [exact ART5|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact STp5|]. split; [exact FRs5|]. split; [exact FH5|].
  split; [exact BS5|]. split; [exact LIB5|]. split; [exact PRES5|]. split; [exact FRS1| exact SP1].
Qed.

End Front.
