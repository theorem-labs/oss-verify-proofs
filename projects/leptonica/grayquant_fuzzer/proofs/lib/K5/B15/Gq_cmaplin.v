(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain Lept_objkit LeptL_kit
  Gm_iface Gq_iface Ed_tracekit Gq_cmaplin_addcolor
  LeptB_guard LeptB_guard2 Gq_guardx.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition RA_CMAPLIN_CALLOC1 : Z := 0x97950.
Definition RA_CMAPLIN_CALLOC2 : Z := 0x9799c.
Lemma tr_cmaplin_2 : In [RA_CMAPLIN_CALLOC2] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Lemma cmaplin_ras_ne : forall ras, In (RA_CMAPLIN_CALLOC1 :: ras) CLIENT_TRACES -> ras <> [].
Proof.
  intros ras H E. subst ras. unfold RA_CMAPLIN_CALLOC1 in H.
  revert H. vm_compute. intros H. repeat (destruct H as [H|H]; [discriminate|]). exact H.
Qed.

(* [comment removed for export] *)
Lemma cmaplin_unwind1 : forall (m : mem) (sp s0 : word) ras sp', uctx m sp s0 ras -> In (RA_CMAPLIN_CALLOC1 :: ras) CLIENT_TRACES ->
  bv_unsigned sp' <= bv_unsigned sp -> unwind_okC m (Z_to_bv 64 RA_CMAPLIN_CALLOC1) s0 sp'.
Proof.
  intros m sp s0 ras sp' U T LE. exists ras. split.
  - apply (chain_ok_lower ras m (bv_unsigned sp) (bv_unsigned sp') (bv_unsigned s0) (cmaplin_ras_ne ras T) LE U).
  - rewrite unsigned_lit by (unfold RA_CMAPLIN_CALLOC1; lia). exact T.
Qed.

(* [comment removed for export] *)
Definition cmaplin24_cells : list cell :=
  [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 255);
   C1 (Z_to_bv 8 85); C1 (Z_to_bv 8 85); C1 (Z_to_bv 8 85); C1 (Z_to_bv 8 255);
   C1 (Z_to_bv 8 170); C1 (Z_to_bv 8 170); C1 (Z_to_bv 8 170); C1 (Z_to_bv 8 255);
   C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255)].

(* [comment removed for export] *)
Ltac divw_fix :=
  match goal with |- context [v_divw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] =>
    let v := eval vm_compute in (bv_unsigned (v_divw (Z_to_bv 64 a) (Z_to_bv 64 b))) in
    replace (v_divw (Z_to_bv 64 a) (Z_to_bv 64 b)) with (Z_to_bv 64 v) in * by (apply bv_eq; vm_compute; reflexivity)
  end.

Section CMAPLIN.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition pixcmapCreateLinear24_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 2 -> a1 = Z_to_bv 64 4 ->
  uctx m sp s0 ras -> In (RA_CMAPLIN_CALLOC1 :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 2 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapCreateLinear m)))
    (fun c => exists (Σ' : rts RT) (cmap carr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 cmap) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ cmap_obj (rt_live RT Σ') m' cmap (mkCmapv carr 2 4 4)
          /\ rw_cells asegs m' carr cmaplin24_cells) c
       /\ rt_live RT Σ' = (carr, 16) :: (cmap, 24) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ').

Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixcmapCreateLinear24_ok : pixcmapCreateLinear24_cps.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ras
    FDO MST -> -> -> UC TR ENV RES.
  pose proof (pixcmapAddColor_grayN_ok RT AF GP) as ADDC.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixcmapCreateLinear, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  walk_to AF MST [(usp - 48, usp)] [e_calloc].
  idtac "MARK clinB: at calloc 1".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  match goal with MUx : munch _ m ?mx |- _ => rename MUx into MU1; rename mx into m1 end.
  assert (UC1 : uctx m1 (Z_to_bv 64 usp) s0 ras).
  { unfold uctx in UC |- *. rewrite unsigned_lit by lia. unfold usp in UC |- *.
    apply (chain_ok_keep ras m m1 _ _ UC). intros a Ha. apply MU1. cbn [outside]. unfold USTACK_TOP in Ha. lia. }
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := 24); rt_side idtac.
    - unfold CALLOC_MAX; lia.
    - eapply (cmaplin_unwind1 m1 (Z_to_bv 64 usp) s0 ras); [exact UC1 | exact TR | rewrite !unsigned_lit by lia; lia]. }
  idtac "MARK clinB: calloc 1 applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  change (1 * 24) with 24 in *. change (Z.to_nat 24) with 24%nat in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 24) :: _ |- _ => rename H into LVA; rename S into Σ1; set (cmap := p) in * end.
  assert (INA : In (cmap, 24) (rt_live RT Σ1)) by (rewrite LVA; left; reflexivity).
  lazymatch goal with A : ART RT Σ1 ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
    pose proof (af_live_range RT AF Σ1 mm cmap 24 A ltac:(rewrite LVA; left; reflexivity)) as (_ & PAHI & PASEG);
    pose proof (gp_live_hi RT GP Σ1 mm cmap 24 A ltac:(rewrite LVA; left; reflexivity)) as PASH;
    assert (NCA : forall a, PF a -> a < cmap \/ cmap + 24 <= a)
      by (intros a Ha; apply (new_chunk_apart RT AF Σ1 mm cmap 24 (rt_live RT Σ) (rt_frames RT Σ) usp a A LVA);
          [ assumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  refresh RT AF. unfold SHB in *.
  walk_to AF MST [(usp - 48, usp); (cmap, cmap + 24)] [e_calloc; 0x97b24].
  idtac "MARK clinB: at calloc 2".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                      intros zz Hzz; right; right; left; exists cmap, 24; split; [rewrite LVA; left; reflexivity| lia])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); repeat split; lia).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 4) (size := 4); rt_side idtac.
    - unfold CALLOC_MAX; lia.
    - rewrite LVA; cbn [length]; lia.
    - apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_cmaplin_2| left; ul]. }
  idtac "MARK clinB: calloc 2 applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  change (4 * 4) with 16 in *. change (Z.to_nat 16) with 16%nat in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 16) :: _ |- _ => rename H into LVB2; rename S into Σ2; set (carr := p) in * end.
  assert (INB : In (carr, 16) (rt_live RT Σ2)) by (rewrite LVB2; left; reflexivity).
  assert (INA2 : In (cmap, 24) (rt_live RT Σ2)) by (rewrite LVB2; right; exact INA).
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  refresh RT AF. lib_refresh RT GP. unfold SHB in *.
  lazymatch goal with A : ART RT Σ2 ?mm |- cps _ (ASTA RT Σ2 _ _) _ => rename A into ART2; rename mm into m2b end.
  assert (QAB : cmap + 24 <= carr \/ carr + 16 <= cmap).
  { pose proof (af_live_disj RT AF Σ2 m2b carr 16 cmap 24 [] (rt_live RT Σ1) ART2 LVB2 ltac:(cbn [app]; exact INA)) as X; clear - X; lia. }
  pose proof (af_live_range RT AF Σ2 m2b carr 16 ART2 INB) as (_ & PBHI & PBSEG).
  pose proof (gp_live_hi RT GP Σ2 m2b carr 16 ART2 INB) as PBSH.
  assert (NCB : forall a, PF a -> a < carr \/ carr + 16 <= a).
  { intros a Ha. eapply (new_chunk_apart RT AF Σ2 m2b carr 16 (rt_live RT Σ1) (rt_frames RT Σ2) usp a ART2 LVB2 eq_refl).
    - repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul.
    - unfold PF in Ha. apply (aclient_mono _ _ usp _ _ _ _ Ha); [solve [live_add_tac]| solve [frames_sub_tac]| lia]. }
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  assert (LVc : rt_live RT Σ2 = (carr, 16) :: (cmap, 24) :: rt_live RT Σ) by (rewrite LVB2, LVA; reflexivity).
  idtac "MARK clinB: facts 2".
  walk_to AF MST [(usp - 48, usp); (cmap, cmap + 24)] [e_pixcmapAddColor; 0x97b24].
  idtac "MARK clinB: at AddColor 0".
  (* [comment removed for export] *)
  divw_fix.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]]; intros zz Hzz; right; right; left; exists cmap, 24; split; [exact INA2| lia]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); repeat split; lia).
  lazymatch goal with CMC : rw_cells asegs ?mc cmap [C8 _; C4 _; C4 _; C4 _; CB 4 ?pd] |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (CMO : cmap_obj (rt_live RT S) mc cmap (mkCmapv carr 2 4 0))
      by (unfold cmap_obj, cmap_ok, chunk, cmap_cells; cbn [c_arr c_depth c_nalloc c_n]; change (4 * 4) with 16;
          split; [exists pd; exact CMC
                | split; [split; [exact INA2| lia]
                | split; [split; [exact INB| lia]
                | split; [split; [cbn; tauto| lia] | clear - QAB; lia]]]]); clear CMC end.
  eapply cps_seq.
  { eapply ADDC with (lo := lo) (cv := mkCmapv carr 2 4 0) (v := 0).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- _ => first [reflexivity | cbn [c_n c_nalloc]; lia | lazymatch goal with |- ?g => idtac "ADDC SIDE LEFT:" g end]
         end. }
  clear CMO.
  idtac "MARK clinB: ADDC 0 applied".
  after_call RT AF.
  cbn [c_arr c_depth c_nalloc c_n] in *.
  fold_ag ltac:(fun Hx => pose proof (NCA _ Hx) as Xc; pose proof (NCB _ Hx) as Xa; split;
                 [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                 | cbn [outside]; clear - Xc Xa; lia]).
  lazymatch goal with H : cmap_obj _ _ cmap _ |- _ => rename H into CMO end.
  lazymatch goal with A : ART RT ?Sa ?mm |- cps _ (ASTA RT ?Sa _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (LVSa : rt_live RT Sa = (carr, 16) :: (cmap, 24) :: rt_live RT Σ) by (repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; reflexivity);
    clear LVc; rename LVSa into LVc; try clear INAc; try clear INBc;
    assert (INAc : In (cmap, 24) (rt_live RT Sa)) by (rewrite LVc; right; left; reflexivity);
    assert (INBc : In (carr, 16) (rt_live RT Sa)) by (rewrite LVc; left; reflexivity) end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  idtac "MARK clinB: after ADDC 0".
  walk_to AF MST [(usp - 48, usp)] [e_pixcmapAddColor; 0x97b24].
  idtac "MARK clinB: walked after ADDC 0".
  (* [comment removed for export] *)
  divw_fix.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply ADDC with (lo := lo) (cv := mkCmapv carr 2 4 1) (v := 85).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- _ => first [reflexivity | cbn [c_n c_nalloc]; lia | lazymatch goal with |- ?g => idtac "ADDC SIDE LEFT:" g end]
         end. }
  clear CMO.
  idtac "MARK clinB: ADDC 1 applied".
  after_call RT AF.
  cbn [c_arr c_depth c_nalloc c_n] in *.
  fold_ag ltac:(fun Hx => pose proof (NCA _ Hx) as Xc; pose proof (NCB _ Hx) as Xa; split;
                 [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                 | cbn [outside]; clear - Xc Xa; lia]).
  lazymatch goal with H : cmap_obj _ _ cmap _ |- _ => rename H into CMO end.
  lazymatch goal with A : ART RT ?Sa ?mm |- cps _ (ASTA RT ?Sa _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (LVSa : rt_live RT Sa = (carr, 16) :: (cmap, 24) :: rt_live RT Σ) by (repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; reflexivity);
    clear LVc; rename LVSa into LVc; try clear INAc; try clear INBc;
    assert (INAc : In (cmap, 24) (rt_live RT Sa)) by (rewrite LVc; right; left; reflexivity);
    assert (INBc : In (carr, 16) (rt_live RT Sa)) by (rewrite LVc; left; reflexivity) end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  idtac "MARK clinB: after ADDC 1".
  walk_to AF MST [(usp - 48, usp)] [e_pixcmapAddColor; 0x97b24].
  idtac "MARK clinB: walked after ADDC 1".
  (* [comment removed for export] *)
  divw_fix.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply ADDC with (lo := lo) (cv := mkCmapv carr 2 4 2) (v := 170).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- _ => first [reflexivity | cbn [c_n c_nalloc]; lia | lazymatch goal with |- ?g => idtac "ADDC SIDE LEFT:" g end]
         end. }
  clear CMO.
  idtac "MARK clinB: ADDC 2 applied".
  after_call RT AF.
  cbn [c_arr c_depth c_nalloc c_n] in *.
  fold_ag ltac:(fun Hx => pose proof (NCA _ Hx) as Xc; pose proof (NCB _ Hx) as Xa; split;
                 [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                 | cbn [outside]; clear - Xc Xa; lia]).
  lazymatch goal with H : cmap_obj _ _ cmap _ |- _ => rename H into CMO end.
  lazymatch goal with A : ART RT ?Sa ?mm |- cps _ (ASTA RT ?Sa _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (LVSa : rt_live RT Sa = (carr, 16) :: (cmap, 24) :: rt_live RT Σ) by (repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; reflexivity);
    clear LVc; rename LVSa into LVc; try clear INAc; try clear INBc;
    assert (INAc : In (cmap, 24) (rt_live RT Sa)) by (rewrite LVc; right; left; reflexivity);
    assert (INBc : In (carr, 16) (rt_live RT Sa)) by (rewrite LVc; left; reflexivity) end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  idtac "MARK clinB: after ADDC 2".
  walk_to AF MST [(usp - 48, usp)] [e_pixcmapAddColor; 0x97b24].
  idtac "MARK clinB: walked after ADDC 2".
  (* [comment removed for export] *)
  divw_fix.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply ADDC with (lo := lo) (cv := mkCmapv carr 2 4 3) (v := 255).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- _ => first [reflexivity | cbn [c_n c_nalloc]; lia | lazymatch goal with |- ?g => idtac "ADDC SIDE LEFT:" g end]
         end. }
  clear CMO.
  idtac "MARK clinB: ADDC 3 applied".
  after_call RT AF.
  cbn [c_arr c_depth c_nalloc c_n] in *.
  fold_ag ltac:(fun Hx => pose proof (NCA _ Hx) as Xc; pose proof (NCB _ Hx) as Xa; split;
                 [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                 | cbn [outside]; clear - Xc Xa; lia]).
  lazymatch goal with H : cmap_obj _ _ cmap _ |- _ => rename H into CMO end.
  lazymatch goal with A : ART RT ?Sa ?mm |- cps _ (ASTA RT ?Sa _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (LVSa : rt_live RT Sa = (carr, 16) :: (cmap, 24) :: rt_live RT Σ) by (repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; reflexivity);
    clear LVc; rename LVSa into LVc; try clear INAc; try clear INBc;
    assert (INAc : In (cmap, 24) (rt_live RT Sa)) by (rewrite LVc; right; left; reflexivity);
    assert (INBc : In (carr, 16) (rt_live RT Sa)) by (rewrite LVc; left; reflexivity) end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  idtac "MARK clinB: after ADDC 3".
  walk_to AF MST [(usp - 48, usp)] [e_pixcmapAddColor; 0x97b24].
  idtac "MARK clinB: walked after ADDC 3".
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with
  | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
  end.
  idtac "MARK clinB: finish facts".
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, cmap, carr end.
  split; [| split; [exact LVc| alg_tac]].
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; assumption]]| split; assumption]|].
  split; [intros a Ha _; apply AGF; exact Ha|].
  split.
  - lazymatch goal with H : cmap_obj _ ?mm cmap _ |- cmap_obj _ ?mm cmap _ => exact H end.
  - lazymatch goal with Q0 : rw_cells asegs ?mm (carr + 4 * 0) [C1 _; C1 _; C1 _; C1 _], Q1 : rw_cells asegs ?mm (carr + 4 * 1) [C1 _; C1 _; C1 _; C1 _],
                        Q2 : rw_cells asegs ?mm (carr + 4 * 2) [C1 _; C1 _; C1 _; C1 _], Q3 : rw_cells asegs ?mm (carr + 4 * 3) [C1 _; C1 _; C1 _; C1 _] |- _ =>
      replace (carr + 4 * 0) with carr in Q0 by lia; unfold cmaplin24_cells;
      apply (proj2 (rw_cells_app mm carr [C1 _; C1 _; C1 _; C1 _] [C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _])); split; [exact Q0|];
      lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (carr + 4 * 1) by (cbn [cells_size csize Nat.add]; lia) end;
      apply (proj2 (rw_cells_app mm (carr + 4 * 1) [C1 _; C1 _; C1 _; C1 _] [C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _])); split; [exact Q1|];
      lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (carr + 4 * 2) by (cbn [cells_size csize Nat.add]; lia) end;
      apply (proj2 (rw_cells_app mm (carr + 4 * 2) [C1 _; C1 _; C1 _; C1 _] [C1 _; C1 _; C1 _; C1 _])); split; [exact Q2|];
      lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (carr + 4 * 3) by (cbn [cells_size csize Nat.add]; lia) end;
      exact Q3 end.
Qed.
End CMAPLIN.
