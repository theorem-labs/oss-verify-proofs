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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain Lept_objkit LeptL_kit
  Gm_iface Gq_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition RA_CMAPLIN_CALLOC1 : Z := 0x96f7c.
Definition RA_CMAPLIN_CALLOC2 : Z := 0x96fbc.
Lemma tr_cmaplin_1 : In [RA_CMAPLIN_CALLOC1] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_cmaplin_2 : In [RA_CMAPLIN_CALLOC2] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Definition cmaplin24_cells : list cell :=
  [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 255);
   C1 (Z_to_bv 8 85); C1 (Z_to_bv 8 85); C1 (Z_to_bv 8 85); C1 (Z_to_bv 8 255);
   C1 (Z_to_bv 8 170); C1 (Z_to_bv 8 170); C1 (Z_to_bv 8 170); C1 (Z_to_bv 8 255);
   C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255)].


(* [comment removed for export] *)
Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Ltac divw_fix :=
  match goal with |- context [v_divw (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] =>
    let v := eval vm_compute in (bv_unsigned (v_divw (Z_to_bv 64 a) (Z_to_bv 64 b))) in
    replace (v_divw (Z_to_bv 64 a) (Z_to_bv 64 b)) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
  end.
(* [comment removed for export] *)
Ltac clin_iter :=
  cwalk1; cwalk [0x970b4; 0x9707c; 0x97288]; rewrite !sx32_small by lia;
  cwalk [0x970d8; 0x9707c; 0x97288]; divw_fix;
  cwalk [0x9707c; 0x97288].

Section CMAPLIN.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition pixcmapCreateLinear24_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 2 -> a1 = Z_to_bv 64 4 ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 2 0 ->
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
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> -> -> ENV RES.
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
  walk_to AF MST [(usp - 160, usp)] [e_calloc].
  idtac "MARK clin: at calloc 1".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  match goal with MUx : munch _ m ?mx |- _ => rename MUx into MU1; rename mx into m1 end.
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := 24); rt_side idtac.
    - unfold CALLOC_MAX; lia.
    - apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_cmaplin_1| left; rewrite ?unsigned_lit by lia; lia]. }
  idtac "MARK clin: calloc 1 applied".
  after_call RT AF.
  idtac "MARK clin: after_call 1".
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
  walk_to AF MST [(usp - 160, usp); (cmap, cmap + 24)] [e_calloc].
  idtac "MARK clin: at calloc 2".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                      intros zz Hzz; right; right; left; exists cmap, 24; split; [rewrite LVA; left; reflexivity| lia])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); repeat split; lia).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 4) (size := 4); rt_side idtac.
    - unfold CALLOC_MAX; lia.
    - rewrite LVA; cbn [length]; lia.
    - apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_cmaplin_2| left; rewrite ?unsigned_lit by lia; lia]. }
  idtac "MARK clin: calloc 2 applied".
  after_call RT AF.
  idtac "MARK clin: after_call 2".
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
  idtac "MARK clin: facts 2".
  walk_to AF MST [(usp - 160, usp); (cmap, cmap + 24); (carr, carr + 16)] [0x97088].
  idtac "MARK clin: at loop head (i = 0)".
  lazymatch goal with H : cmap mod 16 = 0 |- _ => rename H into CM16 end.
  lazymatch goal with H : carr mod 16 = 0 |- _ => rename H into CA16 end.
  rewrite (land7_mod8 (cmap + 12)) in *. rewrite (land7_mod8 (cmap + 16)) in *.
  replace ((cmap + 12) mod 8) with 4 in * by (clear - CM16; Z.div_mod_to_equations; lia).
  replace ((cmap + 16) mod 8) with 0 in * by (clear - CM16; Z.div_mod_to_equations; lia).
  cbn [Z.add] in *.
  clin_iter.
  idtac "MARK clin: iter 0 done".
  clin_iter.
  idtac "MARK clin: iter 1 done".
  clin_iter.
  idtac "MARK clin: iter 2 done".
  clin_iter.
  idtac "MARK clin: iter 3 done".
  cwalk (@nil Z).
  idtac "MARK clin: at ret".
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul
     | split; [intros zz Hzz; right; right; left; exists cmap, 24; split; [exact INA2| lia]
     | split; [intros zz Hzz; right; right; left; exists carr, 16; split; [exact INB| lia]| exact I]]]).
  lazymatch goal with
  | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); pose proof (NCB _ Hx); repeat split; lia)
  end.
  idtac "MARK clin: finish facts".
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  exists Σ2, cmap, carr.
  split; [| rewrite LVB2, LVA; alg_tac].
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
  split; [intros a Ha _; apply AGF; exact Ha|].
  split.
  - unfold cmap_obj, cmap_cells, cmap_ok. cbn [c_arr c_depth c_nalloc c_n].
    lazymatch goal with NA : rw_cells asegs ?mm cmap ?cs |- _ => split; [eexists; exact NA|] end.
    split; [unfold chunk; split; [exact INA2| repeat split; first [assumption | lia]]|].
    change (4 * 4) with 16.
    split; [unfold chunk; split; [exact INB| repeat split; first [assumption | lia]]|].
    split; [| clear - QAB; lia]. split; [cbn; tauto|]. split; [reflexivity| lia].
  - lazymatch goal with CA : rw_cells asegs ?mm carr ?cs |- _ =>
      replace (Z_to_bv 8 (-1)) with (Z_to_bv 8 255) in CA by (apply bv_eq; vm_compute; reflexivity); exact CA end.
Qed.
End CMAPLIN.
