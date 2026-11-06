(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_hdr Gm_iface LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition HS_STOPS : list Z := [0x9074c; 0x9097c; 0x61c00].

(* [comment removed for export] *)
Lemma hdr_sure_arith : forall w h d, hdr_args_ok w h d ->
  0 <= d <= 32 /\ 0 < w < 20001 /\ 0 < h < 20001
  /\ (d * w + 31) mod 18446744073709551616 = d * w + 31
  /\ 1 <= (d * w + 31) / 32 <= 20001
  /\ ((d * w + 31) / 32 * h) mod 18446744073709551616 = (d * w + 31) / 32 * h
  /\ 0 < (d * w + 31) / 32 * h /\ 4 * ((d * w + 31) / 32 * h) <= 67108864
  /\ (d * w + 31) / 32 = (w * d + 31) / 32.
Proof.
  intros w h d (DOK & WB & HB & RB).
  assert (DB : 1 <= d <= 32) by (clear - DOK; cbn in DOK; lia).
  assert (PB : 1 <= d * w <= 640000) by (clear - WB DB; nia).
  replace (w * d) with (d * w) in * by lia.
  set (P := d * w) in *. clearbody P.
  rewrite (Z.mod_small (P + 31)) by lia.
  assert (QB : 1 <= (P + 31) / 32 <= 20001) by (clear - PB; Z.div_mod_to_equations; lia).
  set (q := (P + 31) / 32) in *. clearbody q.
  assert (RB2 : 1 <= q * h <= 400020000) by (clear - QB HB; nia).
  set (R := q * h) in *. clearbody R.
  rewrite (Z.mod_small R) by lia.
  repeat split; lia.
Qed.

Section HDRS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixCreateHeader_sure_ok : pixCreateHeader_sure_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo w h d
    FDO MST -> (WR & ->) (HR & ->) (DR & ->) HOKA ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (hdr_sure_arith w h d HOKA) as (D0 & WB & HB & EQP & QB & EQR & RP & RB & EQW).
  pose proof HOKA as (DOKIN & _ & _ & RBND).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixCreateHeader, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, HS_STOPS in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  Time walk_to AF MST [(usp - 80, usp)] [0x9074c; 0x9097c; 0x61c00].
  rewrite (Z.mod_small d 64) by lia.
  replace (bv_eqb (Z_to_bv 64 (Z.land (4311810326 ≫ d) 1)) z64) with (negb (depth_okb d))
    by (symmetry; unfold bv_eqb; rewrite (inr64_unsigned_lit (Z.land (4311810326 ≫ d) 1)) by zrange;
        change (bv_unsigned z64) with 0; apply depth_bit; lia).
  assert (DOK : depth_okb d = true)
    by (unfold depth_okb; apply existsb_exists; exists d; split; [exact DOKIN| apply Z.eqb_refl]).
  rewrite DOK. cbn [negb]. cbv iota.
  Time awalk [0x9074c; 0x9097c; 0x61c00].
  hide DOK. hide DOKIN. hide RBND. hide EQP. hide EQR. hide EQW.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := 64); rt_side idtac;
    [ unfold CALLOC_MAX; lia
    | apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_calloc_hdr| left; lia] ]. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  change (1 * 64) with 64 in *. change (Z.to_nat 64) with 64%nat in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 64) :: _ |- _ => rename H into LVN; set (px := p) in * end.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
    pose proof (af_live_range RT AF S mm px 64 A ltac:(rewrite LVN; left; reflexivity)) as (_ & PXHI & PXSEG);
    pose proof (gp_live_hi RT GP S mm px 64 A ltac:(rewrite LVN; left; reflexivity)) as PXSH;
    assert (NCA : forall a, PF a -> a < px \/ px + 64 <= a)
      by (intros a Ha; apply (new_chunk_apart RT AF S mm px 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A LVN);
          [ assumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  refresh RT AF. lib_refresh RT GP. unfold SHB in *.
  Time walk_to AF MST [(usp - 80, usp); (px, px + 64)] (@nil Z).
  brfork SPP.
  all: awalk0.
  all: cps_stop.
  all: art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                           intros zz Hzz; right; right; left; exists px, 64; split; [rewrite LVN; left; reflexivity| lia]).
  all: lazymatch goal with
       | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
           is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); repeat split; lia)
       end.
  all: apply cps_finish; intros c Hc; subst QF; cbv beta.
  all: lazymatch type of Hc with ASTA RT ?S _ _ _ =>
         lazymatch goal with H : rw_cells asegs _ _ (C4 _ :: C4 _ :: C4 _ :: C4 (Z_to_bv 64 ?spp) :: _) |- _ =>
           exists S, px, (mkPixv w h d spp ((w * d + 31) / 32) 0 0 0 0 0 0) end end.
  all: (split; [| rewrite LVN; alg_tac]).
  all: (eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists).
  all: (split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|]).
  all: (split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|]).
  all: try (lazymatch goal with WMx : wmono asegs ?m0 ?mf |- wmono asegs ?m0 ?mf => exact WMx end).
  all: (split; [intros a Ha _; apply AGF; exact Ha|]).
  all: unhide_all.
  all: unfold pix_obj, chunk, pix_hdr_ok; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data].
  all: (split; [| repeat split; reflexivity]).
  all: (split; [| split; [split; [rewrite LVN; left; reflexivity| split; [lia| split; [assumption| lia]]]| split; [| split; left; reflexivity]]]).
  all: try (lazymatch goal with H : rw_cells asegs ?mm ?pp (C4 ?c0 :: ?cs) |- rw_cells asegs ?mm ?pp _ =>
         rewrite EQW in H;
         apply (rw_cells_recell _ _ _ _ H); [cbn; repeat split| reflexivity| reflexivity] end).
  all: (split; [exact DOKIN| split; [lia| split; [lia| split; [reflexivity| rewrite <- EQW; lia]]]]).
Qed.
End HDRS.
