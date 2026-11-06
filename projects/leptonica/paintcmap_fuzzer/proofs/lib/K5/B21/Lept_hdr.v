(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition depth_okb (d : Z) : bool := existsb (Z.eqb d) [1; 2; 4; 8; 16; 24; 32].
Lemma depth_bit : forall d, 0 <= d <= 32 -> (Z.land (Z.shiftr 4311810326 d) 1 =? 0) = negb (depth_okb d).
Proof.
  intros d Hd.
  assert (T : forallb (fun k => Bool.eqb (Z.land (Z.shiftr 4311810326 (Z.of_nat k)) 1 =? 0) (negb (depth_okb (Z.of_nat k)))) (seq 0 33) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in T. specialize (T (Z.to_nat d) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T by lia.
  apply Bool.eqb_prop in T. exact T.
Qed.
Lemma depth_okb_in : forall d, depth_okb d = true -> In d [1; 2; 4; 8; 16; 24; 32].
Proof.
  intros d H. unfold depth_okb in H. apply existsb_exists in H. destruct H as (x & Hx & E). apply Z.eqb_eq in E. subst x. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma hdr_ok_arith : forall w h d, - 2^31 <= w -> w < 2^31 -> - 2^31 <= h -> h < 2^31 -> 0 <= d -> d <= 32 ->
  In d [1; 2; 4; 8; 16; 24; 32] ->
  0 < w mod 18446744073709551616 -> w mod 18446744073709551616 < 9223372036854775808 ->
  0 < h mod 18446744073709551616 -> h mod 18446744073709551616 < 9223372036854775808 ->
  w < 20001 -> h < 20001 ->
  (((d * w + 31) mod 18446744073709551616 / 32 * h) mod 18446744073709551616 * 4) mod 18446744073709551616 < 67108865 ->
  0 < w <= 20000 /\ 0 < h <= 20000 /\ 0 < 4 * ((w * d + 31) / 32 * h) <= 67108864
  /\ (d * w + 31) mod 18446744073709551616 / 32 = (w * d + 31) / 32.
Proof.
  intros w h d W0 W1 H0 H1 D0 D1 DOK Wa Wb Ha Hb W20 H20 B.
  assert (WP : 0 < w) by (clear - W0 W1 Wa Wb; Z.div_mod_to_equations; lia).
  assert (HP : 0 < h) by (clear - H0 H1 Ha Hb; Z.div_mod_to_equations; lia).
  assert (DP : 1 <= d) by (clear - DOK; cbn in DOK; lia).
  assert (PB : 1 <= d * w <= 640000) by (clear - WP W20 DP D1; nia).
  replace (w * d) with (d * w) by lia.
  set (P := d * w) in *. clearbody P.
  rewrite (Z.mod_small (P + 31)) in * by lia.
  assert (QB : 1 <= (P + 31) / 32 <= 20001) by (clear - PB; Z.div_mod_to_equations; lia).
  set (q := (P + 31) / 32) in *. clearbody q.
  assert (RB : 1 <= q * h <= 400020000) by (clear - QB HP H20; nia).
  set (R := q * h) in *. clearbody R.
  rewrite (Z.mod_small R) in B by lia. rewrite (Z.mod_small (R * 4)) in B by lia.
  repeat split; lia.
Qed.

Lemma tr_calloc_hdr : In [0x8ee84] CLIENT_TRACES.
Proof. vm_compute. tauto. Qed.

Section HDR.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis STDERR : lept_stderr_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.

Theorem pixCreateHeader_ok : pixCreateHeader_cps RT.
Proof using AF GP STDERR RERR.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo w h d
    FDO MST -> (WR & ->) (HR & ->) (DR & ->) ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixCreateHeader, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  pose proof RERR as RE. unfold returnError_cps in RE. pose proof STDERR as SE. unfold lept_stderr_cps in SE.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  Time walk_to AF MST [(usp - 80, usp)] [0x8d93c; 0x8db6c; 0x5ee1c].
  brfork D32.
  - (* [comment removed for export] *)
    Time awalk [0x8d93c; 0x8db6c; 0x5ee1c].
    hdr_tail_leaf RT AF RE PFS ESP AGF PF QF usp lo.
  - assert (D0 : 0 <= d <= 32) by (clear - D32 DR; Z.div_mod_to_equations; lia).
    clear D32.
    awalk [0x8d93c; 0x8db6c; 0x5ee1c].
    rewrite (Z.mod_small d 64) by lia.
    replace (bv_eqb (Z_to_bv 64 (Z.land (4311810326 ≫ d) 1)) z64) with (negb (depth_okb d))
      by (symmetry; unfold bv_eqb; rewrite (inr64_unsigned_lit (Z.land (4311810326 ≫ d) 1)) by zrange;
          change (bv_unsigned z64) with 0; apply depth_bit; lia).
    destruct (depth_okb d) eqn:DOK; cbn [negb]; cbv iota.
    2:{ awalk [0x8d93c; 0x8db6c; 0x5ee1c]. hdr_tail_leaf RT AF RE PFS ESP AGF PF QF usp lo. }
    apply depth_okb_in in DOK.
    awalk [0x8d93c; 0x8db6c; 0x5ee1c].
    brfork W0.
    { awalk [0x8d93c; 0x8db6c; 0x5ee1c]. hdr_tail_leaf RT AF RE PFS ESP AGF PF QF usp lo. }
    awalk [0x8d93c; 0x8db6c; 0x5ee1c].
    brfork H0.
    { awalk [0x8d93c; 0x8db6c; 0x5ee1c]. hdr_tail_leaf RT AF RE PFS ESP AGF PF QF usp lo. }
    awalk [0x8d93c; 0x8db6c; 0x5ee1c].
    brfork WPL.
    2:{ (* [comment removed for export] *)
      awalk [0x8d93c; 0x8db6c; 0x5ee1c].
      hdr_msg_call RT AF GP SE PFS AGF usp lo [true; false; false; false].
      walk_to AF MST [(usp - 80, usp)] [0x8d93c; 0x8db6c; 0x5ee1c].
      hdr_tail_leaf RT AF RE PFS ESP AGF PF QF usp lo. }
    awalk [0x8d93c; 0x8db6c; 0x5ee1c].
    brfork B31.
    2:{ awalk [0x8d93c; 0x8db6c; 0x5ee1c].
        hdr_msg_call RT AF GP SE PFS AGF usp lo [true; false; false; false].
        walk_to AF MST [(usp - 80, usp)] [0x8d93c; 0x8db6c; 0x5ee1c].
        hdr_tail_leaf RT AF RE PFS ESP AGF PF QF usp lo. }
    awalk [0x8d93c; 0x8db6c; 0x5ee1c].
    brfork B64.
    2:{ awalk [0x8d93c; 0x8db6c; 0x5ee1c].
        hdr_msg_call RT AF GP SE PFS AGF usp lo [true].
        walk_to AF MST [(usp - 80, usp)] [0x8d93c; 0x8db6c; 0x5ee1c].
        hdr_ret_null RT AF PFS ESP AGF PF QF. }
    awalk [0x8d93c; 0x8db6c; 0x5ee1c].
    brfork W20.
    2:{ awalk [0x8d93c; 0x8db6c; 0x5ee1c].
        hdr_msg_call RT AF GP SE PFS AGF usp lo [true].
        walk_to AF MST [(usp - 80, usp)] [0x8d93c; 0x8db6c; 0x5ee1c].
        hdr_ret_null RT AF PFS ESP AGF PF QF. }
    awalk [0x8d93c; 0x8db6c; 0x5ee1c].
    brfork H20.
    2:{ awalk [0x8d93c; 0x8db6c; 0x5ee1c].
        hdr_msg_call RT AF GP SE PFS AGF usp lo [true].
        walk_to AF MST [(usp - 80, usp)] [0x8d93c; 0x8db6c; 0x5ee1c].
        hdr_ret_null RT AF PFS ESP AGF PF QF. }
    awalk [0x8d93c; 0x8db6c; 0x5ee1c].
    assert (WPOSb : 0 < w) by (clear - W1 W2 WR; Z.div_mod_to_equations; lia).     (* [comment removed for export] *)
    assert (HPOSb : 0 < h) by (clear - H1 H2 HR; Z.div_mod_to_equations; lia).
    assert (DPOSb : 1 <= d <= 32) by (clear - DOK; cbn [In] in DOK; lia).
    repeat match goal with H : context [Z.modulo _ 18446744073709551616] |- _ => lazymatch type of H with hid _ => fail | _ => hide H end end.
    hide DOK.
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
    all: (split; [| rewrite LVN; replace (px =? 0) with false by (symmetry; apply Z.eqb_neq; lia); alg_tac]).
    all: (eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists).
    all: (split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|]).
    all: (split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|]).
    all: try (lazymatch goal with WMx : wmono asegs ?m0 ?mf |- wmono asegs ?m0 ?mf => exact WMx end).
    all: (split; [intros a Ha _; apply AGF; exact Ha| right]).
    all: unhide_all.
    all: assert (HA : 0 < w <= 20000 /\ 0 < h <= 20000 /\ 0 < 4 * ((w * d + 31) / 32 * h) <= 67108864
                       /\ (d * w + 31) mod 18446744073709551616 / 32 = (w * d + 31) / 32) by (apply hdr_ok_arith; assumption).
    all: destruct HA as (WOK & HOK & ROK & EQW).
    all: unfold pix_obj, chunk, pix_hdr_ok; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data].
    all: (split; [| repeat split; reflexivity]).
    all: (split; [| split; [split; [rewrite LVN; left; reflexivity| split; [lia| split; [assumption| lia]]]| split; [| split; left; reflexivity]]]).
    all: try (lazymatch goal with H : rw_cells asegs ?mm ?pp (C4 ?c0 :: ?cs) |- rw_cells asegs ?mm ?pp _ =>
           rewrite EQW in H;
           apply (rw_cells_recell _ _ _ _ H); [cbn; repeat split| reflexivity| reflexivity] end).
    all: (split; [exact DOK| split; [exact WOK| split; [exact HOK| split; [reflexivity| lia]]]]).
Qed.
End HDR.
