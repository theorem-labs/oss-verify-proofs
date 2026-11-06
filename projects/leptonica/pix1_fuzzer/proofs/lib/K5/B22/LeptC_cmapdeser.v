(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.B22 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.B22 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.B22 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptC_cmapdeser_loop LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.



Section DS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Lemma tr_ds1 : In [0x8f490] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.
Lemma tr_ds2 : In [0x8f4e0] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.

Lemma pixcmapDeserialize_ok : pixcmapDeserialize_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo dp ncolors
    FDO MST -> -> -> -> NC DP4 OWN ENV RES.
  unfold lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (RESF & RESL & RESC & RESP).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct OWN as (dpp & dpk & DIN & DLO & DHI).
  pose proof (af_acc_live RT AF Σ m dpp dpk ART0 DIN) as (WRD & ACCD).
  pose proof (af_live_range RT AF Σ m dpp dpk ART0 DIN) as (DP0 & DPR & DPS).
  unfold entry_st, e_pixcmapDeserialize, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof ST as (STa & STb & _).
  Time walk_to AF MST [(usp - 112, usp)] [0x5dc60].
  (* [comment removed for export] *)
  cut2f 0x8f484 (Z_to_bv 5 10) (Z_to_bv 5 21)
        (fun (_ u2 : word) => exists depth, u2 = Z_to_bv 64 depth /\ In depth [1; 2; 4; 8] /\ ncolors <= 2 ^ depth).
  { brfork HB1.
    2:{ awalk [0x8f484]. cut2f_done ltac:(exists 8; split; [reflexivity| split; [cbn; tauto| lia]]). }
    awalk [0x8f484].
    brfork HB2.
    1:{ awalk [0x8f484]. cut2f_done ltac:(exists 4; split; [reflexivity| split; [cbn; tauto| lia]]). }
    awalk [0x8f484].
    destruct (Z.ltb_spec ncolors 3) as [HB3|HB3]; cbn [Z.b2z];
      [ cut2f_done ltac:(exists 1; split; [reflexivity| split; [cbn; tauto| lia]])
      | cut2f_done ltac:(exists 2; split; [reflexivity| split; [cbn; tauto| lia]]) ]. }
  destruct HP as (depth & -> & HD & HN).
  awalk [0x5dc60].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq; [eapply (gp_calloc RT GP) with (lo := lo) (nmemb := 1) (size := 24); rt_side idtac |].
  all: lazymatch goal with
       | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_ds1| left; ul]
       | |- (_ <= CALLOC_MAX) => unfold CALLOC_MAX; lia
       | |- _ => idtac
       end.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  lazymatch goal with H : rw_cells asegs ?mm ?p [CB (Z.to_nat (1 * 24)) ?bs] |- _ =>
    pose proof (rw_cells_recell mm p [CB (Z.to_nat (1 * 24)) bs]
                  [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)] H
                  ltac:(cbn; tauto) eq_refl eq_refl) as CMC; clear H end.
  change (1 * 24) with 24 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 24) :: _ |- _ => set (cmap := p) in * end.
  chunk_facts RT AF GP cmap 24.
  assert (CMAP_AP : forall a, PF a -> a < cmap \/ cmap + 24 <= a).
  { intros a Ha. lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (cmap, 24) :: _, FRS : rt_frames RT ?S = _, SP0 : rt_sp0 RT ?S = _ |- _ =>
      apply (new_chunk_apart RT AF S mm cmap 24 _ _ usp a A L FRS ltac:(rewrite SP0; ul) Ha) end. }
  walk_to AF MST [(usp - 112, usp); (cmap, cmap + 24)] [0x5dc60].
  cwalk [0x5dc60].
  assert (ENA : bv_swrap 32 (1 ≪ ((depth mod 18446744073709551616) mod 32)) = 2 ^ depth)
    by (destruct HD as [<-|[<-|[<-|[<-|[]]]]]; reflexivity).
  rewrite ENA in *. clear ENA.
  assert (NA : 2 <= 2 ^ depth <= 256) by (destruct HD as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia).
  set (nalloc := 2 ^ depth) in *.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists cmap, 24; split; [solve [in_live_tac]| lia]| exact I]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (CMAP_AP _ Hx); split; [lia| split; [lia| exact I]]).
  eapply cps_seq; [eapply (gp_calloc RT GP) with (lo := lo) (nmemb := nalloc) (size := 4); rt_side idtac |].
  all: lazymatch goal with
       | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_ds2| left; ul]
       | |- (_ <= CALLOC_MAX) => unfold CALLOC_MAX; lia
       | |- (Z.of_nat (length (rt_live _ _)) < LIVE_MAX) => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; lia
       | |- _ => idtac
       end.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  refresh RT AF.
  replace (nalloc * 4) with (4 * nalloc) in * by lia.
  lazymatch goal with H : rt_live RT ?S = (?p, 4 * nalloc) :: _ |- _ => set (arr := p) in * end.
  lazymatch goal with H : rt_live RT ?S = (arr, 4 * nalloc) :: _ |- _ => rename S into SF end.
  chunk_facts RT AF GP arr (4 * nalloc).
  assert (ARR_AP : forall a, PF a -> a < arr \/ arr + 4 * nalloc <= a).
  { intros a Ha. lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (arr, 4 * nalloc) :: _, FRS : rt_frames RT ?S = _, SP0 : rt_sp0 RT ?S = _ |- _ =>
      apply (new_chunk_apart RT AF S mm arr (4 * nalloc) _ _ usp a A L FRS ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul)) end.
    apply (aclient_mono _ _ usp _ _ _ _ Ha); [solve [live_add_tac]| solve [frames_sub_tac]| lia]. }
  assert (DCA : arr + 4 * nalloc <= cmap \/ cmap + 24 <= arr).
  { lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (arr, 4 * nalloc) :: _ |- _ =>
      apply (af_live_disj RT AF S mm arr (4 * nalloc) cmap 24 [] _ A L); cbn [app]; solve [in_live_tac] end. }
  assert (DDA : arr + 4 * nalloc <= dpp \/ dpp + dpk <= arr).
  { lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (arr, 4 * nalloc) :: _ |- _ =>
      apply (af_live_disj RT AF S mm arr (4 * nalloc) dpp dpk [] _ A L); cbn [app]; solve [in_live_tac] end. }
  assert (DDC : cmap + 24 <= dpp \/ dpp + dpk <= cmap).
  { lazymatch goal with A : ART RT ?S ?mm, L : rt_live RT ?S = (cmap, 24) :: _ |- _ =>
      apply (af_live_disj RT AF S mm cmap 24 dpp dpk [] _ A L); cbn [app]; exact DIN end. }
  walk_to AF MST [(usp - 112, usp); (cmap, cmap + 24); (arr, arr + 4 * nalloc)] [0x8f538].
  (* [comment removed for export] *)
  lazymatch goal with H : wr_at asegs ?mm dpp dpk |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wr_at_sub mm dpp dpk dp (4 * ncolors) H ltac:(lia) ltac:(lia) ltac:(lia)) as WRS end.
  apply wr_at_rw_CB in WRS; [| lia]. destruct WRS as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC. destruct DBC as [DB _].
  lazymatch goal with H : rw_cells asegs ?mm arr [CB _ _] |- _ => pose proof (u8arr_of_rw_cells asegs mm arr _ _ H) as UA; clear H end.
  lazymatch goal with H : acc asegs ?mm dpp dpk |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (acc_sub asegs mm dpp dpk dp (4 * ncolors) H ltac:(lia) ltac:(lia)) as ACCS end.
  eapply evt_cut.
  { eapply (deser_loop (Z.to_nat ncolors) 0) with (dbs := dbs) (abs := repeat (Z_to_bv 8 0) (Z.to_nat (4 * nalloc)))
                                                (depth := depth) (nalloc := nalloc) (arr := arr) (pad := repeat (Z_to_bv 8 0) 4).
    all: lazymatch goal with
         | |- rw_cells _ _ _ _ => exact CMC
         | |- u8arr _ _ _ _ => exact UA
         | |- bytes_at _ _ _ _ => exact DB
         | |- acc _ _ _ _ => first [exact ACCS | assumption]
         | |- mem_inv _ _ => assumption
         | |- Z.of_nat (length _) = _ => first [rewrite repeat_length; lia | rewrite DBL; lia]
         | |- _ => try lia
         end. }
  intros ms' PO. unfold deser_loop_post in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & abs' & -> & MU' & WM' & MI' & CMC' & UA' & UAL').
  assert (IVT : forall S, rt_live RT S = rt_live RT SF -> rt_frames RT S = rt_frames RT SF ->
            ivls_client (rt_live RT S) (rt_frames RT S) (usp + -112) [(usp - 112, usp); (cmap, cmap + 24); (arr, arr + 4 * nalloc)]).
  { intros S EL EF. rewrite EL. cbn [ivls_client]. split; [intros zz Hzz; left; ul|].
    split; [intros zz Hzz; right; right; left; exists cmap, 24; split; [solve [in_live_tac]| lia]|].
    split; [intros zz Hzz; right; right; left; exists arr, (4 * nalloc); split; [solve [in_live_tac]| lia]| exact I]. }
  loop_art RT AF SF m' (usp + -112) MU' ltac:(exact (IVT SF eq_refl eq_refl)).
  clear CMC UA DB.
  lazymatch type of MU' with munch _ ?mm m' =>
    loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR CKS CKR0 CKS0 DCA DDA DDC DLO DHI DPR DPS LOW LOR SPT SPB USP0 USP1 STa NA0 NA1 NC0 NC1; lia) end.
  cwalk (@nil Z).
  cps_stop.
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (CMAP_AP _ Hx); pose proof (ARR_AP _ Hx);
                                   split; [lia| split; [lia| split; [lia| exact I]]]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  exists SF, cmap, (mkCmapv arr depth nalloc ncolors).
  split.
  - eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [exact ARTl| split; [exact MI'| split; [| assumption]]]| split; assumption]|].
    + repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans.
    + split; [intros a Ha _; exact (AGF a Ha)|]. right. split; [| reflexivity].
      unfold cmap_obj, cmap_cells, chunk, cmap_ok. cbn [c_arr c_depth c_nalloc c_n].
      split; [exists (repeat (Z_to_bv 8 0) 4); exact CMC'|].
      split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|].
      split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|].
      split; [split; [exact HD| split; [reflexivity| lia]]| lia].
  - destruct (Z.eqb_spec cmap 0) as [E0|_]; [lia|].
    repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
    repeat split; auto; lia.
Qed.
End DS.
