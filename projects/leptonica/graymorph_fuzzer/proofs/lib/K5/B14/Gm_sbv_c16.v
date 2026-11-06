(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Gm_iface Gm_ropkit GmL_sbv_loop Gm_sbv_defs LeptB_guard LeptB_guard2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac tlia ::= sf_clear_big;
              first [ sf_unhide; unpark_all; zify_prune_sub; Zify.zify; xlia zchecker
                    | Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
Ltac local_acc FSH fr idx off FR64 NAME :=
  let T := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in let B := fresh "B" in
  pose proof FSH as T; split_at T idx T2; split_at T2 1%nat T3; clear T T3;
  lazymatch type of T2 with rw_cells _ ?mm _ _ =>
    assert (NAME : acc asegs mm (fr + off) 4)
      by (destruct T2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + off) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
          let c := eval vm_compute in (2147450880 + Z.of_nat idx) in
          replace (shad (fr + off)) with (fr / 8 + c) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
          exact B) end; clear T2.
(* [comment removed for export] *)
Ltac dedup_ro := repeat match goal with H1 : ro_cells asegs ?m ?a ?c, H2 : ro_cells asegs ?m ?a ?c |- _ => clear H2 end.
Ltac drop_ro a := repeat match goal with H : ro_cells asegs _ a _ |- _ => clear H end.
Ltac drop_acc a := repeat match goal with H : acc asegs _ a _ |- _ => clear H end.
Ltac drop_cells a := repeat match goal with H : rw_cells asegs _ a _ |- _ => clear H end.
Section SBV.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Lemma sbv_c16 : sbv_case RT 16.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pixs vs cvs FDO MST -> -> -> -> -> -> PO PD8 PDN W12 H10 ENV RES AL.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct PO as (PXC & (INP & PX0 & PX16 & _) & HOK & DAT & _).
  destruct DAT as [E|((IND & DA0 & DA16 & DAN) & DNE)]; [contradiction|].
  destruct vs as [w h d spp wpl xres yres inf spec pcm data].
  cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in *.
  unfold pix_cells in PXC. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXC.
  unfold rsize in *. cbn [p_wpl p_h] in *. subst d.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixSetBorderVal, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(data, data + 4 * (wpl * h))] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (WPR : 0 < w <= 20000) by (destruct HOK as (_ & HW & _); cbn [p_w] in HW; exact HW).
  assert (HPR : 0 < h <= 20000) by (destruct HOK as (_ & _ & HH & _); cbn [p_h] in HH; exact HH).
  assert (WPLE : wpl = (w * 8 + 31) / 32) by (destruct HOK as (_ & _ & _ & HWPL & _); cbn [p_w p_d p_wpl] in HWPL; exact HWPL).
  assert (WPLB : 0 < wpl <= 5001) by (clear - WPLE WPR; subst wpl; Z.div_mod_to_equations; lia).
  assert (W4 : w <= 4 * wpl) by (clear - WPLE WPR; subst wpl; Z.div_mod_to_equations; lia).
  assert (RSZ : 0 < 4 * (wpl * h) <= 67108864) by (destruct HOK as (_ & _ & _ & _ & HRS); cbn [p_wpl p_h] in HRS; exact HRS).
  hide WPLE. hide WPLB. hide W4. hide RSZ. hide WPR. hide HPR.
  chunk_facts RT AF GP pixs 64. chunk_facts RT AF GP data (4 * (wpl * h)).
  pose proof (live_apart RT AF Σ m data (4 * (wpl * h)) pixs 64 ART0 IND INP DNE) as DPD.
  park_disj.
  carve_frame 208%nat ST.
  clear_acc.
  walk_to AF MST [(usp - 208, usp)] [0x4b7dc].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  eapply cps_seq.
  { eapply (gp_stack_malloc_1 RT GP) with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [auto| auto| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
  fframe_chunk RT AF fr 1%nat 128 pixs 64.
  fframe_chunk RT AF fr 1%nat 128 data (4 * (wpl * h)).
  refresh RT AF. unfold shad, SHB in *. clear_acc. dedup_ro. park_disj.
  walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x95fe0].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. unfold shad, SHB in *.
  dedup_ro. drop_ro 925184. drop_ro 972160.
  local_acc FSH fr 4%nat 32 FR64 ACCW. local_acc FSH fr 6%nat 48 FR64 ACCH. local_acc FSH fr 8%nat 64 FR64 ACCD.
  walk_to AF MST [(usp - 240, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (data, data + 4 * (wpl * h))] [0x96010; 0x961c4; 0x96a90].
  unfold hid in WPLE, WPLB, W4, RSZ, WPR, HPR.
  rewrite !(sx32_small 8) by lia.
  cwalk [0x961c4; 0x96a90].
  rewrite !(sx32_small wpl) by lia.
  replace (Z.b2z (0 <? data)) with 1 by (symmetry; destruct (Z.ltb_spec 0 data); [reflexivity| lia]).
  (* [comment removed for export] *)
  split_at FRM 4%nat FRW. split_at FRW 1%nat FRW2. split_at FRW2 1%nat FRH. split_at FRH 1%nat FRH2.
  rewrite (sx32_small w) in FRW by lia. rewrite (sx32_small h) in FRH by lia.
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT ?S ?mx, WMx : wmono asegs ?mx ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wr_at_transport asegs mx mm data (4 * (wpl * h))
                  (proj1 (af_acc_live RT AF S mx data (4 * (wpl * h)) A ltac:(repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact IND))) WMx) as WRD end.
  apply wr_at_rw_CB in WRD; [| lia]. destruct WRD as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
  assert (HW1 : 2 * wpl <= wpl * h) by (clear - WPLB H10; nia).
  assert (LDB : wpl * h <= 2 ^ 24) by (clear - RSZ; lia).
  eapply evt_cut.
  { eapply (bsb_rows1 2%nat 0) with (data := data) (ld := wpl * h) (pw := fr + 32) (w := w) (wpl := wpl) (n := 2) (bs := dbs); try eassumption.
    all: unfold parked in *.
    all: try assumption.
    all: first [ lia | (rewrite DBL; lia) | (Z.div_mod_to_equations; lia) ]. }
  intros ms' PO. unfold bsb_rows1_exit in PO.
  destruct PO as (x1' & x2' & x3' & x4' & x5' & x6' & x7' & x8' & x9' & m' & bs' & -> & MU' & WM' & MI' & UA' & UAL' & ACC' & PWC').
  lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?mm, MUl : munch _ ?mm m' |- _ =>
    loop_art RT AF S m' lo MUl
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
             split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]]) end.
  clear DBC DBL ACC.
  lazymatch type of MU' with munch _ ?mm m' =>
    loop_transport mm m' MU' ltac:(fun Hx => first [ clear - Hx CKR0 CKS0 CKH0 LOW FCD0 FCS0 FR64 DPD; unfold parked in *; lia | unfold parked in *; lia ]) end.
  clear MU' WM'.
  unfold SHB in *.
  cwalk [0x9664c; 0x96a90].
  rewrite ?(sx32_small w), ?(sx32_small h) by lia. rewrite ?(unsigned_lit w), ?(unsigned_lit h) by lia.
  cwalk [0x9664c; 0x96a90].
  rewrite ?(sx32_small h) by lia. rewrite ?(unsigned_lit h) by lia.
  cwalk [0x9664c; 0x96a90].
  rewrite ?Z.add_0_r.
  rewrite !(bv_swrap_small 32 (w - 8)) by (change (bv_half_modulus 32) with (2^31); lia).
  rewrite !(bv_swrap_small 32 (wpl * 2)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (wpl * 2) with (2 * wpl) by (clear; lia).
  replace (Z.b2z (0 <? data)) with 1 by (symmetry; destruct (Z.ltb_spec 0 data); [reflexivity| lia]).
  assert (HW2 : (h - 8) * wpl <= wpl * h) by (clear - WPLB H10; nia).
  eapply evt_cut.
  { eapply (bsb_rows2 (Z.to_nat (h - 10)) 2) with (data := data) (ld := wpl * h) (pw := fr + 32) (w := w) (wpl := wpl) (n := h - 8) (nl := 4) (rj := w - 8)
                                               (bs := bs'); try eassumption.
    all: unfold parked in *.
    all: try assumption.
    all: first [ lia | (Z.div_mod_to_equations; lia) ]. }
  intros ms' PO. unfold bsb_rows2_exit in PO.
  destruct PO as (y1' & y2' & y3' & y4' & y5' & y6' & y7' & y8' & y9' & y10' & m'' & bs'' & -> & MU'' & WM'' & MI'' & UA'' & UAL'' & ACC'' & PWC'').
  lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?mm, MUl : munch _ ?mm m'' |- _ =>
    loop_art RT AF S m'' lo MUl
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
             split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]]) end.
  clear UA' UAL' ACC' PWC'.
  lazymatch type of MU'' with munch _ ?mm m'' =>
    loop_transport mm m'' MU'' ltac:(fun Hx => first [ clear - Hx CKR0 CKS0 CKH0 LOW FCD0 FCS0 FR64 DPD; unfold parked in *; lia | unfold parked in *; lia ]) end.
  clear MU'' WM''.
  unfold SHB in *.
  cwalk [0x96778; 0x96a90].
  assert (HW3 : 0 <= (h - 8) * wpl <= wpl * h) by (clear - WPLB H10; nia).
  rewrite !(bv_swrap_small 32 (wpl * (h - 8))) by (change (bv_half_modulus 32) with (2^31); clear - HW3 RSZ; lia).
  replace (wpl * (h - 8)) with ((h - 8) * wpl) by (clear; lia).
  replace (Z.b2z (0 <? data)) with 1 by (symmetry; destruct (Z.ltb_spec 0 data); [reflexivity| lia]).
  eapply evt_cut.
  { eapply (bsb_rows3 8%nat (h - 8)) with (data := data) (ld := wpl * h) (pw := fr + 32) (w := w) (ph := fr + 48) (h := h) (wpl := wpl) (bs := bs''); try eassumption.
    all: unfold parked in *.
    all: try assumption.
    all: first [ lia | (Z.div_mod_to_equations; lia) ]. }
  intros ms' PO. unfold bsb_rows3_exit in PO.
  destruct PO as (z1' & z2' & z3' & z4' & z5' & z6' & z7' & z8' & z9' & mm3 & bss3 & -> & MU3 & WM3 & MI3 & UA3 & UAL3 & ACC3 & PWC3 & PHC3).
  lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?mm, MUl : munch _ ?mm mm3 |- _ =>
    loop_art RT AF S mm3 lo MUl
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
             split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]]) end.
  clear UA'' UAL'' ACC'' PWC''.
  lazymatch type of MU3 with munch _ ?mm mm3 =>
    loop_transport mm mm3 MU3 ltac:(fun Hx => first [ clear - Hx CKR0 CKS0 CKH0 LOW FCD0 FCS0 FR64 DPD; unfold parked in *; lia | unfold parked in *; lia ]) end.
  clear MU3 WM3 UA3 UAL3 ACC3 PWC3 PHC3.
  unfold SHB in *.
  clear FRW FRW2 FRH FRH2.
  (* [comment removed for export] *)
  repeat match goal with H : acc asegs _ _ _ |- _ => clear H end.
  repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
  drop_cells pixs.
  cwalk [0x96af4].
  frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x96afc
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
           split; [intros zz Hzz; right; right; left; exists data, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]]])
    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia])
    ltac:(fun Hx => exact (proj1 Hx))
    ltac:(fun fl FLN => repeat match goal with H : rw_cells asegs _ fr _ |- _ => clear H | H : rw_cells asegs _ (fr / 8 + 2147450880) _ |- _ => clear H end).
  walk_to AF MST [(usp - 208, usp)] (@nil Z).
  try (lazymatch goal with ST' : stk asegs _ lo (usp + -208), FR' : rw_cells asegs _ (usp + -208) _ |- _ => release_frame FR' ST' usp end).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. eexists.
  split.
  + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    * lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end.
    * intros a Ha Ho. apply AGF. split; [| exact Ho].
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in Ha end. exact Ha.
  + repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
    repeat split; auto; lia.
Qed.
End SBV.
