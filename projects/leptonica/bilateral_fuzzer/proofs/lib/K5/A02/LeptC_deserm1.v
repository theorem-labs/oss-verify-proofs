(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit LeptL_kit Lept_chain Lept_leaf LeptC_leaf Lept_objkit Lept_deserkit LeptC_deser2_defs Lept_deser_defs LeptC_deser0_defs LeptC_deserm1_defs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma swrap32_range : forall z, - 2^31 <= bv_swrap 32 z < 2^31.
Proof. intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Lemma range_check32 : forall (x : word) K, 0 < K < 2^31 ->
  2^64 - (K + 1) < bv_swrap 32 (bv_unsigned (sx32 x) + (2^64 - (K + 1))) mod 2^64 ->
  1 <= bv_swrap 32 (bv_unsigned x) <= K.
Proof.
  intros x K HK H. unfold sx32 in H. rewrite Z_to_bv_unsigned in H.
  pose proof (swrap32_range (bv_unsigned x)) as R. set (w := bv_swrap 32 (bv_unsigned x)) in *.
  unfold bv_wrap, bv_modulus in H. change (2 ^ Z.of_N 64) with 18446744073709551616 in H.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H. change (2 ^ Z.of_N 32) with 4294967296 in H. change (4294967296 / 2) with 2147483648 in H.
  change (2^64) with 18446744073709551616 in *. change (2^31) with 2147483648 in *.
  clearbody w. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac d0_epi_null EPI AGF LVP :=
  eapply EPI with (pixr := 0) (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (cv := mkCmapv 0 0 0 0);
  lazymatch goal with
  | |- ART _ _ _ => eassumption
  | |- mem_inv _ _ => assumption
  | |- stk _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- wr_at _ _ _ _ => assumption
  | |- LIBH _ => assumption
  | |- io_ssp _ => assumption
  | |- agree_on _ _ _ => exact AGF
  | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
  | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
  | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
  | |- forall e, In e _ -> In e _ => solve [live_sub_tac]
  | |- _ \/ _ => left; reflexivity
  | |- 0 = 0 -> _ => intros _; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
  | |- 0 <> 0 -> _ => let HH := fresh "HH" in intros HH; contradiction
  | |- forall p k, In (p, k) _ -> 0 < k => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact LVP
  | |- Z.of_nat _ <= _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; lia
  end.
Ltac d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo A W :=
  at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx);
  (let RE := fresh "RE" in pose proof RERR as RE; unfold returnError_cps in RE;
   eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |]);
  after_call RT AF;
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]);
  ds_refresh RT AF GP;
  ds_walk AF MST W;
  ds_to_epi RT AF AGF PFS NFA A;
  d0_epi_null EPI AGF LVP.

Section DESERM1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (QF : config -> Prop) (fr : Z) (dp n : Z) (ras : list Z) (rdes : Z).

Theorem deser_cutm1_ok_0 :
  deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes ->
  deser_epi_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut0_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ->
  deser_cutm1_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP RERR.
  intros (FDO & MST & ART0 & LOW & LOR & STa & SPT & SPA & SPB & FRB & LVB & CRB & NR & DP0 & DP8 & OWN & UCTX & RA4096 & TRS) EPI CUT0.
  unfold deser_cutm1_stmt_0.
  intros Sc mc j0 f0 f1 f2 vx px r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r21 r22 r24 r26 r28 r29 r30 r31 F' fc'
    ARTc MIc STc FR FRM FSH LH SSP AGF FRS ESP0 ECR LVE LVP.
  unfold deser_epi_stmt_0 in EPI. unfold deser_cut0_stmt_0 in CUT0.
  set (PF := deser_PF RT Σ usp) in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  unfold entry_st.
  pose proof (af_frames_range RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR0 & FRHI & _ & _).
  pose proof (af_frames_align RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR64 & FRSEG).
  pose proof (af_frames_hi RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as FRSH.
  change (fs_size 1) with 128 in FRHI, FRSH. rewrite ESP0 in FRHI. unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG.
  assert (NFA : forall a, PF a -> (a < fr \/ fr + 128 <= a) /\ (a < shad fr \/ shad (fr + 128) <= a)).
  { intros a Ha. apply (new_frame_apart RT AF Sc mc fr 1%nat (rt_frames RT Σ) (rt_live RT Σ) usp a ARTc FRS);
      [intros e He; rewrite LVE; exact He| rewrite ESP0; lia| rewrite ESP0; unfold STACK_WIN; lia| exact Ha]. }
  assert (FRTOP : fr + 128 <= 140737488355328) by (clear - FRHI SP0R; lia).
  unfold deser_fshadow in FSH.
  pose proof (proj2 FRM) as WFR. cbn [cells_size csize Nat.add] in WFR. change (Z.of_nat 120) with 120 in WFR.
  pose proof (proj2 FSH) as WFS. cbn [cells_size csize Nat.add] in WFS. change (Z.of_nat 16) with 16 in WFS.
  assert (NLO : 28 <= n) by (clear - NR; lia). assert (NHI : n < 2^26) by (clear - NR; lia).
  destruct OWN as (dpp & dpk & DIN0 & DLO & DHI).
  assert (DIN : In (dpp, dpk) (rt_live RT Sc)) by (rewrite LVE; exact DIN0).
  assert (DPP0 : 0 < dpp) by exact (proj1 (af_live_range RT AF Sc mc dpp dpk ARTc DIN)).
  chunk_facts RT AF GP dpp dpk. fframe_chunk RT AF fr 1%nat 128 dpp dpk.
  pose proof (proj1 (af_acc_live RT AF Sc mc dpp dpk ARTc DIN)) as WRDP.
  pose proof (wr_at_sub mc dpp dpk dp 24 WRDP ltac:(clear - DLO; lia) ltac:(clear - DHI NLO; lia) ltac:(clear; lia)) as WRH.
  apply wr_at_rw_CB in WRH; [| clear; lia]. destruct WRH as (hbs & HBC). change (Z.to_nat 24) with 24%nat in HBC.
  destruct (spix_hdr_cells mc dp hbs HBC) as (b0 & b1 & b2 & b3 & w1 & w2 & w3 & w4 & w5 & HDC). clear HBC.
  ds_refresh RT AF GP.
  Time ds_walk AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
  brfork HW.
  2:{ 
    ds_awalk.
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -192) [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
  pose proof (range_check32 w1 1000000 ltac:(clear; lia) HW) as WR. clear HW.
  set (w := bv_swrap 32 (bv_unsigned w1)) in *. change (sx32 w1) with (Z_to_bv 64 w) in *.
  assert (WLO : 1 <= w) by (clear - WR; lia). assert (WHI : w <= 1000000) by (clear - WR; lia).
  ds_awalk.
  brfork HH.
  2:{ 
    ds_awalk.
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -192) [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
  pose proof (range_check32 w2 1000000 ltac:(clear; lia) HH) as HR. clear HH.
  set (h := bv_swrap 32 (bv_unsigned w2)) in *. change (sx32 w2) with (Z_to_bv 64 h) in *.
  assert (HLO : 1 <= h) by (clear - HR; lia). assert (HHI : h <= 1000000) by (clear - HR; lia).
  ds_awalk.
  brfork HA.
  2:{ 
    ds_awalk.
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -192) [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
  ds_awalk.
  set (nc := bv_unsigned w5 mod 2^32) in *. change (zx32 w5) with (Z_to_bv 64 nc) in *.
  assert (NCLO : 0 <= nc) by (unfold nc; apply Z.mod_pos_bound; clear; lia).
  assert (NCTOP : nc < 2^32) by (unfold nc; apply Z.mod_pos_bound; clear; lia).
  brfork HN1.
  1:{ 
    ds_awalk.
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -192) [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
  ds_awalk.
  brfork HN2.
  1:{ 
    ds_awalk.
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -192) [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
  pose proof (swrap32_range (bv_unsigned w3)) as DR.
  set (d := bv_swrap 32 (bv_unsigned w3)) in *. change (sx32 w3) with (Z_to_bv 64 d) in *.
  assert (NSZ : 4 * nc + 28 <= n) by (clear - HN2; Z.div_mod_to_equations; lia).
  cps_stop. art_now RT AF ltac:(ds_ivt).
  lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => ds_pft PFS NFA Hx) end.
  to_entry.
  eapply CUT0 with (nc := nc) (w := w) (h := h) (d := d).
  all: lazymatch goal with
       | |- ART _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- stk _ _ _ _ => eassumption
       | |- rw_cells _ _ (usp + -192) _ => exact FR
       | |- rw_cells _ _ fr _ => exact FRM
       | |- rw_cells _ _ _ deser_fshadow => unfold deser_fshadow; exact FSH
       | |- LIBH _ => assumption
       | |- io_ssp _ => assumption
       | |- agree_on _ _ _ => exact AGF
       | |- rt_frames _ _ = _ => exact FRS
       | |- rt_sp0 _ _ = _ => exact ESP0
       | |- _ <= rt_credit _ _ => exact ECR
       | |- rt_live _ _ = _ => exact LVE
       | |- forall p k, In (p, k) _ -> 0 < k => exact LVP
       | |- _ <= _ <= _ => first [clear - NCLO HN1; lia | exact WR | exact HR]
       | |- _ <= _ < _ => exact DR
       | |- _ <= _ => exact NSZ
       | |- ?g => idtac "LEFTOVER:" g
       end.
Qed.
(* [comment removed for export] *)
Theorem deser_cutm1_ok_16 :
  deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes ->
  deser_epi_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut0_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ->
  deser_cutm1_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP RERR.
  intros (FDO & MST & ART0 & LOW & LOR & STa & SPT & SPA & SPB & FRB & LVB & CRB & NR & DP0 & DP8 & OWN & UCTX & RA4096 & TRS) EPI CUT0.
  unfold deser_cutm1_stmt_16.
  intros Sc mc j0 jp f0 f1 f2 vx px r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r21 r22 r24 r26 r28 r29 r30 r31 F' fc'
    ARTc MIc STc FR FRM FSH LH SSP AGF FRS ESP0 ECR LVE LVP.
  unfold deser_epi_stmt_16 in EPI. unfold deser_cut0_stmt_16 in CUT0.
  set (PF := deser_PF RT Σ usp) in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  unfold entry_st.
  pose proof (af_frames_range RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR0 & FRHI & _ & _).
  pose proof (af_frames_align RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR64 & FRSEG).
  pose proof (af_frames_hi RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as FRSH.
  change (fs_size 1) with 128 in FRHI, FRSH. rewrite ESP0 in FRHI. unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG.
  assert (NFA : forall a, PF a -> (a < fr \/ fr + 128 <= a) /\ (a < shad fr \/ shad (fr + 128) <= a)).
  { intros a Ha. apply (new_frame_apart RT AF Sc mc fr 1%nat (rt_frames RT Σ) (rt_live RT Σ) usp a ARTc FRS);
      [intros e He; rewrite LVE; exact He| rewrite ESP0; lia| rewrite ESP0; unfold STACK_WIN; lia| exact Ha]. }
  assert (FRTOP : fr + 128 <= 140737488355328) by (clear - FRHI SP0R; lia).
  unfold deser_fshadow in FSH.
  pose proof (proj2 FRM) as WFR. cbn [cells_size csize Nat.add] in WFR. change (Z.of_nat 120) with 120 in WFR.
  pose proof (proj2 FSH) as WFS. cbn [cells_size csize Nat.add] in WFS. change (Z.of_nat 16) with 16 in WFS.
  assert (NLO : 28 <= n) by (clear - NR; lia). assert (NHI : n < 2^26) by (clear - NR; lia).
  destruct OWN as (dpp & dpk & DIN0 & DLO & DHI).
  assert (DIN : In (dpp, dpk) (rt_live RT Sc)) by (rewrite LVE; exact DIN0).
  assert (DPP0 : 0 < dpp) by exact (proj1 (af_live_range RT AF Sc mc dpp dpk ARTc DIN)).
  chunk_facts RT AF GP dpp dpk. fframe_chunk RT AF fr 1%nat 128 dpp dpk.
  pose proof (proj1 (af_acc_live RT AF Sc mc dpp dpk ARTc DIN)) as WRDP.
  pose proof (wr_at_sub mc dpp dpk dp 24 WRDP ltac:(clear - DLO; lia) ltac:(clear - DHI NLO; lia) ltac:(clear; lia)) as WRH.
  apply wr_at_rw_CB in WRH; [| clear; lia]. destruct WRH as (hbs & HBC). change (Z.to_nat 24) with 24%nat in HBC.
  destruct (spix_hdr_cells mc dp hbs HBC) as (b0 & b1 & b2 & b3 & w1 & w2 & w3 & w4 & w5 & HDC). clear HBC.
  ds_refresh RT AF GP.
  Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
  brfork HW.
  2:{ 
    ds_awalk.
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -208) [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
  pose proof (range_check32 w1 1000000 ltac:(clear; lia) HW) as WR. clear HW.
  set (w := bv_swrap 32 (bv_unsigned w1)) in *. change (sx32 w1) with (Z_to_bv 64 w) in *.
  assert (WLO : 1 <= w) by (clear - WR; lia). assert (WHI : w <= 1000000) by (clear - WR; lia).
  ds_awalk.
  brfork HH.
  2:{ 
    ds_awalk.
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -208) [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
  pose proof (range_check32 w2 1000000 ltac:(clear; lia) HH) as HR. clear HH.
  set (h := bv_swrap 32 (bv_unsigned w2)) in *. change (sx32 w2) with (Z_to_bv 64 h) in *.
  assert (HLO : 1 <= h) by (clear - HR; lia). assert (HHI : h <= 1000000) by (clear - HR; lia).
  ds_awalk.
  brfork HA.
  2:{ 
    ds_awalk.
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -208) [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
  ds_awalk.
  set (nc := bv_unsigned w5 mod 2^32) in *. change (zx32 w5) with (Z_to_bv 64 nc) in *.
  assert (NCLO : 0 <= nc) by (unfold nc; apply Z.mod_pos_bound; clear; lia).
  assert (NCTOP : nc < 2^32) by (unfold nc; apply Z.mod_pos_bound; clear; lia).
  brfork HN1.
  1:{ 
    ds_awalk.
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -208) [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
  ds_awalk.
  brfork HN2.
  1:{ 
    ds_awalk.
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -208) [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
  pose proof (swrap32_range (bv_unsigned w3)) as DR.
  set (d := bv_swrap 32 (bv_unsigned w3)) in *. change (sx32 w3) with (Z_to_bv 64 d) in *.
  assert (NSZ : 4 * nc + 28 <= n) by (clear - HN2; Z.div_mod_to_equations; lia).
  cps_stop. art_now RT AF ltac:(ds_ivt).
  lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => ds_pft PFS NFA Hx) end.
  to_entry.
  eapply CUT0 with (nc := nc) (w := w) (h := h) (d := d).
  all: lazymatch goal with
       | |- ART _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- stk _ _ _ _ => eassumption
       | |- rw_cells _ _ (usp + -208) _ => exact FR
       | |- rw_cells _ _ fr _ => exact FRM
       | |- rw_cells _ _ _ deser_fshadow => unfold deser_fshadow; exact FSH
       | |- LIBH _ => assumption
       | |- io_ssp _ => assumption
       | |- agree_on _ _ _ => exact AGF
       | |- rt_frames _ _ = _ => exact FRS
       | |- rt_sp0 _ _ = _ => exact ESP0
       | |- _ <= rt_credit _ _ => exact ECR
       | |- rt_live _ _ = _ => exact LVE
       | |- forall p k, In (p, k) _ -> 0 < k => exact LVP
       | |- _ <= _ <= _ => first [clear - NCLO HN1; lia | exact WR | exact HR]
       | |- _ <= _ < _ => exact DR
       | |- _ <= _ => exact NSZ
       | |- ?g => idtac "LEFTOVER:" g
       end.
Qed.
End DESERM1.
