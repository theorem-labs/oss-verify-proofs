(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d ARt_3ti ARt_fpo ARt_png ARt_soh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3mp4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3mp4 ANodeA6 ASecTop.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_3ti OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_soh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3mp4.ARt3_lma OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3mp4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecTop.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtSf1m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMTac AMallocI AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalmys AMaly5g ABudget ACover ANodeA7 ANodeA6 ASecComb ASecr83 ASecSrz ASecA1 ATransp ASecImg ASecB1 ASecB2 ASecB3 ASecB6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASecTop.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ACor4x6 ASecG2S ACorg10.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASecTop.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASecBG2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecr83 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecSrz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecA1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecImg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecTop.ASecBG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecG2S OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACorg10 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecTop.ASecr3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecBG2.ASeczyk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma page_round_up_id : forall x, 0 <= x -> x mod 4096 = 0 -> page_round_up_Z x = x.
Proof.
  intros x Hx M. unfold page_round_up_Z, page_size. pose proof (Z_div_mod_eq_full x 4096) as Q. rewrite M, Z.add_0_r in Q.
  set (q := x / 4096) in *. clearbody q. rewrite Q. replace (4096 * q + 4096 - 1) with (q * 4096 + 4095) by lia.
  rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
Qed.

Section SecCoreA8.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Hypothesis RZL : rzlog_stmt.
  Hypothesis GT : get_thread_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis P0 : poison0_stmt.
  Hypothesis DPS : depot_put_stmt depot_repL.
  Hypothesis LPRE : lma_pre_stmt.
  Hypothesis LMID : lma_mid_stmt.
  Hypothesis LTAIL : lma_tail_stmt.
  Hypothesis LESP : lma_esp_stmt.
  Hypothesis LESPOST : lma_espost_stmt.
  Hypothesis MFP : mapfixed_pre_stmt.

  Theorem a8_core_cps1 :
    forall (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) (T1 : TSet),
      alloc_core_pre rac spa tp m md A n canfill stkobj lo hi key ->
      524288 <= n ->
      alloc_core_K1v rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T1 ->
      srealizes (cl_segs LPA) (mkCfg (alloc_entry_ms rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n stkobj canfill) md)
                T1.
  Proof.
    intros until T1. intros PRE NR K1.
    (first [ dand25 PRE as AI MI NRQ NCAP LIM NLV TINY SCRED PCRED CF TPE CLO LOSA SAHI HI47 SPA RAC2 ST SM SOLO SOHI TRC TRB KEYU KR | destruct PRE as (AI & MI & NRQ & NCAP & LIM & NLV & TINY & SCRED & PCRED & CF & TPE & CLO & LOSA & SAHI & HI47 & SPA & RAC2 & ST & SM & SOLO & SOHI & TRC & TRB & KEYU & KR) ]).   (* [comment removed for export] *)
    subst tp. unfold alloc_entry_ms. cbn [cl_segs cl_malloc_pc LPA] in MI, K1 |- *.
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0. pose proof alloc_ceiling_val as CE. pose proof (zr_word spa) as SPR; unfold inr64 in SPR.
    assert (NR30 : kMaxPrimaryUser < n < 2^30 + 1) by (unfold kMaxPrimaryUser in *; rewrite NREQ_CAP_eq in NCAP; lia). pose proof NR30 as NRu. unfold kMaxPrimaryUser in NRu.
    assert (NRA : kMaxPrimaryUser < n < 2^30 + 1) by exact NR30.
    specialize (SCRED (proj1 NR30)).
    (first [ pose proof ((hit_place A m md AI)) as dR_2; dand7 dR_2 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_3; dand4 dR_3 as _ _ SEP_tc _ | pose proof (hit_sep A m md AI) as (_ & _ & SEP_tc & _) ]).
    assert (TSDL : 0x5e7b28 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia).
    assert (TPL : bv_unsigned (cl_tp LPA) = 0x5e7bd8) by (cbn [cl_tp LPA]; rewrite unsigned_lit by lia; reflexivity).
    assert (SO : 0 < stkobj < 2^64) by lia.
    assert (LO1 : alloc_ceiling <= lo /\ lo <= bv_unsigned spa - 1024) by lia.
    assert (SPH : bv_unsigned spa <= 2^47) by lia.
    assert (SMW : mapped (aview_of (pa_hull A) m) lo (hi - lo)).
    { intros i Hi. destruct (Z_lt_le_dec (lo + i) (bv_unsigned spa)) as [L|G].
      - (first [ dand3 ST as _ _ ST3 | destruct ST as (_ & _ & ST3) ]). destruct (ST3 (lo + i) ltac:(lia)) as [X _]. unfold wview, wa in X.
        intros E. apply X. rewrite E. cbn [cl_segs LPA]. rewrite unsigned_lit by lia. rewrite (pa_find_segment_none (lo + i) 1); [reflexivity| lia| right; lia].
      - replace (lo + i) with (bv_unsigned spa + (lo + i - bv_unsigned spa)) by lia. apply SM. lia. }
    pose proof (map_size_page n) as MSA. unfold kPageSize in MSA.
    pose proof (map_size_ge n ltac:(lia)) as MSG. pose proof (map_size_le n ltac:(lia)) as MSL.
    destruct (asI_minv A m md AI) as [HMI HH].
    (* [comment removed for export] *)
    pose proof (sec_a1 rac spa gp (cl_tp LPA) t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                  (aview_of (pa_hull A) m) lo n stkobj canfill pa_tsd (p_ctx (a_pl A)) (p_thr (a_pl A)) 0xaaa50
                  MI ST LO1 SPH NR30 SO RZL GT LPRE
                  (hit_INI A m md AI) (hit_RSS A m md AI) (hit_RZm A m md AI) (hit_MUM A m md AI) (hit_PCo A m md AI) (sec_LC A m md AI)
                  (hit_TC A m md AI) (conj TH1 TH2) TPL TSDL (conj CT1 CT2)) as EV1.
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) pa_wx _ (pa_eager A) _ _ md T1 HMI HH).
    { rewrite restrict_MS. exact EV1. }
    intros msr1 md1 Q1 HI1 SB1 CL1.
    (first [ dex12 Q1 as t0a t1a t2a a6a t3a t4a t5a t6a junk0 scrL scrM m1; dand9 Q1 as -> MU1 WM1 MI1 ST1 FRA FRC FRL FRM | dand21 Q1 as t0a t1a t2a a6a t3a t4a t5a t6a junk0 scrL scrM m1 -> MU1 WM1 MI1 ST1 FRA FRC FRL FRM | destruct Q1 as (t0a & t1a & t2a & a6a & t3a & t4a & t5a & t6a & junk0 & scrL & scrM & m1 & -> & MU1 & WM1 & MI1 & ST1 & FRA & FRC & FRL & FRM) ]).
    rewrite unrestrict_MSsvc. cbn [ms_mem] in CL1.
    assert (HH1 : m_halted md1 = None) by (rewrite (same_but_materialized_halted _ _ SB1); exact HH).
    (* [comment removed for export] *)
    match goal with |- srealizes _ (mkCfg ?ms _) _ => set (ms1 := ms) end.
    assert (A1E : ms_gpr ms1 1 = wz (map_size n)) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (A0E : ms_gpr ms1 0 = wz 0) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (PRU : page_round_up_Z (bv_unsigned (ms_gpr ms1 1)) = map_size n).
    { rewrite A1E, unsigned_lit by lia. apply page_round_up_id; lia. }
    eapply (srz_mmap_rw_nf_ex rsegs ms1 md1 (wz 222) (wz 34) T1 HH1 eq_refl eq_refl).   (* [comment removed for export] *)
    - unfold mmap_rw_args. subst ms1. rewrite !ms_gpr_MSsvc. simp_regs. split; [| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity; exact mmap_modeled_b_plain].
      intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia.
    - cbv zeta. rewrite PRU, A0E. exact (sec_grant_exists A m md md1 n AI SB1 HI1 NR30).
    - (* [comment removed for export] *)
      intros mbw GOK. cbv zeta in GOK. rewrite PRU, A0E in GOK. subst ms1.
      rewrite advance_apply_MSsvc, mkR_set_a0, lit_add_lit. change (mmap_ecall_pc + 4) with ANodeA7.mmap_after_pc.
      rewrite !ms_gpr_MSsvc. simp_regs. rewrite unsigned_lit by lia. rewrite (page_round_up_id (map_size n)) by lia.
      change (apply_unmaps ?mm []) with mm. cbn [apply_writes].
      (first [ pose proof ((sec_nch A m md AI)) as dR_6; dand4 dR_6 as NC1 NC2 NC3 NC4 | pose proof (sec_nch A m md AI) as (NC1 & NC2 & NC3 & NC4) ]).
      destruct NC3 as [NRES0|NRES].
      + (* [comment removed for export] *)
        apply (sec_grant2_a8_ok rac spa gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A n lo hi stkobj canfill key T1
                 AI NRA SPA CF CLO LOSA (conj SAHI HI47) SMW (conj SOLO SOHI) TRC TRB KEYU KR LIM NLV SCRED
                 LMID LTAIL TSS PS P0 DPS LESP MFP LESPOST K1 m1 md1 t0a t1a t2a a6a t3a t4a t5a t6a junk0 scrL scrM
                 MU1 WM1 MI1 ST1 HI1 SB1 CL1 FRA FRC FRL FRM mbw GOK ltac:(lia)).
      + (* [comment removed for export] *)
        apply (sec_grant1_a8 rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n lo hi stkobj canfill key T1
                 AI NRA SPA CF CLO LOSA (conj SAHI HI47) SMW (conj SOLO SOHI) TRC TRB KEYU KR LIM NLV SCRED
                 LMID LTAIL TSS PS P0 DPS K1 m1 md1 t0a t1a t2a a6a t3a t4a t5a t6a junk0 scrL scrM
                 MU1 WM1 MI1 ST1 HI1 SB1 CL1 FRA FRC FRL FRM mbw GOK ltac:(unfold kChunksBlockCount in *; lia)).
  Qed.
End SecCoreA8.


Section SecTopA8.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Theorem a8_core_cps1_ok : a8_core_cps1_stmt.
  Proof.
    unfold a8_core_cps1_stmt.
    exact (a8_core_cps1 rzlog_ok get_thread_ok thread_stats_ok poison_ok poison0_ok depot_put_ok
             lma_pre_ok lma_mid_ok lma_tail_ok lma_esp_ok lma_espost_ok mapfixed_pre_ok).
  Qed.
End SecTopA8.
