(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readHead.v, with its module paths and module names changed; 334 of its 373 lines of code are new or changed and 319 lines of the source are left out. *)
(* text_of on image A: THE MALLOC CUT (lib/A/Prog/text_ofKit.v to_gi_mal, wrapper_malloc's entry, ra = 0x87ff0) to
   THE BLOCK CUT (lib/A/Prog/text_ofMalB.v to_gi_230), and so the copy arm's obligation `to_mal : to_mal_obl`:
   - the call: lib/A/Prog/LinkWalkAllocW.v aj_gx_malloc_dw over the wild rule amalloc04_rule_dw (k + 1 bytes); its
     frame chain from s0 = o (text_ofMalKit.v to_chain: the two words under o at the call, the one at o - 16 at most
     o) and its trace the wild prefix [pc_malloc_ra0; 0x87ff0] (to_admits, text_of_traces, LedPre);
   - the block cut's facts: the kept clause of the call composed with malloc's (akept_trans), the copy's source by
     the read set (akept_akb_gx) and LinkWalkShadow.v shadow_transport, the cursor by the write set (ajw_akb), *own's
     writability and shadow (tm_wr_move, shadow_transport).
   Section hypotheses: LAWS, TL, LV, MTL, TB, HSEGS (the image instance and the meter); MALLOCW (amalloc04_rule_dw,
   lib/A/Rt/LinkMallocDepotWA.v PcapB_AMALLOC4_DW); AMCPY (checked_memcpy, lib/A/AE2q.v asan_memcpy_realizes); TO_HO
   (the shadow word of *own visible at the call: text_of_c.v's Pre does not state it yet, routed to its contract owner).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YG0p YG08 YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite LinkWalkSide LinkWalkAlloc text_buf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepot.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkNoWrite LinkWalkLeaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c text_ofDefs text_ofKit text_ofMalKit LinkWalkShadow LinkWalkCall text_ofMalT text_ofMalB PaJournalFs LinkWalkAllocW.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepotW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis MTL : ameter_laws MT.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.
Hypothesis MALLOCW : amalloc04_rule_dw (SK := SK) SEGS B MT.
Hypothesis AMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).
Hypothesis TO_HO : forall cx, to_pre SK B MT CTX cx -> shadow_hull_vis (ard SEGS (to_m0 cx)) (to_o cx) 8.

(* lia without the context's universally quantified facts (their premises cost the zify step most of its time) *)
Ltac lz := repeat match goal with
  | H : ?T |- _ => lazymatch T with
                   | ~ _ => fail
                   | forall _, _ => clear H
                   end
  end; lia.

Theorem to_mal : to_mal_obl SK B MT CTX.
Proof.
  unfold to_mal_obl, to_from. intros cx ms3 md3 HPX HGI.
  pose proof HPX as (HPRE & HRD & Hlive & Hmo & Hch & Hctx & Hled & HP).
  pose proof HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
  destruct (to_pre_happ SK B MT CTX cx HPX) as (AMp & AMo).
  pose proof (TO_HO cx HPX) as HHo.
  pose proof (to_pre_P SK B MT CTX cx HPX) as HP0.
  destruct HP0 as (c0' & c1' & inp' & Hc0' & Hc1' & Hc0r' & Hc1r' & HBP0 & Hp8 & HRAp & HAMp & HAFp & HBO0 & HRAo & HAMo
    & _ & HAFo & HAPop & HAPerr & Hinp' & Hlen' & HRAin & HIN & HUW & HUW16 & HRAT & HAPT & HAOT & HENT & HTR).
  unfold to_gi_mal in HGI. cbv zeta in HGI.
  destruct HGI as (c0 & c1 & inp & adv & n & k & Hpc & R1 & HCORE & HINP & Hadv & Hadvn & Hkn & Hn319 & HNZ & R10 & R9
    & R18 & R21 & Pp & Pp8).
  unfold to_core in HCORE. cbv zeta in HCORE.
  destruct HCORE as (Hrv & Hsv & Hrom & Hfr & Hfc & HJ3 & Hfd & Hfs & R2 & R8 & R20 & RUT & RSV & HUN & HPR & HPW & HBP
    & HOW & HBO).
  pose proof HINP as (Ic0 & Ic1 & Ic0r & Ic1r & Iinp & Ilen).
  assert (E0 : c0' = c0) by exact (tm_au64_det SEGS (to_m0 cx) _ c0' c0 Hc0' Ic0 Hc0r' Ic0r).
  assert (E1 : c1' = c1) by exact (tm_au64_det SEGS (to_m0 cx) _ c1' c1 Hc1' Ic1 Hc1r' Ic1r).
  subst c0'. rewrite E1 in *. clear E1.
  destruct (HIN ltac:(lz)) as (HHin & HAMin & HAFin & HAPinp & HAPino & Hc01o).
  change (aarg (to_regs cx) 0) with (to_p cx) in *. change (aarg (to_regs cx) 1) with (to_o cx) in *.
  change (spZ (to_regs cx)) with (to_sp cx) in *.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as (HB0' & HB1' & HB2').
  pose proof pa_segs_low as Hsegs.
  pose proof (to_win SK B MT CTX cx HPX) as (Wce & W47 & W16 & Wlo & Whi).
  pose proof (ajournal_gx_row SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hrow & _ & _ & _).
  set (regs := to_regs cx) in *. set (W := to_W cx) in *. set (R := ms_regs ms3) in *. set (sp := to_sp cx) in *.
  set (p := to_p cx) in *. set (o := to_o cx) in *.
  assert (HKv : TEXT_OF_AK = 16448) by reflexivity.
  assert (HAS : ASTACK = 16384) by reflexivity.
  assert (VB : BASE = 0x821cc) by exact (lv_text LV).
  assert (Ho0 : 0 <= o < 2 ^ 64) by (unfold o, to_o, aarg, argZ; apply u64_range).
  assert (Hp0 : 0 <= p < 2 ^ 64) by (unfold p, to_p, aarg, argZ; apply u64_range).
  assert (Ho64 : o + 8 <= 2 ^ 47) by (unfold amem_range in AMo; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lz).
  assert (Hp64 : p + 16 <= 2 ^ 47) by (unfold amem_range in AMp; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lz).
  assert (Hc64 : c0 + c1 <= 2 ^ 47) by (unfold amem_range in HAMin; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lz).
  assert (HoS : o + 8 <= sp - TEXT_OF_AK \/ sp + 16 <= o)
    by (revert HAFo; unfold apart_frame, o, sp, to_o, to_sp, regs; clear; intros; lz).
  assert (HpS : p + 16 <= sp - TEXT_OF_AK \/ sp <= p)
    by (revert HAFp; unfold apart_frame, p, sp, to_p, to_sp, regs; clear; intros; lz).
  assert (HcS : c0 + c1 <= sp - TEXT_OF_AK \/ sp <= c0)
    by (revert HAFin; unfold apart_frame, sp, to_sp, regs; clear; intros; lz).
  assert (Hcp : c0 + c1 <= p \/ p + 16 <= c0) by (revert HAPinp; unfold apart, p, to_p, regs; clear; intros; lz).
  assert (Hco : c0 + c1 <= o \/ o + 8 <= c0) by (revert HAPino; unfold apart, o, to_o, regs; clear; intros; lz).
  assert (HopA : o + 8 <= p \/ p + 16 <= o) by (revert HAPop; unfold apart, o, p, to_o, to_p, regs; clear; intros; lz).
  assert (Herrp : as_errno B + 4 <= p \/ p + 16 <= as_errno B)
    by (revert HAPerr; unfold apart, p, to_p, regs; clear; intros; lz).
  assert (Hco1 : c0 + c1 <= o) by (revert Hc01o; unfold o, to_o, regs; clear; intros; lz).
  assert (Hsp' : spZ R = sp - 64) by (unfold spZ; rewrite R2; unfold TO_FRAME; apply unsigned_lit_small; lz).
  assert (Hra : raZ R = TEXT_OF_MALLOC_RA).
  { unfold raZ. rewrite R1. rewrite unsigned_lit_small by (rewrite VB; unfold TO_MAL_RA, AF_text_of; lz).
    rewrite VB. reflexivity. }
  assert (Hs0 : s0Z R = o) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; lz).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  (* a byte of the cursor, *own or the input, off the window, as a number *)
  assert (HoE : forall i, 0 <= i < 8 -> to_E cx (o + i)).
  { intros i Hi. exists (o, o + 8). split; [right; left; reflexivity | cbn [fst snd]; lz]. }
  assert (HpE : forall i, 0 <= i < 16 -> to_E cx (p + i)).
  { intros i Hi. exists (p, p + 16). split; [left; reflexivity | cbn [fst snd]; lz]. }
  assert (HnE : forall a, ~ (p <= a < p + 16) -> ~ (o <= a < o + 8) -> ~ to_E cx a).
  { intros a H1 H2 (r & Hin & Hr). unfold to_wr, text_of_awr in Hin. cbn [In] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr; [apply H1 | apply H2]; exact Hr. }
  (* ---- the frame chain of the call (s0 = o) ---- *)
  set (rd3 := aview SEGS (w_H W) (ms_mem ms3)).
  assert (WORD : forall q, q mod 8 = 0 -> o - 16 <= q -> q + 8 <= o -> sp + 16 <= o ->
            exists v, rdword rd3 q = Some v /\ 0 <= v < 2 ^ 64 /\
              (q = p -> v = c0 + adv + n) /\ (q = p + 8 -> v = c1 - adv - n) /\
              (q + 8 <= p \/ p + 16 <= q -> au64_at SEGS (to_m0 cx) q v)).
  { intros q Hq8 Hq1 Hq2 Hos.
    assert (Hp8' : p mod 8 = 0) by exact Hp8.
    assert (Hcases : q = p \/ q = p + 8 \/ q + 8 <= p \/ p + 16 <= q) by lz.
    destruct Hcases as [-> | [-> | Hd]].
    - exists (c0 + adv + n). split; [exact (rdword_of_val_mem SEGS (w_H W) (ms_mem ms3) p _ Pp ltac:(lz))|].
      split; [lz|]. split; [reflexivity|]. split; [lz|]. lz.
    - exists (c1 - adv - n). split; [exact (rdword_of_val_mem SEGS (w_H W) (ms_mem ms3) (p + 8) _ Pp8 ltac:(lz))|].
      split; [lz|]. split; [lz|]. split; [reflexivity|]. lz.
    - assert (Hq : forall i, 0 <= i < 8 -> rd3 (q + i) = aview SEGS (w_H W) (to_memc cx) (q + i)).
      { intros i Hi. apply HUN; [lz | lz | apply HnE; lz]. }
      assert (Hsome : forall i, 0 <= i < 8 -> aview SEGS (w_H W) (to_memc cx) (q + i) <> None).
      { intros i Hi. pose proof (HUW (q + i - (o - 16)) ltac:(lz)) as H.
        replace (o - 16 + (q + i - (o - 16))) with (q + i) in H by lz.
        exact H. }
      assert (Hw : exists v, rdword (aview SEGS (w_H W) (to_memc cx)) q = Some v).
      { unfold rdword.
        pose proof (Hsome 0 ltac:(lz)) as S0. pose proof (Hsome 1 ltac:(lz)) as S1.
        pose proof (Hsome 2 ltac:(lz)) as S2. pose proof (Hsome 3 ltac:(lz)) as S3.
        pose proof (Hsome 4 ltac:(lz)) as S4. pose proof (Hsome 5 ltac:(lz)) as S5.
        pose proof (Hsome 6 ltac:(lz)) as S6. pose proof (Hsome 7 ltac:(lz)) as S7.
        rewrite Z.add_0_r in S0.
        destruct (aview SEGS (w_H W) (to_memc cx) q); [|congruence].
        destruct (aview SEGS (w_H W) (to_memc cx) (q + 1)); [|congruence].
        destruct (aview SEGS (w_H W) (to_memc cx) (q + 2)); [|congruence].
        destruct (aview SEGS (w_H W) (to_memc cx) (q + 3)); [|congruence].
        destruct (aview SEGS (w_H W) (to_memc cx) (q + 4)); [|congruence].
        destruct (aview SEGS (w_H W) (to_memc cx) (q + 5)); [|congruence].
        destruct (aview SEGS (w_H W) (to_memc cx) (q + 6)); [|congruence].
        destruct (aview SEGS (w_H W) (to_memc cx) (q + 7)); [|congruence].
        eexists. reflexivity. }
      destruct Hw as (v & Hv).
      assert (Hvr : 0 <= v < 2 ^ 64).
      { exact (tm_rdword_rng SEGS _ _ _ _ Hv). }
      exists v. split; [rewrite <- Hv; apply rdword_ext; intros i Hi; exact (Hq i Hi)|].
      split; [exact Hvr|]. split; [intros E; lz|]. split; [intros E; lz|].
      intros _. exact (val_mem_of_rdword SEGS (w_H W) (to_memc cx) q v Hv). }
  assert (CHN : exists ch, chain_pre (to_lyc cx) rd3 R ch).
  { apply (to_chain (to_lyc cx) rd3 R o ltac:(rewrite Hra; unfold TEXT_OF_MALLOC_RA; lz) Hs0).
    intros Ho8 Hlt Htop. rewrite Hsp' in Hlt.
    assert (Hos : sp + 16 <= o) by lz.
    split; [rewrite Hsp'; lz|].
    destruct (WORD (o - 8) ltac:(lz) ltac:(lz) ltac:(lz) Hos) as (v8 & H8 & R8' & _ & _ & _).
    destruct (WORD (o - 16) ltac:(lz) ltac:(lz) ltac:(lz) Hos) as (v16 & H16 & R16 & Ep & Ep8 & Ed).
    exists v8, v16. split; [exact H8|]. split; [exact H16|]. split; [lz|].
    assert (Hc : o - 16 = p \/ o - 16 = p + 8 \/ o - 16 + 8 <= p \/ p + 16 <= o - 16) by lz.
    destruct Hc as [Hc | [Hc | Hc]].
    - rewrite (Ep Hc). lz.
    - rewrite (Ep8 Hc). lz.
    - exact (HUW16 v16 (Ed Hc) R16). }
  destruct CHN as (ch & Hchain).
  (* ---- the call of wrapper_malloc(k + 1) ---- *)
  assert (Hms3 : ms3 = mkst R (Z_to_bv 64 (pc_wrap_malloc (as_code B))) (ms_mem ms3) (seg_rom SEGS)).
  { rewrite (tm_ms_eta ms3 Hfr Hsv Hrv Hfc) at 1. rewrite Hpc, Hrom, <- (pal_malloc B TL). reflexivity. }
  rewrite Hms3.
  eapply SRr_bind.
  { eapply (aj_gx_malloc_dw SK SEGS B MT LAWS pa_segs_low MALLOCW (to_G cx) (to_XO cx) (to_OUT cx) W R (ms_mem ms3)
      (to_STK cx) (to_sp0 cx) (to_FP cx) (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx)
      (to_lyc cx) (to_Sc cx) md3 (to_k cx) (k + 1) _ ch HJ3).
    - exact R10.
    - unfold MALLOC_MAX. lz.
    - unfold TEXT_OF_LIVE in Hlive. lz.
    - rewrite Hsp'. replace (sp - 64) with (sp + (-4) * 16) by lz. rewrite Z_mod_plus_full. exact W16.
    - rewrite Hsp', HAS. lz.
    - rewrite Hsp'. lz.
    - rewrite Hsp'. lz.
    - exact (eq_trans (RUT 3 ltac:(unfold TO_UNTOUCHED; cbn; tauto)) Hgp).
    - exact (eq_trans (RUT 4 ltac:(unfold TO_UNTOUCHED; cbn; tauto)) Htp).
    - exact R1.
    - unfold TO_MAL_RA. apply ret_ok_codeptr_v; [unfold AF_text_of; lz | reflexivity].
    - lz.
    - exact Hchain.
    - unfold call_trace0. apply (to_admits _ _ (raZ R) (spZ R) (s0Z R) ch (to_Sc cx)).
      + rewrite Hra. exact HTR.
      + pose proof (pal_rt_below B TL) as (_ & Hlo). rewrite Hra. rewrite VB in Hlo.
        unfold TEXT_OF_MALLOC_RA. lz.
      + exact Hled.
    - apply (mo_ok_le MT MTL _ _ (mo_malloc MT TEXT_OF_LIVE)); [exact Hmo|].
      apply (mo_malloc_mono MT MTL). unfold TEXT_OF_LIVE. lz. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ4 & HP4 & Hres & Hfr2 & H4096 & Hbl & HKC
    & MLE & HD & Hfd2 & Hfs2).
  pose proof HKC as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6).
  rewrite Hsp', HAS in KC1, KC5, KC6.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
  assert (Hfa : forall c q, frame_addr ly2 c q = frame_addr (to_lyc cx) c q).
  { intros c q.
    rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ4)).
    rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ)).
    reflexivity. }
  assert (HinP : In (res, k + 1) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res (k + 1) HAR4 HinP) as (_ & _ & Hbc & Hiapp & _ & _ & _).
  assert (Hrq : req_size (k + 1) = k + 1)
    by (unfold req_size; replace (k + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lz); reflexivity).
  rewrite Hrq in Hbc, Hiapp. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hiapp.
  assert (Hbl2 : forall b m0, In (b, m0) (ablocks B (to_lyc cx) (to_Sc cx)) -> In (b, m0) (ablocks B ly2 S2))
    by (intros b m0 Hb; rewrite Hbl; apply in_or_app; left; exact Hb).
  pose proof HJ4 as R4. apply (aj_stk_row_eq SK SEGS B) in R4.
  pose proof HJ as Rc. apply (aj_stk_row_eq SK SEGS B) in Rc.
  assert (Elo : ly_stk_lo ly2 = ly_stk_lo (to_lyc cx)) by (rewrite (proj1 R4), (proj1 Rc); reflexivity).
  assert (Ehi : ly_stk_hi ly2 = ly_stk_hi (to_lyc cx)) by (rewrite (proj2 R4), (proj2 Rc); reflexivity).
  set (FR := fun a => res <= a < res + req_size (k + 1)).
  set (EF := fun a => to_E cx a \/ res <= a < res + req_size (k + 1)).
  (* the kept clauses: the entry to the call, the call *)
  assert (KA : akept SEGS B (to_lyc cx) (to_Sc cx) W (to_memc cx) W (ms_mem ms3) (sp - TEXT_OF_AK) sp (to_E cx)).
  { apply (akept_run SEGS B LAWS pa_segs_low (to_lyc cx) (to_Sc cx) W (to_memc cx) (to_mdc cx) W (ms_mem ms3)
      (sp - TEXT_OF_AK) sp (to_E cx) HARc); [lz | lz | | | ].
    - intros a Ha Hw HE. exact (HUN a Ha Hw HE).
    - exact HPR.
    - exact HPW. }
  assert (KB : akept SEGS B (to_lyc cx) (to_Sc cx) W (ms_mem ms3) W2 mem2 (sp - 64 - 16384) (sp - 64) FR).
  { pose proof (akept_of_acall_kept SK SEGS B LAWS pa_segs_low (to_lyc cx) (to_Sc cx) W (ms_mem ms3) W2 mem2
      _ _ FR FR HKC (fun a H => H)) as K. rewrite Hsp', HAS in K. exact K. }
  assert (KAB : akept SEGS B (to_lyc cx) (to_Sc cx) W (to_memc cx) W2 mem2 (sp - TEXT_OF_AK) sp EF).
  { apply (akept_trans SK SEGS B LAWS pa_segs_low (to_lyc cx) (to_Sc cx) W (to_memc cx) (to_Sc cx) W (ms_mem ms3)
      W2 mem2 (sp - TEXT_OF_AK) sp (sp - 64 - 16384) (sp - 64) (to_E cx) FR EF);
      [lz | lz | exact KA | exact KB | lz | lz | tauto | tauto | intros a H; left; exact H
      | intros a H; right; exact H]. }
  (* the write set's and the read set's bytes are no bytes of the block *)
  assert (EnF : forall a, to_E cx a -> ~ FR a).
  { intros a Ha. apply (to_fresh_not_sclass SEGS B LAWS (to_lyc cx) (to_Sc cx) ly2 S2 W2 _ md2 res (k + 1)
      a HAR4 Hbl Hfr2 Hfa Hrow).
    eapply (sclass_of_ajw SK SEGS B LAWS); [exact HGok | exact HJ | exact (Hajw a Ha) |].
    destruct (to_E_app cx a (conj AMp AMo) Ha) as [H | H]; [left; exact H | right; lz]. }
  assert (AKB : forall x, c0 <= x < c0 + c1 -> akb SEGS B (to_lyc cx) (to_Sc cx) (sp - TEXT_OF_AK) sp x).
  { intros x Hx. apply HRD. exists c0, c1. split; [exact Ic0|]. split; [exact Ic1|]. split; [exact Ic0r|].
    split; [exact Ic1r|]. exact Hx. }
  assert (SRCV : forall x, c0 <= x < c0 + c1 -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) (to_memc cx) x).
  { intros x Hx. refine (akept_akb_gx SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ (to_lyc cx) (to_Sc cx) W (to_memc cx) _ _ W2
      mem2 _ _ EF x HJ KAB (AKB x Hx) _).
    intros [Hq | Hq].
    - apply (HnE x); [lz | lz | exact Hq].
    - exact (to_fresh_not_akb SEGS B LAWS (to_lyc cx) (to_Sc cx) ly2 S2 W2 _ md2 res (k + 1) _ _ x HAR4 Hbl Hfr2 Hfa
        Hrow (AKB x Hx) Hq). }
  (* the cursor's bytes across the call *)
  assert (PV : forall i, 0 <= i < 16 -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) (ms_mem ms3) (p + i)).
  { intros i Hi.
    assert (Hakb : akb SEGS B (to_lyc cx) (to_Sc cx) (sp - 64 - 16384) (sp - 64) (p + i)).
    { refine (ajw_akb SK SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (to_lyc cx) (to_Sc cx) _ _ (p + i)
        HGok HJ (Hajw (p + i) (HpE i Hi)) _ _ _ eq_refl eq_refl (fun b m H => H) (fun c q H => H) (fun c q => eq_refl)).
      - lz.
      - destruct (to_E_app cx (p + i) (conj AMp AMo) (HpE i Hi)) as [H | H]; [left; exact H | right; lz].
      - lz. }
    exact (akept_akb_gx SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ (to_lyc cx) (to_Sc cx) W (ms_mem ms3) _ _ W2
      mem2 _ _ FR (p + i) HJ3 KB Hakb (EnF (p + i) (HpE i Hi))). }
  (* *own's bytes across the call, off the image *)
  assert (OV : forall i, 0 <= i < 8 -> ~ in_img SEGS (o + i) ->
            aview SEGS (w_H W2) mem2 (o + i) = aview SEGS (w_H W) (ms_mem ms3) (o + i)).
  { intros i Hi Hni. apply (tm_akept_sclass SEGS B (to_lyc cx) (to_Sc cx) W (ms_mem ms3) W2 mem2 _ _ FR (o + i) KB Hrow).
    - eapply (sclass_of_ajw SK SEGS B LAWS); [exact HGok | exact HJ | exact (Hajw (o + i) (HoE i Hi)) |].
      destruct (to_E_app cx (o + i) (conj AMp AMo) (HoE i Hi)) as [H | H]; [left; exact H | right; lz].
    - exact Hni.
    - lz.
    - exact (EnF (o + i) (HoE i Hi)).
    - lz. }
  (* the shadow span did not change from the entry to the call *)
  assert (SHS : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
            aview SEGS (w_H W) (ms_mem ms3) s = aview SEGS (w_H W) (to_memc cx) s).
  { intros s Hs.
    assert (Hlw : ~ (sp - TEXT_OF_AK <= s < sp)) by (apply (to_low_not_win SK B MT CTX cx s HPX); unfold SHADOW_OFF in Hs; lz).
    apply HUN; [unfold SHADOW_OFF in Hs; lz | exact Hlw |].
    apply (to_E_not_shadow cx s (conj AMp AMo)). exact Hs. }
  assert (FMR : fmiss (to_lyc cx) (to_Sc cx) FR).
  { apply (fmiss_app SEGS B LAWS (to_lyc cx) (to_Sc cx) W (ms_mem ms3) md3 FR HAR3). intros a Ha. unfold FR in Ha.
    rewrite Hrq in Ha. unfold kLowMemEnd, kHighMemBeg in *. lz. }
  assert (FME : fmiss (to_lyc cx) (to_Sc cx) EF).
  { apply fmiss_or; [|exact FMR].
    apply (fmiss_app SEGS B LAWS (to_lyc cx) (to_Sc cx) W (to_memc cx) (to_mdc cx) (to_E cx) HARc).
    intros a Ha. destruct (to_E_app cx a (conj AMp AMo) Ha) as [H | H]; [left; exact H | right; lz]. }
  (* ---- THE BLOCK CUT ---- *)
  change (w64 (BASE + TO_MAL_RA)) with (Z_to_bv 64 (BASE + TO_AT230)).
  apply (to_aft SK B MT CTX LAWS LV MTL AMCPY cx c0 c1 inp adv n k res ly2 S2 W2 regs2 mem2 md2 HPX).
  unfold to_gi_230. cbv zeta.
  split; [exact HJ4|].
  split; [rewrite Hfd2; exact Hfd|]. split; [rewrite Hfs2; exact Hfs|].
  split; [exact (eq_trans (HP4 2 ltac:(unfold acallee_saved; lz)) R2)|].
  split; [exact (eq_trans (HP4 8 ltac:(unfold acallee_saved; lz)) R8)|].
  split; [exact (eq_trans (HP4 9 ltac:(unfold acallee_saved; lz)) R9)|].
  split; [exact Hres|].
  split; [exact (eq_trans (HP4 18 ltac:(unfold acallee_saved; lz)) R18)|].
  split; [exact (eq_trans (HP4 20 ltac:(unfold acallee_saved; lz)) R20)|].
  split; [exact (eq_trans (HP4 21 ltac:(unfold acallee_saved; lz)) R21)|].
  split.
  { intros r Hr. exact (eq_trans (HP4 r ltac:(unfold TO_UNTOUCHED in Hr; cbn [In] in Hr; unfold acallee_saved; lz))
      (RUT r Hr)). }
  split.
  { intros j Hj. refine (eq_trans _ (RSV j Hj)). apply rdword_ext. intros i Hi. apply KC1; lz. }
  split; [exact Hbl|]. split; [exact Hfr2|]. split; [exact Hfa|]. split; [exact H4096|].
  split; [exact KAB|].
  split.
  { intros a Ha. destruct (Z_lt_le_dec a (sp - 64)) as [Hl | Hl].
    - apply KC6. lz.
    - apply KC5; [lz | lz | exact (HPW a Ha)]. }
  split; [exact MLE|].
  split; [unfold text_of_ledpost; exact (alc_depot_any _ _ _ _ HD)|].
  split; [exact HINP|]. split; [lz|]. split; [lz|]. split; [lz|]. split; [lz|].
  split; [exact HNZ|].
  split.
  { intros i Hi. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (SRCV (c0 + adv + i) ltac:(lz))).
    assert (Hl : (Z.to_nat (adv + i) < length inp)%nat) by lz.
    pose proof Iinp as (_ & _ & Hb). pose proof (Hb (Z.to_nat (adv + i)) Hl) as Hbi.
    rewrite Z2Nat.id in Hbi by lz. replace (c0 + (adv + i)) with (c0 + adv + i) in Hbi by lz.
    exact Hbi. }
  split.
  { intros Hk.
    assert (RA0 : range_addressable (aview SEGS (w_H W) (to_memc cx)) SHADOW_OFF (c0 + adv) k)
      by exact (tm_ra_sub _ _ c0 c1 (c0 + adv) k HRAin ltac:(lz) ltac:(lz)).
    assert (HU0 : shadow_hull_vis (aview SEGS (w_H W) (to_memc cx)) (c0 + adv) k)
      by exact (tm_hull_sub _ c0 c1 (c0 + adv) k HHin ltac:(lz) Hk ltac:(lz) ltac:(lz)).
    destruct (shadow_transport SEGS B LAWS TB pa_img_range (to_lyc cx) (to_Sc cx) W (to_memc cx) (to_mdc cx) ly2 S2 W2
      mem2 md2 (sp - TEXT_OF_AK) sp EF (c0 + adv) k HARc HAR4 Elo Ehi Hbl2 KAB FME Hk
      (fun x Hx => sclass_of_akb SEGS B _ _ _ _ x (AKB x ltac:(lz))) RA0 HU0) as (RA2 & HU2).
    split; [exact RA2|]. split; [exact HU2|].
    split; [unfold amem_range in *; lz|].
    split.
    { apply (tm_apart_of_disj res k (c0 + adv) k Hk Hk). intros a H1 H2.
      apply (to_fresh_not_akb SEGS B LAWS (to_lyc cx) (to_Sc cx) ly2 S2 W2 _ md2 res (k + 1) _ _ a HAR4 Hbl Hfr2 Hfa
        Hrow (AKB a ltac:(lz))). rewrite Hrq. lz. }
    intros a Ha. lz. }
  split.
  { apply (tm_val_mem_move SEGS _ _ p 8 _ Pp). intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    apply (mbyte_of_aview SEGS). replace x with (p + (x - p)) by lz. apply PV. lz. }
  split.
  { apply (tm_val_mem_move SEGS _ _ (p + 8) 8 _ Pp8). intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    apply (mbyte_of_aview SEGS). replace x with (p + (x - p)) by lz. apply PV. lz. }
  split.
  { destruct HBP as (junk & Hl & (Hjb & Hjw)). exists junk. split; [exact Hl|]. split.
    - apply (tm_abytes_move SEGS _ _ p junk Hjb). intros x Hx.
      apply (mbyte_of_aview SEGS). replace x with (p + (x - p)) by lz. apply PV. lz.
    - intros i Hi. apply (tm_wr_move SEGS HSEGS (w_H W) (ms_mem ms3) (w_H W2) mem2 (p + i) ltac:(lz) (Hjw i Hi)).
      + intros Hr. exact (Hro (p + i) (HpE i ltac:(lz)) (or_introl Hr)).
      + intros _. apply PV. lz. }
  split.
  { intros i Hi. destruct HBO as (junk & Hl & (_ & Hjw)).
    apply (tm_wr_move SEGS HSEGS (w_H W) (ms_mem ms3) (w_H W2) mem2 (o + i) ltac:(lz) (Hjw i ltac:(lz))).
    - intros Hr. exact (Hro (o + i) (HoE i Hi) (or_introl Hr)).
    - intros Hni. exact (OV i Hi Hni). }
  assert (RA3 : range_addressable (aview SEGS (w_H W) (ms_mem ms3)) SHADOW_OFF o 8)
    by exact (tm_ra_move (aview SEGS (w_H W) (to_memc cx)) _ o 8 ltac:(lz) ltac:(lz) SHS HRAo).
  assert (HU3 : shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms3)) o 8)
    by exact (tm_hull_move (aview SEGS (w_H W) (to_memc cx)) _ o 8 ltac:(lz) ltac:(lz) ltac:(lz) SHS HHo).
  destruct (shadow_transport SEGS B LAWS TB pa_img_range (to_lyc cx) (to_Sc cx) W (ms_mem ms3) md3 ly2 S2 W2
    mem2 md2 (sp - 64 - 16384) (sp - 64) FR o 8 HAR3 HAR4 Elo Ehi Hbl2 KB FMR ltac:(lz)
    (fun x Hx => ltac:(replace x with (o + (x - o)) by lz;
       eapply (sclass_of_ajw SK SEGS B LAWS); [exact HGok | exact HJ | exact (Hajw (o + (x - o)) (HoE (x - o) ltac:(lz))) |];
       destruct (to_E_app cx (o + (x - o)) (conj AMp AMo) (HoE (x - o) ltac:(lz))) as [H | H]; [left; exact H | right; lz]))
    RA3 HU3) as (RA4 & _).
  exact RA4.
Qed.

End b.
End a.
