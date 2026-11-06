(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readHead.v, with its module names changed; 426 of its 464 lines of code are new or changed and 320 lines of the source are left out. *)
(* remember (image A, fuzz_link.asan 0x89db4; listing (internal path)
   (internal record, sha256 e02062b286f1)): the two machine-level ENDS of the walk of lib/A/Prog/remember_c.v
   `remember_acontract`, each stated at the config the symbolic runs reach, so that every path of lib/A/Prog/remember.v
   (the n <= 0 arm) and of lib/A/Prog/rememberLoopRun.v (the strcmp loop) closes with one of them:

     rem_append_tail : the TAIL jump +0xf4 into wrapper_snprintf at a count 0 <= n <= 31 whose list does not hold
                       the name (the append: the count word already holds n + 1, the store +0xc8), through
                       lib/A/Prog/rememberCalls.v `rem_snp_tail`, to the whole `apostF`;
     rem_ret_leaf    : the `ret` +0xa4 that leaves the block as it was (a hit, +0x68 `beqz a0` taken, or 32 names
                       kept, +0x7c `bge a0, s4` not taken), to the whole `apostF` at the entry's own fx.

   What each takes of the memory at that config, against the call memory memc: equal outside the window
   [sp - REMEMBER_AK, sp) (and, for the append, outside the count word [p, p + 4)), the count word read back,
   every present byte still present; of the registers: the callee-saved ones as at the entry
   (`aregs_preserved`), and the snprintf arguments for the append.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs LinkMfDefs LinkSnpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c remember_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  rememberPost rememberEntry rememberKept rememberCalls LinkWalkMkCr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* presence that only grows gives a memory that only grows (model_decide.v's grows_of_present) *)
Lemma rem_grows_of_present : forall H (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Eh; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)).
{ unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists b; exact Em]. }
destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis SNP : asnprintf_link_realizes pa_segs B PCAP_RLO PCAP_RHI LA_W_SNPRINTF.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

(* the byte list of the block and the name are determined by the memory *)
Lemma rem_gdet : forall (m : word -> option byte) p g1 g2,
  amarks_at pa_segs m p g1 -> amarks_at pa_segs m p g2 -> g1 = g2.
Proof.
intros m p g1 g2 ((Hb1 & _) & Hl1) ((Hb2 & _) & Hl2).
destruct Hb1 as (_ & _ & H1). destruct Hb2 as (_ & _ & H2).
assert (HL : length g1 = length g2) by lia.
apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length g1)) as [Hi | Hi].
- rewrite <- (H1 i Hi), (H2 i ltac:(lia)). reflexivity.
- rewrite (proj2 (nth_error_None g1 i) Hi), (proj2 (nth_error_None g2 i) ltac:(lia)). reflexivity.
Qed.

Lemma rem_ndet : forall (m : word -> option byte) q s1 s2,
  acstr_at pa_segs m q s1 -> acstr_at pa_segs m q s2 -> s1 = s2.
Proof.
intros m q s1 s2 (Hb1 & Hn1) (Hb2 & Hn2).
destruct Hb1 as (_ & _ & H1). destruct Hb2 as (_ & _ & H2).
assert (HL : length s1 = length s2).
{ destruct (Nat.lt_trichotomy (length s1) (length s2)) as [Hlt | [Heq | Hgt]];
    [exfalso | exact Heq | exfalso].
  - pose proof (H1 (length s1) ltac:(rewrite length_app; cbn [length]; lia)) as A1.
    pose proof (H2 (length s1) ltac:(rewrite length_app; cbn [length]; lia)) as A2.
    rewrite A1 in A2. rewrite nth_error_app2 in A2 by lia.
    rewrite Nat.sub_diag in A2. cbn [nth_error] in A2.
    rewrite nth_error_app1 in A2 by lia.
    symmetry in A2. apply nth_error_In in A2. exact (Hn2 A2).
  - pose proof (H1 (length s2) ltac:(rewrite length_app; cbn [length]; lia)) as A1.
    pose proof (H2 (length s2) ltac:(rewrite length_app; cbn [length]; lia)) as A2.
    rewrite A2 in A1. rewrite nth_error_app2 in A1 by lia.
    rewrite Nat.sub_diag in A1. cbn [nth_error] in A1.
    rewrite nth_error_app1 in A1 by lia.
    symmetry in A1. apply nth_error_In in A1. exact (Hn1 A1). }
apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length s1)) as [Hi | Hi].
- pose proof (H1 i ltac:(rewrite length_app; cbn [length]; lia)) as A1.
  pose proof (H2 i ltac:(rewrite length_app; cbn [length]; lia)) as A2.
  rewrite A1 in A2. rewrite !nth_error_app1 in A2 by lia. exact A2.
- rewrite (proj2 (nth_error_None s1 i) Hi), (proj2 (nth_error_None s2 i) ltac:(lia)). reflexivity.
Qed.

(* apresent does not see the wrap *)
Lemma rem_apresent_mod : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a <-> apresent H m (a mod 2 ^ 64).
Proof.
intros H m a.
assert (Zmod64 : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z. apply Z.mod_mod. lia. }
unfold apresent. rewrite Zmod64. reflexivity.
Qed.

(* ==========================================================================
   1. The `ret` +0xa4 that leaves the block as it was
   ========================================================================== *)
Lemma rem_ret_leaf : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    (regs : bvmap 5 word) gbs nm (regsR : bvmap 5 word) memR mdR,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - REMEMBER_AK -> spZ regs <= sp0 ->
  amarks_at pa_segs (rdW W memc) (aarg regs 0) gbs -> marks_wf gbs ->
  amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memc) (aarg regs 0) ->
  acstr_at pa_segs (rdW W memc) (aarg regs 1) nm ->
  (existsb (fun y => bl_eqb y nm) (mk_names gbs) = true \/ mk_n gbs = MARKS_MAX) ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memR mdR k ->
  m_fds mdR = m_fds mdc -> m_fs mdR = m_fs mdc ->
  aregs_preserved regs regsR ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) memR a = aview pa_segs (w_H W) memc a) ->
  (forall x, apresent (w_H W) memc x -> apresent (w_H W) memR x) ->
  apostF SK pa_segs B REMEMBER_AK 0 (fun a => inFP (remember_awr regs (rdW W memc)) a) G XO OUT STK sp0 FP
    ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (fun ly2 S2 W2 regs2 mem2 _ =>
       S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       remember_apost pa_segs regs (rdW W memc) regs2 (rdW W2 mem2))
    W (mkCfg (mkst regsR (getr regs 1) memR (seg_rom pa_segs)) mdR).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs gbs nm regsR memR mdR
  HJ0 Hwlo Hwhi HMK HWF HBLK HNM HC HJR FDs FSs HAPR UNR PRGR.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity.
destruct (re_aj_bounds SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ0)
  as (Hceil & H47 & HXO & Hpres).
pose proof HBLK as (Hp0 & Hpm & Hpra & Hphv & Hptail & Hpap).
pose proof HMK as (HMKb & HMKlen). pose proof HMKb as (HMKbytes & HMKwr).
assert (HpLO : aarg regs 0 + 524 <= kLowMemEnd - 1 \/ kHighMemBeg <= aarg regs 0)
  by (unfold amem_range, MK_SIZE in Hpm; destruct Hpm as [Hx | [Hx _]]; lia).
assert (Hpb : aarg regs 0 + 524 <= 2 ^ 47 - 1)
  by (unfold amem_range, MK_SIZE in Hpm; destruct Hpm as [Hx | [_ Hx]]; lia).
apply apostF_of_apost.
eapply (@rem_apost_leaf fx rc SK PI B LAWS).
- exact HJ0.
- exact HJR.
- lia.
- exact Hwlo.
- lia.
- exact FDs.
- exact FSs.
- exact HAPR.
- intros a Ha H1 _. exact (UNR a Ha H1).
- exact PRGR.
- intros a Ha. apply PRGR. apply Hpres. lia.
- intros x Hx.
  assert (Hxin : aarg regs 0 <= x < aarg regs 0 + MK_SIZE).
  { destruct Hx as (r & Hin & Hr). unfold remember_awr in Hin. cbn [In] in Hin.
    destruct Hin as [Heqr | []]. subst r. unfold in_zr, aivl in Hr. cbn [fst snd] in Hr.
    replace (aarg regs 0 =? 0) with false in Hr by (symmetry; apply Z.eqb_neq; lia). exact Hr. }
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
  destruct HpLO as [Hx1 | Hx1]; unfold MK_SIZE in *; lia.
- split; [destruct Sc; reflexivity|].
  split; [apply Permutation_refl|].
  intros gbs0 nm0 HM0 HN0.
  rewrite (rem_gdet _ _ gbs0 gbs HM0 HMK). rewrite (rem_ndet _ _ nm0 nm HN0 HNM).
  apply (rem_post_kept pa_segs (rdW W memc) (rdW W memR) (aarg regs 0) gbs nm HMK HWF HC).
  + intros a Ha. apply (rem_mbyte_eq_of_aview_eq W).
    apply UNR; [unfold MK_SIZE in *; lia | unfold apart_frame, MK_SIZE in *; lia].
  + intros a Ha.
    apply (writable_kept (w_H W) memc); [intros Hx; exact (PRGR _ Hx)|].
    replace a with (aarg regs 0 + (a - aarg regs 0)) by lia.
    apply HMKwr. unfold MK_SIZE in *. lia.
Qed.

(* ==========================================================================
   2. The TAIL jump +0xf4 into wrapper_snprintf: the append at a count n <= 31
   ========================================================================== *)
Lemma rem_append_tail : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    (regs : bvmap 5 word) gbs nm (regsT : bvmap 5 word) memT mdT,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  gx_ok pa_segs B G ->
  arodata_okP pa_segs PCAP_RLO PCAP_RHI B (aview pa_segs (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REMEMBER_AK -> spZ regs <= sp0 ->
  (forall a, inFP (remember_awr regs (rdW W memc)) a -> ajw B G XO OUT STK sp0 FP ly S lyc Sc own a) ->
  (forall a, inFP (remember_awr regs (rdW W memc)) a -> ~ in_roP pa_segs PCAP_RLO PCAP_RHI a) ->
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  amarks_at pa_segs (rdW W memc) (aarg regs 0) gbs -> marks_wf gbs ->
  amarks_ledger (ablocks B lyc Sc) (aarg regs 0) ->
  amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memc) (aarg regs 0) ->
  aarg regs 1 <> 0 -> acstr_at pa_segs (rdW W memc) (aarg regs 1) nm -> (length nm <= 15)%nat ->
  astr_rt_ok pa_segs regs REMEMBER_AK (rdW W memc) (aarg regs 1) nm ->
  apart (aarg regs 1) (Z.of_nat (length nm) + 8) (aarg regs 0) MK_SIZE ->
  acstr_at pa_segs (rdW W memc) LA_FMT_S S_FMT_S ->
  astr_rt_ok pa_segs regs REMEMBER_AK (rdW W memc) LA_FMT_S S_FMT_S ->
  mk_n gbs <= 31 -> existsb (fun y => bl_eqb y nm) (mk_names gbs) = false ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  m_fds mdT = m_fds mdc -> m_fs mdT = m_fs mdc ->
  aregs_preserved regs regsT ->
  getr regsT 1 = getr regs 1 ->
  getr regsT 10 = w64 (aarg regs 0 + (MK_NAME + MARK_LEN * mk_n gbs)) -> getr regsT 11 = w64 16 ->
  getr regsT 12 = w64 LA_FMT_S -> getr regsT 13 = w64 (aarg regs 1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REMEMBER_AK <= a < spZ regs) ->
     ~ (aarg regs 0 <= a < aarg regs 0 + 4) ->
     mbyte pa_segs (rdW W memT) a = mbyte pa_segs (rdW W memc) a) ->
  val_mem pa_segs (rdW W memT) (aarg regs 0) 4 (mk_n gbs + 1) ->
  (forall x, apresent (w_H W) memc x -> apresent (w_H W) memT x) ->
  SRr pa_segs W (mkCfg (mkst regsT (Z_to_bv 64 LA_W_SNPRINTF) memT (seg_rom pa_segs)) mdT)
    (apostF SK pa_segs B REMEMBER_AK 0 (fun a => inFP (remember_awr regs (rdW W memc)) a) G XO OUT STK sp0 FP
       ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
       (fun ly2 S2 W2 regs2 mem2 _ =>
          S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
          remember_apost pa_segs regs (rdW W memc) regs2 (rdW W2 mem2))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs gbs nm regsT memT mdT
  HJ0 HGok HROD Hraw Hra4 Hgp Htp Hal16 Hwlo Hwhi Hajw Hnro Hfrm0 HMK HWF HLED HBLK Hqnz HNM Hlen HNMrt
  Hapart HFMT HFMTrt Hn31 HEX HJ FDs FSs HAP1 Hr1 Hr10 Hr11 Hr12 Hr13 KEEPm HCNT PRG.
pose proof HLED as (HLEDin & HIMG).
pose proof HBLK as (Hp0 & Hpm & Hpra & Hphv & Hptail & Hpap).
pose proof HNMrt as (Hq0 & Hql & Hqm & Hqra & Hqhv & Hqtail & Hqap).
pose proof HMK as (HMKb & HMKlen).
pose proof HMKb as (HMKbytes & HMKwr).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HIMG as HOFF. unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HOFF.
destruct (re_aj_bounds SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ0)
  as (Hceil & H47 & HXO & Hpres).
assert (Hnr : 0 <= mk_n gbs <= 32)
  by (pose proof (amk_n_range gbs HWF) as X; unfold MARKS_MAX in X; exact X).
assert (HSZ : Z.of_nat (length gbs) = MK_SIZE) by exact HMKlen.
(* the shadow band, the image and every byte outside the window and the count word are as they were *)
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HpLO : aarg regs 0 + 524 <= kLowMemEnd - 1 \/ kHighMemBeg <= aarg regs 0)
  by (unfold amem_range, MK_SIZE in Hpm; destruct Hpm as [Hx | [Hx _]]; lia).
assert (Hpb : aarg regs 0 + 524 <= 2 ^ 47 - 1)
  by (unfold amem_range, MK_SIZE in Hpm; destruct Hpm as [Hx | [_ Hx]]; lia).
assert (KEEPv : forall a, 0 <= a < 2 ^ 64 ->
          ~ (spZ regs - REMEMBER_AK <= a < spZ regs) -> ~ (aarg regs 0 <= a < aarg regs 0 + 4) ->
          aview pa_segs (w_H W) memT a = aview pa_segs (w_H W) memc a)
  by (intros a Ha H1 H2; unfold aview; rewrite (KEEPm a Ha H1 H2); reflexivity).
assert (KEEPsh : forall s, SHADOW_OFF <= s < kHighShadowEnd ->
          aview pa_segs (w_H W) memT s = aview pa_segs (w_H W) memc s).
{ intros s Hs. apply KEEPv; [lia | lia |]. destruct HpLO as [Hx | Hx]; lia. }
assert (HULLB : forall x n, 0 <= x -> x + n <= 2 ^ 47 -> 0 < n ->
          forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
            SHADOW_OFF <= s < kHighShadowEnd).
{ intros x n Hx Hxn Hn s Hs. unfold shadow_addr in Hs.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.div_le_mono x (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
  assert (D3 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  assert (D4 : SHADOW_OFF / 8 * 8 = SHADOW_OFF) by reflexivity.
  pose proof (Z.div_le_mono SHADOW_OFF (SHADOW_OFF + x / 8) 8 ltac:(lia) ltac:(lia)) as D5.
  pose proof (Z.mul_div_le (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D6.
  assert (D7 : kHighShadowEnd = SHADOW_OFF + 2 ^ 44) by lia.
  lia. }
assert (TRcstr : forall x s,
          (forall b, x <= b <= x + Z.of_nat (length s) -> ~ (spZ regs - REMEMBER_AK <= b < spZ regs)) ->
          (forall b, x <= b <= x + Z.of_nat (length s) -> ~ (aarg regs 0 <= b < aarg regs 0 + 4)) ->
          acstr_at pa_segs (rdW W memc) x s -> acstr_at pa_segs (rdW W memT) x s).
{ intros x s H1 H2 ((Hx0 & Hxl & Hb) & Hnz).
  rewrite length_app in Hxl. cbn [length] in Hxl.
  split; [|exact Hnz]. split; [exact Hx0|].
  split; [rewrite length_app; cbn [length]; lia|].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (KEEPm (x + Z.of_nat i) ltac:(lia) ltac:(apply H1; lia) ltac:(apply H2; lia)).
  exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)). }
assert (GRc : mem_grows (rdW W memc) (rdW W memT)) by exact (rem_grows_of_present _ _ _ PRG).
assert (TRrt : forall x s,
          astr_rt_ok pa_segs regs REMEMBER_AK (rdW W memc) x s ->
          astr_rt_ok pa_segs regs REMEMBER_AK (rdW W memT) x s).
{ intros x s (Hx0 & Hxl & Hxm & Hra & Hhv & Htl & Hap).
  unfold amem_range in Hxm.
  split; [exact Hx0|]. split; [exact Hxl|]. split; [exact Hxm|].
  split.
  { apply (ra_shadow_eq (ard pa_segs (rdW W memc))); [exact Hra|].
    intros y Hy. apply KEEPsh.
    unfold shadow_addr. pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)).
    assert (y / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
  split.
  { intros sh Hsh.
    assert (Heq : ard pa_segs (rdW W memT) sh = ard pa_segs (rdW W memc) sh).
    { apply KEEPsh. apply (HULLB x (Z.of_nat (length s) + 1)); [lia | lia | lia | exact Hsh]. }
    rewrite Heq. exact (Hhv sh Hsh). }
  split; [|exact Hap].
  intros b Hb. exact (rem_aview_some_grow pa_segs (w_H W) memc memT b GRc (Htl b Hb)). }
(* the block's shadow and place at the tail memory *)
assert (HBLKT : amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memT) (aarg regs 0)).
{ split; [exact Hp0|]. split; [exact Hpm|].
  split.
  { apply (ra_shadow_eq (ard pa_segs (rdW W memc))); [exact Hpra|].
    intros y Hy. apply KEEPsh. unfold shadow_addr.
    pose proof (Z.div_pos y 8 ltac:(unfold MK_SIZE in *; lia) ltac:(lia)).
    assert (y / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; unfold MK_SIZE in *; lia). lia. }
  split.
  { intros sh Hsh.
    assert (Heq : ard pa_segs (rdW W memT) sh = ard pa_segs (rdW W memc) sh).
    { apply KEEPsh. apply (HULLB (aarg regs 0) MK_SIZE);
        [lia | unfold MK_SIZE; lia | unfold MK_SIZE; lia | exact Hsh]. }
    rewrite Heq. exact (Hphv sh Hsh). }
  split; [|exact Hpap].
  intros b Hb. exact (rem_aview_some_grow pa_segs (w_H W) memc memT b GRc (Hptail b Hb)). }
(* every byte of the block is there at the tail memory *)
assert (HSOME : forall i, (i < Z.to_nat MK_SIZE)%nat ->
          exists b, mbyte pa_segs (rdW W memT) (aarg regs 0 + Z.of_nat i) = Some b).
{ intros i Hi.
  destruct (Z_lt_le_dec (Z.of_nat i) 4) as [Hlt | Hge].
  - exists (Z_to_bv 8 (le_byte (mk_n gbs + 1) 4 i)).
    exact (HCNT i ltac:(lia)).
  - rewrite (KEEPm (aarg regs 0 + Z.of_nat i) ltac:(unfold MK_SIZE in *; lia)
               ltac:(unfold apart_frame, MK_SIZE in *; lia) ltac:(lia)).
    destruct HMKbytes as (_ & _ & Hnth).
    rewrite (Hnth i ltac:(unfold MK_SIZE in *; lia)).
    destruct (nth_error gbs i) as [bb|] eqn:Eg; [exists bb; reflexivity|].
    exfalso. apply nth_error_None in Eg. unfold MK_SIZE in *. lia. }
assert (HMAT : exists gbs', amarks_at pa_segs (rdW W memT) (aarg regs 0) gbs').
{ exists (abytes_of pa_segs (rdW W memT) (aarg regs 0) (Z.to_nat MK_SIZE)).
  split; [split|].
  - apply abytes_of_abytes; [lia | unfold MK_SIZE in *; lia | exact HSOME].
  - rewrite abytes_of_length. intros i Hi.
    apply (writable_kept (w_H W) memc); [intros Hx; exact (PRG _ Hx)|].
    apply HMKwr. unfold MK_SIZE in *. lia.
  - rewrite abytes_of_length. unfold MK_SIZE. lia. }
(* the name and the format at the tail memory *)
pose proof HFMTrt as (_ & _ & _ & _ & _ & _ & Hfap).
assert (HNMT : acstr_at pa_segs (rdW W memT) (aarg regs 1) nm).
{ apply TRcstr; [| | exact HNM];
    intros b Hb; unfold apart_frame in Hqap; unfold apart in Hapart; unfold MK_SIZE in *; lia. }
assert (HNMrtT : astr_rt_ok pa_segs regs REMEMBER_AK (rdW W memT) (aarg regs 1) nm).
{ apply TRrt; exact HNMrt. }
assert (HFMTT : acstr_at pa_segs (rdW W memT) LA_FMT_S S_FMT_S).
{ apply TRcstr; [| | exact HFMT];
    intros b Hb; cbn [length S_FMT_S map] in Hb; unfold apart_frame in Hfap;
    unfold LA_FMT_S, MK_SIZE in *; lia. }
assert (HFMTrtT : astr_rt_ok pa_segs regs REMEMBER_AK (rdW W memT) LA_FMT_S S_FMT_S).
{ apply TRrt; exact HFMTrt. }
(* the read-only image at the tail memory: its bytes are image bytes, and `apre`'s last conjunct keeps the
   write set off `in_roP` *)
assert (HRODT : arodata_okP pa_segs PCAP_RLO PCAP_RHI B (aview pa_segs (w_H W) memT)).
{ intros a Hro Hos Her.
  assert (Hlow : 0 <= a < kLowMemEnd).
  { destruct Hro as [(s & Hin & Hw & Hb) | Hrl].
    - apply (pa_segs_low a). exists s. split; [exact Hin | exact Hb].
    - unfold PCAP_RLO, PCAP_RHI in Hrl. lia. }
  rewrite KEEPv; [exact (HROD a Hro Hos Her) | lia | lia |].
  intros Hc2. apply (Hnro a); [| exact Hro].
  unfold remember_awr. exists (aivl (aarg regs 0) MK_SIZE). split; [left; reflexivity|].
  unfold in_zr, aivl. cbn [fst snd].
  replace (aarg regs 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold MK_SIZE in *. lia. }
(* the stack-protector pair, from AR at the tail memory *)
assert (HARt : AR pa_segs B lyc Sc W memT mdT) by (eapply rem_aj_AR; exact HJ).
assert (HGOT : rdword (aview pa_segs (w_H W) memT) LA_GOT_GUARD = Some LA_GUARD)
  by (eapply link_guard_got; eauto).
assert (HCAN : exists g, rdword (aview pa_segs (w_H W) memT) LA_GUARD = Some g)
  by (eapply link_guard_val; eauto).
(* ---- the TAIL jump +0xf4 into wrapper_snprintf ---- *)
eapply SRr_mono.
{ eapply rem_snp_tail with (regs := regs) (raw := getr regs 1)
    (p := aarg regs 0) (n := mk_n gbs) (q := aarg regs 1) (nm := nm).
  - exact LAWS.
  - exact SNP.
  - exact HGok.
  - exact HJ.
  - exact HRODT.
  - exact Hfrm0.
  - exact (f_equal bv_unsigned (HAP1 2 ltac:(unfold acallee_saved; lia))).
  - exact Hal16.
  - exact Hwlo.
  - exact Hwhi.
  - transitivity (getr regs 3); [exact (HAP1 3 ltac:(unfold acallee_saved; lia)) | exact Hgp].
  - transitivity (getr regs 4); [exact (HAP1 4 ltac:(unfold acallee_saved; lia)) | exact Htp].
  - exact Hr1.
  - exact Hraw.
  - exact Hra4.
  - exact Hr10.
  - exact Hr11.
  - exact Hr12.
  - exact Hr13.
  - lia.
  - exact HLEDin.
  - exact HIMG.
  - exact HBLKT.
  - exact HMAT.
  - exact Hqnz.
  - exact HNMT.
  - exact Hlen.
  - exact HNMrtT.
  - exact Hapart.
  - exact HFMTT.
  - exact HFMTrtT.
  - intros a Ha. apply (Hajw a). unfold remember_awr.
    exists (aivl (aarg regs 0) MK_SIZE). split; [left; reflexivity|].
    unfold in_zr, aivl. cbn [fst snd].
    replace (aarg regs 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold MK_NAME, MARK_LEN, MK_SIZE in *. lia.
  - exact HGOT.
  - exact HCAN. }
intros W2 c2 Hwle Hpost. cbv beta in Hpost.
destruct Hpost as (HW & fx' & regs2 & mem2 & md2 & Hc2 & Hfp & Hfz & HJ2 & HPres & Hsame & Hby & Hfr & Hpr).
subst W2. subst c2.
assert (PRG2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a).
{ intros a Ha.
  assert (Ha1 : apresent (w_H W) memT (a mod 2 ^ 64))
    by (apply (proj1 (rem_apresent_mod _ _ a)); exact (PRG a Ha)).
  assert (Ha2 : apresent (w_H W) mem2 (a mod 2 ^ 64))
    by (apply Hpr; [pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)); lia | exact Ha1]).
  exact (proj2 (rem_apresent_mod _ _ a) Ha2). }
exists fx'. split; [split; [exact Hfp | right; exact Hfz]|].
eapply (@rem_apost_leaf fx' rc SK PI B LAWS).
- exact HJ0.
- exact HJ2.
- lia.
- exact Hwlo.
- lia.
- rewrite (same_but_materialized_wvb _ _ Hsame). rewrite (proj1 (wvb_fds_fs _ _ _)). exact FDs.
- rewrite (same_but_materialized_wvb _ _ Hsame). rewrite (proj2 (wvb_fds_fs _ _ _)). exact FSs.
- exact (aregs_preserved_trans regs regsT regs2 HAP1 HPres).
- intros a Ha H1 H2.
  assert (HnotE : ~ (aarg regs 0 <= a < aarg regs 0 + MK_SIZE)).
  { intros Hin. apply H2. unfold remember_awr.
    exists (aivl (aarg regs 0) MK_SIZE). split; [left; reflexivity|].
    unfold in_zr, aivl. cbn [fst snd].
    replace (aarg regs 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
  rewrite (Hfr a Ha); [| unfold MK_NAME, MARK_LEN, MK_SIZE in *; lia | lia].
  apply KEEPv; [exact Ha | lia | unfold MK_SIZE in *; lia].
- exact PRG2.
- intros a Ha. apply PRG2. apply Hpres. lia.
- intros x Hx.
  assert (Hxin : aarg regs 0 <= x < aarg regs 0 + MK_SIZE).
  { destruct Hx as (r & Hin & Hr). unfold remember_awr in Hin. cbn [In] in Hin.
    destruct Hin as [Heqr | []]. subst r. unfold in_zr, aivl in Hr. cbn [fst snd] in Hr.
    replace (aarg regs 0 =? 0) with false in Hr by (symmetry; apply Z.eqb_neq; lia). exact Hr. }
  destruct HpLO as [Hx1 | Hx1]; unfold MK_SIZE in *; lia.
- split; [destruct Sc; reflexivity|].
  split; [apply Permutation_refl|].
  intros gbs0 nm0 HM0 HN0.
  rewrite (rem_gdet _ _ gbs0 gbs HM0 HMK). rewrite (rem_ndet _ _ nm0 nm HN0 HNM).
  apply (rem_marks_after_a pa_segs (rdW W memc) (rdW W mem2) (aarg regs 0) gbs nm (mk_n gbs)).
  + exact HMK.
  + exact HWF.
  + reflexivity.
  + lia.
  + exact (proj2 HNM).
  + exact Hlen.
  + exact HEX.
  + intros kk Hkk.
    assert (Heq : mbyte pa_segs (rdW W mem2) (aarg regs 0 + Z.of_nat kk)
                = mbyte pa_segs (rdW W memT) (aarg regs 0 + Z.of_nat kk)).
    { apply (rem_mbyte_eq_of_aview_eq W).
      apply (Hfr (aarg regs 0 + Z.of_nat kk));
        [unfold MK_SIZE in *; lia
        | unfold MK_NAME, MARK_LEN; lia
        | unfold apart_frame in Hpap; unfold MK_SIZE in *; lia]. }
    rewrite Heq. exact (HCNT kk Hkk).
  + intros j Hj.
    pose proof (Hby j Hj) as Hb. unfold aview in Hb.
    destruct (mbyte pa_segs (rdW W mem2)
                (aarg regs 0 + (MK_NAME + MARK_LEN * mk_n gbs) + j)) as [bb|] eqn:Eb;
      [| discriminate Hb].
    cbn [option_map] in Hb. injection Hb as Hb.
    rewrite (nth_error_nth' (nm ++ [zb 0]) (zb 0))
      by (rewrite length_app; cbn [length]; lia).
    f_equal. apply bv_eq. exact Hb.
  + intros a Ha H1 H2.
    assert (Heq : mbyte pa_segs (rdW W mem2) a = mbyte pa_segs (rdW W memT) a).
    { apply (rem_mbyte_eq_of_aview_eq W).
      apply (Hfr a); [unfold MK_SIZE in *; lia
                     | unfold MK_NAME, MARK_LEN in *; lia
                     | unfold apart_frame in Hpap; unfold MK_SIZE in *; lia]. }
    rewrite Heq.
    apply KEEPm; [unfold MK_SIZE in *; lia
                 | unfold apart_frame in Hpap; unfold MK_SIZE in *; lia | lia].
  + intros a Ha.
    apply (writable_kept (w_H W) memc); [intros Hx; exact (PRG2 _ Hx)|].
    replace a with (aarg regs 0 + (a - aarg regs 0)) by lia.
    apply HMKwr. unfold MK_SIZE in *. lia.
Qed.

End b.
End a.

About rem_ret_leaf.
Print Assumptions rem_ret_leaf.
About rem_append_tail.
Print Assumptions rem_append_tail.
