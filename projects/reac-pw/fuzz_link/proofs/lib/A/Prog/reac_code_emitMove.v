(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readHead.v, with its module names changed; 84 of its 111 lines of code are new or changed and 331 lines of the source are left out. *)
(* reac_code_emit on image A: the caller's format and its %s strings, from the call's memory to a later state of the
   walk (the vfprintf call at +0x138, lib/A/Prog/reac_code_emitMid.v).

   A C string the Pre states at the call (`acstr_at`, model_decide_c.v `astr_rt_ok`) whose bytes and NUL are read-set
   bytes (`akb`) outside the step's exception set keeps both at any later state the call's `akept` reaches:
   - its bytes: link_amem.v akept_akb_gx;
   - its shadow (range_addressable, shadow_hull_vis): LinkWalkShadow.v shadow_transport_akb;
   - the rest of its NUL's granule: LinkWalkMkVis.v tail_vis_transport;
   - the rest is pure, or about the call's registers.
   `em_cstr_keep` is that, `em_args_keep` the same over reac_code_emit_c.v apf_args_ok.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP09 YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable LinkSyms LinkList LinkAddr LinkPa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AB13 AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem LinkWalkCall LinkWalkShadow LinkWalkMkVis.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c reac_code_emit_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis HSEGS : pa_segs = AB1v.tfibsegs.

Lemma em_segs_rom : forall a, 0x10000 <= a < pcap_img_end -> seg_rom pa_segs (Z_to_bv 64 a) <> None.
Proof. intros a Ha. rewrite HSEGS. exact (AB13.tfib_rom_all a Ha). Qed.

Lemma em_acstr_move : forall H H' (m m' : word -> option byte) a s,
  (forall x, a <= x <= a + Z.of_nat (length s) -> aview pa_segs H' m' x = aview pa_segs H m x) ->
  acstr_at pa_segs (mrestrict H m) a s -> acstr_at pa_segs (mrestrict H' m') a s.
Proof.
  intros H H' m m' a s E ((Ha & Hl & Hb) & Hn). split; [|exact Hn]. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite <- (Hb i Hi). apply (mbyte_of_aview pa_segs). apply E.
  rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.

(* the facts a later state of the walk shares with the call *)
Definition em_later (lyc : alayout) (Sc : astate) (ly3 : alayout) (S3 : astate) : Prop :=
  ly_stk_lo ly3 = ly_stk_lo lyc /\ ly_stk_hi ly3 = ly_stk_hi lyc /\
  (forall q m, In (q, m) (ablocks B lyc Sc) -> In (q, m) (ablocks B ly3 S3)) /\
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S3)) /\
  (forall c q, frame_addr ly3 c q = frame_addr lyc c q).

Lemma em_cstr_keep : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    ly3 S3 (W3 : world pa_segs) m3 md3 slo shi (E : Z -> Prop) (regs : bvmap 5 word) K p (s : list byte),
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR pa_segs B ly3 S3 W3 m3 md3 -> em_later lyc Sc ly3 S3 ->
  slo mod 8 = 0 -> shi mod 8 = 0 ->
  akept pa_segs B lyc Sc W memc W3 m3 slo shi E -> fmiss lyc Sc E ->
  (forall a, p <= a <= p + Z.of_nat (length s) -> akb pa_segs B lyc Sc slo shi a) ->
  (forall a, p <= a <= p + Z.of_nat (length s) -> ~ E a) ->
  acstr_at pa_segs (rdW W memc) p s -> astr_rt_ok pa_segs regs K (rdW W memc) p s ->
  acstr_at pa_segs (rdW W3 m3) p s /\ astr_rt_ok pa_segs regs K (rdW W3 m3) p s.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly3 S3 W3 m3 md3 slo shi E regs K p s
    HJ HAR3 (Elo & Ehi & Hbl & Hfr & Hfa) Hslo Hshi HK HfE Hakb HnE Hac Hrt.
  pose proof (ajournal_gx_AR pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof HJ as HR. eapply ajournal_gx_row in HR. destruct HR as (Hlo & Hhi & _ & _).
  assert (Hv : forall a, p <= a <= p + Z.of_nat (length s) ->
    aview pa_segs (w_H W3) m3 a = aview pa_segs (w_H W) memc a).
  { intros a Ha. eapply akept_akb_gx; [exact HJ | exact HK | exact (Hakb a Ha) | exact (HnE a Ha)]. }
  split.
  { apply (em_acstr_move (w_H W) (w_H W3) memc m3); [|exact Hac]. exact Hv. }
  destruct Hrt as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  destruct (shadow_transport_akb pa_segs B LAWS TB pa_img_range lyc Sc W memc mdc ly3 S3 W3 m3 md3 slo shi E p
    (Z.of_nat (length s) + 1) HAR HAR3 Elo Ehi Hbl HK HfE ltac:(lia) ltac:(intros a Ha; apply Hakb; lia) R4 R5)
    as (Ra & Rh).
  split; [exact Ra|]. split; [exact Rh|].
  split; [|exact R7].
  intros b Hb.
  exact (tail_vis_transport pa_segs B LAWS pa_img_range em_segs_rom lyc Sc W memc ly3 S3 W3 m3 md3 slo shi E
    (p + Z.of_nat (length s)) b HAR3 Hlo Hhi Hslo Hshi Hbl Hfr Hfa HK (Hakb (p + Z.of_nat (length s)) ltac:(lia)) Hb (R6 b Hb)).
Qed.

(* the %s strings of the vararg registers *)
Lemma em_args_keep : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    ly3 S3 (W3 : world pa_segs) m3 md3 slo shi (E : Z -> Prop) (regs : bvmap 5 word) K f rs args,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR pa_segs B ly3 S3 W3 m3 md3 -> em_later lyc Sc ly3 S3 ->
  slo mod 8 = 0 -> shi mod 8 = 0 ->
  akept pa_segs B lyc Sc W memc W3 m3 slo shi E -> fmiss lyc Sc E ->
  (forall a, apf_rd rs args a -> akb pa_segs B lyc Sc slo shi a) ->
  (forall a, apf_rd rs args a -> ~ (f <= a < f + AMF_BLOCK) -> ~ E a) ->
  apf_args_ok pa_segs regs K (rdW W memc) f rs args ->
  apf_args_ok pa_segs regs K (rdW W3 m3) f rs args.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly3 S3 W3 m3 md3 slo shi E regs K f rs args
    HJ HAR3 HL Hslo Hshi HK HfE.
  revert rs. induction args as [|a args IH]; intros rs Hakb HnE Hok; [destruct rs; exact I|].
  destruct rs as [|r rs]; [destruct Hok|].
  destruct Hok as (Ha & Hr). split.
  - destruct a as [v|u|s]; cbn [apf_arg_ok] in *; [exact Ha | exact Ha|].
    destruct Ha as (Hs & Hc & Hrt & Hap).
    assert (Hin : forall x, bv_unsigned r <= x <= bv_unsigned r + Z.of_nat (length (map (Z_to_bv 8) s)) ->
      apf_rd (r :: rs) (printf_facts_c.APtr s :: args) x).
    { intros x Hx. rewrite length_map in Hx. cbn [apf_rd]. left. exact Hx. }
    destruct (em_cstr_keep G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly3 S3 W3 m3 md3 slo shi E
      regs K (bv_unsigned r) (map (Z_to_bv 8) s) HJ HAR3 HL Hslo Hshi HK HfE
      ltac:(intros x Hx; exact (Hakb x (Hin x Hx)))
      ltac:(intros x Hx; apply (HnE x (Hin x Hx)); rewrite length_map in Hx; unfold apart in Hap; lia)
      Hc Hrt) as (Hc' & Hrt').
    split; [exact Hs|]. split; [exact Hc'|]. split; [exact Hrt'|]. exact Hap.
  - apply IH; [| |exact Hr].
    + intros x Hx. apply Hakb. destruct a as [v|u|s]; cbn [apf_rd]; [exact Hx | exact Hx | right; exact Hx].
    + intros x Hx. apply HnE. destruct a as [v|u|s]; cbn [apf_rd]; [exact Hx | exact Hx | right; exact Hx].
Qed.

End b.
End a.
