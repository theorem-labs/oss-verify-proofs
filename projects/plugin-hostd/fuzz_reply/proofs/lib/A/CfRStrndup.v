(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: plugin-hostd/fuzz_reply.asan, the cf allocator bridge, part 5: the STRNDUP rule of the `_x`
   journal at top_x's instance, from the cf strndup contract astrndup_realizes_cf (Reusable/YG0dcf.v), taken as a
   hypothesis.  The leaf is the layer's (Reusable/YG0dcf.v astrndup_realizes_cf (pc mid), the measured text):
   its universe premise is `admits (as_universe B) (adup_trace_cf ly (pc_malloc_ra0 code) mid regs ch) S` and malloc_cf
   runs at that trace (the interceptor's own frame at return site mid, as fuzz_command's adup_trace; image A: 0x427b8);
   src_ok / range_addressable are at extent Z.min n (k + 1); the source lies in a live block past its hidden head; the
   entry's sp leaves room for the interceptor's and the malloc body's frames (ly_bot + STRNDUP_FRAME_CF +
   MALLOC_BODY_FRAME_CF < sp).  The rule (W_journal_x.v astrndup_cf_rule_c_x) gives each: frame0_ok, the live block,
   the frame room.
   1. strndup_adup_in_U: at the rule's caller context (CTX_strndup, A/ACej.v:10) and frame0_ok the leaf's trace is
      [0x5408c; 0x427b8; 0x838e4] or, when adup's stop rules fire, [0x5408c]; both are fixed traces of the universe
      (u_fix (as_universe TfibB) = Tfib_universe, ACej.v:230-231).  aj_strndup_at_x_ct turns that membership into the
      leaf's admission by YG01.admits_fix (universe_ok from ARcf), as YGcallx's rules do.
   2. aj_strndup_at_x_ct: the journal-level call-site rule of strndup, the twin of Reusable/YGcallx.v:1062
      aj_malloc_at_x_ct at the shared cf shape (ARxs, QMm_cf, xs_cf), written as A/CfRBridgeAjRealloc.v's
      aj_realloc_null_at_x_ct is: the call's pre, amreal_SRr04 + SRr_mono over the model facts of malloc_cf (k + 1)
      (alloc_model_laws_x_cf), acall_post_journal_xw, ajournal_x_nil_pst + ajournal_x_sub, acall_kept_of_journal_x.
      Its post adds, on the success arm, the leaf's copy of the k source bytes and the NUL at the result.
   3. ASTRNDUP_x_room / ASTRNDUP_x_room_of_cf: the rule at top_x's ARX with the room record's two fields abstract (RM,
      CNT), in CfRBridgeRules.v Section B's / Section R's frame; the leaf at k := n (Z.min n (n + 1) = n; first_byte
      from the rule's no-NUL premise, src_ok from it and the stack exclusion with ESTACK <= ASTACK, the live block from
      the rule's source-block premise with hd_skip [] = 0 at ARX), the NULL arm excluded by
      CfRBridgePrim.malloc_cf_granted_not_null, the tick by CfRBridgeNev.malloc_cf_block_nev, the room after the call by
      YGcfRoomLive.room_live_call_keep, errno and the image bytes as ARE_x_room_of_cf; the meter MT generic, its mo_le
      post from nsec_cf's malloc step and MO_LE_M (CfRBridgeRules.v's KF-COUNT hypotheses).  The call's memory facts
      as CfRBridgeRules.v's rules (QMm): top_x's ARX carries arodata_ok_cf as its LAST conjunct (W1),
      projected at the call into QMm_cf and re-established at the post by CfRBridgeRules.arodata_post_keep (the new
      block is off the image); QMm_cf's hull conjunct from the rule's mo_ok premise (MO_OK_HULL_M); the unit rows
      HRS / HER.
   4. ASTRNDUP_x_kf: the fit at top_x's instance (RPi := RP_cf, MMAX := fr_MMAX, CTX_strndup, the strndup pc of the
      listing) at the KF meter MT (MT_sec's defining equations and MT_ok), as CfRBridgeRules.AMA_x_kf.
      The fits at the trivial meter ameter_triv (ASTRNDUP_x_cf, ASTRNDUP_x_cf_all) are deleted: its mo_ok cannot give
      the hull admission (as CfRBridgeRules' fits at ameter_triv).
   No function is proved (rule 24). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* the strndup pc of the listing (top_x's text `@pa_sigma _ fr_prog_listing PB_fr WS_strndup`) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_kit W_listing W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YGcfRoomPre YGcfXs YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomLive YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x CfParamsReply AD2l ACej CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfRBridgePrim CfRBridgeNev CfRBridgeRules.
(* Required, not Imported: the xs write-set lemma of the realloc rules, cited by qualified name *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CfRBridgeAjRealloc.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The leaf's trace at the rule's call site.                                   *)
Lemma adup_pc0_TfibB : pc_malloc_ra0 (as_code TfibB) = 0x5408c.
Proof. vm_compute. reflexivity. Qed.

(* CTX_strndup = [[0x838e4]] fixes raZ regs = 0x838e4 and ch = []; on frame0_ok the trace is the interceptor's malloc
   site, its own return site 0x427b8 and the drain's 0x838e4 (K0's edge CTX_strndup -0x427b8-> CTX_AMALLOC), else
   (a stop rule) [0x5408c] *)
Lemma strndup_adup_in_U : forall ly regs ch,
  In (raZ regs :: spine ch) CTX_strndup -> frame0_ok ly regs = true ->
  In (adup_trace_cf ly (pc_malloc_ra0 (as_code TfibB)) 0x427b8 regs ch) (as_universe TfibB).
Proof.
intros ly regs ch Hc Hf.
destruct Hc as [Hc | []]. injection Hc as Hra Hsp.
destruct ch as [|r ch]; [|cbn in Hsp; discriminate Hsp].
unfold adup_trace_cf. rewrite Hf, adup_pc0_TfibB.
change (u_fix (as_universe TfibB)) with Tfib_universe.
destruct (_ || _ || _).
- apply memZL_In. vm_compute. reflexivity.
- rewrite <- Hra. apply memZL_In. vm_compute. reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The call-site rule of strndup, at the shared cf shape (YGcallcf.v:252-394). *)
Section SD. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Hypothesis L : AR_laws_cf segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis HU : universe_ok (as_universe B).
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).
Local Abbreviation LAWS := (AR_laws_x_xs segs B L).
Local Abbreviation OWNLOW := (ARx_owned_low_law_xs segs B L).
Local Abbreviation WFL := (ARx_wf_law_xs segs B).
Local Abbreviation LBLK := (alx_blocks segs B ARxs LAWS).
Local Abbreviation LLAY := (alx_layout segs B ARxs LAWS).

(* YGcallx.v:1062 aj_malloc_at_x_ct over astrndup_realizes_cf (tree malloc_cf (m + 1) at the adup trace, leaf
   strndup_leaf_cf); m is the copied length (the leaf's k), x / n the source and its bound. *)
Lemma aj_strndup_at_x_ct : forall (pc mid : Z),
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x n m (o : Z) raw ch,
astrndup_realizes_cf segs B pc mid ->
ajournal_x segs B PST ARxs STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= m <= n -> m + 1 < cf_malloc_max -> blocks_bytes Sc + (m + 1) <= LIVE_MAX ->
first_byte segs W memT x n 0 m -> src_ok segs W regsT memT x (Z.min n (m + 1)) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (Z.min n (m + 1)) ->
(exists q mq, In (q, mq) (ablocks B lyc Sc) /\ q + hd_skip Hpc q <= x /\ x + Z.min n (m + 1) <= q + req_size mq) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
ly_bot lyc + STRNDUP_FRAME_CF + MALLOC_BODY_FRAME_CF < spZ regsT ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm_cf segs B Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (adup_trace_cf lyc (pc_malloc_ra0 (as_code B)) mid regsT ch) (as_universe B) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARxs STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
(exists p trc, apath (malloc_cf (m + 1) (adup_trace_cf lyc (pc_malloc_ra0 (as_code B)) mid regsT ch) Sc) trc (p, S2) /\
 YG0d.gflag trc = true /\
 strndup_leaf_cf segs B lyc Sc Hpc W regsT memT mdc x m (p, S2) W2 c2 /\
 (p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p) /\
 (p <> PNull -> (forall i, 0 <= i < m -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) memT (x + i)) /\
   aview segs (w_H W2) mem2 (res + m) = Some 0) /\
 (p <> PNull -> forall i, 0 <= i < 4 -> mem2 (w64 (as_errno B + i)) = memT (w64 (as_errno B + i))) /\
 (forall w : word, ~ aowned B lyc Sc (bv_unsigned w) -> ~ aowned B ly2 S2 (bv_unsigned w) ->
  ~ ascratch B ASTACK regsT (bv_unsigned w) ->
  ~ ((p <> PNull /\ res <= bv_unsigned w < res + req_size (m + 1)) \/ Exists (in_zr (bv_unsigned w)) (xs_cf lyc Sc ++ xs_cf ly2 S2)) ->
  mem2 w = memT w)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
 \/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, m + 1)] /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size (m + 1))))).
Proof.
intros pc mid W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x n m o raw ch
AS HJ Hx0 Hn0 Hn Hx Hm Hmax Hlive Hfb Hsrc Hra0 Hblk Hsp' Hal Hneg Hbud Hroom Hgp Htp Hra Hraw HQM Hch Htr.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact HQM]. }
destruct (proj1 (acall_pre_x_xs segs B lyc Sc Hpc W regsT memT mdc ch) HPRE) as [HPREcf HXc].
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
assert (AMX : alloc_model_laws_x B QM_cf malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)))
  by exact (alloc_model_laws_x_cf B HU).
pose proof (admits_fix _ _ Sc HU Htr) as Htr'.
pose proof (amx_malloc _ _ _ _ _ _ AMX Sc (m + 1) (adup_trace_cf lyc (pc_malloc_ra0 (as_code B)) mid regsT ch)
  HWF (QMQ_cf segs B Sc memT HQM) ltac:(lia) Hlive Htr') as (HSAFE & HPROG & HNSP & HMP).
pose proof (AS lyc Sc Hpc W regsT memT mdc x n m ch HPREcf Hroom Hx0 Hn0 Hn Hx Hm Hmax Hlive Hfb Hsrc Hra0 Hblk Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (HMP tr r Hpath) as HQ. destruct r as [p S2]. unfold malloc_post_x in HQ.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & Hbl).
pose proof Hleaf as Hleaf0.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOSTcf & Hres & HQT2 & Hcopy & HERR & HX2 & Herrno & Hrawf).
cbn [fst snd] in Hres, HQT2, Hcopy, HERR, HX2, Herrno, Hrawf.
assert (HPOST : acall_post_x segs B ARxs ASTACK lyc Sc Hpc W regsT memT mdc
  (fun a => (p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size (m + 1))
    \/ Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly2 S2)) ly2 S2 W2 regs2 mem2 md2).
{ destruct HPOSTcf as [HA2 R2]. exact (conj (conj HA2 HX2) R2). }
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (LLAY _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
destruct (asptr_null_dec p) as [-> | Hnn].
-
cbn in Hres.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite Hbl. apply map_ext_in. exact Efc. }
assert (HJ1 : ajournal_x segs B [] ARxs ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply (acall_post_journal_xw segs B ARxs LAWS segs_low errno_low OWNLOW lyc Sc Hpc W regsT memT mdc ly2 S2 W2 regs2 mem2 md2 _
(fun a => Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly2 S2)) [] (st_nev S2 - st_nev Sc));
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2].
- intros a Ha. apply (CfRBridgeAjRealloc.cfr_aj_xs_write_ok segs B L lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a HAR HAR2 Hly2);
[intros b m' Hb; left; rewrite Eab2; exact Hb | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha].
- intros a [[Hf _] | Hxa]; [exfalso; exact (Hf eq_refl) | left; exact Hxa].
- intros q m' i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. exact Hq. }
exists ly2, S2, regs2, mem2, md2, 0.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_sub segs B PST ARxs LAWS segs_low);
[exact HJ | exact (ajournal_x_nil_pst segs B ARxs PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|].
split.
{ exists PNull, tr. split; [exact Hpath|]. split; [exact Hgf|]. split; [exact Hleaf0|].
split; [split; intros _; reflexivity|].
split; [intros Hc; exfalso; exact (Hc eq_refl)|]. split; [intros Hc; exfalso; exact (Hc eq_refl)|].
split; [intros Hc; exfalso; exact (Hc eq_refl)|].
intros w H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 |].
intros [[Hc _]|Hxa]; [exact (Hc eq_refl) | apply H4; right; exact Hxa]. }
left. split; [reflexivity|]. split; [exact Eab2|].
split.
{ rewrite Hsp' in HJ1. eapply (acall_kept_of_journal_x segs B ARxs segs_low);
[exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m' i Hb Hi _. rewrite Eab2. exact Hb. }
exact (HERR eq_refl).
-
assert (Hbl' : blocks S2 = blocks Sc ++ [(p, m + 1)]).
{ destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
clear Hbl.
set (res := sptr_addr B ly2 p) in *.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, m + 1)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, m + 1)]). rewrite Hbl', map_app. cbn [map].
f_equal. apply map_ext_in. exact Efc. }
assert (Hnew : In (res, m + 1) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (LBLK ly2 S2 Hpc W2 mem2 md2 res (m + 1) HAR2 Hnew) as (_ & Hr4096 & _).
assert (Hdisj : forall b m' a, In (b, m') (ablocks B lyc Sc) -> b <= a < b + req_size m' ->
  ~ (res <= a < res + req_size (m + 1))).
{ intros b m' a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos_x segs B ARxs LAWS ly2 S2 Hpc W2 mem2 md2 (b, m') (res, m + 1) b1 b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HJ1 : ajournal_x segs B [] ARxs ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply (acall_post_journal_xw segs B ARxs LAWS segs_low errno_low OWNLOW lyc Sc Hpc W regsT memT mdc ly2 S2 W2 regs2 mem2 md2 _
(fun a => Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly2 S2)) [] (st_nev S2 - st_nev Sc));
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2].
- intros a Ha. apply (CfRBridgeAjRealloc.cfr_aj_xs_write_ok segs B L lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a HAR HAR2 Hly2);
[intros b m' Hb; left; rewrite Eab2; apply in_or_app; left; exact Hb | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha].
- intros a [[_ Ha] | Hxa]; [right | left; exact Hxa].
exists res, (m + 1). split; [right; exact Hnew|]. split; [exact Ha|]. right.
intros Hold. exact (Hdisj res (m + 1) a Hold Ha Ha).
- intros q m' i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. apply in_or_app. left. exact Hq. }
exists ly2, S2, regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_sub segs B PST ARxs LAWS segs_low);
[exact HJ | exact (ajournal_x_nil_pst segs B ARxs PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|].
split.
{ exists p, tr. split; [exact Hpath|]. split; [exact Hgf|]. split; [exact Hleaf0|].
split; [split; [intros Hc; exfalso; exact (Hnn Hc) | intros Hc; zlia]|].
split; [intros _; reflexivity|]. split; [exact Hcopy|]. split; [exact Herrno|].
intros w H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 | exact H4]. }
right. split; [exact Hr4096|]. split; [exact Eab2|].
rewrite Hsp' in HJ1. eapply (acall_kept_of_journal_x segs B ARxs segs_low);
[exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m' i Hb Hi _. rewrite Eab2. apply in_or_app. left. exact Hb.
Qed.
End SD.

(* ---------------------------------------------------------------------------- *)
(* 3. The strndup rule, in the ruled text (W_journal_x.v astrndup_cf_rule_c_x, with frame0_ok) at top_x's         *)
(*    instance, the room record's fields RM / CNT abstract (CfRBridgeRules.v Section B's frame).                     *)
Section RS. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_reply.
Variable segs : list Segment.
Hypothesis L : AR_laws_cf segs TfibB.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs TfibB.
Variable RM : astate -> nat -> Prop.
Variable CNT : list (Z * Z) -> Prop.
Hypothesis HRM : RM = fun S _ => room_live_cf S.
Hypothesis HCNT : forall l, CNT l -> cb_cf l.
(* The meter, as CfRBridgeRules.v Section R's (KF-COUNT): MT is generic; the mo_le post follows from the cf model's count of
   granted secondary entries nsec_cf through MT's arithmetic fact MO_LE_M (strndup's tree is malloc_cf (n + 1)); at
   MT_sec from its defining equations (ASTRNDUP_x_kf). *)
Variable MT : ameter_ops.
Variable nsec_cf : astate -> Z.
Hypothesis nsec_malloc_cf : forall n tr s,
  cfx_ipost (malloc_cf n tr s) (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Hypothesis MO_LE_M : forall s s' n, 0 <= n -> nsec_cf s' <= nsec_cf s + (if from_primary n then 0 else 1) ->
  mo_le MT s s' (mo_malloc MT n).
(* As CfRBridgeRules.v Section B's: the hull admission from the rule's count premise, the unit's two image rows. *)
Hypothesis MO_OK_HULL_M : forall s n, 0 <= n -> mo_ok MT s (mo_malloc MT n) -> cf_hull_ok s.
Hypothesis HRS : relro_seg_t segs.
Hypothesis HER : errno_relro_t TfibB.
(* top_x's relation after W1 (W_LLVMFuzzerTestOneInput_top_x.v Definition ARX: arodata_ok_cf LAST) *)
Local Abbreviation ARX := (fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @arodata_ok_cf CfImg_A segs TfibB mem).
Local Abbreviation ARxs := (fun ly S Hp (W : world segs) mem md => ARcf segs TfibB ly S Hp W mem md /\ xs_placed_cf ly S).

Definition ASTRNDUP_x_room (pc : Z) : Prop :=
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x n (o : Z) raw ch (kr : nat),
ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 n -> 0 < x -> 0 <= n -> x + n <= 2 ^ 63 ->
n + 1 < fr_MMAX -> blocks_bytes Sc + (n + 1) <= LIVE_MAX ->
CNT (ablocks TfibB lyc Sc) ->
(forall i, 0 <= i < n -> exists b, aview segs (w_H W) memT (x + i) = Some b /\ b <> 0) ->
(forall a, x <= a < x + n -> ~ (sp0 + o - ASTACK <= a < sp0 + o)) ->
amem_range x n -> range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
(exists p m, In (p, m) (ablocks TfibB lyc Sc) /\ p <= x /\ x + n <= p + req_size m) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
ly_bot lyc + 4096 < spZ regsT ->
ly_bot lyc + STRNDUP_FRAME_CF + MALLOC_BODY_FRAME_CF < spZ regsT ->
getr regsT 3 = w64 (as_gp TfibB) -> getr regsT 4 = w64 (as_tp TfibB) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
frame0_ok lyc regsT = true ->
In (raZ regsT :: spine ch) CTX_strndup ->
RM Sc (1 + kr) ->
mo_ok MT Sc (mo_malloc MT (n + 1)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks TfibB ly2 S2 = ablocks TfibB lyc Sc ++ [(res, n + 1)] /\
(forall i, 0 <= i < n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) memT (x + i)) /\
aview segs (w_H W2) mem2 (res + n) = Some 0 /\
acall_kept segs TfibB lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size (n + 1)) /\
mo_le MT Sc S2 (mo_malloc MT (n + 1)) /\
RM S2 kr /\
(forall i, 0 <= i < 4 -> aview segs (w_H W2) mem2 (as_errno TfibB + i) = aview segs (w_H W) memT (as_errno TfibB + i)) /\
(forall a, in_img segs a -> ~ aowned TfibB lyc Sc a -> ~ aowned TfibB ly2 S2 a ->
 ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
 ~ (res <= a < res + req_size (n + 1)) -> apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).

Theorem ASTRNDUP_x_room_of_cf : forall pc, astrndup_realizes_cf segs TfibB pc 0x427b8 -> ASTRNDUP_x_room pc.
Proof.
intros pc AS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x n o raw ch kr
  HJ Hx0 Hn0 Hx Hn Hxn Hmax Hlive HCB Hbytes Hnostk Hamr Hra0 Hhull HSRC Hsp Hal Hneg Hbud Hpfx Hroom Hgp Htp Hra Hraw Hch
  Hf0 HCTX HRL HMO.
destruct (HCNT _ HCB) as (Hc1 & Hc2 & Hc3). rewrite HRM in HRL. cbv beta in HRL.
pose proof HJ as ([HARc [HHp HAD]] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
subst Hpc.
pose proof (proj1 (count_block_iff_cfr TfibB lyc Sc) (conj Hc1 (conj Hc2 Hc3))) as (HSEC & H24 & HB24 & HPRIM).
pose proof (room_live_room Sc HRL) as HROOM.
(* the call's QMm_cf: the room, the hull admission from the count premise, ARX's arodata *)
pose proof (MO_OK_HULL_M Sc (n + 1) ltac:(lia) HMO) as HHULL.
pose proof (QMm_cf_of_room segs TfibB lyc Sc [] W memT mdc HARc HQT HROOM HHULL HAD) as HQM.
pose proof (universe_ok_of_ARcf segs TfibB lyc Sc [] W memT mdc HARc) as HU.
pose proof (amc_wf _ _ _ _ _ (proj1 HARc)) as HWF.
pose proof (aj_to_xs segs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJx.
assert (HARxs : ARxs lyc Sc [] W memT mdc) by exact (conj HARc (xs_placed_of_ARcf segs TfibB lyc Sc [] W memT mdc HARc)).
(* the leaf's premises at k := n *)
pose proof (strndup_adup_in_U lyc regsT ch HCTX Hf0) as Htr.
assert (Hn' : 0 <= n < 2 ^ 63) by lia.
assert (Hkn : 0 <= n <= n) by lia.
assert (Hmax' : n + 1 < cf_malloc_max) by exact Hmax.
assert (Hfb : first_byte segs W memT x n 0 n).
{ split; [lia|]. split; [exact Hbytes|]. intros Hc. exfalso. lia. }
assert (Emin : Z.min n (n + 1) = n) by lia.
assert (Hsrc : src_ok segs W regsT memT x (Z.min n (n + 1))).
{ rewrite Emin. intros a Ha. destruct (Hbytes (a - x) ltac:(lia)) as (b & Hb & _).
  replace (x + (a - x)) with a in Hb by lia.
  split; [rewrite Hb; discriminate|].
  intros Hs. apply (Hnostk a Ha). rewrite Hsp in Hs. unfold ESTACK, ASTACK in *. lia. }
assert (Hra0' : range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (Z.min n (n + 1))) by (rewrite Emin; exact Hra0).
(* the source's live block (the rule's premise; at ARX the ghost set is [], so no hidden head) *)
assert (Hblk : exists q mq, In (q, mq) (ablocks TfibB lyc Sc) /\ q + hd_skip [] q <= x /\
  x + Z.min n (n + 1) <= q + req_size mq).
{ destruct HSRC as (q & mq & Hin & Hlo & Hhi). exists q, mq. rewrite hd_skip_nil, Emin.
  split; [exact Hin|]. split; lia. }
pose proof (aj_strndup_at_x_ct segs TfibB [] L segs_low errno_low HU pc 0x427b8
  W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc [] mdc k x n n o raw ch AS HJx Hx0 Hn0 Hn' Hx Hkn Hmax' Hlive
  Hfb Hsrc Hra0' Hblk Hsp Hal Hneg Hbud Hroom Hgp Htp Hra Hraw HQM Hch Htr) as HSR.
eapply SRr_mono; [exact HSR|].
intros W2 c2 HwleW (ly2 & S2 & regs2 & mem2 & md2 & res & Hc2' & HJ2 & Hpres & Hres & Hfrs & HPRE &
  (p & trc & Hpath & Hgf & Hleaf & Hiff & Hres2 & Hcopy & Herrno & Hrawf) & Harms).
assert (Hpn : p <> PNull)
  by exact (malloc_cf_granted_not_null (as_universe TfibB) Sc (n + 1) _ trc (p, S2) HWF HQT HPRIM Hpath Hgf).
destruct Harms as [(Hr0 & _) | (H4096 & Eab & Hkept)]; [exfalso; apply Hpn; apply Hiff; exact Hr0|].
pose proof (malloc_cf_block_nev (n + 1) _ Sc trc p S2 Hpath Hpn) as Hnev.
pose proof HJ2 as (HA2 & _).
pose proof HPRE as (_ & _ & _ & Hslo & _).
destruct (Hcopy Hpn) as (Hcp & Hnul).
(* the post's arodata (ARX's last conjunct at the post), from the leaf's raw frame: the new block is off the image *)
assert (HAD2 : arodata_ok_cf segs TfibB mem2).
{ apply (arodata_post_keep segs TfibB lyc Sc [] W regsT memT mdc ly2 S2 [] W2 mem2 md2
    (fun z => (p <> PNull /\ res <= z < res + req_size (n + 1)) \/ Exists (in_zr z) (xs_cf lyc Sc ++ xs_cf ly2 S2))
    HRS HER HARc (proj1 HA2) Hslo); [| |exact HAD].
  - intros a I1 I2 X1 X2 [[_ Hb] | Hxs].
    + assert (Hinab : In (res, n + 1) (ablocks TfibB ly2 S2)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
      exact (ablock_not_img_cfr TfibB ly2 S2 [] _ res (n + 1) a (proj1 (proj1 HA2)) Hinab I2 Hb).
    + apply Exists_app in Hxs as [Hxs|Hxs]; [exact (X1 Hxs) | exact (X2 Hxs)].
  - intros w NX. apply Hrawf; intros H; apply NX; tauto. }
exists ly2, S2, [], regs2, mem2, md2, res.
split; [exact Hc2'|].
split.
{ apply (aj_of_xs segs); [reflexivity | exact HAD2 |]. replace (k + 1) with (k + (st_nev S2 - st_nev Sc)) by lia. exact HJ2. }
split; [exact Hpres|]. split; [exact Hres|]. split; [exact Hfrs|]. split; [exact H4096|]. split; [exact Eab|].
split; [exact Hcp|]. split; [exact Hnul|].
split; [exact Hkept|].
split; [exact (MO_LE_M Sc S2 (n + 1) ltac:(lia) (cfx_ipost_apath _ _ trc (p, S2) (nsec_malloc_cf (n + 1) _ Sc) Hpath))|].
split.
{ rewrite HRM. exact (room_live_call_keep (as_universe TfibB) 1024 (2 ^ 15) Sc S2 HWF HQT HSEC H24 HB24 HRL
    (or_introl (ex_intro _ (n + 1) (ex_intro _ _ (ex_intro _ trc (ex_intro _ p Hpath)))))). }
split.
{ intros i Hi. apply (aview_img_eq segs segs_low).
  - exact (proj1 (proj2 errno_low) (as_errno TfibB + i) ltac:(lia)).
  - exact (Herrno Hpn i Hi). }
intros a Hi Ho1 Ho2 He Hb.
apply (img_present_keep segs L segs_low lyc Sc W regsT memT mdc ly2 S2 W2 mem2 md2
  (fun z => p <> PNull /\ res <= z < res + req_size (n + 1)) a HARxs HA2 Hslo); [| | exact Hi | exact Ho1 | exact He].
+ intros w H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 |].
  intros [Hw | Hw]; apply H4; [left; exact Hw | right; exact Hw].
+ intros [_ Hres1] _. exact (Hb Hres1).
Qed.
End RS.

(* ---------------------------------------------------------------------------- *)
(* 4. KF-COUNT, at top_x's instance of the room record (CfRBridgeRules.v RP_cf, cnt_ok_cb_cf) and the strndup pc of  *)
(*    the listing: the rule at a meter MT given by MT_sec's defining equations, CfRBridgeRules.v Section TOPK's frame  *)
(*    (its Section hypotheses with their exact texts; the meter facts by its kf_MO_LE_M / kf_MO_OK_HULL_M), as        *)
(*    AMA_x_kf.  The FIT CHECK: it type-checks only if ASTRNDUP_x_room is the landed rule at RP_cf.                     *)
Section TOPKS. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_reply.
Variable segs : list Segment.
Hypothesis L : AR_laws_cf segs TfibB.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs TfibB.
Local Abbreviation ARX := (fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @arodata_ok_cf CfImg_A segs TfibB mem).
(* FIT CHECK of the relation: the rules' ARX is top_x's relation after W1, whose text is quoted
   here VERBATIM from commit b27e847023f8, lib/A/W_LLVMFuzzerTestOneInput_top_x.v:171-172
   (Definition ARX's body); it closes by reflexivity only if the two are the same term. *)
Goal ARX = (
  fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_A segs TfibB mem).
Proof. reflexivity. Qed.
Variable MT : ameter_ops.
Variable nsec_cf : astate -> Z.
Hypothesis nsec_malloc_cf : forall n tr s,
  cfx_ipost (malloc_cf n tr s) (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, cfx_ipost (free_cf p tr s) (fun r => nsec_cf (snd r) <= nsec_cf s).
Hypothesis MT_malloc : forall n, mo_malloc MT n = if 64512 <? n then 1 else 0.
Hypothesis MT_free : mo_free MT = 0.
Hypothesis MT_le : forall s s' m, mo_le MT s s' m <-> nsec_cf s' <= nsec_cf s + m.
Hypothesis MT_ok : forall s m, mo_ok MT s m <-> YGcfNames.nsec_cf s + m <= cf_kmax.
Hypothesis HRS : relro_seg_t segs.
Hypothesis HER : errno_relro_t TfibB.

Theorem ASTRNDUP_x_kf :
  astrndup_realizes_cf segs TfibB (@pa_sigma _ fr_prog_listing PB_fr WS_strndup) 0x427b8 ->
  astrndup_cf_rule_c_x segs TfibB [] ARX MT fr_MMAX RP_cf CTX_strndup (@pa_sigma _ fr_prog_listing PB_fr WS_strndup).
Proof.
intros AS. eapply (ASTRNDUP_x_room_of_cf segs L segs_low errno_low (rp_RM RP_cf) (cnt_ok RP_cf) eq_refl cnt_ok_cb_cf
  MT nsec_cf); first [exact AS | exact nsec_malloc_cf | exact (kf_MO_LE_M MT nsec_cf MT_malloc MT_le)
  | exact (kf_MO_OK_HULL_M MT MT_malloc MT_ok) | exact HRS | exact HER].
Qed.
End TOPKS.

Print Assumptions strndup_adup_in_U.
Print Assumptions aj_strndup_at_x_ct.
Print Assumptions ASTRNDUP_x_room_of_cf.
Print Assumptions ASTRNDUP_x_kf.
