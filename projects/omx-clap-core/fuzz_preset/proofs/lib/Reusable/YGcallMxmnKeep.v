(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the KEEP-CARRYING allocator call rules: a walk's malloc / free call yields
   `MN.memnorm segs memT -> MN.memnorm segs mem2` (call memory to return memory) from the keep contracts of
   YGcfMallocComposeKeep.v.  rule 24: proves no function (kind: engine lemmas).
   Each rule is its YGcallMxmn.v original's statement with the keep as the LAST conclusion conjunct, the position the
   _m rules had before field round 3 part 3c, and with the callee text replaced by its keep form.
   1. FREE under the re-hide (aj_free_x_ct_m_rh_keep / aj_free_at_x_ct_m_rh_keep, twins of YGcallMxmn's
      aj_free_x_ct_m_rh / aj_free_at_x_ct_m_rh): the generic free rules YGcallMxmn.aj_free_x_ct_mR /
      aj_free_at_x_ct_mR read the callee's call post APOST, so they are used as they are, at APOST := APOST_cf_keep
      (YGcallcf.APOST_cf with the keep); its two laws follow from APOST_cf's (POST_AR_cf, POST_J_cf) by projection,
      and the text at it comes from YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (afree_realizes_x_cf_rh_keep, the
      twin of YGcallcf.afree_realizes_x_cf_rh).
   2. MALLOC (aj_malloc_x_ct_m_keep / aj_malloc_at_x_m_keep / aj_malloc_x_m_keep, twins of YGcallMxmn's
      aj_malloc_x_ct_m / aj_malloc_at_x_m / aj_malloc_x_m): YGcallx's malloc leaf names no callee post, and SRr is
      continuation-passing, so no instance of the original rules carries a further fact of the leaf to the post.
      aj_malloc_at_x_ct_m_keep is YGcallx.aj_malloc_at_x_ct's proof (at wle) over the keep text amalloc_realizes_x_keep
      (YGcallx.amalloc_realizes_x with the keep at the leaf's end configuration), reading the keep off the leaf; the
      three walk rules are its wrappers, as in YGcallx.  amalloc_realizes_x_xs_keep (the twin of
      YGcallcf.amalloc_realizes_x_xs) gives the keep text at ARxs from YGcfMallocComposeKeep.amalloc_realizes_cf_keep. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
(* the step relation and the allocator realization over a world relation (SRrG, amrealG) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
(* the cf instance: the forms, the primed post and its laws (YGcallcf), the keep contracts *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRehidePost YG0dcfR YGcallcf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocCompose YGcfMallocComposeKeep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module MN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YAkMemnorm.

(* ---------------------------------------------------------------------------- *)
(* 1. Malloc, generic over ARx (YGcallMxmn Section allocm's variables, in its order). *)
Section allocmk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable QM : astate -> Prop.
Variable QMm : astate -> (word -> option byte) -> Prop.
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable ft : sptr -> list Z -> YG00.M unit.
Variable WFx : astate -> Prop.
Variable XS : alayout -> astate -> list (Z * Z).
Local Abbreviation code := (as_code B).

(* YGcallx.malloc_leaf_x with the keep at its end configuration. *)
Definition malloc_leaf_x_keep (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
YGcallx.malloc_leaf_x (fx := fx) segs B ARx XS ly S Hp W regs mem md n r W' c' /\
YGcfMallocCompose.at_mem_cf segs c' (fun mem' => MN.memnorm segs mem -> MN.memnorm segs mem').

(* YGcallx.amalloc_realizes_x with that leaf. *)
Definition amalloc_realizes_x_keep : Prop :=
forall ly S Hp W regs mem md n ch,
YGcallx.acall_pre_x segs B ARx QMm ly S Hp W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < nmax -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly (pc_malloc_ra0 code) regs ch) S ->
amreal segs (mt n (call_trace ly (pc_malloc_ra0 code) regs ch) S) W
(cfg_at segs (pc_wrap_malloc code) regs mem md)
(malloc_leaf_x_keep ly S Hp W regs mem md n).

Lemma amalloc_realizes_x_of_keep : amalloc_realizes_x_keep ->
YGcallx.amalloc_realizes_x (fx := fx) segs B ARx QMm mt nmax XS.
Proof.
intros H ly S Hp W regs mem md n ch Hpre H1 H2 H3 H4.
exact (amreal_mono segs _ _ _ _ _ (fun r W' c' Hl => proj1 Hl) (H ly S Hp W regs mem md n ch Hpre H1 H2 H3 H4)).
Qed.

Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law (rc := rc) segs B ARx.
Hypothesis WFL : ARx_wf_law segs ARx WFx.
Hypothesis AMX : alloc_model_laws_x B QM mt nmax ft WFx.
Hypothesis QMQ : forall S mem, QMm S mem -> QM S.
Hypothesis XSL : ARx_xs_law (rc := rc) segs B ARx XS.

(* YGcallx.aj_malloc_at_x_ct (its R form's proof at wle) over the keep text, plus the keep. *)
Lemma aj_malloc_at_x_ct_m_keep : amalloc_realizes_x_keep ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
YGcallx.acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
YGcallx.malloc_leaf_x (fx := fx) segs B ARx XS lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
YGcallx.acall_kept_x (rc := rc) segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
YGcallx.acall_kept_x (rc := rc) segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n))) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros AMALLOC WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs. pose proof (ajx_wle HJ) as Hwle. pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs. pose proof (ajx_nev HJ) as Hnev. pose proof (ajx_k HJ) as Hk. pose proof (ajx_hi HJ) as F1. pose proof (ajx_blk HJ) as F2. pose proof (ajx_img HJ) as F3. pose proof (ajx_frm HJ) as F4. pose proof (ajx_gone HJ) as Hgone. pose proof (ajx_pres HJ) as Hpres. pose proof (ajx_stk HJ) as Hstatic. pose proof (ajx_extra HJ) as F5. pose proof (ajx_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : YGcallx.acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact HQM]. }
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
pose proof Htr as Htr'.
pose proof (amx_malloc _ _ _ _ _ _ AMX Sc n (call_trace lyc (pc_malloc_ra0 code) regsT ch) HWF (QMQ Sc memT HQM) Hn Hlive Htr')
as (HSAFE & HPROG & HNSP & HMP).
pose proof (AMALLOC lyc Sc Hpc W regsT memT mdc n ch HPRE Ha0 Hn Hlive Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf & HKP).
pose proof (amx_malloc_depot _ _ _ _ _ _ AMX Sc n (call_trace lyc (pc_malloc_ra0 code) regsT ch) HWF (QMQ Sc memT HQM) Hn Hlive Htr' tr r Hpath) as HDEP.
pose proof (HMP tr r Hpath) as HQ. destruct r as [p S2]. unfold malloc_post_x in HQ. cbn [fst snd] in HDEP.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & Hbl).
pose proof Hleaf as Hleaf0.
cbn [fst snd] in Hleaf.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & Hres & HQT2 & HERR & _).
pose proof (HKP _ _ _ _ eq_refl) as KEEP. cbv beta in KEEP.
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (alx_layout segs B ARx LAWS _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
destruct (asptr_null_dec p) as [-> | Hnn].
-
cbn in Hres.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite Hbl. apply map_ext_in. exact Efc. }
assert (HJ1 : @ajournal_xw rc SK segs B [] ARx ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
  (st_nev S2 - st_nev Sc) [call_trace lyc (pc_malloc_ra0 code) regsT ch]).
{ refine (@acall_post_journal_xw rc SK segs B ARx HL LAWS segs_low errno_low OWNLOW lyc Sc Hpc W regsT memT mdc
    ly2 S2 W2 regs2 mem2 md2 _ (fun a => Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2)) [] (st_nev S2 - st_nev Sc)
    [call_trace lyc (pc_malloc_ra0 code) regsT ch]
    HPOST HAR HstkC Hfrs2 ltac:(zlia) ltac:(zlia) Hsecs2 _ _ _ HQT2 (wild_part_step _ _ _ _ HDEP)).
- intros a Ha. apply (@xs_write_ok rc segs B ARx XS HL LAWS XSL lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a
    HAR HAR2 Hly2);
[intros b' Hb'; rewrite Eab2; exact Hb' | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha].
- intros a [[Hf _] | Hx]; [exfalso; exact (Hf eq_refl) | left; exact Hx].
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. exact Hq. }
exists ly2, S2, regs2, mem2, md2, 0.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (@ajournal_xw_sub rc SK segs B PST ARx HL LAWS segs_low);
[exact HJ | exact (@ajournal_xw_nil_pst rc SK segs B ARx PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia
| intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|]. split; [exact Htr'|].
split; [exists PNull, tr; split; [exact Hpath|]; split; [exact Hgf|]; split; [exact Hleaf0|];
split; [split; intros _; reflexivity | intros Hc; exfalso; exact (Hc eq_refl)]|].
split; [|exact KEEP].
left. split; [reflexivity|]. split; [exact Eab2|].
split.
{ rewrite Hsp' in HJ1.
eapply (@acall_kept_of_journal_x rc SK segs B ARx segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb. }
exact (HERR eq_refl).
-
assert (Hbl' : blocks S2 = blocks Sc ++ [(p, n)]).
{ destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
clear Hbl.
set (res := sptr_addr B ly2 p) in *.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, n)]). rewrite Hbl', map_app. cbn [map].
f_equal. apply map_ext_in. exact Efc. }
assert (Hnew : In (res, n) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B ARx LAWS ly2 S2 Hpc W2 mem2 md2 res n HAR2 Hnew) as (_ & Hr4096 & _).
assert (Hdisj : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (res <= a < res + req_size n)).
{ intros b m a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
pose proof (@sep_blocks_pos_x rc segs B ARx HL LAWS ly2 S2 Hpc W2 mem2 md2 (b, m) (res, n) b1 b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HJ1 : @ajournal_xw rc SK segs B [] ARx ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
  (st_nev S2 - st_nev Sc) [call_trace lyc (pc_malloc_ra0 code) regsT ch]).
{ refine (@acall_post_journal_xw rc SK segs B ARx HL LAWS segs_low errno_low OWNLOW lyc Sc Hpc W regsT memT mdc
    ly2 S2 W2 regs2 mem2 md2 _ (fun a => Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2)) [] (st_nev S2 - st_nev Sc)
    [call_trace lyc (pc_malloc_ra0 code) regsT ch]
    HPOST HAR HstkC Hfrs2 ltac:(zlia) ltac:(zlia) Hsecs2 _ _ _ HQT2 (wild_part_step _ _ _ _ HDEP)).
- intros a Ha. apply (@xs_write_ok rc segs B ARx XS HL LAWS XSL lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a
    HAR HAR2 Hly2);
[intros b' Hb'; rewrite Eab2; apply in_or_app; left; exact Hb' | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha].
- intros a [[_ Ha] | Hx]; [right | left; exact Hx].
exists res, n. split; [right; exact Hnew|]. split; [exact Ha|]. right.
intros Hold. exact (Hdisj res n a Hold Ha Ha).
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. apply in_or_app. left. exact Hq. }
exists ly2, S2, regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (@ajournal_xw_sub rc SK segs B PST ARx HL LAWS segs_low);
[exact HJ | exact (@ajournal_xw_nil_pst rc SK segs B ARx PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia
| intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|]. split; [exact Htr'|].
split; [exists p, tr; split; [exact Hpath|]; split; [exact Hgf|]; split; [exact Hleaf0|];
split; [split; [intros Hc; exfalso; exact (Hnn Hc) | intros Hc; zlia] | intros _; reflexivity]|].
split; [|exact KEEP].
right. split; [exact Hr4096|]. split; [exact Eab2|].
rewrite Hsp' in HJ1. eapply (@acall_kept_of_journal_x rc SK segs B ARx segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. apply in_or_app. left. exact Hb.
Qed.

(* YGcallMxmn.aj_malloc_at_x_m (YGcallx.v's aj_malloc_at_x) over the keep text, plus the keep. *)
Lemma aj_malloc_at_x_m_keep : amalloc_realizes_x_keep ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
YGcallx.acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
YGcallx.malloc_leaf_x (fx := fx) segs B ARx XS lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
YGcallx.acall_kept_x (rc := rc) segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
YGcallx.acall_kept_x (rc := rc) segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n))) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros AMALLOC WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
exact (aj_malloc_at_x_ct_m_keep AMALLOC W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch
(admits_call_trace0 _ lyc _ regsT ch Sc (proj1 (proj2 (proj2 errno_low))) Htr)).
Qed.

(* YGcallMxmn.aj_malloc_x_ct_m (YGcallx.v's aj_malloc_x_ct) over the keep text, plus the keep. *)
Lemma aj_malloc_x_ct_m_keep : amalloc_realizes_x_keep ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
YGcallx.acall_pre_x segs B ARx QMm lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
YGcallx.malloc_leaf_x (fx := fx) segs B ARx XS lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
YGcallx.acall_kept_x (rc := rc) segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
YGcallx.acall_kept_x (rc := rc) segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n))) /\
(MN.memnorm segs (ms_mem ms) -> MN.memnorm segs mem2)).
Proof.
intros AMALLOC WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o spw raw ch
HS Hpcs Hrv HJ Ha0 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
pose proof (ajx_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _). pose proof (ajx_qt HJ) as HQT.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpcs.
eapply aj_malloc_at_x_ct_m_keep; eassumption.
Qed.

(* YGcallMxmn.aj_malloc_x_m (YGcallx.v's aj_malloc_x) over the keep text, plus the keep. *)
Lemma aj_malloc_x_m_keep : amalloc_realizes_x_keep ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) (ms_regs ms) ch) Sc ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
YGcallx.acall_pre_x segs B ARx QMm lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
YGcallx.malloc_leaf_x (fx := fx) segs B ARx XS lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
YGcallx.acall_kept_x (rc := rc) segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
YGcallx.acall_kept_x (rc := rc) segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n))) /\
(MN.memnorm segs (ms_mem ms) -> MN.memnorm segs mem2)).
Proof.
intros AMALLOC WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o spw raw ch
HS Hpcs Hrv HJ Ha0 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
pose proof (ajx_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _). pose proof (ajx_qt HJ) as HQT.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpcs.
eapply aj_malloc_at_x_m_keep; eassumption.
Qed.
End allocmk.

(* ---------------------------------------------------------------------------- *)
(* 2. The cf instance: the malloc bridge, and free under the re-hide.                *)
Section allocrhk. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).
Local Abbreviation code := (as_code B).

(* YGcallcf.amalloc_realizes_x_xs with the keep: the keep text at ARxs from the cf keep contract. *)
Lemma amalloc_realizes_x_xs_keep : YGcfMallocComposeKeep.amalloc_realizes_cf_keep segs B ->
amalloc_realizes_x_keep (fx := fx) segs B ARxs (QMm_cf segs B) malloc_cf cf_malloc_max xs_cf.
Proof.
intros AM ly S Hp W regs mem md n ch Hpre H1 H2 H3 H4.
destruct (proj1 (acall_pre_x_xs segs B ly S Hp W regs mem md ch) Hpre) as [Hpc _].
exact (amreal_mono segs _ _ _ _ _
  (fun r W' c' Hl => conj (proj1 (malloc_leaf_cf_xs segs B ly S Hp W regs mem md n r W' c') (proj1 Hl)) (proj2 Hl))
  (AM ly S Hp W regs mem md n ch Hpc H1 H2 H3 H4)).
Qed.

(* YGcallcf.APOST_cf with the keep: the callee post the generic free rules read. *)
Definition APOST_cf_keep (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
APOST_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' /\ (MN.memnorm segs mem -> MN.memnorm segs mem').

Lemma POST_AR_cf_keep : apost_ar_law segs ARxs APOST_cf_keep.
Proof.
intros stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' [H _].
exact (POST_AR_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' H).
Qed.

(* YGcallcf.free_leaf_cf_xA with the keep. *)
Lemma free_leaf_cf_xA_keep : forall ly S Hp W regs mem md ch p n r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S -> free_frame_cf S (snd r) ->
YGcfMallocComposeKeep.free_leaf_cf_rh_keep segs B ly S Hp W regs mem md p n r W' c' ->
free_leaf_xA segs B APOST_cf_keep ly S Hp W regs mem md p n r W' c'.
Proof.
intros ly S Hp W regs mem md ch p n r W' c' Hpre HP HF [HL HK].
destruct (free_leaf_cf_xA segs B ly S Hp W regs mem md ch p n r W' c' Hpre HP HF HL) as (ly' & regs' & mem' & md' & Hc & HA & HQ).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [|exact HQ]. split; [exact HA|].
exact (HK _ _ _ _ Hc).
Qed.

(* YGcallcf.afree_realizes_x_cf_rh with the keep: the generic text at APOST_cf_keep from the cf keep contract. *)
Lemma afree_realizes_x_cf_rh_keep : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep segs B ->
afree_realizes_xR segs B ARxs (QMm_cf segs B) free_cf (wle' segs RZ_cf) APOST_cf_keep.
Proof.
intros AF ly S Hp W regs mem md p n ch Hpre H1 H2 H3 H4.
destruct (proj1 (acall_pre_x_xs segs B ly S Hp W regs mem md ch) Hpre) as [Hpc HX].
pose proof (amrealG_ipost segs (wle' segs RZ_cf) _ _ _ _ _ (cfx_fr_free_cf p (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S)
(AF ly S Hp W regs mem md p n ch Hpc H1 H2 H3 H4)) as HR.
exact (amrealG_mono segs (wle' segs RZ_cf) _ _ _ _ _ (fun r W' c' Hl => free_leaf_cf_xA_keep ly S Hp W regs mem md ch p n r W' c'
Hpc HX (free_frame_cf_of_state S (snd r) (proj1 (proj2 Hl)) (proj2 (proj2 Hl))) (proj1 Hl)) HR).
Qed.

Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARxs HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law (rc := rc) segs B ARxs.
Hypothesis WFL : ARx_wf_law segs ARxs (Wf_cf (as_universe B)).
Hypothesis AMX : alloc_model_laws_x B QM_cf malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)).

Lemma POST_J_cf_keep : apost_j_law (rc := rc) (SK := SK) segs B ARxs (wle' segs RZ_cf) APOST_cf_keep.
Proof.
intros lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 regs2 mem2 md2 Eb XW FP1 k1 WS [H _].
exact (POST_J_cf (SK := SK) segs B LAWS segs_low errno_low OWNLOW lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 regs2 mem2 md2
  Eb XW FP1 k1 WS H).
Qed.

(* YGcallMxmn.aj_free_x_ct_m_rh over the keep contract, plus the keep. *)
Lemma aj_free_x_ct_m_rh_keep : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep segs B ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xwR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm_cf segs B Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr' segs RZ_cf W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2
  (k + (st_nev S2 - st_nev Sc)) (WS ++ [call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (free_cf q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA segs B (APOST_cf segs B) lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
(MN.memnorm segs (ms_mem ms) -> MN.memnorm segs mem2)).
Proof.
intros AF WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o spw raw ch
  HS Hpcs Hrv HJ Hin Hnh Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
eapply (SRrG_mono segs (wle' segs RZ_cf)).
{ exact (YGcallMxmn.aj_free_x_ct_mR (fx := fx) (rc := rc) (SK := SK) segs B PST ARxs QM_cf (QMm_cf segs B) malloc_cf
    cf_malloc_max free_cf (Wf_cf (as_universe B)) LAWS segs_low errno_low WFL AMX (QMQ_cf segs B) (wle' segs RZ_cf)
    (wle'_trans segs RZ_cf) APOST_cf_keep POST_AR_cf_keep POST_J_cf_keep (afree_realizes_x_cf_rh_keep AF)
    W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o spw raw ch
    HS Hpcs Hrv HJ Hin Hnh Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP). }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HP2 & HB2 & HF2 & HPRE2 & HTR2 &
  (q & trc & Hq & Hinq & Hpath & Hgf & Hleaf) & HK2).
destruct Hleaf as (ly' & regs' & mem' & md' & Hc' & (HA' & HMN') & HQ').
assert (Em : mem' = mem2)
  by exact (f_equal (fun c => ms_mem (cfg_ms c)) (eq_trans (eq_sym Hc') Hc)).
exists ly2, S2, regs2, mem2, md2.
split; [exact Hc|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|]. split; [exact HF2|].
split; [exact HPRE2|]. split; [exact HTR2|].
split; [exists q, trc; split; [exact Hq|]; split; [exact Hinq|]; split; [exact Hpath|]; split; [exact Hgf|];
  exists ly', regs', mem', md'; exact (conj Hc' (conj HA' HQ'))|].
split; [exact HK2|].
rewrite <- Em. exact HMN'.
Qed.

(* YGcallMxmn.aj_free_at_x_ct_m_rh over the keep contract, plus the keep. *)
Lemma aj_free_at_x_ct_m_rh_keep : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep segs B ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xwR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm_cf segs B Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr' segs RZ_cf W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2
  (k + (st_nev S2 - st_nev Sc)) (WS ++ [call_trace lyc (pc_free_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (free_cf q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA segs B (APOST_cf segs B) lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros AF WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch
  HJ Hin Hnh Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
eapply (SRrG_mono segs (wle' segs RZ_cf)).
{ exact (YGcallMxmn.aj_free_at_x_ct_mR (fx := fx) (rc := rc) (SK := SK) segs B PST ARxs QM_cf (QMm_cf segs B) malloc_cf
    cf_malloc_max free_cf (Wf_cf (as_universe B)) LAWS segs_low errno_low WFL AMX (QMQ_cf segs B) (wle' segs RZ_cf)
    (wle'_trans segs RZ_cf) APOST_cf_keep POST_AR_cf_keep POST_J_cf_keep (afree_realizes_x_cf_rh_keep AF)
    W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch
    HJ Hin Hnh Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP). }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HP2 & HB2 & HF2 & HPRE2 & HTR2 &
  (q & trc & Hq & Hinq & Hpath & Hgf & Hleaf) & HK2).
destruct Hleaf as (ly' & regs' & mem' & md' & Hc' & (HA' & HMN') & HQ').
assert (Em : mem' = mem2)
  by exact (f_equal (fun c => ms_mem (cfg_ms c)) (eq_trans (eq_sym Hc') Hc)).
exists ly2, S2, regs2, mem2, md2.
split; [exact Hc|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|]. split; [exact HF2|].
split; [exact HPRE2|]. split; [exact HTR2|].
split; [exists q, trc; split; [exact Hq|]; split; [exact Hinq|]; split; [exact Hpath|]; split; [exact Hgf|];
  exists ly', regs', mem', md'; exact (conj Hc' (conj HA' HQ'))|].
split; [exact HK2|].
rewrite <- Em. exact HMN'.
Qed.
End allocrhk.

Print Assumptions YGcallMxmn.aj_malloc_x_ct_m.
Print Assumptions aj_malloc_x_ct_m_keep.
Print Assumptions YGcallMxmn.aj_malloc_at_x_m.
Print Assumptions aj_malloc_at_x_m_keep.
Print Assumptions YGcallMxmn.aj_malloc_x_m.
Print Assumptions aj_malloc_x_m_keep.
Print Assumptions YGcallMxmn.aj_free_x_ct_m_rh.
Print Assumptions aj_free_x_ct_m_rh_keep.
Print Assumptions YGcallMxmn.aj_free_at_x_ct_m_rh.
Print Assumptions aj_free_at_x_ct_m_rh_keep.
Print Assumptions YGcallcf.amalloc_realizes_x_xs.
Print Assumptions amalloc_realizes_x_xs_keep.
Print Assumptions YGcallcf.afree_realizes_x_cf_rh.
Print Assumptions afree_realizes_x_cf_rh_keep.
