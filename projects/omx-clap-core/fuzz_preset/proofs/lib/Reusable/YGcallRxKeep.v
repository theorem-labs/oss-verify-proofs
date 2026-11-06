(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the memnorm-keeping twin of the generic realloc(NULL, n) call rule
   aj_realloc_null_at_x, over YGcallRx.v's text, and of its cf lift arealloc_null_realizes_x_cf (both in
   lib/A/Prog/TxPut102A_Rnull.v at ossv/recipes 87c4b944683b; this tree has only the twins below).
   rule 24: proves no function (kind: invariant lemma).
   1. THE LEAF (Section gr): malloc_leaf_x_keep is YGcallx.v's malloc_leaf_x with the memnorm keep
      `YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'` as the LAST conjunct, flat, after the raw frame: the
      leaf's text before field round 3 part 3c took the keep out, so a walk reads the keep at the index it had then.
      _of_keep projects the keep leaf to the plain leaf; _keep_of builds it from the plain leaf and the keep at the
      leaf's end configuration (YGcfMallocCompose.v at_mem_cf, written out).
   2. THE TEXTS: arealloc_null_realizes_x_keep is YGcallRx.v's arealloc_null_realizes_x with that leaf.
      realloc_null_model_law_x is TxPut102A_Rnull.v's model law of the null tree, restated over this section's
      variables (the rule below takes it).
   3. THE RULE (Section r): aj_realloc_null_at_x_keep is the released aj_realloc_null_at_x with the keep leaf,
      stated over YGcallRx.v's call predicate QMm (the call memory: QMm Sc memT where that file has QM Sc). SRr and
      amreal are continuation-passing (YA0n.v SRr) and the original's post holds the plain leaf only, so the twin does
      not follow from its original: its proof is its original's steps, the leaf passed through.
   4. THE CF LIFT (Section J): arealloc_null_realizes_x_cf_keep gives the generic keep text at ARcf /\ xs_placed_cf,
      XS := xs_cf, QMm := QMm_cf from YGcfReallocComposeKeep.v's arealloc_null_realizes_cf_keep, as
      the released arealloc_null_realizes_x_cf lifted the plain text.
   Numerals: 1, 3, 4, 10, 11 in getr are RISC-V register numbers (WORD); 12 (ENOMEM) and 1 (the OOM byte's value) are
   WORD; 16 (stack alignment), 4096 (the lowest block address) and 16384 (= ASTACK) are LENGTH constants of the
   engine's rules. No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ReallocP YGcallRx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The leaf and 2. the texts, over YGcallRx.v Section gr's variables.          *)
Section gr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable QMm : astate -> (word -> option byte) -> Prop.
Variable RQ : astate -> Z -> list Z -> Prop.
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable ft : sptr -> list Z -> YG00.M unit.
Variable WFx : astate -> Prop.
Variable XS : alayout -> astate -> list (Z * Z).

(* YGcallx.v malloc_leaf_x with the memnorm keep as its last conjunct. *)
Definition malloc_leaf_x_keep (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_x segs B ARx ASTACK ly S Hp W regs mem md
(fun a => (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n) \/
Exists (in_zr a) (XS ly S ++ XS ly' (snd r)))
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r) /\
(fst r = PNull -> rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1) /\
(fst r <> PNull -> forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= bv_unsigned x < sptr_addr B ly' (fst r) + req_size n)
    \/ Exists (in_zr (bv_unsigned x)) (XS ly S ++ XS ly' (snd r))) ->
 mem' x = mem x) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').

Lemma malloc_leaf_x_of_keep : forall ly S Hp W regs mem md n r W' c',
malloc_leaf_x_keep ly S Hp W regs mem md n r W' c' -> malloc_leaf_x segs B ARx XS ly S Hp W regs mem md n r W' c'.
Proof.
intros ly S Hp W regs mem md n r W' c' (ly' & regs' & mem' & md' & Hc & H1 & H2 & H3 & H4 & H5 & H6 & _).
exists ly', regs', mem', md'. exact (conj Hc (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6)))))).
Qed.

Lemma malloc_leaf_x_keep_of : forall ly S Hp W regs mem md n r W' c',
malloc_leaf_x segs B ARx XS ly S Hp W regs mem md n r W' c' ->
(forall pc regs' mem' md', c' = cfg_at segs pc regs' mem' md' ->
 YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem') ->
malloc_leaf_x_keep ly S Hp W regs mem md n r W' c'.
Proof.
intros ly S Hp W regs mem md n r W' c' (ly' & regs' & mem' & md' & Hc & H1 & H2 & H3 & H4 & H5 & H6) HM.
exists ly', regs', mem', md'.
exact (conj Hc (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (HM _ _ _ _ Hc)))))))).
Qed.

(* YGcallRx.v arealloc_null_realizes_x with the keep leaf. *)
Definition arealloc_null_realizes_x_keep (pc pc0 : Z) : Prop :=
forall Hp, arealloc_null_realizesP segs (admits (as_universe B)) mt ft
(fun ly S W regs mem md ch => acall_pre_x segs B ARx QMm ly S Hp W regs mem md ch)
(fun _ _ => True) nmax LIVE_MAX (fun R t W c Q => amreal segs t W c Q)
(fun ly S W regs mem md n r W' c' => malloc_leaf_x_keep ly S Hp W regs mem md n r W' c') pc pc0.

(* TxPut102A_Rnull.v's model law of the null tree: from a WFx state with the realloc room RQ, realloc_null_tree_with is
   safe, granted-progressing and not a spin, every model path moves the blocks as the malloc it is (malloc_post_x),
   and the depot grows by at most the trace. *)
Definition realloc_null_model_law_x : Prop :=
forall s n tr, WFx s -> RQ s n tr -> 1 <= n < nmax -> blocks_bytes s + n <= LIVE_MAX -> admits (as_universe B) tr s ->
asafe (realloc_null_tree_with mt ft n tr s) /\ agprog (realloc_null_tree_with mt ft n tr s) /\
is_spin (realloc_null_tree_with mt ft n tr s) = false /\
(forall tr' r, apath (realloc_null_tree_with mt ft n tr s) tr' r -> malloc_post_x s n r) /\
(forall tr' r, apath (realloc_null_tree_with mt ft n tr s) tr' r -> incl (st_depot (snd r)) (st_depot s ++ [tr])).

(* ---------------------------------------------------------------------------- *)
(* 3. The rule.                                                                   *)
Section r.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law segs B ARx.
Hypothesis WFL : ARx_wf_law segs ARx WFx.
Hypothesis RMN : realloc_null_model_law_x.
Hypothesis XSL : ARx_xs_law segs B ARx XS.

(* the released aj_realloc_null_at_x (header) with the keep leaf, over the call predicate QMm (QMm Sc memT where that file
   has QM Sc): realloc (NULL, n) through the realloc wrapper, the journal advanced at the same ghost set Hpc. *)
Lemma aj_realloc_null_at_x_keep : forall pcR pc0, arealloc_null_realizes_x_keep pcR pc0 ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
getr regsT 10 = w64 0 -> getr regsT 11 = w64 n -> 1 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
RQ Sc n (call_trace lyc pc0 regsT ch) ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc pc0 regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pcR) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc pc0 regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc pc0 regsT ch) Sc /\
(exists q, sptr_addr B ly2 q = res /\ (q = PNull <-> res = 0) /\
  (exists trc, apath (realloc_null_tree_with mt ft n (call_trace lyc pc0 regsT ch) Sc) trc (q, S2) /\
     YG0d.gflag trc = true) /\
  malloc_leaf_x_keep lyc Sc Hpc W regsT memT mdc n (q, S2) W2 c2) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ blocks S2 = blocks Sc /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1 /\
  mt_refused mt ft n (call_trace lyc pc0 regsT ch) Sc S2)
 \/
 (4096 <= res /\ res mod 16 = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros pcR pc0 AREAL WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Ha1 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM HRQ Hch Htr.
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs. pose proof (ajx_wle HJ) as Hwle. pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs. pose proof (ajx_nev HJ) as Hnev. pose proof (ajx_k HJ) as Hk. pose proof (ajx_hi HJ) as F1. pose proof (ajx_blk HJ) as F2. pose proof (ajx_img HJ) as F3. pose proof (ajx_frm HJ) as F4. pose proof (ajx_gone HJ) as Hgone. pose proof (ajx_pres HJ) as Hpres. pose proof (ajx_stk HJ) as Hstatic. pose proof (ajx_extra HJ) as F5. pose proof (ajx_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact HQM]. }
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
destruct (RMN Sc n (call_trace lyc pc0 regsT ch) HWF HRQ Hn Hlive Htr) as (Hsafe & Hprog & Hnspin & Hmpost & Hmdep).
pose proof (AREAL Hpc lyc Sc W regsT memT mdc n ch HPRE I Ha0 Ha1 Hn Hlive Htr) as HREAL.
cbv beta in HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W _ _ HREAL Hsafe Hprog Hnspin). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf & Href).
pose proof (Hmpost tr r Hpath) as HQ. pose proof (Hmdep tr r Hpath) as HDEP. destruct r as [p S2]. unfold malloc_post_x in HQ.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & Hbl).
cbn [fst snd] in Href, HDEP.
pose proof Hleaf as Hleaf0.
cbn [fst snd] in Hleaf.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & Hres & HQT2 & HERR & _).
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
  (st_nev S2 - st_nev Sc) [call_trace lyc pc0 regsT ch]).
{ refine (@acall_post_journal_xw rc SK segs B ARx HL LAWS segs_low errno_low OWNLOW lyc Sc Hpc W regsT memT mdc
    ly2 S2 W2 regs2 mem2 md2 _ (fun a => Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2)) [] (st_nev S2 - st_nev Sc)
    [call_trace lyc pc0 regsT ch]
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
split; [exact HPRE|]. split; [exact Htr|].
split.
{ exists PNull. split; [reflexivity|]. split; [split; intros _; reflexivity|].
split; [exists tr; split; [exact Hpath | exact Hgf] | exact Hleaf0]. }
left. split; [reflexivity|]. split; [exact Eab2|]. split; [exact Hbl|].
split.
{ rewrite Hsp' in HJ1.
eapply (@acall_kept_of_journal_x rc SK segs B ARx segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb. }
destruct (HERR eq_refl) as [Herr Hoom].
split; [exact Herr|]. split; [exact Hoom|]. exact (Href eq_refl).
-
assert (Hbl' : blocks S2 = blocks Sc ++ [(p, n)]).
{ destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
clear Hbl.
set (res := sptr_addr B ly2 p) in *.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, n)]). rewrite Hbl', map_app. cbn [map].
f_equal. apply map_ext_in. exact Efc. }
assert (Hnew : In (res, n) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B ARx LAWS ly2 S2 Hpc W2 mem2 md2 res n HAR2 Hnew) as (Hr16 & Hr4096 & _).
assert (Hdisj : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (res <= a < res + req_size n)).
{ intros b m a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
pose proof (@sep_blocks_pos_x rc segs B ARx HL LAWS ly2 S2 Hpc W2 mem2 md2 (b, m) (res, n) b1 b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HJ1 : @ajournal_xw rc SK segs B [] ARx ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
  (st_nev S2 - st_nev Sc) [call_trace lyc pc0 regsT ch]).
{ refine (@acall_post_journal_xw rc SK segs B ARx HL LAWS segs_low errno_low OWNLOW lyc Sc Hpc W regsT memT mdc
    ly2 S2 W2 regs2 mem2 md2 _ (fun a => Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2)) [] (st_nev S2 - st_nev Sc)
    [call_trace lyc pc0 regsT ch]
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
split; [exact HPRE|]. split; [exact Htr|].
split.
{ exists p. split; [reflexivity|]. split; [split; [intros Hc; exfalso; exact (Hnn Hc) | intros Hc; zlia]|].
split; [exists tr; split; [exact Hpath | exact Hgf] | exact Hleaf0]. }
right. split; [exact Hr4096|]. split; [exact Hr16|]. split; [exact Eab2|].
rewrite Hsp' in HJ1.
eapply (@acall_kept_of_journal_x rc SK segs B ARx segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. apply in_or_app. left. exact Hb.
Qed.
End r.
End gr.

(* ---------------------------------------------------------------------------- *)
(* 4. The cf lift.                                                                *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcallcf YGcfRealloc YGcallRcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocCompose YGcfReallocComposeKeep.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section J.
Variable segs : list Segment.
Variable B : asyms.
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* the released arealloc_null_realizes_x_cf (header) with the keep texts, at QMm := QMm_cf. *)
Lemma arealloc_null_realizes_x_cf_keep : forall pc,
(forall Hp, YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep segs B Hp pc) ->
arealloc_null_realizes_x_keep segs B ARxs (QMm_cf segs B) malloc_cf cf_malloc_max free_cf xs_cf pc cf_pc_realloc_ra0.
Proof.
intros pc H Hp ly S W regs mem md n ch HPRE HR H10 H11 Hn Hlive Htr.
pose proof (H Hp ly S W regs mem md n ch (acall_pre_x_xs_cf segs B ly S Hp W regs mem md ch HPRE)
  HR H10 H11 Hn Hlive Htr) as H0.
cbv beta in H0 |- *.
eapply amreal_mono; [|exact H0].
intros r W' c' [[HL HM] HN]. split; [|exact HN].
exact (malloc_leaf_x_keep_of segs B ARxs xs_cf ly S Hp W regs mem md n r W' c'
  (proj1 (malloc_leaf_cf_xs segs B ly S Hp W regs mem md n r W' c') HL) HM).
Qed.
End J.
End G.
