(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): aj_flag_store_xR is aj_flag_store_x over a journal at
   a world relation R and the step relation SRrG R (YSRrG.SRrG_msteps for the run, YCbqG's R forms for the journal);
   the run keeps the world, so no law of R is read, and the R form takes R reflexive and transitive as every R rule
   does. aj_flag_store_x keeps its statement and is the instance at wle. aj_stack_malloc_at_xR (the call's own journal
   enters the caller's at R by reflexivity and transitivity; the post's own-call journal stays at wle) and
   aj_set_shadow_at_xR are the other two rules over R; their old names are the instances at wle. *)
(* Modified by Theorem Labs, 2026-10: cgif's frame-area call rule aj_stack_malloc_at (proofs/cgif/cgif_file_fuzzer/lib/
   YCbq.v:1749-1809, this tree's copy lib/Reusable/YCbq.v:1749) restated over YCbqG.v's journal ajournal_x (allocator
   invariant a parameter ARx, ghost head set Hp after S / Hpc after Sc, program statics PST), for the frame-area
   contract astack_malloc_realizes_x of the frozen lib/Reusable/FCiface.v (frameclass d9a884240c6e, sha256
   673aac5ee2f6ed86). Generic: no image
   class, no address, no allocator instance.
   Differences from the donor, each minimal:
   (a) cgif read the model's progress and post from model_laws (stack_malloc_progressP, ml_stack_malloc through
       am_wf); here they are ONE hypothesis in ARx form, SMX, which an instance discharges from its own model laws
       (the cf instance: YG05cf.v stack_malloc_progress_cf and stack_malloc_ok_cf with Wf_cf from ARcf);
   (b) the call's own journal is call_effect_journal_x (YGcallx.v:251) at PST = [], lifted by ajournal_x_nil_pst, and
       composed by ajournal_x_sub (YCbqG.v, footprint FP1 = []); Hp is threaded unchanged (FCiface: a frame-area call
       neither poisons nor unpoisons a head);
   (c) the frame's presence (FCiface's post) is also returned, which a caller writing its new frame needs;
   (d) as cgif's aj_stack_malloc_atS (cgif_file_fuzzer lib/YC85.v:292), the post ends with the call's own journal and
       `exists f, S2 = set_fs f Sc` (the call changes st_fs only), so a caller carries a state fact across the call.
   SECOND RULE, aj_flag_store_x: cgif's aj_flag_store (YCbq.v:2362-2439, the inline release under astack_free_law)
   for the LISTING engine over ajournal_x; its ARx-form hypotheses and their cf discharges are stated at the rule
   (ASFX = YG0dcf.v astack_free_law_cf; FFLX = the two conjuncts of cgif's frame_flag_lawP the rule reads, over ARx;
   SFX = YG05cf.v stack_free_ok_cf).
   THIRD RULE, aj_set_shadow_at_x: cgif's frame-area set_shadow call rule (cgif_rgb_fuzzer lib/YC05.v:206) over
   ajournal_x for FCiface's aset_shadow_realizes_x, taken from WalkH6's set-shadow-v2.patch (cold/h-hpreset-7-walk-H6
   321efcb143d) unchanged but for its comment.
   Rule 24: no ajournal_x port of aj_stack_malloc_at or aj_flag_store existed on any branch read (WalkS8a confirmed,
   2026-10-28 ~23:40Z; h-hpreset-7 stopped c-omx-alloc's lane for both); cgif's released YCbq.v is the source ported.
   Numerals: 0, 10 (cgif's class range), 16 (stack alignment), 64 (the smallest frame), 4096 (= ESTACK, YG0d.v),
   2 ^ 40, 2 ^ 64: LENGTH / DERIVED. No ADDRESS. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallSx.v, with its module names changed; 735 of its 901 lines of code are new or changed and 195 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Cno102_FKit.v, with its module paths and module names changed; 177 of its 223 lines of code are new or changed and 855 lines of the source are left out. *)
(* plugin-hostd/fuzz_reply.asan_ubsan, image B: the image-B twin of lib/A/CfRBridgeRulesRh.v, under lib/B so the B
   tree is self-contained (as lib/B/CfRBridgeRulesB.v): the A file's text (a Theorem Labs lane's re-fit,
   a working branch 76a84b5b0b9f) with lib/B's YD2l and W_journal_x for lib/A's (A's CfParamsReply kept) and the
   line numbers of the lib/B files; the A file's header follows.
   The cf allocator rules of top_x at route R (a Theorem Labs lane R, N5 and the TOPK
   rules at R; new file). Rule 24: proves no function (kind: bridge lemmas between existing contract forms).
   1. The journal copies over the R journal. Each is a direct copy of a strict lemma over ajournal_x
      (Reusable/YCbqG.v:242-265) to ajournal_xR (:202-225), the only change being the journal; the world relation R is
      a Section variable, with no reflexivity or transitivity hypothesis, because no proof reads the world conjunct R W W':
      - ajournal_x_impl_xR: W_journal_x.v:1895 ajournal_x_impl (only the first conjunct, the relation, changes);
      - aj_k_le_xR: CfRBridgeRulesB.v:551 aj_k_le (only the event bound and 0 <= k read k);
      - aj_to_xs_xR / aj_of_xs_xR: CfRBridgeRulesB.v aj_to_xs / aj_of_xs (top_x's relation and YGcallcf's ARxs, by
        ajournal_x_impl_xR), at CfF1's A rule fit (fu2-mp 9118a6a96818): top_x's ARX carries arodata_ok_cf on the
        memory, and aj_of_xs takes it at the post memory before the journal.
   2. The generic lifts strict -> R of the two rules that cross no re-hide (malloc, strndup): at any world relation
      R that contains wle (WLE_R) and is transitive (R_trans), W_journal_x.v's strict rule gives its R twin,
      amalloc_cf_rule_c_x -> amalloc_cf_rule_c_xR R and astrndup_cf_rule_c_x pc -> astrndup_cf_rule_c_xR R pc. The
      strict rule is applied at the journal that starts at the call state (aj_start_x_of_xR: YCbqG.ajournal_x_initR's
      body at wle, STK := ASTACK, sp0 := spZ regsT, o := 0, FP := []); its step lifts by SRr_SRrG WLE_R, its journal
      by ajournal_xR_mono WLE_R and goes under the caller's by ajournal_x_subR R_trans (aj_compose_x_xR). The R twin's
      call-boundary premise RO is not used (part 3c at R, a Theorem Labs lane 955086633601: the R rules have no memnorm
      premise). The lifts read no image.
   3. The same lifts for a relation whose own laws are not at hand (top_x's ARX with arodata_ok_cf on the memory: its
      laws need an image keep fact, ReplyKeptAroA.arodata_kept_A, at tfibsegs only): amalloc_cf_rule_c_xR_lift_xs /
      astrndup_cf_rule_c_xR_lift_xs compose over a wider relation ARy that has laws (top_x's: YGcallcf's ARxs), with
      ARx included in ARy, and take the post's ARx from the callee's own journal (aj_compose_x_xR_xs). top_x's
      instances apply them in CfRBridgeRulesRhTopB.v / CfRBridgeRulesRhStrndupB.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YP09 YP03 YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YCbqG YGcallx YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfXs YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The journal copies over the R journal.                                      *)
Section JR. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable R : world segs -> world segs -> Prop.

(* W_journal_x.v:1895 ajournal_x_impl, over ajournal_xR. *)
Lemma ajournal_x_impl_xR : forall (B : asyms)
(R1 R2 : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
PST STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
(R1 ly' S' Hp' W' mem' md' -> R2 ly' S' Hp' W' mem' md') ->
ajournal_xR segs B PST R1 R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_xR segs B PST R2 R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros B R1 R2 PST STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HR HJ.
destruct HJ as (H1 & Hr). split; [exact (HR H1) | exact Hr]. Qed.

(* CfRBridgeRulesB.v:551 aj_k_le, over ajournal_xR. *)
Lemma aj_k_le_xR : forall (B : asyms) PST
  (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
  STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k k', k <= k' ->
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k'.
Proof.
intros B PST ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k k' Hk HJ.
unfold ajournal_xR in *. destruct HJ as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
split; [exact A6|]. split; [lia|]. split; [lia|]. exact A9.
Qed.

(* CfRBridgeRulesB.v:202 / :210 aj_to_xs / aj_of_xs (its Section B: CfImg a Context, CfParams_reply local), over
   ajournal_xR. *)
Section B. Context {ci : CfImg}.
#[local] Existing Instance CfParams_reply.
Local Abbreviation ARX := (fun ly S Hp (W : world segs) mem md =>
  ARcf segs TfibB ly S Hp W mem md /\ Hp = [] /\ arodata_ok_cf segs TfibB mem).
Local Abbreviation ARxs := (fun ly S Hp (W : world segs) mem md => ARcf segs TfibB ly S Hp W mem md /\ xs_placed_cf ly S).

Lemma aj_to_xs_xR : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  ajournal_xR segs TfibB [] ARX R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR segs TfibB [] ARxs R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ. eapply ajournal_x_impl_xR; [|exact HJ].
intros [H _]. exact (conj H (xs_placed_of_ARcf segs TfibB ly' S' Hp' W' mem' md' H)).
Qed.

Lemma aj_of_xs_xR : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k, Hp' = [] ->
  arodata_ok_cf segs TfibB mem' ->
  ajournal_xR segs TfibB [] ARxs R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR segs TfibB [] ARX R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k E AD HJ. eapply ajournal_x_impl_xR; [|exact HJ].
intros [H _]. exact (conj H (conj E AD)).
Qed.
End B.
End JR.

(* ---------------------------------------------------------------------------- *)
(* 2. The generic lifts strict -> R (no re-hide crossing).                        *)
Section LIFT. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable R : world segs -> world segs -> Prop.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.

(* The journal at wle that starts at a call state reached by an R journal (YCbqG.ajournal_x_initR's body). *)
Lemma aj_start_x_of_xR : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k (o : Z) (regsT : bvmap 5 word),
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  ajournal_x segs B PST ARx ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] lyc Sc Hpc W memT mdc 0.
Proof.
intros STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT HJ Hsp' Hal Hneg Hbud.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [zlia|]. split; [apply wle_refl|].
split; [apply aos_step_refl|]. split; [reflexivity|]. split; [zlia|]. split; [zlia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros p m i H1 H2; exfalso; exact (H2 H1)|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact HstkC|]. split; [intros; reflexivity | exact HQT].
Qed.

(* A wle journal from that start, lifted to R and put under the caller's R journal (ajournal_x_subR). *)
Lemma aj_compose_x_xR : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k (o : Z) (regsT : bvmap 5 word)
  ly2 S2 Hp2 W2 mem2 md2 k1,
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
  spZ regsT = sp0 + o -> o <= 0 -> ASTACK - o <= STK ->
  ajournal_x segs B PST ARx ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1).
Proof.
intros STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT ly2 S2 Hp2 W2 mem2 md2 k1 HJ Hsp' Hneg Hbud HJ1.
assert (HJ1R : ajournal_xR segs B PST ARx R ASTACK (sp0 + o) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1).
{ rewrite <- Hsp'. eapply ajournal_xR_mono; [exact WLE_R | exact HJ1]. }
assert (ASTACK = 16384) as Has by reflexivity.
change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARx LAWS segs_low R_trans);
[exact HJ | exact HJ1R | zlia | zlia | intros a (rg & [] & _)].
Qed.

Section CTXs.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RP : roomp.
Variable RO : (word -> option byte) -> Prop.
Variable CTX : list (list Z).

(* W_journal_x.v amalloc_cf_rule_c_x -> amalloc_cf_rule_c_xR R. *)
Lemma amalloc_cf_rule_c_xR_lift : amalloc_cf_rule_c_x segs B PST ARx MT MMAX RP CTX ->
  amalloc_cf_rule_c_xR segs B PST ARx MT MMAX RP RO CTX R.
Proof.
intros H W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch kr
  HJ Ha0 Hn Hlive Hcnt Hsp Hal Hneg Hbud Hpfx Hgp Htp Hra Hraw Hch _ HCTX HRM Hmo.
pose proof (aj_start_x_of_xR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT HJ Hsp Hal Hneg Hbud) as J0.
pose proof (H W regsT memT ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] lyc Sc Hpc mdc 0 n 0 raw ch kr
  J0 Ha0 Hn Hlive Hcnt ltac:(zlia) ltac:(reflexivity) ltac:(zlia) ltac:(zlia) Hpfx Hgp Htp Hra Hraw Hch HCTX HRM Hmo) as HSR.
eapply SRrG_mono; [exact (SRr_SRrG segs R WLE_R _ _ _ HSR)|].
intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & Hc2 & HJ1 & Rest).
rewrite Z.add_0_l in HJ1. rewrite !Z.add_0_r, Hsp in Rest.
exists ly2, S2, Hp2, regs2, mem2, md2, res. split; [exact Hc2|]. split; [|exact Rest].
exact (aj_compose_x_xR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT ly2 S2 Hp2 W2 mem2 md2 1
  HJ Hsp Hneg Hbud HJ1).
Qed.

(* W_journal_x.v astrndup_cf_rule_c_x pc -> astrndup_cf_rule_c_xR R pc. *)
Lemma astrndup_cf_rule_c_xR_lift : forall pc, astrndup_cf_rule_c_x segs B PST ARx MT MMAX RP CTX pc ->
  astrndup_cf_rule_c_xR segs B PST ARx MT MMAX RP CTX R pc.
Proof.
intros pc H W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x n o raw ch kr
  HJ Ha0 Ha1 Hx Hn0 Hxn Hn Hlive Hcnt Hnz Hxs Hamr Hra0 Hhv Hin Hsp Hal Hneg Hbud Hpfx Hfr Hgp Htp Hra Hraw Hch Hf0
  HCTX HRM Hmo.
pose proof (aj_start_x_of_xR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT HJ Hsp Hal Hneg Hbud) as J0.
pose proof (H W regsT memT ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] lyc Sc Hpc mdc 0 x n 0 raw ch kr
  J0 Ha0 Ha1 Hx Hn0 Hxn Hn Hlive Hcnt Hnz ltac:(intros a Ha; rewrite !Z.add_0_r, Hsp; exact (Hxs a Ha))
  Hamr Hra0 Hhv Hin ltac:(zlia) ltac:(reflexivity) ltac:(zlia) ltac:(zlia) Hpfx Hfr Hgp Htp Hra Hraw Hch Hf0
  HCTX HRM Hmo) as HSR.
eapply SRrG_mono; [exact (SRr_SRrG segs R WLE_R _ _ _ HSR)|].
intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & Hc2 & HJ1 & Rest).
rewrite Z.add_0_l in HJ1. rewrite !Z.add_0_r, Hsp in Rest.
exists ly2, S2, Hp2, regs2, mem2, md2, res. split; [exact Hc2|]. split; [|exact Rest].
exact (aj_compose_x_xR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT ly2 S2 Hp2 W2 mem2 md2 1
  HJ Hsp Hneg Hbud HJ1).
Qed.
End CTXs.
End LIFT.

(* ---------------------------------------------------------------------------- *)
(* 3. The lifts over a wider relation with laws (header 3).                       *)
Section LIFTXS. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable ARy : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWSy : AR_laws_x segs B ARy hl.
Hypothesis INC : forall ly S Hp W mem md, ARx ly S Hp W mem md -> ARy ly S Hp W mem md.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable R : world segs -> world segs -> Prop.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.

(* aj_compose_x_xR, composed over ARy: both journals go to ARy (INC at their posts), ajournal_x_subR at ARy's laws,
   and the post's ARx comes back from the callee journal's first conjunct. *)
Lemma aj_compose_x_xR_xs : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k (o : Z) (regsT : bvmap 5 word)
  ly2 S2 Hp2 W2 mem2 md2 k1,
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
  spZ regsT = sp0 + o -> o <= 0 -> ASTACK - o <= STK ->
  ajournal_x segs B PST ARx ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1).
Proof.
intros STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT ly2 S2 Hp2 W2 mem2 md2 k1 HJ Hsp' Hneg Hbud HJ1.
assert (HA2 : ARx ly2 S2 Hp2 W2 mem2 md2) by exact (proj1 HJ1).
assert (HJy : ajournal_xR segs B PST ARy R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k).
{ eapply ajournal_x_impl_xR; [exact (INC lyc Sc Hpc W memT mdc) | exact HJ]. }
assert (HJ1y : ajournal_xR segs B PST ARy R ASTACK (sp0 + o) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1).
{ rewrite <- Hsp'. eapply ajournal_x_impl_xR; [exact (INC ly2 S2 Hp2 W2 mem2 md2)|].
  eapply ajournal_xR_mono; [exact WLE_R | exact HJ1]. }
assert (ASTACK = 16384) as Has by reflexivity.
change own with ([] ++ own).
eapply ajournal_x_impl_xR; [exact (fun _ => HA2)|].
eapply (ajournal_x_subR segs B PST ARy LAWSy segs_low R_trans);
[exact HJy | exact HJ1y | zlia | zlia | intros a (rg & [] & _)].
Qed.

Section CTXs.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RP : roomp.
Variable RO : (word -> option byte) -> Prop.
Variable CTX : list (list Z).

(* amalloc_cf_rule_c_xR_lift with ARx's laws replaced by ARy's (aj_compose_x_xR_xs). *)
Lemma amalloc_cf_rule_c_xR_lift_xs : amalloc_cf_rule_c_x segs B PST ARx MT MMAX RP CTX ->
  amalloc_cf_rule_c_xR segs B PST ARx MT MMAX RP RO CTX R.
Proof.
intros H W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch kr
  HJ Ha0 Hn Hlive Hcnt Hsp Hal Hneg Hbud Hpfx Hgp Htp Hra Hraw Hch _ HCTX HRM Hmo.
pose proof (aj_start_x_of_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT
  HJ Hsp Hal Hneg Hbud) as J0.
pose proof (H W regsT memT ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] lyc Sc Hpc mdc 0 n 0 raw ch kr
  J0 Ha0 Hn Hlive Hcnt ltac:(zlia) ltac:(reflexivity) ltac:(zlia) ltac:(zlia) Hpfx Hgp Htp Hra Hraw Hch HCTX HRM Hmo) as HSR.
eapply SRrG_mono; [exact (SRr_SRrG segs R WLE_R _ _ _ HSR)|].
intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & Hc2 & HJ1 & Rest).
rewrite Z.add_0_l in HJ1. rewrite !Z.add_0_r, Hsp in Rest.
exists ly2, S2, Hp2, regs2, mem2, md2, res. split; [exact Hc2|]. split; [|exact Rest].
exact (aj_compose_x_xR_xs STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT ly2 S2 Hp2 W2 mem2 md2 1
  HJ Hsp Hneg Hbud HJ1).
Qed.

(* astrndup_cf_rule_c_xR_lift with ARx's laws replaced by ARy's (aj_compose_x_xR_xs). *)
Lemma astrndup_cf_rule_c_xR_lift_xs : forall pc, astrndup_cf_rule_c_x segs B PST ARx MT MMAX RP CTX pc ->
  astrndup_cf_rule_c_xR segs B PST ARx MT MMAX RP CTX R pc.
Proof.
intros pc H W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x n o raw ch kr
  HJ Ha0 Ha1 Hx Hn0 Hxn Hn Hlive Hcnt Hnz Hxs Hamr Hra0 Hhv Hin Hsp Hal Hneg Hbud Hpfx Hfr Hgp Htp Hra Hraw Hch Hf0
  HCTX HRM Hmo.
pose proof (aj_start_x_of_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT
  HJ Hsp Hal Hneg Hbud) as J0.
pose proof (H W regsT memT ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] lyc Sc Hpc mdc 0 x n 0 raw ch kr
  J0 Ha0 Ha1 Hx Hn0 Hxn Hn Hlive Hcnt Hnz ltac:(intros a Ha; rewrite !Z.add_0_r, Hsp; exact (Hxs a Ha))
  Hamr Hra0 Hhv Hin ltac:(zlia) ltac:(reflexivity) ltac:(zlia) ltac:(zlia) Hpfx Hfr Hgp Htp Hra Hraw Hch Hf0
  HCTX HRM Hmo) as HSR.
eapply SRrG_mono; [exact (SRr_SRrG segs R WLE_R _ _ _ HSR)|].
intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & Hc2 & HJ1 & Rest).
rewrite Z.add_0_l in HJ1. rewrite !Z.add_0_r, Hsp in Rest.
exists ly2, S2, Hp2, regs2, mem2, md2, res. split; [exact Hc2|]. split; [|exact Rest].
exact (aj_compose_x_xR_xs STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k o regsT ly2 S2 Hp2 W2 mem2 md2 1
  HJ Hsp Hneg Hbud HJ1).
Qed.
End CTXs.
End LIFTXS.
