(* CARRIED from a working branch 861bb2393db4053ec166d3688044f898f949bd22,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCe5x.v, sha256 60aa1000d5c2914faff070207e47062de8425b441c5dcfc635effd251da0c301.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the call journals YCe5.v:255-275 (ajournal) and
   YCbq.v:351-373 (ajournal) with the allocator invariant AR made the parameter ARx of YCbqG.v's shape; no other change. *)
(* YCe5x.v is the ONLY home of the ARx twins of YCe5.ajournal and YCbq.ajournal. A proof that needs YCe5's journal over a
   generic ARx (the consumer is fuzz_reply's lib/A/ACfl.v, whose tfib_lib_contract names YCe5.afn_pre and YCe5.ajournal)
   cites ajournal_e5x; a proof that needs YCbq's journal over a generic ARx cites ajournal_bq_x; nobody makes a second
   copy.
   The pre side is YCbqG.afn_pre_x, which already equals YCe5.afn_pre over ARx + Hp; this file makes no copy of it.
   ajournal_e5x is YCe5's text, so it differs from YCbqG.ajournal_x (YCbqG.v:242-265) in exactly three deliberate places:
   (1) the io conjunct is `same_io md md'`, not `aos_step FP md md'` (YCbqG.v:255);
   (2) the image clause has no `~ Exists (in_zr a) PST -> fp_spares FP a ->` premise (YCbqG.v:255), so Section x takes
       no PST and no YI16.sink_head instance;
   (3) there is no `ly_extra` frame conjunct (YCbqG.v:263-264).
   ARx takes the ghost poisoned-head set Hp, so ajournal_e5x takes Hp (before) and Hp' (after) at the positions
   YCbqG.ajournal_x takes them; only Hp' is read, as the argument of ARx at the post state. YCbqG's hl occurs only in
   its laws record AR_laws_x, never in a journal, so neither journal of this file takes hl.
   The check lemma ajournal_e5x_AR proves the twin: at ARx := cgif's AR with Hp ignored (YCbqG.AR_laws_x_of_AR's
   instance), ajournal_e5x is YCe5.ajournal by reflexivity.
   ajournal_bq_x (Section bq) is YCbq's text YCbq.v:351-373 with AR -> ARx and Hp / Hp' placed as in ajournal_e5x. It
   keeps aos_step, the fp_spares premise and the ly_extra conjunct, so Section bq takes YCbq's YI16.sink_head context SK
   (fp_spares reads it) and no PST. The check lemma ajournal_bq_x_AR proves the twin: at ARx := cgif's AR with Hp
   ignored, ajournal_bq_x is YCbq.ajournal by reflexivity. ajournal_bq_x_iff_x links the two ARx forms for every ARx:
   at PST = [], ajournal_bq_x is YCbqG.ajournal_x, whose one extra premise `~ Exists (in_zr a) []` (YCbqG.v:255) holds.
   Routing of the journal texts of fuzz_preset (checked at 459129c18903): only YCe5 and YCbq define a constant
   `ajournal`; YC80 and YE01 name one by a notation; every other module whose code says `ajournal` (YC5d, YCeg, YCeh,
   YCem, YCfl, YD1r, YD1w) cites one of the two constants and routes as its body.
     YCe5  own body, YCe5.v:255-275 -> ajournal_e5x (this file); identical modulo AR (ajournal_e5x_AR).
     YCbq  own body, YCbq.v:351-373 -> ajournal_bq_x (this file); identical modulo AR (ajournal_bq_x_AR).
           YCbqG.ajournal_x differs from it only in the PST premise YCbqG.v:255 (ajournal_bq_x_iff_x for every ARx,
           ajournal_x_YCbq at ARx := AR: iffs at PST = []).
     YC80  no body: YC80.v:51 is `Local Notation ajournal := (ajournal segs B)`, which is YCbq.ajournal (YC80.v:18
           imports YCbq and no module that defines another ajournal) -> as YCbq.
     YE01  no body: YE01.v:49, the same notation, YCbq.ajournal by YE01.v:21 -> as YCbq.
   YCbq.ajournal differs from YCe5.ajournal at YCbq.v:356 (aos_step FP for same_io), YCbq.v:363 (the extra premise
   fp_spares FP a) and YCbq.v:371-372 (the extra ly_extra conjunct). So no module needs a third journal twin.
   THE KEEP LEMMA (Section k): acall_kept_of_journal_e5x is YCe5.v:842-859 acall_kept_of_journal with ajournal ->
   ajournal_e5x and its AR premise -> ARx; the proof is YCe5's and uses no law. Its conclusion is YCe5.acall_kept
   (YCe5.v:704-715) as it stands, because acall_kept names no AR: a callee journal keeps every byte of a block live
   before and after the call outside E (E covers FP), every image byte that is not an owned static and not errno, every
   byte of a caller frame outside E, and every byte at or above alloc_ceiling outside the callee's stack window. No
   journal conjunct keeps the errno cell (YCe5.v:267 excludes it) or a byte below alloc_ceiling that is in no block, in
   no frame and not in_img. acall_kept_of_journal_e5x_AR checks the twin against YCe5's statement at ARx := AR.
   THE HELPER TWINS (Section k): of the YCe5 names that the closed walk of fuzz_reply's lib/A cites, five state AR:
   sep_blocks (YCe5.v:323) is YCbqG.sep_blocks_x and frames_bounds (YCe5.v:353) is YCbqG.frames_bounds_x; this file
   adds amem_range_of_block_x (YCe5.v:1519, from alx_blocks), shent_app_of_block_x (YCe5.v:2045, from alx_blocks) and
   shent_app_of_frame_x (YCe5.v:2056, from YCbqG.frames_bounds_x), each with a check _AR against YCe5's statement. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Export YM04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCe5.
(* not imported: YCbq and YCbqG redefine YCe5's names (ajournal, frame_rng, astk_ok); the route check names them qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI16 YCbq YCbqG.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Definition ajournal_e5x (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ARx ly' S' Hp' W' mem' md' /\
layout_le (length (st_secs S)) ly ly' /\ (length (st_secs S) <= length (st_secs S'))%nat /\ wle W W' /\ same_io md md' /\
frames S' = own ++ frames S /\
st_nev S' <= st_nev S + k /\ 0 <= k /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> inFP FP (p + i)) /\
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
astk_ok STK ly sp0 /\
qtight S'                                              .
End x.
(* KEEP PERMANENTLY: this check is what stops ajournal_e5x drifting from YCe5.ajournal; never delete or weaken it. *)
Lemma ajournal_e5x_AR : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (segs : list Segment) (B : asyms)
STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_e5x segs B (fun ly S (_ : list Z) W mem md => AR segs B ly S W mem md)
  STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k =
YCe5.ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof. intros. reflexivity. Qed.
(* YCbqG.ajournal_x against YCbq (whose route, with YC80 and YE01, is ajournal_bq_x: see the header): at cgif's AR with
   Hp ignored and no program statics (PST = []), YCbqG.ajournal_x is YCbq.ajournal. An iff, not an equation:
   ajournal_x's premise `~ Exists (in_zr a) []` holds but is not absent. *)
Lemma ajournal_x_YCbq : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (segs : list Segment)
(B : asyms) STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
YCbqG.ajournal_x segs B [] (fun ly S (_ : list Z) W mem md => AR segs B ly S W mem md)
  STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k <->
YCbq.ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros. unfold YCbqG.ajournal_x, YCbq.ajournal.
split; intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12);
do 10 (split; [assumption|]); (split; [|exact H12]).
- intros a Ha Ho He Hf. apply (H11 a Ha Ho He); [intros Hx; inversion Hx | exact Hf].
- intros a Ha Ho He _ Hf. exact (H11 a Ha Ho He Hf).
Qed.
Section bq. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* YCbq.v:351-373 ajournal. YCbq's own names (aos_step, fp_spares, frame_rng, astk_ok) are written qualified: this file
   does not import YCbq, and YCe5, which it imports, has its own frame_rng and astk_ok. *)
Definition ajournal_bq_x (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ARx ly' S' Hp' W' mem' md' /\
layout_le (length (st_secs S)) ly ly' /\ (length (st_secs S) <= length (st_secs S'))%nat /\ wle W W' /\ YCbq.aos_step FP md md' /\
frames S' = own ++ frames S /\
st_nev S' <= st_nev S + k /\ 0 <= k /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) -> YCbq.fp_spares FP a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (YCbq.frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> inFP FP (p + i)) /\
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
YCbq.astk_ok STK ly sp0 /\
(forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
qtight S'                                              .
End bq.
(* KEEP PERMANENTLY: this check is what stops ajournal_bq_x drifting from YCbq.ajournal; never delete or weaken it. *)
Lemma ajournal_bq_x_AR : forall {rc : YM05.RunCeil} {SK : YI16.sink_head} (segs : list Segment)
(B : asyms) STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_bq_x segs B (fun ly S (_ : list Z) W mem md => AR segs B ly S W mem md)
  STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k =
YCbq.ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof. intros. reflexivity. Qed.
(* The two ARx forms of YCbq's journal, linked for every ARx: at PST = [], ajournal_bq_x is YCbqG.ajournal_x. An iff, not
   an equation: ajournal_x's premise `~ Exists (in_zr a) []` holds but is not absent. *)
Lemma ajournal_bq_x_iff_x : forall {rc : YM05.RunCeil} {SK : YI16.sink_head} (segs : list Segment)
(B : asyms) (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_bq_x segs B ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k <->
YCbqG.ajournal_x segs B [] ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros. unfold ajournal_bq_x, YCbqG.ajournal_x.
split; intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12);
do 10 (split; [assumption|]); (split; [|exact H12]).
- intros a Ha Ho He _ Hf. exact (H11 a Ha Ho He Hf).
- intros a Ha Ho He Hf. apply (H11 a Ha Ho He); [intros Hx; inversion Hx | exact Hf].
Qed.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : YCbqG.AR_laws_x segs B ARx hl.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Abbreviation ajournal_e5x := (ajournal_e5x segs B ARx).
(* YCe5.v:842 acall_kept_of_journal *)
Lemma acall_kept_of_journal_e5x : forall stk sp1 FP1 nf lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 (E : Z -> Prop),
ajournal_e5x stk sp1 FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 ->
ARx lyc Sc Hpc W memc mdc ->
(forall a, inFP FP1 a -> E a) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) -> In (b, m) (ablocks B ly2 S2)) ->
acall_kept segs B lyc Sc W memc W2 mem2 (sp1 - stk) sp1 E.
Proof.
intros stk sp1 FP1 nf lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 E
(HAR2 & Hly2 & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & HQT) HAR HFE Hlive.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact G1|]. split.
{ intros b m i Hb Hi HnE. apply (G2 b m i Hb (Hlive b m i Hb Hi HnE) Hi). intros Hf. exact (HnE (HFE _ Hf)). }
split; [exact G3|]. split.
{ intros cid pos a Hin Hr HnE. apply (G4 cid pos a); [cbn; exact Hin | exact Hr | intros Hf; exact (HnE (HFE _ Hf))]. }
split; [|exact Hpres].
intros a Ha Hs Hp. eapply apresent_transfer; [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; [exact Ha | exact Hs] | exact Hp].
Qed.
(* YCe5.v:1519 amem_range_of_block *)
Lemma amem_range_of_block_x : forall ly S Hp W mem md p m a n,
ARx ly S Hp W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m -> amem_range a n.
Proof.
intros ly S Hp W mem md p m a n HAR Hin H1 H2.
destruct (YCbqG.alx_blocks segs B ARx LAWS ly S Hp W mem md p m HAR Hin) as (_ & _ & Hc & [Hh Hh2] & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). zlia.
Qed.
(* YCe5.v:2045 shent_app_of_block *)
Lemma shent_app_of_block_x : forall ly S Hp W mem md E Bx (m : nat) q p n wlo whi M,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> p <= q + wlo -> wlo < whi -> q + whi <= p + req_size n ->
shent_ok segs Bx E M (mkSHE m whi wlo).
Proof.
intros ly S Hp W mem md E Bx m q p n wlo whi M HAR Hin HB Hm Hlo Hlt Hhi.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. split.
- apply range_addressable_nil. zlia.
- destruct (YCbqG.alx_blocks segs B ARx LAWS ly S Hp W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia.
Qed.
(* YCe5.v:2056 shent_app_of_frame *)
Lemma shent_app_of_frame_x : forall ly S Hp W mem md E Bx (m : nat) q cid pos wlo whi M,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> frame_addr ly cid pos <= q + wlo -> wlo < whi ->
q + whi <= frame_addr ly cid pos + fs_frame_bytes cid ->
shent_ok segs Bx E M (mkSHE m whi wlo).
Proof.
intros ly S Hp W mem md E Bx m q cid pos wlo whi M HAR Hin HB Hm Hlo Hlt Hhi.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. split.
- apply range_addressable_nil. zlia.
- destruct (YCbqG.frames_bounds_x segs B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & _ & Happ).
intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia.
Qed.
End k.
(* The checks of Section k: at ARx := cgif's AR with Hp ignored, each twin gives YCe5's statement word for word (the
   helper twins under the laws record at that instance; the keep lemma needs no law). *)
Lemma acall_kept_of_journal_e5x_AR : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (segs : list Segment) (B : asyms),
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
forall stk sp1 FP1 nf lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 (E : Z -> Prop),
YCe5.ajournal segs B stk sp1 FP1 lyc Sc W memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
AR segs B lyc Sc W memc mdc ->
(forall a, inFP FP1 a -> E a) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) -> In (b, m) (ablocks B ly2 S2)) ->
acall_kept segs B lyc Sc W memc W2 mem2 (sp1 - stk) sp1 E.
Proof.
intros fx rc segs B Hlow stk sp1 FP1 nf lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 E.
exact (acall_kept_of_journal_e5x segs B (fun ly S (_ : list Z) W mem md => AR segs B ly S W mem md) Hlow
  stk sp1 FP1 nf lyc Sc [] W memc mdc ly2 S2 [] W2 mem2 md2 k1 E).
Qed.
Lemma amem_range_of_block_x_AR : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (segs : list Segment) (B : asyms) (hl : Z),
YCbqG.AR_laws_x segs B (fun ly S (_ : list Z) W mem md => AR segs B ly S W mem md) hl ->
forall ly S W mem md p m a n,
AR segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m -> amem_range a n.
Proof. intros fx rc segs B hl L ly S W mem md. exact (amem_range_of_block_x segs B _ L ly S [] W mem md). Qed.
Lemma shent_app_of_block_x_AR : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (segs : list Segment) (B : asyms) (hl : Z),
YCbqG.AR_laws_x segs B (fun ly S (_ : list Z) W mem md => AR segs B ly S W mem md) hl ->
forall ly S W mem md E Bx (m : nat) q p n wlo whi M,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> p <= q + wlo -> wlo < whi -> q + whi <= p + req_size n ->
shent_ok segs Bx E M (mkSHE m whi wlo).
Proof. intros fx rc segs B hl L ly S W mem md. exact (shent_app_of_block_x segs B _ L ly S [] W mem md). Qed.
Lemma shent_app_of_frame_x_AR : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (segs : list Segment) (B : asyms) (hl : Z),
YCbqG.AR_laws_x segs B (fun ly S (_ : list Z) W mem md => AR segs B ly S W mem md) hl ->
forall ly S W mem md E Bx (m : nat) q cid pos wlo whi M,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> frame_addr ly cid pos <= q + wlo -> wlo < whi ->
q + whi <= frame_addr ly cid pos + fs_frame_bytes cid ->
shent_ok segs Bx E M (mkSHE m whi wlo).
Proof. intros fx rc segs B hl L ly S W mem md. exact (shent_app_of_frame_x segs B _ L ly S [] W mem md). Qed.
