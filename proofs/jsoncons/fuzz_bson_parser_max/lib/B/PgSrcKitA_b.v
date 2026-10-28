(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PGSKA.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma src_accG (M : word -> option byte) (os isp sbp : Z) (src : PM.srcst) :
  PM.src_fields_at RSEGS PMSPA.accA M os isp sbp src -> PM.nullis_at RSEGS PMA.AD PMSPA.accA M (os + 8) -> PMSPA.accA M (os + 8) 288.
Proof.
  intros SF NI. destruct NI as (_ & _ & NC & _ & _ & IOS). destruct IOS as (_ & _ & _ & _ & _ & _ & _ & IC & _).
  destruct SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC).
  intros a Ha. destruct (Z_lt_le_dec a (os + 8 + 80)) as [X|X]; [apply NC; lia|].
  destruct (Z_lt_le_dec a (os + 8 + 80 + 152)) as [Y|Y]; [apply IC; lia|]. apply SC; lia.
Qed.
(* [comment removed for export] *)
Lemma iss_accG (M : word -> option byte) (ois : Z) (str : PM.vstr) (sm : PM.strm) :
  PM.iss_at RSEGS PMA.AD PMSPA.accA M ois str sm -> PMSPA.accA M ois 272.
Proof.
  intros IA. destruct IA as (_ & _ & C0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _). destruct IOS as (_ & _ & _ & _ & _ & _ & _ & IC & _).
  intros a Ha. destruct (Z_lt_le_dec a (ois + 120)) as [X|X]; [apply C0; lia| apply IC; lia].
Qed.

(* [comment removed for export] *)
Lemma aobjA_sub FF lo hi a n : PMSPA.aobjA FF lo (hi - lo) -> lo <= a -> a + n <= hi -> PMSPA.aobjA FF a n.
Proof. intros (f & Hf & X1 & X2) H1 H2. exists f. split; [exact Hf|]. lia. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma src_visG LB FF LK cr Aw M model os isp sbp src sp scr :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PMSPA.aobjA FF os 296 -> os mod 8 = 0 ->
  PM.src_fields_at RSEGS PMSPA.accA M os isp sbp src -> PM.nullis_at RSEGS PMA.AD PMSPA.accA M (os + 8) -> L5CA.astk ar M sp scr ->
  let MV := mrestrict (ahid Aw model) M in
  (6905856 <= os <= 140737488355032 /\ os mod 8 = 0 /\ (2147446784 + 17592186048512 <= os \/ os + 296 <= 2147446784))
  /\ L5KA.zeros_at MV ((os + 8) / 8 + 2147450880) 36 /\ L5.writable RSEGS MV os 296 /\ os + 296 <= ahl_ceil ar
  /\ (forall a n, os <= a -> a + n <= os + 296 -> L5A.avis (ahid Aw model) a n)
  /\ PMSPA.aobjA FF os 296 /\ ar_fs ar <= os /\ os + 296 <= ar_fs ar + FS_BYTES.
Proof.
  intros HH AO O8 SF NI ASTK MV.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model os 296 sp scr HH (PMKA.aobj_of_aobjA FF os 296 AO O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  pose proof (src_accG M os isp sbp src SF NI) as ACC.
  split; [split; [lia| split; [exact O8| exact OBIG]]|].
  split.
  { apply (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (os + 8) 288 HH).
    - destruct AO as (f & Hf' & X1 & X2). exists f. split; [exact Hf'|]. lia.
    - replace (os + 8) with (os + 1 * 8) by lia. rewrite Z_mod_plus_full. exact O8.
    - lia. - reflexivity. - exact ACC. }
  split.
  { apply (proj2 (L5A.writable_vis _ M os 296 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]. }
  split; [lia|]. split; [intros a n Ha Hn; eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. split; [exact AO|].
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _).
  destruct AO as (f & Hf & X1 & X2). destruct (WF _ Hf) as (W1 & W2 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma iss_visG LB FF LK cr Aw M model ois str sm sp scr :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PMSPA.aobjA FF ois 272 -> ois mod 8 = 0 ->
  PM.iss_at RSEGS PMA.AD PMSPA.accA M ois str sm -> L5CA.astk ar M sp scr ->
  let MV := mrestrict (ahid Aw model) M in
  (6905856 <= ois <= 140737488355056 /\ ois mod 8 = 0 /\ (2147446784 + 17592186048512 <= ois \/ ois + 272 <= 2147446784))
  /\ L5KA.zeros_at MV (ois / 8 + 2147450880) 34 /\ L5.writable RSEGS MV ois 272 /\ ois + 272 <= ahl_ceil ar
  /\ (forall a n, ois <= a -> a + n <= ois + 272 -> L5A.avis (ahid Aw model) a n)
  /\ PMSPA.aobjA FF ois 272.
Proof.
  intros HH AO O8 IA ASTK MV.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model ois 272 sp scr HH (PMKA.aobj_of_aobjA FF ois 272 AO O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  pose proof (iss_accG M ois str sm IA) as ACC.
  split; [split; [lia| split; [exact O8| exact OBIG]]|].
  split; [apply (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model ois 272 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC)|].
  split; [apply (proj2 (L5A.writable_vis _ M ois 272 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
  split; [lia|]. split; [intros a n Ha Hn; eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. exact AO.
Qed.

(* [comment removed for export] *)
Lemma src_piece_issG LB FF LK cr Aw M2 M3 V os ois str sm sp scr :
  ri_inv HI LB FF LK cr Aw M2 V -> PMSPA.aobjA FF os 296 -> PMSPA.aobjA FF ois 272 -> (os + 296 <= ois \/ ois + 272 <= os) ->
  incl (PM.vs_own str) LB -> L5SAR.ek L ar LB FF sp scr [(os + 256, 40)] M2 M3 ->
  PM.iss_at RSEGS PMA.AD PMSPA.accA M2 ois str sm -> PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm.
Proof.
  intros HH AOS AOI APT INC EK IA.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (WS : PMKA.wapp [(os + 256, 40)]).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & _).
    destruct AOS as (f & Hf & Y1 & Y2). destruct (WF _ Hf) as (W1 & W2 & _). unfold app_mem, FS_BYTES in FSAPP, W2.
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; destruct FSAPP as (F0 & [F1|F1] & F2); [left; lia| right; lia]| apply PMKA.wapp_nil]. }
  apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp scr _ M2 M3 EK WS FRB BRB ois str sm AOI INC); [| |exact IA].
  - intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
  - intros c0 n0 p0 E i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. subst str.
    assert (TIN : In (p0, c0) LB) by (apply INC; cbn; left; reflexivity).
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ p0 c0 _ 296 HH TIN AOS) as [X|X]; lia.
Qed.

End WithHeap.

(* [comment removed for export] *)
Lemma src_fields_updG (M M' : word -> option byte) os isp sbp qc de rem de' rem' :
  PM.src_fields_at RSEGS PMSPA.accA M os isp sbp (PM.SRC qc de rem) -> 0 <= os -> os + 296 <= 2 ^ 64 ->
  PMFA.agA M M' os 256 -> PMFA.agsh M M' (os + 256) 40 -> L5.defined M' (os + 256) 8 ->
  PMFA.agsh M M' qc PM.CHUNK -> L5.defined M' qc PM.CHUNK ->
  L5.u64_at RSEGS M' (os + 264) qc -> L5.u64_at RSEGS M' (os + 272) PM.CHUNK ->
  L5.u64_at RSEGS M' (os + 280) de' -> L5.u64_at RSEGS M' (os + 288) rem' ->
  qc <= de' -> 0 <= rem' -> de' + rem' <= qc + PM.CHUNK ->
  PM.src_fields_at RSEGS PMSPA.accA M' os isp sbp (PM.SRC qc de' rem').
Proof.
  intros SF Ho Ho' [AG SH] SH2 D256 SHQ DQ C1 C2 C3 C4 Q1 Q2 Q3.
  destruct SF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & CC & C240).
  unfold PM.src_fields_at. cbn [PM.sr_qc PM.sr_de PM.sr_rem] in *.
  split; [apply (L5C.u64_at_agree RSEGS M M'); [eapply (L5C.agree_on_sub M M' os 256); [exact AG| lia| lia]| lia| lia| exact F1]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [eapply (L5C.agree_on_sub M M' os 256); [exact AG| lia| lia]| lia| lia| exact F2]|].
  split; [exact D256|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact G4|]. split; [exact DQ|].
  split; [exact (PMFA.accA_agree M M' qc PM.CHUNK SHQ CC)|].
  apply (PMFA.accA_agree M M' (os + 240) 56); [| exact C240].
  intros x Hx. destruct (Z_lt_le_dec x (os + 256)) as [X|X]; [apply SH; lia| apply SH2; lia].
Qed.

(* [comment removed for export] *)
Lemma src_fields_keepG (M M' : word -> option byte) os isp sbp src :
  PM.src_fields_at RSEGS PMSPA.accA M os isp sbp src -> 0 <= os -> os + 296 <= 2 ^ 64 ->
  PMFA.agA M M' os 296 -> PMFA.agsh M M' (PM.sr_qc src) PM.CHUNK -> L5.defined M' (PM.sr_qc src) PM.CHUNK ->
  PM.src_fields_at RSEGS PMSPA.accA M' os isp sbp src.
Proof.
  intros SF Ho Ho' [AG SH] SHQ DQ.
  destruct SF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & CC & C240).
  unfold PM.src_fields_at.
  assert (U : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb X. apply (L5C.u64_at_agree RSEGS M M'); [eapply (L5C.agree_on_sub M M' os 296); [exact AG| lia| lia]| lia| lia| exact X]. }
  split; [apply U; [lia| lia| exact F1]|]. split; [apply U; [lia| lia| exact F2]|].
  split; [apply (L5C.defined_agree M M'); [eapply (L5C.agree_on_sub M M' os 296); [exact AG| lia| lia]| exact F3]|].
  split; [apply U; [lia| lia| exact F4]|]. split; [apply U; [lia| lia| exact F5]|]. split; [apply U; [lia| lia| exact F6]|]. split; [apply U; [lia| lia| exact F7]|].
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact DQ|].
  split; [exact (PMFA.accA_agree M M' _ PM.CHUNK SHQ CC)|].
  apply (PMFA.accA_agree M M' (os + 240) 56); [| exact C240]. eapply (PMFA.agsh_sub M M' os 296); [exact SH| lia| lia].
Qed.

End PGSKA.
