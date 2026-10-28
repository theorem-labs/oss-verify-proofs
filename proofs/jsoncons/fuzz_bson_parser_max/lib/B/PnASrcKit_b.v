(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMASK.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma src_acc (M : word -> option byte) (op ois : Z) (s : PM.pst) :
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M op ois s -> PMSPA.accA M (op + 32) 288.
Proof.
  intros PA. destruct PA as (_ & _ & _ & _ & _ & _ & _ & _ & NI & SF & _).
  destruct NI as (_ & _ & NC & _ & _ & IOS). destruct IOS as (_ & _ & _ & _ & _ & _ & _ & IC).
  destruct SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC).
  intros a Ha. destruct (Z_lt_le_dec a (op + 32 + 80)) as [X|X]; [apply NC; lia|].
  destruct (Z_lt_le_dec a (op + 32 + 80 + 152)) as [Y|Y]; [apply IC; lia|]. apply SC; lia.
Qed.

(* [comment removed for export] *)
Lemma parser_src_fieldsA (M M' : word -> option byte) op ois s de' rem' :
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  PMFA.agA M M' op 280 -> PMFA.agA M M' (op + 320) 64 -> PMFA.agsh M M' (op + 280) 40 ->
  0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 -> PMFA.agA M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> PMFA.agA M M' (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> PMFA.agA M M' p c) ->
  mem_grows M M' -> L5.u64_at RSEGS M' (op + 288) (PM.sr_qc (PM.p_src s)) -> L5.u64_at RSEGS M' (op + 296) PM.CHUNK ->
  L5.u64_at RSEGS M' (op + 304) de' -> L5.u64_at RSEGS M' (op + 312) rem' ->
  PM.sr_qc (PM.p_src s) <= de' -> 0 <= rem' -> de' + rem' <= PM.sr_qc (PM.p_src s) + PM.CHUNK ->
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M' op ois (PMSPA.with_src s (PM.SRC (PM.sr_qc (PM.p_src s)) de' rem')).
Proof.
  intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
         [AG1 SH1] [AG2 SH2] SH3 Hq Hq' AGQ Hb Hb' AGB AGT MG C1 C2 C3 C4 Q1 Q2 Q3.
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & CC & C240).
  unfold PMSPA.with_src, PM.parser_at, PM.src_fields_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.sr_qc PM.sr_de PM.sr_rem] in *.
  assert (U64 : forall a v, op <= a -> a + 8 <= op + 280 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
  assert (U64b : forall a v, op + 320 <= a -> a + 8 <= op + 384 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact X]. }
  assert (U32 : forall a v, op <= a -> a + 4 <= op + 280 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
  assert (U8 : forall a v, op <= a -> a + 1 <= op + 280 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
  split; [apply U64; [lia|lia|exact H0]|].
  split; [apply (L5.defined_grows M M' op 384 MG D)|].
  split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH1; lia| exact C24]|].
  split; [apply U8; [lia|lia|exact H8]|]. split; [apply U8; [lia|lia|exact H9]|]. split; [apply U32; [lia|lia|exact H12]|].
  split; [apply U8; [lia|lia|exact H16]|]. split; [apply U32; [lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS PMA.AD M M' (op + 32)); [lia|lia| split; [intros i Hi; apply AG1; lia| intros x Hx; apply SH1; lia]| exact NI]|].
  split.
  { split; [apply U64; [lia|lia|exact F1]|]. split; [apply U64; [lia|lia|exact F2]|].
    split; [apply (L5.defined_grows M M' _ 8 MG F3)|].
    split; [replace (op + 24 + 264) with (op + 288) by lia; exact C1|]. split; [replace (op + 24 + 272) with (op + 296) by lia; exact C2|].
    split; [replace (op + 24 + 280) with (op + 304) by lia; exact C3|]. split; [replace (op + 24 + 288) with (op + 312) by lia; exact C4|].
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact G4|].
    split; [destruct AGQ as [AGq _]; apply (L5C.defined_agree M M'); [exact AGq| exact DC]|].
    split; [destruct AGQ as [_ SHq]; apply (PMFA.accA_agree M M' _ _ SHq CC)|].
    apply (PMFA.accA_agree M M' (op + 24 + 240) 56); [intros x Hx; destruct (Z_lt_le_dec x (op + 280)) as [X|X]; [apply SH1; lia| apply SH3; lia]| exact C240]. }
  split; [apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact H320]|].
  split; [apply U64b; [lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH2; lia| exact C320]|].
  split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| split; [intros i Hi; apply AG2; lia| intros x Hx; apply SH2; lia]| exact AGT| exact TB]|].
  split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|lia|lia| intros i Hi; apply AG2; lia| exact AGB| exact VEC]|].
  split; [exact B1|]. split; [exact B2|]. exact B3.
Qed.

(* [comment removed for export] *)
Lemma agsh_blk L ar LB FF sp scr W M M' q m :
  L5SAR.ek L ar LB FF sp scr W M M' -> PMKA.wapp W -> In (q, m) LB -> 0 <= q -> q + m <= 2 ^ 47 -> PMFA.agsh M M' q m.
Proof.
  intros E WAPP Hin Hq Hqm x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
  apply E. split; [lia|]. split.
  - unfold aclient, aclient_g. do 6 right. exists (q, m). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
  - apply (PMKA.wapp_outside_shadow W (S x) WAPP). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.

(* [comment removed for export] *)
Lemma parser_chunk_keepA (M M' : word -> option byte) op ois s :
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 -> PMFA.agA M M' op 384 ->
  0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 -> PMFA.agsh M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  L5.defined M' op 384 -> L5.defined M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> PMFA.agA M M' (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> PMFA.agA M M' p c) ->
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M' op ois s.
Proof.
  intros PA Ho Ho' [AG SH] Hq Hq' SHQ DOP DCQ Hb Hb' AGB AGT.
  pose proof PA as (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3).
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & CC & C240).
  assert (U64 : forall a v, op <= a -> a + 8 <= op + 384 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
  assert (U32 : forall a v, op <= a -> a + 4 <= op + 384 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
  assert (U8 : forall a v, op <= a -> a + 1 <= op + 384 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
  unfold PM.parser_at, PM.src_fields_at.
  split; [apply U64; [lia|lia|exact H0]|]. split; [exact DOP|].
  split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
  split; [apply U8; [lia|lia|exact H8]|]. split; [apply U8; [lia|lia|exact H9]|]. split; [apply U32; [lia|lia|exact H12]|].
  split; [apply U8; [lia|lia|exact H16]|]. split; [apply U32; [lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS PMA.AD M M' (op + 32)); [lia|lia| split; [intros i Hi; apply AG; lia| intros x Hx; apply SH; lia]| exact NI]|].
  split.
  { split; [apply U64; [lia|lia|exact F1]|]. split; [apply U64; [lia|lia|exact F2]|].
    split; [intros i Hi; replace (op + 24 + 256 + i) with (op + (280 + i)) by lia; apply DOP; lia|].
    split; [apply U64; [lia|lia|exact F4]|]. split; [apply U64; [lia|lia|exact F5]|]. split; [apply U64; [lia|lia|exact F6]|]. split; [apply U64; [lia|lia|exact F7]|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [exact DCQ|].
    split; [apply (PMFA.accA_agree M M' _ _ SHQ CC)|].
    apply (PMFA.accA_agree M M' (op + 24 + 240) 56); [intros x Hx; apply SH; lia| exact C240]. }
  split; [apply U32; [lia|lia|exact H320]|]. split; [apply U64; [lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
  split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| split; [intros i Hi; apply AG; lia| intros x Hx; apply SH; lia]| exact AGT| exact TB]|].
  split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|lia|lia| intros i Hi; apply AG; lia| exact AGB| exact VEC]|].
  split; [exact B1|]. split; [exact B2|]. exact B3.
Qed.

(* [comment removed for export] *)
Lemma iss_st_updA (M M' : word -> option byte) ois str g eg st st' :
  PM.iss_at RSEGS PMA.AD PMSPA.accA M ois str (PM.STRM g eg st) -> 0 <= ois -> ois + 272 <= 2 ^ 64 ->
  PMFA.agA M M' ois 152 -> PMFA.agA M M' (ois + 156) 116 -> PMFA.agsh M M' (ois + 152) 4 -> mem_grows M M' ->
  (forall c n p, str = PM.VLong c n p -> PMFA.agA M M' p c) ->
  L5.u32_at RSEGS M' (ois + 152) st' -> st' = 0 \/ st' = 2 ->
  PM.iss_at RSEGS PMA.AD PMSPA.accA M' ois str (PM.STRM g eg st').
Proof.
  intros IA Ho Ho' [AG1 SH1] [AG2 SH2] SH3 MG AGB C32 ST'.
  destruct IA as (H0 & D & C & H16 & H24 & H32 & H40 & H48 & H64 & VS & H104 & H112 & IOS & E1 & E2).
  destruct IOS as (I0 & I32 & I36 & I40 & I48 & IZ & ID & IC & IST).
  assert (U64 : forall a v, ois <= a -> a + 8 <= ois + 152 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
  assert (U64b : forall a v, ois + 156 <= a -> a + 8 <= ois + 272 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact X]. }
  unfold PM.iss_at, PM.iosb_at. cbn [PM.sm_g PM.sm_eg PM.sm_st] in *.
  split; [apply U64; [lia|lia|exact H0]|]. split; [apply (L5.defined_grows M M' _ _ MG D)|].
  split; [apply (PMFA.accA_agree M M' ois 120); [intros x Hx; apply SH1; lia| exact C]|].
  split; [apply U64; [lia|lia|exact H16]|]. split; [apply U64; [lia|lia|exact H24]|]. split; [apply U64; [lia|lia|exact H32]|].
  split; [apply U64; [lia|lia|exact H40]|]. split; [apply U64; [lia|lia|exact H48]|]. split; [apply U64; [lia|lia|exact H64]|].
  split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (ois + 80)); [lia|lia| split; [intros i Hi; apply AG1; lia| intros x Hx; apply SH1; lia]| exact AGB| exact VS]|].
  split; [apply U64; [lia|lia|exact H104]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact H112]|].
  split.
  { split; [apply U64; [lia|lia|exact I0]|]. split; [replace (ois + 120 + 32) with (ois + 152) by lia; exact C32|].
    split; [apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact I36]|].
    split; [apply U64b; [lia|lia|exact I40]|]. split; [apply U64b; [lia|lia|exact I48]|].
    split; [apply (PMF.zeros_at_agree M M'); [intros i Hi; apply AG2; lia| exact IZ]|].
    split; [apply (L5.defined_grows M M' _ _ MG ID)|].
    split; [apply (PMFA.accA_agree M M' (ois + 120) 152); [intros x Hx; destruct (Z_lt_le_dec x (ois + 152)) as [X|X]; [apply SH1; lia|];
                                                          destruct (Z_lt_le_dec x (ois + 156)) as [Y|Y]; [apply SH3; lia| apply SH2; lia]| exact IC]|].
    exact ST'. }
  split; [exact E1| exact E2].
Qed.

(* [comment removed for export] *)
Lemma iss_unread_whereA M ois str sm :
  PM.iss_at RSEGS PMA.AD PMSPA.accA M ois str sm ->
  (ois + 81 <= PM.sm_g sm /\ PM.sm_eg sm <= ois + 104)
  \/ (exists c n p, str = PM.VLong c n p /\ p <= PM.sm_g sm /\ PM.sm_eg sm <= p + c).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _ & _ & _ & E1 & E2).
  destruct VS as (D & _ & H). destruct str as [n|c n p]; cbn [PM.vs_data PM.vs_size] in *.
  - destruct H as (Hn & _). left. lia.
  - destruct H as (_ & _ & _ & Hn & _). right. exists c, n, p. split; [reflexivity| lia].
Qed.
Lemma iss_size_ltA M ois str sm : PM.iss_at RSEGS PMA.AD PMSPA.accA M ois str sm -> 0 <= PM.sm_eg sm - PM.sm_g sm < 2 ^ 27.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _ & _ & _ & E1 & E2).
  destruct VS as (D & _ & H). destruct str as [n|c n p]; cbn [PM.vs_data PM.vs_size] in *.
  - destruct H as (Hn & _). lia.
  - destruct H as (_ & _ & _ & Hn & Hc & _). lia.
Qed.
Lemma elem_of_InA (x : Z) (l : list Z) : In x l -> x ∈ l.
Proof. induction l as [|a l IH]; intros H; [destruct H|]. destruct H as [<-|H]; [constructor| constructor; apply IH; exact H]. Qed.
Lemma fst_neq_appA (l1 l2 : list (Z * Z)) B1 m1 B2 m2 :
  NoDup (map fst (l1 ++ l2)) -> In (B1, m1) l1 -> In (B2, m2) l2 -> B1 <> B2.
Proof.
  induction l1 as [|a l1 IH]; intros ND H1 H2; [destruct H1|]. cbn [app map] in ND. inversion ND as [|x l NI ND']. subst x l.
  destruct H1 as [->|H1].
  - cbn [fst] in NI. intros E. subst B2. apply NI. apply elem_of_InA. rewrite map_app. apply in_or_app. right. apply (in_map fst l2 (B1, m2) H2).
  - apply IH; assumption.
Qed.

(* [comment removed for export] *)
Lemma defined_dk L ar LB FF sp scr M M' a n :
  L5SAR.dk L ar LB FF sp scr M M' -> (forall i, a <= i < a + n -> aclient L ar LB FF sp scr i) -> 0 <= a -> a + n <= 2 ^ 64 ->
  L5.defined M a n -> L5.defined M' a n.
Proof.
  intros DK CL Ha Hn D i Hi. replace (a + i) with (a + i) by lia. apply (DK (a + i)); [lia| apply CL; lia| apply D; lia].
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma mach_vis LB FF LK cr Aw M model :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PMSTA.base_okA RSEGS PMA.AD M ->
  L5.img_clear (mrestrict (ahid Aw model) M) 65536 1282048 /\ L5.u64_at RSEGS (mrestrict (ahid Aw model) M) 1309752 2147450880
  /\ L5.u32_at RSEGS (mrestrict (ahid Aw model) M) 1309760 1.
Proof.
  intros HH BASE.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (_ & _ & VIMG & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (_ & CSB & CUAR & _).
  split; [apply L5A.img_clear_mrestrict; destruct BASE as (IC & _); cbn [pa_rw_lo PMA.AD ADDR_A] in IC; exact IC|].
  split.
  - apply (proj2 (L5A.u64_at_vis _ M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB.
  - apply (proj2 (L5A.u32_at_vis _ M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR.
Qed.

(* [comment removed for export] *)
Lemma stk_vis LB FF LK cr Aw M model sp scr fr :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.astk ar M sp scr -> 0 <= fr <= scr ->
  ahl_ceil ar + 4096 + fr <= sp /\ sp <= 2 ^ 47 /\ L5.writable RSEGS (mrestrict (ahid Aw model) M) (sp - fr) fr.
Proof.
  intros HH ASTK Hf. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (_ & VIS & _).
  split; [lia|]. split; [lia|].
  apply (proj2 (L5A.writable_vis _ M (sp - fr) fr (VIS (sp - fr) fr ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
  apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M (sp - scr) scr); [exact SDEF| lia| lia]. lia. lia.
Qed.

(* [comment removed for export] *)
Lemma src_vis LB FF LK cr Aw M model fb ois s sp scr :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PMSPA.frame_okA FF fb ->
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M (PMSPA.o_p PMA.AD fb) ois s -> L5CA.astk ar M sp scr ->
  let os := PMSPA.o_src PMA.AD fb in let MV := mrestrict (ahid Aw model) M in
  (6905856 <= os <= 140737488355032 /\ os mod 8 = 0 /\ (2147446784 + 17592186048512 <= os \/ os + 296 <= 2147446784))
  /\ L5KA.zeros_at MV ((os + 8) / 8 + 2147450880) 36 /\ L5.writable RSEGS MV os 296 /\ os + 296 <= ahl_ceil ar
  /\ (forall a n, os <= a -> a + n <= os + 296 -> L5A.avis (ahid Aw model) a n)
  /\ PMSPA.aobjA FF os 296 /\ ar_fs ar <= os /\ os + 296 <= ar_fs ar + FS_BYTES.
Proof.
  intros HH FOK PA ASTK os MV. destruct FOK as ((rs & Hf) & F1024). cbn [pa_frame PMA.AD ADDR_A] in *.
  assert (AO : PMSPA.aobjA FF os 296).
  { exists (fb, 4, rs). split; [exact Hf|]. unfold os, PMSPA.o_src, PMSPA.o_p. cbn [ff_addr ff_class ff_bytes pa_off_p PMA.AD ADDR_A].
    unfold ff_bytes. cbn. lia. }
  assert (O8 : os mod 8 = 0).
  { unfold os, PMSPA.o_src, PMSPA.o_p. cbn [pa_off_p PMA.AD ADDR_A]. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
    rewrite Dm. replace (1024 * (fb / 1024) + 464 + 24) with ((128 * (fb / 1024) + 61) * 8) by lia. apply Z_mod_mult. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model os 296 sp scr HH (PMKA.aobj_of_aobjA FF os 296 AO O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  assert (ACC : PMSPA.accA M (os + 8) 288).
  { replace (os + 8) with (PMSPA.o_p PMA.AD fb + 32) by (unfold os, PMSPA.o_src; lia). exact (src_acc M _ ois s PA). }
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
  destruct (WF _ Hf) as (W1 & W2 & _). unfold ff_addr, ff_class in W1, W2. cbn in W1, W2. unfold ff_bytes in W2. change (64 * 2 ^ 4) with 1024 in W2.
  unfold os, PMSPA.o_src, PMSPA.o_p. cbn [pa_off_p PMA.AD ADDR_A]. unfold FS_BYTES in *. split; lia.
Qed.

Lemma dep_img a : PMST.dep PMA.AD a -> 0x6722c0 <= a < 0x694074.
Proof.
  unfold PMST.dep, pm_foot, pm_initc. cbn [pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A app].
  intros [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
  - repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
  - lia.
  - repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma base_keep LB FF sp scr W M M' :
  L5SAR.ek L ar LB FF sp scr W M M' -> (forall a, 65536 <= a < 6905856 -> L5.outside W a) -> PMSTA.base_okA RSEGS PMA.AD M -> PMSTA.base_okA RSEGS PMA.AD M'.
Proof.
  intros EK OUT BASE. apply (PMKA.base_ok_keepA RSEGS PMA.AD L ar LB FF sp scr W M M' EK PMA.addrs_wf_A); [| |exact BASE].
  - intros a D. pose proof (dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUT; lia.
  - intros a Ha. cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia| apply OUT; lia].
Qed.

(* [comment removed for export] *)
Lemma fs_above_img LB FF LK cr Aw M V : ri_inv HI LB FF LK cr Aw M V -> 6905856 <= ar_fs ar.
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & FSAPP & _ & FSIMG & _).
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG. unfold app_mem, FS_BYTES in *. lia.
Qed.
Lemma blk_img LB FF LK cr Aw M V q m : ri_inv HI LB FF LK cr Aw M V -> In (q, m) LB -> q + m <= 65536 \/ 6905856 <= q.
Proof.
  intros HH Hq. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB _ Hq) as ((_ & BI & _) & _). cbn [fst snd] in BI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BI. lia.
Qed.

(* [comment removed for export] *)
Lemma blk_obj_apart LB FF LK cr Aw M V q m o n :
  ri_inv HI LB FF LK cr Aw M V -> In (q, m) LB -> PMSPA.aobjA FF o n -> q + m <= o \/ o + n <= q.
Proof.
  intros HH Hq (f & Hf & X1 & X2).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  destruct (WB _ Hq) as (_ & _ & _ & _ & _ & _ & FSB). cbn [fst snd] in FSB.
  destruct (WF f Hf) as (Y1 & Y2 & _). destruct FSB as [Z1|Z1]; [left; lia| right; lia].
Qed.

(* [comment removed for export] *)
Lemma iss_vis LB FF LK cr Aw M model fb str sm sp scr :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PMSPA.frame_okA FF fb ->
  PM.iss_at RSEGS PMA.AD PMSPA.accA M (PMSPA.o_is PMA.AD fb) str sm -> L5CA.astk ar M sp scr ->
  let ois := PMSPA.o_is PMA.AD fb in let MV := mrestrict (ahid Aw model) M in
  (6905856 <= ois <= 140737488355056 /\ ois mod 8 = 0 /\ (2147446784 + 17592186048512 <= ois \/ ois + 272 <= 2147446784))
  /\ L5KA.zeros_at MV (ois / 8 + 2147450880) 34 /\ L5.writable RSEGS MV ois 272 /\ ois + 272 <= ahl_ceil ar
  /\ (forall a n, ois <= a -> a + n <= ois + 272 -> L5A.avis (ahid Aw model) a n)
  /\ PMSPA.aobjA FF ois 272 /\ ois + 272 <= PMSPA.o_src PMA.AD fb.
Proof.
  intros HH FOK IA ASTK ois MV. destruct FOK as ((rs & Hf) & F1024). cbn [pa_frame PMA.AD ADDR_A] in *.
  assert (AO : PMSPA.aobjA FF ois 272).
  { exists (fb, 4, rs). split; [exact Hf|]. unfold ois, PMSPA.o_is. cbn [ff_addr ff_class ff_bytes pa_off_is PMA.AD ADDR_A].
    unfold ff_bytes. cbn. lia. }
  assert (O8 : ois mod 8 = 0).
  { unfold ois, PMSPA.o_is. cbn [pa_off_is PMA.AD ADDR_A]. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
    rewrite Dm. replace (1024 * (fb / 1024) + 96) with ((128 * (fb / 1024) + 12) * 8) by lia. apply Z_mod_mult. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model ois 272 sp scr HH (PMKA.aobj_of_aobjA FF ois 272 AO O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  assert (ACC : PMSPA.accA M ois 272).
  { destruct IA as (_ & _ & C0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _). destruct IOS as (_ & _ & _ & _ & _ & _ & _ & IC & _).
    intros a Ha. destruct (Z_lt_le_dec a (ois + 120)) as [X|X]; [apply C0; lia| apply IC; lia]. }
  split; [split; [lia| split; [exact O8| exact OBIG]]|].
  split; [apply (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model ois 272 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC)|].
  split; [apply (proj2 (L5A.writable_vis _ M ois 272 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
  split; [lia|]. split; [intros a n Ha Hn; eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. split; [exact AO|].
  unfold ois, PMSPA.o_is, PMSPA.o_src, PMSPA.o_p. cbn [pa_off_is pa_off_p PMA.AD ADDR_A]. lia.
Qed.

(* [comment removed for export] *)
Lemma blk_byte_vis LB FF LK cr Aw M model q m p :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> In (q, m) LB -> L5.defined M q m -> PMSPA.accA M q m -> m mod 8 = 0 -> q <= p < q + m ->
  let MV := mrestrict (ahid Aw model) M in
  4096 <= p /\ p + 1 <= ahl_ceil ar /\ L5.defined MV p 1 /\ (2147446784 + 17592186048512 <= p \/ p + 1 <= 2147446784)
  /\ L5KA.zeros_at MV (p / 8 + 2147450880) 1
  /\ (p + 1 <= ar_fs ar \/ ar_fs ar + FS_BYTES <= p).
Proof.
  intros HH Hq D ACC M8 Hp MV.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB _ Hq) as (BR & _ & _ & _ & _ & _ & FSB). cbn [fst snd] in *.
  destruct BR as (B0 & B1 & B16 & B3 & B4 & (A0 & A1 & A2)). unfold BIGSHADOW_LO, BIGSHADOW_HI in A1.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (_ & _ & _ & _ & VBLK & _).
  assert (Q8 : q mod 8 = 0) by (apply PMKA.mod16_8'; exact B16).
  set (o := 8 * (p / 8)).
  assert (Ho : o <= p < o + 8) by (unfold o; pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia).
  assert (Hq8 : q <= o /\ o + 8 <= q + m).
  { pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.div_mod m 8 ltac:(lia)) as Dm. rewrite Q8 in Dq. rewrite M8 in Dm.
    assert (L1 : q / 8 <= p / 8) by (apply Z.div_le_mono; lia).
    assert (L2 : p / 8 < q / 8 + m / 8).
    { apply (Z.div_lt_upper_bound p 8 (q / 8 + m / 8)); lia. }
    unfold o. lia. }
  split; [lia|]. split; [lia|].
  split; [apply (proj2 (L5A.defined_vis _ M p 1 (VBLK q m p 1 Hq ltac:(lia) ltac:(lia)))); apply (L5.defined_sub M q m); [exact D| lia| lia]|].
  split; [destruct A1 as [X|X]; [right; lia| left; lia]|].
  split.
  { replace (p / 8) with (o / 8) by (unfold o; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    pose proof (PMKA.blk_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model q m o 8 HH Hq ltac:(lia) ltac:(lia)
                  ltac:(unfold o; rewrite Z.mul_comm, Z_mod_mult; reflexivity) ltac:(lia) ltac:(reflexivity)) as Z8.
    change (8 / 8) with 1 in Z8. apply Z8. intros a Ha. apply ACC. lia. }
  destruct FSB as [X|X]; [left; lia| right; lia].
Qed.

(* [comment removed for export] *)
Lemma frb_of LB FF LK cr Aw M V : ri_inv HI LB FF LK cr Aw M V -> forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47.
Proof.
  intros HH f Hf. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & _).
  destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. split; lia.
Qed.
Lemma brb_of LB FF LK cr Aw M V : ri_inv HI LB FF LK cr Aw M V -> forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47.
Proof.
  intros HH b Hb. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _ & _ & _ & _ & _ & _ & _ & (_ & _ & SPT & _) & _).
  destruct (proj1 (WB b Hb)) as (X0 & _ & _ & _ & X4 & _). split; lia.
Qed.

(* [comment removed for export] *)
Lemma aobj_fb FF fb o n : PMSPA.frame_okA FF fb -> fb + 32 <= o -> o + n <= fb + 1016 -> PMSPA.aobjA FF o n.
Proof.
  intros ((rs & Hf) & _) H1 H2. exists (fb, 4, rs). split; [exact Hf|]. unfold ff_addr, ff_class. cbn. unfold ff_bytes. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma src_piece_parser LB FF LK cr Aw M2 M3 V fb ois s de' rem' sp scr :
  ri_inv HI LB FF LK cr Aw M2 V -> PMSPA.frame_okA FF fb -> incl (PM.parser_own s) LB ->
  L5SAR.ek L ar LB FF sp scr [(PMSPA.o_src PMA.AD fb + 256, 40)] M2 M3 -> mem_grows M2 M3 ->
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M2 (PMSPA.o_p PMA.AD fb) ois s ->
  L5.u64_at RSEGS M3 (PMSPA.o_src PMA.AD fb + 264) (PM.sr_qc (PM.p_src s)) -> L5.u64_at RSEGS M3 (PMSPA.o_src PMA.AD fb + 272) PM.CHUNK ->
  L5.u64_at RSEGS M3 (PMSPA.o_src PMA.AD fb + 280) de' -> L5.u64_at RSEGS M3 (PMSPA.o_src PMA.AD fb + 288) rem' ->
  PM.sr_qc (PM.p_src s) <= de' -> 0 <= rem' -> de' + rem' <= PM.sr_qc (PM.p_src s) + PM.CHUNK ->
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M3 (PMSPA.o_p PMA.AD fb) ois (PMSPA.with_src s (PM.SRC (PM.sr_qc (PM.p_src s)) de' rem')).
Proof.
  intros HH FOK INC EK MG PA C1 C2 C3 C4 Q1 Q2 Q3.
  unfold PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_p PMA.AD ADDR_A] in *.
  pose proof FOK as ((rs & Hfb) & F1024).
  pose proof (frb_of _ _ _ _ _ _ _ HH) as FRB. pose proof (brb_of _ _ _ _ _ _ _ HH) as BRB.
  assert (AOS : PMSPA.aobjA FF (fb + 464 + 24) 296) by (apply (aobj_fb FF fb); [exact FOK| lia| lia]).
  assert (WS : PMKA.wapp [(fb + 464 + 24 + 256, 40)]).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & _).
    destruct (WF _ Hfb) as (Y1 & Y2 & _). unfold ff_addr, ff_class, ff_bytes in Y1, Y2. cbn in Y1, Y2. unfold app_mem, FS_BYTES in FSAPP, Y2.
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; destruct FSAPP as (F0 & [F1|F1] & F2); [left; lia| right; lia]| apply PMKA.wapp_nil]. }
  assert (OUTO : forall i, ~ (fb + 464 + 24 + 256 <= i < fb + 464 + 24 + 296) -> L5.outside [(fb + 464 + 24 + 256, 40)] i).
  { intros i N r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  assert (OUTB : forall q m, In (q, m) LB -> forall i, q <= i < q + m -> L5.outside [(fb + 464 + 24 + 256, 40)] i).
  { intros q m Hq i Hi. apply OUTO. destruct (blk_obj_apart _ _ _ _ _ _ _ q m _ 296 HH Hq AOS) as [X|X]; lia. }
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PTB & PVEC & _).
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB) by (apply INC; unfold PM.parser_own, PM.src_own; cbn; left; reflexivity).
  assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LB) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity).
  apply (parser_src_fieldsA M2 M3 (fb + 464) ois s de' rem' PA).
  - destruct (frb_of _ _ _ _ _ _ _ HH (fb, 4, rs) Hfb). unfold ff_addr in *. cbn in *. lia.
  - destruct (frb_of _ _ _ _ _ _ _ HH (fb, 4, rs) Hfb). unfold ff_addr, ff_class, ff_bytes in *. cbn in *. lia.
  - apply (PMKA.agA_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 464) 280 ltac:(apply (aobj_fb FF fb); [exact FOK| lia| lia])). intros i Hi. apply OUTO. lia.
  - apply (PMKA.agA_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 464 + 320) 64 ltac:(apply (aobj_fb FF fb); [exact FOK| lia| lia])). intros i Hi. apply OUTO. lia.
  - apply (PMKA.agsh_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 464 + 280) 40 ltac:(apply (aobj_fb FF fb); [exact FOK| lia| lia])).
  - destruct (BRB _ QIN). cbn [fst snd] in *. lia.
  - destruct (BRB _ QIN). cbn [fst snd] in *. lia.
  - apply (PMKA.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ QIN). apply OUTB. exact QIN.
  - destruct (BRB _ VIN). cbn [fst snd] in *. lia.
  - destruct (BRB _ VIN). cbn [fst snd] in *. lia.
  - apply (PMKA.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ VIN). apply OUTB. exact VIN.
  - intros c0 n0 p0 E.
    assert (TIN : In (p0, c0) LB) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own; rewrite E; cbn; right; right; left; reflexivity).
    apply (PMKA.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ TIN). apply OUTB. exact TIN.
  - exact MG.
  - replace (fb + 464 + 288) with (fb + 464 + 24 + 264) by lia. exact C1.
  - replace (fb + 464 + 296) with (fb + 464 + 24 + 272) by lia. exact C2.
  - replace (fb + 464 + 304) with (fb + 464 + 24 + 280) by lia. exact C3.
  - replace (fb + 464 + 312) with (fb + 464 + 24 + 288) by lia. exact C4.
  - exact Q1. - exact Q2. - exact Q3.
Qed.

(* [comment removed for export] *)
Lemma src_piece_iss LB FF LK cr Aw M2 M3 V fb str sm sp scr :
  ri_inv HI LB FF LK cr Aw M2 V -> PMSPA.frame_okA FF fb -> incl (PM.vs_own str) LB ->
  L5SAR.ek L ar LB FF sp scr [(PMSPA.o_src PMA.AD fb + 256, 40)] M2 M3 ->
  PM.iss_at RSEGS PMA.AD PMSPA.accA M2 (PMSPA.o_is PMA.AD fb) str sm -> PM.iss_at RSEGS PMA.AD PMSPA.accA M3 (PMSPA.o_is PMA.AD fb) str sm.
Proof.
  intros HH FOK INC EK IA.
  unfold PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in *. cbn [pa_off_p pa_off_is PMA.AD ADDR_A] in *.
  pose proof FOK as ((rs & Hfb) & F1024).
  pose proof (frb_of _ _ _ _ _ _ _ HH) as FRB. pose proof (brb_of _ _ _ _ _ _ _ HH) as BRB.
  assert (AOS : PMSPA.aobjA FF (fb + 464 + 24) 296) by (apply (aobj_fb FF fb); [exact FOK| lia| lia]).
  assert (WS : PMKA.wapp [(fb + 464 + 24 + 256, 40)]).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & _).
    destruct (WF _ Hfb) as (Y1 & Y2 & _). unfold ff_addr, ff_class, ff_bytes in Y1, Y2. cbn in Y1, Y2. unfold app_mem, FS_BYTES in FSAPP, Y2.
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; destruct FSAPP as (F0 & [F1|F1] & F2); [left; lia| right; lia]| apply PMKA.wapp_nil]. }
  apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp scr _ M2 M3 EK WS FRB BRB (fb + 96) str sm ltac:(apply (aobj_fb FF fb); [exact FOK| lia| lia]) INC); [| |exact IA].
  - intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
  - intros c0 n0 p0 E i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. subst str.
    assert (TIN : In (p0, c0) LB) by (apply INC; cbn; left; reflexivity).
    destruct (blk_obj_apart _ _ _ _ _ _ _ p0 c0 _ 296 HH TIN AOS) as [X|X]; lia.
Qed.

(* [comment removed for export] *)
Lemma ret_exit (fx : FPState) R M model K LB FF LK cr Aw (pc r : Z) (W : bv 32) :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model ->
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Jalr 0 1 0, 4%Z) ->
  getr R (Z_to_bv 5 (Z.of_nat 1)) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
  (forall model1, model_rt model model1 -> L5CA.amodel_ok Aw model1 -> ri_inv HI LB FF LK cr Aw M (vml_of model1) ->
     srealizes RSEGS SCFG (L5A.cfg (fx := fx) R r M model1) K) ->
  srealizes RSEGS SCFG (L5A.cfg (fx := fx) R pc M model) K.
Proof.
  intros HH AM HF HE HD Rr Hr1 Hr2 KONT.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw M model fx fx R pc R r (mrestrict (ahid Aw model) M) K HH AM
           (PMK.ret_to RSEGS fx R _ pc W r HF HE HD Rr Hr1 Hr2) (fun _ X => X) (fun _ _ => eq_refl)).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1. apply KONT; assumption.
Qed.

(* [comment removed for export] *)
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Lemma img_shz_vis LB FF LK cr Aw M model a g :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> 0x10000 <= a -> a + 8 * g <= 0x696000 -> a mod 8 = 0 -> 0 < g ->
  (a + 8 * g <= 0x231c0 \/ (0x23b80 <= a /\ a + 8 * g <= 0x13bfc0) \/ 0x13c580 <= a) ->
  L5KA.zeros_at (mrestrict (ahid Aw model) M) (a / 8 + 2147450880) g.
Proof.
  intros HH H1 H2 H8 Hg HP.
  assert (AP : Forall (fun r => a + 8 * g <= fst r \/ snd r <= a) (icl_poison IL)).
  { rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  destruct (aic_img_shadow _ _ _ _ _ ICok LB FF LK cr Aw M _ HH a (8 * g) ltac:(rewrite (L5A.aly_img_lo L C LYa); lia)
              ltac:(rewrite (L5A.aly_img_hi L C LYa); lia) ltac:(lia) AP) as (ZB & ALW).
  assert (INS : forall j, 0 <= j < g -> in_shadow_of a (8 * g) (a / 8 + 2147450880 + j)).
  { intros j Hj. assert (SJ : a / 8 + 2147450880 + j = S (a + 8 * j)).
    { unfold S, SB. replace (a + 8 * j) with (j * 8 + a) by lia. rewrite Z.div_add_l by lia. lia. }
    unfold in_shadow_of. rewrite SJ. unfold S. split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia. }
  apply (proj2 (L5A.zeros_at_vis _ M _ g (L5A.avis_of_shadow_allowed Aw model a (8 * g) _ g ALW INS))).
  intros j Hj. pose proof (ZB _ (INS j Hj)) as B. unfold byte_at in B. exact B.
Qed.

(* [comment removed for export] *)
Lemma blk_apart LB FF LK cr Aw M V B1 m1 B2 m2 :
  ri_inv HI LB FF LK cr Aw M V -> In (B1, m1) LB -> In (B2, m2) LB -> B1 <> B2 -> B1 + m1 <= B2 \/ B2 + m2 <= B1.
Proof.
  intros HH H1 H2 NE. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB _ H1) as (_ & _ & _ & _ & AP & _). cbn [fst snd] in AP.
  apply (L5C.blocks_apart_in B1 m1 (lb_remove B1 LB) B2 m2 AP). apply L5C.in_lb_remove_neq; [exact H2| intros E; apply NE; symmetry; exact E].
Qed.
Lemma lb_nodup LB FF LK cr Aw M V : ri_inv HI LB FF LK cr Aw M V -> NoDup (map fst LB).
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). exact ND.
Qed.

End WithHeap.
End PMASK.
