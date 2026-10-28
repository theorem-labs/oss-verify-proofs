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

Module PMASR1.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Lemma parser_src_tbA (M M' : word -> option byte) op ois s de' rem' :
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  PMFA.agA M M' op 280 -> PMFA.agA M M' (op + 320) 17 -> PMFA.agA M M' (op + 360) 24 -> PMFA.agsh M M' (op + 280) 104 ->
  L5.defined M' op 384 ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> PMFA.agA M M' (op + 336) 24 /\ L5.defined M' p c /\ PMFA.agsh M M' p c) ->
  L5.defined M' (PM.sr_qc (PM.p_src s)) PM.CHUNK -> PMFA.agsh M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> PMFA.agA M M' (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  L5.u64_at RSEGS M' (op + 288) (PM.sr_qc (PM.p_src s)) -> L5.u64_at RSEGS M' (op + 296) PM.CHUNK ->
  L5.u64_at RSEGS M' (op + 304) de' -> L5.u64_at RSEGS M' (op + 312) rem' ->
  PM.sr_qc (PM.p_src s) <= de' -> 0 <= rem' -> de' + rem' <= PM.sr_qc (PM.p_src s) + PM.CHUNK ->
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M' op ois (PMSPA.with_src s (PM.SRC (PM.sr_qc (PM.p_src s)) de' rem')).
Proof.
  intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
         [AG1 SH1] [AG2 SH2] [AG3 SH3] SH4 DEF TBL DCQ SHQ Hb Hb' AGB C1 C2 C3 C4 Q1 Q2 Q3.
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & CC & C240).
  unfold PMSPA.with_src, PM.parser_at, PM.src_fields_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.sr_qc PM.sr_de PM.sr_rem] in *.
  assert (U64 : forall a v, op <= a -> a + 8 <= op + 280 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
  assert (U32 : forall a v, op <= a -> a + 4 <= op + 280 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
  assert (U8 : forall a v, op <= a -> a + 1 <= op + 280 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
  split; [apply U64; [lia|lia|exact H0]|].
  split; [exact DEF|].
  split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH1; lia| exact C24]|].
  split; [apply U8; [lia|lia|exact H8]|]. split; [apply U8; [lia|lia|exact H9]|]. split; [apply U32; [lia|lia|exact H12]|].
  split; [apply U8; [lia|lia|exact H16]|]. split; [apply U32; [lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS PMA.AD M M' (op + 32)); [lia|lia| split; [intros i Hi; apply AG1; lia| intros x Hx; apply SH1; lia]| exact NI]|].
  split.
  { split; [apply U64; [lia|lia|exact F1]|]. split; [apply U64; [lia|lia|exact F2]|].
    split; [intros i Hi; replace (op + 24 + 256 + i) with (op + (280 + i)) by lia; apply DEF; lia|].
    split; [replace (op + 24 + 264) with (op + 288) by lia; exact C1|]. split; [replace (op + 24 + 272) with (op + 296) by lia; exact C2|].
    split; [replace (op + 24 + 280) with (op + 304) by lia; exact C3|]. split; [replace (op + 24 + 288) with (op + 312) by lia; exact C4|].
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact G4|].
    split; [exact DCQ|].
    split; [apply (PMFA.accA_agree M M' _ _ SHQ CC)|].
    apply (PMFA.accA_agree M M' (op + 24 + 240) 56); [intros x Hx; destruct (Z_lt_le_dec x (op + 280)) as [X|X]; [apply SH1; lia| apply SH4; lia]| exact C240]. }
  split; [apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact H320]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact H328]|].
  split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; destruct (Z_lt_le_dec x (op + 337)) as [X|X]; [apply SH2; lia| apply SH4; lia]| exact C320]|].
  split.
  { destruct TB as (TD & TC & TH). split; [intros i Hi; replace (op + 336 + i) with (op + (336 + i)) by lia; apply DEF; lia|].
    split; [apply (PMFA.accA_agree M M' (op + 336) 24); [intros x Hx; apply SH4; lia| exact TC]|].
    destruct (PM.p_tb s) as [n|c n p] eqn:ET.
    - destruct TH as (Hn & B0). split; [exact Hn|]. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact B0].
    - destruct TH as (W0 & W8 & W16 & Hn & Hc & He & DB & CB). destruct (TBL c n p eq_refl) as ([AGT _] & DT & SHT).
      split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AGT; lia| lia| lia| exact W0]|].
      split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AGT; lia| lia| lia| exact W8]|].
      split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AGT; lia| lia| lia| exact W16]|].
      split; [exact Hn|]. split; [exact Hc|]. split; [exact He|]. split; [exact DT|].
      apply (PMFA.accA_agree M M' p c SHT CB). }
  split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|lia|lia| intros i Hi; apply AG3; lia| exact AGB| exact VEC]|].
  split; [exact B1|]. split; [exact B2|]. exact B3.
Qed.

(* [comment removed for export] *)
Lemma aobjA_client {BS ST} L ar LB FF sp scr o n a : PMSPA.aobjA FF o n -> o <= a < o + n -> aclient_g BS ST L ar LB FF sp scr a.
Proof.
  intros (f & Hf & X1 & X2) Ha. unfold aclient_g. do 3 right. left. exists f. split; [exact Hf|]. split; [lia| intros X; lia].
Qed.

Lemma in_fframe_of_aobjA FF o n a : PMSPA.aobjA FF o n -> o <= a < o + n -> in_fframe FF a.
Proof. intros (f & Hf & X1 & X2) Ha. exists f. split; [exact Hf|]. split; [lia| intros X; lia]. Qed.
Lemma in_block_of L0 q m a : In (q, m) L0 -> q <= a < q + m -> in_block L0 a.
Proof. intros Hq Ha. exists (q, m). split; [exact Hq| cbn [fst snd]; exact Ha]. Qed.
(* [comment removed for export] *)
Lemma cl_of_bf {BS ST} L ar LB FF sp scr a : in_block LB a \/ in_fframe FF a -> aclient_g BS ST L ar LB FF sp scr a.
Proof. intros [X|X]; unfold aclient_g; [left; exact X| do 3 right; left; exact X]. Qed.

Lemma sub_in (KS ks : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) ks = true -> forall k, In k ks -> In k KS.
Proof. intros H k Hk. apply L5K.In_of_mem. rewrite forallb_forall in H. apply H. exact Hk. Qed.

Lemma defined_app (M : word -> option byte) a n1 n2 : 0 <= n1 -> L5.defined M a n1 -> L5.defined M (a + n1) n2 -> L5.defined M a (n1 + n2).
Proof.
  intros H0 D1 D2 i Hi. destruct (Z_lt_le_dec i n1) as [X|X]; [apply D1; lia|].
  replace (a + i) with (a + n1 + (i - n1)) by lia. apply D2. lia.
Qed.

(* [comment removed for export] *)
Section VisK.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Lemma vis_scan LB FF LK cr A M model p n :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  (n = 0 \/ (ar_fs ar <= p /\ p + n <= ar_fs ar + FS_BYTES) \/ (exists q m, In (q, m) LB /\ q <= p /\ p + n <= q + m)) ->
  forall a, p <= a < p + n -> ahid A model (Z_to_bv 64 a) = false /\ ahid A model (Z_to_bv 64 (S a)) = false.
Proof.
  intros HH LOC a Ha.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr A M model HH) as VP. cbv zeta in VP.
  destruct VP as (_ & _ & _ & VFS & VB & VBS & VFSS & _).
  destruct LOC as [E|[(X1 & X2)|(q & m & Hq & X1 & X2)]].
  - exfalso. lia.
  - split.
    + pose proof (VFS a 1 ltac:(lia) ltac:(lia) 0 ltac:(lia)) as V. rewrite Z.add_0_r in V. exact V.
    + assert (IS : forall i, 0 <= i < 1 -> in_shadow_of (ar_fs ar) FS_BYTES (S a + i)).
      { intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r. unfold in_shadow_of. split; apply PMKA.S_mono; lia. }
      pose proof (VFSS (S a) 1 IS 0 ltac:(lia)) as V. rewrite Z.add_0_r in V. exact V.
  - split.
    + pose proof (VB q m a 1 Hq ltac:(lia) ltac:(lia) 0 ltac:(lia)) as V. rewrite Z.add_0_r in V. exact V.
    + assert (IS : forall i, 0 <= i < 1 -> in_shadow_of q m (S a + i)).
      { intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r. unfold in_shadow_of. split; apply PMKA.S_mono; lia. }
      pose proof (VBS q m (S a) 1 Hq IS 0 ltac:(lia)) as V. rewrite Z.add_0_r in V. exact V.
Qed.
End VisK.

End PMASR1.
