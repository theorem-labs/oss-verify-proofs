(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs PmStep PmKeep.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMFR.

Lemma outside_of_not_inW W a : ~ PMK.inW W a -> L5.outside W a.
Proof. intros N r Hin Hr. apply N. exists r. split; assumption. Qed.
Lemma inW_nil a : ~ PMK.inW [] a.
Proof. intros (r & [] & _). Qed.
Lemma inW_inv1 b n a : PMK.inW [(b, n)] a -> b <= a < b + n.
Proof. intros (r & [<-|[]] & Hr). exact Hr. Qed.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.

(* [comment removed for export] *)
Definition brange (LBc : list (Z * Z)) : Prop :=
  forall B m, In (B, m) LBc -> 4096 <= B /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\ B + m <= hl_ceil L.
Lemma brange_of_heap (HIok : heap_iface_ok L SCFG HI) LBf LBc cr M VM : hi_heap HI LBf cr M VM -> incl LBc LBf -> brange LBc.
Proof.
  intros HH INC B m Hin. pose proof (proj1 (hio_wf L SCFG HI HIok LBf cr M VM HH) (B, m) (INC _ Hin)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _).
  cbn [fst snd] in *. split; [exact Q0|]. split; [exact Q1| exact Q4].
Qed.
Lemma brange_incl LB1 LB2 : brange LB2 -> incl LB1 LB2 -> brange LB1.
Proof. intros BR INC B m Hin. apply BR. apply INC. exact Hin. Qed.

Section Along.
Variables (LBc : list (Z * Z)) (sp' scr' : Z) (W' : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LBc sp' scr' W' M M'.
Hypothesis STKc : L5C.stk (hl_sptop L) M sp' scr'.
Hypothesis SCR0 : 0 <= scr'.
Hypothesis BR : brange LBc.
Hypothesis WHI : forall a, PMK.inW W' a -> sp' <= a \/ hl_img_lo L <= a < hl_img_hi L.

Lemma ag_hi a n : sp' <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW W' i) -> L5C.agree_on M M' a n.
Proof.
  intros H1 H2 N. apply (PMKP.ek_agree_stack segs L KL LBc sp' scr' W' M M' a n E STKc SCR0 H1 H2). intros i Hi. apply outside_of_not_inW. apply N. exact Hi.
Qed.
Lemma ag_block B m : In (B, m) LBc -> L5C.agree_on M M' B m.
Proof.
  intros Hin. destruct (BR B m Hin) as (Q0 & Q1 & Q4).
  pose proof STKc as (_ & SLO & SHI & STOP & _).
  apply (PMKP.ek_agree L LBc sp' scr' W' M M' B m E). intros i Hi.
  apply (PMKP.kept_block segs L KL LBc sp' scr' W' B m i Hin Hi); [lia| exact Q4| exact Q1| lia|].
  apply outside_of_not_inW. intros I. destruct (WHI i I) as [X|X]; lia.
Qed.

Lemma u64_keep a v : sp' <= a -> a + 8 <= 2 ^ 64 -> (forall i, a <= i < a + 8 -> ~ PMK.inW W' i) -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof. intros H1 H2 N. pose proof STKc as (_ & SLO & _ & STOP & _). apply (L5C.u64_at_agree segs M M'); [apply ag_hi; assumption|lia|lia]. Qed.
Lemma u32_keep a v : sp' <= a -> a + 4 <= 2 ^ 64 -> (forall i, a <= i < a + 4 -> ~ PMK.inW W' i) -> L5.u32_at segs M a v -> L5.u32_at segs M' a v.
Proof. intros H1 H2 N. pose proof STKc as (_ & SLO & _ & STOP & _). apply (PMF.u32_at_agree segs M M'); [apply ag_hi; assumption|lia|lia]. Qed.
Lemma u8_keep a v : sp' <= a -> a + 1 <= 2 ^ 64 -> (forall i, a <= i < a + 1 -> ~ PMK.inW W' i) -> L5.u8_at segs M a v -> L5.u8_at segs M' a v.
Proof. intros H1 H2 N. pose proof STKc as (_ & SLO & _ & STOP & _). apply (L5C.u8_at_agree segs M M'); [apply ag_hi; assumption|lia|lia]. Qed.
Lemma defined_keep a n : sp' <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW W' i) -> L5.defined M a n -> L5.defined M' a n.
Proof. intros H1 H2 N. apply (L5C.defined_agree M M' a n). apply ag_hi; assumption. Qed.

Lemma vstr_keep o s : sp' <= o -> o + 24 <= 2 ^ 64 -> (forall i, o <= i < o + 24 -> ~ PMK.inW W' i) -> incl (PM.vs_own s) LBc ->
  PM.vstr_at segs T3 M o s -> PM.vstr_at segs T3 M' o s.
Proof.
  intros H1 H2 N INC VS. pose proof STKc as (_ & SLO & _ & STOP & _).
  apply (PMF.vstr_at_agree segs M M' o s); [lia|lia| apply ag_hi; assumption| |exact VS].
  intros c n p ->. apply ag_block. apply INC. cbn. auto.
Qed.
Lemma iss_keep ois str sm : sp' <= ois -> ois + 272 <= 2 ^ 64 -> (forall i, ois <= i < ois + 272 -> ~ PMK.inW W' i) -> incl (PM.vs_own str) LBc ->
  PM.iss_at segs A T3 M ois str sm -> PM.iss_at segs A T3 M' ois str sm.
Proof.
  intros H1 H2 N INC VS. pose proof STKc as (_ & SLO & _ & STOP & _).
  apply (PMF.iss_at_agree segs A M M' ois str sm); [lia|lia| apply ag_hi; assumption| |exact VS].
  intros c n p ->. apply ag_block. apply INC. cbn. auto.
Qed.
Lemma parser_keep op ois s : sp' <= op -> op + 384 <= 2 ^ 64 -> (forall i, op <= i < op + 384 -> ~ PMK.inW W' i) -> incl (PM.parser_own s) LBc ->
  PM.parser_at segs A T3 T4 M op ois s -> PM.parser_at segs A T3 T4 M' op ois s.
Proof.
  intros H1 H2 N INC PA. pose proof STKc as (_ & SLO & SHI & STOP & _).
  assert (Bq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc) by (apply INC; unfold PM.parser_own, PM.src_own; cbn; auto).
  assert (Bv : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LBc) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; auto).
  destruct (BR _ _ Bq) as (Q0 & Q1 & Q4). destruct (BR _ _ Bv) as (V0 & V1 & V4).
  apply (PMF.parser_at_agree segs A M M' op ois s); [lia|lia| apply ag_hi; assumption|lia|lia| apply ag_block; exact Bq|lia|lia| apply ag_block; exact Bv| |exact PA].
  intros c n p Et. apply ag_block. apply INC. unfold PM.parser_own. apply in_or_app. right. apply in_or_app. right. rewrite Et. cbn. auto.
Qed.
Lemma nullis_keep o : sp' <= o -> o + 232 <= 2 ^ 64 -> (forall i, o <= i < o + 232 -> ~ PMK.inW W' i) ->
  PM.nullis_at segs A T3 M o -> PM.nullis_at segs A T3 M' o.
Proof. intros H1 H2 N. pose proof STKc as (_ & SLO & _ & STOP & _). apply (PMF.nullis_at_agree segs A M M' o); [lia|lia| apply ag_hi; assumption]. Qed.
Lemma src_keep os isp sbp src : sp' <= os -> os + 296 <= 2 ^ 64 -> (forall i, os + 240 <= i < os + 296 -> ~ PMK.inW W' i) -> In (PM.sr_qc src, PM.CHUNK) LBc ->
  PM.src_fields_at segs T3 M os isp sbp src -> PM.src_fields_at segs T3 M' os isp sbp src.
Proof.
  intros H1 H2 N Bq. pose proof STKc as (_ & SLO & SHI & STOP & _). destruct (BR _ _ Bq) as (Q0 & Q1 & Q4).
  apply (PMF.src_fields_at_agree segs M M' os isp sbp src); [lia|lia|lia|lia| apply ag_hi; [lia|lia|intros i Hi; apply N; lia]| apply ag_block; exact Bq].
Qed.
Lemma ec_keep o v c : sp' <= o -> o + 16 <= 2 ^ 64 -> (forall i, o <= i < o + 16 -> ~ PMK.inW W' i) -> PMSP.ec_at segs M o v c -> PMSP.ec_at segs M' o v c.
Proof.
  intros H1 H2 N (E0 & E8 & ED). split; [|split].
  - apply u32_keep; [lia|lia| intros i Hi; apply N; lia| exact E0].
  - apply u64_keep; [lia|lia| intros i Hi; apply N; lia| exact E8].
  - apply defined_keep; [lia|lia| exact N| exact ED].
Qed.
Lemma visitor_keep o : sp' <= o -> o + 8 <= 2 ^ 64 -> (forall i, o <= i < o + 8 -> ~ PMK.inW W' i) -> PMSP.visitor_at segs A M o -> PMSP.visitor_at segs A M' o.
Proof. unfold PMSP.visitor_at. apply u64_keep. Qed.
End Along.

(* [comment removed for export] *)
Lemma ek_of_piece LB sp scr M M1 (P : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> L5C.stk (hl_sptop L) M sp scr ->
  (forall b, In b LB -> fst b + snd b <= hl_ceil L) -> (forall a, P a -> sp - scr <= a < sp) -> PMK.ek L LB sp scr [] M M1.
Proof. intros FRZ STK LBhi PF. apply (PMK.ek_piece_in segs L KL LB sp scr [] M M1 P FRZ STK LBhi). intros a Pa. left. apply PF. exact Pa. Qed.
Lemma brange_hi LB : brange LB -> forall b, In b LB -> fst b + snd b <= hl_ceil L.
Proof. intros BR (B & m) Hin. destruct (BR B m Hin) as (_ & _ & Q). exact Q. Qed.

(* [comment removed for export] *)
Lemma iosb_revptr (M M' : word -> option byte) o vp vp' rdb st :
  0 <= o -> o + 152 <= 2 ^ 64 -> L5C.agree_on M M' (o + 8) 144 -> L5.u64_at segs M' o vp' -> L5.defined M' o 152 ->
  PM.iosb_at segs A T3 M o vp rdb st -> PM.iosb_at segs A T3 M' o vp' rdb st.
Proof.
  intros Ho Ho' AG V D' (H0 & H32 & H36 & H40 & H48 & Z & D & _ & ST).
  assert (S : forall a' n', o + 8 <= a' -> a' + n' <= o + 152 -> L5C.agree_on M M' a' n') by (intros a' n' X Y; apply (L5C.agree_on_sub M M' (o + 8) 144 a' n' AG); lia).
  split; [exact V|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply S; lia|lia|lia|exact H32]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply S; lia|lia|lia|exact H36]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply S; lia|lia|lia|exact H40]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply S; lia|lia|lia|exact H48]|].
  split; [apply (PMF.zeros_at_agree M M'); [apply S; lia|exact Z]|].
  split; [exact D'|]. split; [exact I| exact ST].
Qed.
(* [comment removed for export] *)
Lemma model_ok_but_vm model model' : PMSP.model_ok model -> model_but_vm model model' -> PMSP.model_ok model'.
Proof.
  intros (H1 & H2 & H3) MB. unfold PMSP.model_ok. rewrite (L5C.halted_but_vm _ _ MB), (L5C.lazy_but_vm _ _ MB), (L5C.materialized_but_vm _ _ MB). auto.
Qed.

End Kit.
End PMFR.
