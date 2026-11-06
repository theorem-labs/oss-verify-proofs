(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmSpecs PmStep PmKeep PmFrame PmParKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECF.

Lemma slice_length_le p i n : 0 <= n -> Z.of_nat (length (UbjRef.slice p i n)) <= n.
Proof. intros Hn. unfold UbjRef.slice. rewrite length_firstn. pose proof (Nat.le_min_l (Z.to_nat n) (length (skipn (Z.to_nat i) p))). lia. Qed.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable E : pe_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation enc_at := (PEC.enc_at segs E L T3 T4).
Abbreviation sink_at := (PESK.sink_at segs L T3 T4).
Abbreviation content_ok := (PEC.content_ok segs A).
Abbreviation ec_state := (PEC.ec_state segs A).
Abbreviation iss_at := (PM.iss_at segs A T3).
Abbreviation parser_at := (PM.parser_at segs A T3 T4).

Section Agree.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').

Lemma eitem_at_agree a e : ag a 24 -> 0 <= a -> a + 24 <= 2 ^ 64 -> PEC.eitem_at segs M a e -> PEC.eitem_at segs M' a e.
Proof.
  intros AG Ha Ha' (K0 & K8 & K16). split; [|split].
  - apply (PMF.u32_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia] |lia|lia| exact K0].
  - apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia] |lia|lia| exact K8].
  - apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia] |lia|lia| exact K16].
Qed.

Lemma enc_at_agree ov fb en :
  0 <= ov -> ov + 56 <= 2 ^ 64 -> ag ov 56 ->
  (0 < PEC.en_k en -> 0 <= PEC.en_b en /\ PEC.en_b en + PEC.ESZ * PEC.ecap (PEC.en_k en) <= 2 ^ 64 /\ ag (PEC.en_b en) (PEC.ESZ * PEC.ecap (PEC.en_k en))) ->
  enc_at M ov fb en -> enc_at M' ov fb en.
Proof.
  intros Ho Ho' AG AGB (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & _ & Hk & Hlen & Hd & Hk0 & HB & HI0).
  pose proof (PEC.ecap_nonneg (PEC.en_k en)) as CN.
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 56 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG|lia|lia]).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V32]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V40]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V48]|].
  split; [apply (L5C.defined_agree M M' ov 56 AG D)|]. split; [exact I|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hd|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & _ & _). destruct (AGB Hp) as (B0 & B1 & AB).
    split; [exact AL|]. split; [exact (L5C.defined_agree M M' _ _ AB DB)|]. split; [exact BR|]. split; exact I.
  - intros i Hi. pose proof (HI0 i Hi) as IT.
    assert (Hp : 0 < PEC.en_k en).
    { destruct (Z.eq_dec (PEC.en_k en) 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (AGB Hp) as (B0 & B1 & AB).
    assert (LE : Z.of_nat (length (PEC.en_stk en)) <= PEC.ecap (PEC.en_k en)) by exact Hlen.
    apply eitem_at_agree; [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact IT].
    eapply L5C.agree_on_sub; [exact AB| unfold PEC.ESZ; lia| unfold PEC.ESZ in *; lia].
Qed.

Lemma sink_at_agree P o k :
  0 <= o -> o + 24 <= 2 ^ 64 -> ag o 24 ->
  (0 < PESK.sk_c k -> 0 <= PESK.sk_b k /\ PESK.sk_b k + PESK.sk_c k <= 2 ^ 64 /\ ag (PESK.sk_b k) (PESK.sk_c k)) ->
  sink_at P M o k -> sink_at P M' o k.
Proof.
  intros Ho Ho' AG AGB (V0 & V8 & V16 & D & _ & Hz & Hc & Hc0 & HB).
  assert (SUB : forall a n, o <= a -> a + n <= o + 24 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG|lia|lia]).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.defined_agree M M' o 24 AG D)|]. split; [exact I|].
  split; [exact Hz|]. split; [exact Hc|]. split; [exact Hc0|].
  intros Hp. destruct (HB Hp) as (DB & _ & _ & BR & CAP). destruct (AGB Hp) as (B0 & B1 & AB).
  split; [exact (L5C.defined_agree M M' _ _ AB DB)|]. split; [exact I|]. split; [exact I|]. split; [exact BR| exact CAP].
Qed.

Lemma ec_state_agree fb e cat :
  0 <= PMSP.o_ec A fb -> PMSP.o_ec A fb + 16 <= 2 ^ 64 -> ag (PMSP.o_ec A fb) 16 -> ec_state M fb e cat -> ec_state M' fb e cat.
Proof.
  intros Ho Ho' AG.
  assert (EC : forall v c, PMSP.ec_at segs M (PMSP.o_ec A fb) v c -> PMSP.ec_at segs M' (PMSP.o_ec A fb) v c).
  { intros v c (E0 & E8 & ED). split; [|split].
    - apply (PMF.u32_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia] |lia|lia| exact E0].
    - apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia] |lia|lia| exact E8].
    - exact (L5C.defined_agree M M' _ _ AG ED). }
  unfold PEC.ec_state. destruct e.
  - intros (v & Hv & EC0). exists v. split; [exact Hv| apply EC; exact EC0].
  - apply EC.
Qed.

Lemma content_ok_agree fb p src str sm :
  0 <= PMSP.o_is A fb -> PMSP.o_is A fb + 272 <= 2 ^ 64 -> ag (PMSP.o_is A fb + 80) 24 ->
  (forall c n q, str = PM.VLong c n q -> 0 <= q /\ q + c <= 2 ^ 64 /\ n < c /\ ag q c) ->
  0 <= PM.sr_qc src -> PM.sr_qc src + PM.CHUNK <= 2 ^ 64 -> PM.sr_qc src <= PM.sr_de src -> 0 <= PM.sr_rem src ->
  PM.sr_de src + PM.sr_rem src <= PM.sr_qc src + PM.CHUNK -> ag (PM.sr_qc src) PM.CHUNK ->
  (forall n, str = PM.VShort n -> n <= 22) ->
  content_ok M fb p src str sm -> content_ok M' fb p src str sm.
Proof.
  intros Ho Ho' AGS AGL Q0 Q1 Q2 Q3 Q4 AGQ SH (SZ & BS & POS & BC & ST2).
  split; [exact SZ|]. split; [|split; [exact POS| split; [| exact ST2]]].
  - assert (LEN : Z.of_nat (length p) = PM.vs_size str) by (unfold blen in SZ; lia).
    destruct str as [n|c n q].
    + cbn [PM.vs_data] in BS |- *. cbn [PM.vs_size] in LEN. pose proof (SH n eq_refl) as Hn.
      apply (L5C.bytes_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AGS|lia|lia] |lia|lia| exact BS].
    + cbn [PM.vs_data] in BS |- *. cbn [PM.vs_size] in LEN. destruct (AGL c n q eq_refl) as (B0 & B1 & Hnc & AB).
      apply (L5C.bytes_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AB|lia|lia] |lia|lia| exact BS].
  - pose proof (slice_length_le p (PEC.pos_of p src sm) (PM.sr_rem src) Q3) as SL.
    apply (L5C.bytes_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AGQ|lia|lia] |lia|lia| exact BC].
Qed.

Lemma content_ok_step fb p src str sm src' sm' :
  0 <= PMSP.o_is A fb -> PMSP.o_is A fb + 272 <= 2 ^ 64 -> ag (PMSP.o_is A fb + 80) 24 ->
  (forall c n q, str = PM.VLong c n q -> 0 <= q /\ q + c <= 2 ^ 64 /\ n < c /\ ag q c) -> (forall n, str = PM.VShort n -> n <= 22) ->
  0 <= PEC.pos_of p src' sm' ->
  L5.bytes_at segs M' (PM.sr_de src') (UbjRef.slice p (PEC.pos_of p src' sm') (PM.sr_rem src')) ->
  (PM.sm_st sm' = 2 -> PM.sm_g sm' = PM.sm_eg sm') ->
  content_ok M fb p src str sm -> content_ok M' fb p src' str sm'.
Proof.
  intros Ho Ho' AGS AGL SH POS BC ST2 (SZ & BS & _ & _ & _).
  split; [exact SZ|]. split; [|split; [exact POS| split; [exact BC| exact ST2]]].
  assert (LEN : Z.of_nat (length p) = PM.vs_size str) by (unfold blen in SZ; lia).
  destruct str as [n|c n q].
  - cbn [PM.vs_data] in BS |- *. cbn [PM.vs_size] in LEN. pose proof (SH n eq_refl) as Hn.
    apply (L5C.bytes_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AGS|lia|lia] |lia|lia| exact BS].
  - cbn [PM.vs_data] in BS |- *. cbn [PM.vs_size] in LEN. destruct (AGL c n q eq_refl) as (B0 & B1 & Hnc & AB).
    apply (L5C.bytes_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AB|lia|lia] |lia|lia| exact BS].
Qed.
End Agree.

Section Along.
Variables (LBc : list (Z * Z)) (sp' scr' : Z) (W' : list L5.range) (M M' : word -> option byte).
Hypothesis EK : PMK.ek L LBc sp' scr' W' M M'.
Hypothesis STKc : L5C.stk (hl_sptop L) M sp' scr'.
Hypothesis SCR0 : 0 <= scr'.
Hypothesis BR : PMFR.brange L LBc.
Hypothesis WHI : forall a, PMK.inW W' a -> sp' <= a \/ hl_img_lo L <= a < hl_img_hi L.

Let ag_hi := PMFR.ag_hi segs L KL LBc sp' scr' W' M M' EK STKc SCR0.
Let ag_block := PMFR.ag_block segs L KL LBc sp' scr' W' M M' EK STKc SCR0 BR WHI.

Lemma enc_keep ov fb en :
  sp' <= ov -> ov + 56 <= 2 ^ 64 -> (forall i, ov <= i < ov + 56 -> ~ PMK.inW W' i) -> incl (PEC.enc_own en) LBc ->
  enc_at M ov fb en -> enc_at M' ov fb en.
Proof.
  intros H1 H2 N INC EN. pose proof STKc as (_ & SLO & _ & STOP & _). pose proof EN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB & _).
  apply (enc_at_agree M M' ov fb en); [lia|lia| apply ag_hi; assumption| |exact EN].
  intros Hp. destruct (HB Hp) as (_ & _ & BRK & _ & _).
  assert (IN : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) LBc).
  { apply INC. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  destruct (BR _ _ IN) as (B0 & B1 & B4). pose proof (PMFR.brange_hi L LBc BR _ IN) as BH. cbn [fst snd] in BH.
  split; [lia|]. split; [unfold hl_ceil in BH; lia|]. apply ag_block. exact IN.
Qed.

Lemma sink_keep P o k :
  sp' <= o -> o + 24 <= 2 ^ 64 -> (forall i, o <= i < o + 24 -> ~ PMK.inW W' i) -> incl (PESK.sink_own k) LBc ->
  sink_at P M o k -> sink_at P M' o k.
Proof.
  intros H1 H2 N INC SK. pose proof STKc as (_ & SLO & _ & STOP & _).
  apply (sink_at_agree M M' P o k); [lia|lia| apply ag_hi; assumption| |exact SK].
  intros Hp.
  assert (IN : In (PESK.sk_b k, PESK.sk_c k) LBc).
  { apply INC. unfold PESK.sink_own. replace (PESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  destruct (BR _ _ IN) as (B0 & B1 & B4). pose proof (PMFR.brange_hi L LBc BR _ IN) as BH. cbn [fst snd] in BH.
  split; [lia|]. split; [unfold hl_ceil in BH; lia|]. apply ag_block. exact IN.
Qed.

Lemma ec_state_keep fb e cat :
  sp' <= PMSP.o_ec A fb -> PMSP.o_ec A fb + 16 <= 2 ^ 64 -> (forall i, PMSP.o_ec A fb <= i < PMSP.o_ec A fb + 16 -> ~ PMK.inW W' i) ->
  ec_state M fb e cat -> ec_state M' fb e cat.
Proof.
  intros H1 H2 N. pose proof STKc as (_ & SLO & _ & STOP & _). apply (ec_state_agree M M' fb e cat); [lia|lia| apply ag_hi; assumption].
Qed.

Lemma content_keep fb p s str sm op :
  sp' <= PMSP.o_is A fb -> PMSP.o_is A fb + 272 <= 2 ^ 64 -> (forall i, PMSP.o_is A fb + 80 <= i < PMSP.o_is A fb + 104 -> ~ PMK.inW W' i) ->
  incl (PM.vs_own str) LBc -> incl (PM.parser_own s) LBc ->
  iss_at M (PMSP.o_is A fb) str sm -> parser_at M op (PMSP.o_is A fb) s ->
  content_ok M fb p (PM.p_src s) str sm -> content_ok M' fb p (PM.p_src s) str sm.
Proof.
  intros H1 H2 N INCS INCP IA PA. pose proof STKc as (_ & SLO & _ & STOP & _).
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). pose proof VS as (_ & _ & VSF).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc) by (apply INCP; unfold PM.parser_own, PM.src_own; cbn; left; reflexivity).
  destruct (BR _ _ QIN) as (Q0 & Q1 & Q4). pose proof (PMFR.brange_hi L LBc BR _ QIN) as QH. cbn [fst snd] in QH. unfold hl_ceil in QH.
  apply (content_ok_agree M M' fb p (PM.p_src s) str sm); try lia.
  - apply ag_hi; [lia|lia|]. intros i Hi. apply N. lia.
  - intros c n q ->. cbn in VSF. destruct VSF as (_ & _ & _ & Hn & Hc & _ & _ & _).
    assert (IN : In (q, c) LBc) by (apply INCS; cbn; left; reflexivity).
    destruct (BR _ _ IN) as (B0 & B1 & B4). pose proof (PMFR.brange_hi L LBc BR _ IN) as BH. cbn [fst snd] in BH. unfold hl_ceil in BH.
    split; [lia|]. split; [lia|]. split; [lia|]. apply ag_block. exact IN.
  - apply ag_block. exact QIN.
  - intros n ->. cbn in VSF. lia.
Qed.
End Along.

Section Upd.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').
Abbreviation dkr := (PMPK.dkr M M').
Local Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].

Lemma parser_depth_upd op ois s d' :
  parser_at M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  ag op 12 -> ag (op + 16) 368 -> dkr (op + 12) 4 ->
  L5.u32_at segs M' (op + 12) d' -> 0 <= d' <= PM.MAX_DEPTH + 1 ->
  dkr (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> ag (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> dkr p c) ->
  parser_at M' op ois
    (PM.PST (PM.p_more s) (PM.p_done s) d' (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s)).
Proof.
  intros PA Ho Ho' AG1 AG2 DK12 C12 Hd DKC Hb Hb' AGV AGT.
  pose proof PA as (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3).
  pose proof SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
  cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG4 : forall a n, op + 16 <= a -> a + n <= op + 384 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG2|lia|lia]).
  split; [u64x AG1 H0|].
  split. { intros i Hi. destruct (Z_lt_le_dec i 12) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 16) as [Y|Y]; [apply DK12; [lia| apply D; lia]|]. rewrite AG2 by lia. apply D. lia. }
  split; [exact I|].
  split; [apply (L5C.u8_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG1|lia|lia]|lia|lia|exact H8]|].
  split; [apply (L5C.u8_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG1|lia|lia]|lia|lia|exact H9]|].
  split; [exact C12|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H20]|].
  split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| apply AG4; lia| exact NI]. }
  split.
  { split; [u64x AG2 F1|]. split; [u64x AG2 F2|].
    split. { apply (L5C.defined_agree M M'); [apply AG4; lia| exact F3]. }
    split; [u64x AG2 F4|]. split; [u64x AG2 F5|]. split; [u64x AG2 F6|]. split; [u64x AG2 F7|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [apply (PMPK.defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H320]|]. split; [u64x AG2 H328|]. split; [exact I|].
  split. { apply (PMPK.vstr_at_keep segs M M'); [lia| lia| apply AG4; lia| exact AGT| exact TB]. }
  split. { apply (PMF.vec_at_agree segs M M' (op + 360) (PM.p_b s) (PM.p_k s) (PM.p_stk s)); [lia|lia|exact Hb|exact Hb'| apply AG4; lia| exact AGV| exact VEC]. }
  split; [exact B1|]. split; [exact B2| exact Hd].
Qed.

Lemma parser_morepop_upd op ois s :
  parser_at M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 -> (1 <= length (PM.p_stk s))%nat ->
  ag op 8 -> ag (op + 9) 359 -> ag (op + 376) 8 -> dkr (op + 8) 1 -> dkr (op + 368) 8 ->
  L5.u8_at segs M' (op + 8) 1 ->
  L5.u64_at segs M' (op + 368) (PM.p_b s + 32 * Z.of_nat (length (PM.p_stk s)) - 32) ->
  dkr (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> ag (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> dkr p c) ->
  parser_at M' op ois
    (PM.PST 1 (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (removelast (PM.p_stk s))).
Proof.
  intros PA Ho Ho' HL AG1 AG9 AG3 DK8 DK368 C8 C368 DKC Hb Hb' AGV AGT.
  pose proof PA as (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3).
  pose proof SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
  cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG4 : forall a n, op + 9 <= a -> a + n <= op + 368 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG9|lia|lia]).
  split; [u64x AG1 H0|].
  split. { intros i Hi. destruct (Z_lt_le_dec i 8) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 9) as [Y|Y]; [apply DK8; [lia| apply D; lia]|].
           destruct (Z_lt_le_dec i 368) as [Y2|Y2]; [rewrite AG9 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 376) as [Y3|Y3]; [apply DK368; [lia| apply D; lia]| rewrite AG3 by lia; apply D; lia]. }
  split; [exact I|]. split; [exact C8|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H9]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H12]|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H20]|].
  split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| apply AG4; lia| exact NI]. }
  split.
  { split; [u64x AG9 F1|]. split; [u64x AG9 F2|].
    split. { apply (L5C.defined_agree M M'); [apply AG4; lia| exact F3]. }
    split; [u64x AG9 F4|]. split; [u64x AG9 F5|]. split; [u64x AG9 F6|]. split; [u64x AG9 F7|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [apply (PMPK.defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H320]|]. split; [u64x AG9 H328|]. split; [exact I|].
  split. { apply (PMPK.vstr_at_keep segs M M'); [lia| lia| apply AG4; lia| exact AGT| exact TB]. }
  split. { apply (PMPK.vec_at_pop segs M M' (op + 360) (PM.p_b s) (PM.p_k s) (PM.p_stk s) VEC HL); [lia|lia|exact Hb|exact Hb'| apply AG4; lia| eapply L5C.agree_on_sub; [exact AG3|lia|lia] | exact AGV|].
           replace (op + 360 + 8) with (op + 368) by lia. exact C368. }
  split; [right; reflexivity|]. split; [exact B2| exact B3].
Qed.
End Upd.

End Kit.
End PECF.
