(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PgV8 PnModel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNMF.

Definition dkr (M M' : word -> option byte) (a n : Z) : Prop :=
  forall i, a <= i < a + n -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None.
Lemma dkr_agree M M' a n : L5C.agree_on M M' a n -> dkr M M' a n.
Proof. intros AG i Hi D. rewrite AG by exact Hi. exact D. Qed.
Lemma dkr_sub M M' a n a' n' : dkr M M' a n -> a <= a' -> a' + n' <= a + n -> dkr M M' a' n'.
Proof. intros D H1 H2 i Hi. apply D. lia. Qed.
Lemma defined_dkr M M' a n : dkr M M' a n -> L5.defined M a n -> L5.defined M' a n.
Proof. intros D H i Hi. apply (D (a + i)); [lia| apply H; exact Hi]. Qed.

Section Agree.
Variable segs : list Segment. Context {bmK : BMode}.
Variable A : pm_addrs.
Variable vp : Z.
Let T3 : (word -> option byte) -> Z -> Z -> Prop := fun _ _ _ => True.
Let T4 : (word -> option byte) -> Z -> Z -> Z -> Prop := fun _ _ _ _ => True.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').

Local Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply PMF.ag_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u32x AG H := apply (PMF.u32_at_agree segs M M'); [eapply PMF.ag_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u8x AG H := apply (L5C.u8_at_agree segs M M'); [eapply PMF.ag_sub; [exact AG|lia|lia]|lia|lia|exact H].

Lemma bstate_at_agree a s : 0 <= a -> a + 40 <= 2 ^ 64 -> ag a 40 -> PNM.bstate_at segs M a s -> PNM.bstate_at segs M' a s.
Proof.
  intros Ha Ha' AG (H0 & H8 & H16 & H24 & H32).
  split; [u32x AG H0|]. split; [u64x AG H8|]. split; [u64x AG H16|]. split; [u8x AG H24| u64x AG H32].
Qed.

Lemma bvec_at_agree v b k stk : 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + PNM.BSZ * 2 ^ k <= 2 ^ 64 -> ag v 24 -> ag b (PNM.BSZ * 2 ^ k) ->
  PNM.bvec_at segs T3 T4 M v b k stk -> PNM.bvec_at segs T3 T4 M' v b k stk.
Proof.
  intros Hv Hv' Hb Hb' AGV AGB (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
  pose proof (PM.pow2_pos k ltac:(lia)) as P2. unfold PNM.BSZ in *.
  split; [u64x AGV V0|]. split; [u64x AGV V8|]. split; [u64x AGV V16|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
  split; [apply (L5C.defined_agree M M' b _ AGB DB)|]. split; [exact I|]. split; [exact I|].
  intros n Hn. pose proof (EL n Hn) as E.
  assert (Hn1 : Z.of_nat n + 1 <= 2 ^ k) by lia.
  assert (Hx : 40 * Z.of_nat n + 40 <= 40 * 2 ^ k) by lia.
  unfold PNM.BSZ. apply bstate_at_agree; [lia|lia| |exact E].
  eapply PMF.ag_sub; [exact AGB|lia|lia].
Qed.

Lemma v8_at_keep v x : 0 <= v -> v + 24 <= 2 ^ 64 -> ag v 24 ->
  (forall b n c, x = PGV8.V8Blk b n c -> dkr M M' b c) ->
  PGV8.v8_at segs T3 T4 M v x -> PGV8.v8_at segs T3 T4 M' v x.
Proof.
  intros Hv Hv' AG DK (D & _ & H). split; [apply (L5C.defined_agree M M' v 24 AG D)|]. split; [exact I|].
  destruct x as [|b n c].
  - destruct H as (W0 & W8 & W16). split; [u64x AG W0|]. split; [u64x AG W8| u64x AG W16].
  - destruct H as (W0 & W8 & W16 & Hn & Hc & Hb & Hal & DB & _ & _).
    split; [u64x AG W0|]. split; [u64x AG W8|]. split; [u64x AG W16|].
    split; [exact Hn|]. split; [exact Hc|]. split; [exact Hb|]. split; [exact Hal|].
    split; [apply (defined_dkr M M' b c (DK b n c eq_refl) DB)|]. split; exact I.
Qed.

Definition vs_cells (o : Z) (x : PM.vstr) : Z * Z := match x with PM.VShort _ => (o, 1) | PM.VLong _ _ _ => (o, 24) end.
Lemma vstr_at_keep o x : 0 <= o -> o + 24 <= 2 ^ 64 -> ag (fst (vs_cells o x)) (snd (vs_cells o x)) -> dkr M M' o 24 ->
  (forall c n p, x = PM.VLong c n p -> dkr M M' p c) ->
  PM.vstr_at segs T3 M o x -> PM.vstr_at segs T3 M' o x.
Proof.
  intros Ho Ho' AG DK DKB (D & _ & H). split; [apply (defined_dkr M M' o 24 DK D)|]. split; [exact I|].
  destruct x as [n|c n p]; cbn [vs_cells fst snd] in AG.
  - destruct H as (Hn & B0). split; [exact Hn| u8x AG B0].
  - destruct H as (W0 & W8 & W16 & Hn & Hc & He & DB & _).
    split; [u64x AG W0|]. split; [u64x AG W8|]. split; [u64x AG W16|].
    split; [exact Hn|]. split; [exact Hc|]. split; [exact He|].
    split; [apply (defined_dkr M M' p c (DKB c n p eq_refl) DB)| exact I].
Qed.

Lemma with_srcB_id s : PNM.with_srcB s (PNM.b_src s) = s.
Proof. destruct s; reflexivity. Qed.

Lemma bparser_at_frame op ois s src' :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 ->
  dkr M M' op PNM.PSIZE ->
  ag op 16 ->
  ag (op + PNM.OFF_SRC + 8) 232 ->
  PM.src_fields_at segs T3 M' (op + PNM.OFF_SRC) ois (ois + 16) src' ->
  ag (op + 312) 8 ->
  ag (op + PNM.OFF_BB) 24 -> (forall b n c, PNM.b_bb s = PGV8.V8Blk b n c -> dkr M M' b c) ->
  ag (fst (vs_cells (op + PNM.OFF_NB) (PNM.b_nb s))) (snd (vs_cells (op + PNM.OFF_NB) (PNM.b_nb s))) ->
  (forall c n p, PNM.b_nb s = PM.VLong c n p -> dkr M M' p c) ->
  ag (fst (vs_cells (op + PNM.OFF_TB) (PNM.b_tb s))) (snd (vs_cells (op + PNM.OFF_TB) (PNM.b_tb s))) ->
  (forall c n p, PNM.b_tb s = PM.VLong c n p -> dkr M M' p c) ->
  ag (op + PNM.OFF_STK) 24 -> 0 <= PNM.b_sb s -> PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s <= 2 ^ 64 -> ag (PNM.b_sb s) (PNM.BSZ * 2 ^ PNM.b_sk s) ->
  PNM.bparser_at segs A T3 T4 vp M op ois s -> PNM.bparser_at segs A T3 T4 vp M' op ois (PNM.with_srcB s src').
Proof.
  intros Ho Ho' DK AG0 AGN SRC AG312 AGBB DKBB AGNB DKNB AGTB DKTB AGSH Hb Hb' AGSB
         (H0 & D & _ & H8 & H9 & H10 & H12 & NI & _ & H312 & _ & BB & NB & TB & STK & M01 & D01).
  destruct s as [mo dn src bb nb tb ng tg bg sb sk stk].
  cbn [PNM.with_srcB PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_ng PNM.b_tg PNM.b_bg PNM.b_sb PNM.b_sk PNM.b_stk] in *.
  unfold PNM.bparser_at. unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  split; [u64x AG0 H0|]. split; [apply (defined_dkr M M' op 416 DK D)|]. split; [exact I|].
  split; [u8x AG0 H8|]. split; [u8x AG0 H9|]. split; [u8x AG0 H10|]. split; [u32x AG0 H12|].
  split; [apply (PMF.nullis_at_agree segs A M M'); [lia|lia|exact AGN|exact NI]|]. split; [exact SRC|].
  split; [u32x AG312 H312|]. split; [exact I|].
  split; [apply v8_at_keep; [lia|lia|exact AGBB|exact DKBB|exact BB]|].
  split; [apply vstr_at_keep; [lia|lia|exact AGNB| apply (dkr_sub M M' op 416); [exact DK|lia|lia]|exact DKNB|exact NB]|].
  split; [apply vstr_at_keep; [lia|lia|exact AGTB| apply (dkr_sub M M' op 416); [exact DK|lia|lia]|exact DKTB|exact TB]|].
  split; [apply bvec_at_agree; [lia|lia|exact Hb|exact Hb'|exact AGSH|exact AGSB|exact STK]|].
  split; [exact M01| exact D01].
Qed.

Lemma bparser_at_frame_gen op ois s src' bb' tb' tg' bg' :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 ->
  dkr M M' op PNM.PSIZE -> ag op 16 -> ag (op + PNM.OFF_SRC + 8) 232 ->
  PM.src_fields_at segs T3 M' (op + PNM.OFF_SRC) ois (ois + 16) src' ->
  ag (op + 312) 8 ->
  PGV8.v8_at segs T3 T4 M' (op + PNM.OFF_BB) bb' ->
  ag (fst (vs_cells (op + PNM.OFF_NB) (PNM.b_nb s))) (snd (vs_cells (op + PNM.OFF_NB) (PNM.b_nb s))) ->
  (forall c n p, PNM.b_nb s = PM.VLong c n p -> dkr M M' p c) ->
  PM.vstr_at segs T3 M' (op + PNM.OFF_TB) tb' ->
  ag (op + PNM.OFF_STK) 24 -> 0 <= PNM.b_sb s -> PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s <= 2 ^ 64 -> ag (PNM.b_sb s) (PNM.BSZ * 2 ^ PNM.b_sk s) ->
  PNM.bparser_at segs A T3 T4 vp M op ois s ->
  PNM.bparser_at segs A T3 T4 vp M' op ois
    (PNM.BPST (PNM.b_more s) (PNM.b_done s) src' bb' (PNM.b_nb s) tb' (PNM.b_ng s) tg' bg' (PNM.b_sb s) (PNM.b_sk s) (PNM.b_stk s)).
Proof.
  intros Ho Ho' DK AG0 AGN SRC AG312 BB' AGNB DKNB TB' AGSH Hb Hb' AGSB
         (H0 & D & _ & H8 & H9 & H10 & H12 & NI & _ & H312 & _ & BB & NB & TB & STK & M01 & D01).
  destruct s as [mo dn src bb nb tb ng tg bg sb sk stk].
  cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_ng PNM.b_tg PNM.b_bg PNM.b_sb PNM.b_sk PNM.b_stk] in *.
  unfold PNM.bparser_at. unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_ng PNM.b_tg PNM.b_bg PNM.b_sb PNM.b_sk PNM.b_stk].
  split; [u64x AG0 H0|]. split; [apply (defined_dkr M M' op 416 DK D)|]. split; [exact I|].
  split; [u8x AG0 H8|]. split; [u8x AG0 H9|]. split; [u8x AG0 H10|]. split; [u32x AG0 H12|].
  split; [apply (PMF.nullis_at_agree segs A M M'); [lia|lia|exact AGN|exact NI]|]. split; [exact SRC|].
  split; [u32x AG312 H312|]. split; [exact I|].
  split; [exact BB'|].
  split; [apply vstr_at_keep; [lia|lia|exact AGNB| apply (dkr_sub M M' op 416); [exact DK|lia|lia]|exact DKNB|exact NB]|].
  split; [exact TB'|].
  split; [apply bvec_at_agree; [lia|lia|exact Hb|exact Hb'|exact AGSH|exact AGSB|exact STK]|].
  split; [exact M01| exact D01].
Qed.

Lemma bparser_at_agree op ois s :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 -> ag op PNM.PSIZE ->
  (forall B m, In (B, m) (PNM.bparser_own s) -> 0 <= B /\ B + m <= 2 ^ 64 /\ ag B m) ->
  PNM.bparser_at segs A T3 T4 vp M op ois s -> PNM.bparser_at segs A T3 T4 vp M' op ois s.
Proof.
  intros Ho Ho' AG BL PA. rewrite <- (with_srcB_id s).
  assert (SRC : PM.src_fields_at segs T3 M (op + PNM.OFF_SRC) ois (ois + 16) (PNM.b_src s)) by (destruct PA as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  assert (SUB : forall a n, op <= a -> a + n <= op + 416 -> ag a n) by (intros a n H1 H2; apply (PMF.ag_sub M M' op 416); [exact AG|lia|lia]).
  assert (Bq : In (PM.sr_qc (PNM.b_src s), PM.CHUNK) (PNM.bparser_own s)) by (unfold PNM.bparser_own, PM.src_own; cbn; auto).
  assert (Bs : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) (PNM.bparser_own s)).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own. apply in_or_app. right. cbn. auto. }
  destruct (BL _ _ Bq) as (Q0 & Q1 & Q2). destruct (BL _ _ Bs) as (S0 & S1 & S2).
  apply (bparser_at_frame op ois s (PNM.b_src s)); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    [lia| lia| apply dkr_agree; exact AG| apply SUB; lia| apply SUB; lia| | apply SUB; lia| apply SUB; lia| | | | | | apply SUB; lia| exact S0| exact S1| exact S2| exact PA].
  - apply (PMF.src_fields_at_agree segs M M'); [lia| lia| exact Q0| exact Q1| apply SUB; lia| exact Q2| exact SRC].
  - intros b n c E. apply dkr_agree. apply (BL b c). unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. left. rewrite E. cbn. auto.
  - destruct (PNM.b_nb s); cbn [vs_cells fst snd]; apply SUB; lia.
  - intros c n p E. apply dkr_agree. apply (BL p c). unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. left. rewrite E. cbn. auto.
  - destruct (PNM.b_tb s); cbn [vs_cells fst snd]; apply SUB; lia.
  - intros c n p E. apply dkr_agree. apply (BL p c). unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. right. rewrite E. cbn. auto.
Qed.

End Agree.
End PNMF.
