(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmModel PmModelFacts PmSpecs PgSrc PgV8 PnModel PnModelFacts.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNBO.

Definition set_more (s : PNM.bpst) (v : Z) : PNM.bpst :=
  PNM.BPST v (PNM.b_done s) (PNM.b_src s) (PNM.b_bb s) (PNM.b_nb s) (PNM.b_tb s) (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) (PNM.b_stk s).
Definition set_stk (s : PNM.bpst) (stk' : list PNM.bstate) : PNM.bpst :=
  PNM.BPST (PNM.b_more s) (PNM.b_done s) (PNM.b_src s) (PNM.b_bb s) (PNM.b_nb s) (PNM.b_tb s) (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) stk'.
Definition set_nb (s : PNM.bpst) (x : PM.vstr) (g : Z) : PNM.bpst :=
  PNM.BPST (PNM.b_more s) (PNM.b_done s) (PNM.b_src s) (PNM.b_bb s) x (PNM.b_tb s) g (PNM.b_tg s) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) (PNM.b_stk s).
Definition set_tb (s : PNM.bpst) (x : PM.vstr) (g : Z) : PNM.bpst :=
  PNM.BPST (PNM.b_more s) (PNM.b_done s) (PNM.b_src s) (PNM.b_bb s) (PNM.b_nb s) x (PNM.b_ng s) g (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) (PNM.b_stk s).

Abbreviation mem := (word -> option byte).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.

Section Obj.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable vp : Z.
Abbreviation bparser_at := (PNM.bparser_at segs A T3 T4 vp).
Variables M M' : mem.
(* [comment removed for export] *)
Variables NT Y : Z -> Prop.
Hypothesis AGX : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> NT i) -> L5C.agree_on M M' a n.
Hypothesis DKY : forall i, Y i -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None.

Lemma agx a n : 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> NT i) -> L5C.agree_on M M' a n.
Proof. exact (AGX a n). Qed.
Lemma dkx a n : (forall i, a <= i < a + n -> Y i) -> PNMF.dkr M M' a n.
Proof. intros HY i Hi D. apply DKY; [apply HY; exact Hi| exact D]. Qed.

Lemma src_keep_x os isp sbp src : 0 <= os -> os + 296 <= 2 ^ 64 -> 0 <= PM.sr_qc src -> PM.sr_qc src + PM.CHUNK <= 2 ^ 64 ->
  (forall i, os + 240 <= i < os + 296 -> NT i) -> (forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> NT i) ->
  PM.src_fields_at segs T3 M os isp sbp src -> PM.src_fields_at segs T3 M' os isp sbp src.
Proof.
  intros H1 H2 H3 H4 N1 N2. apply (PMF.src_fields_at_agree segs M M' os isp sbp src H1 H2 H3 H4).
  - apply agx; [lia|lia| intros i Hi; apply N1; lia].
  - apply agx; [lia|lia| exact N2].
Qed.
Lemma v8_keep_x v x : 0 <= v -> v + 24 <= 2 ^ 64 -> (forall i, v <= i < v + 24 -> NT i) ->
  (forall B m, In (B, m) (PGV8.v8_own x) -> forall i, B <= i < B + m -> Y i) ->
  PGV8.v8_at segs T3 T4 M v x -> PGV8.v8_at segs T3 T4 M' v x.
Proof.
  intros H1 H2 N YB. apply (PNMF.v8_at_keep segs M M' v x H1 H2); [apply agx; [lia|lia|exact N]|].
  intros b n c ->. apply dkx. apply (YB b c). cbn. auto.
Qed.
Lemma vstr_keep_x o x : 0 <= o -> o + 24 <= 2 ^ 64 -> (forall i, o <= i < o + 24 -> NT i) -> (forall i, o <= i < o + 24 -> Y i) ->
  (forall B m, In (B, m) (PM.vs_own x) -> forall i, B <= i < B + m -> Y i) ->
  PM.vstr_at segs T3 M o x -> PM.vstr_at segs T3 M' o x.
Proof.
  intros H1 H2 N YO YB. apply (PNMF.vstr_at_keep segs M M' o x H1 H2); [| apply dkx; exact YO|].
  - destruct x; cbn [PNMF.vs_cells fst snd]; apply agx; try lia; intros i Hi; apply N; lia.
  - intros c n p ->. apply dkx. apply (YB p c). cbn. auto.
Qed.
Lemma bvec_keep_x v b k stk : 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + PNM.BSZ * 2 ^ k <= 2 ^ 64 ->
  (forall i, v <= i < v + 24 -> NT i) -> (forall i, b <= i < b + PNM.BSZ * 2 ^ k -> NT i) ->
  PNM.bvec_at segs T3 T4 M v b k stk -> PNM.bvec_at segs T3 T4 M' v b k stk.
Proof. intros H1 H2 H3 H4 N1 N2. apply (PNMF.bvec_at_agree segs M M' v b k stk H1 H2 H3 H4); (apply agx; [lia|lia|assumption]). Qed.

(* [comment removed for export] *)
Lemma bparser_at_xfer op ois s s' :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 ->
  bparser_at M op ois s -> (forall i, op <= i < op + PNM.PSIZE -> Y i) ->
  (forall i, op <= i < op + 8 -> NT i) -> (forall i, op + 10 <= i < op + 16 -> NT i) ->
  (forall i, op + 24 <= i < op + 256 -> NT i) -> (forall i, op + 312 <= i < op + 320 -> NT i) ->
  L5.u8_at segs M' (op + 8) (PNM.b_more s') -> L5.u8_at segs M' (op + 9) (PNM.b_done s') ->
  (PNM.b_more s' = 0 \/ PNM.b_more s' = 1) -> (PNM.b_done s' = 0 \/ PNM.b_done s' = 1) ->
  PM.src_fields_at segs T3 M' (op + PNM.OFF_SRC) ois (ois + 16) (PNM.b_src s') ->
  PGV8.v8_at segs T3 T4 M' (op + PNM.OFF_BB) (PNM.b_bb s') ->
  PM.vstr_at segs T3 M' (op + PNM.OFF_NB) (PNM.b_nb s') ->
  PM.vstr_at segs T3 M' (op + PNM.OFF_TB) (PNM.b_tb s') ->
  PNM.bvec_at segs T3 T4 M' (op + PNM.OFF_STK) (PNM.b_sb s') (PNM.b_sk s') (PNM.b_stk s') ->
  bparser_at M' op ois s'.
Proof.
  intros Ho Ho' (H0 & D & _ & H8 & H9 & H10 & H12 & NI & _ & H312 & _ & _) YO N0 N10 N24 N312 MO DN M01 D01 SRC BB NB TB STK.
  unfold PNM.bparser_at. unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|exact N0]|lia|lia|exact H0]|].
  split; [apply (PNMF.defined_dkr M M' op 416 (dkx op 416 YO) D)|]. split; [exact I|].
  split; [exact MO|]. split; [exact DN|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply N10; lia]|lia|lia|exact H10]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply N10; lia]|lia|lia|exact H12]|].
  split; [apply (PMF.nullis_at_agree segs A M M'); [lia|lia| apply agx; [lia|lia|intros i Hi; apply N24; lia]| exact NI]|].
  split; [exact SRC|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply N312; lia]|lia|lia|exact H312]|].
  split; [exact I|]. split; [exact BB|]. split; [exact NB|]. split; [exact TB|]. split; [exact STK|]. split; [exact M01| exact D01].
Qed.

End Obj.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Piece.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable vp : Z.
Abbreviation bparser_at := (PNM.bparser_at segs A T3 T4 vp).
Variables M M' : mem.
Variable X : Z -> Prop.
Hypothesis FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ X a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis MG : mem_grows M M'.
Let Y : Z -> Prop := fun _ => True.
Lemma AGX : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ X i) -> L5C.agree_on M M' a n.
Proof. intros a n H1 H2 N i Hi. apply FRZ; [lia| apply N; exact Hi]. Qed.
Lemma DKY : forall i, Y i -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None.
Proof. intros i _ D. apply MG. exact D. Qed.
Let NT : Z -> Prop := fun a => ~ X a.
Let src_keep_x := (src_keep_x segs M M' NT AGX).
Let v8_keep_x := (v8_keep_x segs M M' NT Y AGX DKY).
Let vstr_keep_x := (vstr_keep_x segs M M' NT Y AGX DKY).
Let bvec_keep_x := (bvec_keep_x segs M M' NT AGX).
Let bparser_at_xfer := (bparser_at_xfer segs A vp M M' NT Y AGX DKY).
Let agx := AGX.
Local Ltac yt := first [ exact (fun _ _ => I) | exact (fun _ _ _ _ _ => I) ].

(* [comment removed for export] *)
Definition own_below (op : Z) (s : PNM.bpst) : Prop := forall B m, In (B, m) (PNM.bparser_own s) -> 0 <= B /\ B + m <= op.

(* [comment removed for export] *)
Lemma bparser_set_more op ois s v :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 -> bparser_at M op ois s -> own_below op s ->
  (forall a, op <= a < op + PNM.PSIZE -> X a -> op + 8 <= a < op + 9) ->
  (forall B m, In (B, m) (PNM.bparser_own s) -> forall i, B <= i < B + m -> ~ X i) ->
  L5.u8_at segs M' (op + 8) v -> (v = 0 \/ v = 1) ->
  bparser_at M' op ois (set_more s v).
Proof.
  intros Ho Ho' PA OB XW NB' U8 V01. pose proof PA as (_ & _ & _ & _ & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & _ & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  assert (NX : forall i, op <= i < op + 416 -> ~ (op + 8 <= i < op + 9) -> ~ X i) by (intros i Hi N Xi; apply N; apply XW; [exact Hi| exact Xi]).
  assert (Bq : In (PM.sr_qc (PNM.b_src s), PM.CHUNK) (PNM.bparser_own s)) by (unfold PNM.bparser_own, PM.src_own; cbn; auto).
  assert (Bs : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) (PNM.bparser_own s)).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own. apply in_or_app. right. cbn. auto. }
  apply (bparser_at_xfer op ois s (set_more s v) Ho Ho' PA (fun _ _ => I)); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [set_more PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - exact U8.
  - apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact H9].
  - exact V01.
  - exact D01.
  - destruct (OB _ _ Bq) as (Q0 & Q1).
    apply src_keep_x; [lia|lia|lia|lia| intros i Hi; apply NX; lia| exact (NB' _ _ Bq)| exact SRC].
  - apply v8_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| exact BB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| yt| exact NB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| yt| exact TB].
  - destruct (OB _ _ Bs) as (Q0 & Q1).
    apply bvec_keep_x; [lia|lia|lia|lia| intros i Hi; apply NX; lia| exact (NB' _ _ Bs)| exact STK].
Qed.

(* [comment removed for export] *)
Lemma bparser_top_upd op ois s l c c' :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 -> bparser_at M op ois s -> PNM.b_stk s = l ++ [c] ->
  (forall a, op <= a < op + PNM.PSIZE -> ~ X a) ->
  (forall i, PM.sr_qc (PNM.b_src s) <= i < PM.sr_qc (PNM.b_src s) + PM.CHUNK -> ~ X i) ->
  (forall i, PNM.b_sb s <= i < PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s -> X i ->
             PNM.b_sb s + 40 * Z.of_nat (length l) <= i < PNM.b_sb s + 40 * Z.of_nat (length l) + 40) ->
  PNM.bstate_at segs M' (PNM.b_sb s + 40 * Z.of_nat (length l)) c' ->
  0 <= PNM.b_sb s -> PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s <= 2 ^ 64 ->
  0 <= PM.sr_qc (PNM.b_src s) -> PM.sr_qc (PNM.b_src s) + PM.CHUNK <= 2 ^ 64 ->
  bparser_at M' op ois (set_stk s (l ++ [c'])).
Proof.
  intros Ho Ho' PA ES NXo NXq XW TOP Hb0 Hb1 Hq0 Hq1. pose proof PA as (_ & _ & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNM.BSZ in *.
  set (b := PNM.b_sb s) in *. set (k := PNM.b_sk s) in *. set (n := Z.of_nat (length l)) in *.
  pose proof STK as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL). unfold PNM.BSZ in *.
  rewrite ES in Hlen, V8, EL. rewrite length_app in Hlen, V8, EL. cbn [length] in Hlen, V8, EL.
  assert (Hn : n + 1 <= 2 ^ k) by (unfold n; lia).
  assert (NX : forall i, b <= i < b + 40 * 2 ^ k -> ~ (b + 40 * n <= i < b + 40 * n + 40) -> ~ X i) by (intros i Hi N Xi; apply N; apply XW; [exact Hi| exact Xi]).
  apply (bparser_at_xfer op ois s (set_stk s (l ++ [c'])) Ho Ho' PA (fun _ _ => I)); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [set_stk PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - intros i Hi. apply NXo. lia.
  - intros i Hi. apply NXo. lia.
  - intros i Hi. apply NXo. lia.
  - intros i Hi. apply NXo. lia.
  - apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NXo; lia]|lia|lia|exact H8].
  - apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NXo; lia]|lia|lia|exact H9].
  - exact M01.
  - exact D01.
  - apply src_keep_x; [lia|lia|lia|lia| intros i Hi; apply NXo; lia| exact NXq| exact SRC].
  - apply v8_keep_x; [lia|lia| intros i Hi; apply NXo; lia| yt| exact BB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NXo; lia| yt| yt| exact NB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NXo; lia| yt| yt| exact TB].
  - fold b k. unfold PNM.bvec_at, PNM.BSZ. rewrite length_app. cbn [length].
    split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NXo; lia]|lia|lia|exact V0]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NXo; lia]|lia|lia|exact V8]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NXo; lia]|lia|lia|exact V16]|].
    split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
    split; [apply (L5.defined_grows M M' b _ MG DB)|]. split; [exact I|]. split; [exact I|].
    intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
    + rewrite nth_middle. exact TOP.
    + assert (Hi' : (i < length l)%nat) by lia. rewrite app_nth1 by exact Hi'.
      pose proof (EL i ltac:(lia)) as E. rewrite app_nth1 in E by exact Hi'.
      apply (PNMF.bstate_at_agree segs M M'); [lia|lia| |exact E].
      apply agx; [lia|lia|]. intros j Hj. apply NX; unfold n; lia.
Qed.

(* [comment removed for export] *)
Lemma bparser_set_nb op ois s x' :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 -> bparser_at M op ois s ->
  (forall a, op <= a < op + PNM.PSIZE -> X a -> op + PNM.OFF_NB <= a < op + PNM.OFF_NB + 24) ->
  (forall i, PM.sr_qc (PNM.b_src s) <= i < PM.sr_qc (PNM.b_src s) + PM.CHUNK -> ~ X i) ->
  (forall i, PNM.b_sb s <= i < PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s -> ~ X i) ->
  0 <= PM.sr_qc (PNM.b_src s) -> PM.sr_qc (PNM.b_src s) + PM.CHUNK <= 2 ^ 64 -> 0 <= PNM.b_sb s -> PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s <= 2 ^ 64 ->
  PM.vstr_at segs T3 M' (op + PNM.OFF_NB) x' ->
  bparser_at M' op ois (set_nb s x' (PNM.b_ng s)).
Proof.
  intros Ho Ho' PA XW NXq NXs Hq0 Hq1 Hb0 Hb1 NB'. pose proof PA as (_ & _ & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNM.BSZ in *.
  assert (NX : forall i, op <= i < op + 416 -> ~ (op + 344 <= i < op + 344 + 24) -> ~ X i) by (intros i Hi N Xi; apply N; apply XW; [exact Hi| exact Xi]).
  apply (bparser_at_xfer op ois s (set_nb s x' (PNM.b_ng s)) Ho Ho' PA (fun _ _ => I)); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [set_nb PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact H8].
  - apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact H9].
  - exact M01.
  - exact D01.
  - apply src_keep_x; [lia|lia|lia|lia| intros i Hi; apply NX; lia| exact NXq| exact SRC].
  - apply v8_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| exact BB].
  - exact NB'.
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| yt| exact TB].
  - unfold PNM.BSZ. apply bvec_keep_x; [lia|lia|lia|unfold PNM.BSZ; lia| intros i Hi; apply NX; lia| unfold PNM.BSZ; exact NXs| exact STK].
Qed.

(* [comment removed for export] *)
Lemma bparser_stk_upd op ois s l0 tl tl' :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 -> bparser_at M op ois s -> PNM.b_stk s = l0 ++ tl ->
  (forall a, op <= a < op + PNM.PSIZE -> X a -> op + PNM.OFF_STK + 8 <= a < op + PNM.OFF_STK + 16) ->
  (forall i, PM.sr_qc (PNM.b_src s) <= i < PM.sr_qc (PNM.b_src s) + PM.CHUNK -> ~ X i) ->
  (forall i, PNM.b_sb s <= i < PNM.b_sb s + 40 * Z.of_nat (length l0) -> ~ X i) ->
  L5.u64_at segs M' (op + PNM.OFF_STK + 8) (PNM.b_sb s + PNM.BSZ * Z.of_nat (length (l0 ++ tl'))) ->
  (forall i, (i < length tl')%nat -> PNM.bstate_at segs M' (PNM.b_sb s + PNM.BSZ * Z.of_nat (length l0 + i)) (nth i tl' PNM.bs_root)) ->
  Z.of_nat (length (l0 ++ tl')) <= 2 ^ PNM.b_sk s ->
  0 <= PNM.b_sb s -> PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s <= 2 ^ 64 ->
  0 <= PM.sr_qc (PNM.b_src s) -> PM.sr_qc (PNM.b_src s) + PM.CHUNK <= 2 ^ 64 ->
  bparser_at M' op ois (set_stk s (l0 ++ tl')).
Proof.
  intros Ho Ho' PA ES XW NXq NXp VE EL' Hlen' Hb0 Hb1 Hq0 Hq1. pose proof PA as (_ & _ & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNM.BSZ in *.
  set (b := PNM.b_sb s) in *. set (k := PNM.b_sk s) in *.
  pose proof STK as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL). unfold PNM.BSZ in *.
  assert (NX : forall i, op <= i < op + 416 -> ~ (op + 392 + 8 <= i < op + 392 + 16) -> ~ X i) by (intros i Hi N Xi; apply N; apply XW; [exact Hi| exact Xi]).
  apply (bparser_at_xfer op ois s (set_stk s (l0 ++ tl')) Ho Ho' PA (fun _ _ => I)); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [set_stk PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact H8].
  - apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact H9].
  - exact M01.
  - exact D01.
  - apply src_keep_x; [lia|lia|lia|lia| intros i Hi; apply NX; lia| exact NXq| exact SRC].
  - apply v8_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| exact BB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| yt| exact NB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| yt| exact TB].
  - fold b k. unfold PNM.bvec_at, PNM.BSZ.
    split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact V0]|].
    split; [exact VE|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact V16]|].
    split; [exact Hk|]. split; [exact Hlen'|]. split; [exact Hal|].
    split; [apply (L5.defined_grows M M' b _ MG DB)|]. split; [exact I|]. split; [exact I|].
    intros i Hi. rewrite length_app in Hi, Hlen'. destruct (Nat.lt_ge_cases i (length l0)) as [LT|GE].
    + rewrite app_nth1 by exact LT.
      assert (Hi0 : (i < length (PNM.b_stk s))%nat) by (rewrite ES, length_app; lia).
      pose proof (EL i Hi0) as E. rewrite ES in E. rewrite app_nth1 in E by exact LT.
      apply (PNMF.bstate_at_agree segs M M'); [lia|nia| |exact E].
      apply agx; [lia|nia|]. intros j Hj. apply NXp. nia.
    + rewrite app_nth2 by exact GE. replace (Z.of_nat i) with (Z.of_nat (length l0 + (i - length l0))) by lia.
      apply EL'. lia.
Qed.

(* [comment removed for export] *)
Lemma bparser_hd_stk_upd op ois s mo dn l0 tl tl' :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 -> bparser_at M op ois s -> PNM.b_stk s = l0 ++ tl ->
  (forall a, op <= a < op + PNM.PSIZE -> X a -> (op + 8 <= a < op + 10) \/ (op + PNM.OFF_STK + 8 <= a < op + PNM.OFF_STK + 16)) ->
  (forall i, PM.sr_qc (PNM.b_src s) <= i < PM.sr_qc (PNM.b_src s) + PM.CHUNK -> ~ X i) ->
  (forall i, PNM.b_sb s <= i < PNM.b_sb s + 40 * Z.of_nat (length l0) -> ~ X i) ->
  L5.u8_at segs M' (op + 8) mo -> L5.u8_at segs M' (op + 9) dn -> (mo = 0 \/ mo = 1) -> (dn = 0 \/ dn = 1) ->
  L5.u64_at segs M' (op + PNM.OFF_STK + 8) (PNM.b_sb s + PNM.BSZ * Z.of_nat (length (l0 ++ tl'))) ->
  (forall i, (i < length tl')%nat -> PNM.bstate_at segs M' (PNM.b_sb s + PNM.BSZ * Z.of_nat (length l0 + i)) (nth i tl' PNM.bs_root)) ->
  Z.of_nat (length (l0 ++ tl')) <= 2 ^ PNM.b_sk s ->
  0 <= PNM.b_sb s -> PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s <= 2 ^ 64 ->
  0 <= PM.sr_qc (PNM.b_src s) -> PM.sr_qc (PNM.b_src s) + PM.CHUNK <= 2 ^ 64 ->
  bparser_at M' op ois (PNM.BPST mo dn (PNM.b_src s) (PNM.b_bb s) (PNM.b_nb s) (PNM.b_tb s) (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) (l0 ++ tl')).
Proof.
  intros Ho Ho' PA ES XW NXq NXp U8 U9 M01' D01' VE EL' Hlen' Hb0 Hb1 Hq0 Hq1. pose proof PA as (_ & _ & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNM.BSZ in *.
  set (b := PNM.b_sb s) in *. set (k := PNM.b_sk s) in *.
  pose proof STK as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL). unfold PNM.BSZ in *.
  assert (NX : forall i, op <= i < op + 416 -> ~ (op + 8 <= i < op + 10) -> ~ (op + 392 + 8 <= i < op + 392 + 16) -> ~ X i).
  { intros i Hi N1 N2 Xi. destruct (XW i Hi Xi); [apply N1| apply N2]; assumption. }
  apply (bparser_at_xfer op ois s _ Ho Ho' PA (fun _ _ => I)); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - exact U8.
  - exact U9.
  - exact M01'.
  - exact D01'.
  - apply src_keep_x; [lia|lia|lia|lia| intros i Hi; apply NX; lia| exact NXq| exact SRC].
  - apply v8_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| exact BB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| yt| exact NB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| yt| exact TB].
  - fold b k. unfold PNM.bvec_at, PNM.BSZ.
    split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact V0]|].
    split; [exact VE|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact V16]|].
    split; [exact Hk|]. split; [exact Hlen'|]. split; [exact Hal|].
    split; [apply (L5.defined_grows M M' b _ MG DB)|]. split; [exact I|]. split; [exact I|].
    intros i Hi. rewrite length_app in Hi, Hlen'. destruct (Nat.lt_ge_cases i (length l0)) as [LT|GE].
    + rewrite app_nth1 by exact LT.
      assert (Hi0 : (i < length (PNM.b_stk s))%nat) by (rewrite ES, length_app; lia).
      pose proof (EL i Hi0) as E. rewrite ES in E. rewrite app_nth1 in E by exact LT.
      apply (PNMF.bstate_at_agree segs M M'); [lia|nia| |exact E].
      apply agx; [lia|nia|]. intros j Hj. apply NXp. nia.
    + rewrite app_nth2 by exact GE. replace (Z.of_nat i) with (Z.of_nat (length l0 + (i - length l0))) by lia.
      apply EL'. lia.
Qed.

(* [comment removed for export] *)
Lemma bparser_revec op ois s mo b' k' stk' :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 -> bparser_at M op ois s ->
  (forall a, op <= a < op + PNM.PSIZE -> X a -> (op + 8 <= a < op + 9) \/ (op + PNM.OFF_STK <= a < op + PNM.OFF_STK + 24)) ->
  (forall i, PM.sr_qc (PNM.b_src s) <= i < PM.sr_qc (PNM.b_src s) + PM.CHUNK -> ~ X i) ->
  L5.u8_at segs M' (op + 8) mo -> (mo = 0 \/ mo = 1) ->
  PNM.bvec_at segs T3 T4 M' (op + PNM.OFF_STK) b' k' stk' ->
  0 <= PM.sr_qc (PNM.b_src s) -> PM.sr_qc (PNM.b_src s) + PM.CHUNK <= 2 ^ 64 ->
  bparser_at M' op ois (PNM.BPST mo (PNM.b_done s) (PNM.b_src s) (PNM.b_bb s) (PNM.b_nb s) (PNM.b_tb s) (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) b' k' stk').
Proof.
  intros Ho Ho' PA XW NXq U8 M01' VEC Hq0 Hq1. pose proof PA as (_ & _ & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNM.BSZ in *.
  assert (NX : forall i, op <= i < op + 416 -> ~ (op + 8 <= i < op + 9) -> ~ (op + 392 <= i < op + 392 + 24) -> ~ X i).
  { intros i Hi N1 N2 Xi. destruct (XW i Hi Xi); [apply N1| apply N2]; assumption. }
  apply (bparser_at_xfer op ois s _ Ho Ho' PA (fun _ _ => I)); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - exact U8.
  - apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact H9].
  - exact M01'.
  - exact D01.
  - apply src_keep_x; [lia|lia|lia|lia| intros i Hi; apply NX; lia| exact NXq| exact SRC].
  - apply v8_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| exact BB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| yt| exact NB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| yt| exact TB].
  - exact VEC.
Qed.

End Piece.
End PNBO.
