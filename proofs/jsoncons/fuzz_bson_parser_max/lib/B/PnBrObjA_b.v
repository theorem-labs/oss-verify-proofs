(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core L5KnA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmModel PmModelFacts PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8 PnModel PnModelFacts PnBrObj.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNBOA.
Abbreviation mem := (word -> option byte).
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation set_more := PNBO.set_more.
Abbreviation set_stk := PNBO.set_stk.
Abbreviation set_nb := PNBO.set_nb.
Abbreviation set_tb := PNBO.set_tb.

(* [comment removed for export] *)
Definition gspan (c : Z) : Z := 8 * ((c + 7) / 8).
Lemma gspan_ge c : 0 <= c -> c <= gspan c < c + 8.
Proof. intros Hc. unfold gspan. pose proof (Z.div_mod (c + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma agsh_gspan (M M' : mem) b c : b mod 8 = 0 -> 0 <= c -> PMFA.agsh M M' b c -> PMFA.agsh M M' b (gspan c).
Proof.
  intros Hb Hc H x Hx. destruct (Z_lt_le_dec x (b + c)) as [X|X]; [apply H; lia|].
  pose proof (gspan_ge c Hc) as G. assert (Hc1 : 1 <= c) by (unfold gspan in *; pose proof (Z.div_mod (c + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)); lia).
  assert (E : S x = S (b + c - 1)).
  { unfold S. f_equal. unfold gspan in *.
    pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb, Z.add_0_r in Db.
    pose proof (Z.div_mod (c + 7) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)) as Mq.
    pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
    pose proof (Z.div_mod (b + c - 1) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (b + c - 1) 8 ltac:(lia)) as M1.
    lia. }
  rewrite E. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma annA_agree (M M' : mem) b u c : b mod 8 = 0 -> 0 <= u <= c -> PMFA.agsh M M' b (gspan c) -> annA M b u c -> annA M' b u c.
Proof.
  intros Hb Hu H (Z1 & Zm & Z2). unfold gspan in H.
  pose proof (Z.div_mod u 8 ltac:(lia)) as UD. pose proof (Z.mod_pos_bound u 8 ltac:(lia)) as UM.
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)) as CD. pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)) as CM.
  pose proof (Z.div_mod (u + 7) 8 ltac:(lia)) as UD7. pose proof (Z.mod_pos_bound (u + 7) 8 ltac:(lia)) as UM7.
  assert (U8 : (u + 7) / 8 <= (c + 7) / 8) by (apply Z.div_le_mono; lia).
  split; [|split].
  - intros j Hj. unfold byte_at in *. rewrite (PMFA.S_granule b j Hb ltac:(lia)). rewrite H by lia.
    rewrite <- (PMFA.S_granule b j Hb ltac:(lia)). exact (Z1 j Hj).
  - intros Hm. unfold byte_at in *. rewrite (PMFA.S_granule b (u / 8) Hb ltac:(lia)). rewrite H by lia.
    rewrite <- (PMFA.S_granule b (u / 8) Hb ltac:(lia)). exact (Zm Hm).
  - intros j Hj. unfold byte_at in *. rewrite (PMFA.S_granule b j Hb ltac:(lia)). rewrite H by lia.
    rewrite <- (PMFA.S_granule b j Hb ltac:(lia)). apply Z2. exact Hj.
Qed.

Section Obj.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable vp : Z.
Abbreviation bparser_at := (PNM.bparser_at segs A accA annA vp).
Variables M M' : mem.
(* [comment removed for export] *)
Variables NT Y NS : Z -> Prop.
Hypothesis AGX : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> NT i) -> L5C.agree_on M M' a n.
Hypothesis DKY : forall i, Y i -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None.
Hypothesis SHX : forall a n, (forall i, a <= i < a + n -> NS i) -> PMFA.agsh M M' a n.

Lemma agx a n : 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> NT i) -> L5C.agree_on M M' a n.
Proof. exact (AGX a n). Qed.
Lemma dkx a n : (forall i, a <= i < a + n -> Y i) -> PNMF.dkr M M' a n.
Proof. intros HY i Hi D. apply DKY; [apply HY; exact Hi| exact D]. Qed.
Lemma accx a n : (forall i, a <= i < a + n -> NS i) -> accA M a n -> accA M' a n.
Proof. intros HS C. exact (PMFA.accA_agree M M' a n (SHX a n HS) C). Qed.
Lemma annx b u c : b mod 8 = 0 -> 0 <= u <= c -> (forall i, b <= i < b + gspan c -> NS i) -> annA M b u c -> annA M' b u c.
Proof. intros Hb Hu HS AN. exact (annA_agree M M' b u c Hb Hu (SHX b (gspan c) HS) AN). Qed.

Lemma src_keep_x os isp sbp src : 0 <= os -> os + 296 <= 2 ^ 64 -> 0 <= PM.sr_qc src -> PM.sr_qc src + PM.CHUNK <= 2 ^ 64 ->
  (forall i, os + 240 <= i < os + 296 -> NT i) -> (forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> NT i) ->
  (forall i, os + 240 <= i < os + 296 -> NS i) -> (forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> NS i) ->
  PM.src_fields_at segs accA M os isp sbp src -> PM.src_fields_at segs accA M' os isp sbp src.
Proof.
  intros H1 H2 H3 H4 N1 N2 S1 S2. apply (PMFA.src_fields_at_agreeA segs M M' os isp sbp src H1 H2 H3 H4).
  - split; [apply agx; [lia|lia| intros i Hi; apply N1; lia]| apply SHX; intros i Hi; apply S1; lia].
  - split; [apply agx; [lia|lia| exact N2]| apply SHX; exact S2].
Qed.
Local Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact H].
Lemma v8_keep_x v x : 0 <= v -> v + 24 <= 2 ^ 64 -> (forall i, v <= i < v + 24 -> NT i) -> (forall i, v <= i < v + 24 -> NS i) ->
  (forall B m, In (B, m) (PGV8.v8_own x) -> forall i, B <= i < B + m -> Y i) ->
  (forall B m, In (B, m) (PGV8.v8_own x) -> forall i, B <= i < B + gspan m -> NS i) ->
  PGV8.v8_at segs accA annA M v x -> PGV8.v8_at segs accA annA M' v x.
Proof.
  intros H1 H2 N NSv YB SB (D & C & R). pose proof (agx v 24 H1 H2 N) as AG.
  split; [exact (L5C.defined_agree M M' v 24 AG D)|]. split; [exact (accx v 24 NSv C)|].
  destruct x as [|b n c].
  - destruct R as (W0 & W8 & W16). split; [u64x AG W0|]. split; [u64x AG W8| u64x AG W16].
  - destruct R as (W0 & W8 & W16 & Hn & Hc & Hb & Hal & DB & CB & AB).
    assert (IB : In (b, c) (PGV8.v8_own (PGV8.V8Blk b n c))) by (cbn; auto).
    split; [u64x AG W0|]. split; [u64x AG W8|]. split; [u64x AG W16|].
    split; [exact Hn|]. split; [exact Hc|]. split; [exact Hb|]. split; [exact Hal|].
    split; [exact (PNMF.defined_dkr M M' b c (dkx b c (YB b c IB)) DB)|].
    split; [apply (accx b n); [intros i Hi; apply (SB b c IB); pose proof (gspan_ge c ltac:(lia)); lia| exact CB]|].
    apply (annx b n c); [apply PMFA.mod16_8; exact Hal| lia| exact (SB b c IB)| exact AB].
Qed.
Lemma vstr_keep_x o x : 0 <= o -> o + 24 <= 2 ^ 64 -> (forall i, o <= i < o + 24 -> NT i) -> (forall i, o <= i < o + 24 -> Y i) -> (forall i, o <= i < o + 24 -> NS i) ->
  (forall B m, In (B, m) (PM.vs_own x) -> forall i, B <= i < B + m -> Y i) ->
  (forall B m, In (B, m) (PM.vs_own x) -> forall i, B <= i < B + m -> NS i) ->
  PM.vstr_at segs accA M o x -> PM.vstr_at segs accA M' o x.
Proof.
  intros H1 H2 N YO NSo YB SB (D & C & R). pose proof (agx o 24 H1 H2 N) as AG.
  split; [exact (L5C.defined_agree M M' o 24 AG D)|]. split; [exact (accx o 24 NSo C)|].
  destruct x as [n|c n p].
  - destruct R as (Hn & U). split; [exact Hn|]. apply (L5C.u8_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact U].
  - destruct R as (W0 & W8 & W16 & Hn & Hc & Hev & DB & CB).
    assert (IB : In (p, c) (PM.vs_own (PM.VLong c n p))) by (cbn; auto).
    split; [u64x AG W0|]. split; [u64x AG W8|]. split; [u64x AG W16|].
    split; [exact Hn|]. split; [exact Hc|]. split; [exact Hev|].
    split; [exact (PNMF.defined_dkr M M' p c (dkx p c (YB p c IB)) DB)| exact (accx p c (SB p c IB) CB)].
Qed.
Lemma bvec_keep_x v b k stk : 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + PNM.BSZ * 2 ^ k <= 2 ^ 64 ->
  (forall i, v <= i < v + 24 -> NT i) -> (forall i, b <= i < b + PNM.BSZ * 2 ^ k -> NT i) -> (forall i, b <= i < b + PNM.BSZ * 2 ^ k -> NS i) ->
  PNM.bvec_at segs accA annA M v b k stk -> PNM.bvec_at segs accA annA M' v b k stk.
Proof.
  intros H1 H2 H3 H4 N1 N2 S2 (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AB & EL).
  pose proof (agx v 24 H1 H2 N1) as AG. pose proof (agx b _ H3 H4 N2) as AGB. unfold PNM.bvec_at.
  split; [u64x AG V0|]. split; [u64x AG V8|]. split; [u64x AG V16|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
  split; [exact (L5C.defined_agree M M' b _ AGB DB)|].
  assert (Hnk : PNM.BSZ * Z.of_nat (length stk) <= PNM.BSZ * 2 ^ k) by (unfold PNM.BSZ; nia).
  split; [apply (accx b _); [intros i Hi; apply S2; lia| exact CB]|].
  split. { apply (annx b _ _); [apply PMFA.mod16_8; exact Hal| unfold PNM.BSZ in *; nia| | exact AB].
           intros i Hi. apply S2. unfold gspan, PNM.BSZ in *. replace (40 * 2 ^ k + 7) with (7 + (5 * 2 ^ k) * 8) in Hi by lia.
           rewrite Z.div_add in Hi by lia. change (7 / 8) with 0 in Hi. lia. }
  intros i Hi. apply (PNMF.bstate_at_agree segs M M'); [unfold PNM.BSZ in *; nia| unfold PNM.BSZ in *; nia| | exact (EL i Hi)].
  eapply (L5C.agree_on_sub M M'); [exact AGB| unfold PNM.BSZ; nia| unfold PNM.BSZ in *; nia].
Qed.

(* [comment removed for export] *)
Lemma bparser_at_xfer op ois s s' :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 ->
  bparser_at M op ois s -> (forall i, op <= i < op + PNM.PSIZE -> Y i) -> (forall i, op <= i < op + PNM.PSIZE -> NS i) ->
  (forall i, op <= i < op + 8 -> NT i) -> (forall i, op + 10 <= i < op + 16 -> NT i) ->
  (forall i, op + 24 <= i < op + 256 -> NT i) -> (forall i, op + 312 <= i < op + 320 -> NT i) ->
  L5.u8_at segs M' (op + 8) (PNM.b_more s') -> L5.u8_at segs M' (op + 9) (PNM.b_done s') ->
  (PNM.b_more s' = 0 \/ PNM.b_more s' = 1) -> (PNM.b_done s' = 0 \/ PNM.b_done s' = 1) ->
  PM.src_fields_at segs accA M' (op + PNM.OFF_SRC) ois (ois + 16) (PNM.b_src s') ->
  PGV8.v8_at segs accA annA M' (op + PNM.OFF_BB) (PNM.b_bb s') ->
  PM.vstr_at segs accA M' (op + PNM.OFF_NB) (PNM.b_nb s') ->
  PM.vstr_at segs accA M' (op + PNM.OFF_TB) (PNM.b_tb s') ->
  PNM.bvec_at segs accA annA M' (op + PNM.OFF_STK) (PNM.b_sb s') (PNM.b_sk s') (PNM.b_stk s') ->
  bparser_at M' op ois s'.
Proof.
  intros Ho Ho' (H0 & D & C0 & H8 & H9 & H10 & H12 & NI & _ & H312 & C312 & _) YO SO N0 N10 N24 N312 MO DN M01 D01 SRC BB NB TB STK.
  unfold PNM.bparser_at. unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|exact N0]|lia|lia|exact H0]|].
  split; [apply (PNMF.defined_dkr M M' op 416 (dkx op 416 YO) D)|]. split; [apply (accx op 16); [intros i Hi; apply SO; lia| exact C0]|].
  split; [exact MO|]. split; [exact DN|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply N10; lia]|lia|lia|exact H10]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply N10; lia]|lia|lia|exact H12]|].
  split. { apply (PMFA.nullis_at_agreeA segs A M M'); [lia|lia| | exact NI].
           split; [apply agx; [lia|lia|intros i Hi; apply N24; lia]| apply SHX; intros i Hi; apply SO; lia]. }
  split; [exact SRC|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply N312; lia]|lia|lia|exact H312]|].
  split; [apply (accx (op + 312) 8); [intros i Hi; apply SO; lia| exact C312]|].
  split; [exact BB|]. split; [exact NB|]. split; [exact TB|]. split; [exact STK|]. split; [exact M01| exact D01].
Qed.
End Obj.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Piece.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable vp : Z.
Abbreviation bparser_at := (PNM.bparser_at segs A accA annA vp).
Variables M M' : mem.
Variable X : Z -> Prop.
Hypothesis FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ X a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis MG : mem_grows M M'.
Let Y : Z -> Prop := fun _ => True.
Let NT : Z -> Prop := fun a => ~ X a.
(* [comment removed for export] *)
Definition nsh (i : Z) : Prop := 0 <= S i < 2 ^ 64 /\ ~ X (S i).
Lemma AGX : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ X i) -> L5C.agree_on M M' a n.
Proof. intros a n H1 H2 N i Hi. apply FRZ; [lia| apply N; exact Hi]. Qed.
Lemma DKY : forall i, Y i -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None.
Proof. intros i _ D. apply MG. exact D. Qed.
Lemma SHX : forall a n, (forall i, a <= i < a + n -> nsh i) -> PMFA.agsh M M' a n.
Proof. intros a n HS x Hx. destruct (HS x Hx) as [R N]. apply FRZ; [exact R| exact N]. Qed.
Let src_keep_x := (src_keep_x segs M M' NT nsh AGX SHX).
Let v8_keep_x := (v8_keep_x segs M M' NT Y nsh AGX DKY SHX).
Let vstr_keep_x := (vstr_keep_x segs M M' NT Y nsh AGX DKY SHX).
Let bvec_keep_x := (bvec_keep_x segs M M' NT nsh AGX SHX).
Let bparser_at_xfer := (bparser_at_xfer segs A vp M M' NT Y nsh AGX DKY SHX).
Let agx := AGX.
Local Ltac yt := first [ exact (fun _ _ => I) | exact (fun _ _ _ _ _ => I) ].
Abbreviation own_below := PNBO.own_below.

(* [comment removed for export] *)
Definition shadow_kept (op : Z) (s : PNM.bpst) : Prop :=
  (forall i, op <= i < op + PNM.PSIZE -> nsh i) /\ (forall B m, In (B, m) (PNM.bparser_own s) -> forall i, B <= i < B + gspan m -> nsh i).

Lemma own_src s : In (PM.sr_qc (PNM.b_src s), PM.CHUNK) (PNM.bparser_own s).
Proof. unfold PNM.bparser_own, PM.src_own. cbn. auto. Qed.
Lemma own_stk s : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) (PNM.bparser_own s).
Proof. unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own. apply in_or_app. right. cbn. auto. Qed.
Lemma own_bb s B m : In (B, m) (PGV8.v8_own (PNM.b_bb s)) -> In (B, m) (PNM.bparser_own s).
Proof. intros Hi. unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hi. Qed.
Lemma own_nb s B m : In (B, m) (PM.vs_own (PNM.b_nb s)) -> In (B, m) (PNM.bparser_own s).
Proof. intros Hi. unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hi. Qed.
Lemma own_tb s B m : In (B, m) (PM.vs_own (PNM.b_tb s)) -> In (B, m) (PNM.bparser_own s).
Proof. intros Hi. unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hi. Qed.
Lemma nsh_blk op s B m : shadow_kept op s -> In (B, m) (PNM.bparser_own s) -> 0 <= m -> forall i, B <= i < B + m -> nsh i.
Proof. intros [_ SK] Hi Hm i Hr. apply (SK B m Hi). pose proof (gspan_ge m Hm). lia. Qed.

(* [comment removed for export] *)
Lemma bparser_set_more op ois s v :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 -> bparser_at M op ois s -> own_below op s -> shadow_kept op s ->
  (forall a, op <= a < op + PNM.PSIZE -> X a -> op + 8 <= a < op + 9) ->
  (forall B m, In (B, m) (PNM.bparser_own s) -> forall i, B <= i < B + m -> ~ X i) ->
  L5.u8_at segs M' (op + 8) v -> (v = 0 \/ v = 1) ->
  bparser_at M' op ois (set_more s v).
Proof.
  intros Ho Ho' PA OB SK XW NB' U8 V01. pose proof PA as (_ & _ & _ & _ & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & _ & D01).
  pose proof SK as (SKo & SKb).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  assert (NX : forall i, op <= i < op + 416 -> ~ (op + 8 <= i < op + 9) -> ~ X i) by (intros i Hi N Xi; apply N; apply XW; [exact Hi| exact Xi]).
  pose proof (own_src s) as Bq. pose proof (own_stk s) as Bs.
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & Qr & _). pose proof STK as (_ & _ & _ & Hk & _).
  apply (bparser_at_xfer op ois s (set_more s v) Ho Ho' PA (fun _ _ => I)); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [PNBO.set_more PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - exact SKo.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - exact U8.
  - apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact H9].
  - exact V01.
  - exact D01.
  - destruct (OB _ _ Bq) as (Q0 & Q1).
    apply src_keep_x; [lia|lia|lia|lia| intros i Hi; apply NX; lia| exact (NB' _ _ Bq)| intros i Hi; apply SKo; lia| exact (nsh_blk op s _ _ SK Bq ltac:(unfold PM.CHUNK; lia))| exact SRC].
  - apply v8_keep_x; [lia|lia| intros i Hi; apply NX; lia| intros i Hi; apply SKo; lia| yt| intros B m Hi; exact (SKb B m (own_bb s B m Hi))| exact BB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| intros i Hi; apply SKo; lia| yt| intros B m Hi; apply (nsh_blk op s B m SK (own_nb s B m Hi))| exact NB].
    destruct (PNM.b_nb s); cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst]. destruct NB as (_ & _ & _ & _ & _ & Hc & _). lia.
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| intros i Hi; apply SKo; lia| yt| intros B m Hi; apply (nsh_blk op s B m SK (own_tb s B m Hi))| exact TB].
    destruct (PNM.b_tb s); cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst]. destruct TB as (_ & _ & _ & _ & _ & Hc & _). lia.
  - destruct (OB _ _ Bs) as (Q0 & Q1).
    apply bvec_keep_x; [lia|lia|lia|lia| intros i Hi; apply NX; lia| exact (NB' _ _ Bs)| apply (nsh_blk op s _ _ SK Bs); unfold PNM.BSZ; nia| exact STK].
Qed.

(* [comment removed for export] *)
Lemma bparser_top_upd op ois s l c c' :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 -> bparser_at M op ois s -> PNM.b_stk s = l ++ [c] -> shadow_kept op s ->
  (forall a, op <= a < op + PNM.PSIZE -> ~ X a) ->
  (forall i, PM.sr_qc (PNM.b_src s) <= i < PM.sr_qc (PNM.b_src s) + PM.CHUNK -> ~ X i) ->
  (forall i, PNM.b_sb s <= i < PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s -> X i ->
             PNM.b_sb s + 40 * Z.of_nat (length l) <= i < PNM.b_sb s + 40 * Z.of_nat (length l) + 40) ->
  PNM.bstate_at segs M' (PNM.b_sb s + 40 * Z.of_nat (length l)) c' ->
  0 <= PNM.b_sb s -> PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s <= 2 ^ 64 ->
  0 <= PM.sr_qc (PNM.b_src s) -> PM.sr_qc (PNM.b_src s) + PM.CHUNK <= 2 ^ 64 ->
  bparser_at M' op ois (set_stk s (l ++ [c'])).
Proof.
  intros Ho Ho' PA ES SK NXo NXq XW TOP Hb0 Hb1 Hq0 Hq1. pose proof PA as (_ & _ & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  pose proof SK as (SKo & SKb).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNM.BSZ in *.
  set (b := PNM.b_sb s) in *. set (k := PNM.b_sk s) in *. set (n := Z.of_nat (length l)) in *.
  pose proof STK as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AB & EL). unfold PNM.BSZ in *.
  rewrite ES in Hlen, V8, EL, CB, AB. rewrite length_app in Hlen, V8, EL, CB, AB. cbn [length] in Hlen, V8, EL, CB, AB.
  assert (Hn : n + 1 <= 2 ^ k) by (unfold n; lia).
  assert (NX : forall i, b <= i < b + 40 * 2 ^ k -> ~ (b + 40 * n <= i < b + 40 * n + 40) -> ~ X i) by (intros i Hi N Xi; apply N; apply XW; [exact Hi| exact Xi]).
  pose proof (nsh_blk op s _ _ SK (own_stk s) ltac:(unfold PNM.BSZ; nia)) as NSs. fold b k in NSs. unfold PNM.BSZ in NSs.
  apply (bparser_at_xfer op ois s (set_stk s (l ++ [c'])) Ho Ho' PA (fun _ _ => I)); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [PNBO.set_stk PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - exact SKo.
  - intros i Hi. apply NXo. lia.
  - intros i Hi. apply NXo. lia.
  - intros i Hi. apply NXo. lia.
  - intros i Hi. apply NXo. lia.
  - apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NXo; lia]|lia|lia|exact H8].
  - apply (L5C.u8_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NXo; lia]|lia|lia|exact H9].
  - exact M01.
  - exact D01.
  - apply src_keep_x; [lia|lia|lia|lia| intros i Hi; apply NXo; lia| exact NXq| intros i Hi; apply SKo; lia| exact (nsh_blk op s _ _ SK (own_src s) ltac:(unfold PM.CHUNK; lia))| exact SRC].
  - apply v8_keep_x; [lia|lia| intros i Hi; apply NXo; lia| intros i Hi; apply SKo; lia| yt| intros B m Hi; exact (SKb B m (own_bb s B m Hi))| exact BB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NXo; lia| yt| intros i Hi; apply SKo; lia| yt| intros B m Hi; apply (nsh_blk op s B m SK (own_nb s B m Hi))| exact NB].
    destruct (PNM.b_nb s); cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst]. destruct NB as (_ & _ & _ & _ & _ & Hc & _). lia.
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NXo; lia| yt| intros i Hi; apply SKo; lia| yt| intros B m Hi; apply (nsh_blk op s B m SK (own_tb s B m Hi))| exact TB].
    destruct (PNM.b_tb s); cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst]. destruct TB as (_ & _ & _ & _ & _ & Hc & _). lia.
  - fold b k. unfold PNM.bvec_at, PNM.BSZ. rewrite length_app. cbn [length].
    split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NXo; lia]|lia|lia|exact V0]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NXo; lia]|lia|lia|exact V8]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply agx; [lia|lia|intros i Hi; apply NXo; lia]|lia|lia|exact V16]|].
    split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
    split; [apply (L5.defined_grows M M' b _ MG DB)|].
    split; [apply (accx M M' nsh SHX b _); [intros i Hi; apply NSs; nia| exact CB]|].
    split. { apply (annx M M' nsh SHX b _ _); [apply PMFA.mod16_8; exact Hal| nia| | exact AB].
             intros i Hi. apply NSs. unfold gspan in Hi. replace (40 * 2 ^ k + 7) with (7 + (5 * 2 ^ k) * 8) in Hi by lia.
             rewrite Z.div_add in Hi by lia. change (7 / 8) with 0 in Hi. lia. }
    intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
    + rewrite nth_middle. exact TOP.
    + assert (Hi' : (i < length l)%nat) by lia. rewrite app_nth1 by exact Hi'.
      pose proof (EL i ltac:(lia)) as E. rewrite app_nth1 in E by exact Hi'.
      apply (PNMF.bstate_at_agree segs M M'); [lia|lia| |exact E].
      apply agx; [lia|lia|]. intros j Hj. apply NX; unfold n; lia.
Qed.

End Piece.

Lemma PNM_own_src s : In (PM.sr_qc (PNM.b_src s), PM.CHUNK) (PNM.bparser_own s).
Proof. unfold PNM.bparser_own, PM.src_own. cbn. auto. Qed.
Lemma PNM_own_stk s : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) (PNM.bparser_own s).
Proof. unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own. apply in_or_app. right. cbn. auto. Qed.
Lemma PNM_own_bb s B m : In (B, m) (PGV8.v8_own (PNM.b_bb s)) -> In (B, m) (PNM.bparser_own s).
Proof. intros Hi. unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hi. Qed.
Lemma PNM_own_nb s B m : In (B, m) (PM.vs_own (PNM.b_nb s)) -> In (B, m) (PNM.bparser_own s).
Proof. intros Hi. unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hi. Qed.
Lemma PNM_own_tb s B m : In (B, m) (PM.vs_own (PNM.b_tb s)) -> In (B, m) (PNM.bparser_own s).
Proof. intros Hi. unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hi. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sem.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable vp : Z.
Variables M M' : mem.
Definition snt (i : Z) : Prop := M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Definition sns (i : Z) : Prop := M' (Z_to_bv 64 (S i)) = M (Z_to_bv 64 (S i)).
Lemma sAGX : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> snt i) -> L5C.agree_on M M' a n.
Proof. intros a n _ _ H i Hi. exact (H i Hi). Qed.
Lemma sDKY : forall i, snt i -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None.
Proof. intros i E D. unfold snt in E. rewrite E. exact D. Qed.
Lemma sSHX : forall a n, (forall i, a <= i < a + n -> sns i) -> PMFA.agsh M M' a n.
Proof. intros a n H x Hx. exact (H x Hx). Qed.
(* [comment removed for export] *)
Lemma agA_snt a n : PMFA.agA M M' a n -> forall i, a <= i < a + n -> snt i.
Proof. intros [G _] i Hi. exact (G i Hi). Qed.
Lemma agA_sns a n : PMFA.agA M M' a n -> forall i, a <= i < a + n -> sns i.
Proof. intros [_ S'] i Hi. exact (S' i Hi). Qed.
Definition bparser_at_xferS := (bparser_at_xfer segs A vp M M' snt snt sns sAGX sDKY sSHX).
Definition src_keep_S := (src_keep_x segs M M' snt sns sAGX sSHX).
Definition v8_keep_S := (v8_keep_x segs M M' snt snt sns sAGX sDKY sSHX).
Definition vstr_keep_S := (vstr_keep_x segs M M' snt snt sns sAGX sDKY sSHX).
Definition bvec_keep_S := (bvec_keep_x segs M M' snt sns sAGX sSHX).

(* [comment removed for export] *)
Lemma bparser_keepS op ois s :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 ->
  PMFA.agA M M' op PNM.PSIZE ->
  (forall B m, In (B, m) (PNM.bparser_own s) -> 0 <= B /\ B + m <= 2 ^ 64 /\ PMFA.agA M M' B m) ->
  PNM.bparser_at segs A accA annA vp M op ois s -> PNM.bparser_at segs A accA annA vp M' op ois s.
Proof.
  intros Ho Ho' AGo AGb PA. pose proof PA as (_ & _ & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  pose proof (agA_snt _ _ AGo) as No. pose proof (agA_sns _ _ AGo) as So.
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  assert (BLK : forall B m, In (B, m) (PNM.bparser_own s) -> 0 <= m -> (forall i, B <= i < B + m -> snt i) /\ (forall i, B <= i < B + m -> sns i) /\ 0 <= B /\ B + m <= 2 ^ 64).
  { intros B m Hi Hm. destruct (AGb B m Hi) as (B0 & B1 & AG). split; [exact (agA_snt _ _ AG)|]. split; [exact (agA_sns _ _ AG)|]. lia. }
  assert (BLKG : forall B m, In (B, m) (PNM.bparser_own s) -> 0 <= m -> B mod 8 = 0 -> forall i, B <= i < B + gspan m -> sns i).
  { intros B m Hi Hm HB. destruct (AGb B m Hi) as (B0 & B1 & [_ AG]). exact (agsh_gspan M M' B m HB Hm AG). }
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & Qr & _). pose proof STK as (_ & _ & _ & Hk & _).
  destruct (BLK _ _ (PNM_own_src s) ltac:(unfold PM.CHUNK; lia)) as (NTq & NSq & Q0 & Q1).
  destruct (BLK _ _ (PNM_own_stk s) ltac:(unfold PNM.BSZ; nia)) as (NTs & NSs & S0 & S1).
  replace s with (PNM.BPST (PNM.b_more s) (PNM.b_done s) (PNM.b_src s) (PNM.b_bb s) (PNM.b_nb s) (PNM.b_tb s) (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) (PNM.b_stk s)) at 2 by (destruct s; reflexivity).
  apply (bparser_at_xferS op ois s _ Ho Ho' PA); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - intros i Hi. apply No. lia.
  - exact So.
  - intros i Hi. apply No. lia.
  - intros i Hi. apply No. lia.
  - intros i Hi. apply No. lia.
  - intros i Hi. apply No. lia.
  - apply (L5C.u8_at_agree segs M M'); [apply sAGX; [lia|lia|intros i Hi; apply No; lia]|lia|lia|exact H8].
  - apply (L5C.u8_at_agree segs M M'); [apply sAGX; [lia|lia|intros i Hi; apply No; lia]|lia|lia|exact H9].
  - exact M01.
  - exact D01.
  - apply src_keep_S; [lia|lia|lia|lia| intros i Hi; apply No; lia| exact NTq| intros i Hi; apply So; lia| exact NSq| exact SRC].
  - apply v8_keep_S; [lia|lia| intros i Hi; apply No; lia| intros i Hi; apply So; lia| | | exact BB].
    + intros B m Hi i Hr. pose proof (PNM_own_bb s B m Hi) as OI. destruct (PNM.b_bb s) eqn:EBB; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PGV8.v8_at in BB. destruct BB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (X & _). apply X. exact Hr.
    + intros B m Hi. pose proof (PNM_own_bb s B m Hi) as OI. destruct (PNM.b_bb s) eqn:EBB; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PGV8.v8_at in BB. destruct BB as (_ & _ & _ & _ & _ & Hn & Hc & _ & Hal & _). exact (BLKG _ _ OI ltac:(lia) (PMFA.mod16_8 _ Hal)).
  - apply vstr_keep_S; [lia|lia| intros i Hi; apply No; lia| intros i Hi; apply No; lia| intros i Hi; apply So; lia| | | exact NB].
    + intros B m Hi. pose proof (PNM_own_nb s B m Hi) as OI. destruct (PNM.b_nb s) eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in NB. destruct NB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (X & _). exact X.
    + intros B m Hi. pose proof (PNM_own_nb s B m Hi) as OI. destruct (PNM.b_nb s) eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in NB. destruct NB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (_ & X & _). exact X.
  - apply vstr_keep_S; [lia|lia| intros i Hi; apply No; lia| intros i Hi; apply No; lia| intros i Hi; apply So; lia| | | exact TB].
    + intros B m Hi. pose proof (PNM_own_tb s B m Hi) as OI. destruct (PNM.b_tb s) eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in TB. destruct TB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (X & _). exact X.
    + intros B m Hi. pose proof (PNM_own_tb s B m Hi) as OI. destruct (PNM.b_tb s) eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in TB. destruct TB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (_ & X & _). exact X.
  - apply bvec_keep_S; [lia|lia|lia|lia| intros i Hi; apply No; lia| exact NTs| exact NSs| exact STK].
Qed.
End Sem.
End PNBOA.
