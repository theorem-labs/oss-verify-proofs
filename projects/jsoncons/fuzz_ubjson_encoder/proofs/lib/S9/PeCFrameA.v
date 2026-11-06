(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5KnA L5LazyA L5DefsA L5CoreAS9 L5StepARS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmModelFactsA PmStatics PmStaticsA PmSpecs PmSpecsA PeStepA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCStatics PeCModel PeCFrame PeCSinkA PeCStaticsA PeCModelA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECFA.
Section Kit.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable E : pe_addrs.
Variable L : asan_layout.
Variable ar : asan_run.

Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation enc_atA := (PECA.enc_atA segs E L ar).
Abbreviation sink_atA := (PESKA.sink_atA segs L ar).
Abbreviation ec_stateA := (PECA.ec_stateA segs A).
Abbreviation content_ok := (PEC.content_ok segs A).

Lemma mod16_8 b : b mod 16 = 0 -> b mod 8 = 0.
Proof.
  intros H. destruct (proj1 (Z.mod_divide b 16 ltac:(lia)) H) as [q Hq]. rewrite Hq.
  replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma aobjA_sub FF o n o' n' : PMSPA.aobjA FF o n -> o <= o' -> o' + n' <= o + n -> PMSPA.aobjA FF o' n'.
Proof. intros (f & Hf & H1 & H2) Ho Hn. exists f. split; [exact Hf|]. lia. Qed.

Section Agree.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').
Abbreviation agA := (PMFA.agA M M').
Abbreviation agsh := (PMFA.agsh M M').

Lemma annA_agree b u c : 0 <= u <= c -> b mod 8 = 0 -> agsh b c -> annA M b u c -> annA M' b u c.
Proof.
  intros Hu B8 SH (Z0 & P & T). unfold PMSPA.annA, HAJ.ann_shadow in *.
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)) as D2.
  pose proof (Z.div_mod u 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound u 8 ltac:(lia)) as D4.
  pose proof (Z.div_mod b 8 ltac:(lia)) as D5.
  assert (SJ : forall j, 0 <= j < (c + 7) / 8 -> M' (Z_to_bv 64 (HeapIfaceA.S b + j)) = M (Z_to_bv 64 (HeapIfaceA.S b + j))).
  { intros j Hj. replace (HeapIfaceA.S b + j) with (HeapIfaceA.S (b + j * 8)).
    - apply SH. lia.
    - unfold HeapIfaceA.S. rewrite Z.div_add by lia. lia. }
  assert (U8 : 0 <= u / 8) by (apply Z.div_pos; lia).
  split; [|split].
  - intros j Hj. unfold byte_at. rewrite SJ; [exact (Z0 j Hj)| lia].
  - intros NZ. unfold byte_at. rewrite SJ; [exact (P NZ)| lia].
  - intros j Hj. unfold byte_at. rewrite SJ; [exact (T j Hj)|]. assert (0 <= (u + 7) / 8) by (apply Z.div_pos; lia). lia.
Qed.

Lemma enc_atA_agree ov fb en :
  0 <= ov -> ov + 56 <= 2 ^ 64 -> agA ov 56 ->
  (0 < PEC.en_k en -> 0 <= PEC.en_b en /\ PEC.en_b en + PEC.ESZ * PEC.ecap (PEC.en_k en) <= 2 ^ 64 /\ agA (PEC.en_b en) (PEC.ESZ * PEC.ecap (PEC.en_k en))) ->
  enc_atA M ov fb en -> enc_atA M' ov fb en.
Proof.
  intros Ho Ho' [AG SH] AGB (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & CC & Hk & Hlen & Hd & Hk0 & HB & HI0).
  pose proof (PEC.ecap_nonneg (PEC.en_k en)) as CN.
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 56 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG|lia|lia]).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V32]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V40]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V48]|].
  split; [apply (L5C.defined_agree M M' ov 56 AG D)|]. split; [exact (PMFA.accA_agree M M' ov 56 SH CC)|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hd|]. split; [exact Hk0|]. split.
  - intros Hp. destruct (HB Hp) as (AL & DB & BR & ACCB & ANB). destruct (AGB Hp) as (B0 & B1 & [AB SB]).
    split; [exact AL|]. split; [exact (L5C.defined_agree M M' _ _ AB DB)|]. split; [exact BR|]. split.
    + apply (PMFA.accA_agree M M'); [| exact ACCB]. intros x Hx. apply SB. unfold PEC.ESZ in *. nia.
    + apply annA_agree; [unfold PEC.ESZ in *; nia| exact AL| exact SB| exact ANB].
  - intros i Hi. pose proof (HI0 i Hi) as IT.
    assert (Hp : 0 < PEC.en_k en).
    { destruct (Z.eq_dec (PEC.en_k en) 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in Hlen. rewrite Z0 in Hlen. cbn in Hlen. lia. }
    destruct (AGB Hp) as (B0 & B1 & [AB SB]).
    apply (PECF.eitem_at_agree segs M M'); [| unfold PEC.ESZ in *; lia | unfold PEC.ESZ in *; lia | exact IT].
    eapply L5C.agree_on_sub; [exact AB| unfold PEC.ESZ; lia| unfold PEC.ESZ in *; lia].
Qed.

Lemma sink_atA_agree P o k :
  0 <= o -> o + 24 <= 2 ^ 64 -> agA o 24 ->
  (0 < PESK.sk_c k -> 0 <= PESK.sk_b k /\ PESK.sk_b k + PESK.sk_c k <= 2 ^ 64 /\ agA (PESK.sk_b k) (PESK.sk_c k)) ->
  sink_atA P M o k -> sink_atA P M' o k.
Proof.
  intros Ho Ho' [AG SH] AGB (V0 & V8 & V16 & D & CC & Hz & Hc & Hc0 & HB).
  assert (SUB : forall a n, o <= a -> a + n <= o + 24 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG|lia|lia]).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.defined_agree M M' o 24 AG D)|]. split; [exact (PMFA.accA_agree M M' o 24 SH CC)|].
  split; [exact Hz|]. split; [exact Hc|]. split; [exact Hc0|].
  intros Hp. destruct (HB Hp) as (DB & ACCB & ANB & BR & CAP & NM). destruct (AGB Hp) as (B0 & B1 & [AB SB]).
  pose proof BR as (_ & _ & AL16 & _).
  split; [exact (L5C.defined_agree M M' _ _ AB DB)|]. split.
  { apply (PMFA.accA_agree M M'); [| exact ACCB]. intros x Hx. apply SB. lia. }
  split.
  { apply annA_agree; [lia| exact (mod16_8 _ AL16)| exact SB| exact ANB]. }
  split; [exact BR|]. split; [exact CAP| exact NM].
Qed.

Lemma ec_stateA_agree fb e cat :
  0 <= PMSPA.o_ec A fb -> PMSPA.o_ec A fb + 16 <= 2 ^ 64 -> agA (PMSPA.o_ec A fb) 16 -> ec_stateA M fb e cat -> ec_stateA M' fb e cat.
Proof.
  intros Ho Ho' [AG SH].
  assert (EC : forall v c, PMSPA.ec_at segs M (PMSPA.o_ec A fb) v c -> PMSPA.ec_at segs M' (PMSPA.o_ec A fb) v c).
  { intros v c (E0 & E8 & ED & CC). split; [|split; [|split]].
    - apply (PMF.u32_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia] |lia|lia| exact E0].
    - apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia] |lia|lia| exact E8].
    - exact (L5C.defined_agree M M' _ _ AG ED).
    - exact (PMFA.accA_agree M M' _ _ SH CC). }
  unfold PECA.ec_stateA. destruct e.
  - intros (v & Hv & EC0). exists v. split; [exact Hv| apply EC; exact EC0].
  - apply EC.
Qed.
End Agree.

Section Along.
Variables (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte).
Hypothesis EK : L5SAR.ek L ar LB FF sp scr W M M'.
Hypothesis WAPP : PMKA.wapp W.
Hypothesis FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47.
Hypothesis BRB : forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47.
Abbreviation blk_out := (PMKA.blk_out W).

Let AOBJ := PMKA.agA_obj L ar LB FF sp scr W M M' EK WAPP FRB.
Let ABLK := PMKA.agA_blk L ar LB FF sp scr W M M' EK WAPP BRB.

Lemma enc_keepA ov fb en :
  PMSPA.aobjA FF ov 56 -> (forall i, ov <= i < ov + 56 -> L5.outside W i) ->
  incl (PEC.enc_own en) LB -> (0 < PEC.en_k en -> blk_out (PEC.en_b en) (PEC.ESZ * PEC.ecap (PEC.en_k en))) ->
  enc_atA M ov fb en -> enc_atA M' ov fb en.
Proof.
  intros AO OW INC OB. destruct (PMKA.aobjA_bounds FF FRB ov 56 AO) as [H0 H1].
  apply enc_atA_agree; [lia|lia| exact (AOBJ ov 56 AO OW)|].
  intros Hp. assert (IN : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) LB).
  { apply INC. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  destruct (BRB _ IN) as [B0 B1]. cbn [fst snd] in B0, B1. split; [lia|]. split; [lia|]. exact (ABLK _ _ IN (OB Hp)).
Qed.

Lemma sink_keepA P o k :
  PMSPA.aobjA FF o 24 -> (forall i, o <= i < o + 24 -> L5.outside W i) ->
  incl (PESK.sink_own k) LB -> (0 < PESK.sk_c k -> blk_out (PESK.sk_b k) (PESK.sk_c k)) ->
  sink_atA P M o k -> sink_atA P M' o k.
Proof.
  intros AO OW INC OB. destruct (PMKA.aobjA_bounds FF FRB o 24 AO) as [H0 H1].
  apply sink_atA_agree; [lia|lia| exact (AOBJ o 24 AO OW)|].
  intros Hp. assert (IN : In (PESK.sk_b k, PESK.sk_c k) LB).
  { apply INC. unfold PESK.sink_own. replace (PESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  destruct (BRB _ IN) as [B0 B1]. cbn [fst snd] in B0, B1. split; [lia|]. split; [lia|]. exact (ABLK _ _ IN (OB Hp)).
Qed.

Lemma ec_state_keepA fb e cat :
  PMSPA.aobjA FF (PMSPA.o_ec A fb) 16 -> (forall i, PMSPA.o_ec A fb <= i < PMSPA.o_ec A fb + 16 -> L5.outside W i) ->
  ec_stateA M fb e cat -> ec_stateA M' fb e cat.
Proof.
  intros AO OW. destruct (PMKA.aobjA_bounds FF FRB _ 16 AO) as [H0 H1].
  apply ec_stateA_agree; [lia|lia| exact (AOBJ _ 16 AO OW)].
Qed.

Lemma content_keepA fb p s str sm :
  PMSPA.aobjA FF (PMSPA.o_is A fb) 272 -> (forall i, PMSPA.o_is A fb + 80 <= i < PMSPA.o_is A fb + 80 + 24 -> L5.outside W i) ->
  incl (PM.vs_own str) LB -> (forall c n q, str = PM.VLong c n q -> n < c /\ blk_out q c) -> (forall n, str = PM.VShort n -> n <= 22) ->
  In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB -> blk_out (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  PM.sr_qc (PM.p_src s) <= PM.sr_de (PM.p_src s) -> 0 <= PM.sr_rem (PM.p_src s) ->
  PM.sr_de (PM.p_src s) + PM.sr_rem (PM.p_src s) <= PM.sr_qc (PM.p_src s) + PM.CHUNK ->
  content_ok M fb p (PM.p_src s) str sm -> content_ok M' fb p (PM.p_src s) str sm.
Proof.
  intros AO OW INCS OB SHORT INQ OQ H1 H2 H3.
  destruct (PMKA.aobjA_bounds FF FRB _ 272 AO) as [I0 I1]. destruct (BRB _ INQ) as [Q0 Q1]. cbn [fst snd] in Q0, Q1.
  assert (AIS : L5C.agree_on M M' (PMSPA.o_is A fb + 80) 24).
  { exact (proj1 (AOBJ (PMSPA.o_is A fb + 80) 24 (aobjA_sub FF (PMSPA.o_is A fb) 272 (PMSPA.o_is A fb + 80) 24 AO ltac:(lia) ltac:(lia)) OW)). }
  intros CO. apply (PECF.content_ok_agree segs A M M' fb p (PM.p_src s) str sm).
  - unfold PMSP.o_is, PMSPA.o_is in *. lia.
  - unfold PMSP.o_is, PMSPA.o_is in *. lia.
  - unfold PMSP.o_is, PMSPA.o_is in *. exact AIS.
  - intros c n q Hs. destruct (OB c n q Hs) as [Hn OBq].
    assert (INB : In (q, c) LB) by (apply INCS; unfold PM.vs_own; rewrite Hs; left; reflexivity).
    destruct (BRB _ INB) as [B0 B1]. cbn [fst snd] in B0, B1.
    split; [lia|]. split; [lia|]. split; [exact Hn|]. exact (proj1 (ABLK q c INB OBq)).
  - lia.
  - lia.
  - exact H1.
  - exact H2.
  - exact H3.
  - exact (proj1 (ABLK _ _ INQ OQ)).
  - exact SHORT.
  - exact CO.
Qed.

Lemma err_okA_keep e : PMST.addrs_wf A ->
  (forall a, PMST.dep A a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside W a) ->
  PESTA.err_okA segs A AA E M e -> PESTA.err_okA segs A AA E M' e.
Proof.
  intros WF SD. apply (PESTA.err_okA_frame segs A AA E WF M M').
  intros a Ha D. destruct (SD a D) as (J1 & J2 & J3). apply EK. split; [exact Ha|]. split; [|exact J3].
  unfold aclient, aclient_g. right; right; left. split; [lia| exact J2].
Qed.
End Along.

Section Upd.
Variables M M' : word -> option byte.
Abbreviation agA := (PMFA.agA M M').
Abbreviation agsh := (PMFA.agsh M M').
Abbreviation parser_atA := (PM.parser_at segs A accA annA).

Lemma parser_depth_updA op ois s d' :
  parser_atA M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  agA op 12 -> agA (op + 16) 368 -> agsh op 384 -> L5.defined M' op 384 ->
  L5.u32_at segs M' (op + 12) d' -> 0 <= d' <= PM.MAX_DEPTH + 1 ->
  0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 -> agA (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> agA (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n q, PM.p_tb s = PM.VLong c n q -> agA q c) ->
  parser_atA M' op ois (PM.PST (PM.p_more s) (PM.p_done s) d' (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s)).
Proof.
  intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
         [AG1 _] AG2 SH D' C12 Hd Hq Hq' AGQ Hb Hb' AGV AGT.
  pose proof AG2 as [AG2d _].
  unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG4 : forall a n, op + 16 <= a -> a + n <= op + 384 -> agA a n).
  { intros a n X1 X2. split; [eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| intros x Hx; apply SH; lia]. }
  split; [apply (L5C.u64_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG1|lia|lia]| lia| lia| exact H0]|].
  split; [exact D'|].
  split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
  split; [apply (L5C.u8_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG1|lia|lia]|lia|lia|exact H8]|].
  split; [apply (L5C.u8_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG1|lia|lia]|lia|lia|exact H9]|].
  split; [exact C12|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply (AG4 (op + 16) 1); lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply (AG4 (op + 20) 4); lia|lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA segs A M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
  split; [apply (PMFA.src_fields_at_agreeA segs M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
  split; [apply (PMFA.vstr_at_agreeA segs M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
  split; [apply (PMFA.vec_at_agreeA segs M M' (op + 360)); [lia|lia|exact Hb|exact Hb'| eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| exact AGV| exact VEC]|].
  split; [exact B1|]. split; [exact B2| exact Hd].
Qed.

Lemma parser_morepop_updA op ois s :
  parser_atA M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  agA op 8 -> agA (op + 9) 7 -> agA (op + 16) 344 -> agsh op 384 -> L5.defined M' op 384 ->
  L5.u8_at segs M' (op + 8) 1 ->
  PM.vec_at segs accA annA M' (op + 360) (PM.p_b s) (PM.p_k s) (removelast (PM.p_stk s)) ->
  0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 -> agA (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  (forall c n q, PM.p_tb s = PM.VLong c n q -> agA q c) ->
  parser_atA M' op ois (PM.PST 1 (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (removelast (PM.p_stk s))).
Proof.
  intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
         [AG1 _] [AG9 _] AG2 SH D' C8 VEC' Hq Hq' AGQ AGT.
  pose proof AG2 as [AG2d _].
  unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG4 : forall a n, op + 16 <= a -> a + n <= op + 360 -> agA a n).
  { intros a n X1 X2. split; [eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| intros x Hx; apply SH; lia]. }
  split; [apply (L5C.u64_at_agree segs M M'); [exact AG1| lia| lia| exact H0]|].
  split; [exact D'|].
  split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
  split; [exact C8|].
  split; [apply (L5C.u8_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG9|lia|lia]|lia|lia|exact H9]|].
  split; [apply (PMF.u32_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG9|lia|lia]|lia|lia|exact H12]|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply (AG4 (op + 16) 1); lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply (AG4 (op + 20) 4); lia|lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA segs A M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
  split; [apply (PMFA.src_fields_at_agreeA segs M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
  split; [apply (PMFA.vstr_at_agreeA segs M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
  split; [exact VEC'|].
  split; [right; reflexivity|]. split; [exact B2| exact B3].
Qed.
End Upd.
End Kit.
End PECFA.
