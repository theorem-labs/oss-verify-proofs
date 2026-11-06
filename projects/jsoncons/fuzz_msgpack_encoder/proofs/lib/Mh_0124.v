(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module PnMpKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnMpModelFacts.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQMK.

Definition set_more (s : PQM.mpst) (v : Z) : PQM.mpst :=
  PQM.MPST v (PQM.p_done s) (PQM.p_depth s) (PQM.p_src s) (PQM.p_tb s) (PQM.p_tg s) (PQM.p_bb s) (PQM.p_bg s) (PQM.p_sb s) (PQM.p_sk s) (PQM.p_stk s).

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.
Variable vp vpa : Z.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.

Section Along.
Variables (LBc : list (Z * Z)) (sp' scr' : Z) (W' : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LBc sp' scr' W' M M'.
Hypothesis STKc : L5C.stk (hl_sptop L) M sp' scr'.
Hypothesis SCR0 : 0 <= scr'.
Hypothesis BR : PMFR.brange L LBc.

Let ag_hi := PMPK.ag_hi segs L KL LBc sp' scr' W' M M' E STKc SCR0.
Let ag_blk := PMPK.ag_blk segs L KL LBc sp' scr' W' M M' E STKc BR.
(* [comment removed for export] *)
Definition untouched (B m : Z) : Prop := forall i, B <= i < B + m -> ~ PMK.inW W' i.

(* [comment removed for export] *)
Lemma mparser_keep op ois s : sp' <= op -> op + PQM.PSIZE <= 2 ^ 64 -> (forall i, op <= i < op + PQM.PSIZE -> ~ PMK.inW W' i) ->
  incl (PQM.mparser_own s) LBc -> (forall B m, In (B, m) (PQM.mparser_own s) -> untouched B m) ->
  PQM.mparser_at segs A T3 T4 vp M op ois s -> PQM.mparser_at segs A T3 T4 vp M' op ois s.
Proof.
  intros H1 H2 N INC NB PA. pose proof STKc as (_ & SLO & SHI & STOP & _).
  assert (Iq : In (PM.sr_qc (PQM.p_src s), PM.CHUNK) (PQM.mparser_own s)) by (unfold PQM.mparser_own, PM.src_own; cbn; auto).
  assert (Iv : In (PQM.p_sb s, PQM.PSZ * 2 ^ PQM.p_sk s) (PQM.mparser_own s)).
  { unfold PQM.mparser_own, PQM.mrest_own, PQM.mvec_own. apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
  assert (Bq := INC _ Iq). assert (Bv := INC _ Iv).
  destruct (BR _ _ Bq) as (Q0 & Q1 & Q4). destruct (BR _ _ Bv) as (V0 & V1 & V4).
  unfold PQM.PSIZE in *.
  assert (AGO : forall a n, op <= a -> a + n <= op + 400 -> L5C.agree_on M M' a n).
  { intros a n X1 X2. apply ag_hi; [lia|lia|]. intros i Hi. apply N. lia. }
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _).
  rewrite <- (PQMF.with_src_id s).
  apply (PQMF.mparser_at_frame segs A vp M M' op ois s (PQM.p_src s)); unfold PQM.PSIZE, PQM.OFF_SRC, PQM.OFF_MAXD, PQM.OFF_TB, PQM.OFF_BB, PQM.OFF_STK.
  - lia.
  - lia.
  - apply PQMF.dkr_agree. apply AGO; lia.
  - apply AGO; lia.
  - apply AGO; lia.
  - unfold PQM.OFF_SRC in SRC. apply (PMF.src_fields_at_agree segs M M'); [lia|lia|lia| unfold hl_ceil in Q4; lia| apply AGO; lia| apply ag_blk; [exact Bq| exact (NB _ _ Iq)]| exact SRC].
  - apply AGO; lia.
  - destruct (PQM.p_tb s) as [n0|c0 n0 p0]; cbn [PQMF.vs_cells fst snd]; apply AGO; lia.
  - intros c n p Et. assert (It : In (p, c) (PQM.mparser_own s)).
    { unfold PQM.mparser_own, PQM.mrest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. rewrite Et. left. reflexivity. }
    apply PQMF.dkr_agree. apply ag_blk; [exact (INC _ It)| exact (NB _ _ It)].
  - apply AGO; lia.
  - intros b n c Eb. assert (Ib : In (b, c) (PQM.mparser_own s)).
    { unfold PQM.mparser_own, PQM.mrest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite Eb. left. reflexivity. }
    apply PQMF.dkr_agree. apply ag_blk; [exact (INC _ Ib)| exact (NB _ _ Ib)].
  - apply AGO; lia.
  - lia.
  - unfold hl_ceil in V4. lia.
  - apply ag_blk; [exact Bv| exact (NB _ _ Iv)].
  - exact PA.
Qed.

(* [comment removed for export] *)
Lemma adaptor_keep oa ov st : sp' <= oa -> oa + PQM.ASIZE <= 2 ^ 64 -> (forall i, oa <= i < oa + PQM.ASIZE -> ~ PMK.inW W' i) ->
  incl (PQM.aown st) LBc -> (forall B m, In (B, m) (PQM.aown st) -> untouched B m) ->
  PQM.adaptor_at segs A T3 T4 vpa M oa ov st -> PQM.adaptor_at segs A T3 T4 vpa M' oa ov st.
Proof.
  intros H1 H2 N INC NB AA. pose proof STKc as (_ & SLO & SHI & STOP & _).
  assert (Il : In (PQM.a_lb st, PQM.LSZ * 2 ^ PQM.a_lk st) (PQM.aown st)) by (unfold PQM.aown, PQM.lvec_own; left; reflexivity).
  assert (Bl := INC _ Il).
  destruct (BR _ _ Bl) as (L0 & L1 & L4).
  unfold PQM.ASIZE in *.
  assert (AGO : forall a n, oa <= a -> a + n <= oa + 96 -> L5C.agree_on M M' a n).
  { intros a n X1 X2. apply ag_hi; [lia|lia|]. intros i Hi. apply N. lia. }
  apply (PQMF.adaptor_at_frame segs A vpa M M' oa ov st); unfold PQM.ASIZE, PQM.AOFF_KEY, PQM.AOFF_KB, PQM.AOFF_LV.
  - lia.
  - lia.
  - apply PQMF.dkr_agree. apply AGO; lia.
  - apply AGO; lia.
  - destruct (PQM.a_key st) as [n0|c0 n0 p0]; cbn [PQMF.vs_cells fst snd]; apply AGO; lia.
  - intros c n p Et. assert (It : In (p, c) (PQM.aown st)) by (unfold PQM.aown; apply in_or_app; right; apply in_or_app; left; rewrite Et; left; reflexivity).
    apply PQMF.dkr_agree. apply ag_blk; [exact (INC _ It)| exact (NB _ _ It)].
  - destruct (PQM.a_kb st) as [n0|c0 n0 p0]; cbn [PQMF.vs_cells fst snd]; apply AGO; lia.
  - intros c n p Et. assert (It : In (p, c) (PQM.aown st)) by (unfold PQM.aown; apply in_or_app; right; apply in_or_app; right; rewrite Et; left; reflexivity).
    apply PQMF.dkr_agree. apply ag_blk; [exact (INC _ It)| exact (NB _ _ It)].
  - apply AGO; lia.
  - lia.
  - unfold hl_ceil in L4. lia.
  - apply ag_blk; [exact Bl| exact (NB _ _ Il)].
  - exact AA.
Qed.

End Along.

(* [comment removed for export] *)
Lemma mparser_more_upd M M' op ois s v :
  PQM.mparser_at segs A T3 T4 vp M op ois s -> 0 <= op -> op + PQM.PSIZE <= 2 ^ 64 ->
  L5C.agree_on M M' op 8 -> L5C.agree_on M M' (op + 9) 391 -> PQMF.dkr M M' (op + 8) 1 -> L5.u8_at segs M' (op + 8) v -> (v = 0 \/ v = 1) ->
  PQMF.dkr M M' (PM.sr_qc (PQM.p_src s)) PM.CHUNK ->
  0 <= PQM.p_sb s -> PQM.p_sb s + PQM.PSZ * 2 ^ PQM.p_sk s <= 2 ^ 64 -> L5C.agree_on M M' (PQM.p_sb s) (PQM.PSZ * 2 ^ PQM.p_sk s) ->
  (forall c n p, PQM.p_tb s = PM.VLong c n p -> PQMF.dkr M M' p c) ->
  (forall b n c, PQM.p_bb s = PQV8.V8Blk b n c -> PQMF.dkr M M' b c) ->
  PQM.mparser_at segs A T3 T4 vp M' op ois (set_more s v).
Proof.
  intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & HMX & _ & TB & BB & STK & M01 & D01 & DP)
         Ho Ho' AG1 AG2 DK V8 Hv DKC Hb Hb' AGS DKT DKB.
  unfold PQM.PSIZE in Ho'.
  assert (AG3 : forall a n, op + 9 <= a -> a + n <= op + 400 -> L5C.agree_on M M' a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG2|lia|lia]).
  assert (DK' : PQMF.dkr M M' op 400).
  { intros i Hi Di. destruct (Z_lt_le_dec i (op + 8)) as [X|X]; [rewrite AG1 by lia; exact Di|].
    destruct (Z_lt_le_dec i (op + 9)) as [Y|Y]; [apply DK; [lia| exact Di]| rewrite AG2 by lia; exact Di]. }
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & AC1 & AC2).
  unfold set_more, PQM.mparser_at. cbn [PQM.p_more PQM.p_done PQM.p_depth PQM.p_src PQM.p_tb PQM.p_tg PQM.p_bb PQM.p_bg PQM.p_sb PQM.p_sk PQM.p_stk].
  unfold PQM.PSIZE, PQM.OFF_SRC, PQM.OFF_MAXD, PQM.OFF_TB, PQM.OFF_BB, PQM.OFF_STK in *.
  split; [apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG1|lia|lia]|lia|lia|exact H0]|].
  split; [apply (PQMF.defined_dkr M M' op 400 DK' D)|]. split; [exact I|].
  split; [exact V8|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H9]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H12]|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H20]|].
  split; [apply (PMF.nullis_at_agree segs A M M'); [lia|lia|apply AG3; lia|exact NI]|].
  split.
  { split; [apply (L5C.u64_at_agree segs M M'); [apply AG3; lia|lia|lia|exact F1]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply AG3; lia|lia|lia|exact F2]|].
    split; [apply (L5C.defined_agree M M'); [apply AG3; lia| exact F3]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply AG3; lia|lia|lia|exact F4]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply AG3; lia|lia|lia|exact F5]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply AG3; lia|lia|lia|exact F6]|].
    split; [apply (L5C.u64_at_agree segs M M'); [apply AG3; lia|lia|lia|exact F7]|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [apply (PQMF.defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG3; lia|lia|lia|exact HMX]|]. split; [exact I|].
  split; [apply (PQMF.vstr_at_keep segs M M'); [lia|lia| |apply (PQMF.dkr_sub M M' op 400); [exact DK'|lia|lia]|exact DKT|exact TB]|].
  { destruct (PQM.p_tb s) as [n0|c0 n0 p0]; cbn [PQMF.vs_cells fst snd]; apply AG3; lia. }
  split; [apply (PQMF.v8_at_keep segs M M'); [lia|lia| apply AG3; lia| exact DKB| exact BB]|].
  split; [apply (PQMF.mvec_at_agree segs M M'); [lia|lia|exact Hb|exact Hb'| apply AG3; lia| exact AGS| exact STK]|].
  split; [exact Hv|]. split; [exact D01| exact DP].
Qed.

End Kit.
End PQMK.

End PnMpKit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.
Module PnRunN.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVis OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNRN.
Import NEM. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition TSRES_ME : credit := (48, 6 * 2 ^ 20).
Definition GS_H : Z := 5.
Definition BEGIN_H : Z := 9.
Definition RI_H : Z := 10.
Definition PARSE_H : Z := 11.

(* [comment removed for export] *)
Definition pot_run (L : heap_layout) (s : PQM.mpst) (st : aest) : credit := PM.credit_add (PQM.pot_mparser L s) (pot_ae L st).

Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AQ : pq_addrs.
Variable E : ne_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation iss_at := (PM.iss_at segs A T3).
Abbreviation mparser_at := (PQM.mparser_at segs A T3 T4 (pa_vp_parser A)).
Abbreviation ae_at := (NEM.ae_at segs A E L T3 T4 (qa_vp_adaptor AQ)).
Abbreviation ec_state := (NEM.ec_state segs A).
Abbreviation err_ok := (PQST.err_ok segs A AQ).
Abbreviation entry := (PMSP.entry A L).
Abbreviation frame_ok := (PMSP.frame_ok A L).
Abbreviation pm_scr := PMSP.pm_scr.
Abbreviation cfg := (@PMSP.cfg segs).
Abbreviation o_p := (PQR.o_p A).
Abbreviation o_a := (PQR.o_a A AQ).
Abbreviation o_v := (PQR.o_v A).
Abbreviation o_is := (PQR.o_is A).
Abbreviation o_ec := (PQR.o_ec A).
(* [comment removed for export] *)
Definition o_sink (fb : Z) : Z := fb + ne_off_sink E.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mrun_pre (M : word -> option byte) (fb : Z) (s : PQM.mpst) (st : aest) (str : PM.vstr) (sm : PM.strm) (e b : bool) (cat n : Z) : Prop :=
  mparser_at M (o_p fb) (o_is fb) s /\ ae_at M (o_a fb) (o_v fb) (o_sink fb) st /\ iss_at M (o_is fb) str sm
  /\ L5.u64_at segs M (o_p fb + qa_off_vref AQ) (o_a fb)
  /\ PMST.base_ok segs A M /\ err_ok M e /\ ec_state M (o_ec fb) b cat
  /\ PQM.mgrow_ok s /\ ae_ok st /\ PQM.cpl s (ae_a st) /\ PQM.acct n s (ae_a st) sm /\ oacct n s st sm
  /\ ebound st /\ (b = false -> bal st).
(* [comment removed for export] *)
Definition mrun_fin (M : word -> option byte) (fb : Z) (s : PQM.mpst) (st : aest) (str : PM.vstr) (sm : PM.strm) (e b : bool) (cat : Z) : Prop :=
  mparser_at M (o_p fb) (o_is fb) s /\ ae_at M (o_a fb) (o_v fb) (o_sink fb) st /\ iss_at M (o_is fb) str sm
  /\ L5.u64_at segs M (o_p fb + qa_off_vref AQ) (o_a fb)
  /\ PMST.base_ok segs A M /\ err_ok M e /\ ec_state M (o_ec fb) b cat
  /\ PQM.mgrow_ok s /\ ae_ok st.
Definition W_mrun (fb : Z) : list L5.range := PQR.W_mrun A AQ fb ++ enc_W (o_v fb) ++ [(o_sink fb, 24)].
Definition mown (s : PQM.mpst) (st : aest) : list (Z * Z) := PQM.mparser_own s ++ aeown st.

Definition mprog := bvmap 5 word -> (word -> option byte) -> PQM.mpst -> PQM.mpst -> aest -> aest -> PM.strm -> PM.strm -> Prop.
Definition mrun_post_d (d : Z) (prog : mprog) (R' : bvmap 5 word) (M' : word -> option byte) (fb : Z) (s s' : PQM.mpst)
           (st st' : aest) (str : PM.vstr) (sm sm' : PM.strm) (e e' b b' : bool) (cat n : Z) : Prop :=
  PMSP.src_step (PQM.p_src s) (PQM.p_src s') sm sm' /\ (e = true -> e' = true) /\ (b = true -> b' = true)
  /\ (   (b' = true /\ mrun_fin M' fb s' st' str sm' e' true cat)
      \/ (b' = false /\ mrun_pre M' fb s' st' str sm' e' false cat n /\ PQR.minv_d d s' /\ prog R' M' s s' st st' sm sm')).

(* [comment removed for export] *)
Definition mrun_spec_d (pc h d : Z) (args : bvmap 5 word -> Z -> PQM.mpst -> aest -> PM.strm -> Z -> Prop) (prog : mprog) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat n : Z) (s : PQM.mpst) (st : aest) (str : PM.vstr) (sm : PM.strm) (e b : bool),
    hi_heap HI (mown s st ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r h -> frame_ok sp fb ->
    args R fb s st sm n ->
    mrun_pre M fb s st str sm e b cat n -> incl (PM.vs_own str) LBX -> PQR.minv_d d s ->
    PMSP.credit_le (PM.credit_add (pot_run L s st) TSRES_ME) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PQM.mpst) (st' : aest)
            (sm' : PM.strm) (e' b' : bool) (cr' : credit),
        regs_preserved R R' ->
        mrun_post_d d prog R' M' fb s s' st st' str sm sm' e e' b b' cat n ->
        L5C.hpres L LBX sp (pm_scr h) (W_mrun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_run L s st) (pot_run L s' st') ->
        model_but_vm model model' -> hi_heap HI (mown s' st' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
Definition mrun_spec (pc h : Z) (args : bvmap 5 word -> Z -> PQM.mpst -> aest -> PM.strm -> Z -> Prop) (prog : mprog) : Prop :=
  mrun_spec_d pc h 0 args prog.

(* [comment removed for export] *)
Definition margs3 (R : bvmap 5 word) (fb : Z) (_ : PQM.mpst) (_ : aest) (_ : PM.strm) (_ : Z) : Prop :=   (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_a fb) /\ getr R 12%bv = Z_to_bv 64 (o_ec fb).
(* [comment removed for export] *)
Definition margs_begin (P : Z -> Prop) (R : bvmap 5 word) (fb : Z) (s : PQM.mpst) (st : aest) (sm : PM.strm) (n : Z) : Prop :=
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_a fb) /\ getr R 13%bv = Z_to_bv 64 (o_ec fb)
  /\ (exists t, P t /\ getr R 12%bv = Z_to_bv 64 t) /\ PQM.acct_d 4 n s (ae_a st) sm /\ oacct_d 8 n s st sm.

(* [comment removed for export] *)
Definition margs_gs (t : Z) (R : bvmap 5 word) (fb : Z) (_ : PQM.mpst) (_ : aest) (_ : PM.strm) (_ : Z) : Prop :=
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 12%bv = Z_to_bv 64 (o_ec fb) /\ getr R 11%bv = Z_to_bv 64 t.
(* [comment removed for export] *)
Definition gs_class (t len gsb : Z) : Prop :=
     (128 <= t <= 159 /\ gsb = 0 /\ 0 <= len <= 15)
  \/ (212 <= t <= 216 /\ gsb = 0 /\ 0 <= len <= 16)
  \/ ((t = 196 \/ t = 199 \/ t = 217) /\ gsb = 1 /\ 0 <= len)
  \/ ((t = 197 \/ t = 200 \/ t = 218 \/ t = 220 \/ t = 222) /\ gsb = 2 /\ 0 <= len)
  \/ ((t = 198 \/ t = 201 \/ t = 219 \/ t = 221 \/ t = 223) /\ gsb = 4 /\ 0 <= len).
(* [comment removed for export] *)
Lemma gs_class_hdr_cont t len gsb : gs_class t len gsb -> (128 <= t <= 159 \/ 220 <= t <= 223) -> hdr_cont len <= 1 + 2 * gsb.
Proof.
  intros C T. pose proof (hdr_cont_le len) as HB. unfold hdr_cont in *.
  destruct C as [C|[C|[C|[C|C]]]]; destruct C as (Ct & Eg & Cl); subst gsb;
  first [ lia
        | replace (len <=? 15) with true by (symmetry; apply Z.leb_le; lia); lia
        | destruct (len <=? 15); [lia|]; replace (len <=? 65535) with true by (symmetry; apply Z.leb_le; lia); lia ].
Qed.

(* [comment removed for export] *)
Definition mprog_item : mprog := fun R' M' s s' st st' sm sm' =>
  PQR.mpush_rel s s' /\ PM.unread (PQM.p_src s') sm' < PM.unread (PQM.p_src s) sm.
Definition mprog_push : mprog := fun R' M' s s' st st' sm sm' =>
  PQR.mpush1 s s' /\ PM.unread (PQM.p_src s') sm' <= PM.unread (PQM.p_src s) sm.
Definition mprog_len (t : Z) : mprog := fun R' M' s s' st st' sm sm' =>
  PQM.p_stk s' = PQM.p_stk s /\ st' = st
  /\ exists len gsb, 0 <= len < 2 ^ 64 /\ getr R' 10%bv = Z_to_bv 64 len /\ gs_class t len gsb
     /\ PM.unread (PQM.p_src s') sm' <= PM.unread (PQM.p_src s) sm - gsb.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gs_post_d (d t : Z) (R' : bvmap 5 word) (M' : word -> option byte) (fb : Z) (s s' : PQM.mpst)
           (st st' : aest) (str : PM.vstr) (sm sm' : PM.strm) (e e' b b' : bool) (cat n : Z) : Prop :=
  PMSP.src_step (PQM.p_src s) (PQM.p_src s') sm sm' /\ (e = true -> e' = true) /\ (b = true -> b' = true)
  /\ (   (b' = true /\ mrun_fin M' fb s' st' str sm' e' true cat /\ PQM.p_more s' = 0)
      \/ (b' = b /\ mrun_pre M' fb s' st' str sm' e' b cat n /\ PQR.minv_d d s' /\ mprog_len t R' M' s s' st st' sm sm')).
Definition gs_spec_d (pc h d : Z) (args : bvmap 5 word -> Z -> PQM.mpst -> aest -> PM.strm -> Z -> Prop) (t : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat n : Z) (s : PQM.mpst) (st : aest) (str : PM.vstr) (sm : PM.strm) (e b : bool),
    hi_heap HI (mown s st ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r h -> frame_ok sp fb ->
    args R fb s st sm n ->
    mrun_pre M fb s st str sm e b cat n -> incl (PM.vs_own str) LBX -> PQR.minv_d d s ->
    PMSP.credit_le (PM.credit_add (pot_run L s st) TSRES_ME) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PQM.mpst) (st' : aest)
            (sm' : PM.strm) (e' b' : bool) (cr' : credit),
        regs_preserved R R' ->
        gs_post_d d t R' M' fb s s' st st' str sm sm' e e' b b' cat n ->
        L5C.hpres L LBX sp (pm_scr h) (W_mrun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_run L s st) (pot_run L s' st') ->
        model_but_vm model model' -> hi_heap HI (mown s' st' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
Definition get_size_spec : Prop :=
  forall d t, 0 <= d <= 1 -> PQR.gs_type t -> gs_spec_d (qa_get_size AQ) GS_H d (margs_gs t) t.
Definition begin_array_spec : Prop := mrun_spec (qa_begin_array AQ) BEGIN_H (margs_begin PQR.ba_type) mprog_push.
Definition begin_object_spec : Prop := mrun_spec (qa_begin_object AQ) BEGIN_H (margs_begin PQR.bo_type) mprog_push.
Definition read_item_spec : Prop := mrun_spec (qa_read_item AQ) RI_H margs3 mprog_item.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition parse_post (M' : word -> option byte) (fb : Z) (s s' : PQM.mpst) (st' : aest) (str : PM.vstr) (sm sm' : PM.strm)
           (e e' b' : bool) (cat : Z) : Prop :=
  mrun_fin M' fb s' st' str sm' e' b' cat /\ PMSP.src_step (PQM.p_src s) (PQM.p_src s') sm sm' /\ (e = true -> e' = true)
  /\ L5.defined M' (o_ec fb) 16.
Definition parse_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat n : Z) (s : PQM.mpst) (st : aest) (str : PM.vstr) (sm : PM.strm) (e : bool),
    hi_heap HI (mown s st ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r PARSE_H -> frame_ok sp fb ->
    margs3 R fb s st sm n ->
    mrun_pre M fb s st str sm e false cat n -> incl (PM.vs_own str) LBX -> PQR.minv s ->
    PMSP.credit_le (PM.credit_add (pot_run L s st) TSRES_ME) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PQM.mpst) (st' : aest)
            (sm' : PM.strm) (e' b' : bool) (cr' : credit),
        regs_preserved R R' ->
        parse_post M' fb s s' st' str sm sm' e e' b' cat ->
        L5C.hpres L LBX sp (pm_scr PARSE_H) (W_mrun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_run L s st) PMSP.cr0 ->
        model_but_vm model model' -> hi_heap HI (mown s' st' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (qa_parse AQ) M model) K.

(* [comment removed for export] *)
Lemma pre_push_glue R M d n s st sm :
  ae_ok st -> ebound st -> PQM.nlv (ae_a st) <= PQM.MAX_DEPTH -> PQM.kbsize (ae_a st) + 2 <= PQM.SMB ->
  oacct_d d n s st sm -> 8 <= d -> 0 <= PM.unread (PQM.p_src s) sm -> 0 <= kbsize st -> PNV.pre_push R M st.
Proof.
  intros AOK EB Hn Hk AC Hd Hu Hkb. unfold PNV.pre_push.
  assert (1 <= nlv st) by (destruct AOK as (((L1 & _) & _ & _) & _ & _); unfold nlv, PQM.nlv; lia).
  pose proof (oacct_val_room d n s st sm AC Hu Hkb ltac:(assumption)). unfold nlv, kbsize in *. repeat split; try assumption; lia.
Qed.
Lemma pre_pop_glue R M n s st sm :
  oacct n s st sm -> 0 <= PM.unread (PQM.p_src s) sm -> 2 <= nlv st -> PQM.kbsize (ae_a st) + 2 <= PQM.SMB -> PNV.pre_pop R M st.
Proof.
  intros AC Hu Hn Hk. unfold PNV.pre_pop. pose proof (oacct_pop_room n s st sm AC Hu Hn). unfold nlv, kbsize in *. repeat split; lia.
Qed.
Lemma pre_val_glue R M dk dphi d n s st sm :
  oacct_d d n s st sm -> dphi <= d -> 0 <= PM.unread (PQM.p_src s) sm -> 0 <= kbsize st -> 1 <= nlv st ->
  PQM.kbsize (ae_a st) + dk <= PQM.SMB -> PNV.pre_val dk dphi R M st.
Proof.
  intros AC Hd Hu Hkb Hn Hk. unfold PNV.pre_val. pose proof (oacct_val_room d n s st sm AC Hu Hkb Hn). unfold kbsize in *. split; lia.
Qed.

(* [comment removed for export] *)
Lemma pre_push_of_inv st : ae_ok st -> ebound st -> PQM.nlv (ae_a st) <= PQM.MAX_DEPTH -> esize st <= MAX_DEPTH /\ edepth st + 1 <= MAX_DEPTH.
Proof. intros AOK EB Hn. split; [exact EB|]. exact (edepth_room st AOK Hn). Qed.
Lemma ebound_after_push st st' (b : bool) :
  ae_ok st' -> (b = false -> bal st) -> b = false ->
  esize st' - edepth st' = esize st - edepth st -> nlv st' <= MAX_DEPTH + 1 -> ebound st'.
Proof.
  intros AOK' BAL Hb EQ Hn. specialize (BAL Hb). unfold bal in BAL.
  assert (B' : bal st') by (unfold bal; lia). exact (ebound_of_bal st' AOK' B' Hn).
Qed.
Lemma ebound_after_pop st st' : ebound st -> esize st' <= esize st -> ebound st'.
Proof. unfold ebound. lia. Qed.
Lemma bal_after_pop st st' (b' : bool) : bal st -> (esize st' - edepth st' = esize st - edepth st \/ b' = true) -> b' = false -> bal st'.
Proof. unfold bal. intros B [EQ|Hb] Hf; [lia|congruence]. Qed.

End Specs.
End PNRN.

End PnRunN.
