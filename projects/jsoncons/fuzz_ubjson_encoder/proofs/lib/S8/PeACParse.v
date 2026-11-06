(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith Zwf List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5CoreSpecsAS8 L5StepARS8 L5CoreBRS8 L5ADetailHRS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PnStatics PmCertKitG PmModelFactsA PmStep PeStepA PmParStep PmParKit PmParKit2 PeASrcKit PeAParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrameA PeACReset1 PmAUarK PmAUarKS PmAUar PeACParseD PeALpP1 PeALpP2 PeALpP3 PeALpP4 PeALpP5.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b2df8_b2dfc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8 UbjRefStepS8 UbjRefLoopS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEACLP.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.

Ltac sya := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation own := PEACLPD.own.
Abbreviation ocell := PEACLPD.ocell.

Lemma credit_le_keep p1 c1 c2 p2 : PMSP.credit_le p1 c1 -> PMSP.credit_keep c1 c2 p1 p2 -> PMSP.credit_le p2 c2.
Proof. unfold PMSP.credit_le, PMSP.credit_keep. lia. Qed.
Lemma credit_keep_trans c1 c2 c3 p1 p2 p3 : PMSP.credit_keep c1 c2 p1 p2 -> PMSP.credit_keep c2 c3 p2 p3 -> PMSP.credit_keep c1 c3 p1 p3.
Proof. unfold PMSP.credit_keep. lia. Qed.

Lemma div8_off F a k : F / 8 * 8 = F -> F + 8 * k <= a < F + 8 * k + 8 -> a / 8 = F / 8 + k.
Proof. intros E H. symmetry. apply (Z.div_unique a 8 (F / 8 + k) (a - F - 8 * k)); lia. Qed.

Lemma frame_ok5_push FF fb f : PECA.frame_ok5 FF fb -> PECA.frame_ok5 (f :: FF) fb.
Proof. intros ((r0 & Hf) & Hm). split; [exists r0; right; exact Hf| exact Hm]. Qed.

Tactic Notation "wr_mem" integer(n) := unfold PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W; cbn [app]; do n right; left; reflexivity.
Ltac wr_rng := unfold L5.in_rng, PMSP.o_vec, PMSP.o_src, PMSP.o_tb, PMSP.o_p, PMSP.o_is, PMSP.o_ec, PMSP.o_v, PESK.o_sink;
  cbn [fst snd pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A].

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMA.ly_as0 L C LY.

Lemma content_keepA' LB FF sp scr W M M' fb p s str sm op :
  L5SAR.ek L ar LB FF sp scr W M M' -> PMKA.wapp W ->
  (forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  PMSPA.aobjA FF (PMSPA.o_is AD fb) 272 -> (forall i, PMSPA.o_is AD fb + 80 <= i < PMSPA.o_is AD fb + 80 + 24 -> L5.outside W i) ->
  incl (PM.vs_own str) LB -> In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB ->
  (forall q c, In (q, c) (PM.vs_own str) -> PMKA.blk_out W q c) -> PMKA.blk_out W (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  PM.iss_at RSEGS AD PMSPA.accA M (PMSPA.o_is AD fb) str sm -> PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op (PMSPA.o_is AD fb) s ->
  PEC.content_ok RSEGS AD M fb p (PM.p_src s) str sm -> PEC.content_ok RSEGS AD M' fb p (PM.p_src s) str sm.
Proof.
  intros EK WAPP FRB BRB AO OW INCS QIN OBS OBQ IA PA.
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). pose proof VS as (_ & _ & VSF).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
  apply (PECFA.content_keepA RSEGS AD L ar LB FF sp scr W M M' EK WAPP FRB BRB fb p s str sm AO OW INCS).
  - intros c n q ->. cbn in VSF. destruct VSF as (_ & _ & _ & Hn & Hc & _ & _ & _). split; [lia|]. apply OBS. cbn. left. reflexivity.
  - intros n ->. cbn in VSF. lia.
  - exact QIN.
  - exact OBQ.
  - exact G1.
  - exact G2.
  - exact G3.
Qed.

Hypothesis RTV : PECSA.rtv_spec L ar HI P.
Hypothesis RDV : PECSA.read_value_spec L ar HI P.
Hypothesis RDK : PECSA.read_key_spec L ar HI P.
Hypothesis EAR : PECSA.end_array_spec L ar HI P.
Hypothesis EOB : PECSA.end_object_spec L ar HI P.
Hypothesis PEEK : PECSA.peek_spec L ar HI.
Hypothesis IGN : PECSA.ignore_spec L ar HI.
Hypothesis MKE : PECSA.make_ec_spec L ar HI.
Hypothesis ANN : PECSA.ann_shrink_spec L ar HI.

Section Upd.
Variables Ma Mb : word -> option byte.
Local Ltac u64x AG H := apply (L5C.u64_at_agree RSEGS Ma Mb); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u32x AG H := apply (PMF.u32_at_agree RSEGS Ma Mb); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u8x AG H := apply (L5C.u8_at_agree RSEGS Ma Mb); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].

Lemma vec_at_set_topA v b kk pre q q' :
  PM.vec_at RSEGS PMSPA.accA PMSPA.annA Ma v b kk (pre ++ [q]) -> 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + 32 * 2 ^ kk <= 2 ^ 64 ->
  L5C.agree_on Ma Mb v 24 -> L5C.agree_on Ma Mb b (32 * Z.of_nat (length pre)) ->
  L5C.agree_on Ma Mb (b + 32 * Z.of_nat (length pre) + 32) (32 * 2 ^ kk - 32 * Z.of_nat (length pre) - 32) ->
  PMFA.agsh Ma Mb b (32 * 2 ^ kk) ->
  L5.defined Mb (b + 32 * Z.of_nat (length pre)) 32 -> PM.pstate_at RSEGS Mb (b + 32 * Z.of_nat (length pre)) q' ->
  PM.vec_at RSEGS PMSPA.accA PMSPA.annA Mb v b kk (pre ++ [q']).
Proof.
  intros (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AN & EL) Hv Hv' Hb Hb' AG0 AGL AGH SH DT PT.
  pose proof (PM.pow2_pos kk ltac:(lia)) as P2.
  unfold PM.vec_at. rewrite !length_app in *. cbn [length] in *. rewrite !Nat2Z.inj_add in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
  split; [u64x AG0 V0|]. split; [u64x AG0 V8|]. split; [u64x AG0 V16|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
  split.
  { intros i Hi. destruct (Z_lt_le_dec i (32 * Z.of_nat (length pre))) as [X|X]; [rewrite AGL by lia; apply DB; lia|].
    destruct (Z_lt_le_dec i (32 * Z.of_nat (length pre) + 32)) as [Y|Y].
    - replace (b + i) with (b + 32 * Z.of_nat (length pre) + (i - 32 * Z.of_nat (length pre))) by lia. apply DT. lia.
    - rewrite AGH by lia. apply DB; lia. }
  split; [apply (PMFA.accA_agree Ma Mb b _); [eapply PMFA.agsh_sub; [exact SH|lia|lia]| exact CB]|].
  split; [apply (PMFA.annA_agree Ma Mb b _ _ (PMFA.mod16_8 b Hal)); [lia| apply PMFA.blk8| exact SH| exact AN]|].
  intros i Hi.
  destruct (Nat.eq_dec i (length pre)) as [->|N]; [rewrite PMPK2.nth_app_at; exact PT|].
  rewrite PMPK2.nth_app_last by (try rewrite length_app; cbn; lia).
  specialize (EL i ltac:(lia)). rewrite PMPK2.nth_app_last in EL by (try rewrite length_app; cbn; lia).
  apply (PMF.pstate_at_agree RSEGS Ma Mb); [lia|lia| |exact EL].
  apply (L5C.agree_on_sub Ma Mb b (32 * Z.of_nat (length pre))); [exact AGL|lia|lia].
Qed.

Lemma parser_top_updA o ois0 s0 pre q q' :
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Ma o ois0 s0 -> PM.p_stk s0 = pre ++ [q] -> 0 <= o -> o + 384 <= 2 ^ 64 -> PMFA.agA Ma Mb o 384 ->
  L5.defined Mb (PM.sr_qc (PM.p_src s0)) PM.CHUNK -> PMFA.agsh Ma Mb (PM.sr_qc (PM.p_src s0)) PM.CHUNK ->
  0 <= PM.p_b s0 -> PM.p_b s0 + 32 * 2 ^ PM.p_k s0 <= 2 ^ 64 ->
  L5C.agree_on Ma Mb (PM.p_b s0) (32 * Z.of_nat (length pre)) ->
  L5C.agree_on Ma Mb (PM.p_b s0 + 32 * Z.of_nat (length pre) + 32) (32 * 2 ^ PM.p_k s0 - 32 * Z.of_nat (length pre) - 32) ->
  PMFA.agsh Ma Mb (PM.p_b s0) (32 * 2 ^ PM.p_k s0) ->
  L5.defined Mb (PM.p_b s0 + 32 * Z.of_nat (length pre)) 32 -> PM.pstate_at RSEGS Mb (PM.p_b s0 + 32 * Z.of_nat (length pre)) q' ->
  (forall c n q0, PM.p_tb s0 = PM.VLong c n q0 -> PMFA.agA Ma Mb q0 c) ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mb o ois0
    (PM.PST (PM.p_more s0) (PM.p_done s0) (PM.p_depth s0) (PM.p_src s0) (PM.p_tb s0) (PM.p_tg s0) (PM.p_b s0) (PM.p_k s0) (pre ++ [q'])).
Proof.
  intros PA ES Ho Ho' [AG SH] DCQ SHQ Hb Hb' AGL AGH SHB DT PT AGT.
  pose proof PA as (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3).
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & CC & C240).
  rewrite ES in VEC.
  assert (U64 : forall a v, o <= a -> a + 8 <= o + 384 -> L5.u64_at RSEGS Ma a v -> L5.u64_at RSEGS Mb a v).
  { intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
  assert (U32 : forall a v, o <= a -> a + 4 <= o + 384 -> L5.u32_at RSEGS Ma a v -> L5.u32_at RSEGS Mb a v).
  { intros a v Ha Hb0 X. apply (PMF.u32_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
  assert (U8 : forall a v, o <= a -> a + 1 <= o + 384 -> L5.u8_at RSEGS Ma a v -> L5.u8_at RSEGS Mb a v).
  { intros a v Ha Hb0 X. apply (L5C.u8_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
  unfold PM.parser_at, PM.src_fields_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  split; [apply U64; [lia|lia|exact H0]|]. split; [apply (L5C.defined_agree Ma Mb o 384 AG D)|].
  split; [apply (PMFA.accA_agree Ma Mb o 24); [intros x Hx; apply SH; lia| exact C24]|].
  split; [apply U8; [lia|lia|exact H8]|]. split; [apply U8; [lia|lia|exact H9]|]. split; [apply U32; [lia|lia|exact H12]|].
  split; [apply U8; [lia|lia|exact H16]|]. split; [apply U32; [lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS AD Ma Mb (o + 32)); [lia|lia| split; [intros i Hi; apply AG; lia| intros x Hx; apply SH; lia]| exact NI]|].
  split.
  { split; [apply U64; [lia|lia|exact F1]|]. split; [apply U64; [lia|lia|exact F2]|].
    split; [intros i Hi; replace (o + 24 + 256 + i) with (o + (280 + i)) by lia; rewrite AG by lia; apply D; lia|].
    split; [apply U64; [lia|lia|exact F4]|]. split; [apply U64; [lia|lia|exact F5]|]. split; [apply U64; [lia|lia|exact F6]|]. split; [apply U64; [lia|lia|exact F7]|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [exact DCQ|].
    split; [apply (PMFA.accA_agree Ma Mb _ _ SHQ CC)|].
    apply (PMFA.accA_agree Ma Mb (o + 24 + 240) 56); [intros x Hx; apply SH; lia| exact C240]. }
  split; [apply U32; [lia|lia|exact H320]|]. split; [apply U64; [lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree Ma Mb (o + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
  split; [apply (PMFA.vstr_at_agreeA RSEGS Ma Mb (o + 336)); [lia|lia| split; [intros i Hi; apply AG; lia| intros x Hx; apply SH; lia]| exact AGT| exact TB]|].
  split; [apply (vec_at_set_topA (o + 360) (PM.p_b s0) (PM.p_k s0) pre q q' VEC); [lia|lia|exact Hb|exact Hb'| intros i Hi; apply AG; lia| exact AGL| exact AGH| exact SHB| exact DT| exact PT]|].
  split; [exact B1|]. split; [exact B2| exact B3].
Qed.
End Upd.

Definition set_md (s0 : PM.pst) (mv dv : Z) : PM.pst :=
  PM.PST mv dv (PM.p_depth s0) (PM.p_src s0) (PM.p_tb s0) (PM.p_tg s0) (PM.p_b s0) (PM.p_k s0) (PM.p_stk s0).
Lemma parser_md_updA (Ma Mb : word -> option byte) o ois0 s0 mv dv :
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Ma o ois0 s0 -> 0 <= o -> o + 384 <= 2 ^ 64 ->
  PMFA.agA Ma Mb o 8 -> PMFA.agA Ma Mb (o + 10) 374 -> PMFA.agsh Ma Mb o 384 -> L5.defined Mb o 384 ->
  L5.u8_at RSEGS Mb (o + 8) mv -> L5.u8_at RSEGS Mb (o + 9) dv -> (mv = 0 \/ mv = 1) -> (dv = 0 \/ dv = 1) ->
  0 <= PM.sr_qc (PM.p_src s0) -> PM.sr_qc (PM.p_src s0) + PM.CHUNK <= 2 ^ 64 -> PMFA.agA Ma Mb (PM.sr_qc (PM.p_src s0)) PM.CHUNK ->
  0 <= PM.p_b s0 -> PM.p_b s0 + 32 * 2 ^ PM.p_k s0 <= 2 ^ 64 -> PMFA.agA Ma Mb (PM.p_b s0) (32 * 2 ^ PM.p_k s0) ->
  (forall c n q0, PM.p_tb s0 = PM.VLong c n q0 -> PMFA.agA Ma Mb q0 c) ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mb o ois0 (set_md s0 mv dv).
Proof.
  intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
         [AG1 _] AG2 SH D' C8 C9 Hmv Hdv Hq Hq' AGQ Hb Hb' AGV AGT.
  pose proof AG2 as [AG2d _].
  unfold set_md, PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG4 : forall a n, o + 10 <= a -> a + n <= o + 384 -> PMFA.agA Ma Mb a n).
  { intros a n X1 X2. split; [eapply (L5C.agree_on_sub Ma Mb); [exact AG2d|lia|lia]| intros x Hx; apply SH; lia]. }
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [exact AG1| lia| lia| exact H0]|].
  split; [exact D'|].
  split; [apply (PMFA.accA_agree Ma Mb o 24); [intros x Hx; apply SH; lia| exact C24]|].
  split; [exact C8|]. split; [exact C9|].
  split; [apply (PMF.u32_at_agree RSEGS Ma Mb); [apply (AG4 (o + 12) 4); lia|lia|lia|exact H12]|].
  split; [apply (L5C.u8_at_agree RSEGS Ma Mb); [apply (AG4 (o + 16) 1); lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree RSEGS Ma Mb); [apply (AG4 (o + 20) 4); lia|lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS AD Ma Mb (o + 32)); [lia|lia| apply AG4; lia| exact NI]|].
  split; [apply (PMFA.src_fields_at_agreeA RSEGS Ma Mb (o + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
  split; [apply (PMF.u32_at_agree RSEGS Ma Mb); [apply (AG4 (o + 320) 4); lia|lia|lia|exact H320]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [apply (AG4 (o + 328) 8); lia|lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree Ma Mb (o + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
  split; [apply (PMFA.vstr_at_agreeA RSEGS Ma Mb (o + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
  split; [apply (PMFA.vec_at_agreeA RSEGS Ma Mb (o + 360)); [lia|lia|exact Hb|exact Hb'| eapply (L5C.agree_on_sub Ma Mb); [exact AG2d|lia|lia]| exact AGV| exact VEC]|].
  split; [exact Hmv|]. split; [exact Hdv| exact B3].
Qed.

Lemma parser_vec_updA (Ma Mb : word -> option byte) o ois0 s0 stk' :
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Ma o ois0 s0 -> 0 <= o -> o + 384 <= 2 ^ 64 ->
  PMFA.agA Ma Mb o 360 -> PMFA.agsh Ma Mb o 384 -> L5.defined Mb o 384 ->
  PM.vec_at RSEGS PMSPA.accA PMSPA.annA Mb (o + 360) (PM.p_b s0) (PM.p_k s0) stk' ->
  0 <= PM.sr_qc (PM.p_src s0) -> PM.sr_qc (PM.p_src s0) + PM.CHUNK <= 2 ^ 64 -> PMFA.agA Ma Mb (PM.sr_qc (PM.p_src s0)) PM.CHUNK ->
  (forall c n q0, PM.p_tb s0 = PM.VLong c n q0 -> PMFA.agA Ma Mb q0 c) ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mb o ois0
    (PM.PST (PM.p_more s0) (PM.p_done s0) (PM.p_depth s0) (PM.p_src s0) (PM.p_tb s0) (PM.p_tg s0) (PM.p_b s0) (PM.p_k s0) stk').
Proof.
  intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
         AG2 SH D' VEC' Hq Hq' AGQ AGT.
  pose proof AG2 as [AG2d _].
  unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG4 : forall a n, o <= a -> a + n <= o + 360 -> PMFA.agA Ma Mb a n).
  { intros a n X1 X2. split; [eapply (L5C.agree_on_sub Ma Mb); [exact AG2d|lia|lia]| intros x Hx; apply SH; lia]. }
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [apply (AG4 o 8); lia| lia| lia| exact H0]|].
  split; [exact D'|].
  split; [apply (PMFA.accA_agree Ma Mb o 24); [intros x Hx; apply SH; lia| exact C24]|].
  split; [apply (L5C.u8_at_agree RSEGS Ma Mb); [apply (AG4 (o + 8) 1); lia|lia|lia|exact H8]|].
  split; [apply (L5C.u8_at_agree RSEGS Ma Mb); [apply (AG4 (o + 9) 1); lia|lia|lia|exact H9]|].
  split; [apply (PMF.u32_at_agree RSEGS Ma Mb); [apply (AG4 (o + 12) 4); lia|lia|lia|exact H12]|].
  split; [apply (L5C.u8_at_agree RSEGS Ma Mb); [apply (AG4 (o + 16) 1); lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree RSEGS Ma Mb); [apply (AG4 (o + 20) 4); lia|lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS AD Ma Mb (o + 32)); [lia|lia| apply AG4; lia| exact NI]|].
  split; [apply (PMFA.src_fields_at_agreeA RSEGS Ma Mb (o + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
  split; [apply (PMF.u32_at_agree RSEGS Ma Mb); [apply (AG4 (o + 320) 4); lia|lia|lia|exact H320]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [apply (AG4 (o + 328) 8); lia|lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree Ma Mb (o + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
  split; [apply (PMFA.vstr_at_agreeA RSEGS Ma Mb (o + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
  split; [exact VEC'|].
  split; [exact B1|]. split; [exact B2| exact B3].
Qed.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
          (cr : credit) (sp r fb cat : Z) (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 10.
Hypothesis FRM : PMSPA.ffroomA 10 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_p AD fb).
Hypothesis A11 : getr R 11%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis A12 : getr R 12%bv = Z_to_bv 64 (PMSPA.o_ec AD fb).
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p UbjRef.init s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis HBN : forall n, PESKA.spa_hb P (s_hi (run n p UbjRef.init)).
Hypothesis CRED : PMSP.credit_le (PECA.pot_allA L ar P s en k) cr.
Hypothesis KONT : PEACLPD.apkont L ar HI P K R M model LBX FF LK Aw cr sp r fb p s str sm en k e.
Let op := PMSPA.o_p AD fb. Let ov := PMSPA.o_v AD fb. Let oec := PMSPA.o_ec AD fb. Let ois := PMSPA.o_is AD fb. Let osk := PESK.o_sink EE fb. Let otb := PMSPA.o_tb AD fb.
Let WR := PEC.W_crun AD EE fb.

Lemma CTX : PEACLPD.apctx L ar HI P K R M model LBX FF LK Aw cr sp r fb cat p s str sm en k e.
Proof.
  split; [exact HH|]. split; [exact AM|]. split; [exact K0|]. split; [exact ENT|]. split; [exact FRM|]. split; [exact FRS|]. split; [exact FOK|].
  split; [exact SP32|]. split; [split; [exact A10| split; [exact A11| exact A12]]|]. split; [exact CPRE|]. split; [exact INCS|]. split; [exact POK|].
  split; [exact HBN|]. split; [exact CRED| exact KONT].
Qed.

Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 10) with 32768 in ASTK, STKSH; change (32768 / 8) with 4096 in STKSH;
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl3 in Rgp; rewrite L5K.rl4 in Rtp;
  pose proof FOK as ((rs & Hfb) & Fal);
  assert (Eop : op = fb + 592) by reflexivity; assert (Eov : ov = fb + 496) by reflexivity; assert (Eoec : oec = fb + 1120) by reflexivity;
  assert (Eois : ois = fb + 96) by reflexivity; assert (Eosk : osk = fb + 432) by reflexivity; assert (Eotb : otb = op + 336) by reflexivity;
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & _);
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6); cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6; change (ff_bytes 5) with 2048 in F1, F2, F3, F4, F5, F6;
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in FSAPP; unfold FS_BYTES in FSCEIL, F1, F2;
  assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n)
    by (intros a' n' H1' H2'; exists (fb, 5, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; lia);
  assert (FB8 : forall j, (fb + 8 * j) mod 8 = 0)
    by (intros j'; pose proof (Z.div_mod fb 2048 ltac:(lia)) as E'; rewrite Fal, Z.add_0_r in E'; rewrite E';
        replace (2048 * (fb / 2048) + 8 * j') with ((256 * (fb / 2048) + j') * 8) by lia; apply Z_mod_mult);
  assert (O8 : op mod 8 = 0) by (rewrite Eop; replace (fb + 592) with (fb + 8 * 74) by lia; apply FB8);
  assert (Q8 : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8);
  assert (I8 : ois mod 8 = 0) by (rewrite Eois; replace (fb + 96) with (fb + 8 * 12) by lia; apply FB8);
  assert (C8m : oec mod 8 = 0) by (rewrite Eoec; replace (fb + 1120) with (fb + 8 * 140) by lia; apply FB8);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model op 384 sp 32768 HH (PMKA.aobj_of_aobjA FF op 384 (AOF op 384 ltac:(lia) ltac:(lia)) O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & _);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ois 272 sp 32768 HH (PMKA.aobj_of_aobjA FF ois 272 (AOF ois 272 ltac:(lia) ltac:(lia)) I8) ltac:(lia) ltac:(reflexivity))
    as ((I1 & I2 & I3 & I4 & I5) & IBIG & _);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model oec 16 sp 32768 HH (PMKA.aobj_of_aobjA FF oec 16 (AOF oec 16 ltac:(lia) ltac:(lia)) C8m) ltac:(lia) ltac:(reflexivity))
    as ((E1' & E2' & E3' & E4' & E5') & EBIG & _);
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH);
  assert (AOP : PMSPA.aobjA FF op 384) by (apply AOF; lia);
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply AOF; lia).

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PEACLPD.aframe L ar HI R M model LBX FF LK Aw cr sp s en k F fl LK2 M2 model2.
Hypothesis APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n ->
  (a + n <= F \/ F + ff_bytes 1 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + ff_bytes 1 / 8 <= a) /\ (a + n <= fl \/ fl + 1 <= a).
Let FF' := (F, 1, sp - 256 + 32) :: FF.

Lemma G' : PMAUK.gctx L ar HI LBX FF LK Aw sp 32768 (sp - 256) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PEC.owned s en k).
Proof. exact G. Qed.

Ltac frame_facts :=
  pose proof G' as Gx; destruct Gx as [_ GSPT GSLO GSHI _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS];
  change (ff_bytes 1) with 128 in GFS2, GFCEIL, GFLC, GFR, GF8, GFBIG, GFLA, GNCF; unfold FS_BYTES in GFS2, GFLP.

Definition WretF (Wx : Z -> Prop) (a : Z) : Prop := ((F <= a < F + ff_bytes 1 \/ F / 8 + SB <= a < F / 8 + SB + ff_bytes 1 / 8) \/ a = fl) \/ Wx a.
Lemma wretF_ek LB6 LK6 cr6 A6 (Mx Mf : word -> option byte) V6 (W : list L5.range) (Wx : Z -> Prop) :
  ri_inv HI LB6 ((F, 1, sp - 256 + 32) :: FF) LK6 cr6 A6 Mx V6 ->
  (forall a, Wx a -> ~ L5.outside W a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ WretF Wx a -> Mf (Z_to_bv 64 a) = Mx (Z_to_bv 64 a)) ->
  L5SAR.ek L ar LB6 FF 0 0 W Mx Mf.
Proof.
  intros HH6 WXin FZ. pose proof G' as Gx. destruct Gx as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB & WF & FSAPP & FSCEIL & _).
  unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL.
  assert (FB8 : (F + ff_bytes 1 - 1) / 8 = F / 8 + ff_bytes 1 / 8 - 1 /\ ff_bytes 1 / 8 * 8 = ff_bytes 1) by (split; [exact (proj1 (proj2 F8)) | exact (proj2 (proj2 F8))]).
  apply (L5SAR.ek_piece L ar LB6 FF 0 0 W Mx Mf (WretF Wx) FZ).
  intros a Ha Hc Ho [Wa|Wa]; [| exact (WXin a Wa Ho)].

  assert (IND : forall BS ST, aclient_g BS ST L ar LB6 FF 0 0 a -> in_block LB6 a \/ (hl_img_lo L <= a < hl_img_hi L) \/ (exists b, In b LB6 /\ BS (fst b) (snd b) a)
                  \/ aclient L ar LBX FF sp 32768 a).
  { intros BS ST Xc. destruct Xc as [Xc|[Xc|[Xc|[Xc|[Xc|[Xc|Xc]]]]]].
    - left; exact Xc.
    - right; right; right. unfold aclient, aclient_g. right; left. split; [exact (proj1 Xc)|]. intros Y. destruct Wa as [[Y1|Y1]|Y1].
      + clear - Y1 FCEIL Xc FR. lia.
      + clear - Y1 FR F8 Xc SPT. unfold SB in *. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D. lia.
      + subst a. clear - FLR Xc. lia.
    - right; left. exact (proj1 Xc).
    - right; right; right. unfold aclient, aclient_g. do 3 right; left. exact Xc.
    - right; right; right. unfold aclient, aclient_g. do 4 right; left. exact Xc.
    - right; right; right. unfold aclient, aclient_g. do 5 right; left. exact Xc.
    - right; right; left. exact Xc. }
  destruct (IND _ _ Hc) as [Xc|[Xc|[Xc|Xc]]].
  -
    destruct Xc as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5. destruct Wa as [[Y|Y]|Y].
    + destruct (FA (F, 1, sp - 256 + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z; clear - Y Z Xb FR; lia.
    + destruct B5 as (_ & B5 & _). clear - Y Xb B5 FR F8. unfold SB in *.
      pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D.
      pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
    + subst a. unfold FS_BYTES in BFS, FLP. clear - Xb BFS FLP. lia.
  - rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Xc. destruct Wa as [[Y|Y]|Y].
    + clear - Xc Y FR; lia.
    + clear - Xc Y FR. unfold SB in *. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
    + subst a. clear - Xc FLR; lia.
  -
    destruct Xc as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
    unfold in_shadow_of, S in Xb. destruct Wa as [[Y|Y]|Y].
    + destruct FBIG as [Z|Z]; unfold SB in Xb.
      * pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Y Z Xb D; lia.
      * pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Y Z Xb D FR; lia.
    + destruct (FA (F, 1, sp - 256 + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z.
      * assert (E1 : (F - 1) / 8 = F / 8 - 1).
        { rewrite <- (proj1 F8) at 1. replace (F / 8 * 8 - 1) with (7 + (F / 8 - 1) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        pose proof (Z.div_le_mono (fst b + snd b - 1) (F - 1) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
        clear - Y Xb D. unfold SB in *. lia.
      * assert (E1 : (F + ff_bytes 1) / 8 = F / 8 + ff_bytes 1 / 8).
        { rewrite <- (proj1 F8) at 1. rewrite <- (proj2 FB8) at 1. replace (F / 8 * 8 + ff_bytes 1 / 8 * 8) with ((F / 8 + ff_bytes 1 / 8) * 8) by lia.
          rewrite Z.div_mul by lia. reflexivity. }
        pose proof (Z.div_le_mono (F + ff_bytes 1) (fst b) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
        clear - Y Xb D FB8. unfold SB in *. lia.
    + subst a. destruct FLBIG as [Z|Z]; unfold SB in Xb.
      * pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Z Xb D; lia.
      * pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Z Xb D; lia.
  - destruct Wa as [[Y|Y]|Y].
    + apply (NCF a); [left; clear - Y FR; lia| exact Xc].
    + apply (NCF a); [right; unfold S; rewrite (proj1 FB8); unfold SB in *; clear - Y; lia| exact Xc].
    + subst a. apply FLNC. apply L5SAR.aclient_cons. eapply L5SAR.aclient_00. exact Xc.
Qed.

Definition amid (fxi : FPState) (Ri : bvmap 5 word) (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit)
           (si : PM.pst) (smi : PM.strm) (eni : PEC.enc) (ki : PESK.sink) (ei : bool) (Xi : st) : Prop :=
  PEACLPD.lregs R Ri sp op oec F
  /\ PEACLPD.lmem L ar HI P R M model LBX FF LK Aw cr sp fb cat p s str sm en k e F Mi mdi LKi Awi Xi si smi eni ki ei cri.

Lemma amid_alinv fxi Ri Mi mdi LKi Awi cri si smi eni ki ei i :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei (run i p UbjRef.init) -> halted (run i p UbjRef.init) = false ->
  PEACLPD.alinv L ar HI P R M model LBX FF LK Aw cr sp fb cat p s str sm en k e F Ri Mi mdi LKi Awi (run i p UbjRef.init) si smi eni ki ei cri.
Proof. intros (LR & LM) HX. split; [exact LR|]. split; [exists i; reflexivity|]. split; [exact HX| exact LM]. Qed.
Lemma alinv_amid (fxi : FPState) Ri Mi mdi LKi Awi cri si smi eni ki ei Xi :
  PEACLPD.alinv L ar HI P R M model LBX FF LK Aw cr sp fb cat p s str sm en k e F Ri Mi mdi LKi Awi Xi si smi eni ki ei cri ->
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Xi /\ (exists i, Xi = run i p UbjRef.init) /\ halted Xi = false.
Proof. intros (LR & EX & HX & LM). split; [split; [exact LR| exact LM]|]. split; [exact EX| exact HX]. Qed.

Lemma cpre_stepC LB sp0 scr0 W Mi Mj Xi si smi eni ki ei Xj sj ej :
  L5SAR.ek L ar LB FF sp0 scr0 W Mi Mj -> PMKA.wapp W ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  incl (PM.vs_own str) LB -> incl (PEC.enc_own eni) LB -> incl (PESK.sink_own ki) LB -> In (PM.sr_qc (PM.p_src si), PM.CHUNK) LB ->
  (forall i, fb + 32 <= i < fb + 2040 -> ~ (op <= i < op + 384) -> ~ (oec <= i < oec + 16) -> L5.outside W i) ->
  (forall q c, In (q, c) (PM.vs_own str) -> PMKA.blk_out W q c) -> (forall q c, In (q, c) (PEC.enc_own eni) -> PMKA.blk_out W q c) ->
  (forall q c, In (q, c) (PESK.sink_own ki) -> PMKA.blk_out W q c) -> PMKA.blk_out W (PM.sr_qc (PM.p_src si)) PM.CHUNK ->
  PM.p_src sj = PM.p_src si -> PM.p_tb sj = PM.p_tb si -> PM.p_tg sj = PM.p_tg si ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mj op ois sj -> PMSTA.base_okA RSEGS AD Mj -> PESTA.err_okA RSEGS AD AAD EE Mj ej ->
  PEC.clink p Xj sj smi eni ki -> PECA.ec_stateA RSEGS AD Mj fb (s_ec Xj) cat -> (s_ec Xj = true -> ej = true) ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PECA.crun_preA RSEGS AD AAD EE L ar P Mj fb p Xj sj str smi eni ki ej cat.
Proof.
  intros EK WAPP BRB SINC EINC KINC QIN OW OBS OBE OBK OBQ ESRC ETB ETG PA' BASE' ERR' CL' ECS' ECI' CP. entry_facts.
  destruct CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (OWo : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op \/ op + 384 <= a) -> (a + n <= oec \/ oec + 16 <= a) -> forall i, a <= i < a + n -> L5.outside W i)
    by (intros a n X1 X2 X3 X4 i Hi; apply OW; clear - X1 X2 X3 X4 Hi; lia).
  split; [exact PA'|].
  split.
  { apply (PMKA.iss_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ois str smi AOI); [exact SINC| apply OWo; clear - Eois Eop Eoec; lia| | exact IA].
    intros c0 n0 p0 E0. apply OBS. unfold PM.vs_own. rewrite E0. left. reflexivity. }
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eov Eop Eoec; lia| exact EINC| | exact EA].
    intros Hp. apply OBE. unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [apply (PMKA.u64_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eop Eoec; lia| exact VREF]|].
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eosk Eop Eoec; lia| exact KINC| | exact SKA].
    intros Hp. apply OBK. unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [exact BASE'|].
  split; [exact ERR'|].
  split; [rewrite ETB, ETG; exact TBOK|].
  split.
  { rewrite ESRC. apply (content_keepA' LB FF sp0 scr0 W Mi Mj fb p si str smi op EK WAPP FRB BRB AOI); [fold ois; apply OWo; clear - Eois Eop Eoec; lia| exact SINC| exact QIN| exact OBS| exact OBQ| exact IA| exact PA| exact CONT]. }
  split; [exact CL'|]. split; [exact ECS'|]. split; [exact ECI'|].
  exact (PMKA.acc_keepA' L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC).
Qed.

Ltac open_amid MID :=
  pose proof MID as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27 & J3 & J4) & LMx); unfold PEACLPD.JT in J20;
  unfold PEACLPD.lmem in LMx; change (PMSPA.pm_scr 10) with 32768 in LMx;
  destruct LMx as (BI & CP & LSP & ST & EIMP & CK);
  pose proof BI as (HHi & AMi & MRTi & INCAi & INCLi & ASTKi & EKbi & DKbi & OWNi & FSHDi);
  pose proof AMi as (Mhi & MIi).

Ltac close_amid LR BI CP LSP ST EIMP CK :=
  split; [exact LR| unfold PEACLPD.lmem; change (PMSPA.pm_scr 10) with 32768;
    split; [exact BI| split; [exact CP| split; [exact LSP| split; [exact ST| split; [exact EIMP| exact CK]]]]]].

Ltac vis_amid BI Hh Mv :=
  let X := fresh "VF" in
  pose proof (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 32768 (sp - 256) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PEC.owned s en k) G'
                WR _ _ _ _ _ _ BI) as X;
  destruct X as ((WSi & ICi & CSBi & CUARi & _) & OWNv & (FDi & FWi & FSWi & FLCi & FLWi) & (FLCci & FLVi & VFi & VSi & VSHi));
  change (ff_bytes 1) with 128 in WSi, FDi, FWi, FSWi, FLCi, VFi, VSHi; change (128 / 8) with 16 in FSWi, VSHi;
  replace (sp - (sp - 256)) with 256 in WSi by (clear; lia); replace (sp - (sp - 256)) with 256 in VSi by (clear; lia); replace (F + 128 - 8) with (F + 120) in FLCi by (clear; lia);
  fold Hh in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi, FLVi, VFi, VSi, VSHi; fold Mv in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi.

Lemma lregs_keep Ri Rj :
  PEACLPD.lregs R Ri sp op oec F -> (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr Rj (reg j) = getr Ri (reg j)) ->
  PEACLPD.lregs R Rj sp op oec F.
Proof.
  intros (J2 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27 & J3 & J4) RR. unfold PEACLPD.lregs.
  rewrite (RR 2%nat) by inl. rewrite (RR 8%nat) by inl. rewrite (RR 9%nat) by inl. rewrite (RR 18%nat) by inl. rewrite (RR 19%nat) by inl.
  rewrite (RR 20%nat) by inl. rewrite (RR 21%nat) by inl. rewrite (RR 22%nat) by inl. rewrite (RR 23%nat) by inl. rewrite (RR 24%nat) by inl.
  rewrite (RR 25%nat) by inl. rewrite (RR 26%nat) by inl. rewrite (RR 27%nat) by inl. rewrite (RR 3%nat) by inl. rewrite (RR 4%nat) by inl.
  repeat split; assumption.
Qed.
Lemma lregs_pres Ri Rj : PEACLPD.lregs R Ri sp op oec F -> regs_preserved Ri Rj -> PEACLPD.lregs R Rj sp op oec F.
Proof. intros LR RP. apply (lregs_keep Ri Rj LR). intros j Hj. exact (L5SAR.cs_of_preserved Ri Rj j RP Hj). Qed.

Lemma vb_neq si eni ki q m :
  NoDup (map fst (PEC.owned si eni ki ++ LBX)) ->
  In (q, m) (PM.vs_own (PM.p_tb si) ++ PEC.enc_own eni ++ PESK.sink_own ki ++ LBX) \/ (q, m) = (PM.sr_qc (PM.p_src si), PM.CHUNK) -> q <> PM.p_b si.
Proof.
  intros ND [Hin|E0].
  - apply not_eq_sym.
    apply (PMASK.fst_neq_appA (PM.src_own (PM.p_src si) ++ PM.vec_own (PM.p_b si) (PM.p_k si)) (PM.vs_own (PM.p_tb si) ++ PEC.enc_own eni ++ PESK.sink_own ki ++ LBX)
             (PM.p_b si) (32 * 2 ^ PM.p_k si) q m); [| apply in_or_app; right; left; reflexivity| exact Hin].
    unfold PEC.owned, PM.parser_own in ND. rewrite <- !app_assoc in ND. rewrite <- !app_assoc. exact ND.
  - injection E0 as E1 E2. subst q m. intros E3. unfold PEC.owned, PM.parser_own, PM.src_own, PM.vec_own in ND. cbn in ND. rewrite E3 in ND.
    inversion ND as [|x l NI _]. apply NI. apply PMASK.elem_of_InA. left. reflexivity.
Qed.

Lemma cpre_keepA sp0 scr0 W Mi Mj Xi si smi eni ki ei (LB := PEC.owned si eni ki ++ LBX) :
  L5SAR.ek L ar LB FF sp0 scr0 W Mi Mj -> PMKA.wapp W ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  (forall i, fb + 32 <= i < fb + 2040 -> L5.outside W i) -> (forall a, a < 6914048 -> L5.outside W a) ->
  (forall q m, In (q, m) LB -> PMKA.blk_out W q m) ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PECA.crun_preA RSEGS AD AAD EE L ar P Mj fb p Xi si str smi eni ki ei cat.
Proof.
  intros EK WAPP BRB OW OI OB CP. entry_facts.
  destruct CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (PINC : incl (PM.parser_own si) LB) by (intros x Hx; unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hx).
  assert (EINC : incl (PEC.enc_own eni) LB) by (intros x Hx; unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own ki) LB) by (intros x Hx; unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx).
  assert (SINC : incl (PM.vs_own str) LB) by (intros x Hx; unfold LB; apply in_or_app; right; exact (INCS x Hx)).
  assert (OWo : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> forall i, a <= i < a + n -> L5.outside W i) by (intros a n X1 X2 i Hi; apply OW; clear - X1 X2 Hi; lia).
  split.
  { apply (PMKA.parser_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB _ _ _ AOP); [exact PINC| apply OWo; clear - Eop; lia| | | | exact PA].
    - apply OB. apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity.
    - apply OB. apply PINC. unfold PM.parser_own, PM.vec_own. right. left. reflexivity.
    - intros c0 n0 p0 E0. apply OB. apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E0. right. right. left. reflexivity. }
  split.
  { apply (PMKA.iss_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ois str smi AOI); [exact SINC| apply OWo; clear - Eois; lia| | exact IA].
    intros c0 n0 p0 E0. apply OB. apply SINC. unfold PM.vs_own. rewrite E0. left. reflexivity. }
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eov; lia| exact EINC| | exact EA].
    intros Hp. apply OB. apply EINC. unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [apply (PMKA.u64_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eop; lia| exact VREF]|].
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eosk; lia| exact KINC| | exact SKA].
    intros Hp. apply OB. apply KINC. unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [change (PMSTA.base_okA RSEGS PMA.AD Mj); apply (PMASK.base_keep L ar C LY LB FF sp0 scr0 W Mi Mj EK); [intros a Ha; apply OI; clear - Ha; lia| exact BASE]|].
  split.
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LB FF sp0 scr0 W Mi Mj EK ei PECSA.addrs_wf_A); [| exact ERR].
    intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OI. clear - DI; lia. }
  split; [exact TBOK|].
  split.
  { apply (content_keepA' LB FF sp0 scr0 W Mi Mj fb p si str smi op EK WAPP FRB BRB AOI); [fold ois; apply OWo; clear - Eois; lia| exact SINC| | | | exact IA| exact PA| exact CONT].
    - apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity.
    - intros q c Hq. apply OB. apply SINC. exact Hq.
    - apply OB. apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity. }
  split; [exact CL|].
  split; [apply (PECFA.ec_state_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB fb (s_ec Xi) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [fold oec; apply OWo; clear - Eoec; lia| exact ECS]|].
  split; [exact ECI|].
  exact (PMKA.acc_keepA' L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC).
Qed.

Lemma cpre_stepA sp0 scr0 W Mi Mj Xi si smi eni ki ei Xj sj ej (LB := PEC.owned si eni ki ++ LBX) :
  L5SAR.ek L ar LB FF sp0 scr0 W Mi Mj -> PMKA.wapp W ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) -> NoDup (map fst LB) ->
  (forall i, fb + 32 <= i < fb + 2040 -> ~ (op <= i < op + 384) -> ~ (oec <= i < oec + 16) -> L5.outside W i) ->
  (forall q m, In (q, m) LB -> q <> PM.p_b si -> PMKA.blk_out W q m) ->
  PM.p_src sj = PM.p_src si -> PM.p_tb sj = PM.p_tb si -> PM.p_tg sj = PM.p_tg si ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mj op ois sj -> PMSTA.base_okA RSEGS AD Mj -> PESTA.err_okA RSEGS AD AAD EE Mj ej ->
  PEC.clink p Xj sj smi eni ki -> PECA.ec_stateA RSEGS AD Mj fb (s_ec Xj) cat -> (s_ec Xj = true -> ej = true) ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PECA.crun_preA RSEGS AD AAD EE L ar P Mj fb p Xj sj str smi eni ki ej cat.
Proof.
  intros EK WAPP BRB NDL OW OB ESRC ETB ETG PA' BASE' ERR' CL' ECS' ECI' CP. entry_facts.
  destruct CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (PINC : incl (PM.parser_own si) LB) by (intros x Hx; unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hx).
  assert (EINC : incl (PEC.enc_own eni) LB) by (intros x Hx; unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own ki) LB) by (intros x Hx; unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx).
  assert (SINC : incl (PM.vs_own str) LB) by (intros x Hx; unfold LB; apply in_or_app; right; exact (INCS x Hx)).
  assert (OWo : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op \/ op + 384 <= a) -> (a + n <= oec \/ oec + 16 <= a) -> forall i, a <= i < a + n -> L5.outside W i)
    by (intros a n X1 X2 X3 X4 i Hi; apply OW; clear - X1 X2 X3 X4 Hi; lia).
  assert (OB2 : forall q m, In (q, m) (PM.vs_own (PM.p_tb si) ++ PEC.enc_own eni ++ PESK.sink_own ki ++ LBX) -> PMKA.blk_out W q m).
  { intros q m Hq. apply OB; [| exact (vb_neq si eni ki q m NDL (or_introl Hq))].
    unfold LB, PEC.owned, PM.parser_own. rewrite <- !app_assoc. apply in_or_app. right. apply in_or_app. right. exact Hq. }
  split; [exact PA'|].
  split.
  { apply (PMKA.iss_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ois str smi AOI); [exact SINC| apply OWo; clear - Eois Eop Eoec; lia| | exact IA].
    intros c0 n0 p0 E0. apply OB2. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply INCS. unfold PM.vs_own. rewrite E0. left. reflexivity. }
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eov Eop Eoec; lia| exact EINC| | exact EA].
    intros Hp. apply OB2. apply in_or_app; right. apply in_or_app; left. unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [apply (PMKA.u64_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eop Eoec; lia| exact VREF]|].
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eosk Eop Eoec; lia| exact KINC| | exact SKA].
    intros Hp. apply OB2. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [exact BASE'|].
  split; [exact ERR'|].
  split; [rewrite ETB, ETG; exact TBOK|].
  split.
  { rewrite ESRC. apply (content_keepA' LB FF sp0 scr0 W Mi Mj fb p si str smi op EK WAPP FRB BRB AOI); [fold ois; apply OWo; clear - Eois Eop Eoec; lia| exact SINC| | | | exact IA| exact PA| exact CONT].
    - apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity.
    - intros q c Hq. apply OB2. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply INCS. exact Hq.
    - apply OB; [apply PINC; unfold PM.parser_own, PM.src_own; left; reflexivity| exact (vb_neq si eni ki _ _ NDL (or_intror eq_refl))]. }
  split; [exact CL'|]. split; [exact ECS'|]. split; [exact ECI'|].
  exact (PMKA.acc_keepA' L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC).
Qed.

Definition PF0 (MVi : word -> option byte) : Prop :=
  0 <= sp < 2 ^ 64
  /\ 0 <= op < 2 ^ 64
  /\ 0 <= ov < 2 ^ 64
  /\ 0 <= oec < 2 ^ 64
  /\ L5.img_clear MVi 65536 1286144
  /\ L5.u64_at RSEGS MVi 1317368 2147450880
  /\ L5.u32_at RSEGS MVi 1317376 1
  /\ 140735332487424 <= sp <= 140737488355328
  /\ sp mod 32 = 0
  /\ L5.writable RSEGS MVi (sp - 256) 256
  /\ 6914048 <= op <= 140737488354944
  /\ op mod 8 = 0
  /\ (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784)
  /\ L5KA.zeros_at MVi ((op / 8) + 2147450880) 3
  /\ L5KA.zeros_at MVi (((op + 32) / 8) + 2147450880) 44
  /\ L5KA.zeros_at MVi (((op + 20) / 8) + 2147450880) 1
  /\ L5.writable RSEGS MVi op 384
  /\ ((sp - 256) + 256 <= op \/ op + 384 <= (sp - 256))
  /\ 6914048 <= ov <= 140737488355320
  /\ ov mod 8 = 0
  /\ (2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784)
  /\ L5KA.zeros_at MVi ((ov / 8) + 2147450880) 1
  /\ L5.writable RSEGS MVi ov 8
  /\ ((sp - 256) + 256 <= ov \/ ov + 8 <= (sp - 256))
  /\ 6914048 <= oec <= 140737488355312
  /\ oec mod 8 = 0
  /\ (2147446784 + 17592186048512 <= oec \/ oec + 16 <= 2147446784)
  /\ L5KA.zeros_at MVi ((oec / 8) + 2147450880) 2
  /\ L5.writable RSEGS MVi oec 16
  /\ ((sp - 256) + 256 <= oec \/ oec + 16 <= (sp - 256))
  /\ L5.u64_at RSEGS MVi ov 1258992
  /\ L5KA.zeros_at MVi 2147608254 16
  /\ (op + 384 <= ov \/ ov + 8 <= op)
  /\ (oec + 16 <= ov \/ ov + 8 <= oec)
  /\ (op + 384 <= oec \/ oec + 16 <= op)
  /\ 0 <= F < 2 ^ 64
  /\ 0 <= fl < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 1))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 8))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 9))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 18))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 19))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 20))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 21))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 22))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 23))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 24))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 25))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 26))) < 2 ^ 64
  /\ 0 <= (bv_unsigned (getr R (reg 27))) < 2 ^ 64
  /\ 6914048 <= F <= 140737488355200
  /\ F mod 32 = 0
  /\ L5.defined MVi F 128
  /\ L5.writable RSEGS MVi F 128
  /\ (2147446784 + 17592186048512 <= F \/ F + 128 <= 2147446784)
  /\ L5.writable RSEGS MVi ((F / 8) + 2147450880) 16
  /\ L5.u64_at RSEGS MVi (F + 120) fl
  /\ 4096 <= fl <= 140737488355327
  /\ L5.writable RSEGS MVi fl 1
  /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784)
  /\ (F + 128 <= fl \/ fl + 1 <= F)
  /\ ((sp - 256) + 256 <= F \/ F + 128 <= (sp - 256))
  /\ ((sp - 256) + 256 <= fl \/ fl + 1 <= (sp - 256))
  /\ (op + 384 <= F \/ F + 128 <= op)
  /\ (op + 384 <= fl \/ fl + 1 <= op)
  /\ (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((op / 8) + 2147450880))
  /\ (oec + 16 <= F \/ F + 128 <= oec)
  /\ (oec + 16 <= fl \/ fl + 1 <= oec)
  /\ (((oec / 8) + 2147450880) + 2 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((oec / 8) + 2147450880))
  /\ (ov + 8 <= F \/ F + 128 <= ov)
  /\ (ov + 8 <= fl \/ fl + 1 <= ov)
  /\ (((ov / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((ov / 8) + 2147450880))
  /\ (F + 128 <= 65536 \/ 65536 + 1196128 <= F)
  /\ (((F / 8) + 2147450880) + 16 <= 2147608254 \/ 2147608254 + 16 <= ((F / 8) + 2147450880))
  /\ L5.u64_at RSEGS MVi (sp - 8) (bv_unsigned (getr R (reg 1)))
  /\ L5.u64_at RSEGS MVi (sp - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS MVi (sp - 24) (bv_unsigned (getr R (reg 9)))
  /\ L5.u64_at RSEGS MVi (sp - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS MVi (sp - 40) (bv_unsigned (getr R (reg 19)))
  /\ L5.u64_at RSEGS MVi (sp - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS MVi (sp - 56) (bv_unsigned (getr R (reg 21)))
  /\ L5.u64_at RSEGS MVi (sp - 64) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS MVi (sp - 72) (bv_unsigned (getr R (reg 23)))
  /\ L5.u64_at RSEGS MVi (sp - 80) (bv_unsigned (getr R (reg 24)))
  /\ L5.u64_at RSEGS MVi (sp - 88) (bv_unsigned (getr R (reg 25)))
  /\ L5.u64_at RSEGS MVi (sp - 96) (bv_unsigned (getr R (reg 26)))
  /\ L5.u64_at RSEGS MVi (sp - 104) (bv_unsigned (getr R (reg 27)))
  /\ L5.u64_at RSEGS MVi (op + 328) 16777216.

Definition PF (MVi : word -> option byte) : Prop :=
  PF0 MVi
  /\ L5.u64_at RSEGS MVi (sp - 144) ov
  /\ L5.u64_at RSEGS MVi (sp - 248) (F + 32)
  /\ L5.u64_at RSEGS MVi (sp - 240) 3
  /\ L5.u64_at RSEGS MVi (sp - 232) 1
  /\ L5.u64_at RSEGS MVi (sp - 224) 0
  /\ L5.u64_at RSEGS MVi (sp - 216) (((op + 328) / 8) + 2147450880)
  /\ L5.u64_at RSEGS MVi (sp - 208) (op + 328)
  /\ L5.u64_at RSEGS MVi (sp - 200) ((ov / 8) + 2147450880)
  /\ L5.u64_at RSEGS MVi (sp - 192) (((op + 360) / 8) + 2147450880)
  /\ L5.u64_at RSEGS MVi (sp - 184) (op + 360)
  /\ L5.u64_at RSEGS MVi (sp - 176) F
  /\ L5.u64_at RSEGS MVi (sp - 168) (op + 24)
  /\ L5.u64_at RSEGS MVi (sp - 160) F
  /\ L5.u64_at RSEGS MVi (sp - 152) ((oec / 8) + 2147450880)
  /\ L5.u64_at RSEGS MVi (sp - 136) (((op + 8) / 8) + 2147450880)
  /\ L5.u64_at RSEGS MVi (sp - 112) F.
Lemma pfacts_bc0 Mi mdi LKi cri Awi si smi eni ki ei Xi :
  PMAUK.binv L ar HI M model LBX FF LK Aw sp 32768 (sp - 256) (own sp R) F 1 WR (PEC.owned si eni ki) Mi mdi LKi cri Awi ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat ->
  PF0 (mrestrict (ahid Awi mdi) Mi).
Proof.
  intros BI CP. unfold PF0.
  entry_facts. frame_facts. pose proof BI as (HHi & AMi & MRTi & INCAi & INCLi & ASTKi & EKbi & DKbi & OWNi & FSHDi). pose proof AMi as (Mhi & MIi).
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi. unfold SB in FSWi.
  assert (BASEi : PMSTA.base_okA RSEGS PMA.AD Mi) by exact BASE.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LKi cri Awi Mi mdi HHi BASEi) as (IC0 & CSBv & CUARv). fold Hi in IC0, CSBv, CUARv. fold MVi in IC0, CSBv, CUARv.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 1, sp - 256 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold Hi in Zop, Z32, Z20, OWR, OVIS. fold MVi in Zop, Z32, Z20, OWR. fold op in Zop, Z32, Z20, OWR, OVIS.
  assert (ECX : exists v c, PMSPA.ec_at RSEGS Mi oec v c).
  { pose proof ECS as E0. unfold PECA.ec_stateA in E0. fold oec in E0.
    lazymatch type of E0 with (if ?c then _ else _) => destruct c; [destruct E0 as (v0 & _ & E1); exists v0; eexists; exact E1| exists 0, cat; exact E0] end. }
  destruct ECX as (ecv & ecc & ECat).
  pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb ecv ecc HHi FOK' ECat) as ((_ & _ & _) & ZE & EW & _ & EU & _ & _). fold Hi in ZE, EW, EU. fold MVi in ZE, EW, EU. fold oec in ZE, EW, EU.
  pose proof EA as (EVT & _ & _ & _ & _ & _ & _ & _ & EACC & _).
  pose proof (PMAPAR.ov_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb HHi FOK' (conj EVT (L5CBR.aacc_sub Mi ov 56 ov 8 EACC ltac:(clear; lia) ltac:(clear; lia))))
    as ((V1 & V8 & VBIG) & ZV & VW & V3 & VVT & _ & _). fold Hi in ZV, VW, VVT. fold MVi in ZV, VW, VVT. fold ov in V1, V8, VBIG, ZV, VW, V3, VVT.
  pose proof OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  assert (Q0f : 0 <= F < 2 ^ 64) by (clear - GF1 GF2; lia). assert (Q0g : 0 <= fl < 2 ^ 64) by (clear - GL1 GL2; lia).
  assert (Q0a : 0 <= sp < 2 ^ 64) by (clear - GSLO GSHI GSPT; lia). assert (Q0b : 0 <= op < 2 ^ 64) by (clear - O1 O3; lia).
  assert (Q0c : 0 <= ov < 2 ^ 64) by (clear - V1; lia). assert (Q0d : 0 <= oec < 2 ^ 64) by (clear - O1 O3 Eop Eoec; lia).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 27))) as B27.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27.

  assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF 0 0 (a + i)).
  { intros a n X1 X2 X3 i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - X1 X2 Hi'; lia| intros Y'; clear - X1 X2 Hi' Y'; lia]. }
  assert (CLsh : forall a n, fb / 8 + SB <= a -> a + n <= fb / 8 + SB + 256 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF 0 0 (a + i)).
  { intros a n X1 X2 X3 i Hi'. unfold aclient, aclient_g. do 5 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. unfold in_shadow_of, S. unfold SB in X1, X2 |- *.
    assert (D1 : (fb + 2048 - 1) / 8 = fb / 8 + 255).
    { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
      replace (2048 * (fb / 2048) + 2048 - 1) with (7 + (256 * (fb / 2048) + 255) * 8) by (clear; lia). rewrite Z.div_add by lia.
      replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
    rewrite D1. clear - X1 X2 Hi'. lia. }
  assert (SH8 : forall j : Z, (fb + 8 * j) / 8 + SB = fb / 8 + SB + j).
  { intros j. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 8 * j) with ((256 * (fb / 2048) + j) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  destruct (APART op 384 0 0 (CLfb op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (ApF & ApSF & ApFL).
  destruct (APART oec 16 0 0 (CLfb oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AeF & AeSF & AeFL).
  destruct (APART ov 56 0 0 (CLfb ov 56 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AvF & AvSF & AvFL).
  destruct (APART (op / 8 + SB) 48 0 0 (CLsh (op / 8 + SB) 48 ltac:(rewrite Eop; replace (fb + 592) with (fb + 8 * 74) by (clear; lia); rewrite (SH8 74); clear; lia)
             ltac:(rewrite Eop; replace (fb + 592) with (fb + 8 * 74) by (clear; lia); rewrite (SH8 74); clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsopSF & _).
  destruct (APART (oec / 8 + SB) 2 0 0 (CLsh (oec / 8 + SB) 2 ltac:(rewrite Eoec; replace (fb + 1120) with (fb + 8 * 140) by (clear; lia); rewrite (SH8 140); clear; lia)
             ltac:(rewrite Eoec; replace (fb + 1120) with (fb + 8 * 140) by (clear; lia); rewrite (SH8 140); clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AseSF & _).
  destruct (APART (ov / 8 + SB) 1 0 0 (CLsh (ov / 8 + SB) 1 ltac:(rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by (clear; lia); rewrite (SH8 62); clear; lia)
             ltac:(rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by (clear; lia); rewrite (SH8 62); clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsvSF & _).
  change (ff_bytes 1) with 128 in ApF, ApSF, ApFL, AeF, AeSF, AeFL, AvF, AvSF, AvFL, AsopSF, AseSF, AsvSF.
  change (128 / 8) with 16 in ApSF, AeSF, AvSF, AsopSF, AseSF, AsvSF. unfold SB in ApSF, AeSF, AvSF, AsopSF, AseSF, AsvSF.

  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P328 & _).
  assert (P328v : L5.u64_at RSEGS MVi (op + 328) 16777216)
    by (apply (proj2 (L5A.u64_at_vis Hi Mi (op + 328) 16777216 (OVIS (op + 328) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))); exact P328).
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LKi cri Awi Mi mdi 0x1335f0 16 HHi ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)) as VT1.
  change (0x1335f0 / 8 + 2147450880) with 2147608254 in VT1. fold Hi in VT1. fold MVi in VT1.

  let cl := first [ sya
      | clear - GSLO GSHI GSPT; lia | clear - O1 O3; lia | clear - O2 GSLO; lia | clear - E1' E3'; lia | clear - E2' GSLO; lia
      | clear - V1; lia | clear - V3 GSLO; lia | clear - Eop Eoec Eov; lia
      | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GFLA; lia | clear - GFBIG; lia | clear - GFLBIG; lia | clear - GF32; lia | clear - GF8; lia
      | clear - ApF; lia | clear - ApFL; lia | clear - AsopSF; lia | clear - AeF; lia | clear - AeFL; lia | clear - AseSF; lia
      | clear - AvF; lia | clear - AvFL; lia | clear - AsvSF; lia
      | clear - O8; lia | clear - Q8; lia | clear - C8m; lia | clear - V8; lia | clear - OBIG; lia | clear - EBIG; lia | clear - VBIG; lia | clear - SP32; lia
      | match goal with |- ?G => fail 100 "pfacts: cannot prove" G end ] in
  do 87 (split; [cl|]); cl.
Qed.
Lemma pfacts fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> PF (mrestrict (ahid Awi mdi) Mi).
Proof.
  intros MID. entry_facts. frame_facts. open_amid MID. unfold PF. split; [exact (pfacts_bc0 _ _ _ _ _ _ _ _ _ _ _ BI CP)|].
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *. vis_amid BI Hi MVi.

  pose proof LSP as (Y248 & Y240 & Y232 & Y224 & Y216 & Y208 & Y200 & Y192 & Y184 & Y176 & Y168 & Y160 & Y152 & Y144 & Y136 & Y112).
  fold op in Y216, Y208, Y192, Y184, Y168, Y136. fold ov in Y200, Y144. fold oec in Y152.
  assert (SPV : forall a v, sp - 256 <= a -> a + 8 <= sp -> L5.u64_at RSEGS Mi a v -> L5.u64_at RSEGS MVi a v).
  { intros a v Ha1 Ha2 X'. apply (proj2 (L5A.u64_at_vis Hi Mi a v (L5A.avis_sub Hi (sp - 256) 256 a 8 VSi Ha1 ltac:(clear - Ha2; lia)) ltac:(clear - Ha1 GSLO GSPT; lia) ltac:(clear - Ha2 GSHI GSPT; lia))). exact X'. }
  pose proof (SPV (sp - 248) (F + 32) ltac:(clear; lia) ltac:(clear; lia) Y248) as Y248v. pose proof (SPV (sp - 240) 3 ltac:(clear; lia) ltac:(clear; lia) Y240) as Y240v.
  pose proof (SPV (sp - 232) 1 ltac:(clear; lia) ltac:(clear; lia) Y232) as Y232v. pose proof (SPV (sp - 224) 0 ltac:(clear; lia) ltac:(clear; lia) Y224) as Y224v.
  pose proof (SPV (sp - 216) ((op + 328) / 8 + 2147450880) ltac:(clear; lia) ltac:(clear; lia) Y216) as Y216v. pose proof (SPV (sp - 208) (op + 328) ltac:(clear; lia) ltac:(clear; lia) Y208) as Y208v.
  pose proof (SPV (sp - 200) (ov / 8 + 2147450880) ltac:(clear; lia) ltac:(clear; lia) Y200) as Y200v. pose proof (SPV (sp - 192) ((op + 360) / 8 + 2147450880) ltac:(clear; lia) ltac:(clear; lia) Y192) as Y192v.
  pose proof (SPV (sp - 184) (op + 360) ltac:(clear; lia) ltac:(clear; lia) Y184) as Y184v. pose proof (SPV (sp - 176) F ltac:(clear; lia) ltac:(clear; lia) Y176) as Y176v.
  pose proof (SPV (sp - 168) (op + 24) ltac:(clear; lia) ltac:(clear; lia) Y168) as Y168v. pose proof (SPV (sp - 160) F ltac:(clear; lia) ltac:(clear; lia) Y160) as Y160v.
  pose proof (SPV (sp - 152) (oec / 8 + 2147450880) ltac:(clear; lia) ltac:(clear; lia) Y152) as Y152v. pose proof (SPV (sp - 144) ov ltac:(clear; lia) ltac:(clear; lia) Y144) as Y144v.
  pose proof (SPV (sp - 136) ((op + 8) / 8 + 2147450880) ltac:(clear; lia) ltac:(clear; lia) Y136) as Y136v. pose proof (SPV (sp - 112) F ltac:(clear; lia) ltac:(clear; lia) Y112) as Y112v.
  let cl := first [ sya | match goal with |- ?G => fail 100 "pfacts(spills): cannot prove" G end ] in
  do 15 (split; [cl|]); cl.
Qed.

Ltac open_vf0 H := unfold PF0 in H; destruct H as (VF1 & VF2 & VF3 & VF4 & VF5 & VF6 & VF7 & VF8 & VF9 & VF10 & VF11 & VF12 & VF13 & VF14 & VF15 & VF16 & VF17 & VF18 & VF19 & VF20 & VF21 & VF22 & VF23 & VF24 & VF25 & VF26 & VF27 & VF28 & VF29 & VF30 & VF31 & VF32 & VF33 & VF34 & VF35 & VF36 & VF37 & VF38 & VF39 & VF40 & VF41 & VF42 & VF43 & VF44 & VF45 & VF46 & VF47 & VF48 & VF49 & VF50 & VF51 & VF52 & VF53 & VF54 & VF55 & VF56 & VF57 & VF58 & VF59 & VF60 & VF61 & VF62 & VF63 & VF64 & VF65 & VF66 & VF67 & VF68 & VF69 & VF70 & VF71 & VF72 & VF73 & VF74 & VF75 & VF76 & VF77 & VF78 & VF79 & VF80 & VF81 & VF82 & VF83 & VF84 & VF85 & VF86 & VF87 & VF88).
Ltac open_vf H := let X := fresh "VFS" in unfold PF in H; destruct H as (H & X); open_vf0 H; destruct X as (VS1 & VS2 & VS3 & VS4 & VS5 & VS6 & VS7 & VS8 & VS9 & VS10 & VS11 & VS12 & VS13 & VS14 & VS15 & VS16).

Lemma pfacts_keep (Ma Mb : word -> option byte) : PF Ma -> mem_grows Ma Mb -> 6914048 <= fl ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 10) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 16) -> ~ (fl <= i < fl + 1) ->
      Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)) -> PF Mb.
Proof.
  intros VF MG FL6 AG. unfold PF, PF0 in VF |- *. destruct VF as (VF & VFS). destruct VF as (VF1 & VF2 & VF3 & VF4 & VF5 & VF6 & VF7 & VF8 & VF9 & VF10 & VF11 & VF12 & VF13 & VF14 & VF15 & VF16 & VF17 & VF18 & VF19 & VF20 & VF21 & VF22 & VF23 & VF24 & VF25 & VF26 & VF27 & VF28 & VF29 & VF30 & VF31 & VF32 & VF33 & VF34 & VF35 & VF36 & VF37 & VF38 & VF39 & VF40 & VF41 & VF42 & VF43 & VF44 & VF45 & VF46 & VF47 & VF48 & VF49 & VF50 & VF51 & VF52 & VF53 & VF54 & VF55 & VF56 & VF57 & VF58 & VF59 & VF60 & VF61 & VF62 & VF63 & VF64 & VF65 & VF66 & VF67 & VF68 & VF69 & VF70 & VF71 & VF72 & VF73 & VF74 & VF75 & VF76 & VF77 & VF78 & VF79 & VF80 & VF81 & VF82 & VF83 & VF84 & VF85 & VF86 & VF87 & VF88). destruct VFS as (VS1 & VS2 & VS3 & VS4 & VS5 & VS6 & VS7 & VS8 & VS9 & VS10 & VS11 & VS12 & VS13 & VS14 & VS15 & VS16).
  split.
  { split; [exact VF1|].
    split; [exact VF2|].
    split; [exact VF3|].
    split; [exact VF4|].
    split; [intros i Hi; rewrite AG; [apply VF5; exact Hi| clear - Hi; lia| clear - Hi VF51 VF11 VF58 VF74 VF55 VF13 VF60 FL6; lia| clear - Hi VF51 VF11 VF58 VF74 VF55 VF13 VF60 FL6; lia| clear - Hi VF51 VF11 VF58 VF74 VF55 VF13 VF60 FL6; lia| clear - Hi VF51 VF11 VF58 VF74 VF55 VF13 VF60 FL6; lia]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF51 VF11 VF58 VF74 VF55 VF13 VF60 FL6; lia| clear - VF51 VF11 VF58 VF74 VF55 VF13 VF60 FL6; lia| clear - VF51 VF11 VF58 VF74 VF55 VF13 VF60 FL6; lia| exact VF6]|].
    split; [apply (PMF.u32_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF51 VF11 VF58 VF74 VF55 VF13 VF60 FL6; lia| clear - VF51 VF11 VF58 VF74 VF55 VF13 VF60 FL6; lia| clear - VF51 VF11 VF58 VF74 VF55 VF13 VF60 FL6; lia| exact VF7]|].
    split; [exact VF8|].
    split; [exact VF9|].
    split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF10)|].
    split; [exact VF11|].
    split; [exact VF12|].
    split; [exact VF13|].
    split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF11 VF64 VF65 VF66 VF13 VF51 VF55 VF58 VF60 FL6; lia| exact VF14]|].
    split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF11 VF64 VF65 VF66 VF13 VF51 VF55 VF58 VF60 FL6; lia| exact VF15]|].
    split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF11 VF64 VF65 VF66 VF13 VF51 VF55 VF58 VF60 FL6; lia| exact VF16]|].
    split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF17)|].
    split; [exact VF18|].
    split; [exact VF19|].
    split; [exact VF20|].
    split; [exact VF21|].
    split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF19 VF70 VF71 VF72 VF21 VF51 VF55 VF58 VF60 VF11 VF13 VF33 FL6; lia| exact VF22]|].
    split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF23)|].
    split; [exact VF24|].
    split; [exact VF25|].
    split; [exact VF26|].
    split; [exact VF27|].
    split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF25 VF67 VF68 VF69 VF27 VF51 VF55 VF58 VF60 VF11 VF13 VF35 FL6; lia| exact VF28]|].
    split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF29)|].
    split; [exact VF30|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF19 VF70 VF71 VF72 VF21 VF51 VF55 VF58 VF60 VF11 VF13 VF33 FL6; lia| clear - VF19 VF70 VF71 VF72 VF21 VF51 VF55 VF58 VF60 VF11 VF13 VF33 FL6; lia| clear - VF19 VF70 VF71 VF72 VF21 VF51 VF55 VF58 VF60 VF11 VF13 VF33 FL6; lia| exact VF31]|].
    split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF51 VF11 VF58 VF74 VF55 VF13 VF60 FL6; lia| exact VF32]|].
    split; [exact VF33|].
    split; [exact VF34|].
    split; [exact VF35|].
    split; [exact VF36|].
    split; [exact VF37|].
    split; [exact VF38|].
    split; [exact VF39|].
    split; [exact VF40|].
    split; [exact VF41|].
    split; [exact VF42|].
    split; [exact VF43|].
    split; [exact VF44|].
    split; [exact VF45|].
    split; [exact VF46|].
    split; [exact VF47|].
    split; [exact VF48|].
    split; [exact VF49|].
    split; [exact VF50|].
    split; [exact VF51|].
    split; [exact VF52|].
    split; [exact (L5.defined_grows Ma Mb _ _ MG VF53)|].
    split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF54)|].
    split; [exact VF55|].
    split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF56)|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF51 VF55 VF64 VF61 VF58 VF11 VF13 VF60 FL6; lia| clear - VF51 VF55 VF64 VF61 VF58 VF11 VF13 VF60 FL6; lia| clear - VF51 VF55 VF64 VF61 VF58 VF11 VF13 VF60 FL6; lia| exact VF57]|].
    split; [exact VF58|].
    split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF59)|].
    split; [exact VF60|].
    split; [exact VF61|].
    split; [exact VF62|].
    split; [exact VF63|].
    split; [exact VF64|].
    split; [exact VF65|].
    split; [exact VF66|].
    split; [exact VF67|].
    split; [exact VF68|].
    split; [exact VF69|].
    split; [exact VF70|].
    split; [exact VF71|].
    split; [exact VF72|].
    split; [exact VF73|].
    split; [exact VF74|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF75]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF76]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF77]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF78]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF79]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF80]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF81]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF82]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF83]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF84]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF85]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF86]|].
    split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VF87]|].
    apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF11 VF64 VF65 VF66 VF13 VF51 VF55 VF58 VF60 FL6; lia| clear - VF11 VF64 VF65 VF66 VF13 VF51 VF55 VF58 VF60 FL6; lia| clear - VF11 VF64 VF65 VF66 VF13 VF51 VF55 VF58 VF60 FL6; lia| exact VF88]. }
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS1]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS2]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS3]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS4]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS5]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS6]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS7]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS8]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS9]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS10]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS11]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS12]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS13]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS14]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS15]|].
  apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| clear - VF8 VF18 VF62 VF63 VF51 VF11 VF58 FL6; lia| exact VS16].
Qed.

Definition VALU (T i y d b v : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 39%nat => i | 47%nat => F | 48%nat => fl | 53%nat => y | 54%nat => d | 55%nat => b | 56%nat => v
  | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18))
  | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22))
  | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26))
  | 76%nat => bv_unsigned (getr R (reg 27)) | _ => 0
  end.

Ltac piece_ctx MID :=
  open_amid MID;
  let X := fresh "VF" in
  pose proof (pfacts _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as X; cbv zeta in X;
  lazymatch type of MID with amid _ _ ?Mi ?mdi _ ?Awi _ _ _ _ _ _ _ =>
    set (Hi := ahid Awi mdi) in *; set (MVi := mrestrict Hi Mi) in * end;
  open_vf X.

Ltac fcl := first [sya | unfold PEALPP1.aligned; sya | unfold PEALPP2.aligned; sya | unfold PEALPP3.aligned; sya | unfold PEALPP4.aligned; sya | unfold PEALPP5.aligned; sya].

Tactic Notation "pz" constr(conc) constr(fxi) constr(Ri) constr(T) constr(i) constr(y) constr(d) constr(b) constr(v) "as" ident(P) :=
  let mv := lazymatch goal with m := mrestrict _ _ |- _ => m end in
  pose proof (conc fxi Ri mv (VALU T i y d b v)) as P; unfold VALU in P; cbn beta iota in P.

Tactic Notation "keep_only" ne_hyp_list(l) :=
  clear - LY HIok ICok ILY PO LYa RTV RDV RDK EAR EOB PEEK IGN MKE ANN PMODE HH AM K0 ENT FRM FRS FOK SP32 A10 A11 A12 CPRE INCS POK HBN CRED KONT
          op ov oec ois osk otb WR G APART FF' l.

Lemma ec_vis0 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_ec Y = false -> L5.u32_at RSEGS (mrestrict (ahid Awi mdi) Mi) oec 0.
Proof.
  intros MID EC. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 1, sp - 256 + 32) FOK).
  unfold PECA.ec_stateA in ECS. rewrite EC in ECS. fold oec in ECS.
  pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb 0 cat HHi FOK' ECS) as ((_ & _ & _) & _ & _ & _ & EU & _ & _). exact EU.
Qed.
Lemma ec_vis1 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_ec Y = true ->
  exists v, 1 <= v <= 64 /\ L5.u32_at RSEGS (mrestrict (ahid Awi mdi) Mi) oec v.
Proof.
  intros MID EC. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 1, sp - 256 + 32) FOK).
  unfold PECA.ec_stateA in ECS. rewrite EC in ECS. fold oec in ECS. destruct ECS as (v & Hv & ECS).
  pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb v _ HHi FOK' ECS) as ((_ & _ & _) & _ & _ & _ & EU & _ & _). exists v. split; [exact Hv| exact EU].
Qed.

Lemma md_vis fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  L5.u8_at RSEGS (mrestrict (ahid Awi mdi) Mi) (op + 8) (PM.p_more si) /\ L5.u8_at RSEGS (mrestrict (ahid Awi mdi) Mi) (op + 9) (PM.p_done si)
  /\ PM.p_more si = PEC.b2z (s_more Y) /\ PM.p_done si = PEC.b2z (s_done Y).
Proof.
  intros MID. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 1, sp - 256 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & _ & _ & _ & _ & _ & OVIS & _ & _).
  pose proof PA as (_ & _ & _ & P8 & P9 & _). pose proof CL as (Lmore & Ldone & _).
  split; [| split; [| split; [exact Lmore| exact Ldone]]].
  - apply (proj2 (L5A.u8_at_vis _ Mi (op + 8) _ (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). exact P8.
  - apply (proj2 (L5A.u8_at_vis _ Mi (op + 9) _ (OVIS (op + 9) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). exact P9.
Qed.

Lemma amid_relink fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y Y' :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> PEC.clink p Y' si smi eni ki -> s_ec Y' = s_ec Y ->
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y'.
Proof.
  intros MID CL' EC'. pose proof MID as (LR & _). open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (CP' : PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Y' si str smi eni ki ei cat).
  { split; [exact PA|]. split; [exact IA|]. split; [exact EA|]. split; [exact VREF|]. split; [exact SKA|]. split; [exact BASE|]. split; [exact ERR|].
    split; [exact TBOK|]. split; [exact CONT|]. split; [exact CL'|]. unfold PECA.ec_stateA in ECS |- *. rewrite EC'. split; [exact ECS|]. split; [exact ECI| exact ACC]. }
  close_amid LR BI CP' LSP ST EIMP CK.
Qed.

Lemma amid_regs fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fx' : FPState) R' md' :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg j) = getr Ri (reg j)) ->
  ri_inv HI (PEC.owned si eni ki ++ LBX) FF' LKi cri Awi Mi (vml_of md') -> L5CA.amodel_ok Awi md' -> model_rt mdi md' ->
  amid fx' R' Mi md' LKi Awi cri si smi eni ki ei Y.
Proof.
  intros MID RR HH' AM' MRT'. pose proof MID as (LR & _). open_amid MID.
  pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 32768 (sp - 256) (own sp R) F 1 WR (PEC.owned si eni ki) Mi mdi LKi cri Awi md' BI HH' AM' MRT') as BI'.
  pose proof (lregs_keep Ri R' LR RR) as LR'.
  close_amid LR' BI' CP LSP ST EIMP CK.
Qed.

Lemma amid_ro fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fxj : FPState) Rj (pci pcj : Z) Mjv :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fxj Rj (Z_to_bv 64 pcj) Mjv (seg_rom RSEGS)) ->
  (forall a, 0 <= a < 2 ^ 64 -> Mjv (Z_to_bv 64 a) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 a)) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr Rj (reg j) = getr Ri (reg j)) ->
  (forall mdj, ahid Awi mdj = ahid Awi mdi -> amid fxj Rj Mi mdj LKi Awi cri si smi eni ki ei Y -> srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxj) RSEGS Rj pcj Mi mdj) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID MS FZ RR KONT'. open_amid MID.
  assert (Ej : Mjv = mrestrict (ahid Awi mdi) Mi) by (apply L5SAR.mem_eq_of_agree; exact FZ). subst Mjv.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fxj Ri pci Rj pcj (mrestrict (ahid Awi mdi) Mi) K HHi AMi MS (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros Mj mdj HHj AMj MRTj HIDj VISj MGMj FRj.
  assert (Ej : Mj = Mi) by (apply L5SAR.mem_eq_of_agree; exact FRj). subst Mj.
  apply (KONT' mdj HIDj). exact (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fxj Rj mdj MID RR HHj AMj MRTj).
Qed.

Lemma unread_nn fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> 0 <= PM.unread (PM.p_src si) smi.
Proof.
  intros MID. open_amid MID. pose proof CP as (PA & IA & _).
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E1 & E2).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & G2 & _) & _).
  unfold PM.unread. clear - E2 G2. lia.
Qed.
Lemma w_pos_self Y : w_pos (s_pos Y) Y = Y.
Proof. destruct Y; reflexivity. Qed.

Definition TF (MVi : word -> option byte) (T : Z) : Prop :=
  0 <= T < 2 ^ 64
  /\ 4096 <= T <= 140737488355264
  /\ (T + 32 <= 65536 \/ 65536 + 6848512 <= T)
  /\ T mod 16 = 0
  /\ L5.writable RSEGS MVi T 32
  /\ (2147446784 + 17592186048512 <= T \/ T + 32 <= 2147446784)
  /\ L5KA.zeros_at MVi ((T / 8) + 2147450880) 4
  /\ L5.u64_at RSEGS MVi (op + 368) (T + 32)
  /\ ((sp - 256) + 256 <= T \/ T + 32 <= (sp - 256))
  /\ (op + 384 <= T \/ T + 32 <= op)
  /\ (oec + 16 <= T \/ T + 32 <= oec)
  /\ (ov + 8 <= T \/ T + 32 <= ov)
  /\ (F + 128 <= T \/ T + 32 <= F)
  /\ (((F / 8) + 2147450880) + 16 <= ((T / 8) + 2147450880) \/ ((T / 8) + 2147450880) + 4 <= ((F / 8) + 2147450880)).
Ltac open_tf H := unfold TF in H; destruct H as (TF0 & TF1 & TF2 & TF3 & TF4 & TF5 & TF6 & TF7 & TF8 & TF9 & TF10 & TF11 & TF12 & TF13).

Lemma tfacts fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y pre top :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> PM.p_stk si = pre ++ [top] ->
  TF (mrestrict (ahid Awi mdi) Mi) (PM.p_b si + 32 * Z.of_nat (length pre))
  /\ PM.pstate_at RSEGS (mrestrict (ahid Awi mdi) Mi) (PM.p_b si + 32 * Z.of_nat (length pre)) top
  /\ PM.pstate_at RSEGS Mi (PM.p_b si + 32 * Z.of_nat (length pre)) top
  /\ In (PM.p_b si, 32 * 2 ^ PM.p_k si) (PEC.owned si eni ki ++ LBX) /\ PM.p_b si + 32 * Z.of_nat (length pre) + 32 <= PM.p_b si + 32 * 2 ^ PM.p_k si.
Proof.
  intros MID ES. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi. unfold SB in FSWi.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 1, sp - 256 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold Hi in Zop, Z32, Z20, OWR, OVIS. fold MVi in Zop, Z32, Z20, OWR. fold op in Zop, Z32, Z20, OWR, OVIS.
  pose proof EA as (EVT & _ & _ & _ & _ & _ & _ & _ & EACC & _).
  pose proof (PMAPAR.ov_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb HHi FOK' (conj EVT (L5CBR.aacc_sub Mi ov 56 ov 8 EACC ltac:(clear; lia) ltac:(clear; lia))))
    as ((V1 & V8 & VBIG) & _). fold ov in V1, V8, VBIG.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WB1 & WF1 & FSAPP1 & FSCEIL1 & _).
  destruct si as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1]. cbn [PM.p_stk PM.p_b PM.p_k] in *. subst stk1.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _). cbn [PM.p_b PM.p_k PM.p_stk] in PVEC.
  destruct PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & CB & AN & EL).
  rewrite length_app in Hlen, VC8, CB, AN. cbn [length] in Hlen, VC8, CB, AN. rewrite Nat2Z.inj_add in Hlen, VC8, CB, AN. cbn [Z.of_nat Pos.of_succ_nat] in Hlen, VC8, CB, AN.
  set (LB1 := PEC.owned (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [top])) eni ki ++ LBX) in *.
  assert (VIN : In (vb1, 32 * 2 ^ vk1) LB1).
  { unfold LB1, PEC.owned. apply in_or_app. left. apply in_or_app. left. unfold PM.parser_own, PM.src_own, PM.vec_own. cbn. right. left. reflexivity. }
  destruct (WB1 _ VIN) as ((B0 & BI0 & B16 & _ & B4 & BAPP) & _ & _ & _ & _ & BFA & _). cbn [fst snd] in B0, BI0, B16, B4, BAPP, BFA.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BI0. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
  pose proof (PM.pow2_pos vk1 ltac:(clear - Hk; Lia.lia)) as P2K.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  assert (TB : vb1 <= T /\ T + 32 <= vb1 + 32 * 2 ^ vk1) by (unfold T; clear - Hlen; lia).
  assert (TAL : T mod 16 = 0) by (unfold T; replace (vb1 + 32 * Z.of_nat (length pre)) with (vb1 + (Z.of_nat (length pre) * 2) * 16) by (clear; lia); rewrite Z.mod_add by (clear; Lia.lia); exact Hal).
  assert (TQ : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - TB B0 B4 GSPT; Lia.lia).
  pose proof (BFA (F, 1, sp - 256 + 32) (in_or_app FF' LKi _ (or_introl (or_introl eq_refl)))) as Z1. cbn [ff_addr ff_class fst snd] in Z1. change (ff_bytes 1) with 128 in Z1.
  pose proof (BFA (fb, 5, rs) (in_or_app FF' LKi (fb, 5, rs) (or_introl (or_intror Hfb)))) as Z2. cbn [ff_addr ff_class fst snd] in Z2. change (ff_bytes 5) with 2048 in Z2.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LKi cri Awi Mi mdi HHi) as VP; cbv zeta in VP; destruct VP as (_ & _ & _ & _ & VB & _).
  assert (TV : L5A.avis Hi T 32) by (apply (VB vb1 (32 * 2 ^ vk1) T 32 VIN); clear - TB; lia).
  assert (PT : PM.pstate_at RSEGS Mi T top) by (specialize (EL (length pre) ltac:(rewrite length_app; cbn; clear; Lia.lia)); rewrite PMPK2.nth_app_at in EL; exact EL).
  split; [| split; [| split; [exact PT| split; [exact VIN| exact (proj2 TB)]]]].
  2: { destruct PT as (PT0 & PT8 & PT16 & PT24).
       split; [apply (proj2 (L5A.u32_at_vis _ Mi T _ (L5A.avis_sub Hi T 32 T 4 TV ltac:(clear; Lia.lia) ltac:(clear; Lia.lia)) ltac:(clear - TQ; Lia.lia) ltac:(clear - TQ; Lia.lia))); exact PT0|].
       split; [apply (proj2 (L5A.u64_at_vis _ Mi (T + 8) _ (L5A.avis_sub Hi T 32 (T + 8) 8 TV ltac:(clear; Lia.lia) ltac:(clear; Lia.lia)) ltac:(clear - TQ; Lia.lia) ltac:(clear - TQ; Lia.lia))); exact PT8|].
       split; [apply (proj2 (L5A.u8_at_vis _ Mi (T + 16) _ (L5A.avis_sub Hi T 32 (T + 16) 1 TV ltac:(clear; Lia.lia) ltac:(clear; Lia.lia)) ltac:(clear - TQ; Lia.lia) ltac:(clear - TQ; Lia.lia))); exact PT16|].
       apply (proj2 (L5A.u64_at_vis _ Mi (T + 24) _ (L5A.avis_sub Hi T 32 (T + 24) 8 TV ltac:(clear; Lia.lia) ltac:(clear; Lia.lia)) ltac:(clear - TQ; Lia.lia) ltac:(clear - TQ; Lia.lia))). exact PT24. }
  unfold TF.
  split; [clear - B0 TB B4 GSLO GSHI GSPT; lia|].
  split; [clear - B0 TB B4 GSLO GSHI GSPT; lia|].
  split; [clear - BI0 TB; lia|].
  split; [exact TAL|].
  split; [apply (proj2 (L5A.writable_vis _ Mi T 32 TV ltac:(clear - TQ; Lia.lia) ltac:(clear - TQ; Lia.lia))); apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub Mi vb1 (32 * 2 ^ vk1)); [exact DB| clear - TB; Lia.lia| clear - TB; Lia.lia]| clear - TQ; Lia.lia| clear - TQ; Lia.lia]|].
  split; [destruct BAPP as (_ & [X|X] & _); [right| left]; clear - X TB; lia|].
  split; [replace 4 with (32 / 8) by reflexivity;
          apply (PMKA.blk_shadow_vis L ar C HI LYa HIok _ _ LKi cri Awi Mi mdi vb1 (32 * 2 ^ vk1) T 32 HHi VIN); [clear - TB; Lia.lia| clear - TB; Lia.lia| apply PMKA.mod16_8'; exact TAL| clear; Lia.lia| reflexivity|];
          intros a Ha; apply CB; clear - Ha TB Hlen; unfold T in *; lia|].
  split; [apply (proj2 (L5A.u64_at_vis _ Mi (op + 368) _ ltac:(apply OVIS; clear; Lia.lia) ltac:(clear - O1; Lia.lia) ltac:(clear - O1 O3; Lia.lia))); replace (op + 368) with (op + 360 + 8) by (clear; lia);
          replace (T + 32) with (vb1 + 32 * (Z.of_nat (length pre) + 1)) by (unfold T; clear; lia); exact VC8|].
  split; [clear - B4 TB GSLO; lia|].
  split; [clear - Z2 TB Eop; Lia.lia|]. split; [clear - Z2 TB Eoec; Lia.lia|]. split; [clear - Z2 TB Eov; Lia.lia|].
  split; [clear - Z1 TB; Lia.lia|].
  assert (FS8 : F / 8 * 8 = F) by exact (proj1 GF8).
  assert (TS8 : T / 8 * 8 = T) by (pose proof (Z.div_mod T 8 ltac:(clear; Lia.lia)) as X; rewrite (PMKA.mod16_8' T TAL) in X; clear - X; lia).
  clear - Z1 TB FS8 TS8; Lia.lia.
Qed.

Lemma clink_top Y0 mo dn dp src tb tg vb vk pre t rr t' sm0 en0 k0 :
  PEC.clink p Y0 (PM.PST mo dn dp src tb tg vb vk (pre ++ [PEC.ps_conv t])) sm0 en0 k0 -> s_stk Y0 = t :: rr -> pre = PEC.stk_conv rr ->
  PEC.clink p (w_stk (t' :: rr) Y0) (PM.PST mo dn dp src tb tg vb vk (pre ++ [PEC.ps_conv t'])) sm0 en0 k0.
Proof.
  intros (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9) HS HP. unfold PEC.clink.
  cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_stk PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src] in *.
  rewrite PEC.stk_conv_cons, <- HP.
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [reflexivity|]. split; [exact L5'|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
Qed.

Lemma amid_pieceT fxi Ri Mi mdi LKi Awi cri mo dn dp src tb tg vb vk pre t rr t' smi eni ki ei Y (fxj : FPState) Rj (pci pcj : Z) Mjv (off n : Z)
      (si := PM.PST mo dn dp src tb tg vb vk (pre ++ [PEC.ps_conv t])) (T := vb + 32 * Z.of_nat (length pre)) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_stk Y = t :: rr -> pre = PEC.stk_conv rr ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fxj Rj (Z_to_bv 64 pcj) Mjv (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) Mjv ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (T + off <= a < T + off + n) -> Mjv (Z_to_bv 64 a) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 a)) ->
  0 <= off -> 0 < n -> off + n <= 32 ->
  PM.pstate_at RSEGS Mjv T (PEC.ps_conv t') ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr Rj (reg j) = getr Ri (reg j)) ->
  (forall Mj mdj, mrestrict (ahid Awi mdi) Mj = Mjv -> ahid Awi mdj = ahid Awi mdi -> mem_grows Mi Mj ->
      amid fxj Rj Mj mdj LKi Awi cri (PM.PST mo dn dp src tb tg vb vk (pre ++ [PEC.ps_conv t'])) smi eni ki ei (w_stk (t' :: rr) Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxj) RSEGS Rj pcj Mj mdj) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID HS HP MS MG FZ Hoff Hn Hon PTv RR KONT'. pose proof MID as (LR & _). entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv t) MID eq_refl) as (TFx & _ & PT & VIN & TB2). cbn [si PM.p_b PM.p_k] in TFx, PT, VIN, TB2.
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WB1 & _).
  destruct (WB1 _ VIN) as ((B0 & BI0 & B16 & _ & B4 & BAPP) & _ & _ & _ & _ & BFA & _). cbn [fst snd] in B0, BI0, B16, B4, BAPP, BFA.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BI0. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
  pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & PSRC & _ & _ & _ & _ & PVEC & _). cbn [si PM.p_b PM.p_k PM.p_stk PM.p_src] in PVEC, PSRC.
  pose proof PVEC as (_ & _ & _ & Hk & Hlen & Hal & DB & _). destruct PSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DCH & _).
  rewrite length_app in Hlen. cbn [length] in Hlen. rewrite Nat2Z.inj_add in Hlen. cbn [Z.of_nat Pos.of_succ_nat] in Hlen.
  pose proof (PM.pow2_pos vk ltac:(clear - Hk; lia)) as P2K.
  assert (TB : vb <= T /\ T + 32 <= vb + 32 * 2 ^ vk) by (unfold T; clear - Hlen; lia).
  pose proof (BFA (fb, 5, rs) (in_or_app FF' LKi (fb, 5, rs) (or_introl (or_intror Hfb)))) as Z2. cbn [ff_addr ff_class fst snd] in Z2. change (ff_bytes 5) with 2048 in Z2.
  pose proof GFR as (GF1 & GF2 & _).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LBi FF' LKi cri Awi Mi mdi fxi fxj Ri pci Rj pcj Mjv (fun a => T + off <= a < T + off + n) K HHi AMi MS MG FZ).
  { intros a Ha Wa. split.
    - unfold aclientw, aclient_g. left. exists (vb, 32 * 2 ^ vk). split; [exact VIN|]. cbn [fst snd]. clear - Wa TB Hoff Hon; lia.
    - clear - Wa TB BI0 Hoff Hon. lia. }
  intros Mj mdj HHj AMj MRTj HIDj VISj MGMj FRj VVj. change (mrestrict Hi Mj = Mjv) in VISj.

  assert (EKp : L5SAR.ek L ar LBi FF 0 0 [(T + off, n)] Mi Mj).
  { apply (L5SAR.ek_piece L ar LBi FF 0 0 [(T + off, n)] Mi Mj (fun a => T + off <= a < T + off + n) FRj).
    intros a Ha _ O X. apply (O (T + off, n)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; exact X]. }
  assert (WSp : PMKA.wapp [(T + off, n)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct BAPP as (_ & [X|X] & _); [left| right]; clear - X TB Hon Hoff; lia| apply PMKA.wapp_nil]. }
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  assert (NDi : NoDup (map fst LBi)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HHi).
  assert (OUTB : forall q m, In (q, m) LBi -> q <> vb -> PMKA.blk_out [(T + off, n)] q m).
  { intros q m Hq NE i Hi' r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
    destruct (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ q m vb (32 * 2 ^ vk) HHi Hq VIN NE) as [X|X]; clear - X Hi' TB Hoff Hon; lia. }
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold si, PM.parser_own, PM.src_own; cbn; left; reflexivity).
  assert (QNE : PM.sr_qc src <> vb) by exact (vb_neq si eni ki _ _ NDi (or_intror eq_refl)).
  apply (KONT' Mj mdj VISj HIDj MGMj).
  split; [exact (lregs_keep Ri Rj LR RR)|].
  unfold PEACLPD.lmem. change (PMSPA.pm_scr 10) with 32768.
  split; [| split; [| split; [| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  -
    destruct BI as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10).
    unfold PMAUK.binv. split; [exact HHj|]. split; [exact AMj|]. split; [eapply L5LZ.model_rt_trans; [exact U3| exact MRTj]|]. split; [exact U4|]. split; [exact U5|].
    split; [eapply L5SAR.astk_grows; [exact U6| exact MGMj]|].
    split.
    { eapply L5SAR.ek_trans; [exact U7|]. intros a (Ha & Hc & Ho). apply FRj; [exact Ha|]. intros X.
      assert (VIN' : In (vb, 32 * 2 ^ vk) (PEC.owned si eni ki)) by (unfold PEC.owned; apply in_or_app; left; unfold si, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
      apply (PMARS1.own_not_aclient L ar C HI HIok (PEC.owned si eni ki) LBX _ LKi cri Awi Mi _ vb (32 * 2 ^ vk) a sp 32768 HHi VIN' ltac:(clear - X TB Hoff Hon; lia)).
      apply L5SAR.aclient_cons. exact Hc. }
    split; [eapply L5SAR.dk_trans; [exact U8| apply L5SAR.dk_grows; exact MGMj]|].
    split.
    { apply (PEACLPD.own_agree sp R Mi Mj ltac:(clear - GSLO GSPT; lia) ltac:(clear - GSHI GSPT; lia) U9). intros a Ha. unfold PEACLPD.ocell in Ha.
      apply FRj; [clear - Ha GSLO GSHI GSPT; lia|]. intros X. clear - Ha X B4 TB Hoff Hon GSLO. lia. }
    eapply L5.defined_grows; [exact MGMj| exact U10].
  -
    apply (cpre_stepA 0 0 [(T + off, n)] Mi Mj Y si smi eni ki ei (w_stk (t' :: rr) Y) _ ei EKp WSp BRBi NDi); cbn [si PM.p_src PM.p_tb PM.p_tg PM.p_b].
    + intros i Hi' _ _ r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Hi' Z2 TB Hoff Hon. lia.
    + exact OUTB.
    + reflexivity. + reflexivity. + reflexivity.
    + apply (parser_top_updA Mi Mj op ois si pre (PEC.ps_conv t) (PEC.ps_conv t') PA eq_refl); cbn [si PM.p_src PM.p_b PM.p_k PM.p_tb].
      * clear - O1; lia.
      * clear - O1 O3; lia.
      * apply (PMKA.agA_obj L ar LBi FF 0 0 _ Mi Mj EKp WSp FRB op 384 AOP). intros i Hi' r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Hi' Z2 TB Hoff Hon Eop. lia.
      * apply (L5.defined_grows Mi Mj _ _ MGMj DCH).
      * apply (PMARS1.agsh_blk L ar LBi FF 0 0 _ Mi Mj _ PM.CHUNK EKp WSp QIN); [destruct (BRBi _ QIN) as (X1 & X2); cbn [fst snd] in X1, X2; clear - X1; lia| destruct (BRBi _ QIN) as (X1 & X2); cbn [fst snd] in X1, X2; unfold PM.CHUNK in X2 |- *; clear - X2; lia].
      * clear - B0. lia.
      * clear - B4 GSLO GSHI GSPT. lia.
      * intros i Hi'. rewrite FRj; [reflexivity| clear - Hi' TB B0 B4 GSLO GSHI GSPT; lia| clear - Hi' TB Hoff; unfold T in *; lia].
      * intros i Hi'. rewrite FRj; [reflexivity| clear - Hi' TB B0 B4 GSLO GSHI GSPT; lia| clear - Hi' TB Hon; unfold T in *; lia].
      * apply (PMARS1.agsh_blk L ar LBi FF 0 0 _ Mi Mj vb (32 * 2 ^ vk) EKp WSp VIN); clear - B0 B4 GSLO GSHI GSPT; lia.
      * apply (L5.defined_grows Mi Mj _ _ MGMj). apply (L5.defined_sub Mi vb (32 * 2 ^ vk)); [exact DB| clear - TB; lia| clear - TB; lia].
      * assert (TQ : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - TB B0 B4 GSPT; lia).
        pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LKi cri Awi Mi mdi HHi) as VP; cbv zeta in VP; destruct VP as (_ & _ & _ & _ & VB & _).
        assert (TV : L5A.avis Hi T 32) by (apply (VB vb (32 * 2 ^ vk) T 32 VIN); clear - TB; lia).
        destruct PTv as (PT0 & PT8 & PT16 & PT24). rewrite <- VISj in PT0, PT8, PT16, PT24.
        split; [exact (proj1 (L5A.u32_at_vis Hi Mj T _ (L5A.avis_sub Hi T 32 T 4 TV ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - TQ; lia) ltac:(clear - TQ; lia)) PT0)|].
        split; [exact (proj1 (L5A.u64_at_vis Hi Mj (T + 8) _ (L5A.avis_sub Hi T 32 (T + 8) 8 TV ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - TQ; lia) ltac:(clear - TQ; lia)) PT8)|].
        split; [exact (proj1 (L5A.u8_at_vis Hi Mj (T + 16) _ (L5A.avis_sub Hi T 32 (T + 16) 1 TV ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - TQ; lia) ltac:(clear - TQ; lia)) PT16)|].
        exact (proj1 (L5A.u64_at_vis Hi Mj (T + 24) _ (L5A.avis_sub Hi T 32 (T + 24) 8 TV ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - TQ; lia) ltac:(clear - TQ; lia)) PT24).
      * intros c0 n0 q0 E0. assert (TIN : In (q0, c0) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold si, PM.parser_own, PM.vs_own; cbn [PM.p_tb PM.p_src PM.p_b PM.p_k]; rewrite E0; apply in_or_app; right; right; left; reflexivity).
        apply (PMKA.agA_blk L ar LBi FF 0 0 _ Mi Mj EKp WSp BRBi q0 c0 TIN). apply (OUTB q0 c0 TIN).
        apply (vb_neq si eni ki q0 c0 NDi). left. cbn [si PM.p_tb]. rewrite E0. left. reflexivity.
    + change (PMSTA.base_okA RSEGS PMA.AD Mj). apply (PMASK.base_keep L ar C LY LBi FF 0 0 _ Mi Mj EKp); [| exact BASE].
      intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha BI0 TB Hoff Hon. lia.
    + apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBi FF 0 0 _ Mi Mj EKp ei PECSA.addrs_wf_A); [| exact ERR].
      intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
      split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - DI BI0 TB Hoff Hon. lia.
    + exact (clink_top Y mo dn dp src tb tg vb vk pre t rr t' smi eni ki CL HS HP).
    + cbn [s_ec w_stk]. apply (PECFA.ec_state_keepA RSEGS AD L ar LBi FF 0 0 _ Mi Mj EKp WSp FRB fb (s_ec Y) cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact ECS].
      intros i Hi' r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Hi' Z2 TB Hoff Hon Eoec. lia.
    + cbn [s_ec w_stk]. exact ECI.
    + exact CP.
  -
    apply (PEACLPD.lspill_agree Mi Mj sp F _ _ _ ltac:(clear - GSLO GSPT; lia) ltac:(clear - GSHI GSPT; lia) LSP).
    intros a Ha. apply FRj; [clear - Ha GSLO GSHI GSPT; lia| clear - Ha TB B4 GSLO Hoff Hon; unfold T in *; lia].
Qed.

Lemma wr_where : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 2040) \/ (0x674080 <= a < 0x695df4).
Proof.
  intros rr a Hin Hr. unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
  cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin. unfold L5.in_rng in Hr.
  repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin.
Qed.
Lemma wr_wav : forall rr a, In rr WR -> L5.in_rng rr a -> ~ ocell sp a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 1 / 8).
Proof.
  entry_facts. frame_facts.
  intros rr a Hin Hr. change (ff_bytes 1 / 8) with 16. unfold PEACLPD.ocell, SB.
  pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  pose proof FSAPP as (FA0 & FA1 & FA2).
  destruct (wr_where rr a Hin Hr) as [X'|X']; (split; [clear - X' SLO SPT F2 FSCEIL; lia|]).
  - destruct FA1 as [Y'|Y']; clear - X' Y' DF1 DF2 F1 F2; lia.
  - clear - X' DF1; lia.
Qed.
Lemma wr_F : forall rr a, In rr WR -> L5.in_rng rr a -> ~ (F <= a < F + 128).
Proof.
  entry_facts. frame_facts.
  assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF 0 0 (a + i)).
  { intros a n X1 X2 X3 i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - X1 X2 Hi'; lia| intros Y'; clear - X1 X2 Hi' Y'; lia]. }
  destruct (APART (fb + 32) 2008 0 0 (CLfb (fb + 32) 2008 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z' & _). change (ff_bytes 1) with 128 in Z'.
  pose proof GFR as (GF1 & _).
  intros rr a Hin Hr. destruct (wr_where rr a Hin Hr) as [X'|X']; [clear - X' Z'; lia| clear - X' GFR; lia].
Qed.
Lemma wr_stk : forall rr a, In rr WR -> L5.in_rng rr a -> ~ (sp - 256 <= a < sp).
Proof.
  entry_facts. frame_facts.
  intros rr a Hin Hr. destruct (wr_where rr a Hin Hr) as [X'|X']; [clear - X' F2 FSCEIL GSLO; lia| clear - X' GSLO GSHI GSPT SLO SPT; lia].
Qed.
Lemma wappR : PMKA.wapp WR.
Proof.
  entry_facts. intros rr Hin. destruct rr as [ra' rn]. unfold BIGSHADOW_LO, BIGSHADOW_HI. cbn [fst snd].
  pose proof FSAPP as (FA0 & FA1 & FA2).
  unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
  cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <-; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia|]). destruct Hin.
Qed.
Lemma szk Mc lo g : L5SAR.ek L ar LBX FF sp 32768 WR M Mc -> sp - 32768 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g.
Proof.
  entry_facts. intros EKc H1' H2' H3' H4'.
  apply (PMKA.stksh_keepA L ar LBX FF sp 32768 WR M Mc EKc wappR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
  apply (PMKA.shadow_zero_sub M (sp - 32768) 4096); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
  apply PMKA.mod16_8'. replace (sp - 32768) with (sp + (-2048) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
Qed.

Lemma lspill_callee LB scr Wc Mi Mj : L5CA.ahpres L ar LB FF' (sp - 256) scr Wc Mi Mj -> 0 <= scr ->
  (forall rr a, In rr Wc -> L5.in_rng rr a -> ~ (sp - 256 <= a < sp)) ->
  PEACLPD.lspill Mi sp F op ov oec -> PEACLPD.lspill Mj sp F op ov oec.
Proof.
  entry_facts. frame_facts. intros HP Hs WS LSP0.
  apply (PEACLPD.lspill_agree Mi Mj sp F _ _ _ ltac:(clear - GSLO GSPT; lia) ltac:(clear - GSHI GSPT; lia) LSP0).
  intros a Ha. apply (proj1 HP). split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
  - apply (L5SAR.stack_client L ar LB FF' (sp - 256) scr a); clear - Ha Hs GSLO GSHI GSPT; lia.
  - intros rr Hin Hr. exact (WS rr a Hin Hr ltac:(clear - Ha; lia)).
Qed.

Lemma call_crun (T : Type) (pc h : Z) (args : T -> bvmap 5 word -> Z -> Prop) (MPf : T -> list Z -> st -> Prop) (Ff : T -> list Z -> st -> st)
    (SPEC : PECSPA.crun_spec RSEGS AD AAD EE L ar HI P T pc h args MPf Ff) (ta : T) (q : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> 0 <= h <= 9 ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> args ta Ri fb ->
  MPf ta p Y -> s_bad (Ff ta p Y) = false -> PESKA.spa_hb P (s_hi (Ff ta p Y)) ->
  (forall fx' R' M' md' LK' Aw' cr' si' smi' eni' ki' ei', regs_preserved Ri R' ->
      amid fx' R' M' md' LK' Aw' cr' si' smi' eni' ki' ei' (Ff ta p Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri pc Mi mdi) K.
Proof.
  intros MID Hh J1 RAq ARGS MPa NBa HBa KONT'. pose proof MID as (LR & _). entry_facts. frame_facts. open_amid MID.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 1, sp - 256 + 32) FOK).
  pose proof SPEC as SP. unfold PECSPA.crun_spec in SP.
  assert (ESCR : PMSPA.pm_scr h = 12288 + 2048 * h) by reflexivity.
  apply (SP PMODE ta fxi Ri Mi mdi K LBX FF' LKi Awi cri (sp - 256) q fb cat p Y si str smi eni ki ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3, J3; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4, J4; rewrite <- L5K.rl4; exact Rtp|].
    rewrite ESCR.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 32768 256 (12288 + 2048 * h) ASTKi (mem_grows_refl Mi)); [clear; lia| clear - Hh; lia| clear - Hh; lia| replace (sp - 256) with (sp + (-16) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    replace ((12288 + 2048 * h) / 8) with (1536 + 256 * h).
    2: { apply (Z.div_unique_exact (12288 + 2048 * h) 8 (1536 + 256 * h)); clear - Hh; lia. }
    apply szk; [exact EKbi| clear - Hh; lia| clear - Hh; lia| | clear - Hh; lia].
    replace (sp - 256 - (12288 + 2048 * h)) with (sp + (- (1568 + 256 * h)) * 8) by (clear; lia). rewrite Z_mod_plus_full. apply PMKA.mod16_8'. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMAUAR.ffroomA_push 10 h FF LK LKi _ FRM INCLi); [exact NDFi| clear - Hh; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 256) F 1 (sp - 256 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 256) with (sp + (-8) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { exact ARGS. }
  { exact CP. }
  { exact INCS. }
  { exact POK. }
  { exact MPa. }
  { exact NBa. }
  { exact HBa. }
  { exact (credit_le_keep _ _ _ _ CRED CK). }
  intros fx4 R4 M4 model4 LK4 Aw4 s4 sm4 en4 k4 e4 cr4 RP4 CPRE4 STEP4 EE4 HP4 CK4 MRT4 INCLK4 INCAw4 AM4 HH4.
  rewrite ESCR in HP4.
  assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 32768 (sp - 256) (own sp R) F 1 WR (PEC.owned s4 en4 k4) M4 model4 LK4 cr4 Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 32768 (sp - 256) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PEC.owned s en k) G'
             WR WR (PEC.owned si eni ki) [] (PEC.owned s4 en4 k4) Mi mdi LKi cri Awi M4 model4 LK4 cr4 Aw4 (12288 + 2048 * h) WR BI HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
      [clear - Hh; lia| clear - Hh; lia| exact wr_wav| intros a _ X'; exact X'| intros a X'; exact X']. }
  assert (LSP4 : PEACLPD.lspill M4 sp F op ov oec).
  { apply (lspill_callee LBX (12288 + 2048 * h) WR Mi M4); [exact HP4| clear - Hh; lia| exact wr_stk| exact LSP]. }
  apply (KONT' fx4 R4 M4 model4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4).
  pose proof (lregs_pres Ri R4 LR RP4) as LR4.
  pose proof (PMAPAR.src_step_transA _ _ _ _ _ _ ST STEP4) as ST4.
  assert (EIMP4 : e = true -> e4 = true) by (intros X'; exact (EE4 (EIMP X'))).
  pose proof (credit_keep_trans _ _ _ _ _ _ CK CK4) as CK4'.
  close_amid LR4 BI4 CPRE4 LSP4 ST4 EIMP4 CK4'.
Qed.

Lemma call_mkec (q v : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 oec -> getr Ri (reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
  (forall fx' R' M' md' LK' Aw', regs_preserved Ri R' -> amid fx' R' M' md' LK' Aw' cri si smi eni ki true (w_ec true Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri (pa_make_ec AD) Mi mdi) K.
Proof.
  intros MID J1 RAq J10 J11 Hv KONT'. pose proof MID as (LR & _). entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  assert (NDi : NoDup (map fst LBi)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HHi).
  assert (ECD : L5.defined Mi oec 16 /\ PMSPA.accA Mi oec 16).
  { pose proof ECS as ECS0. unfold PECA.ec_stateA in ECS0. fold oec in ECS0.
    destruct (s_ec Y); [destruct ECS0 as (v0 & _ & (_ & _ & D' & A')); exact (conj D' A')| destruct ECS0 as (_ & _ & D' & A'); exact (conj D' A')]. }
  pose proof MKE as MK. unfold PECSA.make_ec_spec, PECSPA.make_ec_spec in MK.
  apply (MK fxi Ri Mi mdi K LBi FF' LKi Awi cri oec v (sp - 256) q ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3, J3; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4, J4; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 32768 256 14336 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 256) with (sp + (-16) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 256 - 14336) with (sp + (-912) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMAUAR.ffroomA_push 10 1 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 256) F 1 (sp - 256 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact J10. }
  { rewrite L5K.rl11. exact J11. }
  { exact Hv. }
  { apply PMAUAR.aobjA_push. apply AOF; clear - Eoec; lia. }
  { exact C8m. }
  { exact (proj1 ECD). }
  { exact (proj2 ECD). }
  { exact BASE. }
  { exact ERR. }
  intros fx6 R6 M6 model6 LK6 Aw6 RP6 EC6 ERR6 HP6 MRT6 INCLK6 INCAw6 AM6 HH6.
  change (PMSPA.pm_scr 1) with 14336 in HP6.
  set (Wc6 := (oec, 16) :: (if ei then [] else PMSPA.err_W AD)) in HP6.
  assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> (oec <= a < oec + 16) \/ (0x674080 <= a < 0x695df4)).
  { intros rr a Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [left; exact Hr|]. right. destruct ei; [destruct Hin|].
    unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin. unfold L5.in_rng in Hr.
    destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
  assert (Wc6W : forall a, L5.outside WR a -> L5.outside Wc6 a).
  { intros a Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X'|X'].
    + apply (Ho (PMSP.o_ec AD fb, 16)); [unfold WR; wr_mem 6| wr_rng; clear - X' Eoec; lia].
    + unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr X' Eoec O1 Eop; lia|].
      destruct ei; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin.
      destruct Hin as [<-|[<-|[]]].
      * apply (Ho (pa_errcat_guard AD, 2)); [unfold WR; wr_mem 7| exact Hr].
      * apply (Ho (pa_atexit AD, 544)); [unfold WR; wr_mem 8| exact Hr]. }
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 32768 (sp - 256) (own sp R) F 1 WR (PEC.owned si eni ki) M6 model6 LK6 cri Aw6).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 32768 (sp - 256) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PEC.owned s en k) G'
             WR WR (PEC.owned si eni ki) (PEC.owned si eni ki) (PEC.owned si eni ki) Mi mdi LKi cri Awi M6 model6 LK6 cri Aw6 14336 Wc6 BI HP6 HH6 AM6 MRT6 INCAw6 INCLK6);
      [clear; lia| clear; lia| | intros a Hc Ho; exact (Wc6W a Ho)| intros a X'; exact X'].
    intros rr a Hin Hr. change (ff_bytes 1 / 8) with 16. unfold PEACLPD.ocell, SB.
    pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
    assert (DF2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia).
    pose proof FSAPP as (FA0 & FA1 & FA2).
    destruct (Wc6R rr a Hin Hr) as [X'|X']; (split; [clear - X' SLO SPT Eop Eoec F2 FSCEIL; lia|]).
    + destruct FA1 as [Y'|Y']; clear - X' Y' DF1 DF2 F1 F2 Eoec; lia.
    + clear - X' DF1; lia. }
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 1, sp - 256 + 32)] sp 32768 (sp - 256) 14336 Wc6 Wc6 Mi M6 ltac:(rewrite app_nil_l; exact HP6) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK6.
  assert (WAPP6 : PMKA.wapp Wc6).
  { intros rr Hin. unfold Wc6 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; cbn [fst snd].
    - pose proof FSAPP as (FA0 & FA1 & FA2). destruct FA1 as [Y'|Y']; clear - Y' F1 F2 Eoec; lia.
    - destruct ei; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
  assert (OUTB6 : forall q' m, In (q', m) LBi -> forall i, q' <= i < q' + m -> L5.outside Wc6 i).
  { intros q' m Hq i Hi' rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y'].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m oec 16 HHi Hq (PMAUAR.aobjA_push FF oec 16 _ (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia)))) as [Z'|Z']; clear - Hi' Y' Z'; lia.
    - pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q' m HHi Hq) as Z'. destruct Z' as [Z'|Z']; clear - Hi' Y' Z'; lia. }
  assert (LSP6 : PEACLPD.lspill M6 sp F op ov oec).
  { apply (lspill_callee LBi 14336 Wc6 Mi M6 HP6 ltac:(clear; lia)); [| exact LSP].
    intros rr a Hin Hr X'. destruct (Wc6R rr a Hin Hr) as [Y'|Y']; [clear - X' Y' Eoec F2 FSCEIL GSLO; lia| clear - X' Y' GSLO GSHI GSPT SLO SPT; lia]. }
  apply (KONT' fx6 R6 M6 model6 LK6 Aw6 RP6).
  pose proof (lregs_pres Ri R6 LR RP6) as LR6.
  assert (CP6 : PECA.crun_preA RSEGS AD AAD EE L ar P M6 fb p (w_ec true Y) si str smi eni ki true cat).
  { apply (cpre_stepA sp 32768 Wc6 Mi M6 Y si smi eni ki ei (w_ec true Y) si true EK6 WAPP6 BRBi NDi).
    + intros i Hi' N1 N2 rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y']; [clear - N2 Y'; lia| clear - Hi' Y' Eop O1; lia].
    + intros q' m Hq _. exact (OUTB6 q' m Hq).
    + reflexivity. + reflexivity. + reflexivity.
    + apply (PMKA.parser_keepA RSEGS AD L ar LBi FF sp 32768 Wc6 Mi M6 EK6 WAPP6 FRB BRBi _ _ _ AOP); [| | | | | exact PA].
      * unfold LBi, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. left. exact Hx.
      * intros i Hi' rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y']; [clear - Hi' Y' Eop Eoec; lia| clear - Hi' Y' Eop O1; lia].
      * unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.src_own; left; reflexivity.
      * unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
      * intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.vs_own. rewrite E0. right; right; left; reflexivity.
    + apply (PMAPAR.base_keepW L ar C LY LBi FF sp 32768 Wc6 Mi M6 EK6); [| | | | exact BASE].
      * intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [Y'|Y']; [clear - Ha Y' Eoec Eop O1; lia| clear - Ha Y'; lia].
      * intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct ei; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
      * intros rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eoec Eop O1; lia|]. destruct ei; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia.
      * intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct ei; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
    + exact ERR6.
    + destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
      unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad s_ec w_ec].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad].
    + unfold PECA.ec_stateA. cbn [s_ec w_ec]. fold oec. exists v. split; [exact Hv| exact EC6].
    + intros _; reflexivity.
    + exact CP. }
  assert (EIMP6 : e = true -> true = true) by (intros _; reflexivity).
  close_amid LR6 BI6 CP6 LSP6 ST EIMP6 CK.
Qed.

Lemma call_src (pc : Z) (args : list fframe -> bvmap 5 word -> (word -> option byte) -> Z -> Z -> PM.pst -> Prop)
      (res : list Z -> bvmap 5 word -> bvmap 5 word -> (word -> option byte) -> PM.srcst -> PM.srcst -> PM.strm -> PM.strm -> Prop)
      (SPEC : PECSPA.csrc_spec RSEGS AD L ar HI pc 4 32 args PMSPA.no_W res) (ra : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_more Y = true -> s_done Y = false -> 0 <= s_pos Y <= blen p ->
  getr Ri (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr Ri (reg 10) = Z_to_bv 64 (op + 24) -> args FF' Ri Mi (sp - 256) fb si ->
  (forall p0 Ra Rb Mb sa sb ma mb, res p0 Ra Rb Mb sa sb ma mb -> PECSPA.cwin RSEGS Mb p0 sb mb) ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 src2 smi2, regs_preserved Ri R2 -> res p Ri R2 M2 (PM.p_src si) src2 smi smi2 ->
      PEC.pos_of p (PM.p_src si) smi = s_pos Y ->
      amid fx2 R2 M2 md2 LK2' Aw2 cri (PMSPA.with_src si src2) smi2 eni ki ei (w_pos (PEC.pos_of p src2 smi2) Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 ra M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pc Mi mdi) K.
Proof.
  intros MID MORE DONE PPOS J1 RAq J10 ARGS RESW KX. pose proof MID as (LR & _). entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WBi & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDi & NDFi & _).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 1, sp - 256 + 32) FOK).
  assert (PINC : incl (PM.parser_own si) LBi) by (unfold LBi, PEC.owned; intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx).
  assert (SINC : incl (PM.vs_own str) LBi) by (unfold LBi; apply incl_appr; exact INCS).
  assert (EINC : incl (PEC.enc_own eni) LBi) by (unfold LBi, PEC.owned; intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own ki) LBi) by (unfold LBi, PEC.owned; intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx).
  set (qc := PM.sr_qc (PM.p_src si)) in *.
  assert (Iq : In (qc, 16384) LBi) by (apply PINC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  destruct (BRBi _ Iq) as (Bq0' & Bq47). cbn [fst snd] in Bq0', Bq47.
  pose proof (WBi _ Iq) as ((Bq0 & Bq1 & Bq2 & Bq3 & Bq4 & Bq5) & _). cbn [fst snd] in Bq0, Bq1, Bq2, Bq3, Bq4, Bq5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK in Bq5, Bq4.
  destruct Bq5 as (_ & Bq5 & _).
  pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ _ _ HHi Iq) as Bqi. unfold PM.CHUNK in Bqi.
  assert (EPO : LBi = PM.parser_own si ++ (PEC.enc_own eni ++ PESK.sink_own ki ++ LBX)) by (unfold LBi, PEC.owned; rewrite <- !app_assoc; reflexivity).
  assert (NDL : NoDup (map fst (PM.parser_own si ++ (PEC.enc_own eni ++ PESK.sink_own ki ++ LBX)))) by (rewrite <- EPO; exact NDi).
  assert (NEQ : forall q' m, In (q', m) (PEC.enc_own eni ++ PESK.sink_own ki ++ LBX) -> q' <> qc).
  { intros q' m Hin. apply not_eq_sym. apply (PMPK.fst_neq_app (PM.parser_own si) (PEC.enc_own eni ++ PESK.sink_own ki ++ LBX) qc 16384 q' m NDL); [| exact Hin].
    unfold PM.parser_own, PM.src_own. left. reflexivity. }
  assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF 0 0 (a + i)).
  { intros a n X1 X2 X3 i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - X1 X2 Hi'; lia| intros Y'; clear - X1 X2 Hi' Y'; lia]. }
  pose proof GFR as (GF1 & GF2 & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  pose proof (Lpos MORE DONE) as POS.

  pose proof SPEC as SP. unfold PECSPA.csrc_spec in SP.
  apply (SP fxi Ri Mi mdi K (PEC.enc_own eni ++ PESK.sink_own ki ++ LBX) FF' LKi Awi cri (sp - 256) ra fb p si str smi [] ltac:(rewrite <- EPO; exact HHi) AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3, J3; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4, J4; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 4) with 20480. change (20480 / 8) with 2560.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 32768 256 20480 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 256) with (sp + (-16) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 256 - 20480) with (sp + (-1296) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomA_push 10 4 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 256) F 1 (sp - 256 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 256) with (sp + (-8) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { unfold PMSPA.o_src. fold op. rewrite L5K.rl10. exact J10. }
  { exact ARGS. }
  { reflexivity. }
  { exact PA. }
  { exact IA. }
  { exact BASE. }
  { exact ACC. }
  { intros x Hx. apply in_or_app. right. apply in_or_app. right. exact (INCS x Hx). }
  { exact POK. }
  { exact CONT. }
  intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 RP4 PA4 IA4 STEP4 RES4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
  change (PMSPA.pm_scr 4) with 20480 in HP4. rewrite <- EPO in HP4, HH4. rewrite app_nil_r in HP4.
  set (Wc := PMSPA.W_src AD fb (PM.p_src si)) in HP4.
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a -> (op + 280 <= a < op + 320) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (qc <= a < qc + 16384)).
  { intros rr a Hin Hr. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is AD PeCLayoutA.CADDR_A] in Hin. fold qc in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eop Eois; left; lia
      |unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eop Eois; right; left; lia
      |unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eop Eois; right; right; left; lia
      |unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr; clear - Hr; right; right; right; lia]. }
  assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (D2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (WAV4 : forall rr a, In rr Wc -> L5.in_rng rr a -> ~ ocell sp a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 1 / 8)).
  { intros rr a Hin Hr. change (ff_bytes 1 / 8) with 16. unfold PEACLPD.ocell, SB.
    destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|X']]]; (split; [clear - X' O2 I2 Bq4 GFCEIL GSLO Eop Eois GF2 GFR; lia|]).
    + clear - X' OBIG D1 D2; lia.
    + clear - X' IBIG D1 D2; lia.
    + clear - X' IBIG D1 D2; lia.
    + destruct Bq5 as [Yb|Yb]; clear - X' Yb D1 D2; lia. }
  assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 32768 (sp - 256) (own sp R) F 1 WR (PEC.owned si eni ki) M4 md4 LK4 cri Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 32768 (sp - 256) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PEC.owned s en k) G'
             WR WR (PEC.owned si eni ki) (PEC.owned si eni ki) (PEC.owned si eni ki) Mi mdi LKi cri Awi M4 md4 LK4 cri Aw4 20480 Wc BI HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
      [clear; lia| clear; lia| exact WAV4| | intros a X'; exact X'].
    intros a Hc Ho rr Hin Hr. destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|X']]].
      + apply (Ho (PMSP.o_src AD fb + 256, 40)); [unfold WR; wr_mem 1| wr_rng; clear - X' Eop; lia].
      + apply (Ho (PMSP.o_is AD fb + 40, 8)); [unfold WR; wr_mem 2| wr_rng; clear - X' Eois; lia].
      + apply (Ho (PMSP.o_is AD fb + 152, 4)); [unfold WR; wr_mem 3| wr_rng; clear - X' Eois; lia].
      + assert (Iq' : In (qc, 16384) (PEC.owned si eni ki)) by (unfold PEC.owned; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
        exact (PMARS1.own_not_aclient L ar C HI HIok (PEC.owned si eni ki) LBX FF' LKi cri Awi Mi _ qc 16384 a sp 32768 HHi Iq' X' (L5SAR.aclient_cons L ar LBX FF (F, 1, sp - 256 + 32) sp 32768 a Hc)). }
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 1, sp - 256 + 32)] sp 32768 (sp - 256) 20480 Wc Wc Mi M4 ltac:(rewrite app_nil_l; exact HP4) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK4.
  assert (OUTc : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op + 280 \/ op + 320 <= a) -> (a + n <= ois + 40 \/ ois + 48 <= a) ->
                 (a + n <= ois + 152 \/ ois + 156 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i).
  { intros a n X1 X2 X3 X4 X5 i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Yc|[Yc|[Yc|Yc]]]; [clear - Hi' Yc X3; lia| clear - Hi' Yc X4; lia| clear - Hi' Yc X5; lia|].
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 a n HHi Iq (PMAUAR.aobjA_push FF a n _ (AOF a n X1 X2))) as [Z'|Z']; clear - Hi' Yc Z'; lia. }
  assert (WAPPc : PMKA.wapp Wc).
  { intros rr Hin. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is AD PeCLayoutA.CADDR_A] in Hin. fold qc in Hin.
    unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PM.CHUNK.
    - clear - OBIG Eop; lia.
    - clear - IBIG Eois; lia.
    - clear - IBIG Eois; lia.
    - destruct Bq5 as [Yb|Yb]; clear - Yb; lia. }
  assert (OUTBc : forall q' m, In (q', m) LBi -> q' <> qc -> forall i, q' <= i < q' + m -> L5.outside Wc i).
  { intros q' m Hq' NE i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Yc|[Yc|[Yc|Yc]]].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq' (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HHi Hq' (PMAUAR.aobjA_push FF ois 272 _ AOI)) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HHi Hq' (PMAUAR.aobjA_push FF ois 272 _ AOI)) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - pose proof (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ q' m qc 16384 HHi Hq' Iq NE) as Z'. clear - Hi' Yc Z'; lia. }
  assert (OUTcI : forall i, 0x674080 <= i < 0x695df4 -> L5.outside Wc i).
  { intros i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Yc|[Yc|[Yc|Yc]]]; [clear - Hi' Yc O1; lia| clear - Hi' Yc I1; lia| clear - Hi' Yc I1; lia|].
    destruct Bqi as [Z'|Z']; clear - Hi' Yc Z'; lia. }

  assert (EA4 : PECA.enc_atA RSEGS EE L ar M4 ov fb eni).
  { apply (PECFA.enc_keepA RSEGS EE L ar LBi FF sp 32768 Wc Mi M4 EK4 WAPPc FRB BRBi ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINC| | exact EA].
    - apply OUTc; clear - Eop Eov Eois; lia.
    - intros Hp. assert (INe : In (PEC.en_b eni, PEC.ESZ * PEC.ecap (PEC.en_k eni)) (PEC.enc_own eni)).
      { unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      refine (OUTBc _ _ (EINC _ INe) _). apply (NEQ _ (PEC.ESZ * PEC.ecap (PEC.en_k eni))). apply in_or_app. left. exact INe. }
  assert (VREF4 : L5.u64_at RSEGS M4 (op + 384) ov).
  { apply (PMKA.u64_keepA RSEGS L ar LBi FF sp 32768 Wc Mi M4 EK4 WAPPc FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF].
    apply OUTc; clear - Eop Eois; lia. }
  assert (SKA4 : PESKA.sink_atA RSEGS L ar P M4 osk ki).
  { apply (PECFA.sink_keepA RSEGS L ar LBi FF sp 32768 Wc Mi M4 EK4 WAPPc FRB BRBi P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [| exact KINC| | exact SKA].
    - apply OUTc; clear - Eop Eosk Eois; lia.
    - intros Hp. assert (INk : In (PESK.sk_b ki, PESK.sk_c ki) (PESK.sink_own ki)).
      { unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      refine (OUTBc _ _ (KINC _ INk) _). apply (NEQ _ (PESK.sk_c ki)). apply in_or_app. right. apply in_or_app. left. exact INk. }
  assert (ERR4 : PESTA.err_okA RSEGS AD AAD EE M4 ei).
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBi FF sp 32768 Wc Mi M4 EK4 ei PECSA.addrs_wf_A); [| exact ERR].
    intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUTcI; exact DI. }
  assert (BASE4 : PMSTA.base_okA RSEGS AD M4).
  { change (PMSTA.base_okA RSEGS PMA.AD M4). apply (PMASK.base_keep L ar C LY LBi FF sp 32768 Wc Mi M4 EK4); [| exact BASE].
    intros a Ha rr Hin Hr. destruct (WcR rr a Hin Hr) as [Yc|[Yc|[Yc|Yc]]]; [clear - Ha Yc O1; lia| clear - Ha Yc I1; lia| clear - Ha Yc I1; lia| destruct Bqi as [Z'|Z']; clear - Ha Yc Z'; lia]. }
  assert (ECS4 : PECA.ec_stateA RSEGS AD M4 fb (s_ec Y) cat).
  { apply (PECFA.ec_state_keepA RSEGS AD L ar LBi FF sp 32768 Wc Mi M4 EK4 WAPPc FRB fb (s_ec Y) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
    fold oec. apply OUTc; clear - Eop Eoec Eois; lia. }
  assert (ACC4 : PMSPA.accA M4 op PECA.RDR_BYTES).
  { pose proof BI4 as (_ & _ & _ & _ & _ & _ & EKb4 & _).
    exact (PMKA.acc_keepA' L ar LBX FF sp 32768 WR M M4 EKb4 wappR FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CPRE))))))))))))). }
  assert (QC4 : PM.sr_qc src4 = qc) by (destruct STEP4 as (X' & _); exact X').
  set (s4 := PMSPA.with_src si src4) in *.
  assert (EOWN : PM.parser_own s4 = PM.parser_own si) by (unfold s4, PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC4; reflexivity).
  assert (EOWN4 : PEC.owned s4 eni ki = PEC.owned si eni ki) by (unfold PEC.owned; rewrite EOWN; reflexivity).

  assert (CONT4 : PEC.content_ok RSEGS AD M4 fb p src4 str sm4).
  { destruct (RESW _ _ _ _ _ _ _ _ RES4) as (CWP & CWB & CW5). pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS3 & _). pose proof VS3 as (_ & _ & VSF3).
    apply (PECF.content_ok_step RSEGS AD Mi M4 fb p (PM.p_src si) str smi src4 sm4); [clear - I1 Eois; unfold PMSP.o_is; cbn [pa_off_is AD PeCLayoutA.CADDR_A]; lia| clear - I3 Eois; unfold PMSP.o_is; cbn [pa_off_is AD PeCLayoutA.CADDR_A]; lia| | | | exact (proj1 CWP)| exact CWB| exact CW5| exact CONT].
    - unfold PMSP.o_is. cbn [pa_off_is AD PeCLayoutA.CADDR_A]. change (fb + 96) with ois.
      exact (proj1 (PMKA.agA_obj L ar LBi FF sp 32768 Wc Mi M4 EK4 WAPPc FRB (ois + 80) 24 (AOF (ois + 80) 24 ltac:(lia) ltac:(lia)) (OUTc (ois + 80) 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))).
    - intros c0 n0 q0 Es. cbn in VSF3. rewrite Es in VSF3. cbn in VSF3. destruct VSF3 as (_ & _ & _ & Hn0 & Hc0 & _).
      assert (IN0 : In (q0, c0) LBi) by (apply SINC; unfold PM.vs_own; rewrite Es; left; reflexivity).
      destruct (BRBi _ IN0) as (B0' & B1'). cbn [fst snd] in B0', B1'.
      split; [exact B0'|]. split; [clear - B1'; lia|]. split; [clear - Hn0; lia|].
      refine (proj1 (PMKA.agA_blk L ar LBi FF sp 32768 Wc Mi M4 EK4 WAPPc BRBi q0 c0 IN0 _)).
      refine (OUTBc q0 c0 IN0 _). apply (NEQ q0 c0). apply in_or_app. right. apply in_or_app. right. apply INCS. unfold PM.vs_own. rewrite Es. left. reflexivity.
    - intros n0 Es. cbn in VSF3. rewrite Es in VSF3. cbn in VSF3. clear - VSF3. lia. }
  assert (LSP4 : PEACLPD.lspill M4 sp F op ov oec).
  { apply (lspill_callee LBi 20480 Wc Mi M4 HP4 ltac:(clear; lia)); [| exact LSP].
    intros rr a Hin Hr X'. destruct (WcR rr a Hin Hr) as [Yc|[Yc|[Yc|Yc]]]; [clear - X' Yc Eop F2 FSCEIL GSLO; lia| clear - X' Yc Eois F2 FSCEIL GSLO; lia| clear - X' Yc Eois F2 FSCEIL GSLO; lia|].
    clear - X' Yc Bq4 GSLO. lia. }
  apply (KX fx4 R4 M4 md4 LK4 Aw4 src4 sm4 RP4 RES4 POS).
  split; [exact (lregs_pres Ri R4 LR RP4)|]. unfold PEACLPD.lmem. change (PMSPA.pm_scr 10) with 32768.
  split; [rewrite <- EOWN4 in BI4; exact BI4| split; [| split; [exact LSP4| split; [| split; [exact EIMP|]]]]].
  -
    unfold PECA.crun_preA. unfold s4, PMSPA.with_src. cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_more PM.p_done PM.p_depth PM.p_stk].
    split; [exact PA4|]. split; [exact IA4|]. split; [exact EA4|]. split; [exact VREF4|]. split; [exact SKA4|]. split; [exact BASE4|]. split; [exact ERR4|].
    split; [exact TBOK|]. split; [exact CONT4|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_pos PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|].
      split; [intros _ _; reflexivity|].
      split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad]. }
    split; [cbn [s_ec w_pos]; exact ECS4|]. split; [exact ECI| exact ACC4].
  - unfold s4, PMSPA.with_src. cbn [PM.p_src]. exact (PMAPAR.src_step_transA _ _ _ _ _ _ ST STEP4).
  - unfold PMSP.credit_keep, PECA.pot_allA, PEC.credit_add, PM.pot_parser, s4, PMSPA.with_src in CK |- *. cbn [PM.p_k PM.p_tb PM.p_tg fst snd] in CK |- *. exact CK.
Qed.

Lemma unread_nn2 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> 0 <= PM.sr_rem (PM.p_src si) /\ 0 <= PM.sm_eg smi - PM.sm_g smi.
Proof.
  intros MID. open_amid MID. pose proof CP as (PA & IA & _).
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E1 & E2).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & G2 & _) & _).
  clear - E2 G2. split; lia.
Qed.

Lemma cred_fin Mi Xi si smi eni ki ei cri :
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat ->
  PMSP.credit_keep cr cri (PECA.pot_allA L ar P s en k) (PECA.pot_allA L ar P si eni ki) ->
  PMSP.credit_keep cr cri (PECA.pot_allA L ar P s en k) (PESKA.spa_pot P (PESK.sk_c ki)).
Proof.
  intros CP CK0. pose proof CP as (PA & _ & EA & _ & _ & _ & _ & TBOK & _).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PTB & PVEC & _). pose proof PVEC as (_ & _ & _ & Hk & _).
  pose proof EA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EHk & _).
  pose proof (PMA.ly_cost L C LY) as (KPM & BLIN & BOV).
  assert (PPN : 0 <= fst (PM.pot_parser (PMSPA.HV L ar) si) /\ 0 <= snd (PM.pot_parser (PMSPA.HV L ar) si)).
  { pose proof PTB as (_ & _ & TBF). destruct TBOK as (TG1 & TG2 & _).
    unfold PM.pot_parser, PM.credit_add, PM.pot_stack, PM.pot_text. cbn [fst snd].
    unfold PMSPA.HV, LibIfaceAB.heap_view. cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead]. rewrite KPM, BOV.
    assert (CAPB : 0 <= PM.vs_cap (PM.p_tb si) <= 2 ^ 27) by (destruct (PM.p_tb si) as [n1|c1 n1 q1]; cbn [PM.vs_cap] in *; [lia| destruct TBF as (_ & _ & _ & _ & Hc1 & _); lia]).
    pose proof (PM.pow2_pos (PM.p_k si + 1) ltac:(lia)) as P2a. assert (P2b : 2 ^ (PM.p_k si + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
    clear - CAPB P2a P2b Hk TG1. split; nia. }
  assert (EPN : 0 <= fst (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k eni)) /\ 0 <= snd (PEC.pot_estack (PMSPA.HV L ar) (PEC.en_k eni))).
  { pose proof (Z.pow_le_mono_r 2 (PEC.en_k eni) 12 ltac:(lia) ltac:(clear - EHk; lia)) as P2e. pose proof (PM.pow2_pos (PEC.en_k eni) ltac:(clear - EHk; lia)) as P2p.
    unfold PEC.pot_estack. cbn [fst snd]. unfold PMSPA.HV, LibIfaceAB.heap_view. cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead]. rewrite KPM, BOV.
    assert (E2 : 0 <= PEC.ESZ * (2 ^ 12 - 2 ^ PEC.en_k eni)) by (unfold PEC.ESZ; apply Z.mul_nonneg_nonneg; clear - P2e; lia).
    clear - E2 EHk. split; nia. }
  unfold PMSP.credit_keep, PECA.pot_allA, PEC.credit_add, PMSPA.scA in CK0 |- *. cbn [fst snd] in CK0 |- *. clear - CK0 PPN EPN BLIN. nia.
Qed.

Lemma finish (mv dv : Z) (Xf : st) (n : nat) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fx7 : FPState) R7 M7v (pci : Z) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fx7 R7 (Z_to_bv 64 0xb2620) M7v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) M7v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 10) -> M7v (Z_to_bv 64 i) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 i)) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg j) = getr Ri (reg j)) ->
  L5.u8_at RSEGS M7v (op + 8) mv -> L5.u8_at RSEGS M7v (op + 9) dv -> (mv = 0 \/ mv = 1) -> (dv = 0 \/ dv = 1) ->
  Xf = run n p UbjRef.init -> halted Xf = true -> PEC.clink p Xf (set_md si mv dv) smi eni ki -> s_ec Xf = s_ec Y ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID MS7 MG7 FRZ7 K7 MO8 MO9 Hmv Hdv EXF HALT CLF ECF. pose proof MID as (LR & _). entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  pose proof (pfacts _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as PF7. cbv zeta in PF7.
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 1, sp - 256 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold Hi in Zop, Z32, Z20, OWR, OVIS. fold MVi in Zop, Z32, Z20, OWR. fold op in Zop, Z32, Z20, OWR, OVIS.
  destruct (APART op 384 0 0) as (ApF & ApSF & ApFL).
  { intros i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
    split; [clear - Eop Hi'; lia| intros Y'; clear - Eop Hi' Y'; lia]. }
  { clear; lia. }
  change (ff_bytes 1) with 128 in ApF, ApSF. change (128 / 8) with 16 in ApSF. unfold SB in ApSF.
  pose proof GFR as (GF1 & GF2 & GF3 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (DF2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia).

  pose proof (lregs_keep Ri R7 LR K7) as (RQ2 & RQ8 & RQ9 & RQ18 & RQ19 & RQ20 & RQ21 & RQ22 & RQ23 & RQ24 & RQ25 & RQ26 & RQ27 & RQ3 & RQ4). unfold PEACLPD.JT in RQ20.

  assert (AG7 : forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 10) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 16) -> ~ (fl <= i < fl + 1) ->
            M7v (Z_to_bv 64 i) = MVi (Z_to_bv 64 i)).
  { intros i Hi' N1 N2 N3 N4. apply FRZ7; [exact Hi'| exact N1]. }
  pose proof (pfacts_keep MVi M7v PF7 MG7 GL3 AG7) as PF7'.
  assert (RRUN : exists (fx8 : FPState) R8 M8, mem_grows M7v M8
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (F <= i < F + 8) -> ~ (fl <= i < fl + 1) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 16) -> M8 (Z_to_bv 64 i) = M7v (Z_to_bv 64 i))
            /\ msteps RSEGS (@mkst fx7 R7 (Z_to_bv 64 0xb2620) M7v (seg_rom RSEGS)) (@mkst fx8 R8 (Z_to_bv 64 0xb2e48) M8 (seg_rom RSEGS))
            /\ (forall x, In x PEALPP5.KS_alpR -> getr R8 (reg x) = getr R7 (reg x))
            /\ getr R8 (reg 1) = Z_to_bv 64 (bv_unsigned (getr R (reg 1))) /\ getr R8 (reg 2) = Z_to_bv 64 sp
            /\ getr R8 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) /\ getr R8 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9)))
            /\ getr R8 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) /\ getr R8 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19)))
            /\ getr R8 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R (reg 20))) /\ getr R8 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R (reg 21)))
            /\ getr R8 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R (reg 22))) /\ getr R8 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23)))
            /\ getr R8 (reg 24) = Z_to_bv 64 (bv_unsigned (getr R (reg 24))) /\ getr R8 (reg 25) = Z_to_bv 64 (bv_unsigned (getr R (reg 25)))
            /\ getr R8 (reg 26) = Z_to_bv 64 (bv_unsigned (getr R (reg 26))) /\ getr R8 (reg 27) = Z_to_bv 64 (bv_unsigned (getr R (reg 27)))
            /\ L5.u8_at RSEGS M8 fl 0).
  { pose proof PF7' as PFX. open_vf PFX.
    pose proof (PEALPP5.alpR_conc fx7 R7 M7v (VALU 0 0 0 0 0 0)) as PR. unfold VALU in PR. cbn beta iota in PR.
    L5SAR.feed PR ltac:(first [fcl | match goal with |- ?G => fail 100 "alpR feed:" G end]).
    destruct PR as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & MS8 & KS8 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _).
    exists fx8, R8, M8. split; [exact MG8|]. split; [intros i Hi' N1 N2 N3; apply FRZ8; [exact Hi'| clear - N1; lia| clear - N2; lia| clear - N3; lia]|].
    split; [exact MS8|]. split; [exact KS8|]. repeat (split; [assumption|]). exact FL0. }
  destruct RRUN as (fx8 & R8 & M8 & MG8 & FRZ8 & MS8 & KS8 & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0).
  assert (G34 : forall j, In j [3; 4]%nat -> getr R8 (reg j) = getr R (reg j)).
  { intros j Hj. rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b _ PEALPP5.KS_alpR); vm_compute; reflexivity).
    destruct Hj as [<-|[<-|[]]]; [exact RQ3| exact RQ4]. }

  assert (R8ra : getr R8 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Rra, L5.unsigned_lit by (clear - Hr1 Hr2; lia); reflexivity).
  pose proof (PMK.ret_to RSEGS fx8 R8 M8 0xb2e48 W_b2df8 r F_b2df8 eq_refl D_b2df8 R8ra Hr1 Hr2) as MSr.
  assert (MSall : msteps RSEGS (L5SAR.st fxi Ri pci MVi) (L5SAR.st fx8 R8 r M8)).
  { eapply msteps_trans; [exact MS7|]. eapply msteps_trans; [exact MS8| exact MSr]. }
  assert (MGall : mem_grows MVi M8) by (intros z Hz; apply MG8; apply MG7; exact Hz).
  assert (MO8' : L5.u8_at RSEGS M8 (op + 8) mv).
  { apply (L5C.u8_at_agree RSEGS M7v M8); [| clear - O1; lia| clear - O1 O3; lia| exact MO8].
    intros i Hi'. apply FRZ8; [clear - Hi' O1 O3; lia| clear - Hi' ApF; lia| clear - Hi' ApFL; lia| clear - Hi' ApSF; lia]. }
  assert (MO9' : L5.u8_at RSEGS M8 (op + 9) dv).
  { apply (L5C.u8_at_agree RSEGS M7v M8); [| clear - O1; lia| clear - O1 O3; lia| exact MO9].
    intros i Hi'. apply FRZ8; [clear - Hi' O1 O3; lia| clear - Hi' ApF; lia| clear - Hi' ApFL; lia| clear - Hi' ApSF; lia]. }
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 32768 (sp - 256) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PEC.owned s en k) G'
           WR (PEC.owned si eni ki) Mi mdi LKi cri Awi (fun a => op + 8 <= a < op + 10) fxi fx8 Ri pci R8 r M8 K BI).
  { intros a X'. split.
    - apply (L5SAR.fframe_client L ar (PEC.owned si eni ki ++ LBX) FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - X' Eop; lia].
    - intros O. apply (O (PMSP.o_p AD fb + 8, 8)); [unfold WR; wr_mem 0| wr_rng; clear - X' Eop; lia]. }
  { intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 10)) as [X'|X']; [left; exact X'| right; exact X']. }
  { exact MSall. }
  { exact MGall. }
  { intros a Ha Nw. unfold PMAUK.WretX, PMAUK.Wret in Nw. change (ff_bytes 1) with 128 in Nw. change (128 / 8) with 16 in Nw.
    rewrite FRZ8; [| exact Ha| intros X'; apply Nw; left; left; left; exact X'| intros X'; apply Nw; left; right; clear - X'; lia| intros X'; apply Nw; left; left; right; unfold SB; exact X'].
    apply FRZ7; [exact Ha| intros X'; apply Nw; right; exact X']. }
  { exact FL0. }
  intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict Hi Mf = M8) in VISf.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  assert (EKf : L5SAR.ek L ar LBi FF 0 0 [(op + 8, 2)] Mi Mf).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 32768 (sp - 256) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PEC.owned s en k)
             LBi LKi cri Awi Mi Mf _ [(op + 8, 2)] (fun a => op + 8 <= a < op + 10) G' HHi).
    - intros a X' O. apply (O (op + 8, 2)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X'; lia].
    - exact FZf. }
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  assert (NDi : NoDup (map fst LBi)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HHi).
  assert (MO8f : L5.u8_at RSEGS Mf (op + 8) mv).
  { apply (proj1 (L5A.u8_at_vis Hi Mf (op + 8) mv (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). rewrite VISf. exact MO8'. }
  assert (MO9f : L5.u8_at RSEGS Mf (op + 9) dv).
  { apply (proj1 (L5A.u8_at_vis Hi Mf (op + 9) dv (OVIS (op + 9) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). rewrite VISf. exact MO9'. }
  assert (WAPP8 : PMKA.wapp [(op + 8, 2)]).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG; lia. }
  assert (OUT8 : forall a n0, (a + n0 <= op + 8 \/ op + 10 <= a) -> forall i, a <= i < a + n0 -> L5.outside [(op + 8, 2)] i).
  { intros a n0 X3 i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi' Hr X3. lia. }
  assert (OUTB8 : forall q' m, In (q', m) LBi -> forall i, q' <= i < q' + m -> L5.outside [(op + 8, 2)] i).
  { intros q' m Hq i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Hr Z'; lia. }
  assert (Iq : In (PM.sr_qc (PM.p_src si), PM.CHUNK) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (Ib : In (PM.p_b si, 32 * 2 ^ PM.p_k si) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  assert (CPf : PECA.crun_preA RSEGS AD AAD EE L ar P Mf fb p Xf (set_md si mv dv) str smi eni ki ei cat).
  { destruct (BRBi _ Iq) as (Xq1 & Xq2). destruct (BRBi _ Ib) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2. unfold PM.CHUNK in Xq2.
    apply (cpre_stepA 0 0 [(op + 8, 2)] Mi Mf Y si smi eni ki ei Xf (set_md si mv dv) ei EKf WAPP8 BRBi NDi).
    + intros i Hi' Ni _. apply (OUT8 i 1); clear - Hi' Ni; lia.
    + intros q' m Hq _. exact (OUTB8 q' m Hq).
    + reflexivity. + reflexivity. + reflexivity.
    + apply (parser_md_updA Mi Mf op ois si mv dv PA).
      * clear - O1; lia.
      * clear - O1 O3; lia.
      * apply (PMKA.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
      * apply (PMKA.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB (op + 10) 374 (AOF (op + 10) 374 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
      * exact (PMKA.agsh_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB op 384 AOP).
      * pose proof PA as (_ & PDi & _). apply (L5.defined_grows Mi Mf _ _ MGf PDi).
      * exact MO8f.
      * exact MO9f.
      * exact Hmv.
      * exact Hdv.
      * exact Xq1.
      * unfold PM.CHUNK. clear - Xq2; lia.
      * apply (PMKA.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Iq). apply OUTB8. exact Iq.
      * exact Xb1.
      * clear - Xb2; lia.
      * apply (PMKA.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Ib). apply OUTB8. exact Ib.
      * intros c0 n0 p0 E0. assert (Ip : In (p0, c0) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
        apply (PMKA.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Ip). apply OUTB8. exact Ip.
    + change (PMSTA.base_okA RSEGS PMA.AD Mf). apply (PMASK.base_keep L ar C LY LBi FF 0 0 [(op + 8, 2)] Mi Mf EKf); [| exact BASE]. intros a Ha. apply (OUT8 a 1); clear - Ha O1; lia.
    + apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBi FF 0 0 [(op + 8, 2)] Mi Mf EKf ei PECSA.addrs_wf_A); [| exact ERR].
      intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
      split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply (OUT8 a 1); clear - DI O1; lia.
    + exact CLF.
    + rewrite ECF. pose proof ECS as ECS0. unfold PECA.ec_stateA in ECS0 |- *. fold oec in ECS0 |- *.
      assert (AGE4 : L5C.agree_on Mi Mf oec 4) by exact (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB oec 4 (AOF oec 4 ltac:(lia) ltac:(lia)) ltac:(apply OUT8; clear - Eop Eoec; lia))).
      assert (AGE8 : L5C.agree_on Mi Mf (oec + 8) 8) by exact (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB (oec + 8) 8 (AOF (oec + 8) 8 ltac:(lia) ltac:(lia)) ltac:(apply OUT8; clear - Eop Eoec; lia))).
      destruct (s_ec Y).
      * destruct ECS0 as (v & Hv & (ECa & ECb & ECc & ECd)). exists v. split; [exact Hv|]. split; [|split; [|split]].
        -- apply (PMF.u32_at_agree RSEGS Mi Mf); [exact AGE4| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact ECa].
        -- apply (L5C.u64_at_agree RSEGS Mi Mf); [exact AGE8| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact ECb].
        -- apply (L5.defined_grows Mi Mf _ _ MGf ECc).
        -- exact (PMKA.acc_keepA' L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB oec 16 (AOF oec 16 ltac:(lia) ltac:(lia)) ECd).
      * destruct ECS0 as (ECa & ECb & ECc & ECd). split; [|split; [|split]].
        -- apply (PMF.u32_at_agree RSEGS Mi Mf); [exact AGE4| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact ECa].
        -- apply (L5C.u64_at_agree RSEGS Mi Mf); [exact AGE8| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact ECb].
        -- apply (L5.defined_grows Mi Mf _ _ MGf ECc).
        -- exact (PMKA.acc_keepA' L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB oec 16 (AOF oec 16 ltac:(lia) ltac:(lia)) ECd).
    + rewrite ECF. exact ECI.
    + exact CP. }
  pose proof CPf as (PAf & IAf & EAf & VREFf & SKAf & BASEf & ERRf & TBOKf & CONTf & CLf & ECSf & ECIf & ACCf).
  apply (KONT fx8 R8 Mf modelf LKi Awi n (set_md si mv dv) smi eni ki ei cri).
  - apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite E2; exact (eq_sym Rsp) | rewrite G34 by inl; reflexivity
        | rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned | rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned
        | rewrite E20; apply Z_to_bv_bv_unsigned | rewrite E21; apply Z_to_bv_bv_unsigned | rewrite E22; apply Z_to_bv_bv_unsigned | rewrite E23; apply Z_to_bv_bv_unsigned
        | rewrite E24; apply Z_to_bv_bv_unsigned | rewrite E25; apply Z_to_bv_bv_unsigned | rewrite E26; apply Z_to_bv_bv_unsigned | rewrite E27; apply Z_to_bv_bv_unsigned ] |]).
    destruct Hj.
  - rewrite <- EXF. exact HALT.
  - split; [exact PAf|]. split; [exact IAf|]. split; [exact EAf|]. split; [exact SKAf|]. split; [exact BASEf|]. split; [exact ERRf|].
    split; [unfold PECA.ec_stateA in ECSf; fold oec in ECSf; destruct (s_ec Xf); [destruct ECSf as (v3 & _ & _ & _ & D16 & _); exact D16| destruct ECSf as (_ & _ & D16 & _); exact D16]|].
    rewrite <- EXF. destruct CLf as (_ & _ & _ & _ & _ & _ & _ & ZB & _). exact ZB.
  - unfold set_md. cbn [PM.p_src]. exact ST.
  - exact EIMP.
  - exact AHf.
  - apply (cred_fin Mf Xf (set_md si mv dv) smi eni ki ei cri CPf).
    unfold PMSP.credit_keep, set_md, PECA.pot_allA, PEC.credit_add, PM.pot_parser in CK |- *. cbn [PM.p_k PM.p_tb PM.p_tg fst snd] in CK |- *. exact CK.
  - exact MRTf.
  - exact INCLi.
  - exact INCAi.
  - exact AMf.
  - unfold set_md. change (PEC.owned (PM.PST mv dv (PM.p_depth si) (PM.p_src si) (PM.p_tb si) (PM.p_tg si) (PM.p_b si) (PM.p_k si) (PM.p_stk si)) eni ki) with (PEC.owned si eni ki). exact HHf.
Qed.

Lemma tail_J fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_done Y = false ->
  (s_ec Y = false -> forall (fx' : FPState) R' md', amid fx' R' Mi md' LKi Awi cri si smi eni ki ei Y ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx') RSEGS R' PEACLPD.LPHEAD Mi md') K) ->
  (s_ec Y = true -> exists n, w_halt true Y = run n p UbjRef.init) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri PEACLPD.LPJOIN Mi mdi) K.
Proof.
  intros MID DN HEAD EXIT. destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & Emo & Edn).
  destruct (s_ec Y) eqn:EC.
  -
    destruct (ec_vis1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID EC) as (v & Hv & ECv). destruct (EXIT eq_refl) as (n & EXF).
    entry_facts. frame_facts. piece_ctx MID. fold Hi in ECv, MO8, MO9. fold MVi in ECv, MO8, MO9.
    assert (Hv64 : 0 <= v < 2 ^ 64) by (clear - Hv; lia).
    pz PEALPP4.alpJe_conc fxi Ri 0 0 0 0 0 v as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _).
    apply (finish (PM.p_more si) (PM.p_done si) (w_halt true Y) n fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y fx7 R7 M7v PEACLPD.LPJOIN MID MS7 MG7).
    + intros i Hi' _. apply FRZ7. exact Hi'.
    + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpJe). vm_compute. reflexivity.
    + apply (L5C.u8_at_agree RSEGS MVi M7v); [intros i Hi'; apply FRZ7; clear - Hi' O1 O3; lia| clear - O1; lia| clear - O1 O3; lia| exact MO8].
    + apply (L5C.u8_at_agree RSEGS MVi M7v); [intros i Hi'; apply FRZ7; clear - Hi' O1 O3; lia| clear - O1; lia| clear - O1 O3; lia| exact MO9].
    + pose proof CP as (PA & _). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _). exact B1.
    + pose proof CP as (PA & _). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _). exact B2.
    + exact EXF.
    + reflexivity.
    + pose proof CP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9).
      unfold PEC.clink, set_md. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_halt PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
      split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5'|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
    + reflexivity.
  -
    pose proof (ec_vis0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID EC) as EC0.
    entry_facts. frame_facts. piece_ctx MID. fold Hi in EC0, MO8, MO9. fold MVi in EC0, MO8, MO9.
    rewrite Edn, DN in MO9. cbn [PEC.b2z] in MO9.
    pz PEALPP4.alpJ0_conc fxi Ri 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _).
    apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx7 R7 PEACLPD.LPJOIN PEACLPD.LPHEAD M7v MID MS7 FRZ7).
    + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpJ0). vm_compute. reflexivity.
    + intros mdj _ MIDj. exact (HEAD eq_refl fx7 R7 mdj MIDj).
Qed.

Lemma tail_Z fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Yc :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Yc ->
  (exists n, w_halt true (w_more false Yc) = run n p UbjRef.init) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb2e58 Mi mdi) K.
Proof.
  intros MID (n & EXF). destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & Emo & Edn).
  entry_facts. frame_facts. piece_ctx MID. fold Hi in MO8, MO9. fold MVi in MO8, MO9.
  pz PEALPP5.alpZ_conc fxi Ri 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & MZ).
  apply (finish 0 (PM.p_done si) (w_halt true (w_more false Yc)) n fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Yc fx7 R7 M7v 0xb2e58 MID MS7 MG7).
  + intros i Hi' N1. apply FRZ7; [exact Hi'| clear - N1; lia].
  + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEALPP5.KS_alpZ). vm_compute. reflexivity.
  + exact MZ.
  + apply (L5C.u8_at_agree RSEGS MVi M7v); [intros i Hi'; apply FRZ7; [clear - Hi' O1 O3; lia| clear - Hi'; lia]| clear - O1; lia| clear - O1 O3; lia| exact MO9].
  + left; reflexivity.
  + pose proof CP as (PA & _). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _). exact B2.
  + exact EXF.
  + reflexivity.
  + pose proof CP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9).
    unfold PEC.clink, set_md. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_halt w_more PEC.b2z PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
    split; [reflexivity|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [intros X' _; discriminate|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
  + reflexivity.
Qed.

Lemma arm_Mroot (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat) :
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false ->
  PEACLPD.top_mode (run i1 p UbjRef.init) = Mroot ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros MID HALT1 TG IH. set (X1 := run i1 p UbjRef.init) in *.
  pose proof POK as (BOK & BLT).
  pose proof (run_ginv p BOK i1 UbjRef.init (ginv_init p)) as GI1. fold X1 in GI1.
  pose proof (gi_run p X1 GI1 HALT1) as RI1. destruct (halted_false X1 HALT1) as (SHLT1 & SDN1 & SMR1).
  destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm1 & Cd1 & Cdp1 & Cstk1 & Cpos1 & Cestk1 & Ced1 & Cz1 & Cbad1). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm1, Cd1, Cdp1, Cstk1, Cpos1.
  destruct (s_stk X1) as [|t rr] eqn:HS1; [exfalso; pose proof (ri_shape X1 RI1) as SH0; rewrite HS1 in SH0; exact SH0|].
  pose proof (ri_ps X1 RI1) as PS1. rewrite HS1 in PS1. pose proof (Forall_inv PS1) as TOK. clear PS1.
  pose proof (ri_depth X1 RI1) as DEP1. pose proof (ri_dmax X1 RI1) as DMAX1. pose proof (ri_estk_max X1 RI1) as EMAX1. pose proof (ri_estk X1 RI1) as ESTK1.
  pose proof (ri_shape X1 RI1) as SHP1. rewrite HS1 in DEP1, ESTK1, SHP1. cbn [length] in DEP1, ESTK1.
  destruct t as [tmm tl tty ti].
  unfold PEACLPD.top_mode in TG. rewrite HS1 in TG. cbn [hd ps_mode] in TG. subst tmm.
  rewrite PEC.stk_conv_cons in Cstk1. remember (PEC.stk_conv rr) as pre eqn:Epre. subst stk1.
  assert (IM1 : mo1 = 1) by (rewrite Cm1, SMR1; reflexivity). assert (ID1 : dn1 = 0) by (rewrite Cd1, SDN1; reflexivity). clear Cm1 Cd1. subst mo1 dn1.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC1 & PB1 & PB2 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC1, PB1, PB2.
  pose proof PVEC1 as (_ & _ & _ & Hk1 & Hlen1 & _). clear PVEC1.
  rewrite length_app in Hlen1. cbn [length] in Hlen1. rewrite Nat2Z.inj_add in Hlen1. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1.

  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mroot tl tty ti)) MID eq_refl) as (TFv & TPv & TP & VIN & TB2). cbn [PM.p_b PM.p_k] in TFv, TPv, TP, VIN, TB2.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  assert (Q0i : 0 <= ti < 2 ^ 64) by (clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK; cbn [ps_mode ps_len ps_idx ps_type] in TOK; lia).
  pz PEALPP1.alpH0_conc fx1 R1 T ti 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & W3).
  assert (PTv3 : PM.pstate_at RSEGS M3v T (PEC.ps_conv (PS Maccept tl tty ti))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [exact W3|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]|].
    apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TI24]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Maccept tl tty ti) _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_rtv AD) M3v 0 4 MID HS1 Epre MS3 MG3).
  { intros a Ha Na. apply FRZ3; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv3. }
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP1.KS_alpH0). vm_compute. reflexivity. }
  clear MS3 MG3 PTv3. intros M3 md3 VIS3 HID3 MGM3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 . rename MID3 into MID.
  destruct (head_call_facts p X1 (PS Mroot tl tty ti) rr (PS Maccept tl tty ti) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia)) as (MPa1 & MPa2 & MPa3 & MPa4 & MPa5 & MPa6 & GIa & HALTa).
  pose proof MPa1 as ((_ & POSa & _) & SMa).
  pose proof (step_root p X1 _ rr HALT1 HS1 eq_refl) as STEP. rewrite (top_upd_fields _ X1 _ rr HS1) in STEP. cbn [ps_inc ps_mode_set ps_mode ps_len ps_type ps_idx] in STEP.
  pose proof (proj1 (r_tv_eff p (w_stk ((PS Maccept tl tty ti) :: rr) X1) MPa1)) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  pose proof (next_head p i1 X1 (r_tv p (w_stk ((PS Maccept tl tty ti) :: rr) X1)) BOK eq_refl HALT1 STEP DNy HLy ltac:(intros E0; exact (r_tv_more p _ SMa E0))) as NX.
  pose proof (next_head_hi p i1 X1 (r_tv p (w_stk ((PS Maccept tl tty ti) :: rr) X1)) (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  pose proof RTV as SPEC. unfold PECSA.rtv_spec, PECSPA.rtv_spec in SPEC.
  apply (call_crun unit (pa_rtv AD) 9 (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_tv p0 X0) SPEC tt 0xb2794 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 NX DNy MID4. rename MID4 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP3.alpCR0_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb2794 PEACLPD.LPJOIN M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpCR0). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  apply (tail_J _ _ _ _ _ _ _ _ _ _ _ _ _ MID5).
  - rewrite DNy. exact SDN1.
  - intros EC fx' R' md' MID'. destruct (proj1 NX EC) as (EX2 & HALT2 & MU2).
    apply (IH fx' R' M4 md' LK4 Aw4 cr4 s4 sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID'| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  - intros EC. destruct (proj1 (proj2 NX) EC) as (EX3 & _). exists (Datatypes.S i1). exact EX3.
Qed.

Lemma arm_Mval (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat) :
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false ->
  PEACLPD.top_mode (run i1 p UbjRef.init) = Mval ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros MID HALT1 TG IH. set (X1 := run i1 p UbjRef.init) in *.
  pose proof POK as (BOK & BLT).
  pose proof (run_ginv p BOK i1 UbjRef.init (ginv_init p)) as GI1. fold X1 in GI1.
  pose proof (gi_run p X1 GI1 HALT1) as RI1. destruct (halted_false X1 HALT1) as (SHLT1 & SDN1 & SMR1).
  destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm1 & Cd1 & Cdp1 & Cstk1 & Cpos1 & Cestk1 & Ced1 & Cz1 & Cbad1). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm1, Cd1, Cdp1, Cstk1, Cpos1.
  destruct (s_stk X1) as [|t rr] eqn:HS1; [exfalso; pose proof (ri_shape X1 RI1) as SH0; rewrite HS1 in SH0; exact SH0|].
  pose proof (ri_ps X1 RI1) as PS1. rewrite HS1 in PS1. pose proof (Forall_inv PS1) as TOK. clear PS1.
  pose proof (ri_depth X1 RI1) as DEP1. pose proof (ri_dmax X1 RI1) as DMAX1. pose proof (ri_estk_max X1 RI1) as EMAX1. pose proof (ri_estk X1 RI1) as ESTK1.
  pose proof (ri_shape X1 RI1) as SHP1. rewrite HS1 in DEP1, ESTK1, SHP1. cbn [length] in DEP1, ESTK1.
  destruct t as [tmm tl tty ti].
  unfold PEACLPD.top_mode in TG. rewrite HS1 in TG. cbn [hd ps_mode] in TG. subst tmm.
  rewrite PEC.stk_conv_cons in Cstk1. remember (PEC.stk_conv rr) as pre eqn:Epre. subst stk1.
  assert (IM1 : mo1 = 1) by (rewrite Cm1, SMR1; reflexivity). assert (ID1 : dn1 = 0) by (rewrite Cd1, SDN1; reflexivity). clear Cm1 Cd1. subst mo1 dn1.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC1 & PB1 & PB2 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC1, PB1, PB2.
  pose proof PVEC1 as (_ & _ & _ & Hk1 & Hlen1 & _). clear PVEC1.
  rewrite length_app in Hlen1. cbn [length] in Hlen1. rewrite Nat2Z.inj_add in Hlen1. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1.

  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mval tl tty ti)) MID eq_refl) as (TFv & TPv & TP & VIN & TB2). cbn [PM.p_b PM.p_k] in TFv, TPv, TP, VIN, TB2.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  assert (Q0i : 0 <= ti < 2 ^ 64) by (clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK; cbn [ps_mode ps_len ps_idx ps_type] in TOK; lia).
  pz PEALPP2.alpH6_conc fx1 R1 T ti 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & W3).
  assert (PTv3 : PM.pstate_at RSEGS M3v T (PEC.ps_conv (PS Mkey tl tty ti))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [exact W3|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]|].
    apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TI24]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mkey tl tty ti) _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_rtv AD) M3v 0 4 MID HS1 Epre MS3 MG3).
  { intros a Ha Na. apply FRZ3; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv3. }
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP2.KS_alpH6). vm_compute. reflexivity. }
  clear MS3 MG3 PTv3. intros M3 md3 VIS3 HID3 MGM3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 . rename MID3 into MID.
  destruct (head_call_facts p X1 (PS Mval tl tty ti) rr (PS Mkey tl tty ti) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia)) as (MPa1 & MPa2 & MPa3 & MPa4 & MPa5 & MPa6 & GIa & HALTa).
  pose proof MPa1 as ((_ & POSa & _) & SMa).
  pose proof (step_val p X1 _ rr HALT1 HS1 eq_refl) as STEP. rewrite (top_upd_fields _ X1 _ rr HS1) in STEP. cbn [ps_inc ps_mode_set ps_mode ps_len ps_type ps_idx] in STEP.
  pose proof (proj1 (r_tv_eff p (w_stk ((PS Mkey tl tty ti) :: rr) X1) MPa1)) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  pose proof (next_head p i1 X1 (r_tv p (w_stk ((PS Mkey tl tty ti) :: rr) X1)) BOK eq_refl HALT1 STEP DNy HLy ltac:(intros E0; exact (r_tv_more p _ SMa E0))) as NX.
  pose proof (next_head_hi p i1 X1 (r_tv p (w_stk ((PS Mkey tl tty ti) :: rr) X1)) (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  pose proof RTV as SPEC. unfold PECSA.rtv_spec, PECSPA.rtv_spec in SPEC.
  apply (call_crun unit (pa_rtv AD) 9 (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_tv p0 X0) SPEC tt 0xb2b20 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 NX DNy MID4. rename MID4 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP3.alpCR6_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb2b20 PEACLPD.LPJOIN M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpCR6). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  apply (tail_J _ _ _ _ _ _ _ _ _ _ _ _ _ MID5).
  - rewrite DNy. exact SDN1.
  - intros EC fx' R' md' MID'. destruct (proj1 NX EC) as (EX2 & HALT2 & MU2).
    apply (IH fx' R' M4 md' LK4 Aw4 cr4 s4 sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID'| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  - intros EC. destruct (proj1 (proj2 NX) EC) as (EX3 & _). exists (Datatypes.S i1). exact EX3.
Qed.

Lemma arm_Mival (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat) :
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false ->
  PEACLPD.top_mode (run i1 p UbjRef.init) = Mival ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros MID HALT1 TG IH. set (X1 := run i1 p UbjRef.init) in *.
  pose proof POK as (BOK & BLT).
  pose proof (run_ginv p BOK i1 UbjRef.init (ginv_init p)) as GI1. fold X1 in GI1.
  pose proof (gi_run p X1 GI1 HALT1) as RI1. destruct (halted_false X1 HALT1) as (SHLT1 & SDN1 & SMR1).
  destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm1 & Cd1 & Cdp1 & Cstk1 & Cpos1 & Cestk1 & Ced1 & Cz1 & Cbad1). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm1, Cd1, Cdp1, Cstk1, Cpos1.
  destruct (s_stk X1) as [|t rr] eqn:HS1; [exfalso; pose proof (ri_shape X1 RI1) as SH0; rewrite HS1 in SH0; exact SH0|].
  pose proof (ri_ps X1 RI1) as PS1. rewrite HS1 in PS1. pose proof (Forall_inv PS1) as TOK. clear PS1.
  pose proof (ri_depth X1 RI1) as DEP1. pose proof (ri_dmax X1 RI1) as DMAX1. pose proof (ri_estk_max X1 RI1) as EMAX1. pose proof (ri_estk X1 RI1) as ESTK1.
  pose proof (ri_shape X1 RI1) as SHP1. rewrite HS1 in DEP1, ESTK1, SHP1. cbn [length] in DEP1, ESTK1.
  destruct t as [tmm tl tty ti].
  unfold PEACLPD.top_mode in TG. rewrite HS1 in TG. cbn [hd ps_mode] in TG. subst tmm.
  rewrite PEC.stk_conv_cons in Cstk1. remember (PEC.stk_conv rr) as pre eqn:Epre. subst stk1.
  assert (IM1 : mo1 = 1) by (rewrite Cm1, SMR1; reflexivity). assert (ID1 : dn1 = 0) by (rewrite Cd1, SDN1; reflexivity). clear Cm1 Cd1. subst mo1 dn1.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC1 & PB1 & PB2 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC1, PB1, PB2.
  pose proof PVEC1 as (_ & _ & _ & Hk1 & Hlen1 & _). clear PVEC1.
  rewrite length_app in Hlen1. cbn [length] in Hlen1. rewrite Nat2Z.inj_add in Hlen1. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1.

  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mival tl tty ti)) MID eq_refl) as (TFv & TPv & TP & VIN & TB2). cbn [PM.p_b PM.p_k] in TFv, TPv, TP, VIN, TB2.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  assert (Q0i : 0 <= ti < 2 ^ 64) by (clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK; cbn [ps_mode ps_len ps_idx ps_type] in TOK; lia).
  pz PEALPP2.alpH10_conc fx1 R1 T ti 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & W3).
  assert (PTv3 : PM.pstate_at RSEGS M3v T (PEC.ps_conv (PS Mikey tl tty ti))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [exact W3|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]|].
    apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TI24]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mikey tl tty ti) _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_rtv AD) M3v 0 4 MID HS1 Epre MS3 MG3).
  { intros a Ha Na. apply FRZ3; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv3. }
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP2.KS_alpH10). vm_compute. reflexivity. }
  clear MS3 MG3 PTv3. intros M3 md3 VIS3 HID3 MGM3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 . rename MID3 into MID.
  destruct (head_call_facts p X1 (PS Mival tl tty ti) rr (PS Mikey tl tty ti) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia)) as (MPa1 & MPa2 & MPa3 & MPa4 & MPa5 & MPa6 & GIa & HALTa).
  pose proof MPa1 as ((_ & POSa & _) & SMa).
  pose proof (step_ival p X1 _ rr HALT1 HS1 eq_refl) as STEP. rewrite (top_upd_fields _ X1 _ rr HS1) in STEP. cbn [ps_inc ps_mode_set ps_mode ps_len ps_type ps_idx] in STEP.
  pose proof (proj1 (r_tv_eff p (w_stk ((PS Mikey tl tty ti) :: rr) X1) MPa1)) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  pose proof (next_head p i1 X1 (r_tv p (w_stk ((PS Mikey tl tty ti) :: rr) X1)) BOK eq_refl HALT1 STEP DNy HLy ltac:(intros E0; exact (r_tv_more p _ SMa E0))) as NX.
  pose proof (next_head_hi p i1 X1 (r_tv p (w_stk ((PS Mikey tl tty ti) :: rr) X1)) (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  pose proof RTV as SPEC. unfold PECSA.rtv_spec, PECSPA.rtv_spec in SPEC.
  apply (call_crun unit (pa_rtv AD) 9 (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_tv p0 X0) SPEC tt 0xb2b58 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 NX DNy MID4. rename MID4 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP4.alpCR10_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb2b58 PEACLPD.LPJOIN M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpCR10). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  apply (tail_J _ _ _ _ _ _ _ _ _ _ _ _ _ MID5).
  - rewrite DNy. exact SDN1.
  - intros EC fx' R' md' MID'. destruct (proj1 NX EC) as (EX2 & HALT2 & MU2).
    apply (IH fx' R' M4 md' LK4 Aw4 cr4 s4 sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID'| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  - intros EC. destruct (proj1 (proj2 NX) EC) as (EX3 & _). exists (Datatypes.S i1). exact EX3.
Qed.

Lemma arm_Mtval (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat) :
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false ->
  PEACLPD.top_mode (run i1 p UbjRef.init) = Mtval ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros MID HALT1 TG IH. set (X1 := run i1 p UbjRef.init) in *.
  pose proof POK as (BOK & BLT).
  pose proof (run_ginv p BOK i1 UbjRef.init (ginv_init p)) as GI1. fold X1 in GI1.
  pose proof (gi_run p X1 GI1 HALT1) as RI1. destruct (halted_false X1 HALT1) as (SHLT1 & SDN1 & SMR1).
  destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm1 & Cd1 & Cdp1 & Cstk1 & Cpos1 & Cestk1 & Ced1 & Cz1 & Cbad1). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm1, Cd1, Cdp1, Cstk1, Cpos1.
  destruct (s_stk X1) as [|t rr] eqn:HS1; [exfalso; pose proof (ri_shape X1 RI1) as SH0; rewrite HS1 in SH0; exact SH0|].
  pose proof (ri_ps X1 RI1) as PS1. rewrite HS1 in PS1. pose proof (Forall_inv PS1) as TOK. clear PS1.
  pose proof (ri_depth X1 RI1) as DEP1. pose proof (ri_dmax X1 RI1) as DMAX1. pose proof (ri_estk_max X1 RI1) as EMAX1. pose proof (ri_estk X1 RI1) as ESTK1.
  pose proof (ri_shape X1 RI1) as SHP1. rewrite HS1 in DEP1, ESTK1, SHP1. cbn [length] in DEP1, ESTK1.
  destruct t as [tmm tl tty ti].
  unfold PEACLPD.top_mode in TG. rewrite HS1 in TG. cbn [hd ps_mode] in TG. subst tmm.
  rewrite PEC.stk_conv_cons in Cstk1. remember (PEC.stk_conv rr) as pre eqn:Epre. subst stk1.
  assert (IM1 : mo1 = 1) by (rewrite Cm1, SMR1; reflexivity). assert (ID1 : dn1 = 0) by (rewrite Cd1, SDN1; reflexivity). clear Cm1 Cd1. subst mo1 dn1.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC1 & PB1 & PB2 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC1, PB1, PB2.
  pose proof PVEC1 as (_ & _ & _ & Hk1 & Hlen1 & _). clear PVEC1.
  rewrite length_app in Hlen1. cbn [length] in Hlen1. rewrite Nat2Z.inj_add in Hlen1. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1.

  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mtval tl tty ti)) MID eq_refl) as (TFv & TPv & TP & VIN & TB2). cbn [PM.p_b PM.p_k] in TFv, TPv, TP, VIN, TB2.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  assert (Q0i : 0 <= ti < 2 ^ 64) by (clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK; cbn [ps_mode ps_len ps_idx ps_type] in TOK; lia).
  assert (Q0y : 0 <= tty < 2 ^ 64) by (clear - TOK; unfold ps_ok in TOK; cbn [ps_type] in TOK; lia). assert (Hy : 0 <= tty <= 255) by (clear - TOK; unfold ps_ok in TOK; cbn [ps_type] in TOK; lia).
  pz PEALPP2.alpH8_conc fx1 R1 T ti tty 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y13 & _ & W3).
  assert (PTv3 : PM.pstate_at RSEGS M3v T (PEC.ps_conv (PS Mtkey tl tty ti))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [exact W3|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]|].
    apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TI24]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mtkey tl tty ti) _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_read_value AD) M3v 0 4 MID HS1 Epre MS3 MG3).
  { intros a Ha Na. apply FRZ3; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv3. }
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP2.KS_alpH8). vm_compute. reflexivity. }
  clear MS3 MG3 PTv3. intros M3 md3 VIS3 HID3 MGM3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 Y13. rename MID3 into MID.
  destruct (head_call_facts p X1 (PS Mtval tl tty ti) rr (PS Mtkey tl tty ti) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia)) as (MPa1 & MPa2 & MPa3 & MPa4 & MPa5 & MPa6 & GIa & HALTa).
  pose proof MPa1 as ((_ & POSa & _) & SMa).
  pose proof (step_tval p X1 _ rr HALT1 HS1 eq_refl) as STEP. rewrite (top_upd_fields _ X1 _ rr HS1) in STEP. cbn [ps_inc ps_mode_set ps_mode ps_len ps_type ps_idx] in STEP.
  pose proof (r_value_eff p tty (w_stk ((PS Mtkey tl tty ti) :: rr) X1) MPa1) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  pose proof (next_head p i1 X1 (r_value p tty (w_stk ((PS Mtkey tl tty ti) :: rr) X1)) BOK eq_refl HALT1 STEP DNy HLy ltac:(intros E0; exact (r_value_more p _ _ SMa E0))) as NX.
  pose proof (next_head_hi p i1 X1 (r_value p tty (w_stk ((PS Mtkey tl tty ti) :: rr) X1)) (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  pose proof RDV as SPEC. unfold PECSA.read_value_spec, PECSPA.read_value_spec in SPEC.
  apply (call_crun Z (pa_read_value AD) 8 (PECSPA.args_rv AD) PECSPA.mp_rv (fun t0 p0 X0 => r_value p0 t0 X0) SPEC tty 0xb2ba8 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args_rv. rewrite L5K.rl10, L5K.rl11, L5K.rl13, L5K.rl12. split; [exact Y10|]. split; [exact Y11|]. split; [exact Y13|]. split; [clear - TOK; unfold ps_ok in TOK; cbn [ps_type] in TOK; lia| exact Y12]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 NX DNy MID4. rename MID4 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP4.alpCV8_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb2ba8 PEACLPD.LPJOIN M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpCV8). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  apply (tail_J _ _ _ _ _ _ _ _ _ _ _ _ _ MID5).
  - rewrite DNy. exact SDN1.
  - intros EC fx' R' md' MID'. destruct (proj1 NX EC) as (EX2 & HALT2 & MU2).
    apply (IH fx' R' M4 md' LK4 Aw4 cr4 s4 sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID'| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  - intros EC. destruct (proj1 (proj2 NX) EC) as (EX3 & _). exists (Datatypes.S i1). exact EX3.
Qed.

Lemma arm_Marray (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat) :
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false ->
  PEACLPD.top_mode (run i1 p UbjRef.init) = Marray ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros MID HALT1 TG IH. set (X1 := run i1 p UbjRef.init) in *.
  pose proof POK as (BOK & BLT).
  pose proof (run_ginv p BOK i1 UbjRef.init (ginv_init p)) as GI1. fold X1 in GI1.
  pose proof (gi_run p X1 GI1 HALT1) as RI1. destruct (halted_false X1 HALT1) as (SHLT1 & SDN1 & SMR1).
  destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm1 & Cd1 & Cdp1 & Cstk1 & Cpos1 & Cestk1 & Ced1 & Cz1 & Cbad1). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm1, Cd1, Cdp1, Cstk1, Cpos1.
  destruct (s_stk X1) as [|t rr] eqn:HS1; [exfalso; pose proof (ri_shape X1 RI1) as SH0; rewrite HS1 in SH0; exact SH0|].
  pose proof (ri_ps X1 RI1) as PS1. rewrite HS1 in PS1. pose proof (Forall_inv PS1) as TOK. clear PS1.
  pose proof (ri_depth X1 RI1) as DEP1. pose proof (ri_dmax X1 RI1) as DMAX1. pose proof (ri_estk_max X1 RI1) as EMAX1. pose proof (ri_estk X1 RI1) as ESTK1.
  pose proof (ri_shape X1 RI1) as SHP1. rewrite HS1 in DEP1, ESTK1, SHP1. cbn [length] in DEP1, ESTK1.
  destruct t as [tmm tl tty ti].
  unfold PEACLPD.top_mode in TG. rewrite HS1 in TG. cbn [hd ps_mode] in TG. subst tmm.
  rewrite PEC.stk_conv_cons in Cstk1. remember (PEC.stk_conv rr) as pre eqn:Epre. subst stk1.
  assert (IM1 : mo1 = 1) by (rewrite Cm1, SMR1; reflexivity). assert (ID1 : dn1 = 0) by (rewrite Cd1, SDN1; reflexivity). clear Cm1 Cd1. subst mo1 dn1.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC1 & PB1 & PB2 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC1, PB1, PB2.
  pose proof PVEC1 as (_ & _ & _ & Hk1 & Hlen1 & _). clear PVEC1.
  rewrite length_app in Hlen1. cbn [length] in Hlen1. rewrite Nat2Z.inj_add in Hlen1. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1.

  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Marray tl tty ti)) MID eq_refl) as (TFv & TPv & TP & VIN & TB2). cbn [PM.p_b PM.p_k] in TFv, TPv, TP, VIN, TB2.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  assert (PNE : rr <> []) by (intros RR; rewrite RR in SHP1; cbn in SHP1; discriminate).
  destruct (Z_lt_le_dec ti tl) as [LT|GE].
  2: {
    assert (TIL : ti = tl) by (clear - TOK GE; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia). subst ti.
    assert (TLB : 0 <= tl <= 16777216) by (clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia).
    assert (Q0i : 0 <= tl < 2 ^ 64) by (clear - TLB; lia).
  pz PEALPP1.alpH2b_conc fx1 R1 T tl 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_end_array AD) M3v MID MS3 FRZ3).
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP1.KS_alpH2b). vm_compute. reflexivity. }
  clear MS3 FRZ3 MG3. intros md3 HID3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 PNE TLB. rename MID3 into MID.
  pose proof (step_array_end p X1 _ rr HALT1 HS1 eq_refl ltac:(cbn [ps_len ps_idx]; clear; lia)) as STEP.
  destruct (next_head_end p i1 X1 BOK eq_refl HALT1 STEP) as (EX2 & HALT2 & MU2 & NB2).
  pose proof (next_head_end_hi p i1 X1 (PESKA.spa_hb P) eq_refl STEP HBN) as HB2.
  pose proof (head_end_facts p X1 _ rr BOK GI1 HALT1 HS1 eq_refl) as MPE.
  pose proof EAR as SPEC. unfold PECSA.end_array_spec, PECSPA.end_array_spec in SPEC.
  apply (call_crun unit (pa_end_array AD) 5 (PECSPA.args3 AD) PECSPA.mp_end (fun _ p0 X0 => r_end X0) SPEC tt 0xb29dc _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact MPE. }
  { exact NB2. }
  { exact HB2. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 EX2 HALT2 MU2 MID4. rename MID4 into MID.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (_ & MO9 & _ & Edn). rewrite Edn, r_end_done, SDN1 in MO9. cbn [PEC.b2z] in MO9.
  entry_facts. frame_facts. piece_ctx MID. fold Hi in MO9. fold MVi in MO9.
  pz PEALPP4.alpN0_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb29dc PEACLPD.LPHEAD M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpN0). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  apply (IH fx5 R5 M4 md5 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID5| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2]. }

  assert (CB : 0 <= ti /\ ti < tl /\ tl <= 2 ^ 24) by (clear - TOK LT; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia).
  assert (Q0i : 0 <= ti < 2 ^ 64) by (clear - CB; lia). assert (Q0d : 0 <= tl - ti < 2 ^ 64) by (clear - CB; lia).
  assert (Hd : 1 <= tl - ti <= 16777216) by (clear - CB; lia). assert (Hi24 : 0 <= ti <= 16777215) by (clear - CB; lia).
  assert (TL8' : L5.u64_at RSEGS MVi (T + 8) (ti + (tl - ti))) by (replace (ti + (tl - ti)) with tl by (clear; lia); exact TL8).
  pz PEALPP1.alpH2a_conc fx1 R1 T ti 0 (tl - ti) 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & W3).
  assert (PTv3 : PM.pstate_at RSEGS M3v T (PEC.ps_conv (PS Marray tl tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| exact W3]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Marray tl tty (ti + 1)) _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_rtv AD) M3v 24 8 MID HS1 Epre MS3 MG3).
  { intros a Ha Na. apply FRZ3; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv3. }
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP1.KS_alpH2a). vm_compute. reflexivity. }
  clear MS3 MG3 PTv3. intros M3 md3 VIS3 HID3 MGM3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 PNE CB LT. rename MID3 into MID.
  destruct (head_call_facts p X1 (PS Marray tl tty ti) rr (PS Marray tl tty (ti + 1)) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - TOK LT; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia)) as (MPa1 & MPa2 & MPa3 & MPa4 & MPa5 & MPa6 & GIa & HALTa).
  pose proof MPa1 as ((_ & POSa & _) & SMa).
  pose proof (step_array_more p X1 _ rr HALT1 HS1 eq_refl LT) as STEP. rewrite (top_upd_fields _ X1 _ rr HS1) in STEP. cbn [ps_inc ps_mode_set ps_mode ps_len ps_type ps_idx] in STEP.
  pose proof (proj1 (r_tv_eff p (w_stk ((PS Marray tl tty (ti + 1)) :: rr) X1) MPa1)) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  pose proof (next_head p i1 X1 (r_tv p (w_stk ((PS Marray tl tty (ti + 1)) :: rr) X1)) BOK eq_refl HALT1 STEP DNy HLy ltac:(intros E0; exact (r_tv_more p _ SMa E0))) as NX.
  pose proof (next_head_hi p i1 X1 (r_tv p (w_stk ((PS Marray tl tty (ti + 1)) :: rr) X1)) (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  pose proof RTV as SPEC. unfold PECSA.rtv_spec, PECSPA.rtv_spec in SPEC.
  apply (call_crun unit (pa_rtv AD) 9 (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_tv p0 X0) SPEC tt 0xb28d4 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 NX DNy MID4. rename MID4 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP3.alpCR2_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb28d4 PEACLPD.LPJOIN M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpCR2). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  apply (tail_J _ _ _ _ _ _ _ _ _ _ _ _ _ MID5).
  - rewrite DNy. exact SDN1.
  - intros EC fx' R' md' MID'. destruct (proj1 NX EC) as (EX2 & HALT2 & MU2).
    apply (IH fx' R' M4 md' LK4 Aw4 cr4 s4 sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID'| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  - intros EC. destruct (proj1 (proj2 NX) EC) as (EX3 & _). exists (Datatypes.S i1). exact EX3.
Qed.

Lemma arm_Mtarray (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat) :
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false ->
  PEACLPD.top_mode (run i1 p UbjRef.init) = Mtarray ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros MID HALT1 TG IH. set (X1 := run i1 p UbjRef.init) in *.
  pose proof POK as (BOK & BLT).
  pose proof (run_ginv p BOK i1 UbjRef.init (ginv_init p)) as GI1. fold X1 in GI1.
  pose proof (gi_run p X1 GI1 HALT1) as RI1. destruct (halted_false X1 HALT1) as (SHLT1 & SDN1 & SMR1).
  destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm1 & Cd1 & Cdp1 & Cstk1 & Cpos1 & Cestk1 & Ced1 & Cz1 & Cbad1). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm1, Cd1, Cdp1, Cstk1, Cpos1.
  destruct (s_stk X1) as [|t rr] eqn:HS1; [exfalso; pose proof (ri_shape X1 RI1) as SH0; rewrite HS1 in SH0; exact SH0|].
  pose proof (ri_ps X1 RI1) as PS1. rewrite HS1 in PS1. pose proof (Forall_inv PS1) as TOK. clear PS1.
  pose proof (ri_depth X1 RI1) as DEP1. pose proof (ri_dmax X1 RI1) as DMAX1. pose proof (ri_estk_max X1 RI1) as EMAX1. pose proof (ri_estk X1 RI1) as ESTK1.
  pose proof (ri_shape X1 RI1) as SHP1. rewrite HS1 in DEP1, ESTK1, SHP1. cbn [length] in DEP1, ESTK1.
  destruct t as [tmm tl tty ti].
  unfold PEACLPD.top_mode in TG. rewrite HS1 in TG. cbn [hd ps_mode] in TG. subst tmm.
  rewrite PEC.stk_conv_cons in Cstk1. remember (PEC.stk_conv rr) as pre eqn:Epre. subst stk1.
  assert (IM1 : mo1 = 1) by (rewrite Cm1, SMR1; reflexivity). assert (ID1 : dn1 = 0) by (rewrite Cd1, SDN1; reflexivity). clear Cm1 Cd1. subst mo1 dn1.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC1 & PB1 & PB2 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC1, PB1, PB2.
  pose proof PVEC1 as (_ & _ & _ & Hk1 & Hlen1 & _). clear PVEC1.
  rewrite length_app in Hlen1. cbn [length] in Hlen1. rewrite Nat2Z.inj_add in Hlen1. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1.

  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mtarray tl tty ti)) MID eq_refl) as (TFv & TPv & TP & VIN & TB2). cbn [PM.p_b PM.p_k] in TFv, TPv, TP, VIN, TB2.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  assert (PNE : rr <> []) by (intros RR; rewrite RR in SHP1; cbn in SHP1; discriminate).
  destruct (Z_lt_le_dec ti tl) as [LT|GE].
  2: {
    assert (TIL : ti = tl) by (clear - TOK GE; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia). subst ti.
    assert (TLB : 0 <= tl <= 16777216) by (clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia).
    assert (Q0i : 0 <= tl < 2 ^ 64) by (clear - TLB; lia).
  pz PEALPP1.alpH4b_conc fx1 R1 T tl 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_end_array AD) M3v MID MS3 FRZ3).
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP1.KS_alpH4b). vm_compute. reflexivity. }
  clear MS3 FRZ3 MG3. intros md3 HID3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 PNE TLB. rename MID3 into MID.
  pose proof (step_tarray_end p X1 _ rr HALT1 HS1 eq_refl ltac:(cbn [ps_len ps_idx]; clear; lia)) as STEP.
  destruct (next_head_end p i1 X1 BOK eq_refl HALT1 STEP) as (EX2 & HALT2 & MU2 & NB2).
  pose proof (next_head_end_hi p i1 X1 (PESKA.spa_hb P) eq_refl STEP HBN) as HB2.
  pose proof (head_end_facts p X1 _ rr BOK GI1 HALT1 HS1 eq_refl) as MPE.
  pose proof EAR as SPEC. unfold PECSA.end_array_spec, PECSPA.end_array_spec in SPEC.
  apply (call_crun unit (pa_end_array AD) 5 (PECSPA.args3 AD) PECSPA.mp_end (fun _ p0 X0 => r_end X0) SPEC tt 0xb29dc _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact MPE. }
  { exact NB2. }
  { exact HB2. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 EX2 HALT2 MU2 MID4. rename MID4 into MID.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (_ & MO9 & _ & Edn). rewrite Edn, r_end_done, SDN1 in MO9. cbn [PEC.b2z] in MO9.
  entry_facts. frame_facts. piece_ctx MID. fold Hi in MO9. fold MVi in MO9.
  pz PEALPP4.alpN0_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb29dc PEACLPD.LPHEAD M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpN0). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  apply (IH fx5 R5 M4 md5 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID5| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2]. }

  assert (CB : 0 <= ti /\ ti < tl /\ tl <= 2 ^ 24) by (clear - TOK LT; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia).
  assert (Q0i : 0 <= ti < 2 ^ 64) by (clear - CB; lia). assert (Q0d : 0 <= tl - ti < 2 ^ 64) by (clear - CB; lia).
  assert (Hd : 1 <= tl - ti <= 16777216) by (clear - CB; lia). assert (Hi24 : 0 <= ti <= 16777215) by (clear - CB; lia).
  assert (TL8' : L5.u64_at RSEGS MVi (T + 8) (ti + (tl - ti))) by (replace (ti + (tl - ti)) with tl by (clear; lia); exact TL8).
  assert (Q0y : 0 <= tty < 2 ^ 64) by (clear - TOK; unfold ps_ok in TOK; cbn [ps_type] in TOK; lia). assert (Hy : 0 <= tty <= 255) by (clear - TOK; unfold ps_ok in TOK; cbn [ps_type] in TOK; lia).
  pz PEALPP1.alpH4a_conc fx1 R1 T ti tty (tl - ti) 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y13 & _ & W3).
  assert (PTv3 : PM.pstate_at RSEGS M3v T (PEC.ps_conv (PS Mtarray tl tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| exact W3]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mtarray tl tty (ti + 1)) _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_read_value AD) M3v 24 8 MID HS1 Epre MS3 MG3).
  { intros a Ha Na. apply FRZ3; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv3. }
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP1.KS_alpH4a). vm_compute. reflexivity. }
  clear MS3 MG3 PTv3. intros M3 md3 VIS3 HID3 MGM3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 Y13 PNE CB LT. rename MID3 into MID.
  destruct (head_call_facts p X1 (PS Mtarray tl tty ti) rr (PS Mtarray tl tty (ti + 1)) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - TOK LT; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia)) as (MPa1 & MPa2 & MPa3 & MPa4 & MPa5 & MPa6 & GIa & HALTa).
  pose proof MPa1 as ((_ & POSa & _) & SMa).
  pose proof (step_tarray_more p X1 _ rr HALT1 HS1 eq_refl LT) as STEP. rewrite (top_upd_fields _ X1 _ rr HS1) in STEP. cbn [ps_inc ps_mode_set ps_mode ps_len ps_type ps_idx] in STEP.
  pose proof (r_value_eff p tty (w_stk ((PS Mtarray tl tty (ti + 1)) :: rr) X1) MPa1) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  pose proof (next_head p i1 X1 (r_value p tty (w_stk ((PS Mtarray tl tty (ti + 1)) :: rr) X1)) BOK eq_refl HALT1 STEP DNy HLy ltac:(intros E0; exact (r_value_more p _ _ SMa E0))) as NX.
  pose proof (next_head_hi p i1 X1 (r_value p tty (w_stk ((PS Mtarray tl tty (ti + 1)) :: rr) X1)) (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  pose proof RDV as SPEC. unfold PECSA.read_value_spec, PECSPA.read_value_spec in SPEC.
  apply (call_crun Z (pa_read_value AD) 8 (PECSPA.args_rv AD) PECSPA.mp_rv (fun t0 p0 X0 => r_value p0 t0 X0) SPEC tty 0xb2818 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args_rv. rewrite L5K.rl10, L5K.rl11, L5K.rl13, L5K.rl12. split; [exact Y10|]. split; [exact Y11|]. split; [exact Y13|]. split; [clear - TOK; unfold ps_ok in TOK; cbn [ps_type] in TOK; lia| exact Y12]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 NX DNy MID4. rename MID4 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP4.alpCV4_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb2818 PEACLPD.LPJOIN M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpCV4). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  apply (tail_J _ _ _ _ _ _ _ _ _ _ _ _ _ MID5).
  - rewrite DNy. exact SDN1.
  - intros EC fx' R' md' MID'. destruct (proj1 NX EC) as (EX2 & HALT2 & MU2).
    apply (IH fx' R' M4 md' LK4 Aw4 cr4 s4 sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID'| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  - intros EC. destruct (proj1 (proj2 NX) EC) as (EX3 & _). exists (Datatypes.S i1). exact EX3.
Qed.

Lemma arm_Mkey (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat) :
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false ->
  PEACLPD.top_mode (run i1 p UbjRef.init) = Mkey ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros MID HALT1 TG IH. set (X1 := run i1 p UbjRef.init) in *.
  pose proof POK as (BOK & BLT).
  pose proof (run_ginv p BOK i1 UbjRef.init (ginv_init p)) as GI1. fold X1 in GI1.
  pose proof (gi_run p X1 GI1 HALT1) as RI1. destruct (halted_false X1 HALT1) as (SHLT1 & SDN1 & SMR1).
  destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm1 & Cd1 & Cdp1 & Cstk1 & Cpos1 & Cestk1 & Ced1 & Cz1 & Cbad1). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm1, Cd1, Cdp1, Cstk1, Cpos1.
  destruct (s_stk X1) as [|t rr] eqn:HS1; [exfalso; pose proof (ri_shape X1 RI1) as SH0; rewrite HS1 in SH0; exact SH0|].
  pose proof (ri_ps X1 RI1) as PS1. rewrite HS1 in PS1. pose proof (Forall_inv PS1) as TOK. clear PS1.
  pose proof (ri_depth X1 RI1) as DEP1. pose proof (ri_dmax X1 RI1) as DMAX1. pose proof (ri_estk_max X1 RI1) as EMAX1. pose proof (ri_estk X1 RI1) as ESTK1.
  pose proof (ri_shape X1 RI1) as SHP1. rewrite HS1 in DEP1, ESTK1, SHP1. cbn [length] in DEP1, ESTK1.
  destruct t as [tmm tl tty ti].
  unfold PEACLPD.top_mode in TG. rewrite HS1 in TG. cbn [hd ps_mode] in TG. subst tmm.
  rewrite PEC.stk_conv_cons in Cstk1. remember (PEC.stk_conv rr) as pre eqn:Epre. subst stk1.
  assert (IM1 : mo1 = 1) by (rewrite Cm1, SMR1; reflexivity). assert (ID1 : dn1 = 0) by (rewrite Cd1, SDN1; reflexivity). clear Cm1 Cd1. subst mo1 dn1.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC1 & PB1 & PB2 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC1, PB1, PB2.
  pose proof PVEC1 as (_ & _ & _ & Hk1 & Hlen1 & _). clear PVEC1.
  rewrite length_app in Hlen1. cbn [length] in Hlen1. rewrite Nat2Z.inj_add in Hlen1. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1.

  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mkey tl tty ti)) MID eq_refl) as (TFv & TPv & TP & VIN & TB2). cbn [PM.p_b PM.p_k] in TFv, TPv, TP, VIN, TB2.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  assert (PNE : rr <> []) by (intros RR; rewrite RR in SHP1; cbn in SHP1; discriminate).
  destruct (Z_lt_le_dec ti tl) as [LT|GE].
  2: {
    assert (TIL : ti = tl) by (clear - TOK GE; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia). subst ti.
    assert (TLB : 0 <= tl <= 16777216) by (clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia).
    assert (Q0i : 0 <= tl < 2 ^ 64) by (clear - TLB; lia).
  pz PEALPP1.alpH5b_conc fx1 R1 T tl 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_end_object AD) M3v MID MS3 FRZ3).
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP1.KS_alpH5b). vm_compute. reflexivity. }
  clear MS3 FRZ3 MG3. intros md3 HID3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 PNE TLB. rename MID3 into MID.
  pose proof (step_key_end p X1 _ rr HALT1 HS1 eq_refl ltac:(cbn [ps_len ps_idx]; clear; lia)) as STEP.
  destruct (next_head_end p i1 X1 BOK eq_refl HALT1 STEP) as (EX2 & HALT2 & MU2 & NB2).
  pose proof (next_head_end_hi p i1 X1 (PESKA.spa_hb P) eq_refl STEP HBN) as HB2.
  pose proof (head_end_facts p X1 _ rr BOK GI1 HALT1 HS1 eq_refl) as MPE.
  pose proof EOB as SPEC. unfold PECSA.end_object_spec, PECSPA.end_object_spec in SPEC.
  apply (call_crun unit (pa_end_object AD) 5 (PECSPA.args3 AD) PECSPA.mp_end (fun _ p0 X0 => r_end X0) SPEC tt 0xb2bd0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact MPE. }
  { exact NB2. }
  { exact HB2. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 EX2 HALT2 MU2 MID4. rename MID4 into MID.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (_ & MO9 & _ & Edn). rewrite Edn, r_end_done, SDN1 in MO9. cbn [PEC.b2z] in MO9.
  entry_facts. frame_facts. piece_ctx MID. fold Hi in MO9. fold MVi in MO9.
  pz PEALPP4.alpM0_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb2bd0 PEACLPD.LPHEAD M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpM0). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  apply (IH fx5 R5 M4 md5 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID5| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2]. }

  assert (CB : 0 <= ti /\ ti < tl /\ tl <= 2 ^ 24) by (clear - TOK LT; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia).
  assert (Q0i : 0 <= ti < 2 ^ 64) by (clear - CB; lia). assert (Q0d : 0 <= tl - ti < 2 ^ 64) by (clear - CB; lia).
  assert (Hd : 1 <= tl - ti <= 16777216) by (clear - CB; lia). assert (Hi24 : 0 <= ti <= 16777215) by (clear - CB; lia).
  assert (TL8' : L5.u64_at RSEGS MVi (T + 8) (ti + (tl - ti))) by (replace (ti + (tl - ti)) with tl by (clear; lia); exact TL8).
  pz PEALPP1.alpH5a_conc fx1 R1 T ti 0 (tl - ti) 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & W3).
  assert (PTv3 : PM.pstate_at RSEGS M3v T (PEC.ps_conv (PS Mkey tl tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| exact W3]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mkey tl tty (ti + 1)) _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_read_key AD) M3v 24 8 MID HS1 Epre MS3 MG3).
  { intros a Ha Na. apply FRZ3; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv3. }
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP1.KS_alpH5a). vm_compute. reflexivity. }
  clear MS3 MG3 PTv3. intros M3 md3 VIS3 HID3 MGM3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 PNE CB LT. rename MID3 into MID.
  destruct (head_call_facts p X1 (PS Mkey tl tty ti) rr (PS Mkey tl tty (ti + 1)) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - TOK LT; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia)) as (MPa1 & MPa2 & MPa3 & MPa4 & MPa5 & MPa6 & GIa & HALTa).
  pose proof MPa1 as ((_ & POSa & _) & SMa).
  pose proof (step_key_more p X1 _ rr HALT1 HS1 eq_refl LT) as STEP. rewrite (top_upd_fields ps_inc X1 _ rr HS1) in STEP. cbv zeta in STEP. cbn [ps_inc ps_mode ps_len ps_type ps_idx] in STEP.
  pose proof (r_key_eff p (w_stk ((PS Mkey tl tty (ti + 1)) :: rr) X1) (proj1 MPa1)) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  pose proof (next_head_key p i1 X1 (r_key p (w_stk ((PS Mkey tl tty (ti + 1)) :: rr) X1)) Mval BOK eq_refl HALT1 STEP DNy HLy (r_key_more p _)) as NX.
  pose proof (next_head_key_hi p i1 X1 (r_key p (w_stk ((PS Mkey tl tty (ti + 1)) :: rr) X1)) Mval (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  assert (HSY : s_stk (r_key p (w_stk ((PS Mkey tl tty (ti + 1)) :: rr) X1)) = (PS Mkey tl tty (ti + 1)) :: rr) by (rewrite r_key_stk; reflexivity).
  pose proof RDK as SPEC. unfold PECSA.read_key_spec, PECSPA.read_key_spec in SPEC.
  apply (call_crun unit (pa_read_key AD) 7 (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_key p0 X0) SPEC tt 0xb2ac4 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 NX DNy HSY MID4. rename MID4 into MID.
  destruct (s_ec (r_key p (w_stk ((PS Mkey tl tty (ti + 1)) :: rr) X1))) eqn:ECY.
  {
    destruct (proj1 (proj2 NX) eq_refl) as (EX3 & _).
  destruct (ec_vis1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECY) as (v & Hv & ECv). destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _).
  entry_facts. frame_facts. piece_ctx MID. fold Hi in ECv, MO8, MO9. fold MVi in ECv, MO8, MO9.
  assert (Hv64 : 0 <= v < 2 ^ 64) by (clear - Hv; lia).
  pz PEALPP5.alpK5e_conc fx4 R4 0 0 0 0 0 v as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (finish (PM.p_more s4) (PM.p_done s4) (w_halt true (r_key p (w_stk ((PS Mkey tl tty (ti + 1)) :: rr) X1))) (Datatypes.S i1) _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 M5v 0xb2ac4 MID MS5 MG5).
  + intros i Hi' _. apply FRZ5. exact Hi'.
  + intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP5.KS_alpK5e). vm_compute. reflexivity.
  + apply (L5C.u8_at_agree RSEGS MVi M5v); [intros i Hi'; apply FRZ5; clear - Hi' O1 O3; lia| clear - O1; lia| clear - O1 O3; lia| exact MO8].
  + apply (L5C.u8_at_agree RSEGS MVi M5v); [intros i Hi'; apply FRZ5; clear - Hi' O1 O3; lia| clear - O1; lia| clear - O1 O3; lia| exact MO9].
  + pose proof CP as (PA & _). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _). exact B1.
  + pose proof CP as (PA & _). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _). exact B2.
  + exact EX3.
  + reflexivity.
  + pose proof CP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9).
    unfold PEC.clink, set_md. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_halt PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5'|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
  + reflexivity.
  }

  destruct (proj1 NX eq_refl) as (EX2 & HALT2 & MU2 & _).
  rewrite (top_upd_fields (ps_mode_set Mval) (r_key p (w_stk ((PS Mkey tl tty (ti + 1)) :: rr) X1)) _ rr HSY) in EX2, HALT2, MU2. cbn [ps_mode_set ps_mode ps_len ps_type ps_idx] in EX2, HALT2, MU2.
  destruct s4 as [mo4 dn4 dp4 src4 tb4 tg4 vb4 vk4 stk4].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm4 & Cd4 & Cdp4 & Cstk4 & Cpos4 & Cestk4 & Ced4 & Cz4 & Cbad4). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm4, Cd4, Cdp4, Cstk4, Cpos4.
  rewrite HSY, PEC.stk_conv_cons, <- Epre in Cstk4. subst stk4.
  assert (IM4 : mo4 = 1) by (rewrite Cm4, (r_key_more p _ ECY); reflexivity). assert (ID4 : dn4 = 0) by (rewrite Cd4, DNy; cbn [s_done w_stk]; rewrite SDN1; reflexivity). clear Cm4 Cd4. subst mo4 dn4.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC4 & PB14 & PB24 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC4, PB14, PB24.
  pose proof PVEC4 as (_ & _ & _ & Hk4 & Hlen4 & _). clear PVEC4.
  rewrite length_app in Hlen4. cbn [length] in Hlen4. rewrite Nat2Z.inj_add in Hlen4. cbn [Z.of_nat Pos.of_succ_nat] in Hlen4.
  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mkey tl tty (ti + 1))) MID eq_refl) as (TFv & TPv & TP4 & VIN4 & TB24). cbn [PM.p_b PM.p_k] in TFv, TPv, TP4, VIN4, TB24.
  set (T := vb4 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  pose proof (ec_vis0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECY) as EC0. fold Hi in EC0. fold MVi in EC0.
  pz PEALPP5.alpK50_conc fx4 R4 T 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _ & _ & W5).
  assert (PTv5 : PM.pstate_at RSEGS M5v T (PEC.ps_conv (PS Mval tl tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [exact W5|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]|].
    apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TI24]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mval tl tty (ti + 1)) _ _ _ _ _ fx5 R5 0xb2ac4 PEACLPD.LPHEAD M5v 0 4 MID HSY Epre MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv5. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP5.KS_alpK50). vm_compute. reflexivity. }
  clear MS5 MG5 PTv5. intros M5 md5 VIS5 HID5 MGM5 MID5.
  eapply (IH fx5 R5 M5 md5 LK4 Aw4 cr4 _ sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID5| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
Qed.

Lemma arm_Mtkey (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat) :
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false ->
  PEACLPD.top_mode (run i1 p UbjRef.init) = Mtkey ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros MID HALT1 TG IH. set (X1 := run i1 p UbjRef.init) in *.
  pose proof POK as (BOK & BLT).
  pose proof (run_ginv p BOK i1 UbjRef.init (ginv_init p)) as GI1. fold X1 in GI1.
  pose proof (gi_run p X1 GI1 HALT1) as RI1. destruct (halted_false X1 HALT1) as (SHLT1 & SDN1 & SMR1).
  destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm1 & Cd1 & Cdp1 & Cstk1 & Cpos1 & Cestk1 & Ced1 & Cz1 & Cbad1). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm1, Cd1, Cdp1, Cstk1, Cpos1.
  destruct (s_stk X1) as [|t rr] eqn:HS1; [exfalso; pose proof (ri_shape X1 RI1) as SH0; rewrite HS1 in SH0; exact SH0|].
  pose proof (ri_ps X1 RI1) as PS1. rewrite HS1 in PS1. pose proof (Forall_inv PS1) as TOK. clear PS1.
  pose proof (ri_depth X1 RI1) as DEP1. pose proof (ri_dmax X1 RI1) as DMAX1. pose proof (ri_estk_max X1 RI1) as EMAX1. pose proof (ri_estk X1 RI1) as ESTK1.
  pose proof (ri_shape X1 RI1) as SHP1. rewrite HS1 in DEP1, ESTK1, SHP1. cbn [length] in DEP1, ESTK1.
  destruct t as [tmm tl tty ti].
  unfold PEACLPD.top_mode in TG. rewrite HS1 in TG. cbn [hd ps_mode] in TG. subst tmm.
  rewrite PEC.stk_conv_cons in Cstk1. remember (PEC.stk_conv rr) as pre eqn:Epre. subst stk1.
  assert (IM1 : mo1 = 1) by (rewrite Cm1, SMR1; reflexivity). assert (ID1 : dn1 = 0) by (rewrite Cd1, SDN1; reflexivity). clear Cm1 Cd1. subst mo1 dn1.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC1 & PB1 & PB2 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC1, PB1, PB2.
  pose proof PVEC1 as (_ & _ & _ & Hk1 & Hlen1 & _). clear PVEC1.
  rewrite length_app in Hlen1. cbn [length] in Hlen1. rewrite Nat2Z.inj_add in Hlen1. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1.

  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mtkey tl tty ti)) MID eq_refl) as (TFv & TPv & TP & VIN & TB2). cbn [PM.p_b PM.p_k] in TFv, TPv, TP, VIN, TB2.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  assert (PNE : rr <> []) by (intros RR; rewrite RR in SHP1; cbn in SHP1; discriminate).
  destruct (Z_lt_le_dec ti tl) as [LT|GE].
  2: {
    assert (TIL : ti = tl) by (clear - TOK GE; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia). subst ti.
    assert (TLB : 0 <= tl <= 16777216) by (clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia).
    assert (Q0i : 0 <= tl < 2 ^ 64) by (clear - TLB; lia).
  pz PEALPP2.alpH7b_conc fx1 R1 T tl 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_end_object AD) M3v MID MS3 FRZ3).
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP2.KS_alpH7b). vm_compute. reflexivity. }
  clear MS3 FRZ3 MG3. intros md3 HID3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 PNE TLB. rename MID3 into MID.
  pose proof (step_tkey_end p X1 _ rr HALT1 HS1 eq_refl ltac:(cbn [ps_len ps_idx]; clear; lia)) as STEP.
  destruct (next_head_end p i1 X1 BOK eq_refl HALT1 STEP) as (EX2 & HALT2 & MU2 & NB2).
  pose proof (next_head_end_hi p i1 X1 (PESKA.spa_hb P) eq_refl STEP HBN) as HB2.
  pose proof (head_end_facts p X1 _ rr BOK GI1 HALT1 HS1 eq_refl) as MPE.
  pose proof EOB as SPEC. unfold PECSA.end_object_spec, PECSPA.end_object_spec in SPEC.
  apply (call_crun unit (pa_end_object AD) 5 (PECSPA.args3 AD) PECSPA.mp_end (fun _ p0 X0 => r_end X0) SPEC tt 0xb2bd0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact MPE. }
  { exact NB2. }
  { exact HB2. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 EX2 HALT2 MU2 MID4. rename MID4 into MID.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (_ & MO9 & _ & Edn). rewrite Edn, r_end_done, SDN1 in MO9. cbn [PEC.b2z] in MO9.
  entry_facts. frame_facts. piece_ctx MID. fold Hi in MO9. fold MVi in MO9.
  pz PEALPP4.alpM0_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb2bd0 PEACLPD.LPHEAD M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpM0). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  apply (IH fx5 R5 M4 md5 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID5| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2]. }

  assert (CB : 0 <= ti /\ ti < tl /\ tl <= 2 ^ 24) by (clear - TOK LT; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia).
  assert (Q0i : 0 <= ti < 2 ^ 64) by (clear - CB; lia). assert (Q0d : 0 <= tl - ti < 2 ^ 64) by (clear - CB; lia).
  assert (Hd : 1 <= tl - ti <= 16777216) by (clear - CB; lia). assert (Hi24 : 0 <= ti <= 16777215) by (clear - CB; lia).
  assert (TL8' : L5.u64_at RSEGS MVi (T + 8) (ti + (tl - ti))) by (replace (ti + (tl - ti)) with tl by (clear; lia); exact TL8).
  pz PEALPP2.alpH7a_conc fx1 R1 T ti 0 (tl - ti) 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & W3).
  assert (PTv3 : PM.pstate_at RSEGS M3v T (PEC.ps_conv (PS Mtkey tl tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M3v); [intros a Ha; apply FRZ3; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| exact W3]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mtkey tl tty (ti + 1)) _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_read_key AD) M3v 24 8 MID HS1 Epre MS3 MG3).
  { intros a Ha Na. apply FRZ3; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv3. }
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP2.KS_alpH7a). vm_compute. reflexivity. }
  clear MS3 MG3 PTv3. intros M3 md3 VIS3 HID3 MGM3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 Y11 Y12 PNE CB LT. rename MID3 into MID.
  destruct (head_call_facts p X1 (PS Mtkey tl tty ti) rr (PS Mtkey tl tty (ti + 1)) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - TOK LT; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia)) as (MPa1 & MPa2 & MPa3 & MPa4 & MPa5 & MPa6 & GIa & HALTa).
  pose proof MPa1 as ((_ & POSa & _) & SMa).
  pose proof (step_tkey_more p X1 _ rr HALT1 HS1 eq_refl LT) as STEP. rewrite (top_upd_fields ps_inc X1 _ rr HS1) in STEP. cbv zeta in STEP. cbn [ps_inc ps_mode ps_len ps_type ps_idx] in STEP.
  pose proof (r_key_eff p (w_stk ((PS Mtkey tl tty (ti + 1)) :: rr) X1) (proj1 MPa1)) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  pose proof (next_head_key p i1 X1 (r_key p (w_stk ((PS Mtkey tl tty (ti + 1)) :: rr) X1)) Mtval BOK eq_refl HALT1 STEP DNy HLy (r_key_more p _)) as NX.
  pose proof (next_head_key_hi p i1 X1 (r_key p (w_stk ((PS Mtkey tl tty (ti + 1)) :: rr) X1)) Mtval (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  assert (HSY : s_stk (r_key p (w_stk ((PS Mtkey tl tty (ti + 1)) :: rr) X1)) = (PS Mtkey tl tty (ti + 1)) :: rr) by (rewrite r_key_stk; reflexivity).
  pose proof RDK as SPEC. unfold PECSA.read_key_spec, PECSPA.read_key_spec in SPEC.
  apply (call_crun unit (pa_read_key AD) 7 (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_key p0 X0) SPEC tt 0xb2990 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4 MID4.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 NX DNy HSY MID4. rename MID4 into MID.
  destruct (s_ec (r_key p (w_stk ((PS Mtkey tl tty (ti + 1)) :: rr) X1))) eqn:ECY.
  {
    destruct (proj1 (proj2 NX) eq_refl) as (EX3 & _).
  destruct (ec_vis1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECY) as (v & Hv & ECv). destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _).
  entry_facts. frame_facts. piece_ctx MID. fold Hi in ECv, MO8, MO9. fold MVi in ECv, MO8, MO9.
  assert (Hv64 : 0 <= v < 2 ^ 64) by (clear - Hv; lia).
  pz PEALPP5.alpK7e_conc fx4 R4 0 0 0 0 0 v as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _).
  apply (finish (PM.p_more s4) (PM.p_done s4) (w_halt true (r_key p (w_stk ((PS Mtkey tl tty (ti + 1)) :: rr) X1))) (Datatypes.S i1) _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 M5v 0xb2990 MID MS5 MG5).
  + intros i Hi' _. apply FRZ5. exact Hi'.
  + intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP5.KS_alpK7e). vm_compute. reflexivity.
  + apply (L5C.u8_at_agree RSEGS MVi M5v); [intros i Hi'; apply FRZ5; clear - Hi' O1 O3; lia| clear - O1; lia| clear - O1 O3; lia| exact MO8].
  + apply (L5C.u8_at_agree RSEGS MVi M5v); [intros i Hi'; apply FRZ5; clear - Hi' O1 O3; lia| clear - O1; lia| clear - O1 O3; lia| exact MO9].
  + pose proof CP as (PA & _). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _). exact B1.
  + pose proof CP as (PA & _). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _). exact B2.
  + exact EX3.
  + reflexivity.
  + pose proof CP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9).
    unfold PEC.clink, set_md. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_halt PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5'|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
  + reflexivity.
  }

  destruct (proj1 NX eq_refl) as (EX2 & HALT2 & MU2 & _).
  rewrite (top_upd_fields (ps_mode_set Mtval) (r_key p (w_stk ((PS Mtkey tl tty (ti + 1)) :: rr) X1)) _ rr HSY) in EX2, HALT2, MU2. cbn [ps_mode_set ps_mode ps_len ps_type ps_idx] in EX2, HALT2, MU2.
  destruct s4 as [mo4 dn4 dp4 src4 tb4 tg4 vb4 vk4 stk4].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm4 & Cd4 & Cdp4 & Cstk4 & Cpos4 & Cestk4 & Ced4 & Cz4 & Cbad4). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm4, Cd4, Cdp4, Cstk4, Cpos4.
  rewrite HSY, PEC.stk_conv_cons, <- Epre in Cstk4. subst stk4.
  assert (IM4 : mo4 = 1) by (rewrite Cm4, (r_key_more p _ ECY); reflexivity). assert (ID4 : dn4 = 0) by (rewrite Cd4, DNy; cbn [s_done w_stk]; rewrite SDN1; reflexivity). clear Cm4 Cd4. subst mo4 dn4.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC4 & PB14 & PB24 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC4, PB14, PB24.
  pose proof PVEC4 as (_ & _ & _ & Hk4 & Hlen4 & _). clear PVEC4.
  rewrite length_app in Hlen4. cbn [length] in Hlen4. rewrite Nat2Z.inj_add in Hlen4. cbn [Z.of_nat Pos.of_succ_nat] in Hlen4.
  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mtkey tl tty (ti + 1))) MID eq_refl) as (TFv & TPv & TP4 & VIN4 & TB24). cbn [PM.p_b PM.p_k] in TFv, TPv, TP4, VIN4, TB24.
  set (T := vb4 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  pose proof (ec_vis0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECY) as EC0. fold Hi in EC0. fold MVi in EC0.
  pz PEALPP5.alpK70_conc fx4 R4 T 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _ & _ & W5).
  assert (PTv5 : PM.pstate_at RSEGS M5v T (PEC.ps_conv (PS Mtval tl tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [exact W5|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]|].
    apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TI24]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mtval tl tty (ti + 1)) _ _ _ _ _ fx5 R5 0xb2990 PEACLPD.LPHEAD M5v 0 4 MID HSY Epre MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv5. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP5.KS_alpK70). vm_compute. reflexivity. }
  clear MS5 MG5 PTv5. intros M5 md5 VIS5 HID5 MGM5 MID5.
  eapply (IH fx5 R5 M5 md5 LK4 Aw4 cr4 _ sm4 en4 k4 e4 (Datatypes.S i1)); [rewrite <- EX2; exact MID5| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
Qed.

Lemma arm_Miarray (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat) :
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false ->
  PEACLPD.top_mode (run i1 p UbjRef.init) = Miarray ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros MID HALT1 TG IH. set (X1 := run i1 p UbjRef.init) in *.
  pose proof POK as (BOK & BLT).
  pose proof (run_ginv p BOK i1 UbjRef.init (ginv_init p)) as GI1. fold X1 in GI1.
  pose proof (gi_run p X1 GI1 HALT1) as RI1. destruct (halted_false X1 HALT1) as (SHLT1 & SDN1 & SMR1).
  destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm1 & Cd1 & Cdp1 & Cstk1 & Cpos1 & Cestk1 & Ced1 & Cz1 & Cbad1). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm1, Cd1, Cdp1, Cstk1, Cpos1.
  destruct (s_stk X1) as [|t rr] eqn:HS1; [exfalso; pose proof (ri_shape X1 RI1) as SH0; rewrite HS1 in SH0; exact SH0|].
  pose proof (ri_ps X1 RI1) as PS1. rewrite HS1 in PS1. pose proof (Forall_inv PS1) as TOK. clear PS1.
  pose proof (ri_depth X1 RI1) as DEP1. pose proof (ri_dmax X1 RI1) as DMAX1. pose proof (ri_estk_max X1 RI1) as EMAX1. pose proof (ri_estk X1 RI1) as ESTK1.
  pose proof (ri_shape X1 RI1) as SHP1. rewrite HS1 in DEP1, ESTK1, SHP1. cbn [length] in DEP1, ESTK1.
  destruct t as [tmm tl tty ti].
  unfold PEACLPD.top_mode in TG. rewrite HS1 in TG. cbn [hd ps_mode] in TG. subst tmm.
  rewrite PEC.stk_conv_cons in Cstk1. remember (PEC.stk_conv rr) as pre eqn:Epre. subst stk1.
  assert (IM1 : mo1 = 1) by (rewrite Cm1, SMR1; reflexivity). assert (ID1 : dn1 = 0) by (rewrite Cd1, SDN1; reflexivity). clear Cm1 Cd1. subst mo1 dn1.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC1 & PB1 & PB2 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC1, PB1, PB2.
  pose proof PVEC1 as (_ & _ & _ & Hk1 & Hlen1 & _). clear PVEC1.
  rewrite length_app in Hlen1. cbn [length] in Hlen1. rewrite Nat2Z.inj_add in Hlen1. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1.

  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Miarray tl tty ti)) MID eq_refl) as (TFv & TPv & TP & VIN & TB2). cbn [PM.p_b PM.p_k] in TFv, TPv, TP, VIN, TB2.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  assert (PNE : rr <> []) by (intros RR; rewrite RR in SHP1; cbn in SHP1; discriminate).
  assert (IB : tl = 0 /\ 0 <= ti <= 16777216) by (clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia).
  destruct IB as (TL0 & IB). subst tl. assert (Q0i : 0 <= ti < 2 ^ 64) by (clear - IB; lia).
  pose proof (gi_pos p X1 GI1) as GP1.
  pz PEALPP1.alpH3_conc fx1 R1 T ti 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & _ & _ & _ & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_peek AD) M3v MID MS3 FRZ3).
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP1.KS_alpH3). vm_compute. reflexivity. }
  clear MS3 FRZ3 MG3. intros md3 HID3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 PNE IB Q0i GP1. rename MID3 into MID.
  pose proof PEEK as SPEC. unfold PECSA.peek_spec, PECSPA.peek_spec in SPEC.
  apply (call_src (pa_peek AD) _ (PECSPA.cpeek_res RSEGS) SPEC 0xb28f4 _ _ _ _ _ _ _ _ _ _ _ _ _ MID SMR1 SDN1 GP1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10).
  { exact I. }
  { intros p0 Ra Rb Mb sa sb ma mb RS. unfold PECSPA.cpeek_res in RS. exact (proj1 (proj2 RS)). }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 RP4 RES4 POS4 MID4.
  unfold PMSPA.with_src in MID4. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in MID4, POS4, RES4.
  destruct RES4 as (CONS4 & CW4 & RES4).
  assert (HQ4 : PEC.pos_of p src4 sm4 = s_pos X1).
  { unfold PMSPA.consumed in CONS4. cbn [PM.p_src] in CONS4, POS4. unfold PEC.pos_of in POS4 |- *. clear - CONS4 POS4. lia. }
  rewrite HQ4, w_pos_self in MID4.
  destruct RES4 as [(A256 & POS4')|(POS4' & Ab & REM4)].
  {
    assert (ATEND : blen p <= s_pos X1) by (clear - POS4' HQ4; lia). rewrite L5K.rl10 in A256.
    pose proof (step_iarray_eof p X1 _ rr HALT1 HS1 eq_refl ATEND) as STEPe.
    assert (EXe : w_halt true (r_fail X1) = run (Datatypes.S i1) p UbjRef.init) by (rewrite <- STEPe; unfold X1; apply PEACLPD.step_run).
    keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 MID4 A256 EXe. rename MID4 into MID.
    entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP2.alpP3e_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb28f4 (pa_make_ec AD) M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP2.KS_alpP3e). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  clear MID. rename MID5 into MID.
  apply (call_mkec 0xb2e58 1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx6 R6 M6 md6 LK6 Aw6 RP6 MID6.
  apply (tail_Z _ _ _ _ _ _ _ _ _ _ _ _ _ MID6). exists (Datatypes.S i1). unfold r_fail in EXe. exact EXe. }

  pose proof (bat_range p (s_pos X1) BOK) as CRNG. set (c := bat p (s_pos X1)) in *.
  assert (INB : s_pos X1 < blen p) by (clear - POS4' HQ4; lia). rewrite HQ4 in Ab. fold c in Ab. rewrite L5K.rl10 in Ab.
  destruct (Z.eq_dec c 93) as [CM|NM].
  {
    pose proof (step_iarray_close p X1 _ rr HALT1 HS1 eq_refl INB CM) as STEPc.
    rewrite CM in Ab.
    destruct (unread_nn2 _ _ _ _ _ _ _ _ _ _ _ _ _ MID4) as (UR4 & UG4). cbn [PMSPA.with_src PM.p_src] in UR4.
    keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID4 Ab REM4 INB GP1 STEPc HQ4 UR4 UG4 PNE. rename MID4 into MID.
    entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP2.alpP3c_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb28f4 (pa_ignore AD) M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP2.KS_alpP3c). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID5 Y1 Y10 Y11 REM4 INB GP1 STEPc HQ4 UR4 UG4 PNE. rename MID5 into MID.
  pose proof IGN as SPEC. unfold PECSA.ignore_spec, PECSPA.ignore_spec in SPEC.
  apply (call_src (pa_ignore AD) _ (PECSPA.cignore_res RSEGS) SPEC 0xb2914 _ _ _ _ _ _ _ _ _ _ _ _ _ MID SMR1 SDN1 GP1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10).
  { unfold PMSPA.ignore_args. rewrite L5K.rl11. exact Y11. }
  { intros p0 Ra Rb Mb sa sb ma mb RS. unfold PECSPA.cignore_res in RS. exact (proj1 RS). }
  clear SPEC. intros fx6 R6 M6 md6 LK6 Aw6 src6 sm6 RP6 RES6 POS6 MID6.
  unfold PMSPA.with_src in MID6. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in MID6, POS6, RES6.
  destruct RES6 as (CW6 & RES6).
  destruct (unread_nn2 _ _ _ _ _ _ _ _ _ _ _ _ _ MID6) as (UR6 & UG6). cbn [PMSPA.with_src PM.p_src] in UR6.
  assert (HQ6 : PEC.pos_of p src6 sm6 = s_pos X1 + 1).
  { unfold PMSPA.consumed in RES6. cbn [PMSPA.with_src PM.p_src] in RES6, POS6. unfold PEC.pos_of in POS6, HQ4 |- *. unfold PM.unread in *.
    clear - RES6 POS6 HQ4 REM4 UR4 UG4 UR6 UG6 INB. destruct RES6 as [C1|(C0 & U0)]; lia. }
  rewrite HQ6 in MID6.
  pose proof (next_head p i1 X1 (r_end (w_pos (s_pos X1 + 1) X1)) BOK eq_refl HALT1 STEPc (r_end_done _) (r_end_halt _) (fun _ => r_end_more _)) as NX.
  pose proof (next_head_hi p i1 X1 (r_end (w_pos (s_pos X1 + 1) X1)) (PESKA.spa_hb P) eq_refl STEPc HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  pose proof (head_end_facts_w p X1 _ rr (s_pos X1 + 1) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - INB GP1; lia)) as MPE.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 MID6 NX HBY NBY MPE PNE. rename MID6 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP3.alpI3_conc fx6 R6 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11 & Y12).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx7 R7 0xb2914 (pa_end_array AD) M7v MID MS7 FRZ7).
  { intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpI3). vm_compute. reflexivity. }
  clear MS7 FRZ7 MG7. intros md7 HID7 MID7.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 MID7 Y1 Y10 Y11 Y12 NX HBY NBY MPE. rename MID7 into MID.
  pose proof EAR as SPEC. unfold PECSA.end_array_spec, PECSPA.end_array_spec in SPEC.
  apply (call_crun unit (pa_end_array AD) 5 (PECSPA.args3 AD) PECSPA.mp_end (fun _ p0 X0 => r_end X0) SPEC tt 0xb2924 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact MPE. }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx8 R8 M8 md8 LK8 Aw8 cr8 s8 sm8 en8 k8 e8 RP8 MID8.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 NX  MID8. rename MID8 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP4.alpCE3_conc fx8 R8 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx9 R9 0xb2924 PEACLPD.LPJOIN M9v MID MS9 FRZ9).
  { intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpCE3). vm_compute. reflexivity. }
  clear MS9 FRZ9 MG9. intros md9 HID9 MID9.
  apply (tail_J _ _ _ _ _ _ _ _ _ _ _ _ _ MID9).
  - rewrite r_end_done. exact SDN1.
  - intros EC fx' R' md' MID'. destruct (proj1 NX EC) as (EX2 & HALT2 & MU2).
    eapply (IH fx' R' _ md' _ _ _ _ _ _ _ _ (Datatypes.S i1)); [rewrite <- EX2; exact MID'| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  - intros EC. destruct (proj1 (proj2 NX) EC) as (EX3 & _). exists (Datatypes.S i1). exact EX3.
  }

  assert (CB : 0 <= c <= 255 /\ c <> 93) by (clear - CRNG NM; lia). assert (Q0c : 0 <= c < 2 ^ 64) by (clear - CRNG; lia).
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID4 Ab INB GP1 CB Q0c NM PNE IB Q0i. rename MID4 into MID.
  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Miarray 0 tty ti)) MID eq_refl) as (TFv & TPv & _ & _ & _). cbn [PMSPA.with_src PM.p_b PM.p_k PM.p_stk] in TFv, TPv. fold T in TFv, TPv.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PMSPA.with_src PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  destruct (Z.eq_dec ti 16777216) as [IX|IX].
  {
    assert (TI24x : L5.u64_at RSEGS MVi (T + 24) 16777216) by (rewrite <- IX; exact TI24).
    pose proof (step_iarray_full p X1 _ rr HALT1 HS1 eq_refl INB NM ltac:(cbn [ps_idx]; unfold UbjRef.MAX_ITEMS; clear - IX; lia)) as STEPf.
    rewrite (top_upd_fields ps_inc X1 _ rr HS1) in STEPf. cbv [ps_inc ps_mode ps_len ps_type ps_idx] in STEPf.
    destruct (Z_lt_le_dec c 93) as [CL|CH].
    { assert (Hb : 0 <= c <= 92) by (clear - CB CL; lia).
  pz PEALPP2.alpP3lx_conc fx4 R4 T ti 0 0 c 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & _ & W5).
  assert (PTv5 : PM.pstate_at RSEGS M5v T (PEC.ps_conv (PS Miarray 0 tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| replace (ti + 1) with 16777217 by (clear - IX; lia); exact W5]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Miarray 0 tty (ti + 1)) _ _ _ _ _ fx5 R5 0xb28f4 (pa_make_ec AD) M5v 24 8 MID HS1 Epre MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv5. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP2.KS_alpP3lx). vm_compute. reflexivity. }
  clear MS5 MG5 PTv5. intros M5 md5 VIS5 HID5 MGM5 MID5.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 MID5 Y1 Y10 Y11 STEPf. rename MID5 into MID.
  apply (call_mkec 0xb2e58 13 _ _ _ _ _ _ _ _ _ _ _ _ _ MID Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx6 R6 M6 md6 LK6 Aw6 RP6 MID6.
  apply (tail_Z _ _ _ _ _ _ _ _ _ _ _ _ _ MID6). exists (Datatypes.S i1). unfold r_fail in STEPf. rewrite <- STEPf. unfold X1. apply PEACLPD.step_run. }
    { assert (Hb : 94 <= c <= 255) by (clear - CB CH; lia).
  pz PEALPP3.alpP3hx_conc fx4 R4 T ti 0 0 c 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & _ & W5).
  assert (PTv5 : PM.pstate_at RSEGS M5v T (PEC.ps_conv (PS Miarray 0 tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| replace (ti + 1) with 16777217 by (clear - IX; lia); exact W5]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Miarray 0 tty (ti + 1)) _ _ _ _ _ fx5 R5 0xb28f4 (pa_make_ec AD) M5v 24 8 MID HS1 Epre MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv5. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpP3hx). vm_compute. reflexivity. }
  clear MS5 MG5 PTv5. intros M5 md5 VIS5 HID5 MGM5 MID5.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 MID5 Y1 Y10 Y11 STEPf. rename MID5 into MID.
  apply (call_mkec 0xb2e58 13 _ _ _ _ _ _ _ _ _ _ _ _ _ MID Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx6 R6 M6 md6 LK6 Aw6 RP6 MID6.
  apply (tail_Z _ _ _ _ _ _ _ _ _ _ _ _ _ MID6). exists (Datatypes.S i1). unfold r_fail in STEPf. rewrite <- STEPf. unfold X1. apply PEACLPD.step_run. }
  }

  assert (Hi24 : 0 <= ti <= 16777215) by (clear - IB IX; lia).
  pose proof (step_iarray_item p X1 _ rr HALT1 HS1 eq_refl INB NM ltac:(cbn [ps_idx]; unfold UbjRef.MAX_ITEMS; clear - IB IX; lia)) as STEP.
  rewrite (top_upd_fields _ X1 _ rr HS1) in STEP. cbv [ps_inc ps_mode_set ps_mode ps_len ps_type ps_idx] in STEP.
  destruct (head_call_facts p X1 (PS Miarray 0 tty ti) rr (PS Miarray 0 tty (ti + 1)) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - TOK IB IX; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia)) as (MPa1 & MPa2 & MPa3 & MPa4 & MPa5 & MPa6 & GIa & HALTa).
  pose proof MPa1 as ((_ & POSa & _) & SMa).
  destruct (Z_lt_le_dec c 93) as [CL|CH].
  { assert (Hb : 0 <= c <= 92) by (clear - CB CL; lia).
  pz PEALPP2.alpP3l_conc fx4 R4 T ti 0 0 c 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & Y12 & W5).
  assert (PTv5 : PM.pstate_at RSEGS M5v T (PEC.ps_conv (PS Miarray 0 tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| exact W5]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Miarray 0 tty (ti + 1)) _ _ _ _ _ fx5 R5 0xb28f4 (pa_rtv AD) M5v 24 8 MID HS1 Epre MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv5. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP2.KS_alpP3l). vm_compute. reflexivity. }
  clear MS5 MG5 PTv5. intros M5 md5 VIS5 HID5 MGM5 MID5.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID5 Y1 Y10 Y11 Y12 STEP MPa1 MPa2 MPa3 MPa4 MPa5 MPa6 POSa SMa PNE TOK IB IX. rename MID5 into MID.
  pose proof (proj1 (r_tv_eff p (w_stk ((PS Miarray 0 tty (ti + 1)) :: rr) X1) MPa1)) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  pose proof (next_head p i1 X1 (r_tv p (w_stk ((PS Miarray 0 tty (ti + 1)) :: rr) X1)) BOK eq_refl HALT1 STEP DNy HLy ltac:(intros E0; exact (r_tv_more p _ SMa E0))) as NX.
  pose proof (next_head_hi p i1 X1 (r_tv p (w_stk ((PS Miarray 0 tty (ti + 1)) :: rr) X1)) (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  pose proof RTV as SPEC. unfold PECSA.rtv_spec, PECSPA.rtv_spec in SPEC.
  apply (call_crun unit (pa_rtv AD) 9 (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_tv p0 X0) SPEC tt 0xb2cbc _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx6 R6 M6 md6 LK6 Aw6 cr6 s6 sm6 en6 k6 e6 RP6 MID6.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 NX DNy MID6. rename MID6 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP4.alpCR3_conc fx6 R6 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx7 R7 0xb2cbc PEACLPD.LPJOIN M7v MID MS7 FRZ7).
  { intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpCR3). vm_compute. reflexivity. }
  clear MS7 FRZ7 MG7. intros md7 HID7 MID7.
  apply (tail_J _ _ _ _ _ _ _ _ _ _ _ _ _ MID7).
  - rewrite DNy. exact SDN1.
  - intros EC fx' R' md' MID'. destruct (proj1 NX EC) as (EX2 & HALT2 & MU2).
    eapply (IH fx' R' _ md' _ _ _ _ _ _ _ _ (Datatypes.S i1)); [rewrite <- EX2; exact MID'| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  - intros EC. destruct (proj1 (proj2 NX) EC) as (EX3 & _). exists (Datatypes.S i1). exact EX3.
  }
  { assert (Hb : 94 <= c <= 255) by (clear - CB CH; lia).
  pz PEALPP2.alpP3h_conc fx4 R4 T ti 0 0 c 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & Y12 & W5).
  assert (PTv5 : PM.pstate_at RSEGS M5v T (PEC.ps_conv (PS Miarray 0 tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| exact W5]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Miarray 0 tty (ti + 1)) _ _ _ _ _ fx5 R5 0xb28f4 (pa_rtv AD) M5v 24 8 MID HS1 Epre MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv5. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP2.KS_alpP3h). vm_compute. reflexivity. }
  clear MS5 MG5 PTv5. intros M5 md5 VIS5 HID5 MGM5 MID5.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID5 Y1 Y10 Y11 Y12 STEP MPa1 MPa2 MPa3 MPa4 MPa5 MPa6 POSa SMa PNE TOK IB IX. rename MID5 into MID.
  pose proof (proj1 (r_tv_eff p (w_stk ((PS Miarray 0 tty (ti + 1)) :: rr) X1) MPa1)) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  pose proof (next_head p i1 X1 (r_tv p (w_stk ((PS Miarray 0 tty (ti + 1)) :: rr) X1)) BOK eq_refl HALT1 STEP DNy HLy ltac:(intros E0; exact (r_tv_more p _ SMa E0))) as NX.
  pose proof (next_head_hi p i1 X1 (r_tv p (w_stk ((PS Miarray 0 tty (ti + 1)) :: rr) X1)) (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  pose proof RTV as SPEC. unfold PECSA.rtv_spec, PECSPA.rtv_spec in SPEC.
  apply (call_crun unit (pa_rtv AD) 9 (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_tv p0 X0) SPEC tt 0xb2cbc _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx6 R6 M6 md6 LK6 Aw6 cr6 s6 sm6 en6 k6 e6 RP6 MID6.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 NX DNy MID6. rename MID6 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP4.alpCR3_conc fx6 R6 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx7 R7 0xb2cbc PEACLPD.LPJOIN M7v MID MS7 FRZ7).
  { intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpCR3). vm_compute. reflexivity. }
  clear MS7 FRZ7 MG7. intros md7 HID7 MID7.
  apply (tail_J _ _ _ _ _ _ _ _ _ _ _ _ _ MID7).
  - rewrite DNy. exact SDN1.
  - intros EC fx' R' md' MID'. destruct (proj1 NX EC) as (EX2 & HALT2 & MU2).
    eapply (IH fx' R' _ md' _ _ _ _ _ _ _ _ (Datatypes.S i1)); [rewrite <- EX2; exact MID'| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  - intros EC. destruct (proj1 (proj2 NX) EC) as (EX3 & _). exists (Datatypes.S i1). exact EX3.
  }
Qed.

Lemma arm_Mikey (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat) :
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false ->
  PEACLPD.top_mode (run i1 p UbjRef.init) = Mikey ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros MID HALT1 TG IH. set (X1 := run i1 p UbjRef.init) in *.
  pose proof POK as (BOK & BLT).
  pose proof (run_ginv p BOK i1 UbjRef.init (ginv_init p)) as GI1. fold X1 in GI1.
  pose proof (gi_run p X1 GI1 HALT1) as RI1. destruct (halted_false X1 HALT1) as (SHLT1 & SDN1 & SMR1).
  destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm1 & Cd1 & Cdp1 & Cstk1 & Cpos1 & Cestk1 & Ced1 & Cz1 & Cbad1). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm1, Cd1, Cdp1, Cstk1, Cpos1.
  destruct (s_stk X1) as [|t rr] eqn:HS1; [exfalso; pose proof (ri_shape X1 RI1) as SH0; rewrite HS1 in SH0; exact SH0|].
  pose proof (ri_ps X1 RI1) as PS1. rewrite HS1 in PS1. pose proof (Forall_inv PS1) as TOK. clear PS1.
  pose proof (ri_depth X1 RI1) as DEP1. pose proof (ri_dmax X1 RI1) as DMAX1. pose proof (ri_estk_max X1 RI1) as EMAX1. pose proof (ri_estk X1 RI1) as ESTK1.
  pose proof (ri_shape X1 RI1) as SHP1. rewrite HS1 in DEP1, ESTK1, SHP1. cbn [length] in DEP1, ESTK1.
  destruct t as [tmm tl tty ti].
  unfold PEACLPD.top_mode in TG. rewrite HS1 in TG. cbn [hd ps_mode] in TG. subst tmm.
  rewrite PEC.stk_conv_cons in Cstk1. remember (PEC.stk_conv rr) as pre eqn:Epre. subst stk1.
  assert (IM1 : mo1 = 1) by (rewrite Cm1, SMR1; reflexivity). assert (ID1 : dn1 = 0) by (rewrite Cd1, SDN1; reflexivity). clear Cm1 Cd1. subst mo1 dn1.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC1 & PB1 & PB2 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC1, PB1, PB2.
  pose proof PVEC1 as (_ & _ & _ & Hk1 & Hlen1 & _). clear PVEC1.
  rewrite length_app in Hlen1. cbn [length] in Hlen1. rewrite Nat2Z.inj_add in Hlen1. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1.

  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mikey tl tty ti)) MID eq_refl) as (TFv & TPv & TP & VIN & TB2). cbn [PM.p_b PM.p_k] in TFv, TPv, TP, VIN, TB2.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  assert (PNE : rr <> []) by (intros RR; rewrite RR in SHP1; cbn in SHP1; discriminate).
  assert (IB : tl = 0 /\ 0 <= ti <= 16777216) by (clear - TOK; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia).
  destruct IB as (TL0 & IB). subst tl. assert (Q0i : 0 <= ti < 2 ^ 64) by (clear - IB; lia).
  pose proof (gi_pos p X1 GI1) as GP1.
  pz PEALPP2.alpH9_conc fx1 R1 T ti 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & _ & _ & _ & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 PEACLPD.LPHEAD (pa_peek AD) M3v MID MS3 FRZ3).
  { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEALPP2.KS_alpH9). vm_compute. reflexivity. }
  clear MS3 FRZ3 MG3. intros md3 HID3 MID3.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID3 Y1 Y10 PNE IB Q0i GP1. rename MID3 into MID.
  pose proof PEEK as SPEC. unfold PECSA.peek_spec, PECSPA.peek_spec in SPEC.
  apply (call_src (pa_peek AD) _ (PECSPA.cpeek_res RSEGS) SPEC 0xb2838 _ _ _ _ _ _ _ _ _ _ _ _ _ MID SMR1 SDN1 GP1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10).
  { exact I. }
  { intros p0 Ra Rb Mb sa sb ma mb RS. unfold PECSPA.cpeek_res in RS. exact (proj1 (proj2 RS)). }
  clear SPEC. intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 RP4 RES4 POS4 MID4.
  unfold PMSPA.with_src in MID4. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in MID4, POS4, RES4.
  destruct RES4 as (CONS4 & CW4 & RES4).
  assert (HQ4 : PEC.pos_of p src4 sm4 = s_pos X1).
  { unfold PMSPA.consumed in CONS4. cbn [PM.p_src] in CONS4, POS4. unfold PEC.pos_of in POS4 |- *. clear - CONS4 POS4. lia. }
  rewrite HQ4, w_pos_self in MID4.
  destruct RES4 as [(A256 & POS4')|(POS4' & Ab & REM4)].
  {
    assert (ATEND : blen p <= s_pos X1) by (clear - POS4' HQ4; lia). rewrite L5K.rl10 in A256.
    pose proof (step_ikey_eof p X1 _ rr HALT1 HS1 eq_refl ATEND) as STEPe.
    assert (EXe : w_halt true (r_fail X1) = run (Datatypes.S i1) p UbjRef.init) by (rewrite <- STEPe; unfold X1; apply PEACLPD.step_run).
    keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 MID4 A256 EXe. rename MID4 into MID.
    entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP3.alpP9e_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb2838 (pa_make_ec AD) M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpP9e). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  clear MID. rename MID5 into MID.
  apply (call_mkec 0xb2e58 1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx6 R6 M6 md6 LK6 Aw6 RP6 MID6.
  apply (tail_Z _ _ _ _ _ _ _ _ _ _ _ _ _ MID6). exists (Datatypes.S i1). unfold r_fail in EXe. exact EXe. }

  pose proof (bat_range p (s_pos X1) BOK) as CRNG. set (c := bat p (s_pos X1)) in *.
  assert (INB : s_pos X1 < blen p) by (clear - POS4' HQ4; lia). rewrite HQ4 in Ab. fold c in Ab. rewrite L5K.rl10 in Ab.
  destruct (Z.eq_dec c 125) as [CM|NM].
  {
    pose proof (step_ikey_close p X1 _ rr HALT1 HS1 eq_refl INB CM) as STEPc.
    rewrite CM in Ab.
    destruct (unread_nn2 _ _ _ _ _ _ _ _ _ _ _ _ _ MID4) as (UR4 & UG4). cbn [PMSPA.with_src PM.p_src] in UR4.
    keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID4 Ab REM4 INB GP1 STEPc HQ4 UR4 UG4 PNE. rename MID4 into MID.
    entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP3.alpP9c_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 0xb2838 (pa_ignore AD) M5v MID MS5 FRZ5).
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpP9c). vm_compute. reflexivity. }
  clear MS5 FRZ5 MG5. intros md5 HID5 MID5.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID5 Y1 Y10 Y11 REM4 INB GP1 STEPc HQ4 UR4 UG4 PNE. rename MID5 into MID.
  pose proof IGN as SPEC. unfold PECSA.ignore_spec, PECSPA.ignore_spec in SPEC.
  apply (call_src (pa_ignore AD) _ (PECSPA.cignore_res RSEGS) SPEC 0xb2858 _ _ _ _ _ _ _ _ _ _ _ _ _ MID SMR1 SDN1 GP1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10).
  { unfold PMSPA.ignore_args. rewrite L5K.rl11. exact Y11. }
  { intros p0 Ra Rb Mb sa sb ma mb RS. unfold PECSPA.cignore_res in RS. exact (proj1 RS). }
  clear SPEC. intros fx6 R6 M6 md6 LK6 Aw6 src6 sm6 RP6 RES6 POS6 MID6.
  unfold PMSPA.with_src in MID6. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in MID6, POS6, RES6.
  destruct RES6 as (CW6 & RES6).
  destruct (unread_nn2 _ _ _ _ _ _ _ _ _ _ _ _ _ MID6) as (UR6 & UG6). cbn [PMSPA.with_src PM.p_src] in UR6.
  assert (HQ6 : PEC.pos_of p src6 sm6 = s_pos X1 + 1).
  { unfold PMSPA.consumed in RES6. cbn [PMSPA.with_src PM.p_src] in RES6, POS6. unfold PEC.pos_of in POS6, HQ4 |- *. unfold PM.unread in *.
    clear - RES6 POS6 HQ4 REM4 UR4 UG4 UR6 UG6 INB. destruct RES6 as [C1|(C0 & U0)]; lia. }
  rewrite HQ6 in MID6.
  pose proof (next_head p i1 X1 (r_end (w_pos (s_pos X1 + 1) X1)) BOK eq_refl HALT1 STEPc (r_end_done _) (r_end_halt _) (fun _ => r_end_more _)) as NX.
  pose proof (next_head_hi p i1 X1 (r_end (w_pos (s_pos X1 + 1) X1)) (PESKA.spa_hb P) eq_refl STEPc HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  pose proof (head_end_facts_w p X1 _ rr (s_pos X1 + 1) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - INB GP1; lia)) as MPE.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 MID6 NX HBY NBY MPE PNE. rename MID6 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP3.alpI9_conc fx6 R6 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11 & Y12).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx7 R7 0xb2858 (pa_end_object AD) M7v MID MS7 FRZ7).
  { intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpI9). vm_compute. reflexivity. }
  clear MS7 FRZ7 MG7. intros md7 HID7 MID7.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 MID7 Y1 Y10 Y11 Y12 NX HBY NBY MPE. rename MID7 into MID.
  pose proof EOB as SPEC. unfold PECSA.end_object_spec, PECSPA.end_object_spec in SPEC.
  apply (call_crun unit (pa_end_object AD) 5 (PECSPA.args3 AD) PECSPA.mp_end (fun _ p0 X0 => r_end X0) SPEC tt 0xb2868 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact MPE. }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx8 R8 M8 md8 LK8 Aw8 cr8 s8 sm8 en8 k8 e8 RP8 MID8.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 NX  MID8. rename MID8 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEALPP4.alpCE9_conc fx8 R8 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & _).
  apply (amid_ro _ _ _ _ _ _ _ _ _ _ _ _ _ fx9 R9 0xb2868 PEACLPD.LPJOIN M9v MID MS9 FRZ9).
  { intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b _ PEALPP4.KS_alpCE9). vm_compute. reflexivity. }
  clear MS9 FRZ9 MG9. intros md9 HID9 MID9.
  apply (tail_J _ _ _ _ _ _ _ _ _ _ _ _ _ MID9).
  - rewrite r_end_done. exact SDN1.
  - intros EC fx' R' md' MID'. destruct (proj1 NX EC) as (EX2 & HALT2 & MU2).
    eapply (IH fx' R' _ md' _ _ _ _ _ _ _ _ (Datatypes.S i1)); [rewrite <- EX2; exact MID'| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  - intros EC. destruct (proj1 (proj2 NX) EC) as (EX3 & _). exists (Datatypes.S i1). exact EX3.
  }

  assert (CB : 0 <= c <= 255 /\ c <> 125) by (clear - CRNG NM; lia). assert (Q0c : 0 <= c < 2 ^ 64) by (clear - CRNG; lia).
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID4 Ab INB GP1 CB Q0c NM PNE IB Q0i. rename MID4 into MID.
  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mikey 0 tty ti)) MID eq_refl) as (TFv & TPv & _ & _ & _). cbn [PMSPA.with_src PM.p_b PM.p_k PM.p_stk] in TFv, TPv. fold T in TFv, TPv.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PMSPA.with_src PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  destruct (Z.eq_dec ti 16777216) as [IX|IX].
  {
    assert (TI24x : L5.u64_at RSEGS MVi (T + 24) 16777216) by (rewrite <- IX; exact TI24).
    pose proof (step_ikey_full p X1 _ rr HALT1 HS1 eq_refl INB NM ltac:(cbn [ps_idx]; unfold UbjRef.MAX_ITEMS; clear - IX; lia)) as STEPf.
    rewrite (top_upd_fields ps_inc X1 _ rr HS1) in STEPf. cbv [ps_inc ps_mode ps_len ps_type ps_idx] in STEPf.
    destruct (Z_lt_le_dec c 125) as [CL|CH].
    { assert (Hb : 0 <= c <= 124) by (clear - CB CL; lia).
  pz PEALPP3.alpP9lx_conc fx4 R4 T ti 0 0 c 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & _ & W5).
  assert (PTv5 : PM.pstate_at RSEGS M5v T (PEC.ps_conv (PS Mikey 0 tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| replace (ti + 1) with 16777217 by (clear - IX; lia); exact W5]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mikey 0 tty (ti + 1)) _ _ _ _ _ fx5 R5 0xb2838 (pa_make_ec AD) M5v 24 8 MID HS1 Epre MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv5. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpP9lx). vm_compute. reflexivity. }
  clear MS5 MG5 PTv5. intros M5 md5 VIS5 HID5 MGM5 MID5.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 MID5 Y1 Y10 Y11 STEPf. rename MID5 into MID.
  apply (call_mkec 0xb2e58 13 _ _ _ _ _ _ _ _ _ _ _ _ _ MID Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx6 R6 M6 md6 LK6 Aw6 RP6 MID6.
  apply (tail_Z _ _ _ _ _ _ _ _ _ _ _ _ _ MID6). exists (Datatypes.S i1). unfold r_fail in STEPf. rewrite <- STEPf. unfold X1. apply PEACLPD.step_run. }
    { assert (Hb : 126 <= c <= 255) by (clear - CB CH; lia).
  pz PEALPP3.alpP9hx_conc fx4 R4 T ti 0 0 c 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & _ & W5).
  assert (PTv5 : PM.pstate_at RSEGS M5v T (PEC.ps_conv (PS Mikey 0 tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| replace (ti + 1) with 16777217 by (clear - IX; lia); exact W5]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mikey 0 tty (ti + 1)) _ _ _ _ _ fx5 R5 0xb2838 (pa_make_ec AD) M5v 24 8 MID HS1 Epre MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv5. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpP9hx). vm_compute. reflexivity. }
  clear MS5 MG5 PTv5. intros M5 md5 VIS5 HID5 MGM5 MID5.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 MID5 Y1 Y10 Y11 STEPf. rename MID5 into MID.
  apply (call_mkec 0xb2e58 13 _ _ _ _ _ _ _ _ _ _ _ _ _ MID Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx6 R6 M6 md6 LK6 Aw6 RP6 MID6.
  apply (tail_Z _ _ _ _ _ _ _ _ _ _ _ _ _ MID6). exists (Datatypes.S i1). unfold r_fail in STEPf. rewrite <- STEPf. unfold X1. apply PEACLPD.step_run. }
  }

  assert (Hi24 : 0 <= ti <= 16777215) by (clear - IB IX; lia).
  pose proof (step_ikey_item p X1 _ rr HALT1 HS1 eq_refl INB NM ltac:(cbn [ps_idx]; unfold UbjRef.MAX_ITEMS; clear - IB IX; lia)) as STEP.
  rewrite (top_upd_fields _ X1 _ rr HS1) in STEP. cbv [ps_inc ps_mode_set ps_mode ps_len ps_type ps_idx] in STEP.
  destruct (head_call_facts p X1 (PS Mikey 0 tty ti) rr (PS Mikey 0 tty (ti + 1)) BOK GI1 HALT1 HS1 eq_refl ltac:(clear - TOK IB IX; unfold ps_ok, counted_mode, UbjRef.MAX_ITEMS in TOK |- *; cbn [ps_mode ps_len ps_idx ps_type] in TOK |- *; lia)) as (MPa1 & MPa2 & MPa3 & MPa4 & MPa5 & MPa6 & GIa & HALTa).
  pose proof MPa1 as ((_ & POSa & _) & SMa).
  destruct (Z_lt_le_dec c 125) as [CL|CH].
  { assert (Hb : 0 <= c <= 124) by (clear - CB CL; lia).
  pz PEALPP3.alpP9l_conc fx4 R4 T ti 0 0 c 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & Y12 & W5).
  assert (PTv5 : PM.pstate_at RSEGS M5v T (PEC.ps_conv (PS Mikey 0 tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| exact W5]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mikey 0 tty (ti + 1)) _ _ _ _ _ fx5 R5 0xb2838 (pa_read_key AD) M5v 24 8 MID HS1 Epre MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv5. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpP9l). vm_compute. reflexivity. }
  clear MS5 MG5 PTv5. intros M5 md5 VIS5 HID5 MGM5 MID5.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID5 Y1 Y10 Y11 Y12 STEP MPa1 MPa2 MPa3 MPa4 MPa5 MPa6 POSa SMa PNE TOK IB IX. rename MID5 into MID.
  pose proof (r_key_eff p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1) (proj1 MPa1)) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  cbv zeta in STEP.
  pose proof (next_head_key p i1 X1 (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1)) Mival BOK eq_refl HALT1 STEP DNy HLy (r_key_more p _)) as NX.
  pose proof (next_head_key_hi p i1 X1 (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1)) Mival (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  assert (HSY : s_stk (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1)) = (PS Mikey 0 tty (ti + 1)) :: rr) by (rewrite r_key_stk; reflexivity).
  pose proof RDK as SPEC. unfold PECSA.read_key_spec, PECSPA.read_key_spec in SPEC.
  apply (call_crun unit (pa_read_key AD) 7 (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_key p0 X0) SPEC tt 0xb2c28 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx6 R6 M6 md6 LK6 Aw6 cr6 s6 sm6 en6 k6 e6 RP6 MID6.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 NX DNy HSY MID6. rename MID6 into MID.
  destruct (s_ec (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1))) eqn:ECY.
  {
    destruct (proj1 (proj2 NX) eq_refl) as (EX3 & _).
  destruct (ec_vis1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECY) as (v & Hv & ECv). destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _).
  entry_facts. frame_facts. piece_ctx MID. fold Hi in ECv, MO8, MO9. fold MVi in ECv, MO8, MO9.
  assert (Hv64 : 0 <= v < 2 ^ 64) by (clear - Hv; lia).
  pz PEALPP5.alpK9e_conc fx6 R6 0 0 0 0 0 v as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _).
  apply (finish (PM.p_more s6) (PM.p_done s6) (w_halt true (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1))) (Datatypes.S i1) _ _ _ _ _ _ _ _ _ _ _ _ _ fx7 R7 M7v 0xb2c28 MID MS7 MG7).
  + intros i Hi' _. apply FRZ7. exact Hi'.
  + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEALPP5.KS_alpK9e). vm_compute. reflexivity.
  + apply (L5C.u8_at_agree RSEGS MVi M7v); [intros i Hi'; apply FRZ7; clear - Hi' O1 O3; lia| clear - O1; lia| clear - O1 O3; lia| exact MO8].
  + apply (L5C.u8_at_agree RSEGS MVi M7v); [intros i Hi'; apply FRZ7; clear - Hi' O1 O3; lia| clear - O1; lia| clear - O1 O3; lia| exact MO9].
  + pose proof CP as (PA & _). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _). exact B1.
  + pose proof CP as (PA & _). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _). exact B2.
  + exact EX3.
  + reflexivity.
  + pose proof CP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9).
    unfold PEC.clink, set_md. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_halt PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5'|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
  + reflexivity.
  }

  destruct (proj1 NX eq_refl) as (EX2 & HALT2 & MU2 & _).
  rewrite (top_upd_fields (ps_mode_set Mival) (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1)) _ rr HSY) in EX2, HALT2, MU2. cbn [ps_mode_set ps_mode ps_len ps_type ps_idx] in EX2, HALT2, MU2.
  destruct s6 as [mo6 dn6 dp6 src6 tb6 tg6 vb6 vk6 stk6].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm6 & Cd6 & Cdp6 & Cstk6 & Cpos6 & Cestk6 & Ced6 & Cz6 & Cbad6). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm6, Cd6, Cdp6, Cstk6, Cpos6.
  rewrite HSY, PEC.stk_conv_cons, <- Epre in Cstk6. subst stk6.
  assert (IM6 : mo6 = 1) by (rewrite Cm6, (r_key_more p _ ECY); reflexivity). assert (ID6 : dn6 = 0) by (rewrite Cd6, DNy; cbn [s_done w_stk w_pos]; rewrite SDN1; reflexivity). clear Cm6 Cd6. subst mo6 dn6.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC6 & PB16 & PB26 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC6, PB16, PB26.
  pose proof PVEC6 as (_ & _ & _ & Hk6 & Hlen6 & _). clear PVEC6.
  rewrite length_app in Hlen6. cbn [length] in Hlen6. rewrite Nat2Z.inj_add in Hlen6. cbn [Z.of_nat Pos.of_succ_nat] in Hlen6.
  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mikey 0 tty (ti + 1))) MID eq_refl) as (TFv & TPv & TP6 & VIN6 & TB26). cbn [PM.p_b PM.p_k] in TFv, TPv, TP6, VIN6, TB26.
  set (T := vb6 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  pose proof (ec_vis0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECY) as EC0. fold Hi in EC0. fold MVi in EC0.
  pz PEALPP5.alpK90_conc fx6 R6 T 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & W7).
  assert (PTv7 : PM.pstate_at RSEGS M7v T (PEC.ps_conv (PS Mival 0 tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [exact W7|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M7v); [intros a Ha; apply FRZ7; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M7v); [intros a Ha; apply FRZ7; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]|].
    apply (L5C.u64_at_agree RSEGS MVi M7v); [intros a Ha; apply FRZ7; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TI24]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mival 0 tty (ti + 1)) _ _ _ _ _ fx7 R7 0xb2c28 PEACLPD.LPHEAD M7v 0 4 MID HSY Epre MS7 MG7).
  { intros a Ha Na. apply FRZ7; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv7. }
  { intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEALPP5.KS_alpK90). vm_compute. reflexivity. }
  clear MS7 MG7 PTv7. intros M7 md7 VIS7 HID7 MGM7 MID7.
  eapply (IH fx7 R7 M7 md7 LK6 Aw6 cr6 _ sm6 en6 k6 e6 (Datatypes.S i1)); [rewrite <- EX2; exact MID7| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  }
  { assert (Hb : 126 <= c <= 255) by (clear - CB CH; lia).
  pz PEALPP3.alpP9h_conc fx4 R4 T ti 0 0 c 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & Y12 & W5).
  assert (PTv5 : PM.pstate_at RSEGS M5v T (PEC.ps_conv (PS Mikey 0 tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [apply (PMF.u32_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TM0]|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M5v); [intros a Ha; apply FRZ5; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]| exact W5]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mikey 0 tty (ti + 1)) _ _ _ _ _ fx5 R5 0xb2838 (pa_read_key AD) M5v 24 8 MID HS1 Epre MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv5. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP3.KS_alpP9h). vm_compute. reflexivity. }
  clear MS5 MG5 PTv5. intros M5 md5 VIS5 HID5 MGM5 MID5.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre Hk1 Hlen1 TP VIN TB2 X1 T IH HALT1 Cdp1 Cpos1 Cestk1 Ced1 Cz1 Cbad1 PB1 PB2 MID5 Y1 Y10 Y11 Y12 STEP MPa1 MPa2 MPa3 MPa4 MPa5 MPa6 POSa SMa PNE TOK IB IX. rename MID5 into MID.
  pose proof (r_key_eff p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1) (proj1 MPa1)) as EFFa. destruct EFFa as (NBy & DNy & HLy & _).
  cbv zeta in STEP.
  pose proof (next_head_key p i1 X1 (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1)) Mival BOK eq_refl HALT1 STEP DNy HLy (r_key_more p _)) as NX.
  pose proof (next_head_key_hi p i1 X1 (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1)) Mival (PESKA.spa_hb P) eq_refl STEP HBN) as HBY. pose proof (proj2 (proj2 NX)) as NBY.
  assert (HSY : s_stk (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1)) = (PS Mikey 0 tty (ti + 1)) :: rr) by (rewrite r_key_stk; reflexivity).
  pose proof RDK as SPEC. unfold PECSA.read_key_spec, PECSPA.read_key_spec in SPEC.
  apply (call_crun unit (pa_read_key AD) 7 (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_key p0 X0) SPEC tt 0xb2c28 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(clear; lia) Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact (conj MPa1 (conj MPa2 (conj MPa3 (conj MPa4 (conj MPa5 MPa6))))). }
  { exact NBY. }
  { exact HBY. }
  clear SPEC. intros fx6 R6 M6 md6 LK6 Aw6 cr6 s6 sm6 en6 k6 e6 RP6 MID6.
  keep_only BOK BLT GI1 RI1 SHLT1 SDN1 SMR1 HS1 TOK DEP1 DMAX1 EMAX1 ESTK1 SHP1 Epre X1 IH HALT1 NX DNy HSY MID6. rename MID6 into MID.
  destruct (s_ec (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1))) eqn:ECY.
  {
    destruct (proj1 (proj2 NX) eq_refl) as (EX3 & _).
  destruct (ec_vis1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECY) as (v & Hv & ECv). destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _).
  entry_facts. frame_facts. piece_ctx MID. fold Hi in ECv, MO8, MO9. fold MVi in ECv, MO8, MO9.
  assert (Hv64 : 0 <= v < 2 ^ 64) by (clear - Hv; lia).
  pz PEALPP5.alpK9e_conc fx6 R6 0 0 0 0 0 v as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _).
  apply (finish (PM.p_more s6) (PM.p_done s6) (w_halt true (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1))) (Datatypes.S i1) _ _ _ _ _ _ _ _ _ _ _ _ _ fx7 R7 M7v 0xb2c28 MID MS7 MG7).
  + intros i Hi' _. apply FRZ7. exact Hi'.
  + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEALPP5.KS_alpK9e). vm_compute. reflexivity.
  + apply (L5C.u8_at_agree RSEGS MVi M7v); [intros i Hi'; apply FRZ7; clear - Hi' O1 O3; lia| clear - O1; lia| clear - O1 O3; lia| exact MO8].
  + apply (L5C.u8_at_agree RSEGS MVi M7v); [intros i Hi'; apply FRZ7; clear - Hi' O1 O3; lia| clear - O1; lia| clear - O1 O3; lia| exact MO9].
  + pose proof CP as (PA & _). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _). exact B1.
  + pose proof CP as (PA & _). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _). exact B2.
  + exact EX3.
  + reflexivity.
  + pose proof CP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9).
    unfold PEC.clink, set_md. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_halt PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5'|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
  + reflexivity.
  }

  destruct (proj1 NX eq_refl) as (EX2 & HALT2 & MU2 & _).
  rewrite (top_upd_fields (ps_mode_set Mival) (r_key p (w_stk ((PS Mikey 0 tty (ti + 1)) :: rr) X1)) _ rr HSY) in EX2, HALT2, MU2. cbn [ps_mode_set ps_mode ps_len ps_type ps_idx] in EX2, HALT2, MU2.
  destruct s6 as [mo6 dn6 dp6 src6 tb6 tg6 vb6 vk6 stk6].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm6 & Cd6 & Cdp6 & Cstk6 & Cpos6 & Cestk6 & Ced6 & Cz6 & Cbad6). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm6, Cd6, Cdp6, Cstk6, Cpos6.
  rewrite HSY, PEC.stk_conv_cons, <- Epre in Cstk6. subst stk6.
  assert (IM6 : mo6 = 1) by (rewrite Cm6, (r_key_more p _ ECY); reflexivity). assert (ID6 : dn6 = 0) by (rewrite Cd6, DNy; cbn [s_done w_stk w_pos]; rewrite SDN1; reflexivity). clear Cm6 Cd6. subst mo6 dn6.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC6 & PB16 & PB26 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC6, PB16, PB26.
  pose proof PVEC6 as (_ & _ & _ & Hk6 & Hlen6 & _). clear PVEC6.
  rewrite length_app in Hlen6. cbn [length] in Hlen6. rewrite Nat2Z.inj_add in Hlen6. cbn [Z.of_nat Pos.of_succ_nat] in Hlen6.
  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Mikey 0 tty (ti + 1))) MID eq_refl) as (TFv & TPv & TP6 & VIN6 & TB26). cbn [PM.p_b PM.p_k] in TFv, TPv, TP6, VIN6, TB26.
  set (T := vb6 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  pose proof (ec_vis0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECY) as EC0. fold Hi in EC0. fold MVi in EC0.
  pz PEALPP5.alpK90_conc fx6 R6 T 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & W7).
  assert (PTv7 : PM.pstate_at RSEGS M7v T (PEC.ps_conv (PS Mival 0 tty (ti + 1)))).
  { unfold PM.pstate_at. cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx]. split; [exact W7|].
    split; [apply (L5C.u64_at_agree RSEGS MVi M7v); [intros a Ha; apply FRZ7; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TL8]|].
    split; [apply (L5C.u8_at_agree RSEGS MVi M7v); [intros a Ha; apply FRZ7; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TT16]|].
    apply (L5C.u64_at_agree RSEGS MVi M7v); [intros a Ha; apply FRZ7; [clear - Ha TF1; lia| clear - Ha; lia]| clear - TF1; lia| clear - TF1; lia| exact TI24]. }
  apply (amid_pieceT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rr (PS Mival 0 tty (ti + 1)) _ _ _ _ _ fx7 R7 0xb2c28 PEACLPD.LPHEAD M7v 0 4 MID HSY Epre MS7 MG7).
  { intros a Ha Na. apply FRZ7; [exact Ha| clear - Na; unfold T in Na; lia]. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { exact PTv7. }
  { intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEALPP5.KS_alpK90). vm_compute. reflexivity. }
  clear MS7 MG7 PTv7. intros M7 md7 VIS7 HID7 MGM7 MID7.
  eapply (IH fx7 R7 M7 md7 LK6 Aw6 cr6 _ sm6 en6 k6 e6 (Datatypes.S i1)); [rewrite <- EX2; exact MID7| rewrite <- EX2; exact HALT2| rewrite <- EX2; exact MU2].
  }
Qed.

Lemma arm_Maccept (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat) :
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false ->
  PEACLPD.top_mode (run i1 p UbjRef.init) = Maccept ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2 md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros MID HALT1 TG IH. set (X1 := run i1 p UbjRef.init) in *.
  pose proof POK as (BOK & BLT).
  pose proof (run_ginv p BOK i1 UbjRef.init (ginv_init p)) as GI1. fold X1 in GI1.
  pose proof (gi_run p X1 GI1 HALT1) as RI1. destruct (halted_false X1 HALT1) as (SHLT1 & SDN1 & SMR1).
  destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
  pose proof MID as (_ & LMx). unfold PEACLPD.lmem in LMx. destruct LMx as (_ & CPx & _). pose proof CPx as (PAx & _ & _ & _ & _ & _ & _ & _ & _ & CLx & _). clear CPx.
  pose proof CLx as (Cm1 & Cd1 & Cdp1 & Cstk1 & Cpos1 & Cestk1 & Ced1 & Cz1 & Cbad1). clear CLx.
  cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in Cm1, Cd1, Cdp1, Cstk1, Cpos1.
  destruct (s_stk X1) as [|t rr] eqn:HS1; [exfalso; pose proof (ri_shape X1 RI1) as SH0; rewrite HS1 in SH0; exact SH0|].
  pose proof (ri_ps X1 RI1) as PS1. rewrite HS1 in PS1. pose proof (Forall_inv PS1) as TOK. clear PS1.
  pose proof (ri_depth X1 RI1) as DEP1. pose proof (ri_dmax X1 RI1) as DMAX1. pose proof (ri_estk_max X1 RI1) as EMAX1. pose proof (ri_estk X1 RI1) as ESTK1.
  pose proof (ri_shape X1 RI1) as SHP1. rewrite HS1 in DEP1, ESTK1, SHP1. cbn [length] in DEP1, ESTK1.
  destruct t as [tmm tl tty ti].
  unfold PEACLPD.top_mode in TG. rewrite HS1 in TG. cbn [hd ps_mode] in TG. subst tmm.
  rewrite PEC.stk_conv_cons in Cstk1. remember (PEC.stk_conv rr) as pre eqn:Epre. subst stk1.
  assert (IM1 : mo1 = 1) by (rewrite Cm1, SMR1; reflexivity). assert (ID1 : dn1 = 0) by (rewrite Cd1, SDN1; reflexivity). clear Cm1 Cd1. subst mo1 dn1.
  pose proof PAx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC1 & PB1 & PB2 & _). clear PAx. cbn [PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVEC1, PB1, PB2.
  pose proof PVEC1 as (_ & _ & _ & Hk1 & Hlen1 & _). clear PVEC1.
  rewrite length_app in Hlen1. cbn [length] in Hlen1. rewrite Nat2Z.inj_add in Hlen1. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1.

  destruct (tfacts _ _ _ _ _ _ _ _ _ _ _ _ _ pre (PEC.ps_conv (PS Maccept tl tty ti)) MID eq_refl) as (TFv & TPv & TP & VIN & TB2). cbn [PM.p_b PM.p_k] in TFv, TPv, TP, VIN, TB2.
  set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
  destruct TPv as (TM0 & TL8 & TT16 & TI24). cbn [PEC.ps_conv PEC.mode_code PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx ps_mode ps_len ps_type ps_idx] in TM0, TL8, TT16, TI24.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. open_tf TFv.
  fold Hi in TM0, TL8, TT16, TI24, MO8, MO9. fold MVi in TM0, TL8, TT16, TI24, MO8, MO9.
  assert (RR0 : rr = []) by (destruct rr as [|r1 rr1]; [reflexivity| cbn [stk_shape ps_mode container_mode] in SHP1; destruct SHP1 as [SH0 _]; discriminate]).
  subst rr. cbn [PEC.stk_conv rev map app] in Epre. subst pre. cbn [length Z.of_nat app Z.mul Z.add] in T.
  assert (ET : T = vb1) by (unfold T; clear; lia).
  pose proof (step_accept p X1 _ [] HALT1 HS1 eq_refl eq_refl) as STEP.
  assert (EXF : w_done true (w_more false (w_stk [] X1)) = run (Datatypes.S i1) p UbjRef.init) by (rewrite <- STEP; unfold X1; apply PEACLPD.step_run).
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  pose proof PA as (_ & PD1 & _ & _ & _ & _ & _ & _ & _ & PSRC1 & _ & _ & PC320 & PTB1 & PVEC & _). cbn [PM.p_b PM.p_k PM.p_stk PM.p_src PM.p_tb app] in PVEC, PSRC1, PTB1.
  destruct PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & CB & AN & EL). cbn [length Z.of_nat app Pos.of_succ_nat Pos.succ] in VC8, Hlen, CB, AN.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 1, sp - 256 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 md1 fb _ _ HHi FOK' PA) as ((_ & _ & _) & _ & _ & _ & _ & _ & OVIS & _ & _). fold Hi in OVIS. fold op in OVIS.
  assert (V360 : L5.u64_at RSEGS MVi (op + 360) T).
  { rewrite ET. apply (proj2 (L5A.u64_at_vis Hi M1 (op + 360) vb1 (OVIS (op + 360) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). exact VC0. }
  pose proof (PM.pow2_pos vk1 ltac:(clear - Hk; lia)) as P2k.
  set (LBi := PEC.owned (PM.PST 1 0 dp1 src1 tb1 tg1 vb1 vk1 ([] ++ [PEC.ps_conv (PS Maccept tl tty ti)])) en1 k1 ++ LBX) in *.
  set (qc := PM.sr_qc src1) in *.
  set (LBt := (PM.vs_own tb1 ++ PEC.enc_own en1 ++ PESK.sink_own k1) ++ LBX).
  set (LBc := (qc, PM.CHUNK) :: LBt).
  assert (EPO : LBi = (qc, PM.CHUNK) :: (vb1, 32 * 2 ^ vk1) :: LBt) by (unfold LBi, LBt, LBc, PEC.owned, PM.parser_own, PM.src_own, PM.vec_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb app]; reflexivity).
  assert (INCc : forall b, In b LBc -> In b LBi) by (intros b Hb; rewrite EPO; destruct Hb as [<-|Hb]; [left; reflexivity| right; right; exact Hb]).
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRB1.
  assert (BRBc : forall b, In b LBc -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; exact (BRB1 b (INCc b Hb))).
  assert (AOF' : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF' a n) by (intros a n X1' X2'; apply PMAUAR.aobjA_push; apply AOF; [exact X1'| exact X2']).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WB1 & _).
  assert (Ivb : In (vb1, 32 * 2 ^ vk1) LBi) by (rewrite EPO; right; left; reflexivity).
  destruct (WB1 _ Ivb) as ((Bb0 & _ & _ & _ & Bb4 & Bb5) & _). cbn [fst snd] in Bb0, Bb4, Bb5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Bb5.

  pz PEALPP1.alpH1_conc fx1 R1 T ti 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & _ & _ & _ & EW).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LBi FF' LK1 cr1 Aw1 M1 md1 fx1 fx3 R1 PEACLPD.LPHEAD R3 0xaa084 M3v (fun a => op + 368 <= a < op + 376) K HHi AMi MS3 MG3).
  { intros a Ha Nw. apply FRZ3; [exact Ha| clear - Nw; lia]. }
  { intros a Ha Wa. split.
    - apply (L5SAR.fframe_client L ar LBi FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - Wa Eop; lia].
    - clear - Wa O1. lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict Hi M3 = M3v) in VIS3.
  assert (W368 : L5.u64_at RSEGS M3 (op + 368) vb1).
  { apply (proj1 (L5A.u64_at_vis Hi M3 (op + 368) vb1 (OVIS (op + 368) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))).
    rewrite VIS3. rewrite <- ET. exact EW. }
  assert (HHs : ri_inv HI (PM.vec_own vb1 vk1 ++ LBc) FF' LK1 cr1 Aw1 M3 (vml_of md3)).
  { rewrite EPO in HH3. exact (PMARS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH3). }
  assert (EK01 : L5SAR.ek L ar LBc FF' (sp - 256) 12288 [(op + 368, 8)] M1 M3).
  { apply (L5SAR.ek_piece L ar LBc FF' (sp - 256) 12288 [(op + 368, 8)] M1 M3 (fun a => op + 368 <= a < op + 376) FR3).
    intros a Ha _ O X. apply (O (op + 368, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
  assert (EKb3 : L5SAR.ek L ar LBX FF sp 32768 WR M M3).
  { apply (L5SAR.ek_trans L ar LBX FF sp 32768 WR M M1 M3 EKbi).
    apply (L5SAR.ek_piece L ar LBX FF sp 32768 WR M1 M3 (fun a => op + 368 <= a < op + 376) FR3).
    intros a Ha Hc Ho X. apply (Ho (PMSP.o_vec AD fb, 24)); [unfold WR; wr_mem 5| wr_rng; clear - X Eop; lia]. }
  assert (WAPP1 : PMKA.wapp [(op + 368, 8)]).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG; lia. }
  assert (OUT1 : forall a n, (a + n <= op + 368 \/ op + 376 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 368, 8)] i).
  { intros a n Y' i Hi' r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi' Hr Y'. lia. }
  assert (OUTBi : forall q m, In (q, m) LBi -> PMKA.blk_out [(op + 368, 8)] q m).
  { intros q m Hq i Hi' r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 384 HHi Hq (AOF' op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))) as [Z'|Z']; clear - Hi' Hr Z'; lia. }
  assert (SHM1 : forall a0 n0, 0 <= a0 -> a0 + n0 <= 2 ^ 47 -> PMFA.agsh M1 M3 a0 n0).
  { intros a0 n0 Ha Hn0 x Hx. pose proof (PMKA.S_in_shadow x ltac:(clear - Ha Hn0 Hx; lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
    apply FR3; [clear - SX; lia| intros Y'; clear - Y' SX OBIG; lia]. }

  pose proof ANN as ASH. unfold PECSA.ann_shrink_spec, PMSAX.ann_shrink_spec in ASH.
  apply (ASH fx3 R3 M3 md3 K LBc FF' LK1 Aw1 cr1 (op + 360) vb1 vk1 1 [] (sp - 256) 0xb2a18 HHs AM3 K0); clear ASH.
  { split; [rewrite L5K.rl1; exact Y1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (KS3 2%nat) by inl; exact J2|].
    split; [rewrite L5K.rl3; rewrite (KS3 3%nat) by inl; rewrite J3; rewrite <- L5K.rl3; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS3 4%nat) by inl; rewrite J4; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536.
    split; [apply (L5SAR.astk_grows ar M1 M3 (sp - 256) 12288); [apply (L5SAR.astk_sub ar M1 M1 sp 32768 256 12288 ASTKi (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 256) with (sp + (-16) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]| exact MGM3]|].
    apply szk; [exact EKb3| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 256 - 12288) with (sp + (-784) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 256) F 1 (sp - 256 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact Y10. }
  { rewrite L5K.rl11. exact Y11. }
  { apply AOF'; clear - Eop; lia. }
  { replace (op + 360) with (op + 45 * 8) by (clear; lia). rewrite Z_mod_plus_full. exact O8. }
  { apply (PMKA.acc_keepA' L ar LBc FF' (sp - 256) 12288 [(op + 368, 8)] M1 M3 EK01 WAPP1 FRB1 (op + 360) 24 (AOF' (op + 360) 24 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
    intros a Ha. apply PC320. clear - Ha; lia. }
  { cbn [length Z.of_nat]. clear - P2k; lia. }
  { apply (PMKA.u64_keepA RSEGS L ar LBc FF' (sp - 256) 12288 [(op + 368, 8)] M1 M3 EK01 WAPP1 FRB1 (op + 360) vb1 (AOF' (op + 360) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VC0].
    apply OUT1. clear; lia. }
  { replace (op + 360 + 8) with (op + 368) by (clear; lia). replace (vb1 + 32 * Z.of_nat (length (@nil PM.pstate))) with vb1 by (cbn; clear; lia). exact W368. }
  { apply (PMKA.u64_keepA RSEGS L ar LBc FF' (sp - 256) 12288 [(op + 368, 8)] M1 M3 EK01 WAPP1 FRB1 (op + 360 + 16) _ (AOF' (op + 360 + 16) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VC16].
    apply OUT1. clear; lia. }
  { clear - Hk; lia. }
  { exact Hal. }
  { intros i Hi'. apply MGM3. apply DB. exact Hi'. }
  { apply (PMFA.accA_agree M1 M3); [apply SHM1; clear - Bb0 Bb5 P2k; lia| exact CB]. }
  { apply (PMFA.annA_agree M1 M3); [apply PMKA.mod16_8'; exact Hal| clear - P2k; lia| | apply SHM1; clear - Bb0 Bb5; lia| exact AN].
    replace (32 * 2 ^ vk1) with ((4 * 2 ^ vk1) * 8) by (clear; lia). apply Z_mod_mult. }
  { intros i Hi'. cbn [length] in Hi'. clear - Hi'; lia. }
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 VEC4 ACC4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
  change (PMSPA.pm_scr 0) with 12288 in HP4.
  set (s4 := PM.PST 1 0 dp1 src1 tb1 tg1 vb1 vk1 []) in *.
  assert (EO4 : PEC.owned s4 en1 k1 = PEC.owned (PM.PST 1 0 dp1 src1 tb1 tg1 vb1 vk1 ([] ++ [PEC.ps_conv (PS Maccept tl tty ti)])) en1 k1) by reflexivity.
  assert (HH4' : ri_inv HI (PEC.owned s4 en1 k1 ++ LBX) FF' LK4 cr1 Aw4 M4 (vml_of md4)).
  { rewrite EO4. change (PEC.owned (PM.PST 1 0 dp1 src1 tb1 tg1 vb1 vk1 ([] ++ [PEC.ps_conv (PS Maccept tl tty ti)])) en1 k1 ++ LBX) with LBi. rewrite EPO.
    exact (PMARS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH4). }
  assert (EK12 : L5SAR.ek L ar LBc FF' (sp - 256) 12288 [(op + 368, 8)] M3 M4).
  { apply (L5SAR.ek_W L ar LBc FF' (sp - 256) 12288 [(op + 368, 8)] [] M3 M4); [| intros a _ r0 Hr0; destruct Hr0].
    apply (L5SAR.ek_callee L ar LBc [] FF' [] (sp - 256) 12288 (sp - 256) 12288 [] [] M3 M4 HP4); [clear; lia| clear; lia| intros a _ _ r0 Hr0; destruct Hr0]. }
  pose proof (L5SAR.ek_trans L ar LBc FF' (sp - 256) 12288 [(op + 368, 8)] M1 M3 M4 EK01 EK12) as EK02.
  assert (EK02f : L5SAR.ek L ar LBc FF (sp - 256) 12288 [(op + 368, 8)] M1 M4).
  { intros a (Ha & Hc & Ho). apply EK02. split; [exact Ha|]. split; [exact (L5SAR.aclient_cons L ar LBc FF (F, 1, sp - 256 + 32) (sp - 256) 12288 a Hc)| exact Ho]. }
  assert (PD4 : L5.defined M4 op 384).
  { intros i Hi'. apply (proj2 (proj2 HP4)); [clear - Hi' O1 O3; lia| | apply MGM3; apply PD1; exact Hi'].
    apply (L5SAR.fframe_client L ar LBc FF' (sp - 256) 12288 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - Hi' Eop; lia]. }
  destruct (BRBc _ (or_introl eq_refl)) as (Xq1 & Xq2). cbn [fst snd] in Xq1, Xq2.
  assert (MID4 : amid fx4 R4 M4 md4 LK4 Aw4 cr1 s4 sm1 en1 k1 e1 (w_stk [] X1)).
  { split; [exact (lregs_pres R3 R4 (lregs_keep R1 R3 (proj1 MID) ltac:(intros j Hj; apply KS3; revert j Hj; apply (L5K.incl_b _ PEALPP1.KS_alpH1); vm_compute; reflexivity)) RP4)|].
    unfold PEACLPD.lmem. change (PMSPA.pm_scr 10) with 32768.
    split; [| split; [| split; [| split; [exact ST| split; [exact EIMP| exact CK]]]]].
    -
      assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 32768 (sp - 256) (own sp R) F 1 WR (PEC.owned s4 en1 k1) M3 md3 LK1 cr1 Aw1).
      { rewrite EO4. apply (PMAUK.binv_pieceW L ar HI M model LBX FF LK Aw sp 32768 (sp - 256) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PEC.owned s en k) G'
               _ _ M1 md1 LK1 cr1 Aw1 M3 md3 (fun a => op + 368 <= a < op + 376) BI HH3 AM3 MRT3 MGM3 FR3).
        intros a Y'. split.
        + unfold PEACLPD.ocell. clear - Y' O2 GSLO Eop F2 FSCEIL. lia.
        + right; right; right. intros O. apply (O (PMSP.o_vec AD fb, 24)); [unfold WR; wr_mem 5| wr_rng; clear - Y' Eop; lia]. }
      apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 32768 (sp - 256) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PEC.owned s en k) G'
               _ _ (PEC.owned s4 en1 k1) ((qc, PM.CHUNK) :: (PM.vs_own tb1 ++ PEC.enc_own en1 ++ PESK.sink_own k1)) (PEC.owned s4 en1 k1) M3 md3 LK1 cr1 Aw1 M4 md4 LK4 cr1 Aw4 12288 [] BI3);
        [| exact HH4'| exact AM4| exact MRT4| exact INCAw4| exact INCLK4| clear; lia| clear; lia| intros rr0 a Hr0 _; destruct Hr0| intros a _ _ r0 Hr0; destruct Hr0| intros a X'; exact X'].
      change (((qc, PM.CHUNK) :: (PM.vs_own tb1 ++ PEC.enc_own en1 ++ PESK.sink_own k1)) ++ LBX) with LBc. exact HP4.
    -
      apply (cpre_stepC LBc (sp - 256) 12288 [(op + 368, 8)] M1 M4 X1 (PM.PST 1 0 dp1 src1 tb1 tg1 vb1 vk1 ([] ++ [PEC.ps_conv (PS Maccept tl tty ti)])) sm1 en1 k1 e1 (w_stk [] X1) s4 e1 EK02f WAPP1 BRBc).
      + intros x Hx. right. apply in_or_app. right. apply INCS. exact Hx.
      + intros x Hx. right. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hx.
      + intros x Hx. right. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hx.
      + left. reflexivity.
      + intros i Hi' N1 _. apply (OUT1 i 1); clear - Hi' N1; lia.
      + intros q c Hq. apply OUTBi. unfold LBi. apply in_or_app. right. apply INCS. exact Hq.
      + intros q c Hq. apply OUTBi. unfold LBi, PEC.owned. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hq.
      + intros q c Hq. apply OUTBi. unfold LBi, PEC.owned. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hq.
      + apply OUTBi. exact (INCc _ (or_introl eq_refl)).
      + reflexivity. + reflexivity. + reflexivity.
      + apply (parser_vec_updA M1 M4 op ois _ [] PA ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia)); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb].
        * apply (PMKA.agA_obj L ar _ FF' _ _ _ M1 M4 EK02 WAPP1 FRB1 op 360 (AOF' op 360 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT1. clear; lia.
        * exact (PMKA.agsh_obj L ar _ FF' _ _ _ M1 M4 EK02 WAPP1 FRB1 op 384 (AOF' op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
        * exact PD4.
        * exact VEC4.
        * exact Xq1.
        * unfold PM.CHUNK in Xq2 |- *. clear - Xq2; lia.
        * apply (PMKA.agA_blk L ar _ FF' _ _ _ M1 M4 EK02 WAPP1 BRBc _ _ (or_introl eq_refl)). apply OUTBi. exact (INCc _ (or_introl eq_refl)).
        * intros c0 n0 p0 E0. assert (Ip : In (p0, c0) LBc) by (right; apply in_or_app; left; apply in_or_app; left; rewrite E0; left; reflexivity).
          apply (PMKA.agA_blk L ar _ FF' _ _ _ M1 M4 EK02 WAPP1 BRBc _ _ Ip). apply OUTBi. exact (INCc _ Ip).
      + change (PMSTA.base_okA RSEGS PMA.AD M4). apply (PMASK.base_keep L ar C LY LBc FF' _ _ _ M1 M4 EK02); [| exact BASE]. intros a Ha r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O1; lia.
      + apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBc FF' _ _ _ M1 M4 EK02 e1 PECSA.addrs_wf_A); [| exact ERR].
        intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
        split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. intros r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - DI Hr O1; lia.
      + destruct CL as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9). unfold PEC.clink, s4.
        cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_stk PEC.stk_conv rev map PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src] in *.
        split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [reflexivity|]. split; [exact L5'|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
      + cbn [s_ec w_stk]. apply (PECFA.ec_state_keepA RSEGS AD L ar LBc FF' _ _ _ M1 M4 EK02 WAPP1 FRB1 fb (s_ec X1) cat (AOF' oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact ECS].
        intros i Hi' r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi' Hr Eop Eoec. lia.
      + cbn [s_ec w_stk]. exact ECI.
      + exact CP.
    -
      apply (lspill_callee LBc 12288 [] M3 M4 HP4 ltac:(clear; lia) ltac:(intros rr0 a Hr0; destruct Hr0)).
      apply (PEACLPD.lspill_agree M1 M3 sp F _ _ _ ltac:(clear - GSLO GSPT; lia) ltac:(clear - GSHI GSPT; lia) LSP).
      intros a Ha. apply FR3; [clear - Ha GSLO GSHI GSPT; lia| clear - Ha O2 GSLO Eop F2 FSCEIL; lia]. }

  keep_only MID4 EXF. rename MID4 into MID. unfold s4 in MID. clear s4.
  destruct (md_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as (MO8 & MO9 & _ & _). cbn [PM.p_more PM.p_done] in MO8, MO9.
  entry_facts. frame_facts. piece_ctx MID. fold Hi in MO8, MO9. fold MVi in MO8, MO9.
  pz PEALPP1.alpH1b_conc fx4 R4 0 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _ & _ & _ & _ & D9 & M8).
  apply (finish 0 1 (w_done true (w_more false (w_stk [] X1))) (Datatypes.S i1) _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 M5v 0xb2a18 MID MS5 MG5).
  - intros i Hi' N1. apply FRZ5; [exact Hi'| clear - N1; lia].
  - intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEALPP1.KS_alpH1b). vm_compute. reflexivity.
  - exact M8.
  - exact D9.
  - left; reflexivity.
  - right; reflexivity.
  - exact EXF.
  - unfold halted. cbn [s_halt s_done s_more w_done w_more w_stk]. rewrite orb_true_r. reflexivity.
  - pose proof CP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9).
    unfold PEC.clink, set_md. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_done w_more w_stk PEC.b2z PEC.stk_conv rev map PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src] in *.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact L3|]. split; [exact L4|]. split; [intros X' _; discriminate|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
  - reflexivity.
Qed.

Lemma loop : forall n, 0 <= n -> forall (fx1 : FPState) R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (i1 : nat),
  amid fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 (run i1 p UbjRef.init) -> halted (run i1 p UbjRef.init) = false -> mu p (run i1 p UbjRef.init) = n ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R1 PEACLPD.LPHEAD M1 md1) K.
Proof.
  intros n. pattern n. apply (well_founded_ind (Zwf_well_founded 0)). clear n.
  intros n IHn Hn fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT EM.
  pose proof POK as (BOK & _).
  assert (IH : forall (fx2 : FPState) R2 M2' md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2, amid fx2 R2 M2' md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 (run i2 p UbjRef.init) ->
      halted (run i2 p UbjRef.init) = false -> mu p (run i2 p UbjRef.init) < mu p (run i1 p UbjRef.init) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 PEACLPD.LPHEAD M2' md2) K).
  { intros fx2 R2 M2' md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2 MID2 HALT2 LT2.
    pose proof (run_ginv p BOK i2 UbjRef.init (ginv_init p)) as GI2.
    assert (N2 : 0 <= mu p (run i2 p UbjRef.init)) by (pose proof (mu_pos p _ HALT2 GI2); clear - H; lia).
    exact (IHn (mu p (run i2 p UbjRef.init)) ltac:(unfold Zwf; clear - Hn LT2 N2 EM; lia) N2 fx2 R2 M2' md2 LK2' Aw2 cr2 s2 sm2 en2 k2 e2 i2 MID2 HALT2 eq_refl). }
  destruct (PEACLPD.lp_split (PEACLPD.top_mode (run i1 p UbjRef.init))) as [TG|[TG|[TG|TG]]].
  - destruct TG as [TG|[TG|[TG|[TG|TG]]]].
    + exact (arm_Mroot fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT TG IH).
    + exact (arm_Maccept fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT TG IH).
    + exact (arm_Mval fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT TG IH).
    + exact (arm_Mtval fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT TG IH).
    + exact (arm_Mival fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT TG IH).
  - destruct TG as [TG|TG].
    + exact (arm_Marray fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT TG IH).
    + exact (arm_Mtarray fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT TG IH).
  - destruct TG as [TG|TG].
    + exact (arm_Mkey fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT TG IH).
    + exact (arm_Mtkey fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT TG IH).
  - destruct TG as [TG|TG].
    + exact (arm_Miarray fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT TG IH).
    + exact (arm_Mikey fx1 R1 M1 md1 LK1 Aw1 cr1 s1 sm1 en1 k1 e1 i1 MID HALT TG IH).
Qed.

Lemma frame_body (fx1 : FPState) R1 M1 model1 R2 :
  getr R1 (reg 2) = Z_to_bv 64 (sp - 256) -> getr R1 (reg 8) = Z_to_bv 64 sp -> getr R1 (reg 9) = Z_to_bv 64 (sp - 256) ->
  getr R1 (reg 19) = Z_to_bv 64 oec -> getr R1 (reg 21) = Z_to_bv 64 op -> getr R1 (reg 22) = Z_to_bv 64 2147450880 ->
  (forall j, In j [3; 4]%nat -> getr R1 (reg j) = getr R (reg j)) ->
  own sp R M1 -> L5.u64_at RSEGS M1 (sp - 144) ov -> model_rt model model1 ->
  L5SAR.ek L ar (PEC.owned s en k ++ LBX) FF sp 32768 [] M M1 -> L5SAR.dk L ar (PEC.owned s en k ++ LBX) FF sp 32768 M M1 ->
  getr R2 10%bv = Z_to_bv 64 F -> regs_preserved R1 R2 -> L5CA.amodel_ok Aw model2 -> model_rt model1 model2 ->
  L5CA.astk ar M2 sp 32768 -> L5SAR.ek L ar LBX FF sp 32768 [] M M2 -> L5SAR.dk L ar LBX FF sp 32768 M M2 ->
  L5SAR.ek L ar (PEC.owned s en k ++ LBX) FF sp 32768 [] M1 M2 -> L5SAR.dk L ar (PEC.owned s en k ++ LBX) FF sp 32768 M1 M2 ->
  (forall a, sp - 256 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  L5.writable RSEGS (mrestrict (ahid Aw model2) M2) F 128 ->
  L5.writable RSEGS (mrestrict (ahid Aw model2) M2) (F / 8 + SB) 16 ->
  L5KA.zeros_at (mrestrict (ahid Aw model2) M2) (F / 8 + SB) 16 ->
  L5.u64_at RSEGS (mrestrict (ahid Aw model2) M2) (F + 128 - 8) fl -> L5.writable RSEGS (mrestrict (ahid Aw model2) M2) fl 1 ->
  L5.defined (mrestrict (ahid Aw model2) M2) F 128 ->
  L5A.avis (ahid Aw model2) F 128 -> L5A.avis (ahid Aw model2) (F / 8 + SB) 16 -> L5A.avis (ahid Aw model2) fl 1 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R2 0xb2564 M2 model2) K.
Proof.
  intros T2 T8 T9 T19 T21 T22 K34 OWN1 C144 MRT1 EK01f DK01f G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL.
  entry_facts. frame_facts.
  pose proof CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  pose proof (L5SAR.ek_trans L ar LB FF sp 32768 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 32768 M M1 M2 DK01f DK12f) as DK02f.
  assert (HH2 : ri_inv HI LB FF' LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (NCS0 : forall a, sp - 256 <= a < sp -> ~ aclient L ar LB FF sp 32768 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 32768 a HH SPT Hc) as [Y'|Y']; [clear - Xa Y'; lia| clear - Xa Y' SLO; lia]. }
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j))
    by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 256)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 256)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B19R : getr R2 (reg 19) = Z_to_bv 64 oec) by (rewrite (R2c 19%nat) by inl; exact T19).
  assert (B21R : getr R2 (reg 21) = Z_to_bv 64 op) by (rewrite (R2c 21%nat) by inl; exact T21).
  assert (B22R : getr R2 (reg 22) = Z_to_bv 64 2147450880) by (rewrite (R2c 22%nat) by inl; exact T22).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).

  assert (OWN2 : own sp R M2) by (apply (PEACLPD.own_agree sp R M1 M2 ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia) OWN1); intros a Ha; unfold PEACLPD.ocell in Ha; apply AGF; clear - Ha; lia).
  assert (BI2 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 32768 (sp - 256) (own sp R) F 1 WR (PEC.owned s en k) M2 model2 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH2|]. split; [exact AM2|]. split; [eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact ASTK2|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 32768 WR [] M M2 EK02); intros a _ r0 []|]. split; [exact DK02|]. split; [exact OWN2|].
    change (ff_bytes 1 / 8) with 16. apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 16 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (CP2 : PECA.crun_preA RSEGS AD AAD EE L ar P M2 fb p UbjRef.init s str sm en k e cat).
  { apply (cpre_keepA sp 32768 [] M M2 UbjRef.init s sm en k e EK02f PMKA.wapp_nil BRB); [intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CPRE]. }
  assert (ZF16 : L5KA.zeros_at MV2 (F / 8 + 2147450880) 16) by (unfold SB in FSHZ; exact FSHZ).
  pose proof (pfacts_bc0 M2 model2 LK2 cr Aw s sm en k e UbjRef.init BI2 CP2) as VF0. fold H2 in VF0. fold MV2 in VF0. open_vf0 VF0.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF' LK2 cr Aw M2 model2 HH2) as (_ & VIS & _). fold H2 in VIS.
  assert (C144v : L5.u64_at RSEGS MV2 (sp - 144) ov).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (sp - 144) ov (VIS (sp - 144) 8 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia))).
    apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi'; apply AGF; clear - Hi'; lia| clear - SLO SPT; lia| clear - SHI SPT; lia| exact C144]. }
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 1, sp - 256 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 fb _ s HH2 FOK' (proj1 CP2)) as ((_ & _ & _) & _ & _ & _ & _ & _ & OVIS & _ & _). fold H2 in OVIS. fold op in OVIS.
  assert (D9v : L5.u8_at RSEGS MV2 (op + 9) 0).
  { pose proof (proj1 CP2) as (_ & _ & _ & _ & P9 & _). pose proof CL as (_ & Ldone & _). rewrite Ldone in P9. cbn [PEC.b2z s_done UbjRef.init] in P9.
    apply (proj2 (L5A.u8_at_vis H2 M2 (op + 9) 0 (OVIS (op + 9) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). exact P9. }

  pose proof (PEALPP1.alpB_conc fx1 R2 MV2 (VALU 0 0 0 0 0 0)) as PB. unfold VALU in PB. cbn beta iota in PB. L5SAR.feed PB fcl.
  destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y20 & Y23 & Y24 & Y25 & Y26 & Y27
                 & S216 & S192 & S136 & S208 & S200 & S184 & S240 & S152 & S224 & S232 & S168 & S248 & S112 & S160
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S176 & _ & _
                 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & C104 & S144).
  clear VF1 VF2 VF3 VF4 VF5 VF6 VF7 VF8 VF9 VF10 VF11 VF12 VF13 VF14 VF15 VF16 VF17 VF18 VF19 VF20 VF21 VF22 VF23 VF24 VF25 VF26 VF27 VF28 VF29 VF30
        VF31 VF32 VF33 VF34 VF35 VF36 VF37 VF38 VF39 VF40 VF41 VF42 VF43 VF44 VF45 VF46 VF47 VF48 VF49 VF50 VF51 VF52 VF53 VF54 VF55 VF56 VF57 VF58 VF59 VF60
        VF61 VF62 VF63 VF64 VF65 VF66 VF67 VF68 VF69 VF70 VF71 VF72 VF73 VF74 VF75 VF76 VF77 VF78 VF79 VF80 VF81 VF82 VF83 VF84 VF85 VF86 VF87 VF88.
  set (W3 := fun a => (sp - 256 <= a < sp) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16)).
  pose proof GFR as (GF1 & GF2 & GF3 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb2564 R3 PEACLPD.LPHEAD M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; clear - X'; lia| intros X'; apply Hn; right; left; clear - X'; lia| intros X'; apply Hn; right; right; clear - X'; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT; lia| intros Y'; clear - Y'; lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 1 (sp - 256 + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 1 (sp - 256 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X'; lia.
    - destruct Wa as [X'|[X'|X']]; [clear - X' SLO SPT; lia| clear - X' GFR; lia| clear - X' D1; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23 : L5SAR.ek L ar LB FF sp 32768 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 32768 [] M2 M3 W3 FR3). intros a Ha Hc _ X'. destruct X' as [X'|[X'|X']].
    - apply (NCS0 a); [clear - X'; lia| exact Hc].
    - destruct (APART a 1 sp 32768 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y' & _). change (ff_bytes 1) with 128 in Y'. clear - X' Y'; lia.
    - destruct (APART a 1 sp 32768 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y' & _). change (ff_bytes 1 / 8) with 16 in Y'. unfold SB in Y'. clear - X' Y'; lia. }
  assert (SV3 : forall a v, sp - 256 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
  { intros a v Ha1 Ha2 X'. apply (proj1 (L5A.u64_at_vis H2 M3 a v (VIS a 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS3. exact X'. }
  assert (OWN3 : own sp R M3) by (unfold PEACLPD.own; repeat split; (apply SV3; [clear; lia| clear; lia| assumption])).
  assert (LSP3 : PEACLPD.lspill M3 sp F op ov oec) by (unfold PEACLPD.lspill; repeat split; (apply SV3; [clear; lia| clear; lia| assumption])).
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 32768 (sp - 256) (own sp R) F 1 WR (PEC.owned s en k) M3 model3 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2]| exact MRT3]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 32768 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 32768 WR [] M M3); [exact (L5SAR.ek_trans L ar LBX FF sp 32768 [] M M2 M3 EK02 (PMKA.ek_sublb L ar LB LBX FF sp 32768 [] M2 M3 INCX EK23))| intros a _ r0 []]|].
    split; [exact (L5SAR.dk_trans L ar LBX FF sp 32768 M M2 M3 DK02 (L5SAR.dk_grows L ar LBX FF sp 32768 M2 M3 MGM3))|]. split; [exact OWN3|].
    change (ff_bytes 1 / 8) with 16. apply (L5.defined_grows M2 M3 _ _ MGM3). apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 16 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (CP3 : PECA.crun_preA RSEGS AD AAD EE L ar P M3 fb p UbjRef.init s str sm en k e cat).
  { apply (cpre_keepA sp 32768 [] M2 M3 UbjRef.init s sm en k e EK23 PMKA.wapp_nil BRB); [intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP2]. }
  assert (MID3 : amid fx3 R3 M3 model3 LK2 Aw cr s sm en k e (run 0 p UbjRef.init)).
  { split.
    - unfold PEACLPD.lregs, PEACLPD.JT. fold op oec.
      split; [rewrite (KS3 2%nat) by inl; rewrite (R2c 2%nat) by inl; exact T2|]. split; [rewrite (KS3 8%nat) by inl; exact B8R|].
      split; [rewrite (KS3 9%nat) by inl; rewrite (R2c 9%nat) by inl; exact T9|]. split; [exact Y18|]. split; [rewrite (KS3 19%nat) by inl; exact B19R|].
      split; [exact Y20|]. split; [rewrite (KS3 21%nat) by inl; exact B21R|]. split; [rewrite (KS3 22%nat) by inl; exact B22R|].
      split; [exact Y23|]. split; [exact Y24|]. split; [exact Y25|]. split; [exact Y26|]. split; [exact Y27|].
      split; [rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; apply K34; inl| rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; apply K34; inl].
    - unfold PEACLPD.lmem. change (PMSPA.pm_scr 10) with 32768.
      split; [exact BI3|]. split; [exact CP3|]. split; [exact LSP3|].
      split; [unfold PMSPA.src_step; split; [reflexivity|]; split; [reflexivity|]; split; [clear; lia|]; split; [intros X'; exact X'| clear; lia]|].
      split; [intros X'; exact X'| unfold PMSP.credit_keep; clear; lia]. }
  pose proof POK as (BOK & _).
  pose proof (mu_pos p UbjRef.init eq_refl (ginv_init p)) as MU0.
  exact (loop (mu p UbjRef.init) ltac:(clear - MU0; lia) fx3 R3 M3 model3 LK2 Aw cr s sm en k e 0%nat MID3 eq_refl eq_refl).
Qed.

End Frame.

Theorem parse_call : srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx) RSEGS R (pa_parse AD) M model) K.
Proof.
  entry_facts.
  pose proof AM as (Mh & MI).
  pose proof A10 as X10. pose proof A11 as X11. pose proof A12 as X12.
  rewrite L5K.rl10 in X10. rewrite L5K.rl11 in X11. rewrite L5K.rl12 in X12. fold op in X10. fold ov in X11. fold oec in X12.
  pose proof CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (BASE' : PMSTA.base_okA RSEGS PMA.AD M) by exact BASE.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE') as (IC0 & CSBv & CUARv). fold H in IC0, CSBv, CUARv. fold MV in IC0, CSBv, CUARv.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 32768 256 HH ASTK ltac:(clear; lia)) as (SL256 & SH256 & WS256). fold H in WS256. fold MV in WS256.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & _).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK cr Aw M model fb _ s HH FOK PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold H in Zop, Z32, Z20, OWR, OVIS. fold MV in Zop, Z32, Z20, OWR. fold op in Zop, Z32, Z20, OWR, OVIS.
  assert (ECX : exists v c, PMSPA.ec_at RSEGS M oec v c).
  { pose proof ECS as E0. unfold PECA.ec_stateA in E0. fold oec in E0.
    lazymatch type of E0 with (if ?c then _ else _) => destruct c; [destruct E0 as (v0 & _ & E1); exists v0; eexists; exact E1| exists 0, cat; exact E0] end. }
  destruct ECX as (ecv & ecc & ECat).
  pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK cr Aw M model fb ecv ecc HH FOK ECat) as ((_ & _ & _) & ZE & EW & _ & EU & _ & _). fold H in ZE, EW, EU. fold MV in ZE, EW, EU. fold oec in ZE, EW, EU.
  pose proof EA as (EVT & _ & _ & _ & _ & _ & _ & _ & EACC & _).
  pose proof (PMAPAR.ov_vis L ar C HI LY HIok _ _ LK cr Aw M model fb HH FOK (conj EVT (L5CBR.aacc_sub M ov 56 ov 8 EACC ltac:(clear; lia) ltac:(clear; lia))))
    as ((V1 & V8 & VBIG) & ZV & VW & V3 & VVT & _ & _). fold H in ZV, VW, VVT. fold MV in ZV, VW, VVT. fold ov in V1, V8, VBIG, ZV, VW, V3, VVT.
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF LK cr Aw M model 0x1335f0 16 HH ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)) as VT1.
  change (0x1335f0 / 8 + 2147450880) with 2147608254 in VT1. fold H in VT1. fold MV in VT1.
  assert (Q0a : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia). assert (Q0b : 0 <= op < 2 ^ 64) by (clear - O1 O3; lia).
  assert (Q0c : 0 <= ov < 2 ^ 64) by (clear - V1; lia). assert (Q0d : 0 <= oec < 2 ^ 64) by (clear - E1' E3'; lia).

  pose proof (PEALPP1.alpA_conc fx R MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | _ => 0 end)) as PP. cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [sya | unfold PEALPP1.aligned; sya | clear - SL256 SHI SPT; lia | clear - O2 SLO; lia | clear - E2' SLO; lia | clear - V3 SLO; lia
                             | clear - Eop Eoec Eov; lia | clear - O8; lia | clear - C8m; lia | clear - Q8; lia | clear - OBIG; lia | clear - EBIG; lia | clear - VBIG; lia
                             | clear - O1 O3; lia | clear - E1' E3'; lia | clear - O1; lia | clear - E1'; lia | clear - V1; lia | clear - V8; lia
                             | match goal with |- ?G => fail 100 "alpA feed:" G end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T19 & T21 & T22
                 & C144 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C256).
  unfold PMSPA.cfg. cbn [pa_parse AD PeCLayoutA.CADDR_A].
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb24ec R1 0x5e588 M1v (fun a => sp - 256 <= a < sp - 256 + 256) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X'; clear - X' Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL256 SHI SPT; lia| intros X'; clear - X'; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (NCS0 : forall a, sp - 256 <= a < sp -> ~ aclient L ar LB FF sp 32768 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 32768 a HH SPT Hc) as [Y'|Y']; [clear - Xa Y'; lia| clear - Xa Y' SL256; lia]. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 32768 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 32768 [] M M1 (fun a => sp - 256 <= a < sp - 256 + 256) FR1). intros a Ha Hc _ X'. apply (NCS0 a); [clear - X'; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 32768 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBX FF sp 32768 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBX FF sp 32768 M M1 INCX DK01f) as DK01.
  assert (SV1 : forall a v, sp - 256 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X'. apply (proj1 (L5A.u64_at_vis H M1 a v (VIS a 8 ltac:(clear - Ha1 SL256 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL256 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X'. }
  assert (OWN1 : own sp R M1) by (unfold PEACLPD.own; repeat split; (apply SV1; [clear; lia| clear; lia| assumption])).
  pose proof (SV1 (sp - 144) ov ltac:(clear; lia) ltac:(clear; lia) C144) as C144m.
  clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C256 SV1.

  assert (FRk1 : ff_room 1 FF LK) by (pose proof (FRM 1 ltac:(cbn; tauto)) as X'; unfold ff_room; clear - X'; lia).
  change 0x5e588 with (PMA.SM_PC 1).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 1 LBX (PEC.owned s en k) FF LK cr Aw sp 32768 (sp - 256) (sp - 104) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xb2564 ltac:(cbn; tauto) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 256) with (sp + (-16) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (PEACLPD.own_agree sp R Ma Mb ltac:(clear - SL256 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk1. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2' model2' F' fl' LK2' G2 G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART'.
  change (ff_bytes 1) with 128 in FW, FSHW, FSHZ, FLC, FLW, FDEF, VF, VSH, APART'. change (128 / 8) with 16 in FSHW, FSHZ, VSH, APART'.
  fold LB in EK12f, DK12f, APART'.
  apply (frame_body F' fl' LK2' M2' model2' G2 APART' fx1 R1 M1 model1 R2 T2 T8 T9 T19 T21 T22
           ltac:(intros j Hj; apply KS1; revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity)
           OWN1 C144m MRT1 EK01f DK01f G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL).
Qed.
End Call.

Theorem parse_ok : PECSA.parse_spec L ar HI P.
Proof.
  unfold PECSA.parse_spec, PECSPA.parse_spec.
  intros PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 ARGS CPRE INCS POK HBN CRED KONT.
  destruct ARGS as (A10 & A11 & A12).
  exact (parse_call PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 A11 A12 CPRE INCS POK HBN CRED KONT).
Qed.
End WithHeap.
End PEACLP.
