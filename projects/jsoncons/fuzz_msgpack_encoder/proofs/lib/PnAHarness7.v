(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAHarnessSK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5AFrameKR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunHA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.PnAHarnessStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206.PnAHarnessKit4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarnessSK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnRunNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAHarnessKit5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235.PnAHarnessP2.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PQHA7.
Import L5A. Import L5CA. Import L5SAR. Import PQHAS. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RSEGS := Asan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac hsc := first [ asm | apply UR | apply U_to | rk | gmem | (arith_goal; first [asm | alia]) | assumption ].
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Stage.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (R : bvmap 5 word)
          (V2 cls F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr : credit) (W : list L5.range).
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 160) (V2 - 160) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 5 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487392 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.
(* [comment removed for export] *)
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 5, V2 - 160 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 160 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Hypothesis FAL : F mod 2048 = 0.
Hypothesis WERR : forall a, L5.outside W a -> L5.outside (PmSpecs.PMSP.err_W PMA.AD) a.
Hypothesis WJNK : forall a, L5.outside W a -> L5.outside [(6896220, 4)] a.      (* [comment removed for export] *)
(* [comment removed for export] *)
Variable RES : credit.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 160 + 32) :: FF).

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PQHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PQHAK2.wapart_nil | (apply PQHAK2.wapart_cons; [cbn [fst snd]; lia| apply PQHAK2.wapart_nil])]])
  | (apply PQHAK2.wapart_nil) | lia ].


Lemma err_W_hull r : In r (PmSpecs.PMSP.err_W PMA.AD) -> (fst r = 0x692100 /\ snd r = 2) \/ (fst r = 0x6b3b50 /\ snd r = 544).
Proof.
  unfold PmSpecs.PMSP.err_W. cbn. intros Hr.
  destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; [left| right]; split; reflexivity.
Qed.

Lemma fb_mod8 fb k : fb mod 2048 = 0 -> (fb + 8 * k) mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite H, Z.add_0_r in Dm.
  replace (fb + 8 * k) with ((fb / 2048 * 256 + k) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(* [comment removed for export] *)
Definition AST0 (b' : Z) : NEMA.aest := NEMA.AEST (PQRHA.ast_init b') [] NEM.enc0 NESK.sink0.

Lemma mown_init qc b b' : PNRNA.mown (PQRHA.mparser_init qc b) (AST0 b') = PQRA.mown (PQRHA.mparser_init qc b) (PQRHA.ast_init b').
Proof. unfold PNRNA.mown, PQRA.mown, NEMA.aeown, AST0. cbn [NEMA.ae_a NEMA.ae_e NEMA.ae_s]. unfold NEM.enc_own, NESK.sink_own. cbn [NEM.en_k NEM.enc0 NESK.sk_c NESK.sink0 Z.eqb NEM.en_b NEM.ecap NESK.sk_b]. rewrite ?app_nil_r. reflexivity. Qed.

(* [comment removed for export] *)
Lemma init_facts qc b b' :
  PQRA.minv (PQRHA.mparser_init qc b) /\ PQMA.mgrow_ok (PQRHA.mparser_init qc b) /\ NEMA.ae_ok (AST0 b')
  /\ PQMA.cpl (PQRHA.mparser_init qc b) (NEMA.ae_a (AST0 b')) /\ NEMA.ebound (AST0 b') /\ NEMA.bal (AST0 b').
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - unfold PQRA.minv, PQRA.minv_d. cbn [PQMA.p_more PQMA.p_done PQMA.p_depth PQMA.p_stk length PQRHA.mparser_init].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    unfold PQRA.mstack_shape. cbn [length nth]. split; [lia|]. split; [unfold PQMA.MAX_DEPTH; lia|]. split; [left; reflexivity|].
    split; [intros i Hi; lia|]. intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [nth]. unfold PQMA.mstate_ok, PQMA.ms_root. cbn. lia.
  - unfold PQMA.mgrow_ok. cbn [PQMA.p_tb PQMA.p_bb PQMA.p_bg PQRHA.mparser_init]. split; [cbn; lia| reflexivity].
  - unfold NEMA.ae_ok, AST0. cbn [NEMA.ae_a NEMA.ae_kbb NEMA.ae_e NEM.en_depth NEM.enc0]. split; [|split; [vm_compute; reflexivity| vm_compute; reflexivity]].
    unfold PQMA.adaptor_ok. cbn [PQMA.a_lv PQMA.a_key PQMA.a_kg PQMA.a_kb PQMA.a_kbg PQRHA.ast_init].
    split. { unfold PQMA.lv_shape. cbn [length nth]. split; [lia|]. split; [unfold PQMA.MAX_DEPTH; lia|]. split; [reflexivity|].
             split; [intros i Hi; lia|]. intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [nth]. unfold PQMA.alvl_ok, PQMA.lv_root. cbn. lia. }
    unfold PQMA.ks_ok, PQMA.SMK, PQMA.SMB. cbn. split; (split; [lia| split; [lia| reflexivity]]).
  - reflexivity.
  - unfold NEMA.ebound, NEMA.esize, AST0. cbn [NEMA.ae_e NEM.en_n NEM.enc0]. apply Z.leb_le. vm_compute. reflexivity.
  - unfold NEMA.bal, NEMA.esize, NEMA.edepth, AST0. cbn. reflexivity.
Qed.

Lemma stage7 (PARSE : PNRNA.parse_specF RSEGS PMA.AD PnLayoutQA.QADDR_A PMA.AAD NemLayoutA.NEADDR_A L ar (fun _ : list (list Z) => HI) RES)
      (fx8 : FPState) (R8 : bvmap 5 word) (M8 : word -> option byte) (model8 : Model) (K : TSet)
      (LK8 : list fframe) (cr8 : credit) (A8 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (qc b b' : Z) (g : PMST.st) (c n : Z) :
  Bv W (PQRA.mown (PQRHA.mparser_init qc b) (PQRHA.ast_init b') ++ PM.vs_own s' ++ PM.vs_own s) M8 model8 LK8 cr8 A8 -> rinvH R R8 V2 cls F -> K [] ->
  PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M8 ->
  getr R8 (reg 1) = Z_to_bv 64 0xaf4f4 -> getr R8 (reg 10) = Z_to_bv 64 (F + 592) -> getr R8 (reg 11) = Z_to_bv 64 (F + 992) ->
  getr R8 (reg 12) = Z_to_bv 64 (F + 1232) -> getr R8 (reg 18) = Z_to_bv 64 2147450880 -> getr R8 (reg 20) = Z_to_bv 64 18446744073709551608 ->
  getr R8 (reg 21) = Z_to_bv 64 (F + 96) -> getr R8 (reg 22) = Z_to_bv 64 (F + 432) -> getr R8 (reg 23) = Z_to_bv 64 (F + 520) ->
  getr R8 (reg 24) = Z_to_bv 64 (F + 1232) -> getr R8 (reg 25) = Z_to_bv 64 (F + 592) -> getr R8 (reg 26) = Z_to_bv 64 (F + 1168) ->
  PQHAK5.hbaseN F M8 s s' sm -> PQHAK4.hpar4 F M8 (PQRHA.mparser_init qc b) (PQRHA.ast_init b') -> PQHAK4.hec4 F M8 0 c -> PQHAK5.hse0 L ar F M8 ->
  PQMA.acct n (PQRHA.mparser_init qc b) (PQRHA.ast_init b') sm -> NEMA.oacct n (PQRHA.mparser_init qc b) (AST0 b') sm ->
  L5.u64_at RSEGS M8 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M8 (V2 - 136) F ->
  PmSpecs.PMSP.credit_le (PM.credit_add (PM.credit_add (PNRNA.pot_runA L ar (PQRHA.mparser_init qc b) (AST0 b')) (PMSPA.scA L PNRNA.TSRES_ME)) RES) cr8 ->
  (forall (fx9 : FPState) (R9 : bvmap 5 word) (M9 : word -> option byte) (model9 : Model) (LK9 : list fframe) (cr9 : credit) (A9 : list (Z * Z))
          (s9 : PQMA.mpst) (st9 : NEMA.aest) (sm9 : PM.strm) (e9 b9 : bool),
      Bv W (PNRNA.mown s9 st9 ++ PM.vs_own s' ++ PM.vs_own s) M9 model9 LK9 cr9 A9 -> rinvH R R9 V2 cls F ->
      PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A (PMST.ST (PMST.st_loc g) (PMST.st_sys g) e9) M9 -> (PMST.st_err g = true -> e9 = true) ->
      getr R9 (reg 1) = Z_to_bv 64 0xaf508 -> getr R9 (reg 10) = Z_to_bv 64 (F + 592) -> getr R9 (reg 18) = Z_to_bv 64 2147450880 ->
      getr R9 (reg 20) = Z_to_bv 64 18446744073709551608 -> getr R9 (reg 21) = Z_to_bv 64 (F + 96) -> getr R9 (reg 22) = Z_to_bv 64 (F + 432) ->
      getr R9 (reg 23) = Z_to_bv 64 (F + 520) -> getr R9 (reg 24) = Z_to_bv 64 18446744073709551608 -> getr R9 (reg 25) = Z_to_bv 64 (F + 592) ->
      getr R9 (reg 26) = Z_to_bv 64 (F + 1168) ->
      PQHAK5.hbaseN F M9 s s' sm9 -> PQHAK4.hpar4 F M9 s9 (NEMA.ae_a st9) -> PQMA.mgrow_ok s9 -> NEMA.ae_ok st9 ->
      PQHAK5.hseF L ar F M9 (NEMA.ae_e st9) (NEMA.ae_s st9) ->
      PmSpecs.PMSP.credit_keep cr8 cr9 (PM.credit_add (PNRNA.pot_runA L ar (PQRHA.mparser_init qc b) (AST0 b')) RES) PmSpecs.PMSP.cr0 ->
      L5.u64_at RSEGS M9 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M9 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx9 R9 0xaff54 M9 model9) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx8 R8 0xcfdb4 M8 model8) K.
Proof.
  intros BI RI K0 LS R1a R10 R11 R12 R18 R20 R21 R22 R23 R24 R25 R26 HB0 HP0 HE0 HSE0 ACCT OACCT HSTKa HSTKb CRD KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X19 & X21 & X27 & X3 & X4).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PQHAK2.hf F) by (unfold PQHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  pose proof (init_facts qc b b') as (MINV0 & GROW0 & AEOK0 & CPL0 & EB0 & BAL0).
  set (P0 := PQRHA.mparser_init qc b) in *. set (ST0 := AST0 b') in *.
  set (LBX := (PM.vs_own s' ++ PM.vs_own s) ++ LB).
  assert (B1' : ri_inv HI (PNRNA.mown P0 ST0 ++ LBX) FF' LK8 cr8 A8 M8 (vml_of model8)).
  { unfold LBX, P0, ST0. rewrite mown_init. rewrite app_assoc. exact B1. }
  pose proof HB0 as (VS0 & IS0 & VI0). pose proof HP0 as (PA0 & AA0 & REF0 & ACC0). pose proof HE0 as (EV0 & EC0 & EZ0 & ED0).
  pose proof HSE0 as (SK0 & EN0).
  pose proof LS as (LSB & LSL & LSS & LSE).
  unfold PNRNA.parse_specF in PARSE.
  unfold PNRNA.margs3, PNRNA.mrun_pre, PNRNA.parse_post, PNRNA.mrun_fin, PQRA.bb_room, PMSPA.ec_at, PNRNA.W_mrun, PQRA.W_mrun, PGS.W_srcfG, PQMA.adaptor_W, NEM.enc_W,
         PNRNA.o_sink, PQRA.o_src, PQRA.o_tb, PQRA.o_bb, PQRA.o_stk, PQRA.o_a, PQRA.o_p, PQRA.o_is, PQRA.o_ec, PQRA.o_v,
         PmSpecs.PMSP.o_p, PmSpecs.PMSP.o_is, PmSpecs.PMSP.o_ec, PmSpecs.PMSP.o_v, PmSpecs.PMSP.err_W in PARSE.
  unfold PQMA.OFF_SRC, PQMA.OFF_TB, PQMA.OFF_BB, PQMA.OFF_STK, PQMA.AOFF_KEY, PNRNA.PARSE_H, PNRN.PARSE_H in PARSE.
  cbn [app qa_parse pa_tp pa_off_p pa_off_is pa_off_ec pa_off_v pa_errcat_guard pa_atexit PMA.AD PMA.AAD ADDR_A qa_off_a qa_off_vref PnLayoutQA.QADDR_A ne_off_sink NemLayoutA.NEADDR_A] in PARSE.
  apply (PARSE fx8 R8 M8 model8 K LBX FF' LK8 A8 cr8 (V2 - 160) 0xaf4f4 F c n P0 ST0 s' sm (PMST.st_err g) [] B1' B2 K0).
  { eapply PQHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PQHASK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PQHASK.callee_rs; eassumption. }
  { pose proof (Z.div_mod V2 32 ltac:(clear; lia)) as DM. rewrite V2A, Z.add_0_r in DM. replace (V2 - 160) with ((V2 / 32 * 2 - 10) * 16) by (clear - DM; lia). apply Z.mod_mul. clear; lia. }
  { exact (PQHASK.callee_frame FF V2 F FAL). }
  { split; [rewrite L5K.rl10; exact R10|]. split; [rewrite L5K.rl11; replace (F + 592 + 400) with (F + 992) by lia; exact R11| rewrite L5K.rl12; exact R12]. }
  { (* [comment removed for export] *)
    split; [exact PA0|]. split.
    { (* [comment removed for export] *)
      unfold NEMA.ae_atA, ST0, AST0. cbn [NEMA.ae_a NEMA.ae_kbb NEMA.ae_e NEMA.ae_s].
      split; [replace (F + 592 + 400) with (F + 992) by lia; exact AA0|]. split.
      - unfold NEM.kcontent, NEM.content_at, PQRHA.ast_init. cbn [PQMA.a_kb PM.vs_size PM.vs_data length Z.of_nat].
        split; [| reflexivity]. split; [| constructor]. intros i Hi. exfalso. clear - Hi. cbn in Hi. lia.
      - split; [exact EN0| exact SK0]. }
    split; [exact IS0|]. split; [replace (F + 592 + 496) with (F + 1088) by lia; replace (F + 592 + 400) with (F + 992) by lia; exact REF0|].
    split; [exact ACC0|].
    split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 EN0)))))))))|].
    split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 SK0)))))|].
    split; [exact LSB|]. split; [exact LSE|].
    split. { unfold NEMA.ec_stateA, PMSPA.ec_at. split; [exact EV0|]. split; [replace (F + 1232 + 8) with (F + 1240) by lia; exact EC0|]. split.
             - exact ED0.
             - apply (PMARS1.acc_of_shadow_zero M8 (F + 1232) 2 (F + 1232) 16 EZ0); [clear - FM8; lia| lia| lia]. }
    split; [exact GROW0|]. split; [exact AEOK0|]. split; [exact CPL0|]. split; [exact ACCT|]. split; [exact OACCT|]. split; [exact EB0|]. intros _; exact BAL0. }
  { unfold LBX. intros x Hx. apply in_or_app. left. apply in_or_app. left. exact Hx. }
  { exact MINV0. }
  { unfold P0, PQRHA.mparser_init. cbn [PQMA.p_bb PQMA.p_src]. exact I. }
  { exact CRD. }
  intros fx' R' M' model' LK' Aw' s9 st9 sm9 e9 b9 cr' D' RP' PP HP' CK' MRT' INCLK' INCA' AM' ID' HH'.
  change (PMSPA.pm_scr 11) with 34816 in HP'.
  assert (HH'' : ri_inv HI ((PNRNA.mown s9 st9 ++ PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK' cr' Aw' M' (vml_of model')) by (rewrite <- app_assoc; exact HH').
  destruct PP as ((PA' & AE' & IS' & REF' & ACC' & ACCV' & ACCK' & BASE' & ERR' & ECS' & GROW' & AEOK') & SST & EMONO & DEC').
  match type of HP' with L5CA.ahpres _ _ _ _ _ _ ?Wx _ _ => set (Wc := Wx) in * end.
  assert (WcL : forall r, In r Wc -> (F + 96 <= fst r /\ fst r + snd r <= F + 1248) \/ In r (PmSpecs.PMSP.err_W PMA.AD) \/ r = (6896220, 4)).
  { intros r Hr. subst Wc. unfold PmSpecs.PMSP.err_W. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A].
    repeat (apply in_app_or in Hr; destruct Hr as [Hr|Hr]); cbn [In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [cbn [fst snd In]; first [left; lia| right; left; left; reflexivity| right; left; right; left; reflexivity| right; right; reflexivity] |]);
    destruct Hr. }
  assert (WFI : PQHAK2.wfi F Wc).
  { intros r Hr. destruct (WcL r Hr) as [X|[X| ->]]; [left; lia| right; destruct (err_W_hull r X) as [(BW1 & BW2)|(BW1 & BW2)]; rewrite BW1, BW2; lia| right; cbn [fst snd]; lia]. }
  assert (WAF : forall o n, F <= o -> o + n <= F + 2048 -> (forall r, In r Wc -> F + 96 <= fst r -> fst r + snd r <= F + 1248 -> fst r + snd r <= o \/ o + n <= fst r) -> PQHAK2.wapart Wc o n).
  { intros o k H1 H2 H r Hr. destruct (WcL r Hr) as [(Z1 & Z2)|[X| ->]]; [exact (H r Hr Z1 Z2)| left; destruct (err_W_hull r X) as [(BW1 & BW2)|(BW1 & BW2)]; rewrite BW1, BW2; clear - H1 FR; lia| left; cbn [fst snd]; clear - H1 FR; lia]. }
  assert (LS' : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A (PMST.ST (PMST.st_loc g) (PMST.st_sys g) e9) M').
  { apply (PQHAK.ls_ahpres_err L C LY g e9 ar _ FF' (V2 - 160) 34816 Wc M8 M' HP'); [| exact LS| exact ERR'].
    intros a Ha r Hr Hin. unfold L5.in_rng in Hin. unfold PQHAK.bcell, PQHAK.lcell, PQHAK.scell in Ha.
    destruct (WcL r Hr) as [(Z1 & Z2)|[X| ->]]; [clear - Ha Hin Z1 Z2 FR; lia| destruct (err_W_hull r X) as [(BW1 & BW2)|(BW1 & BW2)]; rewrite BW1, BW2 in Hin; clear - Ha Hin; lia| cbn [fst snd] in Hin; clear - Ha Hin; lia]. }
  assert (BI' : Bv W (PNRNA.mown s9 st9 ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ (PM.vs_own s' ++ PM.vs_own s) _ M8 model8 LK8 cr8 A8 M' model' LK' cr' Aw' 34816 Wc BI HP' HH'' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a Hr Ha. unfold L5.in_rng in Ha. unfold tocell. destruct (WcL rr Hr) as [(Z1 & Z2)|[X| ->]].
      + split; [clear - Ha Z1 Z2 FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha Z1 Z2 FR F8 FBIG. lia.
      + destruct (err_W_hull rr X) as [(BW1 & BW2)|(BW1 & BW2)]; rewrite BW1, BW2 in Ha;
          (split; [clear - Ha SLO SPT V2R CLS; lia| unfold HeapIfaceA.SB; change (ff_bytes 5) with 2048; clear - Ha FR F8; lia]).
      + cbn [fst snd] in Ha. split; [clear - Ha SLO SPT V2R CLS; lia| unfold HeapIfaceA.SB; change (ff_bytes 5) with 2048; clear - Ha FR F8; lia].
    - intros a Hc Ho rr Hr Ha. unfold L5.in_rng in Ha. destruct (WcL rr Hr) as [(Z1 & Z2)|[X| ->]].
      + apply (NCF a); [left; clear - Ha Z1 Z2; lia| exact Hc].
      + exact (WERR a Ho rr X Ha).
      + exact (WJNK a Ho _ (or_introl eq_refl) Ha).
    - intros a X. exact X. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R8 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y19 & Y21 & Y27 & Y3 & Y4).
  assert (Y18 : getr R' (reg 18) = Z_to_bv 64 2147450880) by (rewrite (cs_of_preserved R8 R' 18 RP') by inl; exact R18).
  assert (Y20 : getr R' (reg 20) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R8 R' 20 RP') by inl; exact R20).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R8 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R8 R' 23 RP') by inl; exact R23).
  assert (Y24 : getr R' (reg 24) = Z_to_bv 64 (F + 1232)) by (rewrite (cs_of_preserved R8 R' 24 RP') by inl; exact R24).
  assert (Y25 : getr R' (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R8 R' 25 RP') by inl; exact R25).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 (F + 1168)) by (rewrite (cs_of_preserved R8 R' 26 RP') by inl; exact R26).
  assert (FIN8 : In (F, 5, V2 - 160 + 32) (FF' ++ LK8)) by (apply in_or_app; left; left; reflexivity).
  (* [comment removed for export] *)
  assert (AGstk : forall a, V2 - 160 <= a < V2 + cls -> M' (Z_to_bv 64 a) = M8 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP' a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr Hr. unfold L5.in_rng. destruct (WcL rr Hr) as [(Z1 & Z2)|[X| ->]].
      + clear - Ha Z1 Z2 FCEIL SLO CLS. lia.
      + destruct (err_W_hull rr X) as [(BW1 & BW2)|(BW1 & BW2)]; rewrite BW1, BW2; clear - Ha V2R; lia.
      + cbn [fst snd]. clear - Ha V2R. lia. }
  assert (HSTKa' : L5.u64_at RSEGS M' (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M8 M' (V2 - 144) (F + 32)); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb' : L5.u64_at RSEGS M' (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M8 M' (V2 - 136) F); [intros i Hi; apply AGstk; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }
  (* [comment removed for export] *)
  assert (VS' : PM.vstr_at RSEGS PMSPA.accA M' (F + 32) s).
  { eapply PQHAK2.vstr_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact VS0 | exact FHF | exact FIN8 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx)
      | (unfold LBX; intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx)
      | (apply WAF; [lia| lia| intros r Hr Z1 Z2; clear - Z1; lia]) | lia ]. }
  assert (VI' : shadow_zero M' (F + 96) 34)
    by (apply (PQHAK2.shz_callee L ar _ FF' (V2 - 160) 34816 Wc M8 M' (F, 5, V2 - 160 + 32) F (F + 96) 34 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
          [lia| lia| clear - FM8; lia| lia| exact VI0]).
  assert (HB' : PQHAK5.hbaseN F M' s s' sm9) by (split; [exact VS'|]; split; [exact IS'| exact VI']).
  replace (F + 592 + 496) with (F + 1088) in REF' by lia. replace (F + 592 + 400) with (F + 992) in REF', AE' by lia.
  pose proof AE' as (AA' & KC' & EN' & SK').
  assert (HQ' : PQHAK4.hpar4 F M' s9 (NEMA.ae_a st9)) by (split; [exact PA'| split; [exact AA'| split; [exact REF'| exact ACC']]]).
  assert (HSE' : PQHAK5.hseF L ar F M' (NEMA.ae_e st9) (NEMA.ae_s st9)) by (split; [exact SK'| exact EN']).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  LeanFeed.pfeed ident:(P) (PQAHP2.qhaJ_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PQAHP2.aligned; exact V2A) ]).
  destruct P as (fx9 & R9 & M9v & MG9 & hFR & hFZ & (hMS & hKS & hR1 & hR10 & hR24 & hP1 & hP2)).
  set (W9 := fun a => F / 8 + 2147451034 <= a < F / 8 + 2147451034 + 2).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx9 R' 0xaf4f4 R9 0xaff54 M9v W9 K HH'' AM' hMS MG9).
  { intros a Ha Hna. apply hFZ; [exact Ha|]. intros X; apply Hna; subst W9; cbn beta; clear - X; lia. }
  { intros a Ha Wa. subst W9; cbn beta in Wa. split.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR V2R. lia. }
  intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9 VV9. change (mrestrict H' M9 = M9v) in VIS9.
  assert (BI9 : Bv W (PNRNA.mown s9 st9 ++ PM.vs_own s' ++ PM.vs_own s) M9 model9 LK' cr' Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' M9 model9 W9 BI' HH9 AM9 MRT9 MGM9 FR9).
    intros a Wa. subst W9; cbn beta in Wa. change (ff_bytes 5) with 2048. change (2048 / 8) with 256.
    right; right. unfold HeapIfaceA.SB. clear - Wa. lia. }
  assert (RI9 : rinvH R R9 V2 cls F) by (apply (rinvH_ks R R' R9 V2 cls F PQAHP2.KS_qhaJ RI' hKS); vm_compute; reflexivity).
  assert (LS9 : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A (PMST.ST (PMST.st_loc g) (PMST.st_sys g) e9) M9).
  { apply (PQHAK.ls_piece _ M' M9 W9 FR9); [| exact LS']. intros a Wa. subst W9; cbn beta in Wa. clear - Wa FR V2R. lia. }
  assert (PF9 : PQHAK2.pfoot F (V2 - 160) V2 W9) by (intros a Wa; subst W9; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  assert (FIN' : In (F, 5, V2 - 160 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (OAX : forall o n, F <= o -> o + n <= F + 1232 -> PQHAK2.oav W9 o n).
  { intros o k H1 H2 x Hx. subst W9; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR FM8 V2R SLO FCEIL CLS; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  assert (HSE9 : PQHAK5.hseF L ar F M9 (NEMA.ae_e st9) (NEMA.ae_s st9)).
  { pose proof HSE' as (SK9 & EN9). split.
    - apply (PQHAK5.sink_atA_agree L ar M' M9 (NESKA.PMEA L) (F + 432) (NEMA.ae_s st9)); [clear - FR; lia| clear - FR; lia| exact (PQHAK.agA_frame M' M9 W9 (F + 432) 24 FR9 ltac:(clear - FR; lia) ltac:(clear - FR; lia) (OAX (F + 432) 24 ltac:(lia) ltac:(lia)))| | exact SK9].
      intros Hp. pose proof SK9 as (_ & _ & _ & _ & _ & _ & _ & _ & HBk). destruct (HBk Hp) as (_ & _ & _ & BR & _).
      assert (INB : In (NESK.sk_b (NEMA.ae_s st9), NESK.sk_c (NEMA.ae_s st9)) ((PNRNA.mown s9 st9 ++ PM.vs_own s' ++ PM.vs_own s) ++ LB)).
      { apply in_or_app. left. apply in_or_app. left. unfold PNRNA.mown, NEMA.aeown. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
        unfold NESK.sink_own. destruct (Z.eqb_spec (NESK.sk_c (NEMA.ae_s st9)) 0); [exfalso; lia| left; reflexivity]. }
      destruct (PQHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ HH'' INB) as (P0' & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      split; [clear - P0'; lia|]. split; [clear - P47; lia|].
      exact (PQHAK2.blk_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) (V2 - 160) V2 W9 M' M9 HH'' INB FIN' FHF SLOW SHW FR9 PF9).
    - apply (PQHAK5.enc_atA_agree L ar M' M9 (F + 496) (F + 432) (NEMA.ae_e st9)); [clear - FR; lia| clear - FR; lia| exact (PQHAK.agA_frame M' M9 W9 (F + 496) 56 FR9 ltac:(clear - FR; lia) ltac:(clear - FR; lia) (OAX (F + 496) 56 ltac:(lia) ltac:(lia)))| | exact EN9].
      intros Hp. pose proof EN9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBk). destruct (HBk Hp) as (_ & _ & BR & _).
      assert (INB : In (NEM.en_b (NEMA.ae_e st9), NEM.ESZ * NEM.ecap (NEM.en_k (NEMA.ae_e st9))) ((PNRNA.mown s9 st9 ++ PM.vs_own s' ++ PM.vs_own s) ++ LB)).
      { apply in_or_app. left. apply in_or_app. left. unfold PNRNA.mown, NEMA.aeown. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
        unfold NEM.enc_own. destruct (Z.eqb_spec (NEM.en_k (NEMA.ae_e st9)) 0); [exfalso; lia| left; reflexivity]. }
      destruct (PQHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ HH'' INB) as (P0' & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
      split; [clear - P0'; lia|]. split; [clear - P47; lia|].
      exact (PQHAK2.blk_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ F (V2 - 160 + 32) (V2 - 160) V2 W9 M' M9 HH'' INB FIN' FHF SLOW SHW FR9 PF9). }
  apply (KONT fx9 R9 M9 model9 LK' cr' Aw' s9 st9 sm9 e9 b9 BI9 RI9 LS9 EMONO).
  - exact hR1.
  - exact hR10.
  - rewrite (hKS 18%nat) by inl. exact Y18.
  - rewrite (hKS 20%nat) by inl. exact Y20.
  - rewrite (hKS 21%nat) by inl. exact Y21.
  - rewrite (hKS 22%nat) by inl. exact Y22.
  - rewrite (hKS 23%nat) by inl. exact Y23.
  - exact hR24.
  - rewrite (hKS 25%nat) by inl. exact Y25.
  - rewrite (hKS 26%nat) by inl. exact Y26.
  - apply (PQHAK5.hbaseN_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH'' FIN' FHF (V2 - 160) V2 W9 M' M9 SLOW SHW FR9 PF9 s s' sm9);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAX; lia| apply OAX; lia| exact HB'].
  - apply (PQHAK4.hpar4_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) HH'' FIN' FHF (V2 - 160) V2 W9 M' M9 SLOW SHW FR9 PF9 s9 (NEMA.ae_a st9));
      [intros x Hx; apply in_or_app; left; apply in_or_app; left; unfold PNRNA.mown, NEMA.aeown; unfold PQRA.mown in Hx;
       apply in_app_or in Hx; destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx| apply in_or_app; right; apply in_or_app; left; exact Hx]
      | apply OAX; lia| exact HQ'].
  - exact GROW'.
  - exact AEOK'.
  - exact HSE9.
  - exact CK'.
  - apply (L5C.u64_at_agree RSEGS M' M9 (V2 - 144) (F + 32)); [| clear - V2R; lia| clear - V2R; lia| exact HSTKa'].
    intros i Hi. apply FR9; [clear - Hi V2R; lia|]. subst W9; cbn beta. intros X. unfold BIGSHADOW_HI in SHW. clear - Hi X V2R FR SHW. lia.
  - apply (L5C.u64_at_agree RSEGS M' M9 (V2 - 136) F); [| clear - V2R; lia| clear - V2R; lia| exact HSTKb'].
    intros i Hi. apply FR9; [clear - Hi V2R; lia|]. subst W9; cbn beta. intros X. unfold BIGSHADOW_HI in SHW. clear - Hi X V2R FR SHW. lia.
Qed.
End Stage.
End SCFG_1.
End PQHA7.
