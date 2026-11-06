(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9 L5CoreBRB0S9 L5ADetailHRB0S9 L5AFrameKRB0S9 HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmModelFactsA PmStatics PmStaticsA PnStatics PnStaticsA PmSpecs PmSpecsA PeSpecsAb PeStepAB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCStaticsA PeCSink PeCSinkA PeCModel PeCModelA PeCSpecs PeCSpecsA PeCSpecsAb PeBCHarnessStmts PeBCHarnessKit PeBCHarnessKit2 PeBCHarnessSK PeBCHarnessKit3 PeBCHarnessKit4 PeBCHarnessP2 PeCRdReadSpecZ.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Set Keyed Unification.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PEBCH7.
Import L5A. Import L5CA. Import L5SAR. Import PEBCH.

Lemma bytes_ok_pB (payload : list byte) : bytes_ok (PEBCH.p payload).
Proof.
  unfold bytes_ok, PEBCH.p. induction payload as [|b l IH]; cbn; constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. Lia.lia.
Qed.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac hsc := first [ asm | apply UR | apply U_to | rk | gmem | (arith_goal; first [asm | alia]) | assumption ].
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Stage.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (R : bvmap 5 word)
          (V2 cls F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr : credit) (W : list L5.range).
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 160) (V2 - 160) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 5 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487392 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.

Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 5, V2 - 160 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 160 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKB.wapp W.
Hypothesis FAL : F mod 2048 = 0.
Hypothesis WERR : forall a, L5.outside W a -> L5.outside (PMSPA.err_W AD) a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 160 + 32) :: FF).

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PEBHK2.wapart_cons; [cbn [fst snd]; lia| first [apply PEBHK2.wapart_nil | (apply PEBHK2.wapart_cons; [cbn [fst snd]; lia| apply PEBHK2.wapart_nil])]])
  | (apply PEBHK2.wapart_nil) | lia ].

Lemma fb_mod8 fb k : fb mod 2048 = 0 -> (fb + 8 * k) mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite H, Z.add_0_r in Dm.
  replace (fb + 8 * k) with ((fb / 2048 * 256 + k) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Variable P : PESKA.sink_policyA.
Variable payload : list byte.
Local Notation n := (PEBCH.n payload).
Local Notation p := (PEBCH.p payload).
Local Notation parser_at := (PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA).

Lemma stage7 (READ : PECRRZ.reader_read_specZ RSEGS AD AAD EE L ar HI P) (PMODE : PESKA.spa_mode P) (fx8 : FPState) (R8 : bvmap 5 word) (M8 : word -> option byte) (model8 : Model) (K : TSet)
      (LK8 : list fframe) (cr8 : credit) (A8 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (qc b : Z) (g : PMST.st) (cat : Z) :
  Bv W (PM.parser_own (PMSPA.parser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M8 model8 LK8 cr8 A8 -> rinvH R R8 (V2 - 160) F 2147450880 -> K [] ->
  PESTA.ls_okA RSEGS AD AAD EE g M8 ->
  getr R8 (reg 1) = Z_to_bv 64 0xa970c -> getr R8 (reg 10) = Z_to_bv 64 (F + 592) -> getr R8 (reg 11) = Z_to_bv 64 (F + 1120) ->
  getr R8 (reg 18) = Z_to_bv 64 (F + 520) -> getr R8 (reg 20) = Z_to_bv 64 18446744073709551608 ->
  getr R8 (reg 22) = Z_to_bv 64 (F + 432) -> getr R8 (reg 23) = Z_to_bv 64 (F + 496) -> getr R8 (reg 24) = Z_to_bv 64 (F + 1120) -> getr R8 (reg 25) = Z_to_bv 64 (F + 592) ->
  PEBHK2.hbase F M8 s s' sm -> PM.vs_size s' = n -> PM.sm_g sm = PM.vs_data (F + 176) s' -> PM.sm_st sm = 0 -> L5.bytes_at RSEGS M8 (PM.vs_data (F + 176) s') p ->
  PEBCH.hse0 L ar P F M8 -> parser_at M8 (F + 592) (F + 96) (PMSPA.parser_init qc b) -> L5.u64_at RSEGS M8 (F + 976) (F + 496) ->
  PEBHK2.hec F M8 0 cat -> shadow_zero M8 (F + 592) 49 ->
  L5.u64_at RSEGS M8 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M8 (V2 - 136) F ->
  0 <= n < 2 ^ 26 -> (forall nn, PESKA.spa_hb P (s_hi (run nn p UbjRef.init))) ->
  PMSPA.credit_le (PECA.pot_allA L ar P (PMSPA.pst_reset (PMSPA.parser_init qc b)) PEC.enc0 PESK.sink0) cr8 ->
  (forall (fx9 : FPState) (R9 : bvmap 5 word) (M9 : word -> option byte) (model9 : Model) (LK9 : list fframe) (cr9 : credit) (A9 : list (Z * Z))
          (nn : nat) (s1 : PM.pst) (sm1 : PM.strm) (en1 : PEC.enc) (k1 : PESK.sink) (e1 : bool),
      Bv W (PEC.owned s1 en1 k1 ++ PM.vs_own s' ++ PM.vs_own s) M9 model9 LK9 cr9 A9 -> rinvH R R9 (V2 - 160) F 2147450880 ->
      PESTA.ls_okA RSEGS AD AAD EE (PMST.ST (PMST.st_loc g) (PMST.st_sys g) e1) M9 -> (PMST.st_err g = true -> e1 = true) ->
      getr R9 (reg 18) = Z_to_bv 64 (F + 520) -> getr R9 (reg 20) = Z_to_bv 64 18446744073709551608 ->
      getr R9 (reg 22) = Z_to_bv 64 (F + 432) -> getr R9 (reg 23) = Z_to_bv 64 (F + 496) -> getr R9 (reg 24) = Z_to_bv 64 (F + 1120) -> getr R9 (reg 25) = Z_to_bv 64 (F + 592) ->
      PEBHK2.hbase F M9 s s' sm1 -> PEBCH.hparsed L ar P payload F M9 s1 s' sm1 en1 k1 e1 nn ->
      PMSPA.credit_keep cr8 cr9 (PECA.pot_allA L ar P (PMSPA.pst_reset (PMSPA.parser_init qc b)) PEC.enc0 PESK.sink0) (PESKA.spa_pot P (PESK.sk_c k1)) ->
      shadow_zero M9 (F + 592) 49 -> L5.u64_at RSEGS M9 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M9 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx9 R9 0xa970c M9 model9) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx8 R8 0xaa0ac M8 model8) K.
Proof.
  intros BI RI K0 LS R1a R10 R11 R18 R20 R22 R23 R24 R25 HB0 SZ5 SMG SMST PAYB0 HSE0 PA0 VV0 HE0 SZP0 HSTKa HSTKb Hn HPI CRD KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X3 & X4 & X8 & X9 & X19 & X21 & X26 & X27).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PEBHK2.hf F) by (unfold PEBHK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  assert (LENp : Z.of_nat (length p) = n) by (unfold PEBCH.p, PEBCH.n; rewrite length_map; reflexivity).
  assert (BL : blen p = n) by (unfold blen; exact LENp).
  pose proof HB0 as (VS0 & IS0 & VI0). pose proof HE0 as (EV0 & EC0 & EZ0 & ED0). pose proof HSE0 as (SK0 & EN0).
  pose proof LS as (LSB & LSL & LSS & LSE).
  set (P1 := PMSPA.pst_reset (PMSPA.parser_init qc b)) in *.
  set (LBX := (PM.vs_own s' ++ PM.vs_own s) ++ LB).
  assert (OWN1 : PEC.owned P1 PEC.enc0 PESK.sink0 = PM.parser_own (PMSPA.parser_init qc b)).
  { subst P1. unfold PEC.owned, PEC.enc_own, PESK.sink_own, PM.parser_own, PMSPA.pst_reset, PMSPA.parser_init. cbn. rewrite ?app_nil_r. reflexivity. }
  assert (B1' : ri_inv HI (PEC.owned P1 PEC.enc0 PESK.sink0 ++ LBX) FF' LK8 cr8 A8 M8 (vml_of model8)) by (rewrite OWN1; unfold LBX; rewrite app_assoc; exact B1).

  pose proof IS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VSA & _ & _ & _ & EG & GG). replace (F + 96 + 80) with (F + 176) in VSA, EG, GG by (clear; lia).
  assert (UNR : PM.unread (PM.SRC qc qc 0) sm = n) by (unfold PM.unread; cbn [PM.sr_rem]; rewrite EG, SMG, SZ5; clear; lia).
  assert (ECAT : PMSPA.ec_at RSEGS M8 (F + 1120) 0 cat).
  { unfold PMSPA.ec_at. split; [exact EV0|]. split; [replace (F + 1120 + 8) with (F + 1128) by (clear; lia); exact EC0|]. split; [exact ED0|].
    apply (PEBHK2.acc_of_shz M8 (F + 1120) 2 (F + 1120) 16 EZ0); [clear - FM8; lia| clear - FR; lia| clear; lia| clear; lia]. }
  assert (CONT : PEC.content_ok RSEGS AD M8 F p (PM.p_src (PMSPA.parser_init qc b)) s' sm).
  { unfold PEC.content_ok. cbn [PM.p_src PMSPA.parser_init PM.sr_de PM.sr_rem]. unfold PMSPA.o_is. cbn [pa_off_is PeCLayoutB.CADDR_B].
    split; [rewrite BL; exact SZ5|]. split; [replace (F + 96 + 80) with (F + 176) by (clear; lia); exact PAYB0|].
    unfold PEC.pos_of. rewrite UNR, BL. split; [clear; lia|]. replace (n - n) with 0 by (clear; lia).
    split; [| intros E; rewrite SMST in E; discriminate E].
    unfold UbjRef.slice. intros i Hi. exfalso. rewrite length_firstn, Z2Nat.inj_0 in Hi. clear - Hi. Lia.lia. }
  assert (POS0 : PEC.pos_of p (PM.p_src (PMSPA.parser_init qc b)) sm = 0) by (unfold PEC.pos_of; cbn [PM.p_src PMSPA.parser_init]; rewrite UNR, BL; clear; lia).
  unfold PECRRZ.reader_read_specZ in READ.
  apply (READ PMODE fx8 R8 M8 model8 K LBX FF' LK8 A8 cr8 (V2 - 160) 0xa970c F cat p (PMSPA.parser_init qc b) s' sm PEC.enc0 PESK.sink0 (PMST.st_err g) B1' B2 K0).
  { eapply PEBHSK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PEBHSK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PEBHSK.callee_rs; eassumption. }
  { exact (PEBHSK.callee_frame FF V2 F FAL). }
  { pose proof (Z.div_mod V2 32 ltac:(clear; lia)) as DM. rewrite V2A, Z.add_0_r in DM. replace (V2 - 160) with ((V2 / 32 - 5) * 32) by (clear - DM; lia). apply Z.mod_mul. clear; lia. }
  { unfold PMSPA.o_p. cbn [pa_off_p PeCLayoutB.CADDR_B]. rewrite L5K.rl10. exact R10. }
  { unfold PMSPA.o_ec. cbn [pa_off_ec PeCLayoutB.CADDR_B]. rewrite L5K.rl11. exact R11. }
  { unfold PMSPA.o_p, PMSPA.o_is, PMSPA.o_v, PMSPA.o_ec, PESK.o_sink. cbn [pa_off_p pa_off_is pa_off_v pa_off_ec pe_off_sink PeCLayoutB.CADDR_B PeCLayoutB.EADDR_B].
    split; [exact PA0|]. split; [exact IS0|]. split; [exact EN0|].
    split; [replace (F + 592 + 384) with (F + 976) by (clear; lia); exact VV0|].
    split; [exact SK0|]. split; [exact LSB|]. split; [exact LSE|].
    split; [unfold PM.tb_ok; cbn; clear; lia|]. split; [exact CONT|]. split; [exact ECAT|].
    apply (PEBHK2.acc_of_shz M8 (F + 592) 49 (F + 592) 392 SZP0); [clear - FM8; lia| clear - FR; lia| clear; lia| clear; lia]. }
  { cbn. clear; lia. }
  { exact POS0. }
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { unfold LBX. intros x Hx. apply in_or_app. left. apply in_or_app. left. exact Hx. }
  { split; [apply (bytes_ok_pB payload)| rewrite BL; exact (proj2 Hn)]. }
  { exact HPI. }
  { exact CRD. }
  intros fx' R' M' model' LK' Aw' nn s1 sm1 en1 k1 e1 cr' RP' HALT (PA' & IA' & EA' & KA' & BASE' & ERR' & DEF' & SINK') SSTEP EMONO HP' CK' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 11) with 34816 in HP'.
  assert (HH'' : ri_inv HI ((PEC.owned s1 en1 k1 ++ PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK' cr' Aw' M' (vml_of model')) by (rewrite <- app_assoc; exact HH').
  unfold PMSPA.o_p, PMSPA.o_is, PMSPA.o_v, PMSPA.o_ec, PESK.o_sink in PA', IA', EA', KA', DEF'.
  cbn [pa_off_p pa_off_is pa_off_v pa_off_ec pe_off_sink PeCLayoutB.CADDR_B PeCLayoutB.EADDR_B] in PA', IA', EA', KA', DEF'.
  set (Wc := PEC.W_crun AD EE F) in *.
  assert (WcL : forall r, In r Wc -> (F + 96 <= fst r /\ fst r + snd r <= F + 1136) \/ In r (PMSPA.err_W AD)).
  { intros r Hr. subst Wc. unfold PEC.W_crun, PmSpecs.PMSP.W_run, PmSpecs.PMSP.W_srcf, PmSpecs.PMSP.err_W, PmSpecs.PMSP.o_src, PmSpecs.PMSP.o_tb, PmSpecs.PMSP.o_vec, PmSpecs.PMSP.o_p, PmSpecs.PMSP.o_is, PmSpecs.PMSP.o_ec, PmSpecs.PMSP.o_v, PESK.o_sink in Hr.
    cbn [pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit PeCLayoutB.CADDR_B PeCLayoutB.EADDR_B app] in Hr.
    repeat (destruct Hr as [<-|Hr]; [first [left; cbn [fst snd]; clear; lia | (right; unfold PMSPA.err_W; cbn [pa_errcat_guard pa_atexit PeCLayoutB.CADDR_B]; first [left; reflexivity | right; left; reflexivity])]|]). destruct Hr. }
  assert (ERW : forall r, In r (PMSPA.err_W AD) -> (fst r = 6784896 /\ snd r = 2) \/ (fst r = 6922704 /\ snd r = 544)).
  { intros r Hr. unfold PMSPA.err_W in Hr. cbn [pa_errcat_guard pa_atexit PeCLayoutB.CADDR_B] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; [left| right]; split; reflexivity. }
  assert (WFI : PEBHK2.wfi F Wc).
  { intros r Hr. destruct (WcL r Hr) as [X|X]; [left; lia| right; destruct (ERW r X) as [(BW1 & BW2)|(BW1 & BW2)]; rewrite BW1, BW2; lia]. }
  assert (WAF : forall o k, F <= o -> o + k <= F + 2048 -> (forall r, In r Wc -> F + 96 <= fst r -> fst r + snd r <= F + 1136 -> fst r + snd r <= o \/ o + k <= fst r) -> PEBHK2.wapart Wc o k).
  { intros o k H1 H2 H r Hr. destruct (WcL r Hr) as [(Z1 & Z2)|X]; [exact (H r Hr Z1 Z2)| left; destruct (ERW r X) as [(BW1 & BW2)|(BW1 & BW2)]; rewrite BW1, BW2; clear - H1 FR; lia]. }
  assert (LS' : PESTA.ls_okA RSEGS AD AAD EE (PMST.ST (PMST.st_loc g) (PMST.st_sys g) e1) M').
  { apply (PEBHK.ls_ahpres_err L C LY g e1 ar _ FF' (V2 - 160) 34816 Wc M8 M' HP'); [| exact LS| exact ERR'].
    intros a Ha r Hr Hin. unfold L5.in_rng in Hin. unfold PEBHK.bcell, PEBHK.lcell, PEBHK.scell in Ha.
    destruct (WcL r Hr) as [(Z1 & Z2)|X]; [clear - Ha Hin Z1 Z2 FR; lia| destruct (ERW r X) as [(BW1 & BW2)|(BW1 & BW2)]; rewrite BW1, BW2 in Hin; clear - Ha Hin; lia]. }
  assert (BI' : Bv W (PEC.owned s1 en1 k1 ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ (PM.vs_own s' ++ PM.vs_own s) _ M8 model8 LK8 cr8 A8 M' model' LK' cr' Aw' 34816 Wc BI HP' HH'' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a Hr Ha. unfold L5.in_rng in Ha. unfold tocell. destruct (WcL rr Hr) as [(Z1 & Z2)|X].
      + split; [clear - Ha Z1 Z2 FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha Z1 Z2 FR F8 FBIG. lia.
      + destruct (ERW rr X) as [(BW1 & BW2)|(BW1 & BW2)]; rewrite BW1, BW2 in Ha;
          (split; [clear - Ha SLO SPT V2R CLS; lia| unfold HeapIfaceA.SB; change (ff_bytes 5) with 2048; clear - Ha FR F8; lia]).
    - intros a Hc Ho rr Hr Ha. unfold L5.in_rng in Ha. destruct (WcL rr Hr) as [(Z1 & Z2)|X].
      + apply (NCF a); [left; clear - Ha Z1 Z2; lia| exact Hc].
      + exact (WERR a Ho rr X Ha).
    - intros a X. exact X. }
  assert (RI' : rinvH R R' (V2 - 160) F 2147450880) by exact (rinvH_pres R R8 R' (V2 - 160) F 2147450880 RI RP').
  assert (Y18 : getr R' (reg 18) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R8 R' 18 RP') by inl; exact R18).
  assert (Y20 : getr R' (reg 20) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R8 R' 20 RP') by inl; exact R20).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R8 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 496)) by (rewrite (cs_of_preserved R8 R' 23 RP') by inl; exact R23).
  assert (Y24 : getr R' (reg 24) = Z_to_bv 64 (F + 1120)) by (rewrite (cs_of_preserved R8 R' 24 RP') by inl; exact R24).
  assert (Y25 : getr R' (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R8 R' 25 RP') by inl; exact R25).
  assert (FIN8 : In (F, 5, V2 - 160 + 32) (FF' ++ LK8)) by (apply in_or_app; left; left; reflexivity).

  assert (VS' : PM.vstr_at RSEGS PMSPA.accA M' (F + 32) s).
  { eapply PEBHK2.vstr_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact VS0 | exact FHF | exact FIN8 | exact WFI | (left; reflexivity)
      | (split; reflexivity) | (intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx)
      | (unfold LBX; intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx)
      | (apply WAF; [lia| lia| intros r Hr Z1 Z2; clear - Z1; lia]) | lia ]. }
  assert (VI' : shadow_zero M' (F + 96) 34)
    by (apply (PEBHK2.shz_callee L ar _ FF' (V2 - 160) 34816 Wc M8 M' (F, 5, V2 - 160 + 32) F (F + 96) 34 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
          [lia| lia| clear - FM8; lia| lia| exact VI0]).
  assert (AGstk' : forall a, V2 - 160 <= a < V2 + cls -> M' (Z_to_bv 64 a) = M8 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP' a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr Hr. unfold L5.in_rng. destruct (WcL rr Hr) as [(Z1 & Z2)|X]; [clear - Ha Z1 Z2 FCEIL SLO CLS; lia|].
      destruct (ERW rr X) as [(BW1 & BW2)|(BW1 & BW2)]; rewrite BW1, BW2; clear - Ha V2R; lia. }
  assert (HSTKa' : L5.u64_at RSEGS M' (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M8 M' (V2 - 144) (F + 32)); [intros i Hi; apply AGstk'; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]. }
  assert (HSTKb' : L5.u64_at RSEGS M' (V2 - 136) F).
  { apply (L5C.u64_at_agree RSEGS M8 M' (V2 - 136) F); [intros i Hi; apply AGstk'; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]. }
  apply (KONT fx' R' M' model' LK' cr' Aw' nn s1 sm1 en1 k1 e1 BI' RI' LS' EMONO Y18 Y20 Y22 Y23 Y24 Y25).
  - split; [exact VS'| split; [exact IA'| exact VI']].
  - split; [exact PA'|]. split; [exact IA'|]. split; [exact EA'|]. split; [exact KA'|]. split; [exact BASE'|]. split; [exact ERR'|]. split; [exact DEF'|]. split; [exact HALT| exact SINK'].
  - exact CK'.
  - apply (PEBHK2.shz_callee L ar _ FF' (V2 - 160) 34816 Wc M8 M' (F, 5, V2 - 160 + 32) F (F + 592) 49 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
      [lia| lia| exact (fb_mod8 F 74 FAL)| lia| exact SZP0].
  - exact HSTKa'.
  - exact HSTKb'.
Qed.
End Stage.
End SCFG_1.
End PEBCH7.
