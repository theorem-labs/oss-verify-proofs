(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5CoreSpecsAS8 L5StepARS8 L5CoreBRS8 L5ADetailHRS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PnStatics PmCertKitG PmModelFactsA PmStep PeStepA PmParStep PmParKit PeASrcKit PeAParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrameA PeCRdValD PeCRdValW PeCValSpecA PmSpecsAX PeACReset1 PeASrcRead1 PmAUarK PmAUarKS PmAUar PeARel3 PeARvP1 PeARvP2 PeARvP3 PeARvP4 PeARvP5 PeARvP6.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b4180_b4184 Ea0_code_b4300_b4308 Ea0_code_b455c_b4560.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEACRV.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.

Ltac sya := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.

Definition own (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
  /\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))) /\ L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R (reg 26)))
  /\ L5.u64_at RSEGS M (E - 104) (bv_unsigned (getr R (reg 27))).
Definition ocell (E : Z) (a : Z) : Prop := E - 104 <= a < E.
Lemma own_agree E R M1 M1' : 0 <= E - 104 -> E <= 2 ^ 64 ->
  own E R M1 -> (forall a, ocell E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own E R M1'.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) AG. unfold own, ocell in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

Lemma credit_le_keep p1 c1 c2 p2 : PMSP.credit_le p1 c1 -> PMSP.credit_keep c1 c2 p1 p2 -> PMSP.credit_le p2 c2.
Proof. unfold PMSP.credit_le, PMSP.credit_keep. lia. Qed.
Lemma credit_keep_trans c1 c2 c3 p1 p2 p3 : PMSP.credit_keep c1 c2 p1 p2 -> PMSP.credit_keep c2 c3 p2 p3 -> PMSP.credit_keep c1 c3 p1 p3.
Proof. unfold PMSP.credit_keep. lia. Qed.

Lemma div8_off F a k : F / 8 * 8 = F -> F + 8 * k <= a < F + 8 * k + 8 -> a / 8 = F / 8 + k.
Proof. intros E H. symmetry. apply (Z.div_unique a 8 (F / 8 + k) (a - F - 8 * k)); lia. Qed.

Lemma frame_ok5_push FF fb f : PECA.frame_ok5 FF fb -> PECA.frame_ok5 (f :: FF) fb.
Proof. intros ((r0 & Hf) & Hm). split; [exists r0; right; exact Hf| exact Hm]. Qed.

Tactic Notation "wr_mem" integer(n) := unfold PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W; cbn [app]; do n right; left; reflexivity.
Ltac wr_rng := unfold L5.in_rng, PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_v, PESK.o_sink;
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
  (forall q m, In (q, m) LB -> PMKA.blk_out W q m) ->
  PM.iss_at RSEGS AD PMSPA.accA M (PMSPA.o_is AD fb) str sm -> PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op (PMSPA.o_is AD fb) s ->
  PEC.content_ok RSEGS AD M fb p (PM.p_src s) str sm -> PEC.content_ok RSEGS AD M' fb p (PM.p_src s) str sm.
Proof.
  intros EK WAPP FRB BRB AO OW INCS QIN OB IA PA.
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). pose proof VS as (_ & _ & VSF).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
  apply (PECFA.content_keepA RSEGS AD L ar LB FF sp scr W M M' EK WAPP FRB BRB fb p s str sm AO OW INCS).
  - intros c n q ->. cbn in VSF. destruct VSF as (_ & _ & _ & Hn & Hc & _ & _ & _). split; [lia|]. apply OB. apply INCS. cbn. left. reflexivity.
  - intros n ->. cbn in VSF. lia.
  - exact QIN.
  - apply OB. exact QIN.
  - exact G1.
  - exact G2.
  - exact G3.
Qed.

Hypothesis SRD : PECSA.src_read_spec L ar HI.
Hypothesis GL : PECSA.get_length_spec L ar HI P.
Hypothesis RS : PECSA.read_span_spec L ar HI.
Hypothesis VAL : PECVSA.validate_fun_spec RSEGS AD L ar HI (pa_validate AD).
Hypothesis B10 : PMSPA.is_base10_spec RSEGS AD L ar HI.
Hypothesis MKE : PECSA.make_ec_spec L ar HI.
Hypothesis BA : PECSA.begin_array_spec L ar HI P.
Hypothesis BO : PECSA.begin_object_spec L ar HI P.
Hypothesis VN : PECSA.v_null_spec L ar HI P.
Hypothesis VB : PECSA.v_bool_spec L ar HI P.
Hypothesis VU : PECSA.v_uint64_spec L ar HI P.
Hypothesis VI : PECSA.v_int64_spec L ar HI P.
Hypothesis VD : PECSA.v_double_spec L ar HI P.
Hypothesis VS : PECSA.v_string_spec L ar HI P.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (t : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
          (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 8.
Hypothesis FRM : PMSPA.ffroomA 8 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_p AD fb).
Hypothesis A11 : getr R 11%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis A13 : getr R 13%bv = Z_to_bv 64 (PMSPA.o_ec AD fb).
Hypothesis Ht : 0 <= t < 256.
Hypothesis A12 : getr R 12%bv = Z_to_bv 64 t.
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_rv t p X.
Hypothesis NB : s_bad (r_value p t X) = false.
Hypothesis HB : PESKA.spa_hb P (s_hi (r_value p t X)).
Hypothesis CRED : PMSP.credit_le (PECA.pot_allA L ar P s en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (r_value p t X) s' str sm' en' k' e' cat ->
        PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 8) (PEC.W_crun AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_allA L ar P s en k) (PECA.pot_allA L ar P s' en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s' en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.
Let op := PMSPA.o_p AD fb. Let ov := PMSPA.o_v AD fb. Let oec := PMSPA.o_ec AD fb. Let ois := PMSPA.o_is AD fb. Let osk := PESK.o_sink EE fb. Let otb := PMSPA.o_tb AD fb.
Let WR := PEC.W_crun AD EE fb.

Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 8) with 28672 in ASTK, STKSH; change (28672 / 8) with 3584 in STKSH;
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
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model op 384 sp 28672 HH (PMKA.aobj_of_aobjA FF op 384 (AOF op 384 ltac:(lia) ltac:(lia)) O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & _);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ois 272 sp 28672 HH (PMKA.aobj_of_aobjA FF ois 272 (AOF ois 272 ltac:(lia) ltac:(lia)) I8) ltac:(lia) ltac:(reflexivity))
    as ((I1 & I2 & I3 & I4 & I5) & IBIG & _);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model oec 16 sp 28672 HH (PMKA.aobj_of_aobjA FF oec 16 (AOF oec 16 ltac:(lia) ltac:(lia)) C8m) ltac:(lia) ltac:(reflexivity))
    as ((E1' & E2' & E3' & E4' & E5') & EBIG & _);
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH);
  assert (AOP : PMSPA.aobjA FF op 384) by (apply AOF; lia);
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply AOF; lia).

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k).
Hypothesis APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n ->
  (a + n <= F \/ F + ff_bytes 3 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + ff_bytes 3 / 8 <= a) /\ (a + n <= fl \/ fl + 1 <= a).
Let FF' := (F, 3, sp - 128 + 32) :: FF.

Ltac frame_facts :=
  pose proof G as G'; destruct G' as [_ GSPT GSLO GSHI _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS];
  change (ff_bytes 3) with 512 in GFS2, GFCEIL, GFLC, GFR, GF8, GFBIG, GFLA, GNCF; unfold FS_BYTES in GFS2, GFLP.

Definition WretF (Wx : Z -> Prop) (a : Z) : Prop := ((F <= a < F + ff_bytes 3 \/ F / 8 + SB <= a < F / 8 + SB + ff_bytes 3 / 8) \/ a = fl) \/ Wx a.
Lemma wretF_ek LB6 LK6 cr6 A6 (Mx Mf : word -> option byte) V6 (W : list L5.range) (Wx : Z -> Prop) :
  ri_inv HI LB6 ((F, 3, sp - 128 + 32) :: FF) LK6 cr6 A6 Mx V6 ->
  (forall a, Wx a -> ~ L5.outside W a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ WretF Wx a -> Mf (Z_to_bv 64 a) = Mx (Z_to_bv 64 a)) ->
  L5SAR.ek L ar LB6 FF 0 0 W Mx Mf.
Proof.
  intros HH6 WXin FZ. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB & WF & FSAPP & FSCEIL & _).
  unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL.
  assert (FB8 : (F + ff_bytes 3 - 1) / 8 = F / 8 + ff_bytes 3 / 8 - 1 /\ ff_bytes 3 / 8 * 8 = ff_bytes 3) by (split; [exact (proj1 (proj2 F8)) | exact (proj2 (proj2 F8))]).
  apply (L5SAR.ek_piece L ar LB6 FF 0 0 W Mx Mf (WretF Wx) FZ).
  intros a Ha Hc Ho [Wa|Wa]; [| exact (WXin a Wa Ho)].

  assert (IND : forall BS ST, aclient_g BS ST L ar LB6 FF 0 0 a -> in_block LB6 a \/ (hl_img_lo L <= a < hl_img_hi L) \/ (exists b, In b LB6 /\ BS (fst b) (snd b) a)
                  \/ aclient L ar LBX FF sp 28672 a).
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
    + destruct (FA (F, 3, sp - 128 + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z; clear - Y Z Xb FR; lia.
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
    + destruct (FA (F, 3, sp - 128 + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z.
      * assert (E1 : (F - 1) / 8 = F / 8 - 1).
        { rewrite <- (proj1 F8) at 1. replace (F / 8 * 8 - 1) with (7 + (F / 8 - 1) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        pose proof (Z.div_le_mono (fst b + snd b - 1) (F - 1) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
        clear - Y Xb D. unfold SB in *. lia.
      * assert (E1 : (F + ff_bytes 3) / 8 = F / 8 + ff_bytes 3 / 8).
        { rewrite <- (proj1 F8) at 1. rewrite <- (proj2 FB8) at 1. replace (F / 8 * 8 + ff_bytes 3 / 8 * 8) with ((F / 8 + ff_bytes 3 / 8) * 8) by lia.
          rewrite Z.div_mul by lia. reflexivity. }
        pose proof (Z.div_le_mono (F + ff_bytes 3) (fst b) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
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
  (getr Ri (reg 2) = Z_to_bv 64 (sp - 128) /\ getr Ri (reg 8) = Z_to_bv 64 sp /\ getr Ri (reg 9) = Z_to_bv 64 (sp - 128) /\ getr Ri (reg 18) = Z_to_bv 64 (F / 8 + 2147450880)
   /\ getr Ri (reg 19) = Z_to_bv 64 F /\ getr Ri (reg 20) = Z_to_bv 64 op /\ getr Ri (reg 21) = Z_to_bv 64 oec /\ getr Ri (reg 22) = Z_to_bv 64 ov
   /\ getr Ri (reg 26) = Z_to_bv 64 2147450880 /\ getr Ri (reg 27) = Z_to_bv 64 F /\ (forall j, In j [3; 4]%nat -> getr Ri (reg j) = getr R (reg j)))
  /\ PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned si eni ki) Mi mdi LKi cri Awi
  /\ PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat
  /\ PMSPA.src_step (PM.p_src s) (PM.p_src si) sm smi /\ (e = true -> ei = true)
  /\ PMSP.credit_keep cr cri (PECA.pot_allA L ar P s en k) (PECA.pot_allA L ar P si eni ki).

Lemma cpre_keepA LB sp0 scr0 W Mi Mj Xi si smi eni ki ei :
  L5SAR.ek L ar LB FF sp0 scr0 W Mi Mj -> PMKA.wapp W ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  incl (PEC.owned si eni ki) LB -> incl (PM.vs_own str) LB ->
  (forall i, fb + 32 <= i < fb + 2040 -> L5.outside W i) -> (forall a, a < 6914048 -> L5.outside W a) ->
  (forall q m, In (q, m) LB -> PMKA.blk_out W q m) ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PECA.crun_preA RSEGS AD AAD EE L ar P Mj fb p Xi si str smi eni ki ei cat.
Proof.
  intros EK WAPP BRB OINC SINC OW OI OB CP. entry_facts.
  destruct CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (PINC : incl (PM.parser_own si) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; left; exact Hx).
  assert (EINC : incl (PEC.enc_own eni) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own ki) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; right; exact Hx).
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
  { apply (content_keepA' LB FF sp0 scr0 W Mi Mj fb p si str smi op EK WAPP FRB BRB AOI); [fold ois; apply OWo; clear - Eois; lia| exact SINC| | intros q m Hq; exact (OB q m Hq)| exact IA| exact PA| exact CONT].
    apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity. }
  split; [exact CL|].
  split; [apply (PECFA.ec_state_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB fb (s_ec Xi) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [fold oec; apply OWo; clear - Eoec; lia| exact ECS]|].
  split; [exact ECI|].
  exact (PMKA.acc_keepA' L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC).
Qed.

Lemma cpre_stepA LB sp0 scr0 W Mi Mj Xi si smi eni ki ei Xj sj ej :
  L5SAR.ek L ar LB FF sp0 scr0 W Mi Mj -> PMKA.wapp W ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  incl (PEC.owned si eni ki) LB -> incl (PM.vs_own str) LB ->
  (forall i, fb + 32 <= i < fb + 2040 -> ~ (op <= i < op + 384) -> ~ (oec <= i < oec + 16) -> L5.outside W i) ->
  (forall q m, In (q, m) LB -> PMKA.blk_out W q m) ->
  PM.p_src sj = PM.p_src si -> PM.p_tb sj = PM.p_tb si -> PM.p_tg sj = PM.p_tg si ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mj op ois sj -> PMSTA.base_okA RSEGS AD Mj -> PESTA.err_okA RSEGS AD AAD EE Mj ej ->
  PEC.clink p Xj sj smi eni ki -> PECA.ec_stateA RSEGS AD Mj fb (s_ec Xj) cat -> (s_ec Xj = true -> ej = true) ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PECA.crun_preA RSEGS AD AAD EE L ar P Mj fb p Xj sj str smi eni ki ej cat.
Proof.
  intros EK WAPP BRB OINC SINC OW OB ESRC ETB ETG PA' BASE' ERR' CL' ECS' ECI' CP. entry_facts.
  destruct CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (PINC : incl (PM.parser_own si) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; left; exact Hx).
  assert (EINC : incl (PEC.enc_own eni) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own ki) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; right; exact Hx).
  assert (OWo : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op \/ op + 384 <= a) -> (a + n <= oec \/ oec + 16 <= a) -> forall i, a <= i < a + n -> L5.outside W i)
    by (intros a n X1 X2 X3 X4 i Hi; apply OW; clear - X1 X2 X3 X4 Hi; lia).
  split; [exact PA'|].
  split.
  { apply (PMKA.iss_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ois str smi AOI); [exact SINC| apply OWo; clear - Eois Eop Eoec; lia| | exact IA].
    intros c0 n0 p0 E0. apply OB. apply SINC. unfold PM.vs_own. rewrite E0. left. reflexivity. }
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eov Eop Eoec; lia| exact EINC| | exact EA].
    intros Hp. apply OB. apply EINC. unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [apply (PMKA.u64_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eop Eoec; lia| exact VREF]|].
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eosk Eop Eoec; lia| exact KINC| | exact SKA].
    intros Hp. apply OB. apply KINC. unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [exact BASE'|].
  split; [exact ERR'|].
  split; [rewrite ETB, ETG; exact TBOK|].
  split.
  { rewrite ESRC. apply (content_keepA' LB FF sp0 scr0 W Mi Mj fb p si str smi op EK WAPP FRB BRB AOI); [fold ois; apply OWo; clear - Eois Eop Eoec; lia| exact SINC| | intros q m Hq; exact (OB q m Hq)| exact IA| exact PA| exact CONT].
    apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity. }
  split; [exact CL'|]. split; [exact ECS'|]. split; [exact ECI'|].
  exact (PMKA.acc_keepA' L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC).
Qed.

Ltac open_amid MID :=
  pose proof MID as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27 & J34) & BI & CP & ST & EIMP & CK);
  pose proof BI as (HHi & AMi & MRTi & INCAi & INCLi & ASTKi & EKbi & DKbi & OWNi & FSHDi);
  pose proof AMi as (Mhi & MIi).

Ltac vis_amid BI Hh Mv :=
  let X := fresh "VF" in
  pose proof (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
                WR _ _ _ _ _ _ BI) as X;
  destruct X as ((WSi & ICi & CSBi & CUARi & _) & OWNv & (FDi & FWi & FSWi & FLCi & FLWi) & (FLCci & FLVi & VFi & VSi & VSHi));
  change (ff_bytes 3) with 512 in WSi, FDi, FWi, FSWi, FLCi, VFi, VSHi; change (512 / 8) with 64 in FSWi, VSHi;
  replace (sp - (sp - 128)) with 128 in WSi by (clear; lia); replace (F + 512 - 8) with (F + 504) in FLCi by (clear; lia);
  fold Hh in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi, FLVi, VFi, VSi, VSHi; fold Mv in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi.

Lemma amid_regs fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fx' : FPState) R' md' :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%nat -> getr R' (reg j) = getr Ri (reg j)) ->
  ri_inv HI (PEC.owned si eni ki ++ LBX) FF' LKi cri Awi Mi (vml_of md') -> L5CA.amodel_ok Awi md' -> model_rt mdi md' ->
  amid fx' R' Mi md' LKi Awi cri si smi eni ki ei Y.
Proof.
  intros MID RR HH' AM' MRT'. open_amid MID.
  split; [|split; [exact (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned si eni ki) Mi mdi LKi cri Awi md' BI HH' AM' MRT')| split; [exact CP| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  split; [rewrite (RR 2%nat) by inl; exact J2|]. split; [rewrite (RR 8%nat) by inl; exact J8|]. split; [rewrite (RR 9%nat) by inl; exact J9|].
  split; [rewrite (RR 18%nat) by inl; exact J18|]. split; [rewrite (RR 19%nat) by inl; exact J19|]. split; [rewrite (RR 20%nat) by inl; exact J20|].
  split; [rewrite (RR 21%nat) by inl; exact J21|]. split; [rewrite (RR 22%nat) by inl; exact J22|]. split; [rewrite (RR 26%nat) by inl; exact J26|].
  split; [rewrite (RR 27%nat) by inl; exact J27|].
  intros j Hj. rewrite (RR j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
Qed.

Lemma amid_pieceF fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fxj : FPState) Rj (pci pcj : Z) Mjv (Wp : Z -> Prop) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fxj Rj (Z_to_bv 64 pcj) Mjv (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) Mjv ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mjv (Z_to_bv 64 a) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 a)) ->
  (forall a, Wp a -> F / 8 + SB <= a < F / 8 + SB + 64) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%nat -> getr Rj (reg j) = getr Ri (reg j)) ->
  (forall Mj mdj, mrestrict (ahid Awi mdi) Mj = Mjv -> ahid Awi mdj = ahid Awi mdi -> mem_grows Mi Mj ->
      amid fxj Rj Mj mdj LKi Awi cri si smi eni ki ei Y -> srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxj) RSEGS Rj pcj Mj mdj) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID MS MG FZ WPF RR KONT'. entry_facts. frame_facts. open_amid MID.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LBi FF' LKi cri Awi Mi mdi fxi fxj Ri pci Rj pcj Mjv Wp K HHi AMi MS MG FZ).
  { intros a Ha Wa. pose proof (WPF a Wa) as X'. split.
    - apply (L5SAR.fframe_shadow_client L ar LBi FF' 0 0 F 3 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. unfold SB in X'. clear - X'; lia.
    - unfold SB in X'. pose proof GFR as (GF1 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). clear - X' D1; lia. }
  intros Mj mdj HHj AMj MRTj HIDj VISj MGMj FRj VVj.
  assert (EKj : L5SAR.ek L ar LBi FF 0 0 [] Mi Mj).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k)
             LBi LKi cri Awi Mi Mj _ [] (fun _ => False) G HHi); [intros a []|].
    intros a Ha Nw. apply FRj; [exact Ha|]. intros Wa. apply Nw. unfold PMAUK.WretX, PMAUK.Wret. left. left. right. change (ff_bytes 3 / 8) with 64. exact (WPF a Wa). }
  apply (KONT' Mj mdj VISj HIDj MGMj).
  split; [| split; [| split; [| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  - split; [rewrite (RR 2%nat) by inl; exact J2|]. split; [rewrite (RR 8%nat) by inl; exact J8|]. split; [rewrite (RR 9%nat) by inl; exact J9|].
    split; [rewrite (RR 18%nat) by inl; exact J18|]. split; [rewrite (RR 19%nat) by inl; exact J19|]. split; [rewrite (RR 20%nat) by inl; exact J20|].
    split; [rewrite (RR 21%nat) by inl; exact J21|]. split; [rewrite (RR 22%nat) by inl; exact J22|]. split; [rewrite (RR 26%nat) by inl; exact J26|].
    split; [rewrite (RR 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (RR j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR (PEC.owned si eni ki) Mi mdi LKi cri Awi Mj mdj Wp BI HHj AMj MRTj MGMj FRj).
    intros a Wa. right. right. change (ff_bytes 3 / 8) with 64. exact (WPF a Wa).
  - apply (cpre_keepA LBi 0 0 [] Mi Mj Y si smi eni ki ei EKj PMKA.wapp_nil BRBi); [unfold LBi; apply incl_appl; apply incl_refl| unfold LBi; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP].
Qed.

Lemma amid_pieceFW fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fxj : FPState) Rj (pci pcj : Z) Mjv (Wp : Z -> Prop) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fxj Rj (Z_to_bv 64 pcj) Mjv (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) Mjv ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mjv (Z_to_bv 64 a) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 a)) ->
  (forall a, Wp a -> F + 32 <= a < F + 504 \/ F / 8 + SB <= a < F / 8 + SB + 64) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%nat -> getr Rj (reg j) = getr Ri (reg j)) ->
  (forall Mj mdj, mrestrict (ahid Awi mdi) Mj = Mjv -> ahid Awi mdj = ahid Awi mdi -> mem_grows Mi Mj ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mj (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      amid fxj Rj Mj mdj LKi Awi cri si smi eni ki ei Y -> srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxj) RSEGS Rj pcj Mj mdj) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID MS MG FZ WPF RR KONT'. entry_facts. frame_facts. open_amid MID.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LBi FF' LKi cri Awi Mi mdi fxi fxj Ri pci Rj pcj Mjv Wp K HHi AMi MS MG FZ).
  { intros a Ha Wa. pose proof GFR as (GF1 & GF2 & GF3 & _). destruct (WPF a Wa) as [X'|X']; split.
    - apply (L5SAR.fframe_client L ar LBi FF' 0 0 F 3 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512. clear - X'; lia.
    - clear - X' GF3; lia.
    - apply (L5SAR.fframe_shadow_client L ar LBi FF' 0 0 F 3 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. unfold SB in X'. clear - X'; lia.
    - unfold SB in X'. assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). clear - X' D1; lia. }
  intros Mj mdj HHj AMj MRTj HIDj VISj MGMj FRj VVj.
  assert (EKj : L5SAR.ek L ar LBi FF 0 0 [] Mi Mj).
  { apply (wretF_ek LBi LKi cri Awi Mi Mj _ [] (fun _ => False) HHi); [intros a []|].
    intros a Ha Nw. apply FRj; [exact Ha|]. intros Wa. apply Nw. unfold WretF. left. left. change (ff_bytes 3 / 8) with 64. change (ff_bytes 3) with 512.
    destruct (WPF a Wa) as [X'|X']; [left; clear - X'; lia| right; exact X']. }
  apply (KONT' Mj mdj VISj HIDj MGMj FRj).
  split; [| split; [| split; [| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  - split; [rewrite (RR 2%nat) by inl; exact J2|]. split; [rewrite (RR 8%nat) by inl; exact J8|]. split; [rewrite (RR 9%nat) by inl; exact J9|].
    split; [rewrite (RR 18%nat) by inl; exact J18|]. split; [rewrite (RR 19%nat) by inl; exact J19|]. split; [rewrite (RR 20%nat) by inl; exact J20|].
    split; [rewrite (RR 21%nat) by inl; exact J21|]. split; [rewrite (RR 22%nat) by inl; exact J22|]. split; [rewrite (RR 26%nat) by inl; exact J26|].
    split; [rewrite (RR 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (RR j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR (PEC.owned si eni ki) Mi mdi LKi cri Awi Mj mdj Wp BI HHj AMj MRTj MGMj FRj).
    intros a Wa. change (ff_bytes 3 / 8) with 64. change (ff_bytes 3) with 512. destruct (WPF a Wa) as [X'|X']; [right; left; clear - X'; lia| right; right; exact X'].
  - apply (cpre_keepA LBi 0 0 [] Mi Mj Y si smi eni ki ei EKj PMKA.wapp_nil BRBi); [unfold LBi; apply incl_appl; apply incl_refl| unfold LBi; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP].
Qed.

Lemma amid_pieceS fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fxj : FPState) Rj (pci pcj : Z) Mjv (Wp : Z -> Prop) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fxj Rj (Z_to_bv 64 pcj) Mjv (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) Mjv ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mjv (Z_to_bv 64 a) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 a)) ->
  (forall a, Wp a -> sp - 128 <= a < sp - 104) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%nat -> getr Rj (reg j) = getr Ri (reg j)) ->
  (forall Mj mdj, mrestrict (ahid Awi mdi) Mj = Mjv -> ahid Awi mdj = ahid Awi mdi -> mem_grows Mi Mj ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mj (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      amid fxj Rj Mj mdj LKi Awi cri si smi eni ki ei Y -> srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxj) RSEGS Rj pcj Mj mdj) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID MS MG FZ WPF RR KONT'. entry_facts. frame_facts. open_amid MID.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LBi FF' LKi cri Awi Mi mdi fxi fxj Ri pci Rj pcj Mjv Wp K HHi AMi MS MG FZ).
  { intros a Ha Wa. pose proof (WPF a Wa) as X'. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT GSLO GSHI GSPT; lia| intros Y'; clear - Y'; lia].
    - clear - X' SLO SPT GSLO GSPT; lia. }
  intros Mj mdj HHj AMj MRTj HIDj VISj MGMj FRj VVj.
  assert (EKj : L5SAR.ek L ar LBi FF sp 28672 [] Mi Mj).
  { intros a (Ha & Hc & _). apply FRj; [exact Ha|]. intros Wa. pose proof (WPF a Wa) as X'.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LBi FF' LKi cri Awi Mi _ sp 28672 a HHi GSPT (L5SAR.aclient_cons L ar LBi FF (F, 3, sp - 128 + 32) sp 28672 a Hc)) as [Y'|Y'];
      clear - X' Y' GSLO; lia. }
  apply (KONT' Mj mdj VISj HIDj MGMj FRj).
  split; [| split; [| split; [| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  - split; [rewrite (RR 2%nat) by inl; exact J2|]. split; [rewrite (RR 8%nat) by inl; exact J8|]. split; [rewrite (RR 9%nat) by inl; exact J9|].
    split; [rewrite (RR 18%nat) by inl; exact J18|]. split; [rewrite (RR 19%nat) by inl; exact J19|]. split; [rewrite (RR 20%nat) by inl; exact J20|].
    split; [rewrite (RR 21%nat) by inl; exact J21|]. split; [rewrite (RR 22%nat) by inl; exact J22|]. split; [rewrite (RR 26%nat) by inl; exact J26|].
    split; [rewrite (RR 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (RR j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR (PEC.owned si eni ki) Mi mdi LKi cri Awi Mj mdj Wp BI HHj AMj MRTj MGMj FRj).
    intros a Wa. pose proof (WPF a Wa) as X'. left. unfold ocell. clear - X'; lia.
  - apply (cpre_keepA LBi sp 28672 [] Mi Mj Y si smi eni ki ei EKj PMKA.wapp_nil BRBi); [unfold LBi; apply incl_appl; apply incl_refl| unfold LBi; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP].
Qed.

Definition PF (MVi : word -> option byte) : Prop :=
  0 <= sp < 2 ^ 64
  /\ 0 <= op < 2 ^ 64
  /\ 0 <= ov < 2 ^ 64
  /\ 0 <= oec < 2 ^ 64
  /\ L5.img_clear MVi 65536 1286144
  /\ L5.u64_at RSEGS MVi 1317368 2147450880
  /\ L5.u32_at RSEGS MVi 1317376 1
  /\ 140735332487296 <= sp <= 140737488355328
  /\ sp mod 32 = 0
  /\ L5.writable RSEGS MVi (sp - 128) 128
  /\ 6914048 <= op <= 140737488354944
  /\ op mod 8 = 0
  /\ (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784)
  /\ L5KA.zeros_at MVi ((op / 8) + 2147450880) 3
  /\ L5KA.zeros_at MVi (((op + 32) / 8) + 2147450880) 44
  /\ L5KA.zeros_at MVi (((op + 20) / 8) + 2147450880) 1
  /\ L5.writable RSEGS MVi op 384
  /\ ((sp - 128) + 128 <= op \/ op + 384 <= (sp - 128))
  /\ 6914048 <= oec <= 140737488355312
  /\ oec mod 8 = 0
  /\ (2147446784 + 17592186048512 <= oec \/ oec + 16 <= 2147446784)
  /\ L5KA.zeros_at MVi ((oec / 8) + 2147450880) 2
  /\ L5.writable RSEGS MVi oec 16
  /\ ((sp - 128) + 128 <= oec \/ oec + 16 <= (sp - 128))
  /\ (op + 384 <= oec \/ oec + 16 <= op)
  /\ 0 <= F < 2 ^ 64
  /\ 0 <= fl < 2 ^ 64
  /\ 6914048 <= F <= 140737488354816
  /\ F mod 32 = 0
  /\ L5.defined MVi F 512
  /\ L5.writable RSEGS MVi F 512
  /\ (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784)
  /\ L5.writable RSEGS MVi ((F / 8) + 2147450880) 64
  /\ L5.u64_at RSEGS MVi (F + 504) fl
  /\ 4096 <= fl <= 140737488355327
  /\ L5.writable RSEGS MVi fl 1
  /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784)
  /\ (F + 512 <= fl \/ fl + 1 <= F)
  /\ ((sp - 128) + 128 <= F \/ F + 512 <= (sp - 128))
  /\ ((sp - 128) + 128 <= fl \/ fl + 1 <= (sp - 128))
  /\ (op + 384 <= F \/ F + 512 <= op)
  /\ (op + 384 <= fl \/ fl + 1 <= op)
  /\ (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= ((op / 8) + 2147450880))
  /\ (oec + 16 <= F \/ F + 512 <= oec)
  /\ (oec + 16 <= fl \/ fl + 1 <= oec)
  /\ (((oec / 8) + 2147450880) + 2 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= ((oec / 8) + 2147450880))
  /\ (F + 512 <= 65536 \/ 65536 + 1220608 <= F)
  /\ 6914048 <= ov <= 140737488355320
  /\ ov mod 8 = 0
  /\ (2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784)
  /\ L5KA.zeros_at MVi ((ov / 8) + 2147450880) 1
  /\ L5.writable RSEGS MVi ov 8
  /\ ((sp - 128) + 128 <= ov \/ ov + 8 <= (sp - 128))
  /\ L5.u64_at RSEGS MVi ov 1258992
  /\ L5KA.zeros_at MVi 2147608254 16
  /\ (op + 384 <= ov \/ ov + 8 <= op)
  /\ (oec + 16 <= ov \/ ov + 8 <= oec)
  /\ (F + 512 <= ov \/ ov + 8 <= F)
  /\ (fl + 1 <= ov \/ ov + 8 <= fl)
  /\ (((F / 8) + 2147450880) + 64 <= ((ov / 8) + 2147450880) \/ ((ov / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880))
  /\ (((F / 8) + 2147450880) + 64 <= 2147608254 \/ 2147608254 + 16 <= ((F / 8) + 2147450880))
  /\ L5.u8_at RSEGS MVi (op + 16) 0
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
  /\ L5.u64_at RSEGS MVi (sp - 104) (bv_unsigned (getr R (reg 27))).
Lemma pfacts_bc Mi mdi LKi cri Awi si smi eni ki ei Xi :
  PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned si eni ki) Mi mdi LKi cri Awi ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat ->
  PF (mrestrict (ahid Awi mdi) Mi).
Proof.
  intros BI CP. unfold PF.
  entry_facts. frame_facts. pose proof BI as (HHi & AMi & MRTi & INCAi & INCLi & ASTKi & EKbi & DKbi & OWNi & FSHDi). pose proof AMi as (Mhi & MIi).
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi. unfold SB in FSWi.
  assert (BASEi : PMSTA.base_okA RSEGS PMA.AD Mi) by exact BASE.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LKi cri Awi Mi mdi HHi BASEi) as (IC0 & CSBv & CUARv). fold Hi in IC0, CSBv, CUARv. fold MVi in IC0, CSBv, CUARv.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi sp 28672 128 HHi ASTKi ltac:(clear; lia)) as (_ & _ & WS128). fold Hi in WS128. fold MVi in WS128.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
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
  change (ff_bytes 3) with 512 in ApF, ApSF, ApFL, AeF, AeSF, AeFL, AvF, AvSF, AvFL, AsopSF, AseSF, AsvSF.
  change (512 / 8) with 64 in ApSF, AeSF, AvSF, AsopSF, AseSF, AsvSF. unfold SB in ApSF, AeSF, AvSF, AsopSF, AseSF, AsvSF.

  pose proof PA as (_ & _ & _ & _ & _ & _ & P16 & _).
  assert (P16v : L5.u8_at RSEGS MVi (op + 16) 0)
    by (apply (proj2 (L5A.u8_at_vis Hi Mi (op + 16) 0 (OVIS (op + 16) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))); exact P16).
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
Proof. intros MID. pose proof MID as (_ & BI & CP & _). exact (pfacts_bc _ _ _ _ _ _ _ _ _ _ _ BI CP). Qed.

Ltac open_vf H := unfold PF in H; destruct H as (VF1 & VF2 & VF3 & VF4 & VF5 & VF6 & VF7 & VF8 & VF9 & VF10 & VF11 & VF12 & VF13 & VF14 & VF15 & VF16 & VF17 & VF18 & VF19 & VF20 & VF21 & VF22 & VF23 & VF24 & VF25 & VF26 & VF27 & VF28 & VF29 & VF30 & VF31 & VF32 & VF33 & VF34 & VF35 & VF36 & VF37 & VF38 & VF39 & VF40 & VF41 & VF42 & VF43 & VF44 & VF45 & VF46 & VF47 & VF48 & VF49 & VF50 & VF51 & VF52 & VF53 & VF54 & VF55 & VF56 & VF57 & VF58 & VF59 & VF60 & VF61 & VF62 & VF63 & VF64 & VF65 & VF66 & VF67 & VF68 & VF69 & VF70 & VF71 & VF72 & VF73 & VF74 & VF75 & VF76 & VF77 & VF78 & VF79 & VF80 & VF81 & VF82 & VF83 & VF84 & VF85 & VF86 & VF87 & VF88).

Lemma pfacts_keep (Ma Mb : word -> option byte) : PF Ma -> mem_grows Ma Mb -> 6914048 <= fl ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 9) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 64) -> ~ (fl <= i < fl + 1) ->
      Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)) -> PF Mb.
Proof.
  intros VF MG FL6 AG. unfold PF in VF |- *. destruct VF as (VF1 & VF2 & VF3 & VF4 & VF5 & VF6 & VF7 & VF8 & VF9 & VF10 & VF11 & VF12 & VF13 & VF14 & VF15 & VF16 & VF17 & VF18 & VF19 & VF20 & VF21 & VF22 & VF23 & VF24 & VF25 & VF26 & VF27 & VF28 & VF29 & VF30 & VF31 & VF32 & VF33 & VF34 & VF35 & VF36 & VF37 & VF38 & VF39 & VF40 & VF41 & VF42 & VF43 & VF44 & VF45 & VF46 & VF47 & VF48 & VF49 & VF50 & VF51 & VF52 & VF53 & VF54 & VF55 & VF56 & VF57 & VF58 & VF59 & VF60 & VF61 & VF62 & VF63 & VF64 & VF65 & VF66 & VF67 & VF68 & VF69 & VF70 & VF71 & VF72 & VF73 & VF74 & VF75 & VF76 & VF77 & VF78 & VF79 & VF80 & VF81 & VF82 & VF83 & VF84 & VF85 & VF86 & VF87 & VF88).
  split; [exact VF1|].
  split; [exact VF2|].
  split; [exact VF3|].
  split; [exact VF4|].
  split; [intros i Hi; rewrite AG; [apply VF5; exact Hi| clear - Hi; lia| clear - Hi VF28 VF11 VF35 VF61 VF32 VF13 VF37 FL6; lia| clear - Hi VF28 VF11 VF35 VF61 VF32 VF13 VF37 FL6; lia| clear - Hi VF28 VF11 VF35 VF61 VF32 VF13 VF37 FL6; lia| clear - Hi VF28 VF11 VF35 VF61 VF32 VF13 VF37 FL6; lia]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF28 VF11 VF35 VF61 VF32 VF13 VF37 FL6; lia| clear - VF28 VF11 VF35 VF61 VF32 VF13 VF37 FL6; lia| clear - VF28 VF11 VF35 VF61 VF32 VF13 VF37 FL6; lia| exact VF6]|].
  split; [apply (PMF.u32_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF28 VF11 VF35 VF61 VF32 VF13 VF37 FL6; lia| clear - VF28 VF11 VF35 VF61 VF32 VF13 VF37 FL6; lia| clear - VF28 VF11 VF35 VF61 VF32 VF13 VF37 FL6; lia| exact VF7]|].
  split; [exact VF8|].
  split; [exact VF9|].
  split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF10)|].
  split; [exact VF11|].
  split; [exact VF12|].
  split; [exact VF13|].
  split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF11 VF41 VF42 VF43 VF13 VF28 VF32 VF35 VF37 FL6; lia| exact VF14]|].
  split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF11 VF41 VF42 VF43 VF13 VF28 VF32 VF35 VF37 FL6; lia| exact VF15]|].
  split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF11 VF41 VF42 VF43 VF13 VF28 VF32 VF35 VF37 FL6; lia| exact VF16]|].
  split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF17)|].
  split; [exact VF18|].
  split; [exact VF19|].
  split; [exact VF20|].
  split; [exact VF21|].
  split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF19 VF44 VF45 VF46 VF21 VF28 VF32 VF35 VF37 VF11 VF13 VF25 FL6; lia| exact VF22]|].
  split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF23)|].
  split; [exact VF24|].
  split; [exact VF25|].
  split; [exact VF26|].
  split; [exact VF27|].
  split; [exact VF28|].
  split; [exact VF29|].
  split; [exact (L5.defined_grows Ma Mb _ _ MG VF30)|].
  split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF31)|].
  split; [exact VF32|].
  split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF33)|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF28 VF32 VF41 VF38 VF35 VF11 VF13 VF37 FL6; lia| clear - VF28 VF32 VF41 VF38 VF35 VF11 VF13 VF37 FL6; lia| clear - VF28 VF32 VF41 VF38 VF35 VF11 VF13 VF37 FL6; lia| exact VF34]|].
  split; [exact VF35|].
  split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF36)|].
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
  split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF48 VF58 VF59 VF60 VF50 VF28 VF32 VF35 VF37 VF11 VF13 VF56 FL6; lia| exact VF51]|].
  split; [exact (L5.writable_grows RSEGS Ma Mb _ _ MG VF52)|].
  split; [exact VF53|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF48 VF58 VF59 VF60 VF50 VF28 VF32 VF35 VF37 VF11 VF13 VF56 FL6; lia| clear - VF48 VF58 VF59 VF60 VF50 VF28 VF32 VF35 VF37 VF11 VF13 VF56 FL6; lia| clear - VF48 VF58 VF59 VF60 VF50 VF28 VF32 VF35 VF37 VF11 VF13 VF56 FL6; lia| exact VF54]|].
  split; [apply (L5KA.zeros_at_agree1 Ma Mb); [intros i Hi; apply AG; clear - Hi VF28 VF11 VF35 VF61 VF32 VF13 VF37 FL6; lia| exact VF55]|].
  split; [exact VF56|].
  split; [exact VF57|].
  split; [exact VF58|].
  split; [exact VF59|].
  split; [exact VF60|].
  split; [exact VF61|].
  split; [apply (L5C.u8_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF11 VF41 VF42 VF43 VF13 VF28 VF32 VF35 VF37 FL6; lia| clear - VF11 VF41 VF42 VF43 VF13 VF28 VF32 VF35 VF37 FL6; lia| clear - VF11 VF41 VF42 VF43 VF13 VF28 VF32 VF35 VF37 FL6; lia| exact VF62]|].
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
  split; [exact VF75|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF76]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF77]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF78]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF79]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF80]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF81]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF82]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF83]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF84]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF85]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF86]|].
  split; [apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF87]|].
  apply (L5C.u64_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; clear - Hi VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| clear - VF8 VF18 VF39 VF40 VF28 VF11 VF35 FL6; lia| exact VF88].
Qed.

Definition VALU (n q c v x : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp | 33%nat => n | 34%nat => q | 35%nat => c | 36%nat => op | 37%nat => ov | 38%nat => oec | 39%nat => v | 47%nat => F | 48%nat => fl | 50%nat => x
  | 57%nat => bv_unsigned (getr R (reg 1)) | 58%nat => bv_unsigned (getr R (reg 8)) | 59%nat => bv_unsigned (getr R (reg 9)) | 60%nat => bv_unsigned (getr R (reg 18))
  | 61%nat => bv_unsigned (getr R (reg 19)) | 62%nat => bv_unsigned (getr R (reg 20)) | 63%nat => bv_unsigned (getr R (reg 21)) | 64%nat => bv_unsigned (getr R (reg 22))
  | 65%nat => bv_unsigned (getr R (reg 23)) | 66%nat => bv_unsigned (getr R (reg 24)) | 67%nat => bv_unsigned (getr R (reg 25)) | 68%nat => bv_unsigned (getr R (reg 26))
  | 69%nat => bv_unsigned (getr R (reg 27)) | _ => 0
  end.

Ltac piece_ctx MID :=
  open_amid MID;
  let X := fresh "VF" in
  pose proof (pfacts _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as X; cbv zeta in X;
  lazymatch type of MID with amid _ _ ?Mi ?mdi _ ?Awi _ _ _ _ _ _ _ =>
    set (Hi := ahid Awi mdi) in *; set (MVi := mrestrict Hi Mi) in * end;
  open_vf X.

Ltac fcl := first [sya | unfold PEARVP1.aligned; sya | unfold PEARVP2.aligned; sya | unfold PEARVP3.aligned; sya | unfold PEARVP4.aligned; sya | unfold PEARVP5.aligned; sya | unfold PEARVP6.aligned; sya].

Tactic Notation "pz" constr(conc) constr(fxi) constr(Ri) constr(n) constr(q) constr(c) constr(v) constr(x) "as" ident(P) :=
  let mv := lazymatch goal with m := mrestrict _ _ |- _ => m end in
  pose proof (conc fxi Ri mv (VALU n q c v x)) as P; unfold VALU in P; cbn beta iota in P.

Tactic Notation "keep_only" ne_hyp_list(l) :=
  clear - LY HIok ICok ILY PO LYa SRD GL RS VAL B10 MKE BA BO VN VB VU VI VD VS PMODE HH AM K0 ENT FRM FRS FOK SP32 A10 A11 A13 Ht A12 CPRE INCS POK MP NB HB CRED KONT
          op ov oec ois osk otb WR G APART FF' l.

Lemma ec_vis0 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_ec Y = false -> L5.u32_at RSEGS (mrestrict (ahid Awi mdi) Mi) oec 0.
Proof.
  intros MID EC. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
  unfold PECA.ec_stateA in ECS. rewrite EC in ECS. fold oec in ECS.
  pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb 0 cat HHi FOK' ECS) as ((_ & _ & _) & _ & _ & _ & EU & _ & _). exact EU.
Qed.
Lemma ec_vis1 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_ec Y = true ->
  exists v, 1 <= v <= 64 /\ L5.u32_at RSEGS (mrestrict (ahid Awi mdi) Mi) oec v.
Proof.
  intros MID EC. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
  unfold PECA.ec_stateA in ECS. rewrite EC in ECS. fold oec in ECS. destruct ECS as (v & Hv & ECS).
  pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb v _ HHi FOK' ECS) as ((_ & _ & _) & _ & _ & _ & EU & _ & _). exists v. split; [exact Hv| exact EU].
Qed.

Lemma call_mkec (q v : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 oec -> getr Ri (reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
  (forall fx' R' M' md' LK' Aw', regs_preserved Ri R' -> amid fx' R' M' md' LK' Aw' cri si smi eni ki true (w_ec true Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri 0xae310 Mi mdi) K.
Proof.
  intros MID J1 RAq J10 J11 Hv KONT'. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  assert (ECD : L5.defined Mi oec 16 /\ PMSPA.accA Mi oec 16).
  { pose proof ECS as ECS0. unfold PECA.ec_stateA in ECS0. fold oec in ECS0.
    destruct (s_ec Y); [destruct ECS0 as (v0 & _ & (_ & _ & D' & A')); exact (conj D' A')| destruct ECS0 as (_ & _ & D' & A'); exact (conj D' A')]. }
  assert (SZK : forall Mc lo g, L5SAR.ek L ar LBX FF sp 28672 WR M Mc -> sp - 28672 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g).
  { intros Mc lo g EKc H1' H2' H3' H4'.
    assert (WAPPR : PMKA.wapp WR).
    { intros rr Hin. destruct rr as [ra' rn]. unfold BIGSHADOW_LO, BIGSHADOW_HI. cbn [fst snd].
      pose proof FSAPP as (FA0 & FA1 & FA2).
      unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
      cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <-; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia|]). destruct Hin. }
    apply (PMKA.stksh_keepA L ar LBX FF sp 28672 WR M Mc EKc WAPPR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
    apply (PMKA.shadow_zero_sub M (sp - 28672) 3584); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
    apply PMKA.mod16_8'. replace (sp - 28672) with (sp + (-1792) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  unfold PECSA.make_ec_spec, PECSPA.make_ec_spec in MKE.
  apply (MKE fxi Ri Mi mdi K LBi FF' LKi Awi cri oec v (sp - 128) q ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 28672 128 14336 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply SZK; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 14336) with (sp + (-904) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMAUAR.ffroomA_push 8 1 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 3 (sp - 128 + 32) FRS); clear; lia. }
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
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned si eni ki) M6 model6 LK6 cri Aw6).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PEC.owned si eni ki) (PEC.owned si eni ki) Mi mdi LKi cri Awi M6 model6 LK6 cri Aw6 14336 Wc6 BI HP6 HH6 AM6 MRT6 INCAw6 INCLK6);
      [clear; lia| clear; lia| | | intros a X'; exact X'].
    - intros rr a Hin Hr. change (ff_bytes 3 / 8) with 64. unfold ocell, SB.
      pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
      assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
      pose proof FSAPP as (FA0 & FA1 & FA2).
      destruct (Wc6R rr a Hin Hr) as [X'|X']; (split; [clear - X' SLO SPT Eop Eoec F2 FSCEIL; lia|]).
      + destruct FA1 as [Y'|Y']; clear - X' Y' DF1 DF2 F1 F2 Eoec; lia.
      + clear - X' DF1; lia.
    - intros a Hc Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X'|X'].
      + apply (Ho (PMSP.o_ec AD fb, 16)); [unfold WR; wr_mem 6| wr_rng; clear - X' Eoec; lia].
      + unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr X' Eoec O1 Eop; lia|].
        destruct ei; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin.
        destruct Hin as [<-|[<-|[]]].
        * apply (Ho (pa_errcat_guard AD, 2)); [unfold WR; wr_mem 7| exact Hr].
        * apply (Ho (pa_atexit AD, 544)); [unfold WR; wr_mem 8| exact Hr]. }
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 3, sp - 128 + 32)] sp 28672 (sp - 128) 14336 Wc6 Wc6 Mi M6 ltac:(rewrite app_nil_l; exact HP6) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK6.
  assert (WAPP6 : PMKA.wapp Wc6).
  { intros rr Hin. unfold Wc6 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; cbn [fst snd].
    - pose proof FSAPP as (FA0 & FA1 & FA2). destruct FA1 as [Y'|Y']; clear - Y' F1 F2 Eoec; lia.
    - destruct ei; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
  assert (OUTB6 : forall q' m, In (q', m) LBi -> forall i, q' <= i < q' + m -> L5.outside Wc6 i).
  { intros q' m Hq i Hi' rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y'].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m oec 16 HHi Hq (PMAUAR.aobjA_push FF oec 16 _ (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia)))) as [Z'|Z']; clear - Hi' Y' Z'; lia.
    - pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q' m HHi Hq) as Z'. destruct Z' as [Z'|Z']; clear - Hi' Y' Z'; lia. }
  apply (KONT' fx6 R6 M6 model6 LK6 Aw6 RP6).
  split; [|split; [exact BI6| split; [| split; [exact ST| split; [intros _; reflexivity| exact CK]]]]].
  - pose proof (fun j Hj => L5SAR.cs_of_preserved Ri R6 j RP6 Hj) as R6c.
    split; [rewrite (R6c 2%nat) by inl; exact J2|]. split; [rewrite (R6c 8%nat) by inl; exact J8|]. split; [rewrite (R6c 9%nat) by inl; exact J9|].
    split; [rewrite (R6c 18%nat) by inl; exact J18|]. split; [rewrite (R6c 19%nat) by inl; exact J19|]. split; [rewrite (R6c 20%nat) by inl; exact J20|].
    split; [rewrite (R6c 21%nat) by inl; exact J21|]. split; [rewrite (R6c 22%nat) by inl; exact J22|]. split; [rewrite (R6c 26%nat) by inl; exact J26|].
    split; [rewrite (R6c 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (R6c j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (cpre_stepA LBi sp 28672 Wc6 Mi M6 Y si smi eni ki ei (w_ec true Y) si true EK6 WAPP6 BRBi).
    + unfold LBi. apply incl_appl. apply incl_refl.
    + unfold LBi. apply incl_appr. exact INCS.
    + intros i Hi' N1 N2 rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y']; [clear - N2 Y'; lia| clear - Hi' Y' Eop O1; lia].
    + intros q' m Hq. exact (OUTB6 q' m Hq).
    + reflexivity. + reflexivity. + reflexivity.
    + apply (PMKA.parser_keepA RSEGS AD L ar LBi FF sp 28672 Wc6 Mi M6 EK6 WAPP6 FRB BRBi _ _ _ AOP); [| | | | | exact PA].
      * unfold LBi, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. left. exact Hx.
      * intros i Hi' rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y']; [clear - Hi' Y' Eop Eoec; lia| clear - Hi' Y' Eop O1; lia].
      * unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.src_own; left; reflexivity.
      * unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
      * intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.vs_own. rewrite E0. right; right; left; reflexivity.
    + apply (PMAPAR.base_keepW L ar C LY LBi FF sp 28672 Wc6 Mi M6 EK6); [| | | | exact BASE].
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
    + exact CP.
Qed.

Lemma wr_wav : forall rr a, In rr WR -> L5.in_rng rr a -> ~ ocell sp a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 3 / 8).
Proof.
  entry_facts. frame_facts.
  assert (WRR' : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 2040) \/ (0x674080 <= a < 0x695df4)).
  { intros rr a Hin Hr. unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
  intros rr a Hin Hr. change (ff_bytes 3 / 8) with 64. unfold ocell, SB.
  pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  pose proof FSAPP as (FA0 & FA1 & FA2).
  destruct (WRR' rr a Hin Hr) as [X'|X']; (split; [clear - X' SLO SPT F2 FSCEIL; lia|]).
  - destruct FA1 as [Y'|Y']; clear - X' Y' DF1 DF2 F1 F2; lia.
  - clear - X' DF1; lia.
Qed.

Lemma wr_F : forall rr a, In rr WR -> L5.in_rng rr a -> ~ (F <= a < F + 512).
Proof.
  entry_facts. frame_facts.
  assert (WRR' : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 2040) \/ (0x674080 <= a < 0x695df4)).
  { intros rr a Hin Hr. unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
  assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF 0 0 (a + i)).
  { intros a n X1 X2 X3 i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - X1 X2 Hi'; lia| intros Y'; clear - X1 X2 Hi' Y'; lia]. }
  destruct (APART (fb + 32) 2008 0 0 (CLfb (fb + 32) 2008 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z' & _). change (ff_bytes 3) with 512 in Z'.
  pose proof GFR as (GF1 & _).
  intros rr a Hin Hr. destruct (WRR' rr a Hin Hr) as [X'|X']; [clear - X' Z'; lia| clear - X' GFR; lia].
Qed.

Lemma wr_stk : forall rr a, In rr WR -> L5.in_rng rr a -> ~ (sp - 128 <= a < sp).
Proof.
  entry_facts. frame_facts.
  assert (WRR' : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 2040) \/ (0x674080 <= a < 0x695df4)).
  { intros rr a Hin Hr. unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
  intros rr a Hin Hr. destruct (WRR' rr a Hin Hr) as [X'|X']; [clear - X' F2 FSCEIL GSLO; lia| clear - X' GSLO GSHI GSPT SLO SPT; lia].
Qed.

Lemma wappR : PMKA.wapp WR.
Proof.
  entry_facts. intros rr Hin. destruct rr as [ra' rn]. unfold BIGSHADOW_LO, BIGSHADOW_HI. cbn [fst snd].
  pose proof FSAPP as (FA0 & FA1 & FA2).
  unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
  cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <-; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia|]). destruct Hin.
Qed.

Lemma szk Mc lo g : L5SAR.ek L ar LBX FF sp 28672 WR M Mc -> sp - 28672 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g.
Proof.
  entry_facts. intros EKc H1' H2' H3' H4'.
  apply (PMKA.stksh_keepA L ar LBX FF sp 28672 WR M Mc EKc wappR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
  apply (PMKA.shadow_zero_sub M (sp - 28672) 3584); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
  apply PMKA.mod16_8'. replace (sp - 28672) with (sp + (-1792) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
Qed.

Lemma call_gl (q : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 op -> getr Ri (reg 11) = Z_to_bv 64 oec ->
  PECSPA.mp_gl tt p Y ->
  (forall fx' R' M' md' LK' Aw' cr' si' smi' ei', regs_preserved Ri R' -> PECSPA.gl_ret p Y R' ->
      amid fx' R' M' md' LK' Aw' cr' si' smi' eni ki ei' (PECSPA.gl_post p Y) ->
      PM.p_tb si' = PM.p_tb si -> PM.p_tg si' = PM.p_tg si -> PM.p_b si' = PM.p_b si -> PM.p_k si' = PM.p_k si ->
      (forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64 -> M' (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      (forall a, F + 32 <= a < F + 304 -> M' (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri (pa_get_length AD) Mi mdi) K.
Proof.
  intros MID J1 RAq J10 J11 MPG KONT'. entry_facts. frame_facts. open_amid MID.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
  unfold PECSA.get_length_spec, PECSPA.get_length_spec in GL.
  apply (GL PMODE fxi Ri Mi mdi K LBX FF' LKi Awi cri (sp - 128) q fb cat p Y si str smi eni ki ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 5) with 22528. change (22528 / 8) with 2816.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 28672 128 22528 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 22528) with (sp + (-1416) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMAUAR.ffroomA_push 8 5 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 3 (sp - 128 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 128) with (sp + (-4) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { split; [rewrite L5K.rl10; exact J10| rewrite L5K.rl11; exact J11]. }
  { exact CP. }
  { exact INCS. }
  { exact POK. }
  { exact MPG. }
  { exact (credit_le_keep _ _ _ _ CRED CK). }
  intros fx4 R4 M4 model4 LK4 Aw4 s4 sm4 e4 cr4 RP4 CPRE4 RET4 STEP4 EE4 ETB ETG EB EKK HP4 CK4 MRT4 INCLK4 INCAw4 AM4 HH4.
  change (PMSPA.pm_scr 5) with 22528 in HP4.
  assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned s4 eni ki) M4 model4 LK4 cr4 Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) [] (PEC.owned s4 eni ki) Mi mdi LKi cri Awi M4 model4 LK4 cr4 Aw4 22528 WR BI HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
      [clear; lia| clear; lia| exact wr_wav| intros a _ X'; exact X'| intros a X'; exact X']. }
  assert (FSH4 : forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64 -> M4 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
    assert (D2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
    intros a Ha. apply (proj1 HP4). split; [clear - Ha D1 D2; lia| split].
    - apply (L5SAR.fframe_shadow_client L ar LBX FF' (sp - 128) 22528 F 3 (sp - 128 + 32)); [left; reflexivity|].
      change (ff_bytes 3) with 512. unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Ha; lia.
    - intros rr Hin Hr. exact (proj2 (wr_wav rr a Hin Hr) ltac:(change (ff_bytes 3 / 8) with 64; unfold SB; exact Ha)). }
  assert (FDK4 : forall a, F + 32 <= a < F + 304 -> M4 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { pose proof GFR as (GF1 & GF2 & _). intros a Ha. apply (proj1 HP4). split; [clear - Ha GF1 GF2; lia| split].
    - apply (L5SAR.fframe_client L ar LBX FF' (sp - 128) 22528 F 3 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512. clear - Ha; lia.
    - intros rr Hin Hr. exact (wr_F rr a Hin Hr ltac:(clear - Ha; lia)). }
  apply (KONT' fx4 R4 M4 model4 LK4 Aw4 cr4 s4 sm4 e4 RP4 RET4); [| exact ETB| exact ETG| exact EB| exact EKK| exact FSH4| exact FDK4].
  split; [|split; [exact BI4| split; [exact CPRE4| split; [exact (PMAPAR.src_step_transA _ _ _ _ _ _ ST STEP4)| split; [intros X'; exact (EE4 (EIMP X'))| exact (credit_keep_trans _ _ _ _ _ _ CK CK4)]]]]].
  pose proof (fun j Hj => L5SAR.cs_of_preserved Ri R4 j RP4 Hj) as R4c.
  split; [rewrite (R4c 2%nat) by inl; exact J2|]. split; [rewrite (R4c 8%nat) by inl; exact J8|]. split; [rewrite (R4c 9%nat) by inl; exact J9|].
  split; [rewrite (R4c 18%nat) by inl; exact J18|]. split; [rewrite (R4c 19%nat) by inl; exact J19|]. split; [rewrite (R4c 20%nat) by inl; exact J20|].
  split; [rewrite (R4c 21%nat) by inl; exact J21|]. split; [rewrite (R4c 22%nat) by inl; exact J22|]. split; [rewrite (R4c 26%nat) by inl; exact J26|].
  split; [rewrite (R4c 27%nat) by inl; exact J27|].
  intros j Hj. rewrite (R4c j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
Qed.

Lemma call_crun (T : Type) (pc : Z) (args : T -> bvmap 5 word -> Z -> Prop) (MPf : T -> list Z -> st -> Prop) (Ff : T -> list Z -> st -> st)
    (SPEC : PECSPA.crun_spec RSEGS AD AAD EE L ar HI P T pc 7 args MPf Ff) (ta : T) (q : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> args ta Ri fb ->
  MPf ta p Y -> s_bad (Ff ta p Y) = false -> PESKA.spa_hb P (s_hi (Ff ta p Y)) ->
  (forall fx' R' M' md' LK' Aw' cr' si' smi' eni' ki' ei', regs_preserved Ri R' ->
      amid fx' R' M' md' LK' Aw' cr' si' smi' eni' ki' ei' (Ff ta p Y) ->
      (forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64 -> M' (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      (forall a, F + 32 <= a < F + 304 -> M' (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri pc Mi mdi) K.
Proof.
  intros MID J1 RAq ARGS MPa NBa HBa KONT'. entry_facts. frame_facts. open_amid MID.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
  pose proof SPEC as SP. unfold PECSPA.crun_spec in SP.
  apply (SP PMODE ta fxi Ri Mi mdi K LBX FF' LKi Awi cri (sp - 128) q fb cat p Y si str smi eni ki ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 7) with 26624. change (26624 / 8) with 3328.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 28672 128 26624 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 26624) with (sp + (-1672) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMAUAR.ffroomA_push 8 7 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 3 (sp - 128 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 128) with (sp + (-4) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { exact ARGS. }
  { exact CP. }
  { exact INCS. }
  { exact POK. }
  { exact MPa. }
  { exact NBa. }
  { exact HBa. }
  { exact (credit_le_keep _ _ _ _ CRED CK). }
  intros fx4 R4 M4 model4 LK4 Aw4 s4 sm4 en4 k4 e4 cr4 RP4 CPRE4 STEP4 EE4 HP4 CK4 MRT4 INCLK4 INCAw4 AM4 HH4.
  change (PMSPA.pm_scr 7) with 26624 in HP4.
  assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned s4 en4 k4) M4 model4 LK4 cr4 Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) [] (PEC.owned s4 en4 k4) Mi mdi LKi cri Awi M4 model4 LK4 cr4 Aw4 26624 WR BI HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
      [clear; lia| clear; lia| exact wr_wav| intros a _ X'; exact X'| intros a X'; exact X']. }
  assert (FSH4 : forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64 -> M4 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
    assert (D2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
    intros a Ha. apply (proj1 HP4). split; [clear - Ha D1 D2; lia| split].
    - apply (L5SAR.fframe_shadow_client L ar LBX FF' (sp - 128) 26624 F 3 (sp - 128 + 32)); [left; reflexivity|].
      change (ff_bytes 3) with 512. unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Ha; lia.
    - intros rr Hin Hr. exact (proj2 (wr_wav rr a Hin Hr) ltac:(change (ff_bytes 3 / 8) with 64; unfold SB; exact Ha)). }
  assert (FDK4 : forall a, F + 32 <= a < F + 304 -> M4 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { pose proof GFR as (GF1 & GF2 & _). intros a Ha. apply (proj1 HP4). split; [clear - Ha GF1 GF2; lia| split].
    - apply (L5SAR.fframe_client L ar LBX FF' (sp - 128) 26624 F 3 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512. clear - Ha; lia.
    - intros rr Hin Hr. exact (wr_F rr a Hin Hr ltac:(clear - Ha; lia)). }
  apply (KONT' fx4 R4 M4 model4 LK4 Aw4 cr4 s4 sm4 en4 k4 e4 RP4); [| exact FSH4| exact FDK4].
  split; [|split; [exact BI4| split; [exact CPRE4| split; [exact (PMAPAR.src_step_transA _ _ _ _ _ _ ST STEP4)| split; [intros X'; exact (EE4 (EIMP X'))| exact (credit_keep_trans _ _ _ _ _ _ CK CK4)]]]]].
  pose proof (fun j Hj => L5SAR.cs_of_preserved Ri R4 j RP4 Hj) as R4c.
  split; [rewrite (R4c 2%nat) by inl; exact J2|]. split; [rewrite (R4c 8%nat) by inl; exact J8|]. split; [rewrite (R4c 9%nat) by inl; exact J9|].
  split; [rewrite (R4c 18%nat) by inl; exact J18|]. split; [rewrite (R4c 19%nat) by inl; exact J19|]. split; [rewrite (R4c 20%nat) by inl; exact J20|].
  split; [rewrite (R4c 21%nat) by inl; exact J21|]. split; [rewrite (R4c 22%nat) by inl; exact J22|]. split; [rewrite (R4c 26%nat) by inl; exact J26|].
  split; [rewrite (R4c 27%nat) by inl; exact J27|].
  intros j Hj. rewrite (R4c j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
Qed.

Lemma cred_text Mi Xi si smi eni ki ei cri :
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PMSP.credit_le (PECA.pot_allA L ar P si eni ki) cri ->
  PMSP.credit_le (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) (PM.p_tb si) (PM.p_tg si))) cri.
Proof.
  intros CP CLE. pose proof CP as (PA & _ & EA & _ & SKA & _).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _). pose proof PVEC as (_ & _ & _ & Hk & _).
  pose proof EA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EHk & _).
  pose proof (PESKA.sink_potA_nonneg RSEGS L ar P Mi osk ki PO SKA) as (SP1 & SP2).
  pose proof (PMA.ly_cost L C LY) as (KPM & BLIN & BOV).
  apply (PMAPAR.pot_text_le_parserA L ar C LY si cri); [clear - Hk; lia|].
  pose proof (Z.pow_le_mono_r 2 (PEC.en_k eni) 12 ltac:(lia) ltac:(clear - EHk; lia)) as P2e. pose proof (PM.pow2_pos (PEC.en_k eni) ltac:(clear - EHk; lia)) as P2p.
  unfold PMSPA.credit_le, PMSP.credit_le, PECA.pot_allA, PEC.credit_add, PEC.pot_estack, PMSPA.scA in CLE |- *. cbn [fst snd] in CLE |- *.
  unfold PMSPA.HV, LibIfaceAB.heap_view in CLE |- *. cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in CLE |- *. rewrite KPM, BOV, BLIN in CLE |- *.
  assert (E2 : 0 <= PEC.ESZ * (2 ^ 12 - 2 ^ PEC.en_k eni)) by (unfold PEC.ESZ; apply Z.mul_nonneg_nonneg; clear - P2e; lia).
  clear - CLE SP1 SP2 EHk E2. split; nia.
Qed.

Lemma cred_enc Mi Xi si smi eni ki ei cri :
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PMSP.credit_le (PECA.pot_allA L ar P si eni ki) cri ->
  PMSP.credit_le (PECA.pot_encA L ar P eni ki) cri.
Proof.
  intros CP CLE. pose proof CP as (PA & _ & _ & _ & _ & _ & _ & TBOK & _).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PTB & PVEC & _). pose proof PVEC as (_ & _ & _ & Hk & _).
  pose proof (PMA.ly_cost L C LY) as (KPM & BLIN & BOV).
  assert (PPN : 0 <= fst (PM.pot_parser (PMSPA.HV L ar) si) /\ 0 <= snd (PM.pot_parser (PMSPA.HV L ar) si)).
  { pose proof PTB as (_ & _ & TBF). destruct TBOK as (TG1 & TG2 & _).
    unfold PM.pot_parser, PM.credit_add, PM.pot_stack, PM.pot_text. cbn [fst snd].
    unfold PMSPA.HV, LibIfaceAB.heap_view. cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead]. rewrite KPM, BOV.
    assert (CAPB : 0 <= PM.vs_cap (PM.p_tb si) <= 2 ^ 27) by (destruct (PM.p_tb si) as [n1|c1 n1 q1]; cbn [PM.vs_cap] in *; [lia| destruct TBF as (_ & _ & _ & _ & Hc1 & _); lia]).
    pose proof (PM.pow2_pos (PM.p_k si + 1) ltac:(lia)) as P2a. assert (P2b : 2 ^ (PM.p_k si + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
    clear - CAPB P2a P2b Hk TG1. split; nia. }
  unfold PMSP.credit_le, PECA.pot_allA, PECA.pot_encA, PEC.credit_add, PMSPA.scA in CLE |- *. cbn [fst snd] in CLE |- *. clear - CLE PPN BLIN. nia.
Qed.

Lemma call_slot (T : Type) (pc : Z) (args : T -> list fframe -> bvmap 5 word -> (word -> option byte) -> Z -> Z -> PM.pst -> Prop)
      (MPf : T -> list Z -> st -> Prop) (Ff : T -> list Z -> st -> st) (SPEC : PECSPA.eslot_spec RSEGS AD AAD EE L ar HI P T pc args MPf Ff)
      (av : T) (q : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 ov ->
  args av FF' Ri Mi (sp - 128) fb si ->
  MPf av p Y -> s_bad (Ff av p Y) = false -> PESKA.spa_hb P (s_hi (Ff av p Y)) ->
  (forall (fx' : FPState) R' M' md' LK' Aw' en' k' e' cr', regs_preserved Ri R' ->
      amid fx' R' M' md' LK' Aw' cr' si smi en' k' e' (Ff av p Y) ->
      (forall a, sp - 128 <= a < sp -> M' (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx') RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pc Mi mdi) K.
Proof.
  intros MID J1 RAq J10 ARGS MPE NB' HB' KONT'. entry_facts. frame_facts. open_amid MID.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
  unfold PECSPA.eslot_spec in SPEC.
  apply (SPEC PMODE av fxi Ri Mi mdi K LBX FF' LKi Awi cri (sp - 128) q fb cat p Y si str smi eni ki ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 4) with 20480. change (20480 / 8) with 2560.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 28672 128 20480 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 20480) with (sp + (-1288) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomA_push 8 4 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 3 (sp - 128 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 128) with (sp + (-4) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { rewrite L5K.rl10. exact J10. }
  { exact ARGS. }
  { exact CP. } { exact INCS. } { exact POK. } { exact MPE. } { exact NB'. } { exact HB'. }
  { exact (cred_enc Mi Y si smi eni ki ei cri CP (credit_le_keep _ _ _ _ CRED CK)). }
  intros fxn Rn Mn mdn LKn Awn en2 k2 e2 cr2 RP2 CPRE2 EIMP2 HP2 CK2 MRT2 INCLK2 INCAw2 AM2 HH2.
  change (PMSPA.pm_scr 4) with 20480 in HP2.
  assert (WeIN : forall rr, In rr (PEC.W_enc AD EE fb) -> In rr WR).
  { intros rr Hin. unfold PEC.W_enc, PMSP.err_W in Hin. cbn [app] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold WR; [wr_mem 9| wr_mem 10| wr_mem 6| wr_mem 7| wr_mem 8]. }
  assert (BI2 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned si en2 k2) Mn mdn LKn cr2 Awn).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PM.parser_own si) (PEC.owned si en2 k2) Mi mdi LKi cri Awi Mn mdn LKn cr2 Awn 20480 (PEC.W_enc AD EE fb) BI HP2 HH2 AM2 MRT2 INCAw2 INCLK2);
      [clear; lia| clear; lia| intros rr a Hin Hr; exact (wr_wav rr a (WeIN rr Hin) Hr)| intros a _ O rr Hin Hr; exact (O rr (WeIN rr Hin) Hr)| intros a X'; exact X']. }
  assert (CK2' : PMSP.credit_keep cri cr2 (PECA.pot_allA L ar P si eni ki) (PECA.pot_allA L ar P si en2 k2)).
  { unfold PMSP.credit_keep, PECA.pot_allA, PECA.pot_encA, PEC.credit_add in CK2 |- *. cbn [fst snd] in CK2 |- *. clear - CK2. lia. }
  assert (KP2 : forall a, sp - 128 <= a < sp -> Mn (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP2). split; [clear - Ha GSLO GSHI GSPT SLO SPT; lia| split].
    - apply L5SAR.stack_client; [clear - Ha GSLO GSHI GSPT SLO SPT; lia| clear - Ha; lia].
    - intros rr Hin Hr. exact (wr_stk rr a (WeIN rr Hin) Hr Ha). }
  apply (KONT' fxn Rn Mn mdn LKn Awn en2 k2 e2 cr2 RP2); [| exact KP2].
  split; [|split; [exact BI2| split; [exact CPRE2| split; [exact ST| split; [intros X'; exact (EIMP2 (EIMP X'))| exact (credit_keep_trans _ _ _ _ _ _ CK CK2')]]]]].
  pose proof (fun j Hj => L5SAR.cs_of_preserved Ri Rn j RP2 Hj) as Rnc.
  split; [rewrite (Rnc 2%nat) by inl; exact J2|]. split; [rewrite (Rnc 8%nat) by inl; exact J8|]. split; [rewrite (Rnc 9%nat) by inl; exact J9|].
  split; [rewrite (Rnc 18%nat) by inl; exact J18|]. split; [rewrite (Rnc 19%nat) by inl; exact J19|]. split; [rewrite (Rnc 20%nat) by inl; exact J20|].
  split; [rewrite (Rnc 21%nat) by inl; exact J21|]. split; [rewrite (Rnc 22%nat) by inl; exact J22|]. split; [rewrite (Rnc 26%nat) by inl; exact J26|].
  split; [rewrite (Rnc 27%nat) by inl; exact J27|].
  intros j Hj. rewrite (Rnc j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
Qed.

Lemma call_double (q : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 ov -> getr Ri (reg 13) = Z_to_bv 64 oec ->
  PECSPA.mp_enc p Y -> PESKA.spa_hb P (s_hi Y + 9) ->
  (forall (fx' : FPState) R' M' md' LK' Aw' en' k' e' cr' w, regs_preserved Ri R' -> (w = 5 \/ w = 9) ->
      amid fx' R' M' md' LK' Aw' cr' si smi en' k' e' (e_scalar w w Y) ->
      (forall a, sp - 128 <= a < sp -> M' (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx') RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri (pe_double EE) Mi mdi) K.
Proof.
  intros MID J1 RAq J10 J13 MPE HB' KONT'. entry_facts. frame_facts. open_amid MID.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
  pose proof VD as SPEC. unfold PECSA.v_double_spec, PECSPA.v_double_spec in SPEC.
  apply (SPEC PMODE fxi Ri Mi mdi K LBX FF' LKi Awi cri (sp - 128) q fb cat p Y si str smi eni ki ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 4) with 20480. change (20480 / 8) with 2560.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 28672 128 20480 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 20480) with (sp + (-1288) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomA_push 8 4 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 3 (sp - 128 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 128) with (sp + (-4) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { rewrite L5K.rl10. exact J10. }
  { rewrite L5K.rl13. exact J13. }
  { exact CP. } { exact INCS. } { exact POK. } { exact MPE. } { exact HB'. }
  { exact (cred_enc Mi Y si smi eni ki ei cri CP (credit_le_keep _ _ _ _ CRED CK)). }
  intros fxn Rn Mn mdn LKn Awn en2 k2 e2 cr2 w RP2 Hw CPRE2 EIMP2 HP2 CK2 MRT2 INCLK2 INCAw2 AM2 HH2.
  change (PMSPA.pm_scr 4) with 20480 in HP2.
  assert (WeIN : forall rr, In rr (PEC.W_enc AD EE fb) -> In rr WR).
  { intros rr Hin. unfold PEC.W_enc, PMSP.err_W in Hin. cbn [app] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold WR; [wr_mem 9| wr_mem 10| wr_mem 6| wr_mem 7| wr_mem 8]. }
  assert (BI2 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned si en2 k2) Mn mdn LKn cr2 Awn).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PM.parser_own si) (PEC.owned si en2 k2) Mi mdi LKi cri Awi Mn mdn LKn cr2 Awn 20480 (PEC.W_enc AD EE fb) BI HP2 HH2 AM2 MRT2 INCAw2 INCLK2);
      [clear; lia| clear; lia| intros rr a Hin Hr; exact (wr_wav rr a (WeIN rr Hin) Hr)| intros a _ O rr Hin Hr; exact (O rr (WeIN rr Hin) Hr)| intros a X'; exact X']. }
  assert (CK2' : PMSP.credit_keep cri cr2 (PECA.pot_allA L ar P si eni ki) (PECA.pot_allA L ar P si en2 k2)).
  { unfold PMSP.credit_keep, PECA.pot_allA, PECA.pot_encA, PEC.credit_add in CK2 |- *. cbn [fst snd] in CK2 |- *. clear - CK2. lia. }
  assert (KP2 : forall a, sp - 128 <= a < sp -> Mn (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP2). split; [clear - Ha GSLO GSHI GSPT SLO SPT; lia| split].
    - apply L5SAR.stack_client; [clear - Ha GSLO GSHI GSPT SLO SPT; lia| clear - Ha; lia].
    - intros rr Hin Hr. exact (wr_stk rr a (WeIN rr Hin) Hr Ha). }
  apply (KONT' fxn Rn Mn mdn LKn Awn en2 k2 e2 cr2 w RP2 Hw); [| exact KP2].
  split; [|split; [exact BI2| split; [exact CPRE2| split; [exact ST| split; [intros X'; exact (EIMP2 (EIMP X'))| exact (credit_keep_trans _ _ _ _ _ _ CK CK2')]]]]].
  pose proof (fun j Hj => L5SAR.cs_of_preserved Ri Rn j RP2 Hj) as Rnc.
  split; [rewrite (Rnc 2%nat) by inl; exact J2|]. split; [rewrite (Rnc 8%nat) by inl; exact J8|]. split; [rewrite (Rnc 9%nat) by inl; exact J9|].
  split; [rewrite (Rnc 18%nat) by inl; exact J18|]. split; [rewrite (Rnc 19%nat) by inl; exact J19|]. split; [rewrite (Rnc 20%nat) by inl; exact J20|].
  split; [rewrite (Rnc 21%nat) by inl; exact J21|]. split; [rewrite (Rnc 22%nat) by inl; exact J22|]. split; [rewrite (Rnc 26%nat) by inl; exact J26|].
  split; [rewrite (Rnc 27%nat) by inl; exact J27|].
  intros j Hj. rewrite (Rnc j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
Qed.

Lemma call_src (pc aln : Z) (args : list fframe -> bvmap 5 word -> (word -> option byte) -> Z -> Z -> PM.pst -> Prop)
      (Wx : bvmap 5 word -> list L5.range -> Prop)
      (res : list Z -> bvmap 5 word -> bvmap 5 word -> (word -> option byte) -> PM.srcst -> PM.srcst -> PM.strm -> PM.strm -> Prop)
      (SPEC : PECSPA.csrc_spec RSEGS AD L ar HI pc 4 aln args Wx res) (Wq : list L5.range) (ra : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_more Y = true -> s_done Y = false -> 0 <= s_pos Y <= blen p ->
  getr Ri (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr Ri (reg 10) = Z_to_bv 64 (op + 24) ->
  (aln = 16 \/ aln = 32) -> args FF' Ri Mi (sp - 128) fb si -> Wx Ri Wq ->
  (forall rr, In rr Wq -> F + 32 <= fst rr /\ fst rr + snd rr <= F + 304) ->
  (forall p0 Ra Rb Mb sa sb ma mb, res p0 Ra Rb Mb sa sb ma mb -> PECSPA.cwin RSEGS Mb p0 sb mb) ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 src2 smi2, regs_preserved Ri R2 -> res p Ri R2 M2 (PM.p_src si) src2 smi smi2 ->
      PEC.pos_of p (PM.p_src si) smi = s_pos Y ->
      (forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64 -> M2 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      (forall a, F + 32 <= a < F + 304 -> L5.outside Wq a -> M2 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      amid fx2 R2 M2 md2 LK2' Aw2 cri (PMSPA.with_src si src2) smi2 eni ki ei (w_pos (PEC.pos_of p src2 smi2) Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 ra M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pc Mi mdi) K.
Proof.
  intros MID MORE DONE PPOS J1 RAq J10 ALN ARGS WXQ WQR' RESW KX. entry_facts. frame_facts. open_amid MID.
  assert (WQR : forall rr a, In rr Wq -> L5.in_rng rr a -> F + 32 <= a < F + 304).
  { intros rr a Hin Hr. pose proof (WQR' rr Hin) as (W1 & W2). unfold L5.in_rng in Hr. clear - W1 W2 Hr. lia. }
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WBi & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDi & NDFi & _).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
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
  destruct (APART op 384 0 0 (CLfb op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (ApF & ApSF & ApFL).
  destruct (APART ois 272 0 0 (CLfb ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AiF & AiSF & AiFL).
  change (ff_bytes 3) with 512 in ApF, ApSF, AiF, AiSF. change (512 / 8) with 64 in ApSF, AiSF.
  pose proof GFR as (GF1 & GF2 & _).
  assert (Q0f : 0 <= F < 2 ^ 64) by (clear - GF1 GF2; lia).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  pose proof (Lpos MORE DONE) as POS.

  unfold PECSPA.csrc_spec in SPEC.
  apply (SPEC fxi Ri Mi mdi K (PEC.enc_own eni ++ PESK.sink_own ki ++ LBX) FF' LKi Awi cri (sp - 128) ra fb p si str smi Wq ltac:(rewrite <- EPO; exact HHi) AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 4) with 20480. change (20480 / 8) with 2560.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 28672 128 20480 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 20480) with (sp + (-1288) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomA_push 8 4 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 3 (sp - 128 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { destruct ALN as [-> | ->]; [replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16
                                | replace (sp - 128) with (sp + (-4) * 32) by (clear; lia); rewrite Z_mod_plus_full; exact SP32]. }
  { unfold PMSPA.o_src. fold op. rewrite L5K.rl10. exact J10. }
  { exact ARGS. }
  { exact WXQ. }
  { exact PA. }
  { exact IA. }
  { exact BASE. }
  { exact ACC. }
  { intros x Hx. apply in_or_app. right. apply in_or_app. right. exact (INCS x Hx). }
  { exact POK. }
  { exact CONT. }
  intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 RP4 PA4 IA4 STEP4 RES4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
  change (PMSPA.pm_scr 4) with 20480 in HP4. rewrite <- EPO in HP4, HH4.
  set (Wc := PMSPA.W_src AD fb (PM.p_src si) ++ Wq) in HP4.
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a ->
            (op + 280 <= a < op + 320) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (qc <= a < qc + 16384) \/ (F + 32 <= a < F + 304 /\ ~ L5.outside Wq a)).
  { intros rr a Hin Hr. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is AD PeCLayoutA.CADDR_A] in Hin. fold qc in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|Hin]]]];
      [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eop Eois; left; lia
      |unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eop Eois; right; left; lia
      |unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eop Eois; right; right; left; lia
      |unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr; clear - Hr; right; right; right; left; lia
      |right; right; right; right; split; [exact (WQR rr a Hin Hr)| intros O; exact (O rr Hin Hr)]]. }
  assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (D2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (WAV4 : forall rr a, In rr Wc -> L5.in_rng rr a -> ~ ocell sp a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 3 / 8)).
  { intros rr a Hin Hr. change (ff_bytes 3 / 8) with 64. unfold ocell, SB.
    destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|[X'|(X' & XW')]]]]; (split; [clear - X' O2 I2 Bq4 GFCEIL GSLO Eop Eois GF2 GFR; lia|]).
    + clear - X' OBIG D1 D2; lia.
    + clear - X' IBIG D1 D2; lia.
    + clear - X' IBIG D1 D2; lia.
    + destruct Bq5 as [Yb|Yb]; clear - X' Yb D1 D2; lia.
    + destruct GFBIG as [Yb|Yb]; clear - X' Yb D1 D2 GFR; lia. }

  assert (FSH4 : forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64 -> M4 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP4). split; [clear - Ha D1 D2; lia| split].
    - apply (L5SAR.fframe_shadow_client L ar LBi FF' (sp - 128) 20480 F 3 (sp - 128 + 32)); [left; reflexivity|].
      change (ff_bytes 3) with 512. unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Ha; lia.
    - intros rr Hin Hr. exact (proj2 (WAV4 rr a Hin Hr) ltac:(change (ff_bytes 3 / 8) with 64; unfold SB; exact Ha)). }

  assert (FDK4 : forall a, F + 32 <= a < F + 304 -> L5.outside Wq a -> M4 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { intros a Ha Hoq. apply (proj1 HP4). split; [clear - Ha GF1 GF2; lia| split].
    - apply (L5SAR.fframe_client L ar LBi FF' (sp - 128) 20480 F 3 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512. clear - Ha; lia.
    - assert (AOFF : PMSPA.aobjA FF' (F + 32) 272) by (exists (F, 3, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 3) with 512; clear; lia]).
      intros rr Hin Hr. destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|[X'|(X' & XW')]]]].
      + destruct (APART (op + 280) 40 0 0 (CLfb (op + 280) 40 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z' & _). change (ff_bytes 3) with 512 in Z'. clear - Ha X' Z'; lia.
      + destruct (APART (ois + 40) 8 0 0 (CLfb (ois + 40) 8 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z' & _). change (ff_bytes 3) with 512 in Z'. clear - Ha X' Z'; lia.
      + destruct (APART (ois + 152) 4 0 0 (CLfb (ois + 152) 4 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z' & _). change (ff_bytes 3) with 512 in Z'. clear - Ha X' Z'; lia.
      + destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 (F + 32) 272 HHi Iq AOFF) as [Z'|Z']; clear - Ha X' Z'; lia.
      + exact (XW' Hoq). }
  assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned si eni ki) M4 md4 LK4 cri Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PEC.owned si eni ki) (PEC.owned si eni ki) Mi mdi LKi cri Awi M4 md4 LK4 cri Aw4 20480 Wc BI HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
      [clear; lia| clear; lia| exact WAV4| | intros a X'; exact X'].
    intros a Hc Ho rr Hin Hr. destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|[X'|(X' & XW')]]]].
      + apply (Ho (PMSP.o_src AD fb + 256, 40)); [unfold WR; wr_mem 1| wr_rng; clear - X' Eop; lia].
      + apply (Ho (PMSP.o_is AD fb + 40, 8)); [unfold WR; wr_mem 2| wr_rng; clear - X' Eois; lia].
      + apply (Ho (PMSP.o_is AD fb + 152, 4)); [unfold WR; wr_mem 3| wr_rng; clear - X' Eois; lia].
      + assert (Iq' : In (qc, 16384) (PEC.owned si eni ki)) by (unfold PEC.owned; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
        exact (PMARS1.own_not_aclient L ar C HI HIok (PEC.owned si eni ki) LBX FF' LKi cri Awi Mi _ qc 16384 a sp 28672 HHi Iq' X' (L5SAR.aclient_cons L ar LBX FF (F, 3, sp - 128 + 32) sp 28672 a Hc)).
      + apply (GNCF a); [left; clear - X' GFR; lia| exact Hc]. }
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 3, sp - 128 + 32)] sp 28672 (sp - 128) 20480 Wc Wc Mi M4 ltac:(rewrite app_nil_l; exact HP4) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK4.
  assert (OUTc : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op + 280 \/ op + 320 <= a) -> (a + n <= ois + 40 \/ ois + 48 <= a) ->
                 (a + n <= ois + 152 \/ ois + 156 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i).
  { intros a n X1 X2 X3 X4 X5 i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Yc|[Yc|[Yc|[Yc|(Yc & YW)]]]]; [clear - Hi' Yc X3; lia| clear - Hi' Yc X4; lia| clear - Hi' Yc X5; lia| |].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 a n HHi Iq (PMAUAR.aobjA_push FF a n _ (AOF a n X1 X2))) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - destruct (APART a n 0 0 (CLfb a n X1 X2 ltac:(clear - Hi'; lia)) ltac:(clear - Hi'; lia)) as (Z' & _). change (ff_bytes 3) with 512 in Z'. clear - Hi' Yc Z' GFR; lia. }
  assert (WAPPc : PMKA.wapp Wc).
  { intros rr Hin. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is AD PeCLayoutA.CADDR_A] in Hin. fold qc in Hin.
    unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|[<-|[<-|[<-|Hin]]]]; cbn [fst snd]; unfold PM.CHUNK.
    - clear - OBIG Eop; lia.
    - clear - IBIG Eois; lia.
    - clear - IBIG Eois; lia.
    - destruct Bq5 as [Yb|Yb]; clear - Yb; lia.
    - pose proof (WQR' rr Hin) as (W1 & W2). destruct GFBIG as [Yb|Yb]; clear - Yb W1 W2 GFR; lia. }
  assert (OUTBc : forall q' m, In (q', m) LBi -> q' <> qc -> forall i, q' <= i < q' + m -> L5.outside Wc i).
  { intros q' m Hq' NE i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Yc|[Yc|[Yc|[Yc|(Yc & YW)]]]].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq' (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HHi Hq' (PMAUAR.aobjA_push FF ois 272 _ AOI)) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HHi Hq' (PMAUAR.aobjA_push FF ois 272 _ AOI)) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - pose proof (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ q' m qc 16384 HHi Hq' Iq NE) as Z'. clear - Hi' Yc Z'; lia.
    - pose proof (WBi _ Hq') as (_ & _ & _ & _ & _ & _ & FA). cbn [fst snd] in FA.
      unfold FS_BYTES in FA, GFS1, GFS2. clear - Hi' Yc FA GFS1 GFS2 GFR; lia. }
  assert (OUTcI : forall i, 0x674080 <= i < 0x695df4 -> L5.outside Wc i).
  { intros i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Yc|[Yc|[Yc|[Yc|(Yc & YW)]]]]; [clear - Hi' Yc O1; lia| clear - Hi' Yc I1; lia| clear - Hi' Yc I1; lia| |].
    - destruct Bqi as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - clear - Hi' Yc GFR; lia. }

  assert (EA4 : PECA.enc_atA RSEGS EE L ar M4 ov fb eni).
  { apply (PECFA.enc_keepA RSEGS EE L ar LBi FF sp 28672 Wc Mi M4 EK4 WAPPc FRB BRBi ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINC| | exact EA].
    - apply OUTc; clear - Eop Eov Eois; lia.
    - intros Hp. assert (INe : In (PEC.en_b eni, PEC.ESZ * PEC.ecap (PEC.en_k eni)) (PEC.enc_own eni)).
      { unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      refine (OUTBc _ _ (EINC _ INe) _). apply (NEQ _ (PEC.ESZ * PEC.ecap (PEC.en_k eni))). apply in_or_app. left. exact INe. }
  assert (VREF4 : L5.u64_at RSEGS M4 (op + 384) ov).
  { apply (PMKA.u64_keepA RSEGS L ar LBi FF sp 28672 Wc Mi M4 EK4 WAPPc FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF].
    apply OUTc; clear - Eop Eois; lia. }
  assert (SKA4 : PESKA.sink_atA RSEGS L ar P M4 osk ki).
  { apply (PECFA.sink_keepA RSEGS L ar LBi FF sp 28672 Wc Mi M4 EK4 WAPPc FRB BRBi P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [| exact KINC| | exact SKA].
    - apply OUTc; clear - Eop Eosk Eois; lia.
    - intros Hp. assert (INk : In (PESK.sk_b ki, PESK.sk_c ki) (PESK.sink_own ki)).
      { unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      refine (OUTBc _ _ (KINC _ INk) _). apply (NEQ _ (PESK.sk_c ki)). apply in_or_app. right. apply in_or_app. left. exact INk. }
  assert (ERR4 : PESTA.err_okA RSEGS AD AAD EE M4 ei).
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBi FF sp 28672 Wc Mi M4 EK4 ei PECSA.addrs_wf_A); [| exact ERR].
    intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUTcI; exact DI. }
  assert (BASE4 : PMSTA.base_okA RSEGS AD M4).
  { change (PMSTA.base_okA RSEGS PMA.AD M4). apply (PMASK.base_keep L ar C LY LBi FF sp 28672 Wc Mi M4 EK4); [| exact BASE].
    intros a Ha rr Hin Hr. destruct (WcR rr a Hin Hr) as [Yc|[Yc|[Yc|[Yc|(Yc & YW)]]]]; [clear - Ha Yc O1; lia| clear - Ha Yc I1; lia| clear - Ha Yc I1; lia| destruct Bqi as [Z'|Z']; clear - Ha Yc Z'; lia| clear - Ha Yc GFR; lia]. }
  assert (ECS4 : PECA.ec_stateA RSEGS AD M4 fb (s_ec Y) cat).
  { apply (PECFA.ec_state_keepA RSEGS AD L ar LBi FF sp 28672 Wc Mi M4 EK4 WAPPc FRB fb (s_ec Y) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
    fold oec. apply OUTc; clear - Eop Eoec Eois; lia. }
  assert (ACC4 : PMSPA.accA M4 op PECA.RDR_BYTES).
  { pose proof BI4 as (_ & _ & _ & _ & _ & _ & EKb4 & _).
    exact (PMKA.acc_keepA' L ar LBX FF sp 28672 WR M M4 EKb4 wappR FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CPRE))))))))))))). }
  assert (QC4 : PM.sr_qc src4 = qc) by (destruct STEP4 as (X' & _); exact X').
  set (s4 := PMSPA.with_src si src4) in *.
  assert (EOWN : PM.parser_own s4 = PM.parser_own si) by (unfold s4, PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC4; reflexivity).
  assert (EOWN4 : PEC.owned s4 eni ki = PEC.owned si eni ki) by (unfold PEC.owned; rewrite EOWN; reflexivity).

  assert (CONT4 : PEC.content_ok RSEGS AD M4 fb p src4 str sm4).
  { destruct (RESW _ _ _ _ _ _ _ _ RES4) as (CWP & CWB & CW5). pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS3 & _). pose proof VS3 as (_ & _ & VSF3).
    apply (PECF.content_ok_step RSEGS AD Mi M4 fb p (PM.p_src si) str smi src4 sm4); [clear - I1 Eois; unfold PMSP.o_is; cbn [pa_off_is AD PeCLayoutA.CADDR_A]; lia| clear - I3 Eois; unfold PMSP.o_is; cbn [pa_off_is AD PeCLayoutA.CADDR_A]; lia| | | | exact (proj1 CWP)| exact CWB| exact CW5| exact CONT].
    - unfold PMSP.o_is. cbn [pa_off_is AD PeCLayoutA.CADDR_A]. change (fb + 96) with ois.
      exact (proj1 (PMKA.agA_obj L ar LBi FF sp 28672 Wc Mi M4 EK4 WAPPc FRB (ois + 80) 24 (AOF (ois + 80) 24 ltac:(lia) ltac:(lia)) (OUTc (ois + 80) 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))).
    - intros c0 n0 q0 Es. cbn in VSF3. rewrite Es in VSF3. cbn in VSF3. destruct VSF3 as (_ & _ & _ & Hn0 & Hc0 & _).
      assert (IN0 : In (q0, c0) LBi) by (apply SINC; unfold PM.vs_own; rewrite Es; left; reflexivity).
      destruct (BRBi _ IN0) as (B0' & B1'). cbn [fst snd] in B0', B1'.
      split; [exact B0'|]. split; [clear - B1'; lia|]. split; [clear - Hn0; lia|].
      refine (proj1 (PMKA.agA_blk L ar LBi FF sp 28672 Wc Mi M4 EK4 WAPPc BRBi q0 c0 IN0 _)).
      refine (OUTBc q0 c0 IN0 _). apply (NEQ q0 c0). apply in_or_app. right. apply in_or_app. right. apply INCS. unfold PM.vs_own. rewrite Es. left. reflexivity.
    - intros n0 Es. cbn in VSF3. rewrite Es in VSF3. cbn in VSF3. clear - VSF3. lia. }
  assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr Ri (reg j))
    by (intros j Hj; exact (L5SAR.cs_of_preserved Ri R4 j RP4 Hj)).
  apply (KX fx4 R4 M4 md4 LK4 Aw4 src4 sm4 RP4 RES4 POS FSH4 FDK4).
  unfold amid. split; [| split; [rewrite <- EOWN4 in BI4; exact BI4| split; [| split; [| split; [exact EIMP|]]]]].
  - split; [rewrite (R4c 2%nat) by inl; exact J2|]. split; [rewrite (R4c 8%nat) by inl; exact J8|]. split; [rewrite (R4c 9%nat) by inl; exact J9|].
    split; [rewrite (R4c 18%nat) by inl; exact J18|]. split; [rewrite (R4c 19%nat) by inl; exact J19|]. split; [rewrite (R4c 20%nat) by inl; exact J20|].
    split; [rewrite (R4c 21%nat) by inl; exact J21|]. split; [rewrite (R4c 22%nat) by inl; exact J22|]. split; [rewrite (R4c 26%nat) by inl; exact J26|].
    split; [rewrite (R4c 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (R4c j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
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

Lemma w_pos_self Y : w_pos (s_pos Y) Y = Y.
Proof. destruct Y; reflexivity. Qed.

Lemma call_read (q kk ra g sv : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_more Y = true -> s_done Y = false -> 0 <= s_pos Y <= blen p ->
  getr Ri (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra ->
  getr Ri (reg 10) = Z_to_bv 64 (op + 24) -> getr Ri (reg 11) = Z_to_bv 64 q -> getr Ri (reg 12) = Z_to_bv 64 kk ->
  q = F + 8 * g -> 4 <= g <= 36 -> 1 <= kk <= 8 ->
  L5.u8_at RSEGS (mrestrict (ahid Awi mdi) Mi) (F / 8 + 2147450880 + g) sv -> (sv = 0 \/ kk <= sv <= 7) ->
  (forall (fxb : FPState) Rb Mb mdb LKb Awb srcb smb d, regs_preserved Ri Rb -> getr Rb (reg 10) = Z_to_bv 64 d -> 0 <= d <= kk ->
      (d < kk -> s_pos Y + d = blen p) -> s_pos Y + d <= blen p ->
      L5.bytes_at RSEGS Mb q (UbjRef.slice p (s_pos Y) d) -> L5.u8_at RSEGS Mb (F / 8 + 2147450880 + g) sv ->
      amid fxb Rb Mb mdb LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos Y + d) Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxb) RSEGS Rb ra Mb mdb) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri (pa_src_read AD) Mi mdi) K.
Proof.
  intros MID MORE DONE PPOS J1 RAq J10 J11 J12 Eq Hg Hkk SHB SVK KX. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  pose proof GFR as (GF1 & GF2 & _).
  assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF 0 0 (a + i)).
  { intros a n X1 X2 X3 i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - X1 X2 Hi'; lia| intros Y'; clear - X1 X2 Hi' Y'; lia]. }
  destruct (APART op 384 0 0 (CLfb op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (ApF & _).
  destruct (APART ois 272 0 0 (CLfb ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AiF & _).
  change (ff_bytes 3) with 512 in ApF, AiF.
  assert (FDm : L5.defined Mi F 512) by (apply (proj1 (L5A.defined_vis Hi Mi F 512 VFi)); exact FDi).
  assert (SHBm : L5.u8_at RSEGS Mi (F / 8 + 2147450880 + g) sv).
  { apply (proj1 (L5A.u8_at_vis Hi Mi (F / 8 + 2147450880 + g) sv (L5A.avis_sub Hi (F / 8 + SB) 64 (F / 8 + 2147450880 + g) 1 VSHi ltac:(unfold SB; clear - Hg; lia) ltac:(unfold SB; clear - Hg; lia))
             ltac:(clear - GF1 Hg; lia) ltac:(unfold SB; clear - GF1 GF2 Hg; lia))). exact SHB. }
  assert (ACCq : PMSPA.accA Mi q kk).
  { unfold PMSPA.accA, aacc. intros a Ha. unfold S.
    assert (Da : a / 8 + SB = F / 8 + 2147450880 + g) by (unfold SB; rewrite (div8_off F a g (proj1 GF8)); [clear; lia| clear - Ha Eq Hkk; lia]).
    rewrite Da. pose proof (L5ADHR.byte_of_u8 Mi _ sv SHBm ltac:(right; clear - GF1 Hg; lia) ltac:(clear - GF1 GF2 Hg; lia)) as BY.
    destruct SVK as [S0|Skk]; [left; rewrite <- S0; exact BY| right]. exists sv. split; [exact BY|]. split; [clear - Skk Hkk; lia|].
    assert (Am : a mod 8 = a - q) by (rewrite Eq; rewrite (Zmod_eq a 8) by (clear; lia); rewrite (div8_off F a g (proj1 GF8)) by (clear - Ha Eq Hkk; lia); clear - GF8; lia).
    rewrite Am. clear - Ha Skk; lia. }
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). pose proof (Lpos MORE DONE) as POS.
  pose proof SRD as SP. unfold PECSA.src_read_spec, PECSPA.src_read_spec in SP.
  apply (call_src (pa_src_read AD) 16 (PECSPA.cread_args AD) PECSPA.cread_W (PECSPA.cread_res RSEGS) SP [(q, kk)] ra fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y MID MORE DONE PPOS J1 RAq J10
           ltac:(left; reflexivity)).
  { exists q, kk. split; [rewrite L5K.rl11; exact J11|]. split; [rewrite L5K.rl12; exact J12|]. split; [clear - Hkk; lia|].
    split; [exists (F, 3, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 3) with 512; clear - Eq Hg Hkk; lia]|].
    split; [apply (L5.defined_sub Mi F 512); [exact FDm| clear - Eq Hg; lia| clear - Eq Hg Hkk; lia]|].
    split; [exact ACCq|]. split; [fold ois; clear - AiF Eq Hg Hkk; lia| fold op; unfold PECA.RDR_BYTES; clear - ApF Eq Hg Hkk; lia]. }
  { exists q, kk. split; [rewrite L5K.rl11; exact J11|]. split; [rewrite L5K.rl12; exact J12|]. split; [clear - GF1 GF2 Eq Hg Hkk; lia|]. split; [clear - Hkk; lia| reflexivity]. }
  { intros rr [<-|[]]. cbn [fst snd]. clear - Eq Hg Hkk; lia. }
  { intros p0 Ra Rb Mb sa sb ma mb (CW & _). exact CW. }
  intros fxb Rb Mb mdb LKb Awb srcb smb RPb RES POS' FSHb _ MIDb.
  assert (SHBb : L5.u8_at RSEGS Mb (F / 8 + 2147450880 + g) sv).
  { apply (L5C.u8_at_agree RSEGS Mi Mb); [intros i Hi'; apply FSHb; clear - Hi' Hg; lia| clear - GF1 Hg; lia| clear - GF1 GF2 Hg; lia| exact SHBm]. }
  destruct RES as (CW4 & p' & k' & d & Yp & Yk & Hp1 & Hp2 & Hk' & Yd & Hd & CONS & SHORT & DEFd & BYT).
  assert (Ek : k' = kk).
  { rewrite L5K.rl12 in Yk. rewrite J12 in Yk. apply (f_equal bv_unsigned) in Yk. unfold PM.CHUNK in Hk'. rewrite !L5.unsigned_lit in Yk by (clear - Hk' Hkk; lia). clear - Yk; lia. }
  subst k'.
  assert (Ep : p' = q).
  { rewrite L5K.rl11 in Yp. rewrite J11 in Yp. apply (f_equal bv_unsigned) in Yp. rewrite !L5.unsigned_lit in Yp by (clear - Hp1 Hp2 GF1 GF2 Eq Hg Hkk; lia). clear - Yp; lia. }
  subst p'. rewrite L5K.rl10 in Yd.
  assert (UNR : PM.unread (PM.p_src si) smi = blen p - s_pos Y) by (unfold PEC.pos_of in POS; clear - POS; lia).
  unfold PMSPA.consumed in CONS.
  assert (LE : s_pos Y + d <= blen p).
  { destruct CW4 as (CWP & _). unfold PEC.pos_of in CWP. clear - CWP CONS UNR Hd. lia. }
  assert (SHORT' : d < kk -> s_pos Y + d = blen p).
  { intros Hdk. pose proof (SHORT Hdk) as U0. clear - U0 CONS UNR. lia. }
  assert (EP : PEC.pos_of p srcb smb = s_pos Y + d) by (unfold PEC.pos_of in POS |- *; clear - CONS POS; lia).
  rewrite POS in BYT. rewrite EP in MIDb.
  exact (KX fxb Rb Mb mdb LKb Awb srcb smb d RPb Yd Hd SHORT' LE BYT SHBb MIDb).
Qed.

Lemma call_span (len q : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_more Y = true -> s_done Y = false -> 0 <= s_pos Y <= blen p ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 (op + 24) -> getr Ri (reg 11) = Z_to_bv 64 len -> getr Ri (reg 12) = Z_to_bv 64 otb -> 0 <= len < 2 ^ 64 ->
  (forall fx' R' M' md' LK' Aw' cr' si' smi' ptr n, regs_preserved Ri R' ->
      getr R' (reg 10) = Z_to_bv 64 ptr -> getr R' (reg 11) = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
      ((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own si') /\ B <= ptr /\ ptr + n <= B + m) \/ (otb + 1 <= ptr /\ ptr + n <= otb + 24)) ->
      L5.defined M' ptr n -> PMSPA.accA M' ptr n -> L5.bytes_at RSEGS M' ptr (UbjRef.slice p (s_pos Y) n) -> n = Z.min len (blen p - s_pos Y) ->
      amid fx' R' M' md' LK' Aw' cr' si' smi' eni ki ei (w_pos (s_pos Y + n) Y) ->
      PM.p_b si' = PM.p_b si -> PM.p_k si' = PM.p_k si ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri (pa_read_span AD) Mi mdi) K.
Proof.
  intros MID MORE DONE PPOS J1 RAq J10 J11 J12 Hlen KONT'. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  set (LBX0 := PEC.enc_own eni ++ PESK.sink_own ki ++ LBX).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). pose proof (Lpos MORE DONE) as POS.
  unfold PECSA.read_span_spec, PECSPA.read_span_spec in RS.
  apply (RS fxi Ri Mi mdi K LBX0 FF' LKi Awi cri (sp - 128) q fb len p si str smi ltac:(unfold LBX0; rewrite PEC.owned_app; exact HHi) AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 6) with 24576. change (24576 / 8) with 3072.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 28672 128 24576 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 24576) with (sp + (-1544) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMAUAR.ffroomA_push 8 6 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 3 (sp - 128 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 128) with (sp + (-4) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { rewrite L5K.rl10. exact J10. }
  { rewrite L5K.rl11. exact J11. }
  { rewrite L5K.rl12. exact J12. }
  { exact Hlen. }
  { exact PA. } { exact IA. } { exact BASE. } { exact ACC. } { exact TBOK. }
  { unfold LBX0. intros x Hx. apply in_or_app. right. apply in_or_app. right. exact (INCS x Hx). }
  { exact POK. } { exact CONT. }
  { exact (cred_text Mi Y si smi eni ki ei cri CP (credit_le_keep _ _ _ _ CRED CK)). }
  intros fxn Rn Mn mdn LKn Awn s2 sm2 cr2 ptr n RP2 Y10 Y11 Hn Hn26 LOC DEF2 ACC2 BYT2 NMIN PA2 IA2 TBOK2 CONT2 Emore Edone Edepth Eb Ek Estk STEP2 CONS HP2 CK2 MRT2 INCLK2 INCAw2 AM2 HH2.
  change (PMSPA.pm_scr 6) with 24576 in HP2. rewrite L5K.rl10 in Y10. rewrite L5K.rl11 in Y11.
  assert (OWN2 : PM.parser_own s2 ++ LBX0 = PEC.owned s2 eni ki ++ LBX) by (unfold LBX0; rewrite PEC.owned_app; reflexivity).
  rewrite OWN2 in HH2. fold otb in HP2. set (Wc := PMSPA.W_srcf AD fb ++ [(otb, 24)]) in HP2.
  pose proof HP2 as HP2a. unfold LBX0 in HP2a. rewrite app_assoc in HP2a.
  assert (X0INC : incl LBX0 LBi) by (unfold LBX0, LBi, PEC.owned; intros x Hx; rewrite <- !app_assoc; apply in_or_app; right; exact Hx).
  assert (BRB0 : forall b, In b LBX0 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; exact (BRBi b (X0INC b Hb))).
  assert (WcIN : forall rr, In rr Wc -> In rr WR).
  { intros rr Hin. unfold Wc, PMSPA.W_srcf in Hin. cbn [app] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; unfold WR; [wr_mem 1| wr_mem 2| wr_mem 3| wr_mem 4]. }
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a -> (op + 280 <= a < op + 320) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (otb <= a < otb + 24)).
  { intros rr a Hin Hr. unfold Wc, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is AD PeCLayoutA.CADDR_A] in Hin.
    unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; [clear - Hr Eop| clear - Hr Eois| clear - Hr Eois| clear - Hr Eotb Eop]; lia. }
  assert (BI2 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned s2 eni ki) Mn mdn LKn cr2 Awn).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PEC.enc_own eni ++ PESK.sink_own ki) (PEC.owned s2 eni ki) Mi mdi LKi cri Awi Mn mdn LKn cr2 Awn 24576 Wc BI HP2a HH2 AM2 MRT2 INCAw2 INCLK2);
      [clear; lia| clear; lia| intros rr a Hin Hr; exact (wr_wav rr a (WcIN rr Hin) Hr)| intros a _ O rr Hin Hr; exact (O rr (WcIN rr Hin) Hr)| intros a X'; exact X']. }
  pose proof (L5SAR.ek_callee L ar LBX0 [] FF [(F, 3, sp - 128 + 32)] sp 28672 (sp - 128) 24576 Wc Wc Mi Mn ltac:(rewrite app_nil_l; exact HP2) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK2.
  assert (WAPPc : PMKA.wapp Wc) by (intros rr Hin; exact (wappR rr (WcIN rr Hin))).
  assert (OUTc : forall a m, fb + 32 <= a -> a + m <= fb + 2040 -> (a + m <= op + 280 \/ op + 320 <= a) -> (a + m <= ois + 40 \/ ois + 48 <= a) -> (a + m <= ois + 152 \/ ois + 156 <= a) ->
                 (a + m <= otb \/ otb + 24 <= a) -> forall i, a <= i < a + m -> L5.outside Wc i).
  { intros a m X1 X2 X3 X4 X5 X6 i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Y'|[Y'|[Y'|Y']]]; [clear - Hi' Y' X3| clear - Hi' Y' X4| clear - Hi' Y' X5| clear - Hi' Y' X6]; lia. }
  assert (OUTBc : forall q' m, In (q', m) LBX0 -> forall i, q' <= i < q' + m -> L5.outside Wc i).
  { intros q' m Hq0 i Hi' rr Hin Hr. pose proof (X0INC _ Hq0) as Hq. destruct (WcR rr i Hin Hr) as [Y'|[Y'|[Y'|Y']]].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Y' Z'; lia.
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HHi Hq (PMAUAR.aobjA_push FF ois 272 _ AOI)) as [Z'|Z']; clear - Hi' Y' Z'; lia.
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HHi Hq (PMAUAR.aobjA_push FF ois 272 _ AOI)) as [Z'|Z']; clear - Hi' Y' Z'; lia.
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Y' Z' Eotb; lia. }
  assert (EINC : incl (PEC.enc_own eni) LBX0) by (unfold LBX0; intros x Hx; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own ki) LBX0) by (unfold LBX0; intros x Hx; apply in_or_app; right; apply in_or_app; left; exact Hx).
  unfold PEC.pos_of in POS, BYT2, NMIN. unfold PMSPA.consumed in CONS.
  assert (CK2' : PMSP.credit_keep cri cr2 (PECA.pot_allA L ar P si eni ki) (PECA.pot_allA L ar P s2 eni ki)).
  { pose proof (PMA.ly_cost L C LY) as (KPM & BLIN & BOV).
    unfold PMSP.credit_keep, PECA.pot_allA, PEC.credit_add, PM.pot_parser, PM.credit_add, PMSPA.scA in CK2 |- *. cbn [fst snd] in CK2 |- *. rewrite BLIN in CK2 |- *. rewrite Ek. clear - CK2. lia. }
  apply (KONT' fxn Rn Mn mdn LKn Awn cr2 s2 sm2 ptr n RP2 Y10 Y11 Hn Hn26 LOC DEF2 ACC2); [rewrite <- POS; exact BYT2| rewrite <- POS; exact NMIN| | exact Eb| exact Ek].
  split; [|split; [exact BI2| split; [| split; [exact (PMAPAR.src_step_transA _ _ _ _ _ _ ST STEP2)| split; [exact EIMP| exact (credit_keep_trans _ _ _ _ _ _ CK CK2')]]]]].
  - pose proof (fun j Hj => L5SAR.cs_of_preserved Ri Rn j RP2 Hj) as Rnc.
    split; [rewrite (Rnc 2%nat) by inl; exact J2|]. split; [rewrite (Rnc 8%nat) by inl; exact J8|]. split; [rewrite (Rnc 9%nat) by inl; exact J9|].
    split; [rewrite (Rnc 18%nat) by inl; exact J18|]. split; [rewrite (Rnc 19%nat) by inl; exact J19|]. split; [rewrite (Rnc 20%nat) by inl; exact J20|].
    split; [rewrite (Rnc 21%nat) by inl; exact J21|]. split; [rewrite (Rnc 22%nat) by inl; exact J22|]. split; [rewrite (Rnc 26%nat) by inl; exact J26|].
    split; [rewrite (Rnc 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (Rnc j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - split; [exact PA2|]. split; [exact IA2|].
    split; [apply (PECFA.enc_keepA RSEGS EE L ar LBX0 FF sp 28672 Wc Mi Mn EK2 WAPPc FRB BRB0 ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [apply OUTc; clear - Eov Eop Eois Eotb; lia| exact EINC| | exact EA]|].
    { intros Hp. refine (OUTBc _ _ _). apply EINC. unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    split; [apply (PMKA.u64_keepA RSEGS L ar LBX0 FF sp 28672 Wc Mi Mn EK2 WAPPc FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [apply OUTc; clear - Eop Eois Eotb; lia| exact VREF]|].
    split; [apply (PECFA.sink_keepA RSEGS L ar LBX0 FF sp 28672 Wc Mi Mn EK2 WAPPc FRB BRB0 P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [apply OUTc; clear - Eosk Eop Eois Eotb; lia| exact KINC| | exact SKA]|].
    { intros Hp. refine (OUTBc _ _ _). apply KINC. unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    split; [change (PMSTA.base_okA RSEGS PMA.AD Mn); apply (PMASK.base_keep L ar C LY LBX0 FF sp 28672 Wc Mi Mn EK2); [| exact BASE]|].
    { intros a Ha rr Hin Hr. destruct (WcR rr a Hin Hr) as [Y'|[Y'|[Y'|Y']]]; [clear - Ha Y' O1| clear - Ha Y' I1| clear - Ha Y' I1| clear - Ha Y' O1 Eotb]; lia. }
    split.
    { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBX0 FF sp 28672 Wc Mi Mn EK2 ei PECSA.addrs_wf_A); [| exact ERR].
      intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
      split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|].
      intros rr Hin Hr. destruct (WcR rr a Hin Hr) as [Y'|[Y'|[Y'|Y']]]; [clear - DI Y' O1| clear - DI Y' I1| clear - DI Y' I1| clear - DI Y' O1 Eotb]; lia. }
    split; [exact TBOK2|]. split; [exact CONT2|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_pos].
      rewrite Emore, Edone, Edepth, Estk. split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|].
      split; [intros _ _; unfold PEC.pos_of; clear - CONS POS; lia|].
      split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad]. }
    split; [| split; [exact ECI|]].
    { cbn [s_ec w_pos]. apply (PECFA.ec_state_keepA RSEGS AD L ar LBX0 FF sp 28672 Wc Mi Mn EK2 WAPPc FRB fb (s_ec Y) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
      fold oec. apply OUTc; clear - Eoec Eop Eois Eotb; lia. }
    pose proof BI2 as (_ & _ & _ & _ & _ & _ & EKb2 & _).
    exact (PMKA.acc_keepA' L ar LBX FF sp 28672 WR M Mn EKb2 wappR FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) (PECA.crun_preA_rdr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPRE)).
Qed.

Lemma call_valid (pp n q : Z) (l : list Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 pp -> getr Ri (reg 11) = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
  0 <= pp -> (n = 0 \/ 0 < pp) -> pp + n <= 2 ^ 47 -> L5.defined Mi pp n -> PMSPA.accA Mi pp n ->
  (n = 0 \/ (exists B m, In (B, m) (PEC.owned si eni ki ++ LBX) /\ B <= pp /\ pp + n <= B + m) \/ (otb + 1 <= pp /\ pp + n <= otb + 24) \/ (F + 32 <= pp /\ pp + n <= F + 504)) ->
  L5.bytes_at RSEGS Mi pp l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
  (forall fx' R' M' md' v, regs_preserved Ri R' -> getr R' (reg 11) = Z_to_bv 64 v -> 0 <= v < 7 -> (v = 0 <-> UbjRef.utf8_valid l = true) ->
      mem_grows Mi M' -> (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 - 12288 <= i < sp - 128) -> M' (Z_to_bv 64 i) = Mi (Z_to_bv 64 i)) ->
      amid fx' R' M' md' LKi Awi cri si smi eni ki ei Y ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri (pa_validate AD) Mi mdi) K.
Proof.
  intros MID J1 RAq J10 J11 Hn Hp0 Hp1 Hp2 DEFp ACCp LOC BYT LEN LB8 KONT'. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
  assert (ASTKv : L5CA.astk ar Mi (sp - 128) 12288).
  { apply (L5SAR.astk_sub ar Mi Mi sp 28672 128 12288 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia|].
    replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  unfold PECVSA.validate_fun_spec in VAL.
  apply (VAL fxi Ri Mi mdi K LBi FF' LKi Awi cri pp n (sp - 128) q l HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536.
    split; [exact ASTKv|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 12288) with (sp + (-776) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomA_push 8 0 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 3 (sp - 128 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact J10. }
  { rewrite L5K.rl11. exact J11. }
  { exact Hn. } { exact Hp0. } { exact Hp1. } { exact Hp2. } { exact DEFp. } { exact ACCp. }
  { intros a Ha. apply (PMASR1.vis_scan L ar C HI LY HIok _ FF' LKi cri Awi Mi mdi pp n HHi); [| exact Ha].
    destruct LOC as [X'|[(Bq & mq & Hin & X1 & X2)|[(X1 & X2)|(X1 & X2)]]]; [left; exact X'| right; right; exists Bq, mq; split; [exact Hin| split; [exact X1| exact X2]]| right; left| right; left].
    - unfold FS_BYTES. clear - X1 X2 F1 F2 Eotb Eop. lia.
    - unfold FS_BYTES in GFS2 |- *. clear - X1 X2 GFS1 GFS2. lia. }
  { change (PMSPA.pm_scr 0) with 12288.
    destruct LOC as [X'|[(Bq & mq & Hin & X1 & X2)|[(X1 & X2)|(X1 & X2)]]]; [left; exact X'| | |].
    - right. right. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WBi & _). pose proof (WBi _ Hin) as ((_ & _ & _ & _ & Xc & _) & _). cbn [fst snd] in Xc.
      clear - X2 Xc SLO. lia.
    - right. right. clear - X2 Eotb Eop F2 FSCEIL SLO. lia.
    - right. right. clear - X2 GFCEIL GSLO. lia. }
  { exact BASE. }
  { exact BYT. } { exact LEN. } { exact LB8. }
  intros fx8 R8 M8 model8 v RP8 FBT8 MG8 MRT8 AM8 HH8 V11 Hv HV.
  assert (AH8 : L5CA.ahpres L ar LBi FF' (sp - 128) 12288 [] Mi M8).
  { apply (PMAUAR.ahpres_of_frame_but L ar C HI LY HIok LBi FF' LKi cri Awi Mi M8 (vml_of mdi) (sp - 128) 12288 HHi);
      [clear - SPT; lia| clear - SLO; lia| clear; lia| exact FBT8| exact MG8|].
    pose proof ASTKv as (_ & _ & _ & _ & X' & _). exact X'. }
  assert (BI8 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned si eni ki) M8 model8 LKi cri Awi).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PEC.owned si eni ki) (PEC.owned si eni ki) Mi mdi LKi cri Awi M8 model8 LKi cri Awi 12288 [] BI AH8 HH8 AM8 MRT8 (incl_refl _) (incl_refl _));
      [clear; lia| clear; lia| intros rr a []| intros a _ _ rr []| intros a X'; exact X']. }
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 3, sp - 128 + 32)] sp 28672 (sp - 128) 12288 [] [] Mi M8 ltac:(rewrite app_nil_l; exact AH8) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK8.
  apply (KONT' fx8 R8 M8 model8 v RP8).
  { rewrite <- L5K.rl11. exact V11. }
  { exact Hv. } { exact HV. } { exact MG8. }
  { intros i Hi' Ni. apply FBT8. intros rr [<-|[]]. unfold L5.in_rng. cbn [fst snd]. rewrite L5.unsigned_lit by exact Hi'. change (PMSPA.pm_scr 0) with 12288. clear - Ni. lia. }
  split; [|split; [exact BI8| split; [| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  - pose proof (fun j Hj => L5SAR.cs_of_preserved Ri R8 j RP8 Hj) as R8c.
    split; [rewrite (R8c 2%nat) by inl; exact J2|]. split; [rewrite (R8c 8%nat) by inl; exact J8|]. split; [rewrite (R8c 9%nat) by inl; exact J9|].
    split; [rewrite (R8c 18%nat) by inl; exact J18|]. split; [rewrite (R8c 19%nat) by inl; exact J19|]. split; [rewrite (R8c 20%nat) by inl; exact J20|].
    split; [rewrite (R8c 21%nat) by inl; exact J21|]. split; [rewrite (R8c 22%nat) by inl; exact J22|]. split; [rewrite (R8c 26%nat) by inl; exact J26|].
    split; [rewrite (R8c 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (R8c j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (cpre_keepA LBi sp 28672 [] Mi M8 Y si smi eni ki ei EK8 PMKA.wapp_nil BRBi); [unfold LBi; apply incl_appl; apply incl_refl| unfold LBi; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP].
Qed.

Lemma call_b10 (pp n q : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 pp -> getr Ri (reg 11) = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
  0 <= pp -> (n = 0 \/ 0 < pp) -> pp + n <= 2 ^ 47 -> L5.defined Mi pp n -> PMSPA.accA Mi pp n ->
  (n = 0 \/ (exists B m, In (B, m) (PEC.owned si eni ki ++ LBX) /\ B <= pp /\ pp + n <= B + m) \/ (otb + 1 <= pp /\ pp + n <= otb + 24) \/ (F + 32 <= pp /\ pp + n <= F + 504)) ->
  (forall fx' R' M' md', regs_preserved Ri R' ->
      mem_grows Mi M' -> (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 - 12288 <= i < sp - 128) -> M' (Z_to_bv 64 i) = Mi (Z_to_bv 64 i)) ->
      amid fx' R' M' md' LKi Awi cri si smi eni ki ei Y ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri (pa_is_base10 AD) Mi mdi) K.
Proof.
  intros MID J1 RAq J10 J11 Hn Hp0 Hp1 Hp2 DEFp ACCp LOC KONT'. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
  assert (ASTKv : L5CA.astk ar Mi (sp - 128) 12288).
  { apply (L5SAR.astk_sub ar Mi Mi sp 28672 128 12288 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia|].
    replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  pose proof B10 as BX. unfold PMSPA.is_base10_spec, PMSPA.scan_spec in BX.
  apply (BX fxi Ri Mi mdi K LBi FF' LKi Awi cri pp n (sp - 128) q HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536.
    split; [exact ASTKv|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 12288) with (sp + (-776) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomA_push 8 0 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 3 (sp - 128 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact J10. }
  { rewrite L5K.rl11. exact J11. }
  { exact Hn. } { exact Hp0. } { exact Hp1. } { exact Hp2. } { exact DEFp. } { exact ACCp. }
  { intros a Ha. apply (PMASR1.vis_scan L ar C HI LY HIok _ FF' LKi cri Awi Mi mdi pp n HHi); [| exact Ha].
    destruct LOC as [X'|[(Bq & mq & Hin & X1 & X2)|[(X1 & X2)|(X1 & X2)]]]; [left; exact X'| right; right; exists Bq, mq; split; [exact Hin| split; [exact X1| exact X2]]| right; left| right; left].
    - unfold FS_BYTES. clear - X1 X2 F1 F2 Eotb Eop. lia.
    - unfold FS_BYTES in GFS2 |- *. clear - X1 X2 GFS1 GFS2. lia. }
  { change (PMSPA.pm_scr 0) with 12288.
    destruct LOC as [X'|[(Bq & mq & Hin & X1 & X2)|[(X1 & X2)|(X1 & X2)]]]; [left; exact X'| | |].
    - right. right. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WBi & _). pose proof (WBi _ Hin) as ((_ & _ & _ & _ & Xc & _) & _). cbn [fst snd] in Xc.
      clear - X2 Xc SLO. lia.
    - right. right. clear - X2 Eotb Eop F2 FSCEIL SLO. lia.
    - right. right. clear - X2 GFCEIL GSLO. lia. }
  { exact BASE. }
  intros fx8 R8 M8 model8 RP8 FBT8 MG8 MRT8 AM8 HH8.
  assert (AH8 : L5CA.ahpres L ar LBi FF' (sp - 128) 12288 [] Mi M8).
  { apply (PMAUAR.ahpres_of_frame_but L ar C HI LY HIok LBi FF' LKi cri Awi Mi M8 (vml_of mdi) (sp - 128) 12288 HHi);
      [clear - SPT; lia| clear - SLO; lia| clear; lia| exact FBT8| exact MG8|].
    pose proof ASTKv as (_ & _ & _ & _ & X' & _). exact X'. }
  assert (BI8 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned si eni ki) M8 model8 LKi cri Awi).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PEC.owned si eni ki) (PEC.owned si eni ki) Mi mdi LKi cri Awi M8 model8 LKi cri Awi 12288 [] BI AH8 HH8 AM8 MRT8 (incl_refl _) (incl_refl _));
      [clear; lia| clear; lia| intros rr a []| intros a _ _ rr []| intros a X'; exact X']. }
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 3, sp - 128 + 32)] sp 28672 (sp - 128) 12288 [] [] Mi M8 ltac:(rewrite app_nil_l; exact AH8) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK8.
  apply (KONT' fx8 R8 M8 model8 RP8).
  { exact MG8. }
  { intros i Hi' Ni. apply FBT8. intros rr [<-|[]]. unfold L5.in_rng. cbn [fst snd]. rewrite L5.unsigned_lit by exact Hi'. change (PMSPA.pm_scr 0) with 12288. clear - Ni. lia. }
  split; [|split; [exact BI8| split; [| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  - pose proof (fun j Hj => L5SAR.cs_of_preserved Ri R8 j RP8 Hj) as R8c.
    split; [rewrite (R8c 2%nat) by inl; exact J2|]. split; [rewrite (R8c 8%nat) by inl; exact J8|]. split; [rewrite (R8c 9%nat) by inl; exact J9|].
    split; [rewrite (R8c 18%nat) by inl; exact J18|]. split; [rewrite (R8c 19%nat) by inl; exact J19|]. split; [rewrite (R8c 20%nat) by inl; exact J20|].
    split; [rewrite (R8c 21%nat) by inl; exact J21|]. split; [rewrite (R8c 22%nat) by inl; exact J22|]. split; [rewrite (R8c 26%nat) by inl; exact J26|].
    split; [rewrite (R8c 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (R8c j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (cpre_keepA LBi sp 28672 [] Mi M8 Y si smi eni ki ei EK8 PMKA.wapp_nil BRBi); [unfold LBi; apply incl_appl; apply incl_refl| unfold LBi; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP].
Qed.

Lemma finish (v' : Z) (Xf : st) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fx7 : FPState) R7 M7v (pci : Z) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fx7 R7 (Z_to_bv 64 0xb44a8) M7v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) M7v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 8 + 1) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 64) ->
      M7v (Z_to_bv 64 i) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 i)) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%nat -> getr R7 (reg j) = getr Ri (reg j)) ->
  L5.u8_at RSEGS M7v (op + 8) v' -> (v' = 0 \/ v' = 1) ->
  Xf = r_value p t X -> PEC.clink p Xf (PMPK.set_more si v') smi eni ki -> s_ec Xf = s_ec Y ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID MS7 MG7 FRZ7 K7 MO0 Hv' EXF CLF ECF. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  pose proof (pfacts _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as PF0.
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold Hi in Zop, Z32, Z20, OWR, OVIS. fold MVi in Zop, Z32, Z20, OWR.
  destruct (APART op 384 0 0) as (ApF & ApSF & ApFL).
  { intros i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
    split; [clear - Eop Hi'; lia| intros Y'; clear - Eop Hi' Y'; lia]. }
  { clear; lia. }
  change (ff_bytes 3) with 512 in ApF, ApSF. change (512 / 8) with 64 in ApSF. unfold SB in ApSF.
  pose proof GFR as (GF1 & GF2 & GF3 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  fold Hi in MS7, MG7, FRZ7. fold MVi in MS7, MG7, FRZ7.

  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as STi. rewrite (L5A.aly_segs L C LYa) in STi.
  pose proof (L5A.statics_facts L C Mi LYa STi) as (_ & _ & _ & RMS & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi HHi) as (_ & _ & VIMG & _).
  assert (RMSv : L5.u64_at RSEGS MVi 1290696 1226892)
    by (apply (proj2 (L5A.u64_at_vis Hi Mi 1290696 1226892 (VIMG 1290696 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))); exact RMS).

  assert (RQ2 : getr R7 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (K7 2%nat) by inl; exact J2).
  assert (RQ8 : getr R7 (reg 8) = Z_to_bv 64 sp) by (rewrite (K7 8%nat) by inl; exact J8).
  assert (RQ9 : getr R7 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (K7 9%nat) by inl; exact J9).
  assert (RQ18 : getr R7 (reg 18) = Z_to_bv 64 (F / 8 + 2147450880)) by (rewrite (K7 18%nat) by inl; exact J18).
  assert (RQ19 : getr R7 (reg 19) = Z_to_bv 64 F) by (rewrite (K7 19%nat) by inl; exact J19).
  assert (RQ20 : getr R7 (reg 20) = Z_to_bv 64 op) by (rewrite (K7 20%nat) by inl; exact J20).
  assert (RQ21 : getr R7 (reg 21) = Z_to_bv 64 oec) by (rewrite (K7 21%nat) by inl; exact J21).
  assert (RQ22 : getr R7 (reg 22) = Z_to_bv 64 ov) by (rewrite (K7 22%nat) by inl; exact J22).
  assert (RQ26 : getr R7 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (K7 26%nat) by inl; exact J26).
  assert (RQ27 : getr R7 (reg 27) = Z_to_bv 64 F) by (rewrite (K7 27%nat) by inl; exact J27).

  assert (AG7 : forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 9) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 64) -> ~ (fl <= i < fl + 1) ->
            M7v (Z_to_bv 64 i) = MVi (Z_to_bv 64 i)).
  { intros i Hi' N1 N2 N3 N4. apply FRZ7; [exact Hi'| clear - N1; lia| exact N3]. }
  pose proof (pfacts_keep MVi M7v PF0 MG7 GL3 AG7) as PF7.
  assert (QRUN : exists (fx8 : FPState) R8 M8, mem_grows M7v M8 /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (F <= i < F + 8) -> M8 (Z_to_bv 64 i) = M7v (Z_to_bv 64 i))
            /\ msteps RSEGS (@mkst fx7 R7 (Z_to_bv 64 0xb44a8) M7v (seg_rom RSEGS)) (@mkst fx8 R8 (Z_to_bv 64 0x7c290) M8 (seg_rom RSEGS))
            /\ (forall x, In x PEARVP6.KS_arvQ -> getr R8 (reg x) = getr R7 (reg x))
            /\ getr R8 (reg 1) = Z_to_bv 64 0xb44c4 /\ getr R8 (reg 10) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R8 (reg 11) = Z_to_bv 64 64).
  { pose proof PF7 as PFX. open_vf PFX.
    pose proof (PEARVP6.arvQ_conc fx7 R7 M7v (VALU 0 0 0 0 0)) as PQ. unfold VALU in PQ. cbn beta iota in PQ.
    L5SAR.feed PQ ltac:(first [fcl | idtac]).
    destruct PQ as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & MS8 & KS8 & T1 & T10 & T11 & _).
    exists fx8, R8, M8. split; [exact MG8|]. split; [intros i Hi' N1; apply FRZ8; [exact Hi'| clear - N1; lia]|].
    split; [exact MS8|]. split; [exact KS8|]. split; [exact T1|]. split; [exact T10| exact T11]. }
  destruct QRUN as (fx8 & R8 & M8 & MG8 & FRZ8 & MS8 & KS8 & T1 & T10 & T11).

  assert (AG8 : forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 9) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 64) -> ~ (fl <= i < fl + 1) ->
            M8 (Z_to_bv 64 i) = MVi (Z_to_bv 64 i)).
  { intros i Hi' N1 N2 N3 N4. rewrite (FRZ8 i Hi' N2). exact (AG7 i Hi' N1 N2 N3 N4). }
  assert (MG08 : mem_grows MVi M8) by (intros z Hz; apply MG8; apply MG7; exact Hz).
  pose proof (pfacts_keep MVi M8 PF0 MG08 GL3 AG8) as PF8.
  assert (TRUN : exists (fx9 : FPState) R9, msteps RSEGS (L5SAR.st fx8 R8 0x7c290 M8) (L5SAR.st fx9 R9 0xb44c4 (wbytes M8 (Z_to_bv 64 (F / 8 + 2147450880)) (repeat (Z_to_bv 8 245) (Z.to_nat 64))))
            /\ (forall j, In j PNAREL.KEPT -> getr R9 (reg j) = getr R8 (reg j))).
  { pose proof PF8 as PFX. open_vf PFX.
    assert (RMS8 : L5.u64_at RSEGS M8 1290696 1226892).
    { apply (L5C.u64_at_agree RSEGS MVi M8); [intros i Hi'; apply AG8; [clear - Hi'; lia| clear - Hi' O1 OBIG; lia| clear - Hi' GF3; lia| clear - Hi' DF1; lia| clear - Hi' GL3; lia]| clear; lia| clear; lia| exact RMSv]. }
    lazymatch goal with VI : L5.img_clear M8 65536 1286144, VS : L5.u64_at RSEGS M8 1317368 2147450880, VU : L5.u32_at RSEGS M8 1317376 1, VW : L5.writable RSEGS M8 (F / 8 + 2147450880) 64 |- _ =>
      destruct (PNAREL.setshadow_f5_run fx8 R8 M8 (F / 8 + 2147450880) 64 0xb44c4 (fun i Hi => VI i ltac:(clear - Hi; lia)) VS VU RMS8 T10 T11 T1 ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear - DF1; lia) ltac:(clear - DF2; lia) VW) as (fx9 & R9 & MS9 & KP9);
      exists fx9, R9; split; [exact MS9| exact KP9] end. }
  destruct TRUN as (fx9 & R9 & MS9 & KP9).
  set (M9 := wbytes M8 (Z_to_bv 64 (F / 8 + 2147450880)) (repeat (Z_to_bv 8 245) (Z.to_nat 64))) in *.
  assert (MG9 : mem_grows M8 M9) by (apply wbytes_grows).
  assert (FRZ9 : forall a, 0 <= a < 2 ^ 64 -> ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64) -> M9 (Z_to_bv 64 a) = M8 (Z_to_bv 64 a)).
  { intros a Ha Hn. subst M9. apply AX2S.wbytes_out. rewrite repeat_length, L5.unsigned_lit by (clear - DF1 DF2; lia). clear - DF1 DF2; lia.
    rewrite repeat_length, !L5.unsigned_lit by (clear - DF1 DF2 Ha; lia). clear - Hn. lia. }
  assert (AG9 : forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 9) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 64) -> ~ (fl <= i < fl + 1) ->
            M9 (Z_to_bv 64 i) = MVi (Z_to_bv 64 i)).
  { intros i Hi' N1 N2 N3 N4. rewrite (FRZ9 i Hi' N3). exact (AG8 i Hi' N1 N2 N3 N4). }
  assert (MG09 : mem_grows MVi M9) by (intros z Hz; apply MG9; apply MG08; exact Hz).
  pose proof (pfacts_keep MVi M9 PF0 MG09 GL3 AG9) as PF9.

  assert (K9 : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%nat -> getr R9 (reg j) = getr R7 (reg j)).
  { intros j Hj. rewrite (KP9 j) by (revert j Hj; apply (L5K.incl_b _ PNAREL.KEPT); vm_compute; reflexivity).
    apply KS8. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvQ). vm_compute. reflexivity. }

  assert (RRUN : exists (fx10 : FPState) R10 M10, mem_grows M9 M10 /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (fl <= i < fl + 1) -> M10 (Z_to_bv 64 i) = M9 (Z_to_bv 64 i))
            /\ msteps RSEGS (@mkst fx9 R9 (Z_to_bv 64 0xb44c4) M9 (seg_rom RSEGS)) (@mkst fx10 R10 (Z_to_bv 64 0xb45ac) M10 (seg_rom RSEGS))
            /\ (forall x, In x PEARVP6.KS_arvR2 -> getr R10 (reg x) = getr R9 (reg x))
            /\ getr R10 (reg 1) = Z_to_bv 64 (bv_unsigned (getr R (reg 1))) /\ getr R10 (reg 2) = Z_to_bv 64 sp
            /\ getr R10 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) /\ getr R10 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9)))
            /\ getr R10 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) /\ getr R10 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19)))
            /\ getr R10 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R (reg 20))) /\ getr R10 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R (reg 21)))
            /\ getr R10 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R (reg 22))) /\ getr R10 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23)))
            /\ getr R10 (reg 24) = Z_to_bv 64 (bv_unsigned (getr R (reg 24))) /\ getr R10 (reg 25) = Z_to_bv 64 (bv_unsigned (getr R (reg 25)))
            /\ getr R10 (reg 26) = Z_to_bv 64 (bv_unsigned (getr R (reg 26))) /\ getr R10 (reg 27) = Z_to_bv 64 (bv_unsigned (getr R (reg 27)))
            /\ L5.u8_at RSEGS M10 fl 0).
  { pose proof PF9 as PFX. open_vf PFX.
    assert (Y2 : getr R9 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (K9 2%nat) by inl; exact RQ2).
    assert (Y8 : getr R9 (reg 8) = Z_to_bv 64 sp) by (rewrite (K9 8%nat) by inl; exact RQ8).
    assert (Y9 : getr R9 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (K9 9%nat) by inl; exact RQ9).
    assert (Y18 : getr R9 (reg 18) = Z_to_bv 64 (F / 8 + 2147450880)) by (rewrite (K9 18%nat) by inl; exact RQ18).
    assert (Y19 : getr R9 (reg 19) = Z_to_bv 64 F) by (rewrite (K9 19%nat) by inl; exact RQ19).
    assert (Y20 : getr R9 (reg 20) = Z_to_bv 64 op) by (rewrite (K9 20%nat) by inl; exact RQ20).
    assert (Y21 : getr R9 (reg 21) = Z_to_bv 64 oec) by (rewrite (K9 21%nat) by inl; exact RQ21).
    assert (Y22 : getr R9 (reg 22) = Z_to_bv 64 ov) by (rewrite (K9 22%nat) by inl; exact RQ22).
    assert (Y26 : getr R9 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (K9 26%nat) by inl; exact RQ26).
    assert (Y27 : getr R9 (reg 27) = Z_to_bv 64 F) by (rewrite (K9 27%nat) by inl; exact RQ27).
    pose proof (PEARVP6.arvR2_conc fx9 R9 M9 (VALU 0 0 0 0 0)) as PR. unfold VALU in PR. cbn beta iota in PR.
    L5SAR.feed PR ltac:(first [fcl | idtac]).
    destruct PR as (fx10 & R10 & M10 & MG10 & _ & FRZ10 & MS10 & KS10 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0).
    exists fx10, R10, M10. split; [exact MG10|]. split; [intros i Hi' N1; apply FRZ10; [exact Hi'| clear - N1; lia]|].
    split; [exact MS10|]. split; [exact KS10|]. repeat (split; [assumption|]). exact FL0. }
  destruct RRUN as (fx10 & R10 & M10 & MG10 & FRZ10 & MS10 & KS10 & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0).
  assert (G34 : forall j, In j [3; 4]%nat -> getr R10 (reg j) = getr Ri (reg j)).
  { intros j Hj. rewrite (KS10 j) by (revert j Hj; apply (L5K.incl_b _ PEARVP6.KS_arvR2); vm_compute; reflexivity).
    rewrite (K9 j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity).
    apply K7. revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity. }

  assert (R10ra : getr R10 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Rra, L5.unsigned_lit by (clear - Hr1 Hr2; lia); reflexivity).
  pose proof (PMK.ret_to RSEGS fx10 R10 M10 0xb45ac W_b455c r F_b455c eq_refl D_b455c R10ra Hr1 Hr2) as MSr.
  assert (MSall : msteps RSEGS (L5SAR.st fxi Ri pci MVi) (L5SAR.st fx10 R10 r M10)).
  { eapply msteps_trans; [exact MS7|]. eapply msteps_trans; [exact MS8|]. eapply msteps_trans; [exact MS9|]. eapply msteps_trans; [exact MS10| exact MSr]. }
  assert (MGall : mem_grows MVi M10) by (intros z Hz; apply MG10; apply MG09; exact Hz).
  assert (MO10 : L5.u8_at RSEGS M10 (op + 8) v').
  { apply (L5C.u8_at_agree RSEGS M7v M10); [| clear - O1; lia| clear - O1 O3; lia| exact MO0].
    intros i Hi'. rewrite FRZ10; [| clear - Hi' O1 O3; lia| clear - Hi' ApFL; lia]. rewrite FRZ9; [| clear - Hi' O1 O3; lia| clear - Hi' ApSF; lia].
    apply FRZ8; [clear - Hi' O1 O3; lia| clear - Hi' ApF; lia]. }
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
           WR (PEC.owned si eni ki) Mi mdi LKi cri Awi (fun a => op + 8 <= a < op + 9) fxi fx10 Ri pci R10 r M10 K BI).
  { intros a X'. split.
    - apply (L5SAR.fframe_client L ar (PEC.owned si eni ki ++ LBX) FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - X' Eop; lia].
    - intros O. apply (O (PMSP.o_p AD fb + 8, 8)); [unfold WR; wr_mem 0| wr_rng; clear - X' Eop; lia]. }
  { intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [X'|X']; [left; exact X'| right; exact X']. }
  { exact MSall. }
  { exact MGall. }
  { intros a Ha Nw. unfold PMAUK.WretX, PMAUK.Wret in Nw. change (ff_bytes 3) with 512 in Nw. change (512 / 8) with 64 in Nw.
    rewrite FRZ10; [| exact Ha| intros X'; apply Nw; left; right; clear - X'; lia].
    apply AG9; [exact Ha| intros X'; apply Nw; right; exact X'| intros X'; apply Nw; left; left; left; exact X'
              | intros X'; apply Nw; left; left; right; unfold SB; exact X'| intros X'; apply Nw; left; right; clear - X'; lia]. }
  { exact FL0. }
  intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict Hi Mf = M10) in VISf.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  assert (EKf : L5SAR.ek L ar LBi FF 0 0 [(op + 8, 1)] Mi Mf).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k)
             LBi LKi cri Awi Mi Mf _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) G HHi).
    - intros a X' O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X'; lia].
    - exact FZf. }
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  assert (MO0f : L5.u8_at RSEGS Mf (op + 8) v').
  { apply (proj1 (L5A.u8_at_vis Hi Mf (op + 8) v' (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). rewrite VISf. exact MO10. }
  assert (WAPP8 : PMKA.wapp [(op + 8, 1)]).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG; lia. }
  assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
  { intros a n X3 i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi' Hr X3. lia. }
  assert (OUTB8 : forall q' m, In (q', m) LBi -> forall i, q' <= i < q' + m -> L5.outside [(op + 8, 1)] i).
  { intros q' m Hq i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Hr Z'; lia. }
  assert (Iq : In (PM.sr_qc (PM.p_src si), PM.CHUNK) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (Ib : In (PM.p_b si, 32 * 2 ^ PM.p_k si) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  apply (KONT fx10 R10 Mf modelf LKi Awi (PMPK.set_more si v') smi eni ki ei cri).
  - apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite E2; exact (eq_sym Rsp) | rewrite G34 by inl; apply J34; inl
        | rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned | rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned
        | rewrite E20; apply Z_to_bv_bv_unsigned | rewrite E21; apply Z_to_bv_bv_unsigned | rewrite E22; apply Z_to_bv_bv_unsigned | rewrite E23; apply Z_to_bv_bv_unsigned
        | rewrite E24; apply Z_to_bv_bv_unsigned | rewrite E25; apply Z_to_bv_bv_unsigned | rewrite E26; apply Z_to_bv_bv_unsigned | rewrite E27; apply Z_to_bv_bv_unsigned ] |]).
    destruct Hj.
  - destruct (BRBi _ Iq) as (Xq1 & Xq2). destruct (BRBi _ Ib) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2. unfold PM.CHUNK in Xq2.
    rewrite <- EXF.
    apply (cpre_stepA LBi 0 0 [(op + 8, 1)] Mi Mf Y si smi eni ki ei Xf (PMPK.set_more si v') ei EKf WAPP8 BRBi).
    + unfold LBi. apply incl_appl. apply incl_refl.
    + unfold LBi. apply incl_appr. exact INCS.
    + intros i Hi' Ni _. apply (OUT8 i 1); clear - Hi' Ni; lia.
    + intros q' m Hq. exact (OUTB8 q' m Hq).
    + reflexivity. + reflexivity. + reflexivity.
    + apply (PMAPAR.parser_more_updA Mi Mf op ois si v' PA).
      * clear - O1; lia.
      * clear - O1 O3; lia.
      * apply (PMKA.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
      * apply (PMKA.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
      * exact (PMKA.agsh_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB op 384 AOP).
      * pose proof PA as (_ & PDi & _). apply (L5.defined_grows Mi Mf _ _ MGf PDi).
      * exact MO0f.
      * exact Hv'.
      * exact Xq1.
      * unfold PM.CHUNK. clear - Xq2; lia.
      * apply (PMKA.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Iq). apply OUTB8. exact Iq.
      * exact Xb1.
      * clear - Xb2; lia.
      * apply (PMKA.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Ib). apply OUTB8. exact Ib.
      * intros c0 n0 p0 E0. assert (Ip : In (p0, c0) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
        apply (PMKA.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Ip). apply OUTB8. exact Ip.
    + change (PMSTA.base_okA RSEGS PMA.AD Mf). apply (PMASK.base_keep L ar C LY LBi FF 0 0 [(op + 8, 1)] Mi Mf EKf); [| exact BASE]. intros a Ha. apply (OUT8 a 1); clear - Ha O1; lia.
    + apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBi FF 0 0 [(op + 8, 1)] Mi Mf EKf ei PECSA.addrs_wf_A); [| exact ERR].
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
    + exact CP.
  - unfold PMPK.set_more. cbn [PM.p_src]. exact ST.
  - exact EIMP.
  - exact AHf.
  - unfold PMSP.credit_keep, PMPK.set_more, PECA.pot_allA, PEC.credit_add, PM.pot_parser in CK |- *. cbn [PM.p_k PM.p_tb PM.p_tg fst snd] in CK |- *. exact CK.
  - exact MRTf.
  - exact INCLi.
  - exact INCAi.
  - exact AMf.
  - unfold PMPK.set_more. change (PEC.owned (PM.PST v' (PM.p_done si) (PM.p_depth si) (PM.p_src si) (PM.p_tb si) (PM.p_tg si) (PM.p_b si) (PM.p_k si) (PM.p_stk si)) eni ki)
      with (PEC.owned si eni ki). exact HHf.
Qed.

Lemma clink_fail Y0 s0 sm0 en0 k0 : PEC.clink p Y0 s0 sm0 en0 k0 -> PEC.clink p (w_more false Y0) (PMPK.set_more s0 0) sm0 en0 k0.
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  unfold PEC.clink, PMPK.set_more. destruct Y0; cbn in *.
  split; [reflexivity|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
  split; [intros X' _; discriminate X'|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
Qed.
Lemma clink_same Y0 s0 sm0 en0 k0 : PEC.clink p Y0 s0 sm0 en0 k0 -> PEC.clink p Y0 (PMPK.set_more s0 (PM.p_more s0)) sm0 en0 k0.
Proof. intros CL0. destruct s0. unfold PMPK.set_more. cbn. exact CL0. Qed.
Lemma more_01 Y0 s0 sm0 en0 k0 : PEC.clink p Y0 s0 sm0 en0 k0 -> PM.p_more s0 = 0 \/ PM.p_more s0 = 1.
Proof. intros (L1 & _). rewrite L1. unfold PEC.b2z. destruct (s_more Y0); [right| left]; reflexivity. Qed.

Lemma tail_J fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fx7 : FPState) R7 M7v (pci : Z) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fx7 R7 (Z_to_bv 64 0xb4490) M7v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) M7v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 8 + 1) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 64) ->
      M7v (Z_to_bv 64 i) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 i)) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%nat -> getr R7 (reg j) = getr Ri (reg j)) ->
  L5.u8_at RSEGS M7v (op + 8) (PM.p_more si) ->
  r_value p t X = PECRVD.fin Y ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID MS7 MG7 FRZ7 K7 MO7 RV. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  pose proof (pfacts _ _ _ _ _ _ _ _ _ _ _ _ _ MID) as PF0.
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
  destruct (APART op 384 0 0) as (ApF & ApSF & ApFL).
  { intros i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
    split; [clear - Eop Hi'; lia| intros Y'; clear - Eop Hi' Y'; lia]. }
  { clear; lia. }
  destruct (APART oec 16 0 0) as (AeF & AeSF & AeFL).
  { intros i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
    split; [clear - Eoec Hi'; lia| intros Y'; clear - Eoec Hi' Y'; lia]. }
  { clear; lia. }
  change (ff_bytes 3) with 512 in ApF, ApSF, AeF, AeSF. change (512 / 8) with 64 in ApSF, AeSF. unfold SB in ApSF, AeSF.
  pose proof GFR as (GF1 & GF2 & GF3 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  fold Hi in MS7, MG7, FRZ7. fold MVi in MS7, MG7, FRZ7.
  assert (AG7 : forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 9) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 64) -> ~ (fl <= i < fl + 1) ->
            M7v (Z_to_bv 64 i) = MVi (Z_to_bv 64 i)).
  { intros i Hi' N1 N2 N3 N4. apply FRZ7; [exact Hi'| clear - N1; lia| exact N3]. }
  pose proof (pfacts_keep MVi M7v PF0 MG7 GL3 AG7) as PF7.
  assert (RQ2 : getr R7 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (K7 2%nat) by inl; exact J2).
  assert (RQ8 : getr R7 (reg 8) = Z_to_bv 64 sp) by (rewrite (K7 8%nat) by inl; exact J8).
  assert (RQ9 : getr R7 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (K7 9%nat) by inl; exact J9).
  assert (RQ18 : getr R7 (reg 18) = Z_to_bv 64 (F / 8 + 2147450880)) by (rewrite (K7 18%nat) by inl; exact J18).
  assert (RQ19 : getr R7 (reg 19) = Z_to_bv 64 F) by (rewrite (K7 19%nat) by inl; exact J19).
  assert (RQ20 : getr R7 (reg 20) = Z_to_bv 64 op) by (rewrite (K7 20%nat) by inl; exact J20).
  assert (RQ21 : getr R7 (reg 21) = Z_to_bv 64 oec) by (rewrite (K7 21%nat) by inl; exact J21).
  assert (RQ22 : getr R7 (reg 22) = Z_to_bv 64 ov) by (rewrite (K7 22%nat) by inl; exact J22).
  assert (RQ26 : getr R7 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (K7 26%nat) by inl; exact J26).
  assert (RQ27 : getr R7 (reg 27) = Z_to_bv 64 F) by (rewrite (K7 27%nat) by inl; exact J27).
  assert (AGE : forall i, oec <= i < oec + 4 -> M7v (Z_to_bv 64 i) = MVi (Z_to_bv 64 i)).
  { intros i Hi'. apply FRZ7; [clear - Hi' O1 O3 Eop Eoec; lia| clear - Hi' Eop Eoec; lia| clear - Hi' AeSF; lia]. }
  destruct (s_ec Y) eqn:EY.
  -
    destruct (ec_vis1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID EY) as (v & Hv & ECU). fold Hi in ECU. fold MVi in ECU.
    assert (ECU7 : L5.u32_at RSEGS M7v oec v) by (apply (PMF.u32_at_agree RSEGS MVi M7v); [exact AGE| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact ECU]).
    assert (JRUN : exists (fx8 : FPState) R8 M8, mem_grows M7v M8 /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 8 + 1) -> M8 (Z_to_bv 64 i) = M7v (Z_to_bv 64 i))
              /\ msteps RSEGS (@mkst fx7 R7 (Z_to_bv 64 0xb4490) M7v (seg_rom RSEGS)) (@mkst fx8 R8 (Z_to_bv 64 0xb44a8) M8 (seg_rom RSEGS))
              /\ (forall x, In x PEARVP6.KS_arvJe -> getr R8 (reg x) = getr R7 (reg x)) /\ L5.u8_at RSEGS M8 (op + 8) 0).
    { pose proof PF7 as PFX. open_vf PFX. assert (Hv' : 1 <= v <= 64) by exact Hv. assert (Bv : 0 <= v < 2 ^ 64) by (clear - Hv; lia).
      pose proof (PEARVP6.arvJe_conc fx7 R7 M7v (VALU 0 0 0 v 0)) as PJ. unfold VALU in PJ. cbn beta iota in PJ.
      L5SAR.feed PJ ltac:(first [fcl | idtac]).
      destruct PJ as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & MS8 & KS8 & _ & _ & MO8).
      exists fx8, R8, M8. split; [exact MG8|]. split; [exact FRZ8|]. split; [exact MS8|]. split; [exact KS8| exact MO8]. }
    destruct JRUN as (fx8 & R8 & M8 & MG8 & FRZ8 & MS8 & KS8 & MO8).
    apply (finish 0 (w_more false Y) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y fx8 R8 M8 pci MID).
    + exact (msteps_trans _ _ _ _ MS7 MS8).
    + intros z Hz. apply MG8. apply MG7. exact Hz.
    + intros i Hi' N1 N2. rewrite (FRZ8 i Hi' N1). exact (FRZ7 i Hi' N1 N2).
    + intros j Hj. rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b _ PEARVP6.KS_arvJe); vm_compute; reflexivity). exact (K7 j Hj).
    + exact MO8.
    + left; reflexivity.
    + rewrite RV. symmetry. exact (PECRVD.fin_true Y EY).
    + exact (clink_fail _ _ _ _ _ CL).
    + cbn [s_ec w_more]. destruct Y; reflexivity.
  -
    pose proof (ec_vis0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID EY) as ECU. fold Hi in ECU. fold MVi in ECU.
    assert (ECU7 : L5.u32_at RSEGS M7v oec 0) by (apply (PMF.u32_at_agree RSEGS MVi M7v); [exact AGE| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact ECU]).
    assert (JRUN : exists (fx8 : FPState) R8 M8, mem_grows M7v M8 /\ (forall i, 0 <= i < 2 ^ 64 -> M8 (Z_to_bv 64 i) = M7v (Z_to_bv 64 i))
              /\ msteps RSEGS (@mkst fx7 R7 (Z_to_bv 64 0xb4490) M7v (seg_rom RSEGS)) (@mkst fx8 R8 (Z_to_bv 64 0xb44a8) M8 (seg_rom RSEGS))
              /\ (forall x, In x PEARVP6.KS_arvJ0 -> getr R8 (reg x) = getr R7 (reg x))).
    { pose proof PF7 as PFX. open_vf PFX.
      pose proof (PEARVP6.arvJ0_conc fx7 R7 M7v (VALU 0 0 0 0 0)) as PJ. unfold VALU in PJ. cbn beta iota in PJ.
      L5SAR.feed PJ ltac:(first [fcl | idtac]).
      destruct PJ as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & MS8 & KS8 & _).
      exists fx8, R8, M8. split; [exact MG8|]. split; [exact FRZ8|]. split; [exact MS8| exact KS8]. }
    destruct JRUN as (fx8 & R8 & M8 & MG8 & FRZ8 & MS8 & KS8).
    apply (finish (PM.p_more si) Y fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y fx8 R8 M8 pci MID).
    + exact (msteps_trans _ _ _ _ MS7 MS8).
    + intros z Hz. apply MG8. apply MG7. exact Hz.
    + intros i Hi' N1 N2. rewrite (FRZ8 i Hi'). exact (FRZ7 i Hi' N1 N2).
    + intros j Hj. rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b _ PEARVP6.KS_arvJ0); vm_compute; reflexivity). exact (K7 j Hj).
    + apply (L5C.u8_at_agree RSEGS M7v M8); [intros i Hi'; apply FRZ8; clear - Hi' O1 O3; lia| clear - O1; lia| clear - O1 O3; lia| exact MO7].
    + exact (more_01 _ _ _ _ _ CL).
    + rewrite RV. symmetry. exact (PECRVD.fin_false Y EY).
    + exact (clink_same _ _ _ _ _ CL).
    + reflexivity.
Qed.

Lemma more_vis fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> L5.u8_at RSEGS (mrestrict (ahid Awi mdi) Mi) (op + 8) (PM.p_more si).
Proof.
  intros MID. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 3, sp - 128 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  pose proof PA as (_ & _ & _ & P8 & _).
  apply (proj2 (L5A.u8_at_vis _ Mi (op + 8) (PM.p_more si) (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). exact P8.
Qed.

Lemma entry_model : s_more X = true /\ s_done X = false /\ 0 <= s_pos X <= blen p /\ PECSPA.mp_enc p X /\ s_bad X = false.
Proof.
  destruct MP as ((PRE & MORE) & DONE & HALT & DEP & EST & STKLE). pose proof PRE as (BOK & PPOS & PLH & PBAD & PED & PEOK).
  split; [exact MORE|]. split; [exact DONE|]. split; [exact PPOS|]. split; [| exact PBAD].
  unfold PECSPA.mp_enc. split; [exact PLH|]. split; [exact PBAD|]. split; [exact PEOK|]. rewrite PED. exact DEP.
Qed.

Lemma count_eq d kk : 0 <= d <= kk -> kk < 2 ^ 62 -> ((d - kk) mod 2 ^ 64) < 1 -> d = kk.
Proof.
  intros H1 H2 H3. destruct (Z.eq_dec d kk) as [E|N]; [exact E|]. exfalso.
  replace (d - kk) with ((d - kk + 2 ^ 64) + (-1) * 2 ^ 64) in H3 by lia. rewrite Z.mod_add in H3 by lia. rewrite Z.mod_small in H3 by lia. lia.
Qed.
Lemma count_ne d kk : 0 <= d <= kk -> kk < 2 ^ 62 -> 1 <= ((d - kk) mod 2 ^ 64) -> d < kk.
Proof.
  intros H1 H2 H3. destruct (Z.eq_dec d kk) as [E|N]; [|lia]. exfalso. subst d. rewrite Z.sub_diag, Z.mod_0_l in H3 by lia. lia.
Qed.

Lemma amid_relink fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y Y' :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> PEC.clink p Y' si smi eni ki -> s_ec Y' = s_ec Y ->
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y'.
Proof.
  intros MID CL' EC'. pose proof MID as (RG & BI & CP & ST & EIMP & CK).
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  split; [exact RG|]. split; [exact BI|]. split; [| split; [exact ST| split; [exact EIMP| exact CK]]].
  split; [exact PA|]. split; [exact IA|]. split; [exact EA|]. split; [exact VREF|]. split; [exact SKA|]. split; [exact BASE|]. split; [exact ERR|].
  split; [exact TBOK|]. split; [exact CONT|]. split; [exact CL'|]. rewrite EC'. split; [exact ECS|]. split; [exact ECI| exact ACC].
Qed.

Lemma iwA v : PECSPA.int64_width v = PECS.int64_width v. Proof. reflexivity. Qed.
Lemma uwA v : PECSPA.uint64_width v = PECS.uint64_width v. Proof. reflexivity. Qed.

Lemma arm_N fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 78 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTN_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _).
  apply (tail_J fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X fx7 R7 M7v 0xb3aec MID MS7 MG7).
  - intros i Hi' _ _. apply FRZ7. exact Hi'.
  - intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTN). vm_compute. reflexivity.
  - assert (E7 : M7v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). rewrite E7. exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite Et. exact (PECRVD.rv_N p X).
Qed.

Lemma arm_Z fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 90 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTZ_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & _ & Y13 & Y14).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pe_null EE) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTZ). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD MID1 Y1 Y10 Y13 Et.
  pose proof VN as SPEC. unfold PECSA.v_null_spec, PECSPA.v_null_spec in SPEC.
  apply (call_slot unit (pe_null EE) (PECSPA.args_t3 AD) (fun _ => PECSPA.mp_enc) (fun _ _ X0 => e_scalar 1 1 X0) SPEC tt 0xb3e8c fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1
           ltac:(split; [clear; lia| reflexivity]) Y10).
  { unfold PECSPA.args_t3. rewrite L5K.rl13. exact Y13. }
  { exact MPE. }
  { rewrite PECRVD.e_scalar_bad. exact XBAD. }
  { rewrite PECRVD.e_scalar_hi. pose proof HB as HB'. rewrite (PECRVD.rv_ZTF p t X ltac:(rewrite Et; clear; lia)) in HB'.
    unfold PECRVD.fin in HB'. rewrite PECRVD.w_more_same in HB' by (rewrite PECRVD.e_scalar_more; exact MORE).
    destruct (s_ec (e_scalar 1 1 X)); cbn [s_hi w_more] in HB'; rewrite ?PECRVD.e_scalar_hi in HB'; [destruct X; cbn in HB' |- *; exact HB'| exact HB']. }
  intros fx4 R4 M4 md4 LK4 Aw4 en4 k4 e4 cr4 RP4 MID4 KP4.
  keep_only MORE DONE PPOS Et MID4. rename MID4 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP5.arvZZ_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & MO7).
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 si smi en4 k4 e4 (e_scalar 1 1 X) fx7 R7 M7v 0xb3e8c MID MS7 MG7).
  - intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1].
  - intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZZ). vm_compute. reflexivity.
  - replace (PM.p_more si) with 1; [exact MO7|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
    rewrite Lmore. rewrite PECRVD.e_scalar_more, MORE. reflexivity.
  - rewrite (PECRVD.rv_ZTF p t X ltac:(rewrite Et; clear; lia)). unfold PECRVD.fin. rewrite PECRVD.w_more_same by (rewrite PECRVD.e_scalar_more; exact MORE). reflexivity.
Qed.

Lemma arm_T fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 84 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTT_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & _ & Y13 & Y14 & _).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pe_bool EE) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTT). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD MID1 Y1 Y10 Y11 Y14 Et.
  pose proof VB as SPEC. unfold PECSA.v_bool_spec, PECSPA.v_bool_spec in SPEC.
  apply (call_slot bool (pe_bool EE) (PECSPA.args_bool AD) (fun _ => PECSPA.mp_enc) (fun _ _ X0 => e_scalar 1 1 X0) SPEC true 0xb3f08 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1
           ltac:(split; [clear; lia| reflexivity]) Y10).
  { unfold PECSPA.args_bool. rewrite L5K.rl11, L5K.rl14. split; [exact Y11| exact Y14]. }
  { exact MPE. }
  { rewrite PECRVD.e_scalar_bad. exact XBAD. }
  { rewrite PECRVD.e_scalar_hi. pose proof HB as HB'. rewrite (PECRVD.rv_ZTF p t X ltac:(rewrite Et; clear; lia)) in HB'.
    unfold PECRVD.fin in HB'. rewrite PECRVD.w_more_same in HB' by (rewrite PECRVD.e_scalar_more; exact MORE).
    destruct (s_ec (e_scalar 1 1 X)); cbn [s_hi w_more] in HB'; rewrite ?PECRVD.e_scalar_hi in HB'; [destruct X; cbn in HB' |- *; exact HB'| exact HB']. }
  intros fx4 R4 M4 md4 LK4 Aw4 en4 k4 e4 cr4 RP4 MID4 KP4.
  keep_only MORE DONE PPOS Et MID4. rename MID4 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP5.arvZT_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & MO7).
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 si smi en4 k4 e4 (e_scalar 1 1 X) fx7 R7 M7v 0xb3f08 MID MS7 MG7).
  - intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1].
  - intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZT). vm_compute. reflexivity.
  - replace (PM.p_more si) with 1; [exact MO7|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
    rewrite Lmore. rewrite PECRVD.e_scalar_more, MORE. reflexivity.
  - rewrite (PECRVD.rv_ZTF p t X ltac:(rewrite Et; clear; lia)). unfold PECRVD.fin. rewrite PECRVD.w_more_same by (rewrite PECRVD.e_scalar_more; exact MORE). reflexivity.
Qed.

Lemma arm_F fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 70 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTF_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & _ & Y13 & Y14 & _).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pe_bool EE) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTF). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD MID1 Y1 Y10 Y11 Y14 Et.
  pose proof VB as SPEC. unfold PECSA.v_bool_spec, PECSPA.v_bool_spec in SPEC.
  apply (call_slot bool (pe_bool EE) (PECSPA.args_bool AD) (fun _ => PECSPA.mp_enc) (fun _ _ X0 => e_scalar 1 1 X0) SPEC false 0xb3e18 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1
           ltac:(split; [clear; lia| reflexivity]) Y10).
  { unfold PECSPA.args_bool. rewrite L5K.rl11, L5K.rl14. split; [exact Y11| exact Y14]. }
  { exact MPE. }
  { rewrite PECRVD.e_scalar_bad. exact XBAD. }
  { rewrite PECRVD.e_scalar_hi. pose proof HB as HB'. rewrite (PECRVD.rv_ZTF p t X ltac:(rewrite Et; clear; lia)) in HB'.
    unfold PECRVD.fin in HB'. rewrite PECRVD.w_more_same in HB' by (rewrite PECRVD.e_scalar_more; exact MORE).
    destruct (s_ec (e_scalar 1 1 X)); cbn [s_hi w_more] in HB'; rewrite ?PECRVD.e_scalar_hi in HB'; [destruct X; cbn in HB' |- *; exact HB'| exact HB']. }
  intros fx4 R4 M4 md4 LK4 Aw4 en4 k4 e4 cr4 RP4 MID4 KP4.
  keep_only MORE DONE PPOS Et MID4. rename MID4 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP5.arvZF_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & MO7).
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 si smi en4 k4 e4 (e_scalar 1 1 X) fx7 R7 M7v 0xb3e18 MID MS7 MG7).
  - intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1].
  - intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZF). vm_compute. reflexivity.
  - replace (PM.p_more si) with 1; [exact MO7|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
    rewrite Lmore. rewrite PECRVD.e_scalar_more, MORE. reflexivity.
  - rewrite (PECRVD.rv_ZTF p t X ltac:(rewrite Et; clear; lia)). unfold PECRVD.fin. rewrite PECRVD.w_more_same by (rewrite PECRVD.e_scalar_more; exact MORE). reflexivity.
Qed.

Lemma arm_A fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 91 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTA_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & Y12).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_begin_array AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTA). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD MID1 Y1 Y10 Y11 Y12 Et.
  assert (RVX : r_value p t X = PECRVD.fin (r_begin p false X)) by (rewrite Et; reflexivity).
  pose proof BA as SPEC. unfold PECSA.begin_array_spec in SPEC.
  apply (call_crun unit (pa_begin_array AD) (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_begin p0 false X0) SPEC tt 0xb4118 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact MP. }
  { pose proof NB as NB'. rewrite RVX in NB'. unfold PECRVD.fin in NB'. destruct (s_ec (r_begin p false X)); [destruct (r_begin p false X); exact NB'| exact NB']. }
  { pose proof HB as HB'. rewrite RVX in HB'. unfold PECRVD.fin in HB'. destruct (s_ec (r_begin p false X)); [destruct (r_begin p false X); exact HB'| exact HB']. }
  intros fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en4 k4 e4 RP4 MID4 FSH4 FDK4.
  keep_only Et RVX MID4. rename MID4 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP5.arvKA_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7).
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en4 k4 e4 (r_begin p false X) fx7 R7 M7v 0xb4118 MID MS7 MG7).
  - intros i Hi' _ _. apply FRZ7. exact Hi'.
  - intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvKA). vm_compute. reflexivity.
  - assert (E7 : M7v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). rewrite E7. exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - exact RVX.
Qed.

Lemma arm_O fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 123 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTO_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & Y12).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_begin_object AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTO). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD MID1 Y1 Y10 Y11 Y12 Et.
  assert (RVX : r_value p t X = PECRVD.fin (r_begin p true X)) by (rewrite Et; reflexivity).
  pose proof BO as SPEC. unfold PECSA.begin_object_spec in SPEC.
  apply (call_crun unit (pa_begin_object AD) (PECSPA.args3 AD) PECSPA.mp_run (fun _ p0 X0 => r_begin p0 true X0) SPEC tt 0xb3c6c fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1
           ltac:(split; [clear; lia| reflexivity])).
  { unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10| split; [exact Y11| exact Y12]]. }
  { exact MP. }
  { pose proof NB as NB'. rewrite RVX in NB'. unfold PECRVD.fin in NB'. destruct (s_ec (r_begin p true X)); [destruct (r_begin p true X); exact NB'| exact NB']. }
  { pose proof HB as HB'. rewrite RVX in HB'. unfold PECRVD.fin in HB'. destruct (s_ec (r_begin p true X)); [destruct (r_begin p true X); exact HB'| exact HB']. }
  intros fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en4 k4 e4 RP4 MID4 FSH4 FDK4.
  keep_only Et RVX MID4. rename MID4 into MID.
  entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP5.arvKO_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7).
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en4 k4 e4 (r_begin p true X) fx7 R7 M7v 0xb3c6c MID MS7 MG7).
  - intros i Hi' _ _. apply FRZ7. exact Hi'.
  - intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvKO). vm_compute. reflexivity.
  - assert (E7 : M7v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). rewrite E7. exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - exact RVX.
Qed.

Lemma unk_X69 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 69 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX69_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX69). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X71 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 71 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX71_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX71). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X74 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 74 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX74_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX74). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X75 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 75 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX75_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX75). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X77 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 77 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX77_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX77). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X79 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 79 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX79_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX79). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X80 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 80 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX80_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX80). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X81 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 81 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX81_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX81). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X82 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 82 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX82_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX82). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X86 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 86 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX86_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX86). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X87 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 87 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX87_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX87). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X88 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 88 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX88_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX88). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_X89 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 89 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP2.arvX89_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvX89). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_Y0 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> 0 <= t <= 66 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP2.arvY0_conc fxi Ri t 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvY0). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_Y92 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> 92 <= t <= 99 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP2.arvY92_conc fxi Ri t 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvY92). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_Y101 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> 101 <= t <= 104 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP2.arvY101_conc fxi Ri t 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvY101). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_Y106 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> 106 <= t <= 107 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP2.arvY106_conc fxi Ri t 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvY106). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_Y109 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> 109 <= t <= 122 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP2.arvY109_conc fxi Ri t 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvY109). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma unk_Y124 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> 124 <= t <= 255 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et NM. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia). entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP2.arvY124_conc fxi Ri t 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Et; lia]).
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_make_ec AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP2.KS_arvY124). vm_compute. reflexivity. }
  keep_only NM MID1 Y1 Y10 Y11.
  apply (call_mkec 0xb4490 6 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID1 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true (w_ec true X) fx4 R4 (mrestrict (ahid Aw4 md4) M4) 0xb4490 MID (mst_refl _ _) (mem_grows_refl _)).
  - intros i _ _ _. reflexivity.
  - intros j _. reflexivity.
  - exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - rewrite (PECRVD.rv_unknown p t X NM). unfold PECRVD.fin. cbn [s_ec w_ec]. destruct X; reflexivity.
Qed.

Lemma arm_unknown fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> PECRVD.is_marker t = false ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 NM.
  destruct (PECRVD.unknown_cases t Ht NM) as [U|[U|[U|[U|[U|[U|U]]]]]].
  - cbn [In] in U.
    repeat (destruct U as [U|U]; [symmetry in U; first [exact (unk_X69 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X71 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X74 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X75 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X77 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X79 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X80 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X81 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X82 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X86 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X87 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X88 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM)
      | exact (unk_X89 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM) ] |]).
    destruct U.
  - exact (unk_Y0 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM).
  - exact (unk_Y92 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM).
  - exact (unk_Y101 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM).
  - exact (unk_Y106 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM).
  - exact (unk_Y109 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM).
  - exact (unk_Y124 _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 U NM).
Qed.

Lemma arm_i fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 105 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTi_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & Y12 & Y23 & Y24 & SH1).
  apply (amid_pieceFW fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X fx1 R1 0xb3aec (pa_src_read AD) M1v (fun a => F / 8 + 2147450880 + 4 <= a < F / 8 + 2147450880 + 4 + 1) MID MS1 MG1).
  { intros a Ha Na. apply FRZ1; [exact Ha| revert Na; clear; intros Na; unfold SB in *; intros X'; apply Na; lia]. }
  { intros a X'. unfold SB. right. clear - X'; lia. }
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTi). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et Y1 Y10 Y11 Y12 Y23 Y24 SH1.
  intros M1 md1 VIS1 HID1 MGM1 FR1w MID.
  apply (call_read (F + 32) 1 0xb3bb8 4 1 fx1 R1 M1 md1 LKi Awi cri si smi eni ki ei X MID MORE DONE PPOS Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(rewrite HID1, VIS1; replace (F / 8 + 2147450880 + 4) with (F / 8 + 2147450884) by (clear; lia); exact SH1) ltac:(right; clear; lia)).
  keep_only MORE DONE PPOS MPE XBAD Et Y23 Y24.
  intros fxb Rb Mb mdb LKb Awb srcb smb d RP2 Z10 Hd SHORT LE BYT SHB2 MID.
  assert (S23 : getr Rb (reg 23) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved _ Rb 23 RP2) by inl; exact Y23).
  assert (S24 : getr Rb (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved _ Rb 24 RP2) by inl; exact Y24).
  assert (Hd64 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  entry_facts. frame_facts. piece_ctx MID.
  destruct (Z.eq_dec d 1) as [Ed|Nd].
  -
    subst d.
    assert (FD : L5.defined MVi (F + 32) 8) by (lazymatch goal with H : L5.defined MVi F 512 |- _ => apply (L5.defined_sub MVi F 512); [exact H| clear; lia| clear; lia] end).
    pose proof GFR as (GF1 & GF2 & GF3 & _).
    destruct (PMCG.u64_of_defined RSEGS MVi (F + 32) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) FD) as (x & Hx & CX).
    pz PEARVP3.arviV_conc fxb Rb 0 0 0 0 x as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hx; lia]).
    destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10b & Z11 & _ & _ & Z14 & _).
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb3bb8 R3 (pe_int64 EE) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arviV). vm_compute. reflexivity. }
    lazymatch type of Z11 with getr _ _ = AX2.edenot ?EEv _ => destruct (PECRVW.wid_sext8 EEv (AX2.EVar 50)) as (v & Hv & Ev) end. rewrite Ev in Z11.
    keep_only MORE DONE PPOS MPE XBAD Et LE MID3 Z1 Z10b Z11 Z14 Hv. rename MID3 into MID.
    pose proof VI as SPEC. unfold PECSA.v_int64_spec, PECSPA.v_int64_spec in SPEC.
    apply (call_slot Z (pe_int64 EE) (PECSPA.args_i64 AD) (fun _ => PECSPA.mp_enc) (fun v0 _ X0 => e_scalar (PECSPA.int64_width v0) (PECSPA.int64_width v0) X0) SPEC v 0xb3c08 fx3 R3 Mb md3 LKb Awb cri
             (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b).
    { unfold PECSPA.args_i64. rewrite L5K.rl11, L5K.rl14. split; [clear - Hv; lia|]. split; [exact Z11| exact Z14]. }
    { unfold PECSPA.mp_enc in MPE |- *. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. exact MPE. }
    { rewrite PECRVD.e_scalar_bad. cbn [s_bad w_pos]. exact XBAD. }
    { rewrite PECRVD.e_scalar_hi. cbn [s_hi w_pos]. pose proof HB as HB'. rewrite Et, PECRVD.rv_i, (PECRVD.num_arm_ok p 1 2 2 X LE) in HB'.
      unfold PECRVD.fin in HB'. rewrite PECRVD.w_more_same in HB' by (rewrite PECRVD.e_scalar_more; exact MORE).
      assert (HB2 : PESKA.spa_hb P (s_hi X + 2)).
      { destruct (s_ec (e_scalar 2 2 (w_pos (s_pos X + 1) X))); cbn [s_hi w_more] in HB'; rewrite PECRVD.e_scalar_hi in HB'; exact HB'. }
      apply (PESKA.spao_hb_mono L P PO _ _ HB2). pose proof (PECRVD.iw8 v Hv) as IW. rewrite <- (iwA v) in IW. clear - IW; lia. }
    intros fx4 R4 M4 md4 LK4 Aw4 en4 k4 e4 cr4 RP4 MID4 KP4.
    keep_only MORE DONE PPOS Et LE Hv MID4. rename MID4 into MID.
    assert (MIDr : amid fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 2 2 (w_pos (s_pos X + 1) X))).
    { apply (amid_relink _ _ _ _ _ _ _ _ _ _ _ _ _ _ MID); [| rewrite !PECRVD.e_scalar_ec; reflexivity].
      pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      revert CLm. apply PECRVD.clink_scalar_widen. pose proof (PECRVD.iw8 v Hv) as IW. rewrite <- (iwA v) in IW. clear - IW; lia. }
    clear MID. rename MIDr into MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP5.arvZi_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & _ & MO7).
    apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 2 2 (w_pos (s_pos X + 1) X)) fx7 R7 M7v 0xb3c08 MID MS7 MG7).
    + intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZi). vm_compute. reflexivity.
    + replace (PM.p_more (PMSPA.with_src si srcb)) with 1; [exact MO7|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
      rewrite Lmore. rewrite PECRVD.e_scalar_more. cbn [s_more w_pos]. rewrite MORE. reflexivity.
    + rewrite Et, PECRVD.rv_i, (PECRVD.num_arm_ok p 1 2 2 X LE). unfold PECRVD.fin. rewrite PECRVD.w_more_same by (rewrite PECRVD.e_scalar_more; exact MORE). reflexivity.
  -
    assert (Hd' : 0 <= d <= 0) by (clear - Hd Nd; lia).
    pz PEARVP3.arviN_conc fxb Rb 0 0 d 0 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hd'; lia]).
    destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10b & Z11).
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb3bb8 R3 (pa_make_ec AD) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arviN). vm_compute. reflexivity. }
    keep_only Et Hd Nd SHORT MID3 Z1 Z10b Z11. rename MID3 into MID.
    apply (call_mkec 0xb4700 1 fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b Z11 ltac:(clear; lia)).
    clear MID. intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP6.arvEi_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & MO7).
    apply (finish 0 (r_fail X) fx4 R4 M4 md4 LK4 Aw4 cri (PMSPA.with_src si srcb) smb eni ki true _ fx7 R7 M7v 0xb4700 MID MS7 MG7).
    + intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvEi). vm_compute. reflexivity.
    + exact MO7.
    + left; reflexivity.
    + rewrite Et, PECRVD.rv_i. symmetry. apply (PECRVD.num_arm_short p 1 2 2 X). clear - SHORT Nd Hd; lia.
    + pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      apply (PECRVD.clink_but_pos p (r_fail X) (w_more false (w_ec true (w_pos (s_pos X + d) X)))); [reflexivity| | exact (clink_fail _ _ _ _ _ CLm)].
      apply PECRVD.but_pos_r_fail. apply PECRVD.but_pos_sym. apply PECRVD.but_pos_w_pos.
    + reflexivity.
Qed.

Lemma arm_I fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 73 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTI_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & Y12 & Y23 & Y24 & SH1).
  apply (amid_pieceFW fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X fx1 R1 0xb3aec (pa_src_read AD) M1v (fun a => F / 8 + 2147450880 + 8 <= a < F / 8 + 2147450880 + 8 + 1) MID MS1 MG1).
  { intros a Ha Na. apply FRZ1; [exact Ha| revert Na; clear; intros Na; unfold SB in *; intros X'; apply Na; lia]. }
  { intros a X'. unfold SB. right. clear - X'; lia. }
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTI). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et Y1 Y10 Y11 Y12 Y23 Y24 SH1.
  intros M1 md1 VIS1 HID1 MGM1 FR1w MID.
  apply (call_read (F + 64) 2 0xb3f60 8 2 fx1 R1 M1 md1 LKi Awi cri si smi eni ki ei X MID MORE DONE PPOS Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(rewrite HID1, VIS1; replace (F / 8 + 2147450880 + 8) with (F / 8 + 2147450888) by (clear; lia); exact SH1) ltac:(right; clear; lia)).
  keep_only MORE DONE PPOS MPE XBAD Et Y23 Y24.
  intros fxb Rb Mb mdb LKb Awb srcb smb d RP2 Z10 Hd SHORT LE BYT SHB2 MID.
  assert (S23 : getr Rb (reg 23) = Z_to_bv 64 (F + 64)) by (rewrite (L5SAR.cs_of_preserved _ Rb 23 RP2) by inl; exact Y23).
  assert (S24 : getr Rb (reg 24) = Z_to_bv 64 2) by (rewrite (L5SAR.cs_of_preserved _ Rb 24 RP2) by inl; exact Y24).
  assert (Hd64 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  entry_facts. frame_facts. piece_ctx MID.
  destruct (Z.eq_dec d 2) as [Ed|Nd].
  -
    subst d.
    assert (FD : L5.defined MVi (F + 64) 8) by (lazymatch goal with H : L5.defined MVi F 512 |- _ => apply (L5.defined_sub MVi F 512); [exact H| clear; lia| clear; lia] end).
    pose proof GFR as (GF1 & GF2 & GF3 & _).
    destruct (PMCG.u64_of_defined RSEGS MVi (F + 64) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) FD) as (x & Hx & CX).
    pz PEARVP3.arvIV_conc fxb Rb 0 0 0 0 x as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hx; lia]).
    destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10b & Z11 & _ & _ & Z14 & _).
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb3f60 R3 (pe_int64 EE) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 2) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvIV). vm_compute. reflexivity. }
    lazymatch type of Z11 with getr _ _ = AX2.edenot ?EEv _ => destruct (PECRVW.wid_sra48 EEv (AX2.EMd Instr.M_MUL (AX2.ELit 72058693549555712) (AX2.EExt false 0 2 (AX2.EVar 50)))) as (v & Hv & Ev) end. rewrite Ev in Z11.
    keep_only MORE DONE PPOS MPE XBAD Et LE MID3 Z1 Z10b Z11 Z14 Hv. rename MID3 into MID.
    pose proof VI as SPEC. unfold PECSA.v_int64_spec, PECSPA.v_int64_spec in SPEC.
    apply (call_slot Z (pe_int64 EE) (PECSPA.args_i64 AD) (fun _ => PECSPA.mp_enc) (fun v0 _ X0 => e_scalar (PECSPA.int64_width v0) (PECSPA.int64_width v0) X0) SPEC v 0xb3fb8 fx3 R3 Mb md3 LKb Awb cri
             (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 2) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b).
    { unfold PECSPA.args_i64. rewrite L5K.rl11, L5K.rl14. split; [clear - Hv; lia|]. split; [exact Z11| exact Z14]. }
    { unfold PECSPA.mp_enc in MPE |- *. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. exact MPE. }
    { rewrite PECRVD.e_scalar_bad. cbn [s_bad w_pos]. exact XBAD. }
    { rewrite PECRVD.e_scalar_hi. cbn [s_hi w_pos]. pose proof HB as HB'. rewrite Et, PECRVD.rv_I, (PECRVD.num_arm_ok p 2 2 3 X LE) in HB'.
      unfold PECRVD.fin in HB'. rewrite PECRVD.w_more_same in HB' by (rewrite PECRVD.e_scalar_more; exact MORE).
      assert (HB2 : PESKA.spa_hb P (s_hi X + 3)).
      { destruct (s_ec (e_scalar 2 3 (w_pos (s_pos X + 2) X))); cbn [s_hi w_more] in HB'; rewrite PECRVD.e_scalar_hi in HB'; exact HB'. }
      apply (PESKA.spao_hb_mono L P PO _ _ HB2). pose proof (PECRVD.iw16 v Hv) as IW. rewrite <- (iwA v) in IW. clear - IW; lia. }
    intros fx4 R4 M4 md4 LK4 Aw4 en4 k4 e4 cr4 RP4 MID4 KP4.
    keep_only MORE DONE PPOS Et LE Hv MID4. rename MID4 into MID.
    assert (MIDr : amid fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 2 3 (w_pos (s_pos X + 2) X))).
    { apply (amid_relink _ _ _ _ _ _ _ _ _ _ _ _ _ _ MID); [| rewrite !PECRVD.e_scalar_ec; reflexivity].
      pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      revert CLm. apply PECRVD.clink_scalar_widen. pose proof (PECRVD.iw16 v Hv) as IW. rewrite <- (iwA v) in IW. clear - IW; lia. }
    clear MID. rename MIDr into MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP5.arvZI_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & _ & MO7).
    apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 2 3 (w_pos (s_pos X + 2) X)) fx7 R7 M7v 0xb3fb8 MID MS7 MG7).
    + intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZI). vm_compute. reflexivity.
    + replace (PM.p_more (PMSPA.with_src si srcb)) with 1; [exact MO7|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
      rewrite Lmore. rewrite PECRVD.e_scalar_more. cbn [s_more w_pos]. rewrite MORE. reflexivity.
    + rewrite Et, PECRVD.rv_I, (PECRVD.num_arm_ok p 2 2 3 X LE). unfold PECRVD.fin. rewrite PECRVD.w_more_same by (rewrite PECRVD.e_scalar_more; exact MORE). reflexivity.
  -
    assert (Hd' : 0 <= d <= 1) by (clear - Hd Nd; lia).
    pz PEARVP3.arvIN_conc fxb Rb 0 0 d 0 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hd'; lia]).
    destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10b & Z11).
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb3f60 R3 (pa_make_ec AD) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvIN). vm_compute. reflexivity. }
    keep_only Et Hd Nd SHORT MID3 Z1 Z10b Z11. rename MID3 into MID.
    apply (call_mkec 0xb45bc 1 fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b Z11 ltac:(clear; lia)).
    clear MID. intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP6.arvEI_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & MO7).
    apply (finish 0 (r_fail X) fx4 R4 M4 md4 LK4 Aw4 cri (PMSPA.with_src si srcb) smb eni ki true _ fx7 R7 M7v 0xb45bc MID MS7 MG7).
    + intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvEI). vm_compute. reflexivity.
    + exact MO7.
    + left; reflexivity.
    + rewrite Et, PECRVD.rv_I. symmetry. apply (PECRVD.num_arm_short p 2 2 3 X). clear - SHORT Nd Hd; lia.
    + pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      apply (PECRVD.clink_but_pos p (r_fail X) (w_more false (w_ec true (w_pos (s_pos X + d) X)))); [reflexivity| | exact (clink_fail _ _ _ _ _ CLm)].
      apply PECRVD.but_pos_r_fail. apply PECRVD.but_pos_sym. apply PECRVD.but_pos_w_pos.
    + reflexivity.
Qed.

Lemma arm_l fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 108 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTl_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & Y12 & Y23 & Y24 & SH1).
  apply (amid_pieceFW fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X fx1 R1 0xb3aec (pa_src_read AD) M1v (fun a => F / 8 + 2147450880 + 10 <= a < F / 8 + 2147450880 + 10 + 1) MID MS1 MG1).
  { intros a Ha Na. apply FRZ1; [exact Ha| revert Na; clear; intros Na; unfold SB in *; intros X'; apply Na; lia]. }
  { intros a X'. unfold SB. right. clear - X'; lia. }
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTl). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et Y1 Y10 Y11 Y12 Y23 Y24 SH1.
  intros M1 md1 VIS1 HID1 MGM1 FR1w MID.
  apply (call_read (F + 80) 4 0xb43cc 10 4 fx1 R1 M1 md1 LKi Awi cri si smi eni ki ei X MID MORE DONE PPOS Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(rewrite HID1, VIS1; replace (F / 8 + 2147450880 + 10) with (F / 8 + 2147450890) by (clear; lia); exact SH1) ltac:(right; clear; lia)).
  keep_only MORE DONE PPOS MPE XBAD Et Y23 Y24.
  intros fxb Rb Mb mdb LKb Awb srcb smb d RP2 Z10 Hd SHORT LE BYT SHB2 MID.
  assert (S23 : getr Rb (reg 23) = Z_to_bv 64 (F + 80)) by (rewrite (L5SAR.cs_of_preserved _ Rb 23 RP2) by inl; exact Y23).
  assert (S24 : getr Rb (reg 24) = Z_to_bv 64 4) by (rewrite (L5SAR.cs_of_preserved _ Rb 24 RP2) by inl; exact Y24).
  assert (Hd64 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  entry_facts. frame_facts. piece_ctx MID.
  destruct (Z.eq_dec d 4) as [Ed|Nd].
  -
    subst d.
    assert (FD : L5.defined MVi (F + 80) 8) by (lazymatch goal with H : L5.defined MVi F 512 |- _ => apply (L5.defined_sub MVi F 512); [exact H| clear; lia| clear; lia] end).
    pose proof GFR as (GF1 & GF2 & GF3 & _).
    destruct (PMCG.u64_of_defined RSEGS MVi (F + 80) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) FD) as (x & Hx & CX).
    pz PEARVP3.arvlV_conc fxb Rb 0 0 0 0 x as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hx; lia]).
    destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10b & Z11 & _ & _ & Z14 & _).
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb43cc R3 (pe_int64 EE) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 4) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvlV). vm_compute. reflexivity. }
    lazymatch type of Z11 with getr _ _ = AX2.edenot ?EEv _ => destruct (PECRVW.wid_sext32 EEv (AX2.EExt true 0 4 (AX2.EVar 50))) as (v & Hv & Ev) end. rewrite Ev in Z11.
    keep_only MORE DONE PPOS MPE XBAD Et LE MID3 Z1 Z10b Z11 Z14 Hv. rename MID3 into MID.
    pose proof VI as SPEC. unfold PECSA.v_int64_spec, PECSPA.v_int64_spec in SPEC.
    apply (call_slot Z (pe_int64 EE) (PECSPA.args_i64 AD) (fun _ => PECSPA.mp_enc) (fun v0 _ X0 => e_scalar (PECSPA.int64_width v0) (PECSPA.int64_width v0) X0) SPEC v 0xb4440 fx3 R3 Mb md3 LKb Awb cri
             (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 4) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b).
    { unfold PECSPA.args_i64. rewrite L5K.rl11, L5K.rl14. split; [clear - Hv; lia|]. split; [exact Z11| exact Z14]. }
    { unfold PECSPA.mp_enc in MPE |- *. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. exact MPE. }
    { rewrite PECRVD.e_scalar_bad. cbn [s_bad w_pos]. exact XBAD. }
    { rewrite PECRVD.e_scalar_hi. cbn [s_hi w_pos]. pose proof HB as HB'. rewrite Et, PECRVD.rv_l, (PECRVD.num_arm_ok p 4 2 5 X LE) in HB'.
      unfold PECRVD.fin in HB'. rewrite PECRVD.w_more_same in HB' by (rewrite PECRVD.e_scalar_more; exact MORE).
      assert (HB2 : PESKA.spa_hb P (s_hi X + 5)).
      { destruct (s_ec (e_scalar 2 5 (w_pos (s_pos X + 4) X))); cbn [s_hi w_more] in HB'; rewrite PECRVD.e_scalar_hi in HB'; exact HB'. }
      apply (PESKA.spao_hb_mono L P PO _ _ HB2). pose proof (PECRVD.iw32 v Hv) as IW. rewrite <- (iwA v) in IW. clear - IW; lia. }
    intros fx4 R4 M4 md4 LK4 Aw4 en4 k4 e4 cr4 RP4 MID4 KP4.
    keep_only MORE DONE PPOS Et LE Hv MID4. rename MID4 into MID.
    assert (MIDr : amid fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 2 5 (w_pos (s_pos X + 4) X))).
    { apply (amid_relink _ _ _ _ _ _ _ _ _ _ _ _ _ _ MID); [| rewrite !PECRVD.e_scalar_ec; reflexivity].
      pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      revert CLm. apply PECRVD.clink_scalar_widen. pose proof (PECRVD.iw32 v Hv) as IW. rewrite <- (iwA v) in IW. clear - IW; lia. }
    clear MID. rename MIDr into MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP5.arvZl_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & _ & MO7).
    apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 2 5 (w_pos (s_pos X + 4) X)) fx7 R7 M7v 0xb4440 MID MS7 MG7).
    + intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZl). vm_compute. reflexivity.
    + replace (PM.p_more (PMSPA.with_src si srcb)) with 1; [exact MO7|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
      rewrite Lmore. rewrite PECRVD.e_scalar_more. cbn [s_more w_pos]. rewrite MORE. reflexivity.
    + rewrite Et, PECRVD.rv_l, (PECRVD.num_arm_ok p 4 2 5 X LE). unfold PECRVD.fin. rewrite PECRVD.w_more_same by (rewrite PECRVD.e_scalar_more; exact MORE). reflexivity.
  -
    assert (Hd' : 0 <= d <= 3) by (clear - Hd Nd; lia).
    pz PEARVP3.arvlN_conc fxb Rb 0 0 d 0 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hd'; lia]).
    destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10b & Z11).
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb43cc R3 (pa_make_ec AD) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvlN). vm_compute. reflexivity. }
    keep_only Et Hd Nd SHORT MID3 Z1 Z10b Z11. rename MID3 into MID.
    apply (call_mkec 0xb46d0 1 fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b Z11 ltac:(clear; lia)).
    clear MID. intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP6.arvEl_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & MO7).
    apply (finish 0 (r_fail X) fx4 R4 M4 md4 LK4 Aw4 cri (PMSPA.with_src si srcb) smb eni ki true _ fx7 R7 M7v 0xb46d0 MID MS7 MG7).
    + intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvEl). vm_compute. reflexivity.
    + exact MO7.
    + left; reflexivity.
    + rewrite Et, PECRVD.rv_l. symmetry. apply (PECRVD.num_arm_short p 4 2 5 X). clear - SHORT Nd Hd; lia.
    + pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      apply (PECRVD.clink_but_pos p (r_fail X) (w_more false (w_ec true (w_pos (s_pos X + d) X)))); [reflexivity| | exact (clink_fail _ _ _ _ _ CLm)].
      apply PECRVD.but_pos_r_fail. apply PECRVD.but_pos_sym. apply PECRVD.but_pos_w_pos.
    + reflexivity.
Qed.

Lemma arm_U fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 85 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTU_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & Y12 & Y23 & SH1).
  apply (amid_pieceFW fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X fx1 R1 0xb3aec (pa_src_read AD) M1v (fun a => F / 8 + 2147450880 + 6 <= a < F / 8 + 2147450880 + 6 + 1) MID MS1 MG1).
  { intros a Ha Na. apply FRZ1; [exact Ha| revert Na; clear; intros Na; unfold SB in *; intros X'; apply Na; lia]. }
  { intros a X'. unfold SB. right. clear - X'; lia. }
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTU). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et Y1 Y10 Y11 Y12 Y23 SH1.
  intros M1 md1 VIS1 HID1 MGM1 FR1w MID.
  apply (call_read (F + 48) 1 0xb4248 6 1 fx1 R1 M1 md1 LKi Awi cri si smi eni ki ei X MID MORE DONE PPOS Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(rewrite HID1, VIS1; replace (F / 8 + 2147450880 + 6) with (F / 8 + 2147450886) by (clear; lia); exact SH1) ltac:(right; clear; lia)).
  keep_only MORE DONE PPOS MPE XBAD Et Y23.
  intros fxb Rb Mb mdb LKb Awb srcb smb d RP2 Z10 Hd SHORT LE BYT SHB2 MID.
  assert (S23 : getr Rb (reg 23) = Z_to_bv 64 (F + 48)) by (rewrite (L5SAR.cs_of_preserved _ Rb 23 RP2) by inl; exact Y23).
  entry_facts. frame_facts. piece_ctx MID.
  destruct (Z.eq_dec d 1) as [Ed|Nd].
  -
    subst d. pose proof POK as (BOK & _). pose proof GFR as (GF1 & GF2 & GF3 & _).
    set (b := bat p (s_pos X)) in *. pose proof (PECRVD.bat_byte p (s_pos X) BOK ltac:(clear - PPOS LE; lia)) as BB. fold b in BB. assert (BB64 : 0 <= b < 2 ^ 64) by (clear - BB; lia).
    assert (BBr : 0 <= b <= 255) by (clear - BB; lia).
    assert (Cb : L5.u8_at RSEGS Mb (F + 48) b).
    { rewrite (PECRVD.slice_pos_1 p (s_pos X)) in BYT by (clear - PPOS LE; lia). pose proof (BYT 0%nat ltac:(cbn; lia)) as B0. cbn [nth Z.of_nat] in B0. rewrite Z.add_0_r in B0. exact B0. }
    assert (CX : L5.u8_at RSEGS MVi (F + 48) b).
    { vis_amid BI Hi MVi. lazymatch goal with H : L5A.avis _ F 512 |- _ => exact (proj2 (L5A.u8_at_vis _ Mb (F + 48) b (L5A.avis_sub _ F 512 (F + 48) 1 H ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia)) Cb) end. }
    pz PEARVP3.arvUV_conc fxb Rb 0 0 0 0 b as PB. L5SAR.feed PB ltac:(first [fcl | clear - BB64; lia| clear - BBr; lia]).
    destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10b & Z11 & _ & _ & Z14 & _).
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb4248 R3 (pe_uint64 EE) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvUV). vm_compute. reflexivity. }
    keep_only MORE DONE PPOS MPE XBAD Et LE MID3 Z1 Z10b Z11 Z14 BB. rename MID3 into MID.
    pose proof VU as SPEC. unfold PECSA.v_uint64_spec, PECSPA.v_uint64_spec in SPEC.
    apply (call_slot Z (pe_uint64 EE) (PECSPA.args_u64 AD) (fun _ => PECSPA.mp_enc) (fun v0 _ X0 => e_scalar (PECSPA.uint64_width v0) (PECSPA.uint64_width v0) X0) SPEC (bat p (s_pos X)) 0xb4290 fx3 R3 Mb md3 LKb Awb cri
             (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b).
    { unfold PECSPA.args_u64. rewrite L5K.rl11, L5K.rl14. split; [unfold UbjRef.INT64_MAX; clear - BB; lia|]. split; [exact Z11| exact Z14]. }
    { unfold PECSPA.mp_enc in MPE |- *. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. exact MPE. }
    { rewrite PECRVD.e_scalar_bad. cbn [s_bad w_pos]. exact XBAD. }
    { rewrite PECRVD.e_scalar_hi. cbn [s_hi w_pos]. pose proof HB as HB'. rewrite Et, PECRVD.rv_U, (PECRVD.num_arm_ok p 1 2 2 X LE) in HB'.
      unfold PECRVD.fin in HB'. rewrite PECRVD.w_more_same in HB' by (rewrite PECRVD.e_scalar_more; exact MORE).
      assert (HB2 : PESKA.spa_hb P (s_hi X + 2)).
      { destruct (s_ec (e_scalar 2 2 (w_pos (s_pos X + 1) X))); cbn [s_hi w_more] in HB'; rewrite PECRVD.e_scalar_hi in HB'; exact HB'. }
      rewrite uwA, (PECRVD.uw8 (bat p (s_pos X))) by (clear - BB; lia). exact HB2. }
    intros fx4 R4 M4 md4 LK4 Aw4 en4 k4 e4 cr4 RP4 MID4 KP4.
    keep_only MORE DONE PPOS Et LE BB MID4. rename MID4 into MID. rewrite uwA, (PECRVD.uw8 (bat p (s_pos X))) in MID by (clear - BB; lia).
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP5.arvZU_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & _ & MO7).
    apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 2 2 (w_pos (s_pos X + 1) X)) fx7 R7 M7v 0xb4290 MID MS7 MG7).
    + intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZU). vm_compute. reflexivity.
    + replace (PM.p_more (PMSPA.with_src si srcb)) with 1; [exact MO7|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
      rewrite Lmore. rewrite PECRVD.e_scalar_more. cbn [s_more w_pos]. rewrite MORE. reflexivity.
    + rewrite Et, PECRVD.rv_U, (PECRVD.num_arm_ok p 1 2 2 X LE). unfold PECRVD.fin. rewrite PECRVD.w_more_same by (rewrite PECRVD.e_scalar_more; exact MORE). reflexivity.
  -
    assert (Ed : d = 0) by (clear - Hd Nd; lia). rewrite Ed in Z10.
    pz PEARVP3.arvUN_conc fxb Rb 0 0 0 0 0 as PB. L5SAR.feed PB fcl.
    destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10b & Z11).
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb4248 R3 (pa_make_ec AD) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvUN). vm_compute. reflexivity. }
    keep_only Et Hd Nd SHORT MID3 Z1 Z10b Z11. rename MID3 into MID.
    apply (call_mkec 0xb4730 1 fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b Z11 ltac:(clear; lia)).
    clear MID. intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP6.arvEU_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & MO7).
    apply (finish 0 (r_fail X) fx4 R4 M4 md4 LK4 Aw4 cri (PMSPA.with_src si srcb) smb eni ki true _ fx7 R7 M7v 0xb4730 MID MS7 MG7).
    + intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvEU). vm_compute. reflexivity.
    + exact MO7.
    + left; reflexivity.
    + rewrite Et, PECRVD.rv_U. symmetry. apply (PECRVD.num_arm_short p 1 2 2 X). clear - SHORT Nd Hd; lia.
    + pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      apply (PECRVD.clink_but_pos p (r_fail X) (w_more false (w_ec true (w_pos (s_pos X + d) X)))); [reflexivity| | exact (clink_fail _ _ _ _ _ CLm)].
      apply PECRVD.but_pos_r_fail. apply PECRVD.but_pos_sym. apply PECRVD.but_pos_w_pos.
    + reflexivity.
Qed.

Lemma arm_L fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 76 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTL_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & Y12 & Y23 & Y24 & SH1).
  apply (amid_pieceFW fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X fx1 R1 0xb3aec (pa_src_read AD) M1v (fun a => F / 8 + 2147450880 + 12 <= a < F / 8 + 2147450880 + 12 + 1) MID MS1 MG1).
  { intros a Ha Na. apply FRZ1; [exact Ha| revert Na; clear; intros Na; unfold SB in *; intros X'; apply Na; lia]. }
  { intros a X'. unfold SB. right. clear - X'; lia. }
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTL). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et Y1 Y10 Y11 Y12 Y23 Y24 SH1.
  intros M1 md1 VIS1 HID1 MGM1 FR1w MID.
  apply (call_read (F + 96) 8 0xb4018 12 0 fx1 R1 M1 md1 LKi Awi cri si smi eni ki ei X MID MORE DONE PPOS Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(rewrite HID1, VIS1; replace (F / 8 + 2147450880 + 12) with (F / 8 + 2147450892) by (clear; lia); exact SH1) ltac:(left; reflexivity)).
  keep_only MORE DONE PPOS MPE XBAD Et Y23 Y24.
  intros fxb Rb Mb mdb LKb Awb srcb smb d RP2 Z10 Hd SHORT LE BYT SHB2 MID.
  assert (S23 : getr Rb (reg 23) = Z_to_bv 64 (F + 96)) by (rewrite (L5SAR.cs_of_preserved _ Rb 23 RP2) by inl; exact Y23).
  assert (S24 : getr Rb (reg 24) = Z_to_bv 64 8) by (rewrite (L5SAR.cs_of_preserved _ Rb 24 RP2) by inl; exact Y24).
  assert (Hd64 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP3.arvRL_conc fxb Rb 0 0 d 0 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hd; lia]).
  destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & [(MS3 & KS3 & Z1 & Z10b & _ & _ & Z14 & _ & CQ3) | (MS3 & KS3 & Z1 & Z10b & Z11 & CQ3)]).
  +
    pose proof (count_eq d 8 Hd ltac:(clear; lia) CQ3) as Ed. subst d.
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb4018 R3 (pe_int64 EE) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 8) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvRL_0). vm_compute. reflexivity. }
    destruct (PECRVD.word_as_signed (getr R3 (reg 11))) as (v & Hv & Ev).
    keep_only MORE DONE PPOS MPE XBAD Et LE MID3 Z1 Z10b Z14 Hv Ev. rename MID3 into MID.
    pose proof VI as SPEC. unfold PECSA.v_int64_spec, PECSPA.v_int64_spec in SPEC.
    apply (call_slot Z (pe_int64 EE) (PECSPA.args_i64 AD) (fun _ => PECSPA.mp_enc) (fun v0 _ X0 => e_scalar (PECSPA.int64_width v0) (PECSPA.int64_width v0) X0) SPEC v 0xb40c4 fx3 R3 Mb md3 LKb Awb cri
             (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 8) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b).
    { unfold PECSPA.args_i64. rewrite L5K.rl11, L5K.rl14. split; [clear - Hv; lia|]. split; [exact Ev| exact Z14]. }
    { unfold PECSPA.mp_enc in MPE |- *. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. exact MPE. }
    { rewrite PECRVD.e_scalar_bad. cbn [s_bad w_pos]. exact XBAD. }
    { rewrite PECRVD.e_scalar_hi. cbn [s_hi w_pos]. pose proof HB as HB'. rewrite Et, PECRVD.rv_L, (PECRVD.num_arm_ok p 8 2 9 X LE) in HB'.
      unfold PECRVD.fin in HB'. rewrite PECRVD.w_more_same in HB' by (rewrite PECRVD.e_scalar_more; exact MORE).
      assert (HB2 : PESKA.spa_hb P (s_hi X + 9)).
      { destruct (s_ec (e_scalar 2 9 (w_pos (s_pos X + 8) X))); cbn [s_hi w_more] in HB'; rewrite PECRVD.e_scalar_hi in HB'; exact HB'. }
      apply (PESKA.spao_hb_mono L P PO _ _ HB2). pose proof (PECRVD.iw64 v) as IW. rewrite <- (iwA v) in IW. clear - IW; lia. }
    intros fx4 R4 M4 md4 LK4 Aw4 en4 k4 e4 cr4 RP4 MID4 KP4.
    keep_only MORE DONE PPOS Et LE Hv MID4. rename MID4 into MID.
    assert (MIDr : amid fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 2 9 (w_pos (s_pos X + 8) X))).
    { apply (amid_relink _ _ _ _ _ _ _ _ _ _ _ _ _ _ MID); [| rewrite !PECRVD.e_scalar_ec; reflexivity].
      pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      revert CLm. apply PECRVD.clink_scalar_widen. pose proof (PECRVD.iw64 v) as IW. rewrite <- (iwA v) in IW. clear - IW; lia. }
    clear MID. rename MIDr into MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP5.arvZL_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & _ & MO7).
    apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 2 9 (w_pos (s_pos X + 8) X)) fx7 R7 M7v 0xb40c4 MID MS7 MG7).
    * intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    * intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZL). vm_compute. reflexivity.
    * replace (PM.p_more (PMSPA.with_src si srcb)) with 1; [exact MO7|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
      rewrite Lmore. rewrite PECRVD.e_scalar_more. cbn [s_more w_pos]. rewrite MORE. reflexivity.
    * rewrite Et, PECRVD.rv_L, (PECRVD.num_arm_ok p 8 2 9 X LE). unfold PECRVD.fin. rewrite PECRVD.w_more_same by (rewrite PECRVD.e_scalar_more; exact MORE). reflexivity.
  +
    pose proof (count_ne d 8 Hd ltac:(clear; lia) CQ3) as Nd.
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb4018 R3 (pa_make_ec AD) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvRL_1). vm_compute. reflexivity. }
    keep_only Et Hd Nd SHORT MID3 Z1 Z10b Z11. rename MID3 into MID.
    apply (call_mkec 0xb45ec 1 fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b Z11 ltac:(clear; lia)).
    clear MID. intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP6.arvEL_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & MO7).
    apply (finish 0 (r_fail X) fx4 R4 M4 md4 LK4 Aw4 cri (PMSPA.with_src si srcb) smb eni ki true _ fx7 R7 M7v 0xb45ec MID MS7 MG7).
    * intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    * intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvEL). vm_compute. reflexivity.
    * exact MO7.
    * left; reflexivity.
    * rewrite Et, PECRVD.rv_L. symmetry. apply (PECRVD.num_arm_short p 8 2 9 X). clear - SHORT Nd Hd; lia.
    * pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      apply (PECRVD.clink_but_pos p (r_fail X) (w_more false (w_ec true (w_pos (s_pos X + d) X)))); [reflexivity| | exact (clink_fail _ _ _ _ _ CLm)].
      apply PECRVD.but_pos_r_fail. apply PECRVD.but_pos_sym. apply PECRVD.but_pos_w_pos.
    * reflexivity.
Qed.

Lemma arm_d fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 100 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTd_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & Y12 & Y23 & Y24 & SH1).
  apply (amid_pieceFW fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X fx1 R1 0xb3aec (pa_src_read AD) M1v (fun a => F / 8 + 2147450880 + 16 <= a < F / 8 + 2147450880 + 16 + 1) MID MS1 MG1).
  { intros a Ha Na. apply FRZ1; [exact Ha| revert Na; clear; intros Na; unfold SB in *; intros X'; apply Na; lia]. }
  { intros a X'. unfold SB. right. clear - X'; lia. }
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTd). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et Y1 Y10 Y11 Y12 Y23 Y24 SH1.
  intros M1 md1 VIS1 HID1 MGM1 FR1w MID.
  apply (call_read (F + 128) 4 0xb42f0 16 4 fx1 R1 M1 md1 LKi Awi cri si smi eni ki ei X MID MORE DONE PPOS Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(rewrite HID1, VIS1; replace (F / 8 + 2147450880 + 16) with (F / 8 + 2147450896) by (clear; lia); exact SH1) ltac:(right; clear; lia)).
  keep_only MORE DONE PPOS MPE XBAD Et Y23 Y24.
  intros fxb Rb Mb mdb LKb Awb srcb smb d RP2 Z10 Hd SHORT LE BYT SHB2 MID.
  assert (S23 : getr Rb (reg 23) = Z_to_bv 64 (F + 128)) by (rewrite (L5SAR.cs_of_preserved _ Rb 23 RP2) by inl; exact Y23).
  assert (S24 : getr Rb (reg 24) = Z_to_bv 64 4) by (rewrite (L5SAR.cs_of_preserved _ Rb 24 RP2) by inl; exact Y24).
  assert (Hd64 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP3.arvRd_conc fxb Rb 0 0 d 0 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hd; lia]).
  destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & [(MS3 & KS3 & Z10b & Z14f & CQ3) | (MS3 & KS3 & Z1 & Z10b & Z11 & CQ3)]).
  +
    pose proof (count_eq d 4 Hd ltac:(clear; lia) CQ3) as Ed. subst d.
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    destruct (PMPX.fmv_fx_run RSEGS fx3 R3 MVi 0xb4350 W_b4300 _ _ _ F_b4300 eq_refl D_b4300 (or_introl eq_refl) ltac:(clear; lia) ltac:(clear; lia)) as (fxh & MSh).
    change (0xb4350 + 4) with 0xb4354 in MSh.
    destruct (PMPX.fcvt_f_run RSEGS fxh R3 MVi 0xb4354 W_b4304 _ _ _ _ _ F_b4304 eq_refl D_b4304 (or_intror eq_refl) ltac:(vm_compute; intros XX; discriminate XX) ltac:(clear; lia) ltac:(clear; lia)) as (fxq & MSq).
    change (0xb4354 + 4) with 0xb4358 in MSq.
    pose proof (msteps_trans _ _ _ _ MS3 (msteps_trans _ _ _ _ MSh MSq)) as MSfp.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fxq Rb 0xb42f0 R3 0xb4358 MVi K HHi AMi MSfp (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fxq R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 4) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fxq R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvRd_0). vm_compute. reflexivity. }
    assert (S23c : getr R3 (reg 23) = Z_to_bv 64 (F + 128)) by (rewrite (KS3 23%nat) by inl; exact S23).
    assert (S24c : getr R3 (reg 24) = Z_to_bv 64 4) by (rewrite (KS3 24%nat) by inl; exact S24).
    keep_only MORE DONE PPOS MPE XBAD Et LE MID3 Z14f S23c S24c. rename MID3 into MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP3.arvRd2_conc fxq R3 0 0 0 0 0 as PC. L5SAR.feed PC fcl.
    destruct PC as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Q1 & Q10 & _ & _ & Q13).
    assert (E5 : M5v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb md3 fxq fx5 R3 0xb4358 R5 (pe_double EE) MVi K HHi AMi MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx5 R5 Mb md5 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 4) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 md5 MID); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvRd2). vm_compute. reflexivity. }
    keep_only MORE DONE PPOS MPE XBAD Et LE MID5 Q1 Q10 Q13. rename MID5 into MID.
    apply (call_double 0xb436c fx5 R5 Mb md5 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 4) X) MID Q1 ltac:(split; [clear; lia| reflexivity]) Q10 Q13).
    { unfold PECSPA.mp_enc in MPE |- *. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. exact MPE. }
    { cbn [s_hi w_pos]. pose proof HB as HB'. rewrite Et, PECRVD.rv_d, (PECRVD.num_arm_ok p 4 5 9 X LE) in HB'.
      unfold PECRVD.fin in HB'. rewrite PECRVD.w_more_same in HB' by (rewrite PECRVD.e_scalar_more; exact MORE).
      destruct (s_ec (e_scalar 5 9 (w_pos (s_pos X + 4) X))); cbn [s_hi w_more] in HB'; rewrite PECRVD.e_scalar_hi in HB'; exact HB'. }
    intros fx4 R4 M4 md4 LK4 Aw4 en4 k4 e4 cr4 w RP4 Hw MID4 KP4.
    keep_only MORE DONE PPOS Et LE Hw MID4. rename MID4 into MID.
    assert (MIDr : amid fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 5 9 (w_pos (s_pos X + 4) X))).
    { apply (amid_relink _ _ _ _ _ _ _ _ _ _ _ _ _ _ MID); [| rewrite !PECRVD.e_scalar_ec; reflexivity].
      pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      revert CLm. apply PECRVD.clink_scalar_widen. clear - Hw; lia. }
    clear MID. rename MIDr into MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP5.arvZd_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & _ & MO7).
    apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 5 9 (w_pos (s_pos X + 4) X)) fx7 R7 M7v 0xb436c MID MS7 MG7).
    * intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    * intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZd). vm_compute. reflexivity.
    * replace (PM.p_more (PMSPA.with_src si srcb)) with 1; [exact MO7|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
      rewrite Lmore. rewrite PECRVD.e_scalar_more. cbn [s_more w_pos]. rewrite MORE. reflexivity.
    * rewrite Et, PECRVD.rv_d, (PECRVD.num_arm_ok p 4 5 9 X LE). unfold PECRVD.fin. rewrite PECRVD.w_more_same by (rewrite PECRVD.e_scalar_more; exact MORE). reflexivity.
  +
    pose proof (count_ne d 4 Hd ltac:(clear; lia) CQ3) as Nd.
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb42f0 R3 (pa_make_ec AD) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvRd_1). vm_compute. reflexivity. }
    keep_only Et Hd Nd SHORT MID3 Z1 Z10b Z11. rename MID3 into MID.
    apply (call_mkec 0xb46a0 1 fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b Z11 ltac:(clear; lia)).
    clear MID. intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP6.arvEd_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & MO7).
    apply (finish 0 (r_fail X) fx4 R4 M4 md4 LK4 Aw4 cri (PMSPA.with_src si srcb) smb eni ki true _ fx7 R7 M7v 0xb46a0 MID MS7 MG7).
    * intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    * intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvEd). vm_compute. reflexivity.
    * exact MO7.
    * left; reflexivity.
    * rewrite Et, PECRVD.rv_d. symmetry. apply (PECRVD.num_arm_short p 4 5 9 X). clear - SHORT Nd Hd; lia.
    * pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      apply (PECRVD.clink_but_pos p (r_fail X) (w_more false (w_ec true (w_pos (s_pos X + d) X)))); [reflexivity| | exact (clink_fail _ _ _ _ _ CLm)].
      apply PECRVD.but_pos_r_fail. apply PECRVD.but_pos_sym. apply PECRVD.but_pos_w_pos.
    * reflexivity.
Qed.

Lemma arm_D fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 68 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTD_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & Y12 & Y23 & Y24 & SH1).
  apply (amid_pieceFW fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X fx1 R1 0xb3aec (pa_src_read AD) M1v (fun a => F / 8 + 2147450880 + 18 <= a < F / 8 + 2147450880 + 18 + 1) MID MS1 MG1).
  { intros a Ha Na. apply FRZ1; [exact Ha| revert Na; clear; intros Na; unfold SB in *; intros X'; apply Na; lia]. }
  { intros a X'. unfold SB. right. clear - X'; lia. }
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTD). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et Y1 Y10 Y11 Y12 Y23 Y24 SH1.
  intros M1 md1 VIS1 HID1 MGM1 FR1w MID.
  apply (call_read (F + 144) 8 0xb4138 18 0 fx1 R1 M1 md1 LKi Awi cri si smi eni ki ei X MID MORE DONE PPOS Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(rewrite HID1, VIS1; replace (F / 8 + 2147450880 + 18) with (F / 8 + 2147450898) by (clear; lia); exact SH1) ltac:(left; reflexivity)).
  keep_only MORE DONE PPOS MPE XBAD Et Y23 Y24.
  intros fxb Rb Mb mdb LKb Awb srcb smb d RP2 Z10 Hd SHORT LE BYT SHB2 MID.
  assert (S23 : getr Rb (reg 23) = Z_to_bv 64 (F + 144)) by (rewrite (L5SAR.cs_of_preserved _ Rb 23 RP2) by inl; exact Y23).
  assert (S24 : getr Rb (reg 24) = Z_to_bv 64 8) by (rewrite (L5SAR.cs_of_preserved _ Rb 24 RP2) by inl; exact Y24).
  assert (Hd64 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP3.arvRD_conc fxb Rb 0 0 d 0 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hd; lia]).
  destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & [(MS3 & KS3 & Z10b & Z14f & CQ3) | (MS3 & KS3 & Z1 & Z10b & Z11 & CQ3)]).
  +
    pose proof (count_eq d 8 Hd ltac:(clear; lia) CQ3) as Ed. subst d.
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    destruct (PMPX.fmv_fx_run RSEGS fx3 R3 MVi 0xb41d0 W_b4180 _ _ _ F_b4180 eq_refl D_b4180 (or_intror eq_refl) ltac:(clear; lia) ltac:(clear; lia)) as (fxq & MSq).
    change (0xb41d0 + 4) with 0xb41d4 in MSq.
    pose proof (msteps_trans _ _ _ _ MS3 MSq) as MSfp.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fxq Rb 0xb4138 R3 0xb41d4 MVi K HHi AMi MSfp (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fxq R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 8) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fxq R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvRD_0). vm_compute. reflexivity. }
    assert (S23c : getr R3 (reg 23) = Z_to_bv 64 (F + 144)) by (rewrite (KS3 23%nat) by inl; exact S23).
    assert (S24c : getr R3 (reg 24) = Z_to_bv 64 8) by (rewrite (KS3 24%nat) by inl; exact S24).
    keep_only MORE DONE PPOS MPE XBAD Et LE MID3 Z14f S23c S24c. rename MID3 into MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP3.arvRD2_conc fxq R3 0 0 0 0 0 as PC. L5SAR.feed PC fcl.
    destruct PC as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Q1 & Q10 & _ & _ & Q13).
    assert (E5 : M5v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb md3 fxq fx5 R3 0xb41d4 R5 (pe_double EE) MVi K HHi AMi MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx5 R5 Mb md5 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 8) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 md5 MID); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvRD2). vm_compute. reflexivity. }
    keep_only MORE DONE PPOS MPE XBAD Et LE MID5 Q1 Q10 Q13. rename MID5 into MID.
    apply (call_double 0xb41e8 fx5 R5 Mb md5 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 8) X) MID Q1 ltac:(split; [clear; lia| reflexivity]) Q10 Q13).
    { unfold PECSPA.mp_enc in MPE |- *. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. exact MPE. }
    { cbn [s_hi w_pos]. pose proof HB as HB'. rewrite Et, PECRVD.rv_D, (PECRVD.num_arm_ok p 8 5 9 X LE) in HB'.
      unfold PECRVD.fin in HB'. rewrite PECRVD.w_more_same in HB' by (rewrite PECRVD.e_scalar_more; exact MORE).
      destruct (s_ec (e_scalar 5 9 (w_pos (s_pos X + 8) X))); cbn [s_hi w_more] in HB'; rewrite PECRVD.e_scalar_hi in HB'; exact HB'. }
    intros fx4 R4 M4 md4 LK4 Aw4 en4 k4 e4 cr4 w RP4 Hw MID4 KP4.
    keep_only MORE DONE PPOS Et LE Hw MID4. rename MID4 into MID.
    assert (MIDr : amid fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 5 9 (w_pos (s_pos X + 8) X))).
    { apply (amid_relink _ _ _ _ _ _ _ _ _ _ _ _ _ _ MID); [| rewrite !PECRVD.e_scalar_ec; reflexivity].
      pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      revert CLm. apply PECRVD.clink_scalar_widen. clear - Hw; lia. }
    clear MID. rename MIDr into MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP5.arvZD_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & _ & MO7).
    apply (tail_J fx4 R4 M4 md4 LK4 Aw4 cr4 (PMSPA.with_src si srcb) smb en4 k4 e4 (e_scalar 5 9 (w_pos (s_pos X + 8) X)) fx7 R7 M7v 0xb41e8 MID MS7 MG7).
    * intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    * intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZD). vm_compute. reflexivity.
    * replace (PM.p_more (PMSPA.with_src si srcb)) with 1; [exact MO7|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
      rewrite Lmore. rewrite PECRVD.e_scalar_more. cbn [s_more w_pos]. rewrite MORE. reflexivity.
    * rewrite Et, PECRVD.rv_D, (PECRVD.num_arm_ok p 8 5 9 X LE). unfold PECRVD.fin. rewrite PECRVD.w_more_same by (rewrite PECRVD.e_scalar_more; exact MORE). reflexivity.
  +
    pose proof (count_ne d 8 Hd ltac:(clear; lia) CQ3) as Nd.
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb4138 R3 (pa_make_ec AD) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvRD_1). vm_compute. reflexivity. }
    keep_only Et Hd Nd SHORT MID3 Z1 Z10b Z11. rename MID3 into MID.
    apply (call_mkec 0xb461c 1 fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b Z11 ltac:(clear; lia)).
    clear MID. intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP6.arvED_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & MO7).
    apply (finish 0 (r_fail X) fx4 R4 M4 md4 LK4 Aw4 cri (PMSPA.with_src si srcb) smb eni ki true _ fx7 R7 M7v 0xb461c MID MS7 MG7).
    * intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    * intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvED). vm_compute. reflexivity.
    * exact MO7.
    * left; reflexivity.
    * rewrite Et, PECRVD.rv_D. symmetry. apply (PECRVD.num_arm_short p 8 5 9 X). clear - SHORT Nd Hd; lia.
    * pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      apply (PECRVD.clink_but_pos p (r_fail X) (w_more false (w_ec true (w_pos (s_pos X + d) X)))); [reflexivity| | exact (clink_fail _ _ _ _ _ CLm)].
      apply PECRVD.but_pos_r_fail. apply PECRVD.but_pos_sym. apply PECRVD.but_pos_w_pos.
    * reflexivity.
Qed.

Lemma tail_G fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fx7 : FPState) R7 M7v (pci : Z) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fx7 R7 (Z_to_bv 64 0xb44a8) M7v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) M7v -> (forall i, 0 <= i < 2 ^ 64 -> M7v (Z_to_bv 64 i) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 i)) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%nat -> getr R7 (reg j) = getr Ri (reg j)) ->
  s_ec Y = true -> r_value p t X = Y ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID MS7 MG7 FRZ7 K7 EY RV.
  apply (finish (PM.p_more si) Y fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y fx7 R7 M7v pci MID MS7 MG7).
  - intros i Hi' _ _. apply FRZ7. exact Hi'.
  - exact K7.
  - assert (E7 : M7v = mrestrict (ahid Awi mdi) Mi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). rewrite E7. exact (more_vis _ _ _ _ _ _ _ _ _ _ _ _ _ MID).
  - pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). exact (more_01 _ _ _ _ _ CLm).
  - symmetry. exact RV.
  - pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). exact (clink_same _ _ _ _ _ CLm).
  - reflexivity.
Qed.

Lemma arm_S fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 83 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTS_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_get_length AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTS). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et MID1 Y1 Y10 Y11. rename MID1 into MID.
  pose proof POK as (BOK & _). pose proof MP as ((PRE & _) & _ & HALT & _).
  apply (call_gl 0xb3c7c fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11).
  { unfold PECSPA.mp_gl. split; [exact BOK|]. split; [exact PPOS|]. split; [exact MORE|]. split; [exact DONE|]. split; [exact HALT| exact XBAD]. }
  clear MID. intros fx2 R2 Mg md2 LKg Aw2 cr2 si2 smi2 e2 RP2 RET2 MID ETB ETG EB EK FSH2 FDK2.
  unfold PECSPA.gl_post in MID. unfold PECSPA.gl_ret in RET2.
  destruct (UbjRef.get_length p (s_pos X)) as [[n pos1]|] eqn:GLd.
  2: {
       keep_only Et GLd MID. entry_facts. frame_facts. piece_ctx MID.
       destruct (ec_vis1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID eq_refl) as (v & Hv & ECU). fold Hi in ECU. fold MVi in ECU. assert (Bv : 0 <= v < 2 ^ 64) by (clear - Hv; lia). assert (Hv' : 1 <= v <= 64) by exact Hv.
       pose proof (bv_unsigned_in_range 64 (getr R2 (reg 10))) as B10v. change (bv_modulus 64) with (2 ^ 64) in B10v.
       assert (W10 : getr R2 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R2 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
       pz PEARVP4.arvSGe_conc fx2 R2 (bv_unsigned (getr R2 (reg 10))) 0 0 v 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - B10v; lia]).
       destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & _ & _ & _).
       apply (tail_G fx2 R2 Mg md2 LKg Aw2 cr2 si2 smi2 eni ki e2 (r_fail X) fx3 R3 M3v 0xb3c7c MID MS3 MG3 FRZ3); [| reflexivity| rewrite Et, PECRVD.rv_S; unfold PECRVD.str_arm; rewrite GLd; reflexivity].
       intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvSGe). vm_compute. reflexivity. }
  pose proof (get_length_some p (s_pos X) n pos1 BOK ltac:(clear - PPOS; lia) GLd) as (Hn & Hpos1 & _).
  destruct (s_ec X) eqn:EX.
  {
    keep_only Et GLd EX Hn MID RET2. entry_facts. frame_facts. piece_ctx MID.
    destruct (ec_vis1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(cbn; exact EX)) as (v & Hv & ECU). fold Hi in ECU. fold MVi in ECU. assert (Bv : 0 <= v < 2 ^ 64) by (clear - Hv; lia). assert (Hv' : 1 <= v <= 64) by exact Hv.
    rewrite L5K.rl10 in RET2. assert (Hn64 : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
    pz PEARVP4.arvSGe_conc fx2 R2 n 0 0 v 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Hn64; lia]).
    destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & _ & _ & _).
    apply (tail_G fx2 R2 Mg md2 LKg Aw2 cr2 si2 smi2 eni ki e2 (w_pos pos1 X) fx3 R3 M3v 0xb3c7c MID MS3 MG3 FRZ3); [| cbn; exact EX| rewrite Et, PECRVD.rv_S; unfold PECRVD.str_arm; rewrite GLd, EX; reflexivity].
    intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvSGe). vm_compute. reflexivity. }

  keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 BOK MID RET2 ETB ETG EB EK. entry_facts. frame_facts. piece_ctx MID.
  pose proof (ec_vis0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(cbn; exact EX)) as ECU. fold Hi in ECU. fold MVi in ECU.
  rewrite L5K.rl10 in RET2. assert (Hn64 : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
  pz PEARVP4.arvSG0_conc fx2 R2 n 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Hn64; lia]).
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10 & Z11 & Z12 & Zs).
  assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKg cr2 Aw2 Mg md2 fx2 fx3 R2 0xb3c7c R3 (pa_read_span AD) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
  assert (E3 : M3 = Mg) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
  assert (MID3 : amid fx3 R3 Mg md3 LKg Aw2 cr2 si2 smi2 eni ki e2 (w_pos pos1 X)).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
    intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvSG0). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 BOK MID3 ETB ETG EB EK Z1 Z10 Z11 Z12 Zs. rename MID3 into MID.
  apply (call_span n 0xb3ca8 fx3 R3 Mg md3 LKg Aw2 cr2 si2 smi2 eni ki e2 (w_pos pos1 X) MID ltac:(cbn; exact MORE) ltac:(cbn; exact DONE) ltac:(cbn [s_pos w_pos]; clear - Hpos1 PPOS; lia)
           Z1 ltac:(split; [clear; lia| reflexivity]) Z10 Z11 Z12 ltac:(clear - Hn; lia)).
  clear MID. intros fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 ptr n2 RP4 V10 V11 Hn2 Hn26 LOC DEF4 ACC4 BYT4 NMIN MID EB4 EK4. cbn [s_pos w_pos] in BYT4, NMIN, MID.
  assert (WW : w_pos (pos1 + n2) (w_pos pos1 X) = w_pos (pos1 + n2) X) by (destruct X; reflexivity). rewrite WW in MID. clear WW.
  assert (Ss : getr R4 (reg 23) = Z_to_bv 64 n) by (rewrite (L5SAR.cs_of_preserved _ R4 23 RP4) by inl; exact Zs).
  entry_facts. frame_facts. piece_ctx MID.
  assert (PTRR : 0 <= ptr < 2 ^ 64).
  { destruct LOC as [[-> ->]|[(B & m & HinB & HB1 & HB2)|[T1 T2]]].
    - clear. lia.
    - pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRB. assert (HinB' : In (B, m) (PEC.owned si4 eni ki ++ LBX)) by (unfold PEC.owned; apply in_or_app; left; apply in_or_app; left; exact HinB).
      destruct (BRB _ HinB') as (B0 & B47). cbn [fst snd] in B0, B47. clear - B0 B47 HB1 HB2 Hn2. lia.
    - clear - T1 T2 Eotb Eop O1 O3 Hn2. lia. }
  assert (Hn264 : 0 <= n2 < 2 ^ 64) by (clear - Hn2 Hn; lia).
  pz PEARVP4.arvSF_conc fx4 R4 n ptr n2 0 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hn; lia| clear - PTRR; lia| clear - Hn264; lia]).
  destruct PB as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & [(MS5 & KS5 & Q1 & Q11 & Q24 & CQ5) | (MS5 & KS5 & Q1 & Q10 & Q11 & CQ5)]).
  +
    assert (En : n2 = n).
    { clear - CQ5 Hn Hn2. destruct (Z.eq_dec n2 n) as [E|N]; [exact E| exfalso].
      replace (n2 - n) with ((n2 - n + 2 ^ 64) + (-1) * 2 ^ 64) in CQ5 by lia. rewrite Z.mod_add in CQ5 by lia. rewrite Z.mod_small in CQ5 by lia. lia. }
    rewrite En in *. clear En CQ5.
    assert (LEN : pos1 + n <= blen p) by (clear - NMIN Hn Hpos1; lia).
    assert (SLEN : Z.of_nat (length (UbjRef.slice p pos1 n)) = n) by (apply PECRVD.slice_length; clear - Hn Hpos1 LEN PPOS; lia).
    assert (SBYT : Forall (fun b => 0 <= b < 256) (UbjRef.slice p pos1 n)) by (apply PECRVD.slice_bytes; exact BOK).
    pose proof GFR as (GF1 & GF2 & GF3 & _).
    assert (PTR47 : 0 <= ptr /\ (n = 0 \/ 0 < ptr) /\ ptr + n <= 2 ^ 47 /\ (ptr + n <= F \/ F + 512 <= ptr) /\ (n = 0 \/ ptr + n <= ahl_ceil ar) /\ (n = 0 \/ ptr + n <= 2147446784 \/ 17594333495296 <= ptr)).
    { destruct LOC as [[E0 En0]|[(B & m & HinB & HB1 & HB2)|[T1 T2]]].
      - rewrite E0, En0. clear - GF1. lia.
      - pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRB. assert (HinB' : In (B, m) (PEC.owned si4 eni ki ++ LBX)) by (unfold PEC.owned; apply in_or_app; left; apply in_or_app; left; exact HinB).
        destruct (BRB _ HinB') as (B0 & B47). cbn [fst snd] in B0, B47.
        pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WBi & _). destruct (WBi _ HinB') as ((W0' & W1' & W2' & W3' & W4' & W5') & _ & _ & _ & _ & FA & _). cbn [fst snd] in W0', W1', W2', W3', W4', W5'.
        destruct (FA (F, 3, sp - 128 + 32) (or_introl eq_refl)) as [Z'|Z']; cbn [ff_addr ff_class fst snd] in Z'; change (ff_bytes 3) with 512 in Z';
          (refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); [clear - B0 HB1; lia| right; clear - W0' HB1; lia| clear - B47 HB2; lia| clear - Z' HB1 HB2 Hn; lia| right; clear - W0' W1' W2' W3' W4' W5' HB2 SLO SHI SPT; lia
             | right; unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in W5'; clear - W5' HB1 HB2; lia]).
      - refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); [clear - T1 Eotb Eop O1; lia| right; clear - T1 Eotb Eop O1; lia| clear - T2 Eotb Eop O3; lia| lazymatch goal with H : op + 384 <= F \/ _ |- _ => clear - T1 T2 Eotb H Hn; lia end
          | right; clear - T2 Eotb Eop F2 FSCEIL; lia| right; clear - T1 T2 Eotb Eop F1 F2 FSAPP; lia]. }
    destruct PTR47 as (PT0 & PT1 & PT2 & PTF & PT4 & PTA).
    assert (E5 : M5v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr4 Aw4 M4 md4 fx4 fx5 R4 0xb3ca8 R5 (pa_validate AD) MVi K HHi AMi MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx5 R5 M4 md5 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 md5 MID); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvSF_0). vm_compute. reflexivity. }
    keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 BOK Hn26 LEN SLEN SBYT PT0 PT1 PT2 PTF PT4 PTA LOC DEF4 ACC4 BYT4 V10 MID5 Q1 Q11 Q24 KS5 Ss. rename MID5 into MID.

    apply (call_valid ptr n 0xb3cb8 (UbjRef.slice p pos1 n) fx5 R5 M4 md5 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X) MID Q1 ltac:(split; [clear; lia| reflexivity])
             ltac:(rewrite (KS5 10%nat) by inl; exact V10) Q11 ltac:(clear - Hn Hn26; lia) PT0 PT1 PT2 DEF4 ACC4
             ltac:(destruct LOC as [[E0 En0]|[(Bb & mb & Hinb & Xb1 & Xb2)|TT]]; [left; exact En0| right; left; exists Bb, mb; split; [unfold PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hinb| split; [exact Xb1| exact Xb2]]| right; right; left; exact TT]) BYT4 SLEN SBYT).
    clear MID. intros fx6 R6 M6 md6 v RP6 V11' Hv HV MG6 FRZ6 MID.
    assert (S23v : getr R6 (reg 23) = Z_to_bv 64 n) by (rewrite (L5SAR.cs_of_preserved _ R6 23 RP6) by inl; rewrite (KS5 23%nat) by inl; exact Ss).
    assert (S24v : getr R6 (reg 24) = Z_to_bv 64 ptr) by (rewrite (L5SAR.cs_of_preserved _ R6 24 RP6) by inl; exact Q24).
    assert (Bv : 0 <= v < 2 ^ 64) by (clear - Hv; lia). assert (Hv6 : 0 <= v <= 6) by (clear - Hv; lia).
    entry_facts. frame_facts. piece_ctx MID.
    assert (BYT6 : L5.bytes_at RSEGS M6 ptr (UbjRef.slice p pos1 n)).
    { apply (L5C.bytes_at_agree RSEGS M4 M6); [| exact PT0| rewrite SLEN; clear - PT2; lia| exact BYT4]. rewrite SLEN. intros i Hi'. apply FRZ6; [clear - Hi' PT0 PT2; lia|]. intros X'. clear - Hi' X' PT4 GSLO. lia. }
    assert (DEF6 : L5.defined M6 ptr n) by exact (L5.defined_grows M4 M6 ptr n MG6 DEF4).
    assert (ACC6 : PMSPA.accA M6 ptr n).
    { apply (PMFA.accA_agree M4 M6 ptr n); [| exact ACC4]. intros x Hx. unfold S, SB. apply FRZ6; [clear - Hx PT0 PT2; lia| clear - Hx PT0 PT2 GSLO GSPT; lia]. }
    assert (PTRR : 0 <= ptr < 2 ^ 64) by (clear - PT0 PT2 Hn; lia). assert (Hn64 : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
    pz PEARVP4.arvSW_conc fx6 R6 n ptr 0 v 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hv6; lia]).
    destruct PB as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & [(MS7 & KS7 & E1 & E10 & E11 & E12 & _ & E14 & _ & Cn & Cp & SHb & SHa & CQ7 & _ & _) | (MS7 & KS7 & E1 & E10 & E11 & CQ7)]).
    *
      assert (Ev : v = 0) by (clear - CQ7 Hv; destruct (Z.eq_dec v 0) as [E|N]; [exact E| exfalso; rewrite Z.sub_0_r in CQ7; rewrite Z.mod_small in CQ7 by lia; lia]).
      assert (VT : UbjRef.utf8_valid (UbjRef.slice p pos1 n) = true) by (apply HV; exact Ev).
      apply (amid_pieceFW fx6 R6 M6 md6 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X) fx7 R7 0xb3cb8 (pe_string EE) M7v (fun a => (F + 224 <= a < F + 224 + 16) \/ (F / 8 + 2147450880 + 28 <= a < F / 8 + 2147450880 + 28 + 2)) MID MS7 MG7).
      { intros a Ha Na. apply FRZ7; [exact Ha| clear - Na; intros X'; apply Na; left; exact X'| clear - Na; intros X'; apply Na; right; exact X']. }
      { intros a X'. unfold SB. destruct X' as [X'|X']; [left; clear - X'; lia| right; clear - X'; lia]. }
      { intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvSW_0). vm_compute. reflexivity. }
      keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 Hn26 LEN SLEN SBYT PT0 PT1 PT2 PTF PT4 PTA LOC DEF6 ACC6 BYT6 VT E1 E10 E11 E12 E14 Cn Cp SHa SHb.
      intros M7 md7 VIS7 HID7 MGM7 FR7w MID.
      entry_facts. frame_facts. piece_ctx MID. vis_amid BI Hi MVi. pose proof GFR as (GF1 & GF2 & GF3 & _).
      assert (EV7 : MVi = M7v) by (unfold MVi; first [rewrite HID7 | unfold Hi; rewrite HID7]; exact VIS7).
      assert (Cp' : L5.u64_at RSEGS M7 (F + 224) ptr) by (apply (proj1 (L5A.u64_at_vis Hi M7 (F + 224) ptr (L5A.avis_sub Hi F 512 (F + 224) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))); fold MVi; rewrite EV7; exact Cp).
      assert (Cn' : L5.u64_at RSEGS M7 (F + 232) n) by (apply (proj1 (L5A.u64_at_vis Hi M7 (F + 232) n (L5A.avis_sub Hi F 512 (F + 232) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))); fold MVi; rewrite EV7; exact Cn).
      assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
      assert (SHa' : L5.u8_at RSEGS M7 (F / 8 + 2147450908) 0) by (apply (proj1 (L5A.u8_at_vis Hi M7 (F / 8 + 2147450908) 0 (L5A.avis_sub Hi (F / 8 + SB) 64 (F / 8 + 2147450908) 1 VSHi ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - D1; lia) ltac:(clear - D2; lia))); fold MVi; rewrite EV7; exact SHa).
      assert (SHb' : L5.u8_at RSEGS M7 (F / 8 + 2147450909) 0) by (apply (proj1 (L5A.u8_at_vis Hi M7 (F / 8 + 2147450909) 0 (L5A.avis_sub Hi (F / 8 + SB) 64 (F / 8 + 2147450909) 1 VSHi ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - D1; lia) ltac:(clear - D2; lia))); fold MVi; rewrite EV7; exact SHb).
      assert (ACCsv : PMSPA.accA M7 (F + 224) 16).
      { intros a Ha. left. unfold byte_at, S.
        destruct (Z_lt_le_dec a (F + 232)) as [Xa|Xa].
        - rewrite (div8_off F a 28 (proj1 GF8)) by (clear - Ha Xa; lia). unfold SB. replace (F / 8 + 28 + 2147450880) with (F / 8 + 2147450908) by (clear; lia).
          apply (L5ADHR.byte_of_u8 M7 _ 0 SHa'); clear - D1 D2; lia.
        - rewrite (div8_off F a 29 (proj1 GF8)) by (clear - Ha Xa; lia). unfold SB. replace (F / 8 + 29 + 2147450880) with (F / 8 + 2147450909) by (clear; lia).
          apply (L5ADHR.byte_of_u8 M7 _ 0 SHb'); clear - D1 D2; lia. }
      assert (APF : F + 224 + 16 <= fb \/ fb + 2048 <= F + 224).
      { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & WFn & _).
        destruct (WFn (F, 3, sp - 128 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF0).
        assert (Iin : In (fb, 5, rs) (ff_remove F FF' ++ LK4)) by (apply in_or_app; left; unfold FF'; cbn [ff_remove ff_addr fst snd]; rewrite Z.eqb_refl; exact Hfb).
        pose proof (APF0 _ Iin) as APF1. cbn [ff_addr ff_class fst snd] in APF1. change (ff_bytes 5) with 2048 in APF1. change (ff_bytes 3) with 512 in APF1. clear - APF1. lia. }
      assert (AG67 : forall i, ptr <= i < ptr + n -> M7 (Z_to_bv 64 i) = M6 (Z_to_bv 64 i)).
      { intros i Hi'. apply FR7w; [clear - Hi' PT0 PT2; lia|]. intros [X'|X']; [clear - Hi' X' PTF; lia| clear - Hi' X' PTA PT1 D1 D2 GF1 GF2; lia]. }
      assert (BYT7 : L5.bytes_at RSEGS M7 ptr (UbjRef.slice p pos1 n)) by (apply (L5C.bytes_at_agree RSEGS M6 M7); [rewrite SLEN; exact AG67| exact PT0| rewrite SLEN; clear - PT2; lia| exact BYT6]).
      assert (DEF7 : L5.defined M7 ptr n) by exact (L5.defined_grows M6 M7 ptr n MGM7 DEF6).
      assert (ACC7 : PMSPA.accA M7 ptr n).
      { apply (PMFA.accA_agree M6 M7 ptr n); [| exact ACC6]. intros x Hx. unfold S, SB. apply FR7w; [clear - Hx PT0 PT2; lia|].
        intros [X'|X']; [clear - Hx X' PT0 PT2 GF1 GFBIG; lia|]. assert (XD : x / 8 <> F / 8 + 28 /\ x / 8 <> F / 8 + 29).
        { clear - Hx PTF PT1 GF8. destruct PTF as [Y|Y]; [pose proof (Z.div_le_mono x (F - 1) 8 ltac:(lia) ltac:(lia)) as DM| pose proof (Z.div_le_mono (F + 512) x 8 ltac:(lia) ltac:(lia)) as DM];
             rewrite <- (proj1 GF8) in DM at 1 || idtac; [replace (F / 8 * 8 - 1) with (7 + (F / 8 - 1) * 8) in DM by lia; rewrite Z.div_add in DM by lia; lia| ].
             rewrite <- (proj1 GF8) in DM. replace (F / 8 * 8 + 512) with ((F / 8 + 64) * 8) in DM by lia. rewrite Z.div_mul in DM by lia. lia. }
        clear - X' XD. lia. }
      keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 Hn26 LEN SLEN SBYT PT0 PT1 PT2 LOC VT MID E1 E10 E11 E12 E14  Cp' Cn' ACCsv APF BYT7 DEF7 ACC7. entry_facts. frame_facts.
      pose proof VS as SPEC. unfold PECSA.v_string_spec, PECSPA.v_string_spec in SPEC.
      apply (call_slot (Z * list Z) (pe_string EE) (PECSPA.args_str RSEGS AD) (fun _ => PECSPA.mp_enc) (fun d _ X0 => e_string (UbjRef.utf8_valid (snd d)) (Z.of_nat (length (snd d))) X0) SPEC
               (ptr, UbjRef.slice p pos1 n) 0xb48ec fx7 R7 M7 md7 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X) MID E1 ltac:(split; [clear; lia| reflexivity]) E10).
      { unfold PECSPA.args_str, PECSPA.args_sv. cbn [fst snd]. rewrite L5K.rl11, L5K.rl12, L5K.rl14. rewrite SLEN.
        split; [| split; [exact E14| exists 0; split; [clear; lia| exact E12]]].
        exists (F + 224). split; [exact E11|]. split; [replace (F + 224) with (F / 8 * 8 + 28 * 8) by (clear - GF8; destruct GF8 as (X' & _); lia); rewrite Z_mod_plus_full; apply Z_mod_mult|].
        split; [exists (F, 3, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 3) with 512; clear; lia]|].
        split; [exact ACCsv|]. split; [exact APF|]. split; [exact Cp'|]. split; [replace (F + 224 + 8) with (F + 232) by (clear; lia); exact Cn'|].
        split; [exact BYT7|]. split; [exact SBYT|]. split; [clear - Hn26; lia|]. split; [exact DEF7|]. split; [exact ACC7|].
        destruct LOC as [[E0 En0]|[BB|[T1 T2]]]; [right; right; left; split; [exact E0| rewrite En0 in SLEN |- *; destruct (UbjRef.slice p pos1 0); [reflexivity| exfalso; cbn in SLEN; clear - SLEN; lia]]
          | left; exact BB| right; left; split; [exact T1| exact T2]]. }
      { unfold PECSPA.mp_enc in MPE |- *. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. exact MPE. }
      { cbn [snd]. rewrite SLEN, VT. pose proof NB as NB'. rewrite Et, PECRVD.rv_S in NB'. unfold PECRVD.str_arm in NB'. rewrite GLd, EX in NB'. replace (blen p <? pos1 + n) with false in NB' by (symmetry; apply Z.ltb_ge; exact LEN). rewrite VT in NB'. cbn [negb andb] in NB'. unfold PECRVD.fin in NB'. destruct (s_ec (w_more true (e_string true n (w_pos (pos1 + n) X)))); cbn [s_bad w_more] in NB'; exact NB'. }
      { cbn [snd]. rewrite SLEN, VT. pose proof HB as HB'. rewrite Et, PECRVD.rv_S in HB'. unfold PECRVD.str_arm in HB'. rewrite GLd, EX in HB'. replace (blen p <? pos1 + n) with false in HB' by (symmetry; apply Z.ltb_ge; exact LEN). rewrite VT in HB'. cbn [negb andb] in HB'. unfold PECRVD.fin in HB'. destruct (s_ec (w_more true (e_string true n (w_pos (pos1 + n) X)))); cbn [s_hi w_more] in HB'; exact HB'. }
      intros fx8 R8 M8 md8 LK8 Aw8 en8 k8 e8 cr8 RP8 MID8 KP8. cbn [snd] in MID8. rewrite SLEN, VT in MID8.
      keep_only MORE DONE PPOS Et GLd EX LEN VT  MID8. rename MID8 into MID.
      entry_facts. frame_facts. piece_ctx MID.
      pz PEARVP5.arvZS_conc fx8 R8 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
      destruct PZ as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & _ & _ & _ & MO9 & _ & _).
      apply (tail_J fx8 R8 M8 md8 LK8 Aw8 cr8 si4 sm4 en8 k8 e8 (e_string true n (w_pos (pos1 + n) X)) fx9 R9 M9v 0xb48ec MID MS9 MG9).
      - intros i Hi' N1 N2. apply FRZ9; [exact Hi'| exact N1| clear - N2; lia| clear - N2; lia].
      - intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZS). vm_compute. reflexivity.
      - replace (PM.p_more si4) with 1; [exact MO9|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
        rewrite Lmore. rewrite PECRVD.e_string_more. cbn [s_more w_pos]. rewrite MORE. reflexivity.
      - rewrite Et, PECRVD.rv_S. unfold PECRVD.str_arm. rewrite GLd, EX. replace (blen p <? pos1 + n) with false by (symmetry; apply Z.ltb_ge; exact LEN). rewrite VT. cbn [negb andb]. rewrite PECRVD.w_more_same; [reflexivity|]. rewrite PECRVD.e_string_more. cbn [s_more w_pos]. exact MORE.

    *
      assert (Nv : v <> 0) by (clear - CQ7 Hv; intros E; subst v; rewrite Z.sub_0_r, Z.mod_0_l in CQ7 by lia; lia).
      assert (VF : UbjRef.utf8_valid (UbjRef.slice p pos1 n) = false) by (destruct (UbjRef.utf8_valid (UbjRef.slice p pos1 n)) eqn:EV; [exfalso; apply Nv; apply HV; reflexivity| reflexivity]).
      apply (amid_pieceFW fx6 R6 M6 md6 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X) fx7 R7 0xb3cb8 (pa_make_ec AD) M7v (fun a => (F + 224 <= a < F + 224 + 16) \/ (F / 8 + 2147450880 + 28 <= a < F / 8 + 2147450880 + 28 + 2)) MID MS7 MG7).
      { intros a Ha Na. apply FRZ7; [exact Ha| clear - Na; intros X'; apply Na; left; exact X'| clear - Na; intros X'; apply Na; right; exact X']. }
      { intros a X'. unfold SB. destruct X' as [X'|X']; [left; clear - X'; lia| right; clear - X'; lia]. }
      { intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvSW_1). vm_compute. reflexivity. }
      keep_only Et GLd EX LEN VF E1 E10 E11.
      intros M7 md7 VIS7 HID7 MGM7 FR7w MID.
      apply (call_mkec 0xb3ccc 7 fx7 R7 M7 md7 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X) MID E1 ltac:(split; [clear; lia| reflexivity]) E10 E11 ltac:(clear; lia)).
      clear MID. intros fx8 R8 M8 md8 LK8 Aw8 RP8 MID.
      entry_facts. frame_facts. piece_ctx MID.
      pz PEARVP6.arvESv_conc fx8 R8 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
      destruct PZ as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & _ & _ & MO9).
      apply (finish 0 (r_fail X) fx8 R8 M8 md8 LK8 Aw8 cr4 si4 sm4 eni ki true _ fx9 R9 M9v 0xb3ccc MID MS9 MG9).
      -- intros i Hi' N1 _. apply FRZ9; [exact Hi'| exact N1].
      -- intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvESv). vm_compute. reflexivity.
      -- exact MO9.
      -- left; reflexivity.
      -- rewrite Et, PECRVD.rv_S. unfold PECRVD.str_arm. rewrite GLd, EX. replace (blen p <? pos1 + n) with false by (symmetry; apply Z.ltb_ge; exact LEN). rewrite VF. cbn [negb andb Z.eqb Pos.eqb]. reflexivity.
      -- pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
         apply (PECRVD.clink_but_pos p (r_fail X) (w_more false (w_ec true (w_pos (pos1 + n) X)))); [reflexivity| | exact (clink_fail _ _ _ _ _ CLm)].
         apply PECRVD.but_pos_r_fail. apply PECRVD.but_pos_sym. apply PECRVD.but_pos_w_pos.
      -- reflexivity.
  +
    assert (SHORT : pos1 + n > blen p).
    {{ destruct (Z.eq_dec n2 n) as [E|N]; [exfalso| clear - N Hn Hn2 NMIN; lia]. rewrite E in CQ5. rewrite Z.sub_diag, Z.mod_0_l in CQ5 by (clear; lia). clear - CQ5; lia. }}
    assert (E5 : M5v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr4 Aw4 M4 md4 fx4 fx5 R4 0xb3ca8 R5 (pa_make_ec AD) MVi K HHi AMi MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx5 R5 M4 md5 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n2) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 md5 MID); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvSF_1). vm_compute. reflexivity. }
    keep_only Et GLd EX SHORT MID5 Q1 Q10 Q11. rename MID5 into MID.
    apply (call_mkec 0xb464c 1 fx5 R5 M4 md5 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n2) X) MID Q1 ltac:(split; [clear; lia| reflexivity]) Q10 Q11 ltac:(clear; lia)).
    clear MID. intros fx6 R6 M6 md6 LK6 Aw6 RP6 MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP6.arvESs_conc fx6 R6 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & MO7).
    apply (finish 0 (r_fail X) fx6 R6 M6 md6 LK6 Aw6 cr4 si4 sm4 eni ki true _ fx7 R7 M7v 0xb464c MID MS7 MG7).
    * intros i Hi' N1 _. apply FRZ7; [exact Hi'| exact N1].
    * intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvESs). vm_compute. reflexivity.
    * exact MO7.
    * left; reflexivity.
    * rewrite Et, PECRVD.rv_S. unfold PECRVD.str_arm. rewrite GLd, EX. replace (blen p <? pos1 + n) with true by (symmetry; apply Z.ltb_lt; clear - SHORT; lia). reflexivity.
    * pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      apply (PECRVD.clink_but_pos p (r_fail X) (w_more false (w_ec true (w_pos (pos1 + n2) X)))); [reflexivity| | exact (clink_fail _ _ _ _ _ CLm)].
      apply PECRVD.but_pos_r_fail. apply PECRVD.but_pos_sym. apply PECRVD.but_pos_w_pos.
    * reflexivity.
Qed.

Lemma arm_H fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 72 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTH_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11).
  assert (E1 : M1v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ1; exact Ha). subst M1v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx1 Ri 0xb3aec R1 (pa_get_length AD) MVi K HHi AMi MS1 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1 : M1 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  assert (MID1 : amid fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx1 R1 md1 MID); [| exact HH1| exact AM1| exact MRT1].
    intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTH). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et MID1 Y1 Y10 Y11. rename MID1 into MID.
  pose proof POK as (BOK & _). pose proof MP as ((PRE & _) & _ & HALT & _).
  apply (call_gl 0xb3cf8 fx1 R1 Mi md1 LKi Awi cri si smi eni ki ei X MID Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11).
  { unfold PECSPA.mp_gl. split; [exact BOK|]. split; [exact PPOS|]. split; [exact MORE|]. split; [exact DONE|]. split; [exact HALT| exact XBAD]. }
  clear MID. intros fx2 R2 Mg md2 LKg Aw2 cr2 si2 smi2 e2 RP2 RET2 MID ETB ETG EB EK FSH2 FDK2.
  unfold PECSPA.gl_post in MID. unfold PECSPA.gl_ret in RET2.
  destruct (UbjRef.get_length p (s_pos X)) as [[n pos1]|] eqn:GLd.
  2: {
       keep_only Et GLd MID. entry_facts. frame_facts. piece_ctx MID.
       destruct (ec_vis1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID eq_refl) as (v & Hv & ECU). fold Hi in ECU. fold MVi in ECU. assert (Bv : 0 <= v < 2 ^ 64) by (clear - Hv; lia). assert (Hv' : 1 <= v <= 64) by exact Hv.
       pose proof (bv_unsigned_in_range 64 (getr R2 (reg 10))) as B10v. change (bv_modulus 64) with (2 ^ 64) in B10v.
       assert (W10 : getr R2 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R2 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
       pz PEARVP4.arvHGe_conc fx2 R2 (bv_unsigned (getr R2 (reg 10))) 0 0 v 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - B10v; lia]).
       destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & _ & _ & _).
       apply (tail_G fx2 R2 Mg md2 LKg Aw2 cr2 si2 smi2 eni ki e2 (r_fail X) fx3 R3 M3v 0xb3cf8 MID MS3 MG3 FRZ3); [| reflexivity| rewrite Et, PECRVD.rv_H; unfold PECRVD.str_arm; rewrite GLd; reflexivity].
       intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvHGe). vm_compute. reflexivity. }
  pose proof (get_length_some p (s_pos X) n pos1 BOK ltac:(clear - PPOS; lia) GLd) as (Hn & Hpos1 & _).
  destruct (s_ec X) eqn:EX.
  {
    keep_only Et GLd EX Hn MID RET2. entry_facts. frame_facts. piece_ctx MID.
    destruct (ec_vis1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(cbn; exact EX)) as (v & Hv & ECU). fold Hi in ECU. fold MVi in ECU. assert (Bv : 0 <= v < 2 ^ 64) by (clear - Hv; lia). assert (Hv' : 1 <= v <= 64) by exact Hv.
    rewrite L5K.rl10 in RET2. assert (Hn64 : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
    pz PEARVP4.arvHGe_conc fx2 R2 n 0 0 v 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Hn64; lia]).
    destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & _ & _ & _).
    apply (tail_G fx2 R2 Mg md2 LKg Aw2 cr2 si2 smi2 eni ki e2 (w_pos pos1 X) fx3 R3 M3v 0xb3cf8 MID MS3 MG3 FRZ3); [| cbn; exact EX| rewrite Et, PECRVD.rv_H; unfold PECRVD.str_arm; rewrite GLd, EX; reflexivity].
    intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvHGe). vm_compute. reflexivity. }

  keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 BOK MID RET2 ETB ETG EB EK. entry_facts. frame_facts. piece_ctx MID.
  pose proof (ec_vis0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ltac:(cbn; exact EX)) as ECU. fold Hi in ECU. fold MVi in ECU.
  rewrite L5K.rl10 in RET2. assert (Hn64 : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
  pz PEARVP4.arvHG0_conc fx2 R2 n 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Hn64; lia]).
  destruct PZ as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10 & Z11 & Z12 & Zs).
  assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKg cr2 Aw2 Mg md2 fx2 fx3 R2 0xb3cf8 R3 (pa_read_span AD) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
  assert (E3 : M3 = Mg) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
  assert (MID3 : amid fx3 R3 Mg md3 LKg Aw2 cr2 si2 smi2 eni ki e2 (w_pos pos1 X)).
  { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
    intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvHG0). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 BOK MID3 ETB ETG EB EK Z1 Z10 Z11 Z12 Zs. rename MID3 into MID.
  apply (call_span n 0xb3d24 fx3 R3 Mg md3 LKg Aw2 cr2 si2 smi2 eni ki e2 (w_pos pos1 X) MID ltac:(cbn; exact MORE) ltac:(cbn; exact DONE) ltac:(cbn [s_pos w_pos]; clear - Hpos1 PPOS; lia)
           Z1 ltac:(split; [clear; lia| reflexivity]) Z10 Z11 Z12 ltac:(clear - Hn; lia)).
  clear MID. intros fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 ptr n2 RP4 V10 V11 Hn2 Hn26 LOC DEF4 ACC4 BYT4 NMIN MID EB4 EK4. cbn [s_pos w_pos] in BYT4, NMIN, MID.
  assert (WW : w_pos (pos1 + n2) (w_pos pos1 X) = w_pos (pos1 + n2) X) by (destruct X; reflexivity). rewrite WW in MID. clear WW.
  assert (Ss : getr R4 (reg 25) = Z_to_bv 64 n) by (rewrite (L5SAR.cs_of_preserved _ R4 25 RP4) by inl; exact Zs).
  entry_facts. frame_facts. piece_ctx MID.
  assert (PTRR : 0 <= ptr < 2 ^ 64).
  { destruct LOC as [[-> ->]|[(B & m & HinB & HB1 & HB2)|[T1 T2]]].
    - clear. lia.
    - pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRB. assert (HinB' : In (B, m) (PEC.owned si4 eni ki ++ LBX)) by (unfold PEC.owned; apply in_or_app; left; apply in_or_app; left; exact HinB).
      destruct (BRB _ HinB') as (B0 & B47). cbn [fst snd] in B0, B47. clear - B0 B47 HB1 HB2 Hn2. lia.
    - clear - T1 T2 Eotb Eop O1 O3 Hn2. lia. }
  assert (Hn264 : 0 <= n2 < 2 ^ 64) by (clear - Hn2 Hn; lia).
  pz PEARVP4.arvHF_conc fx4 R4 n ptr n2 0 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hn; lia| clear - PTRR; lia| clear - Hn264; lia]).
  destruct PB as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & [(MS5 & KS5 & Q1 & Q11 & Q23 & CQ5) | (MS5 & KS5 & Q1 & Q10 & Q11 & CQ5)]).
  +
    assert (En : n2 = n).
    { clear - CQ5 Hn Hn2. destruct (Z.eq_dec n2 n) as [E|N]; [exact E| exfalso].
      replace (n2 - n) with ((n2 - n + 2 ^ 64) + (-1) * 2 ^ 64) in CQ5 by lia. rewrite Z.mod_add in CQ5 by lia. rewrite Z.mod_small in CQ5 by lia. lia. }
    rewrite En in *. clear En CQ5.
    assert (LEN : pos1 + n <= blen p) by (clear - NMIN Hn Hpos1; lia).
    assert (SLEN : Z.of_nat (length (UbjRef.slice p pos1 n)) = n) by (apply PECRVD.slice_length; clear - Hn Hpos1 LEN PPOS; lia).
    assert (SBYT : Forall (fun b => 0 <= b < 256) (UbjRef.slice p pos1 n)) by (apply PECRVD.slice_bytes; exact BOK).
    pose proof GFR as (GF1 & GF2 & GF3 & _).
    assert (PTR47 : 0 <= ptr /\ (n = 0 \/ 0 < ptr) /\ ptr + n <= 2 ^ 47 /\ (ptr + n <= F \/ F + 512 <= ptr) /\ (n = 0 \/ ptr + n <= ahl_ceil ar) /\ (n = 0 \/ ptr + n <= 2147446784 \/ 17594333495296 <= ptr)).
    { destruct LOC as [[E0 En0]|[(B & m & HinB & HB1 & HB2)|[T1 T2]]].
      - rewrite E0, En0. clear - GF1. lia.
      - pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRB. assert (HinB' : In (B, m) (PEC.owned si4 eni ki ++ LBX)) by (unfold PEC.owned; apply in_or_app; left; apply in_or_app; left; exact HinB).
        destruct (BRB _ HinB') as (B0 & B47). cbn [fst snd] in B0, B47.
        pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WBi & _). destruct (WBi _ HinB') as ((W0' & W1' & W2' & W3' & W4' & W5') & _ & _ & _ & _ & FA & _). cbn [fst snd] in W0', W1', W2', W3', W4', W5'.
        destruct (FA (F, 3, sp - 128 + 32) (or_introl eq_refl)) as [Z'|Z']; cbn [ff_addr ff_class fst snd] in Z'; change (ff_bytes 3) with 512 in Z';
          (refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); [clear - B0 HB1; lia| right; clear - W0' HB1; lia| clear - B47 HB2; lia| clear - Z' HB1 HB2 Hn; lia| right; clear - W0' W1' W2' W3' W4' W5' HB2 SLO SHI SPT; lia
             | right; unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in W5'; clear - W5' HB1 HB2; lia]).
      - refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); [clear - T1 Eotb Eop O1; lia| right; clear - T1 Eotb Eop O1; lia| clear - T2 Eotb Eop O3; lia| lazymatch goal with H : op + 384 <= F \/ _ |- _ => clear - T1 T2 Eotb H Hn; lia end
          | right; clear - T2 Eotb Eop F2 FSCEIL; lia| right; clear - T1 T2 Eotb Eop F1 F2 FSAPP; lia]. }
    destruct PTR47 as (PT0 & PT1 & PT2 & PTF & PT4 & PTA).
    assert (E5 : M5v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr4 Aw4 M4 md4 fx4 fx5 R4 0xb3d24 R5 (pa_is_base10 AD) MVi K HHi AMi MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx5 R5 M4 md5 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 md5 MID); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvHF_0). vm_compute. reflexivity. }
    keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 BOK Hn26 LEN SLEN SBYT PT0 PT1 PT2 PTF PT4 PTA LOC DEF4 ACC4 BYT4 V10 MID5 Q1 Q11 Q23 KS5 Ss. rename MID5 into MID.

    apply (call_b10 ptr n 0xb3d34 fx5 R5 M4 md5 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X) MID Q1 ltac:(split; [clear; lia| reflexivity])
             ltac:(rewrite (KS5 10%nat) by inl; exact V10) Q11 ltac:(clear - Hn Hn26; lia) PT0 PT1 PT2 DEF4 ACC4
             ltac:(destruct LOC as [[E0 En0]|[(Bb & mb & Hinb & Xb1 & Xb2)|TT]]; [left; exact En0| right; left; exists Bb, mb; split; [unfold PEC.owned; apply in_or_app; left; apply in_or_app; left; exact Hinb| split; [exact Xb1| exact Xb2]]| right; right; left; exact TT])).
    clear MID. intros fx6 R6 M6 md6 RP6 MG6 FRZ6 MID.
    assert (S25v : getr R6 (reg 25) = Z_to_bv 64 n) by (rewrite (L5SAR.cs_of_preserved _ R6 25 RP6) by inl; rewrite (KS5 25%nat) by inl; exact Ss).
    assert (S23v : getr R6 (reg 23) = Z_to_bv 64 ptr) by (rewrite (L5SAR.cs_of_preserved _ R6 23 RP6) by inl; exact Q23).
    entry_facts. frame_facts. piece_ctx MID.
    assert (BYT6 : L5.bytes_at RSEGS M6 ptr (UbjRef.slice p pos1 n)).
    { apply (L5C.bytes_at_agree RSEGS M4 M6); [| exact PT0| rewrite SLEN; clear - PT2; lia| exact BYT4]. rewrite SLEN. intros i Hi'. apply FRZ6; [clear - Hi' PT0 PT2; lia|]. intros X'. clear - Hi' X' PT4 GSLO. lia. }
    assert (DEF6 : L5.defined M6 ptr n) by exact (L5.defined_grows M4 M6 ptr n MG6 DEF4).
    assert (ACC6 : PMSPA.accA M6 ptr n).
    { apply (PMFA.accA_agree M4 M6 ptr n); [| exact ACC4]. intros x Hx. unfold S, SB. apply FRZ6; [clear - Hx PT0 PT2; lia| clear - Hx PT0 PT2 GSLO GSPT; lia]. }
    pose proof (bv_unsigned_in_range 64 (getr R6 (reg 10))) as B10v. change (bv_modulus 64) with (2 ^ 64) in B10v.
    assert (W10 : getr R6 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R6 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (PTRR : 0 <= ptr < 2 ^ 64) by (clear - PT0 PT2 Hn; lia). assert (Hn64 : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
    destruct (Z.eq_dec (bv_unsigned (getr R6 (reg 10))) 0) as [V0|VNZ].
    *
      rewrite V0 in W10.
      pz PEARVP4.arvHK3_conc fx6 R6 n ptr 0 0 0 as PB. L5SAR.feed PB fcl.
      destruct PB as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & E1 & E10 & E11 & E12 & _ & E14 & _ & E23 & E24 & Cn & Cp & SHb & SHa & _ & _).
      apply (amid_pieceFW fx6 R6 M6 md6 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X) fx7 R7 0xb3d34 (pe_string EE) M7v (fun a => (F + 288 <= a < F + 288 + 16) \/ (F / 8 + 2147450880 + 36 <= a < F / 8 + 2147450880 + 36 + 2)) MID MS7 MG7).
      { intros a Ha Na. apply FRZ7; [exact Ha| clear - Na; intros X'; apply Na; left; exact X'| clear - Na; intros X'; apply Na; right; exact X']. }
      { intros a X'. unfold SB. destruct X' as [X'|X']; [left; clear - X'; lia| right; clear - X'; lia]. }
      { intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvHK3). vm_compute. reflexivity. }
      keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 Hn26 LEN SLEN SBYT PT0 PT1 PT2 PTF PT4 PTA LOC DEF6 ACC6 BYT6 E1 E10 E11 E12 E14 E23 E24 Cn Cp SHa SHb.
      intros M7 md7 VIS7 HID7 MGM7 FR7w MID.
      entry_facts. frame_facts. piece_ctx MID. vis_amid BI Hi MVi. pose proof GFR as (GF1 & GF2 & GF3 & _).
      assert (EV7 : MVi = M7v) by (unfold MVi; first [rewrite HID7 | unfold Hi; rewrite HID7]; exact VIS7).
      assert (Cp' : L5.u64_at RSEGS M7 (F + 288) ptr) by (apply (proj1 (L5A.u64_at_vis Hi M7 (F + 288) ptr (L5A.avis_sub Hi F 512 (F + 288) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))); fold MVi; rewrite EV7; exact Cp).
      assert (Cn' : L5.u64_at RSEGS M7 (F + 296) n) by (apply (proj1 (L5A.u64_at_vis Hi M7 (F + 296) n (L5A.avis_sub Hi F 512 (F + 296) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))); fold MVi; rewrite EV7; exact Cn).
      assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
      assert (SHa' : L5.u8_at RSEGS M7 (F / 8 + 2147450916) 0) by (apply (proj1 (L5A.u8_at_vis Hi M7 (F / 8 + 2147450916) 0 (L5A.avis_sub Hi (F / 8 + SB) 64 (F / 8 + 2147450916) 1 VSHi ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - D1; lia) ltac:(clear - D2; lia))); fold MVi; rewrite EV7; exact SHa).
      assert (SHb' : L5.u8_at RSEGS M7 (F / 8 + 2147450917) 0) by (apply (proj1 (L5A.u8_at_vis Hi M7 (F / 8 + 2147450917) 0 (L5A.avis_sub Hi (F / 8 + SB) 64 (F / 8 + 2147450917) 1 VSHi ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - D1; lia) ltac:(clear - D2; lia))); fold MVi; rewrite EV7; exact SHb).
      assert (ACCsv : PMSPA.accA M7 (F + 288) 16).
      { intros a Ha. left. unfold byte_at, S.
        destruct (Z_lt_le_dec a (F + 296)) as [Xa|Xa].
        - rewrite (div8_off F a 36 (proj1 GF8)) by (clear - Ha Xa; lia). unfold SB. replace (F / 8 + 36 + 2147450880) with (F / 8 + 2147450916) by (clear; lia).
          apply (L5ADHR.byte_of_u8 M7 _ 0 SHa'); clear - D1 D2; lia.
        - rewrite (div8_off F a 37 (proj1 GF8)) by (clear - Ha Xa; lia). unfold SB. replace (F / 8 + 37 + 2147450880) with (F / 8 + 2147450917) by (clear; lia).
          apply (L5ADHR.byte_of_u8 M7 _ 0 SHb'); clear - D1 D2; lia. }
      assert (APF : F + 288 + 16 <= fb \/ fb + 2048 <= F + 288).
      { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & WFn & _).
        destruct (WFn (F, 3, sp - 128 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF0).
        assert (Iin : In (fb, 5, rs) (ff_remove F FF' ++ LK4)) by (apply in_or_app; left; unfold FF'; cbn [ff_remove ff_addr fst snd]; rewrite Z.eqb_refl; exact Hfb).
        pose proof (APF0 _ Iin) as APF1. cbn [ff_addr ff_class fst snd] in APF1. change (ff_bytes 5) with 2048 in APF1. change (ff_bytes 3) with 512 in APF1. clear - APF1. lia. }
      assert (AG67 : forall i, ptr <= i < ptr + n -> M7 (Z_to_bv 64 i) = M6 (Z_to_bv 64 i)).
      { intros i Hi'. apply FR7w; [clear - Hi' PT0 PT2; lia|]. intros [X'|X']; [clear - Hi' X' PTF; lia| clear - Hi' X' PTA PT1 D1 D2 GF1 GF2; lia]. }
      assert (BYT7 : L5.bytes_at RSEGS M7 ptr (UbjRef.slice p pos1 n)) by (apply (L5C.bytes_at_agree RSEGS M6 M7); [rewrite SLEN; exact AG67| exact PT0| rewrite SLEN; clear - PT2; lia| exact BYT6]).
      assert (DEF7 : L5.defined M7 ptr n) by exact (L5.defined_grows M6 M7 ptr n MGM7 DEF6).
      assert (ACC7 : PMSPA.accA M7 ptr n).
      { apply (PMFA.accA_agree M6 M7 ptr n); [| exact ACC6]. intros x Hx. unfold S, SB. apply FR7w; [clear - Hx PT0 PT2; lia|].
        intros [X'|X']; [clear - Hx X' PT0 PT2 GF1 GFBIG; lia|]. assert (XD : x / 8 <> F / 8 + 36 /\ x / 8 <> F / 8 + 37).
        { clear - Hx PTF PT1 GF8. destruct PTF as [Y|Y]; [pose proof (Z.div_le_mono x (F - 1) 8 ltac:(lia) ltac:(lia)) as DM| pose proof (Z.div_le_mono (F + 512) x 8 ltac:(lia) ltac:(lia)) as DM];
             rewrite <- (proj1 GF8) in DM at 1 || idtac; [replace (F / 8 * 8 - 1) with (7 + (F / 8 - 1) * 8) in DM by lia; rewrite Z.div_add in DM by lia; lia| ].
             rewrite <- (proj1 GF8) in DM. replace (F / 8 * 8 + 512) with ((F / 8 + 64) * 8) in DM by lia. rewrite Z.div_mul in DM by lia. lia. }
        clear - X' XD. lia. }
      keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 Hn26 LEN SLEN SBYT PT0 PT1 PT2 LOC  MID E1 E10 E11 E12 E14 E23 E24 Cp' Cn' ACCsv APF BYT7 DEF7 ACC7. entry_facts. frame_facts.
      pose proof VS as SPEC. unfold PECSA.v_string_spec, PECSPA.v_string_spec in SPEC.
      apply (call_slot (Z * list Z) (pe_string EE) (PECSPA.args_str RSEGS AD) (fun _ => PECSPA.mp_enc) (fun d _ X0 => e_string (UbjRef.utf8_valid (snd d)) (Z.of_nat (length (snd d))) X0) SPEC
               (ptr, UbjRef.slice p pos1 n) 0xb47ac fx7 R7 M7 md7 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X) MID E1 ltac:(split; [clear; lia| reflexivity]) E10).
      { unfold PECSPA.args_str, PECSPA.args_sv. cbn [fst snd]. rewrite L5K.rl11, L5K.rl12, L5K.rl14. rewrite SLEN.
        split; [| split; [exact E14| exists 3; split; [clear; lia| exact E12]]].
        exists (F + 288). split; [exact E11|]. split; [replace (F + 288) with (F / 8 * 8 + 36 * 8) by (clear - GF8; destruct GF8 as (X' & _); lia); rewrite Z_mod_plus_full; apply Z_mod_mult|].
        split; [exists (F, 3, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 3) with 512; clear; lia]|].
        split; [exact ACCsv|]. split; [exact APF|]. split; [exact Cp'|]. split; [replace (F + 288 + 8) with (F + 296) by (clear; lia); exact Cn'|].
        split; [exact BYT7|]. split; [exact SBYT|]. split; [clear - Hn26; lia|]. split; [exact DEF7|]. split; [exact ACC7|].
        destruct LOC as [[E0 En0]|[BB|[T1 T2]]]; [right; right; left; split; [exact E0| rewrite En0 in SLEN |- *; destruct (UbjRef.slice p pos1 0); [reflexivity| exfalso; cbn in SLEN; clear - SLEN; lia]]
          | left; exact BB| right; left; split; [exact T1| exact T2]]. }
      { unfold PECSPA.mp_enc in MPE |- *. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. exact MPE. }
      { cbn [snd]. rewrite SLEN. pose proof NB as NB'. rewrite Et, PECRVD.rv_H in NB'. unfold PECRVD.str_arm in NB'. rewrite GLd, EX in NB'. replace (blen p <? pos1 + n) with false in NB' by (symmetry; apply Z.ltb_ge; exact LEN). cbn [Z.eqb Pos.eqb andb] in NB'. unfold PECRVD.fin in NB'. destruct (s_ec (w_more true (e_string (UbjRef.utf8_valid (UbjRef.slice p pos1 n)) n (w_pos (pos1 + n) X)))); cbn [s_bad w_more] in NB'; exact NB'. }
      { cbn [snd]. rewrite SLEN. pose proof HB as HB'. rewrite Et, PECRVD.rv_H in HB'. unfold PECRVD.str_arm in HB'. rewrite GLd, EX in HB'. replace (blen p <? pos1 + n) with false in HB' by (symmetry; apply Z.ltb_ge; exact LEN). cbn [Z.eqb Pos.eqb andb] in HB'. unfold PECRVD.fin in HB'. destruct (s_ec (w_more true (e_string (UbjRef.utf8_valid (UbjRef.slice p pos1 n)) n (w_pos (pos1 + n) X)))); cbn [s_hi w_more] in HB'; exact HB'. }
      intros fx8 R8 M8 md8 LK8 Aw8 en8 k8 e8 cr8 RP8 MID8 KP8. cbn [snd] in MID8. rewrite SLEN in MID8.
      assert (S23z : getr R8 (reg 23) = Z_to_bv 64 (op + 8)) by (rewrite (L5SAR.cs_of_preserved _ R8 23 RP8) by inl; exact E23).
      assert (S24z : getr R8 (reg 24) = Z_to_bv 64 (op + 16)) by (rewrite (L5SAR.cs_of_preserved _ R8 24 RP8) by inl; exact E24).
      keep_only MORE DONE PPOS Et GLd EX LEN  S23z S24z MID8. rename MID8 into MID.
      entry_facts. frame_facts. piece_ctx MID.
      pz PEARVP5.arvZH3_conc fx8 R8 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
      destruct PZ as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & _ & _ & _ & MO9 & _ & _).
      apply (tail_J fx8 R8 M8 md8 LK8 Aw8 cr8 si4 sm4 en8 k8 e8 (e_string (UbjRef.utf8_valid (UbjRef.slice p pos1 n)) n (w_pos (pos1 + n) X)) fx9 R9 M9v 0xb47ac MID MS9 MG9).
      - intros i Hi' N1 N2. apply FRZ9; [exact Hi'| exact N1| clear - N2; lia| clear - N2; lia].
      - intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZH3). vm_compute. reflexivity.
      - replace (PM.p_more si4) with 1; [exact MO9|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
        rewrite Lmore. rewrite PECRVD.e_string_more. cbn [s_more w_pos]. rewrite MORE. reflexivity.
      - rewrite Et, PECRVD.rv_H. unfold PECRVD.str_arm. rewrite GLd, EX. replace (blen p <? pos1 + n) with false by (symmetry; apply Z.ltb_ge; exact LEN). cbn [Z.eqb Pos.eqb andb]. rewrite PECRVD.w_more_same; [reflexivity|]. rewrite PECRVD.e_string_more. cbn [s_more w_pos]. exact MORE.

    *
      assert (VR : 1 <= bv_unsigned (getr R6 (reg 10)) <= 18446744073709551615) by (clear - B10v VNZ; lia).
      pz PEARVP4.arvHK2_conc fx6 R6 n ptr 0 (bv_unsigned (getr R6 (reg 10))) 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - B10v; lia| clear - VR; lia]).
      destruct PB as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & E1 & E10 & E11 & E12 & _ & E14 & _ & E23 & E24 & Cn & Cp & SHb & SHa & _ & _).
      apply (amid_pieceFW fx6 R6 M6 md6 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X) fx7 R7 0xb3d34 (pe_string EE) M7v (fun a => (F + 256 <= a < F + 256 + 16) \/ (F / 8 + 2147450880 + 32 <= a < F / 8 + 2147450880 + 32 + 2)) MID MS7 MG7).
      { intros a Ha Na. apply FRZ7; [exact Ha| clear - Na; intros X'; apply Na; left; exact X'| clear - Na; intros X'; apply Na; right; exact X']. }
      { intros a X'. unfold SB. destruct X' as [X'|X']; [left; clear - X'; lia| right; clear - X'; lia]. }
      { intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvHK2). vm_compute. reflexivity. }
      keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 Hn26 LEN SLEN SBYT PT0 PT1 PT2 PTF PT4 PTA LOC DEF6 ACC6 BYT6 E1 E10 E11 E12 E14 E23 E24 Cn Cp SHa SHb.
      intros M7 md7 VIS7 HID7 MGM7 FR7w MID.
      entry_facts. frame_facts. piece_ctx MID. vis_amid BI Hi MVi. pose proof GFR as (GF1 & GF2 & GF3 & _).
      assert (EV7 : MVi = M7v) by (unfold MVi; first [rewrite HID7 | unfold Hi; rewrite HID7]; exact VIS7).
      assert (Cp' : L5.u64_at RSEGS M7 (F + 256) ptr) by (apply (proj1 (L5A.u64_at_vis Hi M7 (F + 256) ptr (L5A.avis_sub Hi F 512 (F + 256) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))); fold MVi; rewrite EV7; exact Cp).
      assert (Cn' : L5.u64_at RSEGS M7 (F + 264) n) by (apply (proj1 (L5A.u64_at_vis Hi M7 (F + 264) n (L5A.avis_sub Hi F 512 (F + 264) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))); fold MVi; rewrite EV7; exact Cn).
      assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
      assert (SHa' : L5.u8_at RSEGS M7 (F / 8 + 2147450912) 0) by (apply (proj1 (L5A.u8_at_vis Hi M7 (F / 8 + 2147450912) 0 (L5A.avis_sub Hi (F / 8 + SB) 64 (F / 8 + 2147450912) 1 VSHi ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - D1; lia) ltac:(clear - D2; lia))); fold MVi; rewrite EV7; exact SHa).
      assert (SHb' : L5.u8_at RSEGS M7 (F / 8 + 2147450913) 0) by (apply (proj1 (L5A.u8_at_vis Hi M7 (F / 8 + 2147450913) 0 (L5A.avis_sub Hi (F / 8 + SB) 64 (F / 8 + 2147450913) 1 VSHi ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - D1; lia) ltac:(clear - D2; lia))); fold MVi; rewrite EV7; exact SHb).
      assert (ACCsv : PMSPA.accA M7 (F + 256) 16).
      { intros a Ha. left. unfold byte_at, S.
        destruct (Z_lt_le_dec a (F + 264)) as [Xa|Xa].
        - rewrite (div8_off F a 32 (proj1 GF8)) by (clear - Ha Xa; lia). unfold SB. replace (F / 8 + 32 + 2147450880) with (F / 8 + 2147450912) by (clear; lia).
          apply (L5ADHR.byte_of_u8 M7 _ 0 SHa'); clear - D1 D2; lia.
        - rewrite (div8_off F a 33 (proj1 GF8)) by (clear - Ha Xa; lia). unfold SB. replace (F / 8 + 33 + 2147450880) with (F / 8 + 2147450913) by (clear; lia).
          apply (L5ADHR.byte_of_u8 M7 _ 0 SHb'); clear - D1 D2; lia. }
      assert (APF : F + 256 + 16 <= fb \/ fb + 2048 <= F + 256).
      { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & WFn & _).
        destruct (WFn (F, 3, sp - 128 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF0).
        assert (Iin : In (fb, 5, rs) (ff_remove F FF' ++ LK4)) by (apply in_or_app; left; unfold FF'; cbn [ff_remove ff_addr fst snd]; rewrite Z.eqb_refl; exact Hfb).
        pose proof (APF0 _ Iin) as APF1. cbn [ff_addr ff_class fst snd] in APF1. change (ff_bytes 5) with 2048 in APF1. change (ff_bytes 3) with 512 in APF1. clear - APF1. lia. }
      assert (AG67 : forall i, ptr <= i < ptr + n -> M7 (Z_to_bv 64 i) = M6 (Z_to_bv 64 i)).
      { intros i Hi'. apply FR7w; [clear - Hi' PT0 PT2; lia|]. intros [X'|X']; [clear - Hi' X' PTF; lia| clear - Hi' X' PTA PT1 D1 D2 GF1 GF2; lia]. }
      assert (BYT7 : L5.bytes_at RSEGS M7 ptr (UbjRef.slice p pos1 n)) by (apply (L5C.bytes_at_agree RSEGS M6 M7); [rewrite SLEN; exact AG67| exact PT0| rewrite SLEN; clear - PT2; lia| exact BYT6]).
      assert (DEF7 : L5.defined M7 ptr n) by exact (L5.defined_grows M6 M7 ptr n MGM7 DEF6).
      assert (ACC7 : PMSPA.accA M7 ptr n).
      { apply (PMFA.accA_agree M6 M7 ptr n); [| exact ACC6]. intros x Hx. unfold S, SB. apply FR7w; [clear - Hx PT0 PT2; lia|].
        intros [X'|X']; [clear - Hx X' PT0 PT2 GF1 GFBIG; lia|]. assert (XD : x / 8 <> F / 8 + 32 /\ x / 8 <> F / 8 + 33).
        { clear - Hx PTF PT1 GF8. destruct PTF as [Y|Y]; [pose proof (Z.div_le_mono x (F - 1) 8 ltac:(lia) ltac:(lia)) as DM| pose proof (Z.div_le_mono (F + 512) x 8 ltac:(lia) ltac:(lia)) as DM];
             rewrite <- (proj1 GF8) in DM at 1 || idtac; [replace (F / 8 * 8 - 1) with (7 + (F / 8 - 1) * 8) in DM by lia; rewrite Z.div_add in DM by lia; lia| ].
             rewrite <- (proj1 GF8) in DM. replace (F / 8 * 8 + 512) with ((F / 8 + 64) * 8) in DM by lia. rewrite Z.div_mul in DM by lia. lia. }
        clear - X' XD. lia. }
      keep_only MORE DONE PPOS MPE XBAD Et GLd EX Hn Hpos1 Hn26 LEN SLEN SBYT PT0 PT1 PT2 LOC  MID E1 E10 E11 E12 E14 E23 E24 Cp' Cn' ACCsv APF BYT7 DEF7 ACC7. entry_facts. frame_facts.
      pose proof VS as SPEC. unfold PECSA.v_string_spec, PECSPA.v_string_spec in SPEC.
      apply (call_slot (Z * list Z) (pe_string EE) (PECSPA.args_str RSEGS AD) (fun _ => PECSPA.mp_enc) (fun d _ X0 => e_string (UbjRef.utf8_valid (snd d)) (Z.of_nat (length (snd d))) X0) SPEC
               (ptr, UbjRef.slice p pos1 n) 0xb3d98 fx7 R7 M7 md7 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n) X) MID E1 ltac:(split; [clear; lia| reflexivity]) E10).
      { unfold PECSPA.args_str, PECSPA.args_sv. cbn [fst snd]. rewrite L5K.rl11, L5K.rl12, L5K.rl14. rewrite SLEN.
        split; [| split; [exact E14| exists 2; split; [clear; lia| exact E12]]].
        exists (F + 256). split; [exact E11|]. split; [replace (F + 256) with (F / 8 * 8 + 32 * 8) by (clear - GF8; destruct GF8 as (X' & _); lia); rewrite Z_mod_plus_full; apply Z_mod_mult|].
        split; [exists (F, 3, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 3) with 512; clear; lia]|].
        split; [exact ACCsv|]. split; [exact APF|]. split; [exact Cp'|]. split; [replace (F + 256 + 8) with (F + 264) by (clear; lia); exact Cn'|].
        split; [exact BYT7|]. split; [exact SBYT|]. split; [clear - Hn26; lia|]. split; [exact DEF7|]. split; [exact ACC7|].
        destruct LOC as [[E0 En0]|[BB|[T1 T2]]]; [right; right; left; split; [exact E0| rewrite En0 in SLEN |- *; destruct (UbjRef.slice p pos1 0); [reflexivity| exfalso; cbn in SLEN; clear - SLEN; lia]]
          | left; exact BB| right; left; split; [exact T1| exact T2]]. }
      { unfold PECSPA.mp_enc in MPE |- *. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. exact MPE. }
      { cbn [snd]. rewrite SLEN. pose proof NB as NB'. rewrite Et, PECRVD.rv_H in NB'. unfold PECRVD.str_arm in NB'. rewrite GLd, EX in NB'. replace (blen p <? pos1 + n) with false in NB' by (symmetry; apply Z.ltb_ge; exact LEN). cbn [Z.eqb Pos.eqb andb] in NB'. unfold PECRVD.fin in NB'. destruct (s_ec (w_more true (e_string (UbjRef.utf8_valid (UbjRef.slice p pos1 n)) n (w_pos (pos1 + n) X)))); cbn [s_bad w_more] in NB'; exact NB'. }
      { cbn [snd]. rewrite SLEN. pose proof HB as HB'. rewrite Et, PECRVD.rv_H in HB'. unfold PECRVD.str_arm in HB'. rewrite GLd, EX in HB'. replace (blen p <? pos1 + n) with false in HB' by (symmetry; apply Z.ltb_ge; exact LEN). cbn [Z.eqb Pos.eqb andb] in HB'. unfold PECRVD.fin in HB'. destruct (s_ec (w_more true (e_string (UbjRef.utf8_valid (UbjRef.slice p pos1 n)) n (w_pos (pos1 + n) X)))); cbn [s_hi w_more] in HB'; exact HB'. }
      intros fx8 R8 M8 md8 LK8 Aw8 en8 k8 e8 cr8 RP8 MID8 KP8. cbn [snd] in MID8. rewrite SLEN in MID8.
      assert (S23z : getr R8 (reg 23) = Z_to_bv 64 (op + 8)) by (rewrite (L5SAR.cs_of_preserved _ R8 23 RP8) by inl; exact E23).
      assert (S24z : getr R8 (reg 24) = Z_to_bv 64 (op + 16)) by (rewrite (L5SAR.cs_of_preserved _ R8 24 RP8) by inl; exact E24).
      keep_only MORE DONE PPOS Et GLd EX LEN  S23z S24z MID8. rename MID8 into MID.
      entry_facts. frame_facts. piece_ctx MID.
      pz PEARVP5.arvZH2_conc fx8 R8 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
      destruct PZ as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & _ & _ & _ & MO9 & _ & _).
      apply (tail_J fx8 R8 M8 md8 LK8 Aw8 cr8 si4 sm4 en8 k8 e8 (e_string (UbjRef.utf8_valid (UbjRef.slice p pos1 n)) n (w_pos (pos1 + n) X)) fx9 R9 M9v 0xb3d98 MID MS9 MG9).
      - intros i Hi' N1 N2. apply FRZ9; [exact Hi'| exact N1| clear - N2; lia| clear - N2; lia].
      - intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZH2). vm_compute. reflexivity.
      - replace (PM.p_more si4) with 1; [exact MO9|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
        rewrite Lmore. rewrite PECRVD.e_string_more. cbn [s_more w_pos]. rewrite MORE. reflexivity.
      - rewrite Et, PECRVD.rv_H. unfold PECRVD.str_arm. rewrite GLd, EX. replace (blen p <? pos1 + n) with false by (symmetry; apply Z.ltb_ge; exact LEN). cbn [Z.eqb Pos.eqb andb]. rewrite PECRVD.w_more_same; [reflexivity|]. rewrite PECRVD.e_string_more. cbn [s_more w_pos]. exact MORE.

  +
    assert (SHORT : pos1 + n > blen p).
    {{ destruct (Z.eq_dec n2 n) as [E|N]; [exfalso| clear - N Hn Hn2 NMIN; lia]. rewrite E in CQ5. rewrite Z.sub_diag, Z.mod_0_l in CQ5 by (clear; lia). clear - CQ5; lia. }}
    assert (E5 : M5v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr4 Aw4 M4 md4 fx4 fx5 R4 0xb3d24 R5 (pa_make_ec AD) MVi K HHi AMi MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx5 R5 M4 md5 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n2) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx5 R5 md5 MID); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b _ PEARVP4.KS_arvHF_1). vm_compute. reflexivity. }
    keep_only Et GLd EX SHORT MID5 Q1 Q10 Q11. rename MID5 into MID.
    apply (call_mkec 0xb4678 1 fx5 R5 M4 md5 LK4 Aw4 cr4 si4 sm4 eni ki e2 (w_pos (pos1 + n2) X) MID Q1 ltac:(split; [clear; lia| reflexivity]) Q10 Q11 ltac:(clear; lia)).
    clear MID. intros fx6 R6 M6 md6 LK6 Aw6 RP6 MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP6.arvEHs_conc fx6 R6 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & MO7).
    apply (finish 0 (r_fail X) fx6 R6 M6 md6 LK6 Aw6 cr4 si4 sm4 eni ki true _ fx7 R7 M7v 0xb4678 MID MS7 MG7).
    * intros i Hi' N1 _. apply FRZ7; [exact Hi'| exact N1].
    * intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvEHs). vm_compute. reflexivity.
    * exact MO7.
    * left; reflexivity.
    * rewrite Et, PECRVD.rv_H. unfold PECRVD.str_arm. rewrite GLd, EX. replace (blen p <? pos1 + n) with true by (symmetry; apply Z.ltb_lt; clear - SHORT; lia). reflexivity.
    * pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      apply (PECRVD.clink_but_pos p (r_fail X) (w_more false (w_ec true (w_pos (pos1 + n2) X)))); [reflexivity| | exact (clink_fail _ _ _ _ _ CLm)].
      apply PECRVD.but_pos_r_fail. apply PECRVD.but_pos_sym. apply PECRVD.but_pos_w_pos.
    * reflexivity.
Qed.

Lemma arm_C fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X -> getr Ri (reg 23) = Z_to_bv 64 t -> getr Ri (reg 12) = Z_to_bv 64 99 -> t = 67 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb3aec Mi mdi) K.
Proof.
  intros MID J23 J12 Et. pose proof entry_model as (MORE & DONE & PPOS & MPE & XBAD). entry_facts. frame_facts. piece_ctx MID.
  rewrite Et in J23. pz PEARVP1.arvTC_conc fxi Ri 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Y1 & Y10 & Y11 & Y12 & Y23 & Y24 & C0 & SH1 & _ & _).
  apply (amid_pieceFW fxi Ri Mi mdi LKi Awi cri si smi eni ki ei X fx1 R1 0xb3aec (pa_src_read AD) M1v (fun a => (F / 8 + 2147450880 + 22 <= a < F / 8 + 2147450880 + 22 + 1) \/ (F + 176 <= a < F + 176 + 1)) MID MS1 MG1).
  { intros a Ha Na. apply FRZ1; [exact Ha| clear - Na; intros X'; apply Na; left; exact X'| clear - Na; intros X'; apply Na; right; exact X']. }
  { intros a X'. unfold SB. destruct X' as [X'|X']; [right; clear - X'; lia| left; clear - X'; lia]. }
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b _ PEARVP1.KS_arvTC). vm_compute. reflexivity. }
  keep_only MORE DONE PPOS MPE XBAD Et Y1 Y10 Y11 Y12 Y23 Y24 SH1.
  intros M1 md1 VIS1 HID1 MGM1 FR1w MID.
  apply (call_read (F + 176) 1 0xb3b38 22 1 fx1 R1 M1 md1 LKi Awi cri si smi eni ki ei X MID MORE DONE PPOS Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(rewrite HID1, VIS1; replace (F / 8 + 2147450880 + 22) with (F / 8 + 2147450902) by (clear; lia); exact SH1) ltac:(right; clear; lia)).
  keep_only MORE DONE PPOS MPE XBAD Et Y23 Y24.
  intros fxb Rb Mb mdb LKb Awb srcb smb d RP2 Z10 Hd SHORT LE BYT SHB2 MID.
  assert (S23 : getr Rb (reg 23) = Z_to_bv 64 (F + 176)) by (rewrite (L5SAR.cs_of_preserved _ Rb 23 RP2) by inl; exact Y23).
  assert (S24 : getr Rb (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved _ Rb 24 RP2) by inl; exact Y24).
  assert (Hd64 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  entry_facts. frame_facts. piece_ctx MID.
  pz PEARVP3.arvCR_conc fxb Rb 0 0 d 0 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hd; lia]).
  destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & [(MS3 & KS3 & Z1 & Z10b & Z11 & CQ3) | (MS3 & KS3 & Z1 & Z10b & Z11 & CQ3)]).
  +
    pose proof (count_eq d 1 Hd ltac:(clear; lia) CQ3) as Ed. rewrite Ed in *. clear Ed CQ3.
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb3b38 R3 (pa_validate AD) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvCR_0). vm_compute. reflexivity. }
    pose proof POK as (BOK & _). pose proof GFR as (GF1 & GF2 & GF3 & _).
    set (b := bat p (s_pos X)) in *. pose proof (PECRVD.bat_byte p (s_pos X) BOK ltac:(clear - PPOS LE; lia)) as BB. fold b in BB.
    assert (BYTb : L5.bytes_at RSEGS Mb (F + 176) [b]) by (rewrite (PECRVD.slice_pos_1 p (s_pos X)) in BYT by (clear - PPOS LE; lia); exact BYT).
    vis_amid BI Hi MVi.
    assert (DEFb : L5.defined Mb (F + 176) 1) by (apply (proj1 (L5A.defined_vis Hi Mb (F + 176) 1 (L5A.avis_sub Hi F 512 (F + 176) 1 VFi ltac:(clear; lia) ltac:(clear; lia)))); lazymatch goal with H : L5.defined MVi F 512 |- _ => apply (L5.defined_sub MVi F 512); [exact H| clear; lia| clear; lia] end).
    assert (ACCb : PMSPA.accA Mb (F + 176) 1).
    { unfold PMSPA.accA, aacc. intros a Ha. unfold S.
      assert (Da : a / 8 + SB = F / 8 + 2147450880 + 22) by (unfold SB; rewrite (div8_off F a 22 (proj1 GF8)); [clear; lia| clear - Ha; lia]).
      rewrite Da. pose proof (L5ADHR.byte_of_u8 Mb _ 1 SHB2 ltac:(right; clear - GF1; lia) ltac:(clear - GF1 GF2; lia)) as BY.
      right. exists 1. split; [exact BY|]. split; [clear; lia|].
      assert (Am : a mod 8 = a - (F + 176)) by (rewrite (Zmod_eq a 8) by (clear; lia); rewrite (div8_off F a 22 (proj1 GF8)) by (clear - Ha; lia); clear - GF8; lia).
      rewrite Am. clear - Ha; lia. }
    pose proof GFR as GFRc. keep_only MORE DONE PPOS MPE XBAD Et LE BB BYTb DEFb ACCb SHB2 MID3 Z1 Z10b Z11 S23 S24 KS3 GFRc. rename MID3 into MID.
    apply (call_valid (F + 176) 1 0xb3b48 [b] fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X) MID Z1 ltac:(split; [clear; lia| reflexivity])
             Z10b Z11 ltac:(clear; lia) ltac:(clear - GFRc; lia) ltac:(right; clear - GFRc; lia) ltac:(clear - GFRc; lia)
             DEFb ACCb ltac:(right; right; right; clear; lia) BYTb eq_refl ltac:(constructor; [exact BB| constructor])).
    clear MID GFRc. intros fx6 R6 M6 md6 v RP6 V11' Hv HV MG6 FRZ6 MID.
    assert (S23v : getr R6 (reg 23) = Z_to_bv 64 (F + 176)) by (rewrite (L5SAR.cs_of_preserved _ R6 23 RP6) by inl; rewrite (KS3 23%nat) by inl; exact S23).
    assert (S24v : getr R6 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved _ R6 24 RP6) by inl; rewrite (KS3 24%nat) by inl; exact S24).
    assert (Bv : 0 <= v < 2 ^ 64) by (clear - Hv; lia). assert (Hv6 : 0 <= v <= 6) by (clear - Hv; lia).
    entry_facts. frame_facts. piece_ctx MID. pose proof GFR as (GF1 & GF2 & GF3 & _).
    assert (BYT6 : L5.bytes_at RSEGS M6 (F + 176) [b]).
    { apply (L5C.bytes_at_agree RSEGS Mb M6); [| clear - GF1; lia| cbn; clear - GF2; lia| exact BYTb]. cbn. intros i Hi'. apply FRZ6; [clear - Hi' GF1 GF2; lia|]. intros X'. clear - Hi' X' GFCEIL GSLO. lia. }
    assert (DEF6 : L5.defined M6 (F + 176) 1) by exact (L5.defined_grows Mb M6 (F + 176) 1 MG6 DEFb).
    assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
    assert (SHB6 : L5.u8_at RSEGS M6 (F / 8 + 2147450880 + 22) 1).
    { apply (L5C.u8_at_agree RSEGS Mb M6); [| clear - D1; lia| clear - D2; lia| exact SHB2]. intros i Hi'. apply FRZ6; [clear - Hi' D1 D2; lia| clear - Hi' D1 D2 GSLO GSPT; lia]. }
    pz PEARVP3.arvCW_conc fx6 R6 0 0 0 v 0 as PB. L5SAR.feed PB ltac:(first [fcl | clear - Hv6; lia]).
    destruct PB as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & [(MS7 & KS7 & CQ7) | (MS7 & KS7 & E1 & E10 & E11 & _ & CQ7)]).
    *
      assert (Ev : v = 0) by (clear - CQ7 Hv; destruct (Z.eq_dec v 0) as [E|N]; [exact E| exfalso; rewrite Z.sub_0_r in CQ7; rewrite Z.mod_small in CQ7 by lia; lia]).
      assert (VT : UbjRef.utf8_valid [b] = true) by (apply HV; exact Ev).
      assert (E7 : M7v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). subst M7v.
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb M6 md6 fx6 fx7 R6 0xb3b48 R7 0xb47e8 MVi K HHi AMi MS7 (fun x Hx => Hx) (fun a Ha => eq_refl)).
      intros M7 md7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7.
      assert (E7 : M7 = M6) by (apply L5SAR.mem_eq_of_agree; exact FR7). subst M7.
      assert (MID7 : amid fx7 R7 M6 md7 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X)).
      { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx7 R7 md7 MID); [| exact HH7| exact AM7| exact MRT7].
        intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvCW_0). vm_compute. reflexivity. }
      keep_only MORE DONE PPOS MPE XBAD Et LE BB BYT6 DEF6 SHB6 VT MID7 S23v S24v KS7. rename MID7 into MID.
      assert (S23w : getr R7 (reg 23) = Z_to_bv 64 (F + 176)) by (rewrite (KS7 23%nat) by inl; exact S23v).
      assert (S24w : getr R7 (reg 24) = Z_to_bv 64 1) by (rewrite (KS7 24%nat) by inl; exact S24v).
      entry_facts. frame_facts. piece_ctx MID.
      pz PEARVP3.arvCK1_conc fx7 R7 0 0 0 0 0 as PB. L5SAR.feed PB fcl.
      destruct PB as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & G11 & SHb & SHa).
      apply (amid_pieceFW fx7 R7 M6 md7 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X) fx8 R8 0xb47e8 0xb47f4 M8v (fun a => F / 8 + 2147450880 + 24 <= a < F / 8 + 2147450880 + 24 + 2) MID MS8 MG8).
      { intros a Ha Na. apply FRZ8; [exact Ha| revert Na; clear; intros Na; unfold SB in *; intros X'; apply Na; lia]. }
      { intros a X'. unfold SB. right. clear - X'; lia. }
      { intros j Hj. apply KS8. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvCK1). vm_compute. reflexivity. }
      keep_only MORE DONE PPOS MPE XBAD Et LE BB BYT6 DEF6 SHB6 VT S23w S24w G11 SHa SHb KS8.
      intros M8 md8 VIS8 HID8 MGM8 FR8w MID.
      entry_facts. frame_facts. piece_ctx MID. pose proof GFR as (GF1 & GF2 & GF3 & _).
      assert (EV8 : MVi = M8v) by (unfold MVi; first [rewrite HID8 | unfold Hi; rewrite HID8]; exact VIS8).
      assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
      assert (ZSV : L5KA.zeros_at MVi ((F + 192) / 8 + 2147450880) 2).
      { rewrite EV8. replace ((F + 192) / 8 + 2147450880) with (F / 8 + 2147450904) by (rewrite (div8_off F (F + 192) 24 (proj1 GF8)) by (clear; lia); clear; lia).
        intros i Hi'. destruct (Z.eq_dec i 0) as [->|Ni].
        - rewrite Z.add_0_r. apply (L5ADHR.byte_of_u8 M8v _ 0 SHa); [right; clear - D1; lia| clear - D1 D2; lia].
        - replace i with 1 by (clear - Hi' Ni; lia). replace (F / 8 + 2147450904 + 1) with (F / 8 + 2147450905) by (clear; lia). apply (L5ADHR.byte_of_u8 M8v _ 0 SHb); [right; clear - D1; lia| clear - D1 D2; lia]. }
      vis_amid BI Hi MVi.
      assert (SHa8 : L5.u8_at RSEGS M8 (F / 8 + 2147450904) 0) by (apply (proj1 (L5A.u8_at_vis Hi M8 (F / 8 + 2147450904) 0 (L5A.avis_sub Hi (F / 8 + SB) 64 (F / 8 + 2147450904) 1 VSHi ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - D1; lia) ltac:(clear - D2; lia))); fold MVi; rewrite EV8; exact SHa).
      assert (SHb8 : L5.u8_at RSEGS M8 (F / 8 + 2147450905) 0) by (apply (proj1 (L5A.u8_at_vis Hi M8 (F / 8 + 2147450905) 0 (L5A.avis_sub Hi (F / 8 + SB) 64 (F / 8 + 2147450905) 1 VSHi ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) ltac:(clear - D1; lia) ltac:(clear - D2; lia))); fold MVi; rewrite EV8; exact SHb).
      assert (S23x : getr R8 (reg 23) = Z_to_bv 64 (F + 176)) by (rewrite (KS8 23%nat) by inl; exact S23w).
      assert (S24x : getr R8 (reg 24) = Z_to_bv 64 1) by (rewrite (KS8 24%nat) by inl; exact S24w).
      assert (BYT8 : L5.bytes_at RSEGS M8 (F + 176) [b]).
      { apply (L5C.bytes_at_agree RSEGS M6 M8); [| clear - GF1; lia| cbn; clear - GF2; lia| exact BYT6]. cbn. intros i Hi'. apply FR8w; [clear - Hi' GF1 GF2; lia|]. intros X'. clear - Hi' X' GF1 GFBIG; lia. }
      assert (DEF8 : L5.defined M8 (F + 176) 1) by exact (L5.defined_grows M6 M8 (F + 176) 1 MGM8 DEF6).
      assert (SHB8 : L5.u8_at RSEGS M8 (F / 8 + 2147450880 + 22) 1).
      { apply (L5C.u8_at_agree RSEGS M6 M8); [| clear - D1; lia| clear - D2; lia| exact SHB6]. intros i Hi'. apply FR8w; [clear - Hi' D1 D2; lia| clear - Hi'; lia]. }
      pz PEARVP3.arvCK2_conc fx8 R8 0 0 0 0 0 as PB. L5SAR.feed PB fcl.
      destruct PB as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & E1 & E10 & E12 & _ & E14 & _ & Cn & Cp & _ & _).
      apply (amid_pieceFW fx8 R8 M8 md8 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X) fx9 R9 0xb47f4 (pe_string EE) M9v (fun a => F + 192 <= a < F + 192 + 16) MID MS9 MG9).
      { intros a Ha Na. apply FRZ9; [exact Ha| exact Na]. }
      { intros a X'. unfold SB. left. clear - X'; lia. }
      { intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvCK2). vm_compute. reflexivity. }
      keep_only MORE DONE PPOS MPE XBAD Et LE BB BYT8 DEF8 SHB8 VT S23x S24x G11 SHa8 SHb8 E1 E10 E12 E14 Cn Cp KS9.
      intros M9 md9 VIS9 HID9 MGM9 FR9w MID.
      entry_facts. frame_facts. piece_ctx MID. vis_amid BI Hi MVi. pose proof GFR as (GF1 & GF2 & GF3 & _).
      assert (EV9 : MVi = M9v) by (unfold MVi; first [rewrite HID9 | unfold Hi; rewrite HID9]; exact VIS9).
      assert (Cp' : L5.u64_at RSEGS M9 (F + 192) (F + 176)) by (apply (proj1 (L5A.u64_at_vis Hi M9 (F + 192) (F + 176) (L5A.avis_sub Hi F 512 (F + 192) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))); fold MVi; rewrite EV9; exact Cp).
      assert (Cn' : L5.u64_at RSEGS M9 (F + 200) 1) by (apply (proj1 (L5A.u64_at_vis Hi M9 (F + 200) 1 (L5A.avis_sub Hi F 512 (F + 200) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia))); fold MVi; rewrite EV9; exact Cn).
      assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
      assert (AG89s : forall i, F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 64 -> M9 (Z_to_bv 64 i) = M8 (Z_to_bv 64 i)) by (intros i Hi'; apply FR9w; [clear - Hi' D1 D2; lia| clear - Hi' D1 D2 GF1 GF2 GFBIG; lia]).
      assert (SHa' : L5.u8_at RSEGS M9 (F / 8 + 2147450904) 0) by (apply (L5C.u8_at_agree RSEGS M8 M9); [intros i Hi'; apply AG89s; clear - Hi'; lia| clear - D1; lia| clear - D2; lia| exact SHa8]).
      assert (SHb' : L5.u8_at RSEGS M9 (F / 8 + 2147450905) 0) by (apply (L5C.u8_at_agree RSEGS M8 M9); [intros i Hi'; apply AG89s; clear - Hi'; lia| clear - D1; lia| clear - D2; lia| exact SHb8]).
      assert (E11 : getr R9 (reg 11) = Z_to_bv 64 (F + 192)) by (rewrite (KS9 11%nat) by inl; exact G11).
      assert (ACCsv : PMSPA.accA M9 (F + 192) 16).
      { intros a Ha. left. unfold byte_at, S.
        destruct (Z_lt_le_dec a (F + 200)) as [Xa|Xa].
        - rewrite (div8_off F a 24 (proj1 GF8)) by (clear - Ha Xa; lia). unfold SB. replace (F / 8 + 24 + 2147450880) with (F / 8 + 2147450904) by (clear; lia).
          apply (L5ADHR.byte_of_u8 M9 _ 0 SHa'); clear - D1 D2; lia.
        - rewrite (div8_off F a 25 (proj1 GF8)) by (clear - Ha Xa; lia). unfold SB. replace (F / 8 + 25 + 2147450880) with (F / 8 + 2147450905) by (clear; lia).
          apply (L5ADHR.byte_of_u8 M9 _ 0 SHb'); clear - D1 D2; lia. }
      assert (APF : forall o m, F + 32 <= o -> o + m <= F + 504 -> o + m <= fb \/ fb + 2048 <= o).
      { intros o m Ho1 Ho2. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & WFn & _).
        destruct (WFn (F, 3, sp - 128 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF0).
        assert (Iin : In (fb, 5, rs) (ff_remove F FF' ++ LKb)) by (apply in_or_app; left; unfold FF'; cbn [ff_remove ff_addr fst snd]; rewrite Z.eqb_refl; exact Hfb).
        pose proof (APF0 _ Iin) as APF1. cbn [ff_addr ff_class fst snd] in APF1. change (ff_bytes 5) with 2048 in APF1. change (ff_bytes 3) with 512 in APF1. clear - APF1 Ho1 Ho2. lia. }
      assert (BYT9 : L5.bytes_at RSEGS M9 (F + 176) [b]).
      { apply (L5C.bytes_at_agree RSEGS M8 M9); [| clear - GF1; lia| cbn; clear - GF2; lia| exact BYT8]. cbn. intros i Hi'. apply FR9w; [clear - Hi' GF1 GF2; lia| clear - Hi'; lia]. }
      assert (DEF9 : L5.defined M9 (F + 176) 1) by exact (L5.defined_grows M8 M9 (F + 176) 1 MGM9 DEF8).
      assert (ACC9 : PMSPA.accA M9 (F + 176) 1).
      { unfold PMSPA.accA, aacc. intros a Ha. unfold S.
        assert (Da : a / 8 + SB = F / 8 + 2147450880 + 22) by (unfold SB; rewrite (div8_off F a 22 (proj1 GF8)); [clear; lia| clear - Ha; lia]).
        rewrite Da. assert (SHB9 : L5.u8_at RSEGS M9 (F / 8 + 2147450880 + 22) 1) by (apply (L5C.u8_at_agree RSEGS M8 M9); [intros i Hi'; apply AG89s; clear - Hi'; lia| clear - D1; lia| clear - D2; lia| exact SHB8]).
        pose proof (L5ADHR.byte_of_u8 M9 _ 1 SHB9 ltac:(right; clear - D1; lia) ltac:(clear - D1 D2; lia)) as BY.
        right. exists 1. split; [exact BY|]. split; [clear; lia|].
        assert (Am : a mod 8 = a - (F + 176)) by (rewrite (Zmod_eq a 8) by (clear; lia); rewrite (div8_off F a 22 (proj1 GF8)) by (clear - Ha; lia); clear - GF8; lia).
        rewrite Am. clear - Ha; lia. }
      keep_only MORE DONE PPOS MPE XBAD Et LE BB VT MID E1 E10 E11 E12 E14 Cp' Cn' ACCsv APF BYT9 DEF9 ACC9. entry_facts. frame_facts.
      pose proof VS as SPEC. unfold PECSA.v_string_spec, PECSPA.v_string_spec in SPEC.
      apply (call_slot (Z * list Z) (pe_string EE) (PECSPA.args_str RSEGS AD) (fun _ => PECSPA.mp_enc) (fun d _ X0 => e_string (UbjRef.utf8_valid (snd d)) (Z.of_nat (length (snd d))) X0) SPEC
               (F + 176, [b]) 0xb484c fx9 R9 M9 md9 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X) MID E1 ltac:(split; [clear; lia| reflexivity]) E10).
      { unfold PECSPA.args_str, PECSPA.args_sv. cbn [fst snd length Z.of_nat Pos.of_succ_nat]. rewrite L5K.rl11, L5K.rl12, L5K.rl14.
        split; [| split; [exact E14| exists 0; split; [clear; lia| exact E12]]].
        exists (F + 192). split; [exact E11|]. split; [replace (F + 192) with (F / 8 * 8 + 24 * 8) by (clear - GF8; destruct GF8 as (X' & _); lia); rewrite Z_mod_plus_full; apply Z_mod_mult|].
        split; [exists (F, 3, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 3) with 512; clear; lia]|].
        split; [exact ACCsv|]. split; [apply APF; clear; lia|]. split; [exact Cp'|]. split; [replace (F + 192 + 8) with (F + 200) by (clear; lia); exact Cn'|].
        split; [exact BYT9|]. split; [constructor; [exact BB| constructor]|]. split; [clear; lia|]. split; [exact DEF9|]. split; [exact ACC9|].
        right; right; right. split; [exists (F, 3, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 3) with 512; clear; lia]| apply APF; clear; lia]. }
      { unfold PECSPA.mp_enc in MPE |- *. cbn [s_lo s_hi s_bad s_estk s_edepth w_pos]. exact MPE. }
      { cbn [snd length Z.of_nat Pos.of_succ_nat]. rewrite VT. pose proof NB as NB'. rewrite Et, PECRVD.rv_C in NB'. replace (blen p <? s_pos X + 1) with false in NB' by (symmetry; apply Z.ltb_ge; exact LE).
        rewrite (PECRVD.slice_pos_1 p (s_pos X)) in NB' by (clear - LE PPOS; lia). fold b in NB'. rewrite VT in NB'.
        unfold PECRVD.fin in NB'. destruct (s_ec (w_more true (e_string true 1 (w_pos (s_pos X + 1) X)))); cbn [s_bad w_more] in NB'; exact NB'. }
      { cbn [snd length Z.of_nat Pos.of_succ_nat]. rewrite VT. pose proof HB as HB'. rewrite Et, PECRVD.rv_C in HB'. replace (blen p <? s_pos X + 1) with false in HB' by (symmetry; apply Z.ltb_ge; exact LE).
        rewrite (PECRVD.slice_pos_1 p (s_pos X)) in HB' by (clear - LE PPOS; lia). fold b in HB'. rewrite VT in HB'.
        unfold PECRVD.fin in HB'. destruct (s_ec (w_more true (e_string true 1 (w_pos (s_pos X + 1) X)))); cbn [s_hi w_more] in HB'; exact HB'. }
      intros fx10 R10 M10 md10 LK10 Aw10 en10 k10 e10 cr10 RP10 MID10 KP10. cbn [snd length Z.of_nat Pos.of_succ_nat] in MID10. rewrite VT in MID10.
      keep_only MORE DONE PPOS Et LE VT MID10. rename MID10 into MID.
      entry_facts. frame_facts. piece_ctx MID.
      pz PEARVP5.arvZC_conc fx10 R10 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
      destruct PZ as (fx11 & R11 & M11v & MG11 & _ & FRZ11 & MS11 & KS11 & _ & _ & _ & _ & MO11 & _ & _).
      apply (tail_J fx10 R10 M10 md10 LK10 Aw10 cr10 (PMSPA.with_src si srcb) smb en10 k10 e10 (e_string true 1 (w_pos (s_pos X + 1) X)) fx11 R11 M11v 0xb484c MID MS11 MG11).
      -- intros i Hi' N1 N2. apply FRZ11; [exact Hi'| exact N1| clear - N2; lia| clear - N2; lia| clear - N2; lia].
      -- intros j Hj. apply KS11. revert j Hj. apply (L5K.incl_b _ PEARVP5.KS_arvZC). vm_compute. reflexivity.
      -- replace (PM.p_more (PMSPA.with_src si srcb)) with 1; [exact MO11|]. pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). destruct CLm as (Lmore & _).
         rewrite Lmore. rewrite PECRVD.e_string_more. cbn [s_more w_pos]. rewrite MORE. reflexivity.
      -- rewrite Et, PECRVD.rv_C. replace (blen p <? s_pos X + 1) with false by (symmetry; apply Z.ltb_ge; exact LE). rewrite (PECRVD.slice_pos_1 p (s_pos X)) by (clear - LE PPOS; lia). fold b. rewrite VT.
         rewrite PECRVD.w_more_same; [reflexivity|]. rewrite PECRVD.e_string_more. cbn [s_more w_pos]. exact MORE.
    *
      assert (Nv : v <> 0) by (clear - CQ7 Hv; intros E; subst v; rewrite Z.sub_0_r, Z.mod_0_l in CQ7 by lia; lia).
      assert (VF : UbjRef.utf8_valid [b] = false) by (destruct (UbjRef.utf8_valid [b]) eqn:EV; [exfalso; apply Nv; apply HV; reflexivity| reflexivity]).
      assert (E7 : M7v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). subst M7v.
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb M6 md6 fx6 fx7 R6 0xb3b48 R7 (pa_make_ec AD) MVi K HHi AMi MS7 (fun x Hx => Hx) (fun a Ha => eq_refl)).
      intros M7 md7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7.
      assert (E7 : M7 = M6) by (apply L5SAR.mem_eq_of_agree; exact FR7). subst M7.
      assert (MID7 : amid fx7 R7 M6 md7 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X)).
      { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx7 R7 md7 MID); [| exact HH7| exact AM7| exact MRT7].
        intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvCW_1). vm_compute. reflexivity. }
      keep_only Et LE PPOS VF MID7 E1 E10 E11. rename MID7 into MID.
      apply (call_mkec 0xb3b60 7 fx7 R7 M6 md7 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + 1) X) MID E1 ltac:(split; [clear; lia| reflexivity]) E10 E11 ltac:(clear; lia)).
      clear MID. intros fx8 R8 M8 md8 LK8 Aw8 RP8 MID.
      entry_facts. frame_facts. piece_ctx MID.
      pz PEARVP6.arvEC_conc fx8 R8 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
      destruct PZ as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & _ & _ & _ & MO9).
      apply (finish 0 (r_fail (w_pos (s_pos X + 1) X)) fx8 R8 M8 md8 LK8 Aw8 cri (PMSPA.with_src si srcb) smb eni ki true _ fx9 R9 M9v 0xb3b60 MID MS9 MG9).
      -- intros i Hi' N1 N2. apply FRZ9; [exact Hi'| exact N1| clear - N2; lia].
      -- intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvEC). vm_compute. reflexivity.
      -- exact MO9.
      -- left; reflexivity.
      -- rewrite Et, PECRVD.rv_C. replace (blen p <? s_pos X + 1) with false by (symmetry; apply Z.ltb_ge; exact LE). rewrite (PECRVD.slice_pos_1 p (s_pos X)) by (clear - LE PPOS; lia). fold b. rewrite VF. reflexivity.
      -- pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _). exact (clink_fail _ _ _ _ _ CLm).
      -- reflexivity.
  +
    pose proof (count_ne d 1 Hd ltac:(clear; lia) CQ3) as Nd.
    assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKb cri Awb Mb mdb fxb fx3 Rb 0xb3b38 R3 (pa_make_ec AD) MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = Mb) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (MID3 : amid fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X)).
    { apply (amid_regs _ _ _ _ _ _ _ _ _ _ _ _ _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
      intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b _ PEARVP3.KS_arvCR_1). vm_compute. reflexivity. }
    keep_only Et Hd Nd SHORT MID3 Z1 Z10b Z11. rename MID3 into MID.
    apply (call_mkec 0xb3b60 1 fx3 R3 Mb md3 LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos X + d) X) MID Z1 ltac:(split; [clear; lia| reflexivity]) Z10b Z11 ltac:(clear; lia)).
    clear MID. intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEARVP6.arvEC_conc fx4 R4 0 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & MO7).
    apply (finish 0 (r_fail X) fx4 R4 M4 md4 LK4 Aw4 cri (PMSPA.with_src si srcb) smb eni ki true _ fx7 R7 M7v 0xb3b60 MID MS7 MG7).
    * intros i Hi' N1 N2. apply FRZ7; [exact Hi'| exact N1| clear - N2; lia].
    * intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b _ PEARVP6.KS_arvEC). vm_compute. reflexivity.
    * exact MO7.
    * left; reflexivity.
    * rewrite Et, PECRVD.rv_C. replace (blen p <? s_pos X + 1) with true by (symmetry; apply Z.ltb_lt; clear - SHORT Nd Hd; lia). reflexivity.
    * pose proof MID as (_ & _ & CPm & _). pose proof CPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLm & _).
      apply (PECRVD.clink_but_pos p (r_fail X) (w_more false (w_ec true (w_pos (s_pos X + d) X)))); [reflexivity| | exact (clink_fail _ _ _ _ _ CLm)].
      apply PECRVD.but_pos_r_fail. apply PECRVD.but_pos_sym. apply PECRVD.but_pos_w_pos.
    * reflexivity.
Qed.

Lemma frame_body (fx1 : FPState) R1 M1 model1 R2 :
  (forall (fx3 : FPState) R3 M3 md3, amid fx3 R3 M3 md3 LK2 Aw cr s sm en k e X -> getr R3 (reg 23) = Z_to_bv 64 t -> getr R3 (reg 12) = Z_to_bv 64 99 ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx3) RSEGS R3 0xb3aec M3 md3) K) ->
  getr R1 (reg 2) = Z_to_bv 64 (sp - 128) -> getr R1 (reg 8) = Z_to_bv 64 sp -> getr R1 (reg 9) = Z_to_bv 64 (sp - 128) ->
  getr R1 (reg 20) = Z_to_bv 64 op -> getr R1 (reg 21) = Z_to_bv 64 oec -> getr R1 (reg 22) = Z_to_bv 64 ov -> getr R1 (reg 23) = Z_to_bv 64 t -> getr R1 (reg 26) = Z_to_bv 64 2147450880 ->
  (forall j, In j [3; 4]%nat -> getr R1 (reg j) = getr R (reg j)) ->
  own sp R M1 -> model_rt model model1 ->
  L5SAR.ek L ar (PEC.owned s en k ++ LBX) FF sp 28672 [] M M1 -> L5SAR.dk L ar (PEC.owned s en k ++ LBX) FF sp 28672 M M1 ->
  getr R2 10%bv = Z_to_bv 64 F -> regs_preserved R1 R2 -> L5CA.amodel_ok Aw model2 -> model_rt model1 model2 ->
  L5CA.astk ar M2 sp 28672 -> L5SAR.ek L ar LBX FF sp 28672 [] M M2 -> L5SAR.dk L ar LBX FF sp 28672 M M2 ->
  L5SAR.ek L ar (PEC.owned s en k ++ LBX) FF sp 28672 [] M1 M2 -> L5SAR.dk L ar (PEC.owned s en k ++ LBX) FF sp 28672 M1 M2 ->
  (forall a, sp - 128 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  L5.writable RSEGS (mrestrict (ahid Aw model2) M2) F 512 ->
  L5.writable RSEGS (mrestrict (ahid Aw model2) M2) (F / 8 + SB) 64 ->
  L5KA.zeros_at (mrestrict (ahid Aw model2) M2) (F / 8 + SB) 64 ->
  L5.u64_at RSEGS (mrestrict (ahid Aw model2) M2) (F + 512 - 8) fl -> L5.writable RSEGS (mrestrict (ahid Aw model2) M2) fl 1 ->
  L5.defined (mrestrict (ahid Aw model2) M2) F 512 ->
  L5A.avis (ahid Aw model2) F 512 -> L5A.avis (ahid Aw model2) (F / 8 + SB) 64 -> L5A.avis (ahid Aw model2) fl 1 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R2 0xb39d8 M2 model2) K.
Proof.
  intros ARMS T2 T8 T9 T20 T21 T22 T23 T26 K34 OWN1 MRT1 EK01f DK01f G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL.
  entry_facts. frame_facts.
  pose proof CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  pose proof (L5SAR.ek_trans L ar LB FF sp 28672 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 28672 M M1 M2 DK01f DK12f) as DK02f.
  assert (HH2 : ri_inv HI LB FF' LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 28672 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 28672 a HH SPT Hc) as [Y'|Y']; [clear - Xa Y'; lia| clear - Xa Y' SLO; lia]. }
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j))
    by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 op) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (B21R : getr R2 (reg 21) = Z_to_bv 64 oec) by (rewrite (R2c 21%nat) by inl; exact T21).
  assert (B22R : getr R2 (reg 22) = Z_to_bv 64 ov) by (rewrite (R2c 22%nat) by inl; exact T22).
  assert (B23R : getr R2 (reg 23) = Z_to_bv 64 t) by (rewrite (R2c 23%nat) by inl; exact T23).
  assert (B26R : getr R2 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R2c 26%nat) by inl; exact T26).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).

  assert (OWN2 : own sp R M2) by (apply (own_agree sp R M1 M2 ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia) OWN1); intros a Ha; unfold ocell in Ha; apply AGF; clear - Ha; lia).
  assert (BI2 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned s en k) M2 model2 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH2|]. split; [exact AM2|]. split; [eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact ASTK2|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 28672 WR [] M M2 EK02); intros a _ r0 []|]. split; [exact DK02|]. split; [exact OWN2|].
    change (ff_bytes 3 / 8) with 64. apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 64 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (CP2 : PECA.crun_preA RSEGS AD AAD EE L ar P M2 fb p X s str sm en k e cat).
  { apply (cpre_keepA LB sp 28672 [] M M2 X s sm en k e EK02f PMKA.wapp_nil BRB); [unfold LB; apply incl_appl; apply incl_refl| unfold LB; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CPRE]. }
  assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia).
  assert (ZF64 : L5KA.zeros_at MV2 (F / 8 + 2147450880) 64) by (unfold SB in FSHZ; exact FSHZ).
  pose proof (pfacts_bc M2 model2 LK2 cr Aw s sm en k e X BI2 CP2) as VF0. fold H2 in VF0. fold MV2 in VF0. open_vf VF0.

  pose proof (PEARVP1.arvB_conc fx1 R2 MV2 (VALU t 0 0 0 0)) as PB. unfold VALU in PB. cbn beta iota in PB. L5SAR.feed PB fcl.
  destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & _ & _ & Y12 & _ & _ & Y18 & Y19 & Y27 & _).
  clear VF1 VF2 VF3 VF4 VF5 VF6 VF7 VF8 VF9 VF10 VF11 VF12 VF13 VF14 VF15 VF16 VF17 VF18 VF19 VF20 VF21 VF22 VF23 VF24 VF25 VF26 VF27 VF28 VF29 VF30
        VF31 VF32 VF33 VF34 VF35 VF36 VF37 VF38 VF39 VF40 VF41 VF42 VF43 VF44 VF45 VF46 VF47 VF48 VF49 VF50 VF51 VF52 VF53 VF54 VF55 VF56 VF57 VF58 VF59 VF60
        VF61 VF62 VF63 VF64 VF65 VF66 VF67 VF68 VF69 VF70 VF71 VF72 VF73 VF74 VF75 VF76 VF77 VF78 VF79 VF80 VF81 VF82 VF83 VF84 VF85 VF86 VF87 VF88.
  set (W3 := fun a => (sp - 112 <= a < sp - 112 + 8) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 40)).
  pose proof GFR as (GF1 & GF2 & GF3 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb39d8 R3 0xb3aec M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; clear - X'; lia| intros X'; apply Hn; right; left; clear - X'; lia| intros X'; apply Hn; right; right; clear - X'; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT; lia| intros Y'; clear - Y'; lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 3 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 3) with 512; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 3 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X'; lia.
    - destruct Wa as [X'|[X'|X']]; [clear - X' SLO SPT; lia| clear - X' GFR; lia| clear - X' D1; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23 : L5SAR.ek L ar LB FF sp 28672 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 28672 [] M2 M3 W3 FR3). intros a Ha Hc _ X'. destruct X' as [X'|[X'|X']].
    - apply (NCS0 a); [clear - X'; lia| exact Hc].
    - destruct (APART a 1 sp 28672 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y' & _). change (ff_bytes 3) with 512 in Y'. clear - X' Y'; lia.
    - destruct (APART a 1 sp 28672 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y' & _). change (ff_bytes 3 / 8) with 64 in Y'. unfold SB in Y'. clear - X' Y'; lia. }
  assert (OWN3 : own sp R M3).
  { apply (own_agree sp R M2 M3 ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia) OWN2). intros a Ha. unfold ocell in Ha.
    apply FR3; [clear - Ha SLO SHI SPT; lia|]. intros [X'|[X'|X']]; [clear - X' Ha; lia| clear - X' Ha GFCEIL GSLO; lia| clear - X' Ha D1 D2 SLO SPT; lia]. }
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (own sp R) F 3 WR (PEC.owned s en k) M3 model3 LK2 cr Aw).
  { apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PEC.owned s en k) G
             WR (PEC.owned s en k) M2 model2 LK2 cr Aw M3 model3 W3 BI2 HH3 AM3 MRT3 MGM3 FR3).
    intros a Wa. destruct Wa as [X'|[X'|X']]; [left; split; [clear - X'; lia| unfold ocell; clear - X'; lia]| right; left; change (ff_bytes 3) with 512; clear - X'; lia
      | right; right; change (ff_bytes 3 / 8) with 64; unfold SB; clear - X'; lia]. }
  assert (CP3 : PECA.crun_preA RSEGS AD AAD EE L ar P M3 fb p X s str sm en k e cat).
  { apply (cpre_keepA LB sp 28672 [] M2 M3 X s sm en k e EK23 PMKA.wapp_nil BRB); [unfold LB; apply incl_appl; apply incl_refl| unfold LB; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP2]. }
  assert (AMID3 : amid fx3 R3 M3 model3 LK2 Aw cr s sm en k e X).
  { unfold amid. split; [| split; [exact BI3| split; [exact CP3| split; [| split; [intros X'; exact X'| unfold PMSP.credit_keep; clear; lia]]]]].
    - split; [rewrite (KS3 2%nat) by inl; exact B2R|]. split; [rewrite (KS3 8%nat) by inl; exact B8R|]. split; [rewrite (KS3 9%nat) by inl; exact B9R|].
      split; [exact Y18|]. split; [exact Y19|]. split; [rewrite (KS3 20%nat) by inl; exact B20R|]. split; [rewrite (KS3 21%nat) by inl; exact B21R|].
      split; [rewrite (KS3 22%nat) by inl; exact B22R|]. split; [rewrite (KS3 26%nat) by inl; exact B26R|]. split; [exact Y27|].
      intros j Hj. rewrite (KS3 j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity).
      rewrite (R2c j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply K34. exact Hj.
    - unfold PMSPA.src_step. split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|]. split; [intros X'; exact X'| clear; lia]. }
  apply (ARMS fx3 R3 M3 model3 AMID3); [rewrite (KS3 23%nat) by inl; exact B23R| exact Y12].
Qed.

Lemma arms_all (fx3 : FPState) R3 M3 md3 :
  amid fx3 R3 M3 md3 LK2 Aw cr s sm en k e X -> getr R3 (reg 23) = Z_to_bv 64 t -> getr R3 (reg 12) = Z_to_bv 64 99 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx3) RSEGS R3 0xb3aec M3 md3) K.
Proof.
  intros MID J23 J12.
  destruct (PECRVD.is_marker t) eqn:MK; [| exact (arm_unknown _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 MK)].
  destruct (PECRVD.marker_cases t MK) as [[Et|[Et|Et]]|[Et|[[Et|[Et|[Et|[Et|[Et|[Et|Et]]]]]]|[Et|[[Et|Et]|[Et|Et]]]]]].
  - exact (arm_Z _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_T _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_F _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_N _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_i _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_U _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_I _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_l _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_L _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_d _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_D _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_C _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_S _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_H _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_A _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
  - exact (arm_O _ _ _ _ _ _ _ _ _ _ _ _ MID J23 J12 Et).
Qed.
End Frame.

Theorem read_value_call : srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx) RSEGS R (pa_read_value AD) M model) K.
Proof.
  entry_facts.
  pose proof AM as (Mh & MI).
  pose proof A10 as X10. pose proof A11 as X11. pose proof A12 as X12. pose proof A13 as X13.
  rewrite L5K.rl10 in X10. rewrite L5K.rl11 in X11. rewrite L5K.rl12 in X12. rewrite L5K.rl13 in X13. fold op in X10. fold ov in X11. fold oec in X13.
  pose proof CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (BASE' : PMSTA.base_okA RSEGS PMA.AD M) by exact BASE.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE') as (IC0 & CSBv & CUARv). fold H in IC0, CSBv, CUARv. fold MV in IC0, CSBv, CUARv.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 28672 128 HH ASTK ltac:(clear; lia)) as (SL128 & SH128 & WS128). fold H in WS128. fold MV in WS128.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & _).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK cr Aw M model fb _ s HH FOK PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold H in Zop, Z32, Z20, OWR, OVIS. fold MV in Zop, Z32, Z20, OWR. fold op in Zop, Z32, Z20, OWR, OVIS.
  assert (ECX : exists v c, PMSPA.ec_at RSEGS M oec v c).
  { pose proof ECS as E0. unfold PECA.ec_stateA in E0. fold oec in E0.
    lazymatch type of E0 with (if ?c then _ else _) => destruct c; [destruct E0 as (v0 & _ & E1); exists v0; eexists; exact E1| exists 0, cat; exact E0] end. }
  destruct ECX as (ecv & ecc & ECat).
  pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK cr Aw M model fb ecv ecc HH FOK ECat) as ((_ & _ & _) & ZE & EW & _ & EU & _ & _). fold H in ZE, EW, EU. fold MV in ZE, EW, EU. fold oec in ZE, EW, EU.
  assert (Q0a : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia). assert (Q0b : 0 <= op < 2 ^ 64) by (clear - O1 O3; lia).
  assert (Q0c : 0 <= ov < 2 ^ 64) by (clear - O1 O3 Eop Eov; lia). assert (Q0d : 0 <= oec < 2 ^ 64) by (clear - E1' E3'; lia).
  assert (Ht64 : 0 <= t < 2 ^ 64) by (clear - Ht; lia).

  pose proof (PEARVP1.arvA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => t | 36%nat => op | 37%nat => ov | 38%nat => oec | _ => 0 end)) as PP. cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [sya | unfold PEARVP1.aligned; sya | clear - SL128 SHI SPT; lia | clear - O2 SLO; lia | clear - E2' SLO; lia
                             | clear - Eop Eoec Eov; lia | clear - O8; lia | clear - C8m; lia | clear - OBIG; lia | clear - EBIG; lia
                             | clear - O1 O3; lia | clear - E1' E3'; lia | clear - O1; lia | clear - E1'; lia]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T20 & T21 & T22 & T23 & T26
                 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C128).
  unfold PMSPA.cfg. cbn [pa_read_value AD PeCLayoutA.CADDR_A].
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb395c R1 0x5e8b4 M1v (fun a => sp - 128 <= a < sp - 128 + 128) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X'; clear - X' Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL128 SHI SPT; lia| intros X'; clear - X'; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 28672 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 28672 a HH SPT Hc) as [Y'|Y']; [clear - Xa Y'; lia| clear - Xa Y' SL128; lia]. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 28672 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 28672 [] M M1 (fun a => sp - 128 <= a < sp - 128 + 128) FR1). intros a Ha Hc _ X'. apply (NCS0 a); [clear - X'; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 28672 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBX FF sp 28672 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBX FF sp 28672 M M1 INCX DK01f) as DK01.
  assert (SV1 : forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X'. apply (proj1 (L5A.u64_at_vis H M1 a v (VIS a 8 ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X'. }
  assert (OWN1 : own sp R M1).
  { unfold own. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
  clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C128 SV1.

  assert (FRk3 : ff_room 3 FF LK) by (pose proof (FRM 3 ltac:(cbn; tauto)) as X'; unfold ff_room; clear - X'; lia).
  change 0x5e8b4 with (PMA.SM_PC 3).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 3 LBX (PEC.owned s en k) FF LK cr Aw sp 28672 (sp - 128) (sp - 104) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xb39d8 ltac:(cbn; tauto) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk3. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 3) with 512 in FW, FSHW, FSHZ, FLC, FLW, FDEF, VF, VSH, APART. change (512 / 8) with 64 in FSHW, FSHZ, VSH, APART.
  fold LB in EK12f, DK12f, APART.
  apply (frame_body F fl LK2 M2 model2 G APART fx1 R1 M1 model1 R2 (arms_all F fl LK2 M2 model2 G APART) T2 T8 T9 T20 T21 T22 T23 T26
           ltac:(intros j Hj; apply KS1; revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity)
           OWN1 MRT1 EK01f DK01f G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL).
Qed.
End Call.

Theorem read_value_ok : PECSA.read_value_spec L ar HI P.
Proof.
  unfold PECSA.read_value_spec, PECSPA.read_value_spec, PECSPA.crun_spec.
  intros PMODE t fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 ARGS CPRE INCS POK MP NB HB CRED KONT.
  destruct ARGS as (A10 & A11 & A13 & Ht & A12).
  exact (read_value_call PMODE t fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 A11 A13 Ht A12 CPRE INCS POK MP NB HB CRED KONT).
Qed.
End WithHeap.
End PEACRV.
