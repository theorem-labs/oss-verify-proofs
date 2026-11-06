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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrameA PeCRdValD PeCBegD PeABegKit PmSpecsAX PeACReset1 PeASrcRead1 PmAUarK PmAUarKS PmAUar PeABaP1 PeABaP2 PeABaP3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b6d84_b6d88.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEACBA.
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

Hypothesis PEEK : PECSA.peek_spec L ar HI.
Hypothesis IGN : PECSA.ignore_spec L ar HI.
Hypothesis SRD : PECSA.src_read_spec L ar HI.
Hypothesis GL : PECSA.get_length_spec L ar HI P.
Hypothesis MKE : PECSA.make_ec_spec L ar HI.
Hypothesis PMI : PECSA.push_mi_spec L ar HI.
Hypothesis PMS : PECSA.push_ms_spec L ar HI.
Hypothesis PMSU : PECSA.push_msu_spec L ar HI.
Hypothesis VBI : PECSA.v_begin_arr_spec L ar HI P.
Hypothesis VBL : PECSA.v_begin_arr_len_spec L ar HI P.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
          (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 7.
Hypothesis FRM : PMSPA.ffroomA 7 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_p AD fb).
Hypothesis A11 : getr R 11%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis A12 : getr R 12%bv = Z_to_bv 64 (PMSPA.o_ec AD fb).
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_run tt p X.
Hypothesis NB : s_bad (r_begin p false X) = false.
Hypothesis HB : PESKA.spa_hb P (s_hi (r_begin p false X)).
Hypothesis CRED : PMSP.credit_le (PECA.pot_allA L ar P s en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (r_begin p false X) s' str sm' en' k' e' cat ->
        PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 7) (PEC.W_crun AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_allA L ar P s en k) (PECA.pot_allA L ar P s' en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s' en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.
Let op := PMSPA.o_p AD fb. Let ov := PMSPA.o_v AD fb. Let oec := PMSPA.o_ec AD fb. Let ois := PMSPA.o_is AD fb. Let osk := PESK.o_sink EE fb. Let otb := PMSPA.o_tb AD fb.
Let WR := PEC.W_crun AD EE fb.

Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 7) with 26624 in ASTK, STKSH; change (26624 / 8) with 3328 in STKSH;
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
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model op 384 sp 26624 HH (PMKA.aobj_of_aobjA FF op 384 (AOF op 384 ltac:(lia) ltac:(lia)) O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & _);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ois 272 sp 26624 HH (PMKA.aobj_of_aobjA FF ois 272 (AOF ois 272 ltac:(lia) ltac:(lia)) I8) ltac:(lia) ltac:(reflexivity))
    as ((I1 & I2 & I3 & I4 & I5) & IBIG & _);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model oec 16 sp 26624 HH (PMKA.aobj_of_aobjA FF oec 16 (AOF oec 16 ltac:(lia) ltac:(lia)) C8m) ltac:(lia) ltac:(reflexivity))
    as ((E1' & E2' & E3' & E4' & E5') & EBIG & _);
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH);
  assert (AOP : PMSPA.aobjA FF op 384) by (apply AOF; lia);
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply AOF; lia).

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k).
Hypothesis APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n ->
  (a + n <= F \/ F + ff_bytes 0 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + ff_bytes 0 / 8 <= a) /\ (a + n <= fl \/ fl + 1 <= a).
Let FF' := (F, 0, sp - 128 + 32) :: FF.

Ltac frame_facts :=
  pose proof G as G'; destruct G' as [_ GSPT GSLO GSHI _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS];
  change (ff_bytes 0) with 64 in GFS2, GFCEIL, GFLC, GFR, GF8, GFBIG, GFLA, GNCF; unfold FS_BYTES in GFS2, GFLP.

Definition amid (fxi : FPState) (Ri : bvmap 5 word) (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit)
           (si : PM.pst) (smi : PM.strm) (eni : PEC.enc) (ki : PESK.sink) (ei : bool) (Xi : st) : Prop :=
  (getr Ri (reg 2) = Z_to_bv 64 (sp - 128) /\ getr Ri (reg 8) = Z_to_bv 64 sp /\ getr Ri (reg 9) = Z_to_bv 64 (sp - 128) /\ getr Ri (reg 18) = Z_to_bv 64 F
   /\ getr Ri (reg 19) = Z_to_bv 64 op /\ getr Ri (reg 20) = Z_to_bv 64 oec /\ getr Ri (reg 21) = Z_to_bv 64 ov /\ getr Ri (reg 25) = Z_to_bv 64 F
   /\ getr Ri (reg 26) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr Ri (reg 27) = Z_to_bv 64 2147450880 /\ (forall j, In j [3; 4]%nat -> getr Ri (reg j) = getr R (reg j)))
  /\ PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned si eni ki) Mi mdi LKi cri Awi
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
  pose proof MID as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J25 & J26 & J27 & J34) & BI & CP & ST & EIMP & CK);
  pose proof BI as (HHi & AMi & MRTi & INCAi & INCLi & ASTKi & EKbi & DKbi & OWNi & FSHDi);
  pose proof AMi as (Mhi & MIi).

Ltac vis_amid BI Hh Mv :=
  let X := fresh "VF" in
  pose proof (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
                WR _ _ _ _ _ _ BI) as X;
  destruct X as ((WSi & ICi & CSBi & CUARi & _) & OWNv & (FDi & FWi & FSWi & FLCi & FLWi) & (FLCci & FLVi & VFi & VSi & VSHi));
  change (ff_bytes 0) with 64 in WSi, FDi, FWi, FSWi, FLCi, VFi, VSHi; change (64 / 8) with 8 in FSWi, VSHi;
  replace (sp - (sp - 128)) with 128 in WSi by (clear; lia); replace (F + 64 - 8) with (F + 56) in FLCi by (clear; lia);
  fold Hh in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi, FLVi, VFi, VSi, VSHi; fold Mv in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi.

Lemma amid_regs fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fx' : FPState) R' md' :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat -> getr R' (reg j) = getr Ri (reg j)) ->
  ri_inv HI (PEC.owned si eni ki ++ LBX) FF' LKi cri Awi Mi (vml_of md') -> L5CA.amodel_ok Awi md' -> model_rt mdi md' ->
  amid fx' R' Mi md' LKi Awi cri si smi eni ki ei Y.
Proof.
  intros MID RR HH' AM' MRT'. open_amid MID.
  split; [|split; [exact (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned si eni ki) Mi mdi LKi cri Awi md' BI HH' AM' MRT')| split; [exact CP| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  split; [rewrite (RR 2%nat) by inl; exact J2|]. split; [rewrite (RR 8%nat) by inl; exact J8|]. split; [rewrite (RR 9%nat) by inl; exact J9|].
  split; [rewrite (RR 18%nat) by inl; exact J18|]. split; [rewrite (RR 19%nat) by inl; exact J19|]. split; [rewrite (RR 20%nat) by inl; exact J20|].
  split; [rewrite (RR 21%nat) by inl; exact J21|]. split; [rewrite (RR 25%nat) by inl; exact J25|]. split; [rewrite (RR 26%nat) by inl; exact J26|].
  split; [rewrite (RR 27%nat) by inl; exact J27|].
  intros j Hj. rewrite (RR j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
Qed.

Lemma amid_pieceF fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fxj : FPState) Rj (pci pcj : Z) Mjv (Wp : Z -> Prop) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fxj Rj (Z_to_bv 64 pcj) Mjv (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) Mjv ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mjv (Z_to_bv 64 a) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 a)) ->
  (forall a, Wp a -> F / 8 + SB <= a < F / 8 + SB + 8) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat -> getr Rj (reg j) = getr Ri (reg j)) ->
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
    - apply (L5SAR.fframe_shadow_client L ar LBi FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. unfold SB in X'. clear - X'; lia.
    - unfold SB in X'. pose proof GFR as (GF1 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). clear - X' D1; lia. }
  intros Mj mdj HHj AMj MRTj HIDj VISj MGMj FRj VVj.
  assert (EKj : L5SAR.ek L ar LBi FF 0 0 [] Mi Mj).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k)
             LBi LKi cri Awi Mi Mj _ [] (fun _ => False) G HHi); [intros a []|].
    intros a Ha Nw. apply FRj; [exact Ha|]. intros Wa. apply Nw. unfold PMAUK.WretX, PMAUK.Wret. left. left. right. change (ff_bytes 0 / 8) with 8. exact (WPF a Wa). }
  apply (KONT' Mj mdj VISj HIDj MGMj).
  split; [| split; [| split; [| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  - split; [rewrite (RR 2%nat) by inl; exact J2|]. split; [rewrite (RR 8%nat) by inl; exact J8|]. split; [rewrite (RR 9%nat) by inl; exact J9|].
    split; [rewrite (RR 18%nat) by inl; exact J18|]. split; [rewrite (RR 19%nat) by inl; exact J19|]. split; [rewrite (RR 20%nat) by inl; exact J20|].
    split; [rewrite (RR 21%nat) by inl; exact J21|]. split; [rewrite (RR 25%nat) by inl; exact J25|]. split; [rewrite (RR 26%nat) by inl; exact J26|].
    split; [rewrite (RR 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (RR j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR (PEC.owned si eni ki) Mi mdi LKi cri Awi Mj mdj Wp BI HHj AMj MRTj MGMj FRj).
    intros a Wa. right. right. change (ff_bytes 0 / 8) with 8. exact (WPF a Wa).
  - apply (cpre_keepA LBi 0 0 [] Mi Mj Y si smi eni ki ei EKj PMKA.wapp_nil BRBi); [unfold LBi; apply incl_appl; apply incl_refl| unfold LBi; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP].
Qed.

Lemma amid_pieceS fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fxj : FPState) Rj (pci pcj : Z) Mjv (Wp : Z -> Prop) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fxj Rj (Z_to_bv 64 pcj) Mjv (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) Mjv ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mjv (Z_to_bv 64 a) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 a)) ->
  (forall a, Wp a -> sp - 128 <= a < sp - 104) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat -> getr Rj (reg j) = getr Ri (reg j)) ->
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
  assert (EKj : L5SAR.ek L ar LBi FF sp 26624 [] Mi Mj).
  { intros a (Ha & Hc & _). apply FRj; [exact Ha|]. intros Wa. pose proof (WPF a Wa) as X'.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LBi FF' LKi cri Awi Mi _ sp 26624 a HHi GSPT (L5SAR.aclient_cons L ar LBi FF (F, 0, sp - 128 + 32) sp 26624 a Hc)) as [Y'|Y'];
      clear - X' Y' GSLO; lia. }
  apply (KONT' Mj mdj VISj HIDj MGMj FRj).
  split; [| split; [| split; [| split; [exact ST| split; [exact EIMP| exact CK]]]]].
  - split; [rewrite (RR 2%nat) by inl; exact J2|]. split; [rewrite (RR 8%nat) by inl; exact J8|]. split; [rewrite (RR 9%nat) by inl; exact J9|].
    split; [rewrite (RR 18%nat) by inl; exact J18|]. split; [rewrite (RR 19%nat) by inl; exact J19|]. split; [rewrite (RR 20%nat) by inl; exact J20|].
    split; [rewrite (RR 21%nat) by inl; exact J21|]. split; [rewrite (RR 25%nat) by inl; exact J25|]. split; [rewrite (RR 26%nat) by inl; exact J26|].
    split; [rewrite (RR 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (RR j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR (PEC.owned si eni ki) Mi mdi LKi cri Awi Mj mdj Wp BI HHj AMj MRTj MGMj FRj).
    intros a Wa. pose proof (WPF a Wa) as X'. left. unfold ocell. clear - X'; lia.
  - apply (cpre_keepA LBi sp 26624 [] Mi Mj Y si smi eni ki ei EKj PMKA.wapp_nil BRBi); [unfold LBi; apply incl_appl; apply incl_refl| unfold LBi; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP].
Qed.

Lemma pfacts_bc Mi mdi LKi cri Awi si smi eni ki ei Xi :
  PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned si eni ki) Mi mdi LKi cri Awi ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat ->
  let MVi := mrestrict (ahid Awi mdi) Mi in
  0 <= sp < 2 ^ 64
  /\ 0 <= op < 2 ^ 64
  /\ 0 <= ov < 2 ^ 64
  /\ 0 <= oec < 2 ^ 64
  /\ L5.img_clear MVi 65536 1286144
  /\ L5.u64_at RSEGS MVi 1317368 2147450880
  /\ L5.u32_at RSEGS MVi 1317376 1
  /\ 140735332487328 <= sp <= 140737488355328
  /\ sp mod 32 = 0
  /\ L5.writable RSEGS MVi (sp - 160) 160
  /\ 6914048 <= op <= 140737488354944
  /\ op mod 8 = 0
  /\ (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784)
  /\ L5KA.zeros_at MVi ((op / 8) + 2147450880) 3
  /\ L5KA.zeros_at MVi (((op + 32) / 8) + 2147450880) 44
  /\ L5KA.zeros_at MVi (((op + 20) / 8) + 2147450880) 1
  /\ L5.writable RSEGS MVi op 384
  /\ ((sp - 160) + 160 <= op \/ op + 384 <= (sp - 160))
  /\ 6914048 <= oec <= 140737488355312
  /\ oec mod 8 = 0
  /\ (2147446784 + 17592186048512 <= oec \/ oec + 16 <= 2147446784)
  /\ L5KA.zeros_at MVi ((oec / 8) + 2147450880) 2
  /\ L5.writable RSEGS MVi oec 16
  /\ ((sp - 160) + 160 <= oec \/ oec + 16 <= (sp - 160))
  /\ 6914048 <= ov <= 140737488355320
  /\ ov mod 8 = 0
  /\ (2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784)
  /\ L5KA.zeros_at MVi ((ov / 8) + 2147450880) 1
  /\ L5.writable RSEGS MVi ov 8
  /\ ((sp - 160) + 160 <= ov \/ ov + 8 <= (sp - 160))
  /\ (op + 384 <= oec \/ oec + 16 <= op)
  /\ (op + 384 <= ov \/ ov + 8 <= op)
  /\ (oec + 16 <= ov \/ ov + 8 <= oec)
  /\ 0 <= F < 2 ^ 64
  /\ 0 <= fl < 2 ^ 64
  /\ 6914048 <= F <= 140737488355264
  /\ F mod 32 = 0
  /\ L5.defined MVi F 64
  /\ L5.writable RSEGS MVi F 64
  /\ (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784)
  /\ L5.writable RSEGS MVi ((F / 8) + 2147450880) 8
  /\ L5.u64_at RSEGS MVi (F + 56) fl
  /\ 4096 <= fl <= 140737488355327
  /\ L5.writable RSEGS MVi fl 1
  /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784)
  /\ (F + 64 <= fl \/ fl + 1 <= F)
  /\ ((sp - 160) + 160 <= F \/ F + 64 <= (sp - 160))
  /\ ((sp - 160) + 160 <= fl \/ fl + 1 <= (sp - 160))
  /\ (op + 384 <= F \/ F + 64 <= op)
  /\ (op + 384 <= fl \/ fl + 1 <= op)
  /\ (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880))
  /\ (oec + 16 <= F \/ F + 64 <= oec)
  /\ (oec + 16 <= fl \/ fl + 1 <= oec)
  /\ (((oec / 8) + 2147450880) + 2 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((oec / 8) + 2147450880))
  /\ (ov + 8 <= F \/ F + 64 <= ov)
  /\ (ov + 8 <= fl \/ fl + 1 <= ov)
  /\ (((ov / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((ov / 8) + 2147450880))
  /\ (F + 64 <= 65536 \/ 65536 + 1196128 <= F)
  /\ L5.u32_at RSEGS MVi (op + 320) 1024
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
  /\ L5.u64_at RSEGS MVi (sp - 104) (bv_unsigned (getr R (reg 27)))
  /\ L5.u64_at RSEGS MVi (op + 328) 16777216
  /\ L5.u64_at RSEGS MVi ov 1258992
  /\ L5KA.zeros_at MVi 2147608265 1
  /\ L5KA.zeros_at MVi 2147608256 1
  /\ L5.u8_at RSEGS MVi (op + 16) 0.
Proof.
  intros BI CP. cbv zeta.
  entry_facts. frame_facts. pose proof BI as (HHi & AMi & MRTi & INCAi & INCLi & ASTKi & EKbi & DKbi & OWNi & FSHDi). pose proof AMi as (Mhi & MIi).
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi. unfold SB in FSWi.
  assert (BASEi : PMSTA.base_okA RSEGS PMA.AD Mi) by exact BASE.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LKi cri Awi Mi mdi HHi BASEi) as (IC0 & CSBv & CUARv). fold Hi in IC0, CSBv, CUARv. fold MVi in IC0, CSBv, CUARv.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi sp 26624 160 HHi ASTKi ltac:(clear; lia)) as (_ & _ & WS160). fold Hi in WS160. fold MVi in WS160.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold Hi in Zop, Z32, Z20, OWR, OVIS. fold MVi in Zop, Z32, Z20, OWR. fold op in Zop, Z32, Z20, OWR, OVIS.
  assert (ECX : exists v c, PMSPA.ec_at RSEGS Mi oec v c).
  { pose proof ECS as E0. unfold PECA.ec_stateA in E0. fold oec in E0.
    lazymatch type of E0 with (if ?c then _ else _) => destruct c; [destruct E0 as (v0 & _ & E1); exists v0; eexists; exact E1| exists 0, cat; exact E0] end. }
  destruct ECX as (ecv & ecc & ECat).
  pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb ecv ecc HHi FOK' ECat) as ((_ & _ & _) & ZE & EW & _ & EU & _ & _). fold Hi in ZE, EW, EU. fold MVi in ZE, EW, EU. fold oec in ZE, EW, EU.
  pose proof EA as (EVT & _ & _ & _ & _ & _ & _ & _ & EACC & _).
  pose proof (PMAPAR.ov_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb HHi FOK' (conj EVT (PMABK.aacc_sub Mi ov 56 ov 8 EACC ltac:(clear; lia) ltac:(clear; lia))))
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
  change (ff_bytes 0) with 64 in ApF, ApSF, ApFL, AeF, AeSF, AeFL, AvF, AvSF, AvFL, AsopSF, AseSF, AsvSF.
  change (64 / 8) with 8 in ApSF, AeSF, AvSF, AsopSF, AseSF, AsvSF. unfold SB in ApSF, AeSF, AvSF, AsopSF, AseSF, AsvSF.

  pose proof PA as (_ & _ & _ & _ & _ & _ & P16 & _ & _ & _ & P320 & P328 & _).
  assert (P16v : L5.u8_at RSEGS MVi (op + 16) 0)
    by (apply (proj2 (L5A.u8_at_vis Hi Mi (op + 16) 0 (OVIS (op + 16) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))); exact P16).
  assert (P320v : L5.u32_at RSEGS MVi (op + 320) 1024)
    by (apply (proj2 (L5A.u32_at_vis Hi Mi (op + 320) 1024 (OVIS (op + 320) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))); exact P320).
  assert (P328v : L5.u64_at RSEGS MVi (op + 328) 16777216)
    by (apply (proj2 (L5A.u64_at_vis Hi Mi (op + 328) 16777216 (OVIS (op + 328) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))); exact P328).
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LKi cri Awi Mi mdi 0x133600 1 HHi ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)) as VT1.
  change (0x133600 / 8 + 2147450880) with 2147608256 in VT1. fold Hi in VT1. fold MVi in VT1.
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LKi cri Awi Mi mdi 0x133648 1 HHi ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)) as VT2.
  change (0x133648 / 8 + 2147450880) with 2147608265 in VT2. fold Hi in VT2. fold MVi in VT2.

  let cl := first [ sya
      | clear - GSLO GSHI GSPT; lia | clear - O1 O3; lia | clear - O2 GSLO; lia | clear - E1' E3'; lia | clear - E2' GSLO; lia
      | clear - V1; lia | clear - V3 GSLO; lia | clear - Eop Eoec Eov; lia
      | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GFLA; lia | clear - GFBIG; lia | clear - GFLBIG; lia | clear - GF32; lia | clear - GF8; lia
      | clear - ApF; lia | clear - ApFL; lia | clear - AsopSF; lia | clear - AeF; lia | clear - AeFL; lia | clear - AseSF; lia
      | clear - AvF; lia | clear - AvFL; lia | clear - AsvSF; lia
      | clear - O8; lia | clear - Q8; lia | clear - C8m; lia | clear - V8; lia | clear - OBIG; lia | clear - EBIG; lia | clear - VBIG; lia | clear - SP32; lia
      | match goal with |- ?G => fail 100 "pfacts: cannot prove" G end ] in
  do 89 (split; [cl|]); cl.
Qed.
Lemma pfacts fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  let MVi := mrestrict (ahid Awi mdi) Mi in
  0 <= sp < 2 ^ 64
  /\ 0 <= op < 2 ^ 64
  /\ 0 <= ov < 2 ^ 64
  /\ 0 <= oec < 2 ^ 64
  /\ L5.img_clear MVi 65536 1286144
  /\ L5.u64_at RSEGS MVi 1317368 2147450880
  /\ L5.u32_at RSEGS MVi 1317376 1
  /\ 140735332487328 <= sp <= 140737488355328
  /\ sp mod 32 = 0
  /\ L5.writable RSEGS MVi (sp - 160) 160
  /\ 6914048 <= op <= 140737488354944
  /\ op mod 8 = 0
  /\ (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784)
  /\ L5KA.zeros_at MVi ((op / 8) + 2147450880) 3
  /\ L5KA.zeros_at MVi (((op + 32) / 8) + 2147450880) 44
  /\ L5KA.zeros_at MVi (((op + 20) / 8) + 2147450880) 1
  /\ L5.writable RSEGS MVi op 384
  /\ ((sp - 160) + 160 <= op \/ op + 384 <= (sp - 160))
  /\ 6914048 <= oec <= 140737488355312
  /\ oec mod 8 = 0
  /\ (2147446784 + 17592186048512 <= oec \/ oec + 16 <= 2147446784)
  /\ L5KA.zeros_at MVi ((oec / 8) + 2147450880) 2
  /\ L5.writable RSEGS MVi oec 16
  /\ ((sp - 160) + 160 <= oec \/ oec + 16 <= (sp - 160))
  /\ 6914048 <= ov <= 140737488355320
  /\ ov mod 8 = 0
  /\ (2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784)
  /\ L5KA.zeros_at MVi ((ov / 8) + 2147450880) 1
  /\ L5.writable RSEGS MVi ov 8
  /\ ((sp - 160) + 160 <= ov \/ ov + 8 <= (sp - 160))
  /\ (op + 384 <= oec \/ oec + 16 <= op)
  /\ (op + 384 <= ov \/ ov + 8 <= op)
  /\ (oec + 16 <= ov \/ ov + 8 <= oec)
  /\ 0 <= F < 2 ^ 64
  /\ 0 <= fl < 2 ^ 64
  /\ 6914048 <= F <= 140737488355264
  /\ F mod 32 = 0
  /\ L5.defined MVi F 64
  /\ L5.writable RSEGS MVi F 64
  /\ (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784)
  /\ L5.writable RSEGS MVi ((F / 8) + 2147450880) 8
  /\ L5.u64_at RSEGS MVi (F + 56) fl
  /\ 4096 <= fl <= 140737488355327
  /\ L5.writable RSEGS MVi fl 1
  /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784)
  /\ (F + 64 <= fl \/ fl + 1 <= F)
  /\ ((sp - 160) + 160 <= F \/ F + 64 <= (sp - 160))
  /\ ((sp - 160) + 160 <= fl \/ fl + 1 <= (sp - 160))
  /\ (op + 384 <= F \/ F + 64 <= op)
  /\ (op + 384 <= fl \/ fl + 1 <= op)
  /\ (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880))
  /\ (oec + 16 <= F \/ F + 64 <= oec)
  /\ (oec + 16 <= fl \/ fl + 1 <= oec)
  /\ (((oec / 8) + 2147450880) + 2 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((oec / 8) + 2147450880))
  /\ (ov + 8 <= F \/ F + 64 <= ov)
  /\ (ov + 8 <= fl \/ fl + 1 <= ov)
  /\ (((ov / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((ov / 8) + 2147450880))
  /\ (F + 64 <= 65536 \/ 65536 + 1196128 <= F)
  /\ L5.u32_at RSEGS MVi (op + 320) 1024
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
  /\ L5.u64_at RSEGS MVi (sp - 104) (bv_unsigned (getr R (reg 27)))
  /\ L5.u64_at RSEGS MVi (op + 328) 16777216
  /\ L5.u64_at RSEGS MVi ov 1258992
  /\ L5KA.zeros_at MVi 2147608265 1
  /\ L5KA.zeros_at MVi 2147608256 1
  /\ L5.u8_at RSEGS MVi (op + 16) 0.
Proof. intros MID. pose proof MID as (_ & BI & CP & _). exact (pfacts_bc _ _ _ _ _ _ _ _ _ _ _ BI CP). Qed.

Ltac open_vf H := destruct H as (VF1 & VF2 & VF3 & VF4 & VF5 & VF6 & VF7 & VF8 & VF9 & VF10 & VF11 & VF12 & VF13 & VF14 & VF15 & VF16 & VF17 & VF18 & VF19 & VF20 & VF21 & VF22 & VF23 & VF24 & VF25 & VF26 & VF27 & VF28 & VF29 & VF30 & VF31 & VF32 & VF33 & VF34 & VF35 & VF36 & VF37 & VF38 & VF39 & VF40 & VF41 & VF42 & VF43 & VF44 & VF45 & VF46 & VF47 & VF48 & VF49 & VF50 & VF51 & VF52 & VF53 & VF54 & VF55 & VF56 & VF57 & VF58 & VF59 & VF60 & VF61 & VF62 & VF63 & VF64 & VF65 & VF66 & VF67 & VF68 & VF69 & VF70 & VF71 & VF72 & VF73 & VF74 & VF75 & VF76 & VF77 & VF78 & VF79 & VF80 & VF81 & VF82 & VF83 & VF84 & VF85 & VF86 & VF87 & VF88 & VF89 & VF90).

Definition VAL (d c x49 x : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp | 33%nat => d | 36%nat => op | 37%nat => ov | 38%nat => oec | 39%nat => c | 47%nat => F | 48%nat => fl | 49%nat => x49 | 50%nat => x
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

Ltac fcl := first [sya | unfold PEABAP1.aligned; sya | unfold PEABAP2.aligned; sya | unfold PEABAP3.aligned; sya].

Tactic Notation "pz" constr(conc) constr(fxi) constr(Ri) constr(d) constr(c) constr(x49) constr(x) "as" ident(P) :=
  let mv := lazymatch goal with m := mrestrict _ _ |- _ => m end in
  pose proof (conc fxi Ri mv (VAL d c x49 x)) as P; unfold VAL in P; cbn beta iota in P.

Tactic Notation "keep_only" ne_hyp_list(l) :=
  clear - LY HIok ICok ILY PO LYa PEEK IGN SRD GL MKE PMI PMS PMSU VBI VBL PMODE HH AM K0 ENT FRM FRS FOK SP32 A10 A11 A12 CPRE INCS POK MP NB HB CRED KONT
          op ov oec ois osk otb WR G APART FF' l.

Lemma ec_vis0 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_ec Y = false -> L5.u32_at RSEGS (mrestrict (ahid Awi mdi) Mi) oec 0.
Proof.
  intros MID EC. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
  unfold PECA.ec_stateA in ECS. rewrite EC in ECS. fold oec in ECS.
  pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb 0 cat HHi FOK' ECS) as ((_ & _ & _) & _ & _ & _ & EU & _ & _). exact EU.
Qed.
Lemma ec_vis1 fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_ec Y = true ->
  exists v, 1 <= v <= 64 /\ L5.u32_at RSEGS (mrestrict (ahid Awi mdi) Mi) oec v.
Proof.
  intros MID EC. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
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
  assert (SZK : forall Mc lo g, L5SAR.ek L ar LBX FF sp 26624 WR M Mc -> sp - 26624 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g).
  { intros Mc lo g EKc H1' H2' H3' H4'.
    assert (WAPPR : PMKA.wapp WR).
    { intros rr Hin. destruct rr as [ra' rn]. unfold BIGSHADOW_LO, BIGSHADOW_HI. cbn [fst snd].
      pose proof FSAPP as (FA0 & FA1 & FA2).
      unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
      cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <-; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia|]). destruct Hin. }
    apply (PMKA.stksh_keepA L ar LBX FF sp 26624 WR M Mc EKc WAPPR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
    apply (PMKA.shadow_zero_sub M (sp - 26624) 3328); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
    apply PMKA.mod16_8'. replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  unfold PECSA.make_ec_spec, PECSPA.make_ec_spec in MKE.
  apply (MKE fxi Ri Mi mdi K LBi FF' LKi Awi cri oec v (sp - 128) q ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 26624 128 14336 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply SZK; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 14336) with (sp + (-904) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMAUAR.ffroomA_push 7 1 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
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
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned si eni ki) M6 model6 LK6 cri Aw6).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PEC.owned si eni ki) (PEC.owned si eni ki) Mi mdi LKi cri Awi M6 model6 LK6 cri Aw6 14336 Wc6 BI HP6 HH6 AM6 MRT6 INCAw6 INCLK6);
      [clear; lia| clear; lia| | | intros a X'; exact X'].
    - intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
      pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
      assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
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
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 0, sp - 128 + 32)] sp 26624 (sp - 128) 14336 Wc6 Wc6 Mi M6 ltac:(rewrite app_nil_l; exact HP6) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK6.
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
    split; [rewrite (R6c 21%nat) by inl; exact J21|]. split; [rewrite (R6c 25%nat) by inl; exact J25|]. split; [rewrite (R6c 26%nat) by inl; exact J26|].
    split; [rewrite (R6c 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (R6c j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (cpre_stepA LBi sp 26624 Wc6 Mi M6 Y si smi eni ki ei (w_ec true Y) si true EK6 WAPP6 BRBi).
    + unfold LBi. apply incl_appl. apply incl_refl.
    + unfold LBi. apply incl_appr. exact INCS.
    + intros i Hi' N1 N2 rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y']; [clear - N2 Y'; lia| clear - Hi' Y' Eop O1; lia].
    + intros q' m Hq. exact (OUTB6 q' m Hq).
    + reflexivity. + reflexivity. + reflexivity.
    + apply (PMKA.parser_keepA RSEGS AD L ar LBi FF sp 26624 Wc6 Mi M6 EK6 WAPP6 FRB BRBi _ _ _ AOP); [| | | | | exact PA].
      * unfold LBi, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. left. exact Hx.
      * intros i Hi' rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y']; [clear - Hi' Y' Eop Eoec; lia| clear - Hi' Y' Eop O1; lia].
      * unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.src_own; left; reflexivity.
      * unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
      * intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.vs_own. rewrite E0. right; right; left; reflexivity.
    + apply (PMAPAR.base_keepW L ar C LY LBi FF sp 26624 Wc6 Mi M6 EK6); [| | | | exact BASE].
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

Lemma wr_wav : forall rr a, In rr WR -> L5.in_rng rr a -> ~ ocell sp a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 0 / 8).
Proof.
  entry_facts. frame_facts.
  assert (WRR' : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 2040) \/ (0x674080 <= a < 0x695df4)).
  { intros rr a Hin Hr. unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
  intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
  pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  pose proof FSAPP as (FA0 & FA1 & FA2).
  destruct (WRR' rr a Hin Hr) as [X'|X']; (split; [clear - X' SLO SPT F2 FSCEIL; lia|]).
  - destruct FA1 as [Y'|Y']; clear - X' Y' DF1 DF2 F1 F2; lia.
  - clear - X' DF1; lia.
Qed.

Lemma wr_F : forall rr a, In rr WR -> L5.in_rng rr a -> ~ (F <= a < F + 64).
Proof.
  entry_facts. frame_facts.
  assert (WRR' : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 2040) \/ (0x674080 <= a < 0x695df4)).
  { intros rr a Hin Hr. unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
  assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF 0 0 (a + i)).
  { intros a n X1 X2 X3 i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - X1 X2 Hi'; lia| intros Y'; clear - X1 X2 Hi' Y'; lia]. }
  destruct (APART (fb + 32) 2008 0 0 (CLfb (fb + 32) 2008 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z' & _). change (ff_bytes 0) with 64 in Z'.
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

Lemma szk Mc lo g : L5SAR.ek L ar LBX FF sp 26624 WR M Mc -> sp - 26624 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g.
Proof.
  entry_facts. intros EKc H1' H2' H3' H4'.
  apply (PMKA.stksh_keepA L ar LBX FF sp 26624 WR M Mc EKc wappR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
  apply (PMKA.shadow_zero_sub M (sp - 26624) 3328); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
  apply PMKA.mod16_8'. replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
Qed.

Lemma call_gl (q : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 op -> getr Ri (reg 11) = Z_to_bv 64 oec ->
  PECSPA.mp_gl tt p Y ->
  (forall fx' R' M' md' LK' Aw' cr' si' smi' ei', regs_preserved Ri R' -> PECSPA.gl_ret p Y R' ->
      amid fx' R' M' md' LK' Aw' cr' si' smi' eni ki ei' (PECSPA.gl_post p Y) ->
      PM.p_tb si' = PM.p_tb si -> PM.p_tg si' = PM.p_tg si -> PM.p_b si' = PM.p_b si -> PM.p_k si' = PM.p_k si ->
      (forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8 -> M' (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      (forall a, F + 32 <= a < F + 56 -> M' (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri (pa_get_length AD) Mi mdi) K.
Proof.
  intros MID J1 RAq J10 J11 MPG KONT'. entry_facts. frame_facts. open_amid MID.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
  unfold PECSA.get_length_spec, PECSPA.get_length_spec in GL.
  apply (GL PMODE fxi Ri Mi mdi K LBX FF' LKi Awi cri (sp - 128) q fb cat p Y si str smi eni ki ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 5) with 22528. change (22528 / 8) with 2816.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 26624 128 22528 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 22528) with (sp + (-1416) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMAUAR.ffroomA_push 7 5 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
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
  assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned s4 eni ki) M4 model4 LK4 cr4 Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) [] (PEC.owned s4 eni ki) Mi mdi LKi cri Awi M4 model4 LK4 cr4 Aw4 22528 WR BI HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
      [clear; lia| clear; lia| exact wr_wav| intros a _ X'; exact X'| intros a X'; exact X']. }
  assert (FSH4 : forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8 -> M4 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
    assert (D2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
    intros a Ha. apply (proj1 HP4). split; [clear - Ha D1 D2; lia| split].
    - apply (L5SAR.fframe_shadow_client L ar LBX FF' (sp - 128) 22528 F 0 (sp - 128 + 32)); [left; reflexivity|].
      change (ff_bytes 0) with 64. unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Ha; lia.
    - intros rr Hin Hr. exact (proj2 (wr_wav rr a Hin Hr) ltac:(change (ff_bytes 0 / 8) with 8; unfold SB; exact Ha)). }
  assert (FDK4 : forall a, F + 32 <= a < F + 56 -> M4 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { pose proof GFR as (GF1 & GF2 & _). intros a Ha. apply (proj1 HP4). split; [clear - Ha GF1 GF2; lia| split].
    - apply (L5SAR.fframe_client L ar LBX FF' (sp - 128) 22528 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64. clear - Ha; lia.
    - intros rr Hin Hr. exact (wr_F rr a Hin Hr ltac:(clear - Ha; lia)). }
  apply (KONT' fx4 R4 M4 model4 LK4 Aw4 cr4 s4 sm4 e4 RP4 RET4); [| exact ETB| exact ETG| exact EB| exact EKK| exact FSH4| exact FDK4].
  split; [|split; [exact BI4| split; [exact CPRE4| split; [exact (PMAPAR.src_step_transA _ _ _ _ _ _ ST STEP4)| split; [intros X'; exact (EE4 (EIMP X'))| exact (credit_keep_trans _ _ _ _ _ _ CK CK4)]]]]].
  pose proof (fun j Hj => L5SAR.cs_of_preserved Ri R4 j RP4 Hj) as R4c.
  split; [rewrite (R4c 2%nat) by inl; exact J2|]. split; [rewrite (R4c 8%nat) by inl; exact J8|]. split; [rewrite (R4c 9%nat) by inl; exact J9|].
  split; [rewrite (R4c 18%nat) by inl; exact J18|]. split; [rewrite (R4c 19%nat) by inl; exact J19|]. split; [rewrite (R4c 20%nat) by inl; exact J20|].
  split; [rewrite (R4c 21%nat) by inl; exact J21|]. split; [rewrite (R4c 25%nat) by inl; exact J25|]. split; [rewrite (R4c 26%nat) by inl; exact J26|].
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
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
  unfold PECSPA.eslot_spec in SPEC.
  apply (SPEC PMODE av fxi Ri Mi mdi K LBX FF' LKi Awi cri (sp - 128) q fb cat p Y si str smi eni ki ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 4) with 20480. change (20480 / 8) with 2560.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 26624 128 20480 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 20480) with (sp + (-1288) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomA_push 7 4 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
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
  assert (BI2 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned si en2 k2) Mn mdn LKn cr2 Awn).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
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
  split; [rewrite (Rnc 21%nat) by inl; exact J21|]. split; [rewrite (Rnc 25%nat) by inl; exact J25|]. split; [rewrite (Rnc 26%nat) by inl; exact J26|].
  split; [rewrite (Rnc 27%nat) by inl; exact J27|].
  intros j Hj. rewrite (Rnc j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
Qed.

Lemma stk_bz fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> forall q, sp - 26624 <= q < sp -> byte_at Mi (HeapIfaceA.S q) 0.
Proof.
  intros MID q Hq. entry_facts. open_amid MID.
  assert (M8a : (sp - 26624) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
  pose proof (szk Mi (sp - 26624) 3328 EKbi ltac:(clear; lia) ltac:(clear; lia) M8a ltac:(clear; lia)) as SZ.
  assert (E : HeapIfaceA.S q = HeapIfaceA.S (sp - 26624) + (q / 8 - (sp - 26624) / 8)) by (unfold HeapIfaceA.S; clear; lia).
  rewrite E. apply SZ.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  clear - Hq M8a. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma stk_cell fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y q n :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> sp - 128 <= q -> q + n <= sp - 104 -> 0 < n ->
  PMSPA.accA Mi q n /\ byte_at Mi (HeapIfaceA.S q) 0 /\ PMSAX.arg_ok ar FF' (sp - 128) (op + 360) q n
  /\ (forall v, L5.u32_at RSEGS (mrestrict (ahid Awi mdi) Mi) q v -> n = 4 -> L5.u32_at RSEGS Mi q v)
  /\ (forall v, L5.u64_at RSEGS (mrestrict (ahid Awi mdi) Mi) q v -> n = 8 -> L5.u64_at RSEGS Mi q v).
Proof.
  intros MID H1 H2 Hn. entry_facts. frame_facts. open_amid MID.
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *. vis_amid BI Hi MVi.
  split. { intros a Ha. left. apply (stk_bz fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y MID). clear - Ha H1 H2; lia. }
  split; [apply (stk_bz fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y MID); clear - H1 H2 Hn; lia|].
  split. { unfold PMSAX.arg_ok. split; [right; split; [clear - H1; lia| clear - H2 GSHI; lia]| right; clear - H1 F2 FSCEIL GSLO Eop; lia]. }
  split. { intros v Xv En. subst n. apply (proj1 (L5A.u32_at_vis Hi Mi q v (L5A.avis_sub Hi (sp - 128) (sp - (sp - 128)) q 4 VSi ltac:(clear - H1; lia) ltac:(clear - H2; lia)) ltac:(clear - H1 GSLO GSHI GSPT; lia) ltac:(clear - H2 GSHI GSPT; lia))). exact Xv. }
  intros v Xv En. subst n. apply (proj1 (L5A.u64_at_vis Hi Mi q v (L5A.avis_sub Hi (sp - 128) (sp - (sp - 128)) q 8 VSi ltac:(clear - H1; lia) ltac:(clear - H2; lia)) ltac:(clear - H1 GSLO GSHI GSPT; lia) ltac:(clear - H2 GSHI GSPT; lia))). exact Xv.
Qed.

Lemma call_src (pc aln : Z) (args : list fframe -> bvmap 5 word -> (word -> option byte) -> Z -> Z -> PM.pst -> Prop)
      (Wx : bvmap 5 word -> list L5.range -> Prop)
      (res : list Z -> bvmap 5 word -> bvmap 5 word -> (word -> option byte) -> PM.srcst -> PM.srcst -> PM.strm -> PM.strm -> Prop)
      (SPEC : PECSPA.csrc_spec RSEGS AD L ar HI pc 4 aln args Wx res) (Wq : list L5.range) (ra : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_more Y = true -> s_done Y = false -> 0 <= s_pos Y <= blen p ->
  getr Ri (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr Ri (reg 10) = Z_to_bv 64 (op + 24) ->
  (aln = 16 \/ aln = 32) -> args FF' Ri Mi (sp - 128) fb si -> Wx Ri Wq ->
  (forall rr, In rr Wq -> F + 32 <= fst rr /\ fst rr + snd rr <= F + 40) ->
  (forall p0 Ra Rb Mb sa sb ma mb, res p0 Ra Rb Mb sa sb ma mb -> PECSPA.cwin RSEGS Mb p0 sb mb) ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 src2 smi2, regs_preserved Ri R2 -> res p Ri R2 M2 (PM.p_src si) src2 smi smi2 ->
      PEC.pos_of p (PM.p_src si) smi = s_pos Y ->
      (forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8 -> M2 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      (forall a, F + 32 <= a < F + 56 -> L5.outside Wq a -> M2 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      amid fx2 R2 M2 md2 LK2' Aw2 cri (PMSPA.with_src si src2) smi2 eni ki ei (w_pos (PEC.pos_of p src2 smi2) Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 ra M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pc Mi mdi) K.
Proof.
  intros MID MORE DONE PPOS J1 RAq J10 ALN ARGS WXQ WQR' RESW KX. entry_facts. frame_facts. open_amid MID.
  assert (WQR : forall rr a, In rr Wq -> L5.in_rng rr a -> F + 32 <= a < F + 40).
  { intros rr a Hin Hr. pose proof (WQR' rr Hin) as (W1 & W2). unfold L5.in_rng in Hr. clear - W1 W2 Hr. lia. }
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WBi & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDi & NDFi & _).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
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
  change (ff_bytes 0) with 64 in ApF, ApSF, AiF, AiSF. change (64 / 8) with 8 in ApSF, AiSF.
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
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 26624 128 20480 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 20480) with (sp + (-1288) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomA_push 7 4 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
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
            (op + 280 <= a < op + 320) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (qc <= a < qc + 16384) \/ (F + 32 <= a < F + 40 /\ ~ L5.outside Wq a)).
  { intros rr a Hin Hr. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is AD PeCLayoutA.CADDR_A] in Hin. fold qc in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|Hin]]]];
      [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eop Eois; left; lia
      |unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eop Eois; right; left; lia
      |unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eop Eois; right; right; left; lia
      |unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr; clear - Hr; right; right; right; left; lia
      |right; right; right; right; split; [exact (WQR rr a Hin Hr)| intros O; exact (O rr Hin Hr)]]. }
  assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (D2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (WAV4 : forall rr a, In rr Wc -> L5.in_rng rr a -> ~ ocell sp a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 0 / 8)).
  { intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
    destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|[X'|(X' & XW')]]]]; (split; [clear - X' O2 I2 Bq4 GFCEIL GSLO Eop Eois GF2 GFR; lia|]).
    + clear - X' OBIG D1 D2; lia.
    + clear - X' IBIG D1 D2; lia.
    + clear - X' IBIG D1 D2; lia.
    + destruct Bq5 as [Yb|Yb]; clear - X' Yb D1 D2; lia.
    + destruct GFBIG as [Yb|Yb]; clear - X' Yb D1 D2 GFR; lia. }

  assert (FSH4 : forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8 -> M4 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP4). split; [clear - Ha D1 D2; lia| split].
    - apply (L5SAR.fframe_shadow_client L ar LBi FF' (sp - 128) 20480 F 0 (sp - 128 + 32)); [left; reflexivity|].
      change (ff_bytes 0) with 64. unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Ha; lia.
    - intros rr Hin Hr. exact (proj2 (WAV4 rr a Hin Hr) ltac:(change (ff_bytes 0 / 8) with 8; unfold SB; exact Ha)). }

  assert (FDK4 : forall a, F + 32 <= a < F + 56 -> L5.outside Wq a -> M4 (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { intros a Ha Hoq. apply (proj1 HP4). split; [clear - Ha GF1 GF2; lia| split].
    - apply (L5SAR.fframe_client L ar LBi FF' (sp - 128) 20480 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64. clear - Ha; lia.
    - assert (AOFF : PMSPA.aobjA FF' (F + 32) 24) by (exists (F, 0, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; clear; lia]).
      intros rr Hin Hr. destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|[X'|(X' & XW')]]]].
      + destruct (APART (op + 280) 40 0 0 (CLfb (op + 280) 40 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z' & _). change (ff_bytes 0) with 64 in Z'. clear - Ha X' Z'; lia.
      + destruct (APART (ois + 40) 8 0 0 (CLfb (ois + 40) 8 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z' & _). change (ff_bytes 0) with 64 in Z'. clear - Ha X' Z'; lia.
      + destruct (APART (ois + 152) 4 0 0 (CLfb (ois + 152) 4 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z' & _). change (ff_bytes 0) with 64 in Z'. clear - Ha X' Z'; lia.
      + destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 (F + 32) 24 HHi Iq AOFF) as [Z'|Z']; clear - Ha X' Z'; lia.
      + exact (XW' Hoq). }
  assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned si eni ki) M4 md4 LK4 cri Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) (PEC.owned si eni ki) (PEC.owned si eni ki) Mi mdi LKi cri Awi M4 md4 LK4 cri Aw4 20480 Wc BI HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
      [clear; lia| clear; lia| exact WAV4| | intros a X'; exact X'].
    intros a Hc Ho rr Hin Hr. destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|[X'|(X' & XW')]]]].
      + apply (Ho (PMSP.o_src AD fb + 256, 40)); [unfold WR; wr_mem 1| wr_rng; clear - X' Eop; lia].
      + apply (Ho (PMSP.o_is AD fb + 40, 8)); [unfold WR; wr_mem 2| wr_rng; clear - X' Eois; lia].
      + apply (Ho (PMSP.o_is AD fb + 152, 4)); [unfold WR; wr_mem 3| wr_rng; clear - X' Eois; lia].
      + assert (Iq' : In (qc, 16384) (PEC.owned si eni ki)) by (unfold PEC.owned; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
        exact (PMARS1.own_not_aclient L ar C HI HIok (PEC.owned si eni ki) LBX FF' LKi cri Awi Mi _ qc 16384 a sp 26624 HHi Iq' X' (L5SAR.aclient_cons L ar LBX FF (F, 0, sp - 128 + 32) sp 26624 a Hc)).
      + apply (GNCF a); [left; clear - X' GFR; lia| exact Hc]. }
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 0, sp - 128 + 32)] sp 26624 (sp - 128) 20480 Wc Wc Mi M4 ltac:(rewrite app_nil_l; exact HP4) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK4.
  assert (OUTc : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op + 280 \/ op + 320 <= a) -> (a + n <= ois + 40 \/ ois + 48 <= a) ->
                 (a + n <= ois + 152 \/ ois + 156 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i).
  { intros a n X1 X2 X3 X4 X5 i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Yc|[Yc|[Yc|[Yc|(Yc & YW)]]]]; [clear - Hi' Yc X3; lia| clear - Hi' Yc X4; lia| clear - Hi' Yc X5; lia| |].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 a n HHi Iq (PMAUAR.aobjA_push FF a n _ (AOF a n X1 X2))) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - destruct (APART a n 0 0 (CLfb a n X1 X2 ltac:(clear - Hi'; lia)) ltac:(clear - Hi'; lia)) as (Z' & _). change (ff_bytes 0) with 64 in Z'. clear - Hi' Yc Z' GFR; lia. }
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
  { apply (PECFA.enc_keepA RSEGS EE L ar LBi FF sp 26624 Wc Mi M4 EK4 WAPPc FRB BRBi ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINC| | exact EA].
    - apply OUTc; clear - Eop Eov Eois; lia.
    - intros Hp. assert (INe : In (PEC.en_b eni, PEC.ESZ * PEC.ecap (PEC.en_k eni)) (PEC.enc_own eni)).
      { unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      refine (OUTBc _ _ (EINC _ INe) _). apply (NEQ _ (PEC.ESZ * PEC.ecap (PEC.en_k eni))). apply in_or_app. left. exact INe. }
  assert (VREF4 : L5.u64_at RSEGS M4 (op + 384) ov).
  { apply (PMKA.u64_keepA RSEGS L ar LBi FF sp 26624 Wc Mi M4 EK4 WAPPc FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF].
    apply OUTc; clear - Eop Eois; lia. }
  assert (SKA4 : PESKA.sink_atA RSEGS L ar P M4 osk ki).
  { apply (PECFA.sink_keepA RSEGS L ar LBi FF sp 26624 Wc Mi M4 EK4 WAPPc FRB BRBi P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [| exact KINC| | exact SKA].
    - apply OUTc; clear - Eop Eosk Eois; lia.
    - intros Hp. assert (INk : In (PESK.sk_b ki, PESK.sk_c ki) (PESK.sink_own ki)).
      { unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      refine (OUTBc _ _ (KINC _ INk) _). apply (NEQ _ (PESK.sk_c ki)). apply in_or_app. right. apply in_or_app. left. exact INk. }
  assert (ERR4 : PESTA.err_okA RSEGS AD AAD EE M4 ei).
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBi FF sp 26624 Wc Mi M4 EK4 ei PECSA.addrs_wf_A); [| exact ERR].
    intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUTcI; exact DI. }
  assert (BASE4 : PMSTA.base_okA RSEGS AD M4).
  { change (PMSTA.base_okA RSEGS PMA.AD M4). apply (PMASK.base_keep L ar C LY LBi FF sp 26624 Wc Mi M4 EK4); [| exact BASE].
    intros a Ha rr Hin Hr. destruct (WcR rr a Hin Hr) as [Yc|[Yc|[Yc|[Yc|(Yc & YW)]]]]; [clear - Ha Yc O1; lia| clear - Ha Yc I1; lia| clear - Ha Yc I1; lia| destruct Bqi as [Z'|Z']; clear - Ha Yc Z'; lia| clear - Ha Yc GFR; lia]. }
  assert (ECS4 : PECA.ec_stateA RSEGS AD M4 fb (s_ec Y) cat).
  { apply (PECFA.ec_state_keepA RSEGS AD L ar LBi FF sp 26624 Wc Mi M4 EK4 WAPPc FRB fb (s_ec Y) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
    fold oec. apply OUTc; clear - Eop Eoec Eois; lia. }
  assert (ACC4 : PMSPA.accA M4 op PECA.RDR_BYTES).
  { pose proof BI4 as (_ & _ & _ & _ & _ & _ & EKb4 & _).
    exact (PMKA.acc_keepA' L ar LBX FF sp 26624 WR M M4 EKb4 wappR FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CPRE))))))))))))). }
  assert (QC4 : PM.sr_qc src4 = qc) by (destruct STEP4 as (X' & _); exact X').
  set (s4 := PMSPA.with_src si src4) in *.
  assert (EOWN : PM.parser_own s4 = PM.parser_own si) by (unfold s4, PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC4; reflexivity).
  assert (EOWN4 : PEC.owned s4 eni ki = PEC.owned si eni ki) by (unfold PEC.owned; rewrite EOWN; reflexivity).

  assert (CONT4 : PEC.content_ok RSEGS AD M4 fb p src4 str sm4).
  { destruct (RESW _ _ _ _ _ _ _ _ RES4) as (CWP & CWB & CW5). pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS3 & _). pose proof VS3 as (_ & _ & VSF3).
    apply (PECF.content_ok_step RSEGS AD Mi M4 fb p (PM.p_src si) str smi src4 sm4); [clear - I1 Eois; unfold PMSP.o_is; cbn [pa_off_is AD PeCLayoutA.CADDR_A]; lia| clear - I3 Eois; unfold PMSP.o_is; cbn [pa_off_is AD PeCLayoutA.CADDR_A]; lia| | | | exact (proj1 CWP)| exact CWB| exact CW5| exact CONT].
    - unfold PMSP.o_is. cbn [pa_off_is AD PeCLayoutA.CADDR_A]. change (fb + 96) with ois.
      exact (proj1 (PMKA.agA_obj L ar LBi FF sp 26624 Wc Mi M4 EK4 WAPPc FRB (ois + 80) 24 (AOF (ois + 80) 24 ltac:(lia) ltac:(lia)) (OUTc (ois + 80) 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))).
    - intros c0 n0 q0 Es. cbn in VSF3. rewrite Es in VSF3. cbn in VSF3. destruct VSF3 as (_ & _ & _ & Hn0 & Hc0 & _).
      assert (IN0 : In (q0, c0) LBi) by (apply SINC; unfold PM.vs_own; rewrite Es; left; reflexivity).
      destruct (BRBi _ IN0) as (B0' & B1'). cbn [fst snd] in B0', B1'.
      split; [exact B0'|]. split; [clear - B1'; lia|]. split; [clear - Hn0; lia|].
      refine (proj1 (PMKA.agA_blk L ar LBi FF sp 26624 Wc Mi M4 EK4 WAPPc BRBi q0 c0 IN0 _)).
      refine (OUTBc q0 c0 IN0 _). apply (NEQ q0 c0). apply in_or_app. right. apply in_or_app. right. apply INCS. unfold PM.vs_own. rewrite Es. left. reflexivity.
    - intros n0 Es. cbn in VSF3. rewrite Es in VSF3. cbn in VSF3. clear - VSF3. lia. }
  assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr Ri (reg j))
    by (intros j Hj; exact (L5SAR.cs_of_preserved Ri R4 j RP4 Hj)).
  apply (KX fx4 R4 M4 md4 LK4 Aw4 src4 sm4 RP4 RES4 POS FSH4 FDK4).
  unfold amid. split; [| split; [rewrite <- EOWN4 in BI4; exact BI4| split; [| split; [| split; [exact EIMP|]]]]].
  - split; [rewrite (R4c 2%nat) by inl; exact J2|]. split; [rewrite (R4c 8%nat) by inl; exact J8|]. split; [rewrite (R4c 9%nat) by inl; exact J9|].
    split; [rewrite (R4c 18%nat) by inl; exact J18|]. split; [rewrite (R4c 19%nat) by inl; exact J19|]. split; [rewrite (R4c 20%nat) by inl; exact J20|].
    split; [rewrite (R4c 21%nat) by inl; exact J21|]. split; [rewrite (R4c 25%nat) by inl; exact J25|]. split; [rewrite (R4c 26%nat) by inl; exact J26|].
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

Lemma call_peek (ra : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_more Y = true -> s_done Y = false -> 0 <= s_pos Y <= blen p ->
  getr Ri (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr Ri (reg 10) = Z_to_bv 64 (op + 24) ->
  (forall (fxb : FPState) Rb Mb mdb LKb Awb srcb smb, regs_preserved Ri Rb ->
      ((getr Rb (reg 10) = Z_to_bv 64 256 /\ s_pos Y = blen p) \/ (s_pos Y < blen p /\ getr Rb (reg 10) = Z_to_bv 64 (bat p (s_pos Y)) /\ 1 <= PM.sr_rem srcb)) ->
      (forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8 -> Mb (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      (forall a, F + 32 <= a < F + 56 -> Mb (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      amid fxb Rb Mb mdb LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei Y ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxb) RSEGS Rb ra Mb mdb) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri (pa_peek AD) Mi mdi) K.
Proof.
  intros MID MORE DONE PPOS J1 RAq J10 KX.
  pose proof PEEK as SP. unfold PECSA.peek_spec, PECSPA.peek_spec in SP.
  apply (call_src (pa_peek AD) 32 PMSPA.no_args PMSPA.no_W (PECSPA.cpeek_res RSEGS) SP [] ra fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y MID MORE DONE PPOS J1 RAq J10
           ltac:(right; reflexivity) I eq_refl ltac:(intros rr [])).
  { intros p0 Ra Rb Mb sa sb ma mb (_ & CW & _). exact CW. }
  intros fxb Rb Mb mdb LKb Awb srcb smb RPb RES POS FSHb FDKb MIDb.
  destruct RES as (CONS & CW & ALT). unfold PMSPA.consumed in CONS.
  assert (EP : PEC.pos_of p srcb smb = s_pos Y) by (unfold PEC.pos_of in POS |- *; clear - CONS POS; lia).
  rewrite EP, w_pos_self in MIDb. rewrite EP in ALT. rewrite L5K.rl10 in ALT.
  apply (KX fxb Rb Mb mdb LKb Awb srcb smb RPb); [| exact FSHb| intros a Ha; exact (FDKb a Ha ltac:(intros rr []))| exact MIDb].
  destruct ALT as [(A1 & A2)|(A1 & A2 & A3)]; [left; split; [exact A1| first [exact A2 | symmetry; exact A2]]| right; split; [exact A1| split; [exact A2| exact A3]]].
Qed.

Lemma call_ignore (ra : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_more Y = true -> s_done Y = false -> 0 <= s_pos Y < blen p ->
  getr Ri (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr Ri (reg 10) = Z_to_bv 64 (op + 24) -> getr Ri (reg 11) = Z_to_bv 64 1 ->
  1 <= PM.sr_rem (PM.p_src si) ->
  (forall (fxb : FPState) Rb Mb mdb LKb Awb srcb smb, regs_preserved Ri Rb ->
      (forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8 -> Mb (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      (forall a, F + 32 <= a < F + 56 -> Mb (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      amid fxb Rb Mb mdb LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos Y + 1) Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxb) RSEGS Rb ra Mb mdb) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri (pa_ignore AD) Mi mdi) K.
Proof.
  intros MID MORE DONE PPOS J1 RAq J10 J11 REM KX.
  pose proof IGN as SP. unfold PECSA.ignore_spec, PECSPA.ignore_spec in SP.
  apply (call_src (pa_ignore AD) 32 PMSPA.ignore_args PMSPA.no_W (PECSPA.cignore_res RSEGS) SP [] ra fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y MID MORE DONE ltac:(clear - PPOS; lia) J1 RAq J10
           ltac:(right; reflexivity) J11 eq_refl ltac:(intros rr [])).
  { intros p0 Ra Rb Mb sa sb ma mb (CW & _). exact CW. }
  intros fxb Rb Mb mdb LKb Awb srcb smb RPb RES POS FSHb FDKb MIDb.
  destruct RES as (CW & ALT). unfold PMSPA.consumed in ALT.
  pose proof MID as (_ & _ & CP & _). pose proof CP as (_ & _ & _ & _ & _ & _ & _ & _ & CONT & _).
  assert (UNR : PM.unread (PM.p_src si) smi = blen p - s_pos Y) by (unfold PEC.pos_of in POS; clear - POS; lia).
  assert (EP : PEC.pos_of p srcb smb = s_pos Y + 1).
  { destruct ALT as [C1|(C0 & U0)]; [unfold PEC.pos_of in POS |- *; clear - C1 POS; lia|].
    exfalso. pose proof CONT as (_ & _ & _ & WIN & _). clear - C0 U0 UNR PPOS REM WIN. unfold PM.unread in *. lia. }
  rewrite EP in MIDb. exact (KX fxb Rb Mb mdb LKb Awb srcb smb RPb FSHb (fun a Ha => FDKb a Ha ltac:(intros rr [])) MIDb).
Qed.

Lemma call_read (ra : Z) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y -> s_more Y = true -> s_done Y = false -> 0 <= s_pos Y <= blen p ->
  getr Ri (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra ->
  getr Ri (reg 10) = Z_to_bv 64 (op + 24) -> getr Ri (reg 11) = Z_to_bv 64 (F + 32) -> getr Ri (reg 12) = Z_to_bv 64 1 ->
  L5.u8_at RSEGS (mrestrict (ahid Awi mdi) Mi) (F / 8 + 2147450880 + 4) 1 ->
  (forall (fxb : FPState) Rb Mb mdb LKb Awb srcb smb d, regs_preserved Ri Rb -> getr Rb (reg 10) = Z_to_bv 64 d -> 0 <= d <= 1 ->
      (d < 1 -> s_pos Y + d = blen p) -> s_pos Y + d <= blen p ->
      L5.bytes_at RSEGS Mb (F + 32) (UbjRef.slice p (s_pos Y) d) -> L5.u8_at RSEGS Mb (F / 8 + 2147450880 + 4) 1 ->
      amid fxb Rb Mb mdb LKb Awb cri (PMSPA.with_src si srcb) smb eni ki ei (w_pos (s_pos Y + d) Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxb) RSEGS Rb ra Mb mdb) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri (pa_src_read AD) Mi mdi) K.
Proof.
  intros MID MORE DONE PPOS J1 RAq J10 J11 J12 SHB KX. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  pose proof GFR as (GF1 & GF2 & _).
  assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF 0 0 (a + i)).
  { intros a n X1 X2 X3 i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - X1 X2 Hi'; lia| intros Y'; clear - X1 X2 Hi' Y'; lia]. }
  destruct (APART op 384 0 0 (CLfb op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (ApF & _).
  destruct (APART ois 272 0 0 (CLfb ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AiF & _).
  change (ff_bytes 0) with 64 in ApF, AiF.
  assert (FDm : L5.defined Mi F 64) by (apply (proj1 (L5A.defined_vis Hi Mi F 64 VFi)); exact FDi).
  assert (SHBm : L5.u8_at RSEGS Mi (F / 8 + 2147450880 + 4) 1).
  { apply (proj1 (L5A.u8_at_vis Hi Mi (F / 8 + 2147450880 + 4) 1 (L5A.avis_sub Hi (F / 8 + SB) 8 (F / 8 + 2147450880 + 4) 1 VSHi ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
             ltac:(clear - GF1; lia) ltac:(unfold SB; clear - GF1 GF2; lia))). exact SHB. }
  assert (ACCq : PMSPA.accA Mi (F + 32) 1).
  { unfold PMSPA.accA, aacc. intros a Ha. unfold S.
    assert (Da : a / 8 + SB = F / 8 + 2147450880 + 4) by (unfold SB; rewrite (div8_off F a 4 (proj1 GF8)); [clear; lia| clear - Ha; lia]).
    rewrite Da. right. exists 1. split; [exact (L5ADHR.byte_of_u8 Mi _ 1 SHBm ltac:(right; clear - GF1; lia) ltac:(clear - GF1 GF2; lia))|]. split; [clear; lia|].
    assert (Am : a mod 8 = a - (F + 32)) by (rewrite (Zmod_eq a 8) by (clear; lia); rewrite (div8_off F a 4 (proj1 GF8)) by (clear - Ha; lia); clear - GF8; lia).
    rewrite Am. clear - Ha; lia. }
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad). pose proof (Lpos MORE DONE) as POS.
  pose proof SRD as SP. unfold PECSA.src_read_spec, PECSPA.src_read_spec in SP.
  apply (call_src (pa_src_read AD) 16 (PECSPA.cread_args AD) PECSPA.cread_W (PECSPA.cread_res RSEGS) SP [(F + 32, 1)] ra fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y MID MORE DONE PPOS J1 RAq J10
           ltac:(left; reflexivity)).
  { exists (F + 32), 1. split; [rewrite L5K.rl11; exact J11|]. split; [rewrite L5K.rl12; exact J12|]. split; [clear; lia|].
    split; [exists (F, 0, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; clear; lia]|].
    split; [apply (L5.defined_sub Mi F 64); [exact FDm| clear; lia| clear; lia]|].
    split; [exact ACCq|]. split; [fold ois; clear - AiF; lia| fold op; unfold PECA.RDR_BYTES; clear - ApF; lia]. }
  { exists (F + 32), 1. split; [rewrite L5K.rl11; exact J11|]. split; [rewrite L5K.rl12; exact J12|]. split; [clear - GF1 GF2; lia|]. split; [clear; lia| reflexivity]. }
  { intros rr [<-|[]]. cbn [fst snd]. clear; lia. }
  { intros p0 Ra Rb Mb sa sb ma mb (CW & _). exact CW. }
  intros fxb Rb Mb mdb LKb Awb srcb smb RPb RES POS' FSHb _ MIDb.
  assert (SHBb : L5.u8_at RSEGS Mb (F / 8 + 2147450880 + 4) 1).
  { apply (L5C.u8_at_agree RSEGS Mi Mb); [intros i Hi'; apply FSHb; clear - Hi'; lia| clear - GF1; lia| clear - GF1 GF2; lia| exact SHBm]. }
  destruct RES as (CW4 & p' & k' & d & Yp & Yk & Hp1 & Hp2 & Hk' & Yd & Hd & CONS & SHORT & DEFd & BYT).
  assert (Ek : k' = 1).
  { rewrite L5K.rl12 in Yk. rewrite J12 in Yk. apply (f_equal bv_unsigned) in Yk. unfold PM.CHUNK in Hk'. rewrite !L5.unsigned_lit in Yk by (clear - Hk'; lia). clear - Yk; lia. }
  subst k'.
  assert (Ep : p' = F + 32).
  { rewrite L5K.rl11 in Yp. rewrite J11 in Yp. apply (f_equal bv_unsigned) in Yp. rewrite !L5.unsigned_lit in Yp by (clear - Hp1 Hp2 GF1 GF2; lia). clear - Yp; lia. }
  subst p'. rewrite L5K.rl10 in Yd.
  assert (UNR : PM.unread (PM.p_src si) smi = blen p - s_pos Y) by (unfold PEC.pos_of in POS; clear - POS; lia).
  unfold PMSPA.consumed in CONS.
  assert (LE : s_pos Y + d <= blen p).
  { destruct CW4 as (CWP & _). unfold PEC.pos_of in CWP. clear - CWP CONS UNR Hd. lia. }
  assert (SHORT' : d < 1 -> s_pos Y + d = blen p).
  { intros Hdk. pose proof (SHORT Hdk) as U0. clear - U0 CONS UNR. lia. }
  assert (EP : PEC.pos_of p srcb smb = s_pos Y + d) by (unfold PEC.pos_of in POS |- *; clear - CONS POS; lia).
  rewrite POS in BYT. rewrite EP in MIDb.
  exact (KX fxb Rb Mb mdb LKb Awb srcb smb d RPb Yd Hd SHORT' LE BYT SHBb MIDb).
Qed.

Lemma cred_parser Mi Xi si smi eni ki ei cri :
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi eni ki ei cat -> PMSP.credit_le (PECA.pot_allA L ar P si eni ki) cri ->
  PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) si)) cri.
Proof.
  intros CP CLE. pose proof CP as (PA & _ & EA & _ & SKA & _).
  pose proof EA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EHk & _).
  pose proof (PESKA.sink_potA_nonneg RSEGS L ar P Mi osk ki PO SKA) as (SP1 & SP2).
  pose proof (PMA.ly_cost L C LY) as (KPM & BLIN & BOV).
  pose proof (Z.pow_le_mono_r 2 (PEC.en_k eni) 12 ltac:(lia) ltac:(clear - EHk; lia)) as P2e. pose proof (PM.pow2_pos (PEC.en_k eni) ltac:(clear - EHk; lia)) as P2p.
  unfold PMSPA.credit_le, PMSP.credit_le, PECA.pot_allA, PEC.credit_add, PEC.pot_estack, PMSPA.scA in CLE |- *. cbn [fst snd] in CLE |- *.
  unfold PMSPA.HV, LibIfaceAB.heap_view in CLE |- *. cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in CLE |- *. rewrite KPM, BOV, BLIN in CLE |- *.
  assert (E2 : 0 <= PEC.ESZ * (2 ^ 12 - 2 ^ PEC.en_k eni)) by (unfold PEC.ESZ; apply Z.mul_nonneg_nonneg; clear - P2e; lia).
  clear - CLE SP1 SP2 EHk E2. split; nia.
Qed.

Lemma call_push (pc : Z) cells (SPEC : PMSAX.push_spec_at RSEGS AD L ar HI pc false cells) (t : UbjRef.pstate) (ra : Z)
      fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr Ri (reg 10) = Z_to_bv 64 (op + 360) ->
  cells FF' (sp - 128) (op + 360) Mi Ri (PEC.ps_conv t) ->
  PM.pstate_ok (PEC.ps_conv t) -> ~ PM.mode_bottom (PM.ps_mode (PEC.ps_conv t)) ->
  Z.of_nat (length (PM.p_stk si)) <= PM.MAX_DEPTH ->
  (forall (fx' : FPState) R' M' md' LK' Aw' b' k' cr', regs_preserved Ri R' ->
      amid fx' R' M' md' LK' Aw' cr' (PMABK.push_st si b' k' (PEC.ps_conv t)) smi eni ki ei (w_stk (t :: s_stk Y) Y) ->
      (forall a, sp - 128 <= a < sp -> M' (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx') RSEGS R' ra M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pc Mi mdi) K.
Proof.
  intros MID J1 RAq J10 CELLS Hc Hm HL KX. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WBi & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDi & NDFi & _).
  pose proof GFR as (GF1 & GF2 & _).
  pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C320 & TBV & VEC & _).
  pose proof VEC as (V0 & V8 & V16 & Hk' & Hlen & Hal & DB & CB & AN & EL).
  set (qc := PM.sr_qc (PM.p_src si)) in *. set (b := PM.p_b si) in *. set (kv := PM.p_k si) in *.
  set (LBXp := (qc, PM.CHUNK) :: ((PM.vs_own (PM.p_tb si) ++ (PEC.enc_own eni ++ PESK.sink_own ki)) ++ LBX)).
  assert (HHs : ri_inv HI (PM.vec_own b kv ++ LBXp) FF' LKi cri Awi Mi (vml_of mdi)) by (apply (PMABK.ri_swap12 L ar C HI HIok); exact HHi).
  assert (Iv : In (b, 32 * 2 ^ kv) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  assert (Iq : In (qc, PM.CHUNK) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  destruct (WBi _ Iv) as ((Bb4 & _ & _ & _ & _ & _) & _). cbn [fst snd] in Bb4.
  assert (K10 : Z.of_nat (length (PM.p_stk si)) = 2 ^ kv -> kv <= 10).
  { intros E'. destruct (Z.eq_dec kv 11) as [E11|N11]; [| clear - Hk' N11; unfold kv in *; lia]. rewrite E11 in E'. change (2 ^ 11) with 2048 in E'. unfold PM.MAX_DEPTH in HL. clear - E' HL; lia. }
  assert (Cap : PM.vs_cap (PM.p_tb si) <= 2 ^ 27).
  { pose proof TBV as (_ & _ & TBV'). destruct (PM.p_tb si) as [n0|c0 n0 q0]; cbn [PM.vs_cap]; [clear; lia|]. destruct TBV' as (_ & _ & _ & _ & CB' & _). clear - CB'; lia. }
  assert (Bnz : Z.eqb b 0 = false) by (apply Z.eqb_neq; clear - Bb4; lia).
  assert (SHop : (op + 360) mod 8 = 0) by (rewrite Eop; replace (fb + 592 + 360) with (fb + 8 * 119) by (clear; lia); apply FB8).
  pose proof (cred_parser Mi Y si smi eni ki ei cri CP (credit_le_keep _ _ _ _ CRED CK)) as CRL.
  unfold PMSAX.push_spec_at in SPEC.
  apply (SPEC fxi Ri Mi mdi K LBXp FF' LKi Awi cri (op + 360) b kv (PM.p_stk si) (PM.vec_own b kv) (PEC.ps_conv t) (sp - 128) ra HHs AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 26624 128 12288 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 12288) with (sp + (-776) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact J10. }
  { apply PMAUAR.aobjA_push. apply AOF; clear - Eop; lia. }
  { exact SHop. }
  { apply (PMABK.aacc_sub Mi (op + 320) 64); [exact C320| clear; lia| clear; lia]. }
  { right. split; [exact VEC| reflexivity]. }
  { intros X0. discriminate X0. }
  { intros [E'|E']; [discriminate E'| exact (K10 E')]. }
  { exact CELLS. }
  { intros [E'|E']; [discriminate E'|]. rewrite Bnz. exact (proj1 (PMABK.stk_credit L ar C LY si cri TBOK Cap ltac:(pose proof (K10 E'); clear - H Hk'; unfold kv in *; lia) CRL)). }
  intros fx' R' M' md' LK' Aw' b' k' cr' RP' VEC' ACC' PO' HP' MRT' ILK' IAW' AM' HH'.
  change (PMSPA.pm_scr 0) with 12288 in HP'.
  set (s' := PMABK.push_st si b' k' (PEC.ps_conv t)).
  assert (HH1 : ri_inv HI (PEC.owned s' eni ki ++ LBX) FF' LK' cr' Aw' M' (vml_of md')) by (apply (PMABK.ri_swap12 L ar C HI HIok); exact HH').
  set (Wc := [(op + 360, 24)]) in HP'.
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  pose proof FSAPP as (FA0 & FA1 & FA2).
  assert (BI' : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned s' eni ki) M' md' LK' cr' Aw').
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si eni ki) ((qc, PM.CHUNK) :: (PM.vs_own (PM.p_tb si) ++ (PEC.enc_own eni ++ PESK.sink_own ki))) (PEC.owned s' eni ki)
             Mi mdi LKi cri Awi M' md' LK' cr' Aw' 12288 Wc BI HP' HH1 AM' MRT' IAW' ILK'); [clear; lia| clear; lia| | | intros a X0; exact X0].
    - intros rr a [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
      split; [clear - Hr O2 SLO Eop; lia|]. destruct FA1 as [Y'|Y']; clear - Hr Y' DF1 DF2 F1 F2 Eop; lia.
    - intros a _ O rr [<-|[]] Hr. apply (O (PMSP.o_vec AD fb, 24)); [unfold WR; wr_mem 5| exact Hr]. }
  assert (EKp : L5SAR.ek L ar LBXp FF sp 26624 Wc Mi M')
    by exact (L5SAR.ek_callee L ar LBXp [] FF [(F, 0, sp - 128 + 32)] sp 26624 (sp - 128) 12288 Wc Wc Mi M' HP' ltac:(clear; lia) ltac:(clear; lia) (fun a _ X0 => X0)).
  assert (WAPPc : PMKA.wapp Wc).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG; lia. }
  assert (INCp : incl LBXp LBi).
  { intros bb Hbb. unfold LBXp in Hbb. destruct Hbb as [<-|Hbb]; [exact Iq|]. apply in_app_or in Hbb. destruct Hbb as [Hbb|Hbb]; [| unfold LBi; apply in_or_app; right; exact Hbb].
    apply in_app_or in Hbb. unfold LBi, PEC.owned. apply in_or_app; left. destruct Hbb as [Hbb|Hbb]; [apply in_or_app; left; unfold PM.parser_own; apply in_or_app; right; apply in_or_app; right; exact Hbb|].
    apply in_or_app; right. exact Hbb. }
  assert (BRBp : forall bb, In bb LBXp -> 0 <= fst bb /\ fst bb + snd bb <= 2 ^ 47) by (intros bb Hbb; exact (BRBi bb (INCp bb Hbb))).
  assert (OUTc : forall a n, a + n <= op + 360 \/ op + 384 <= a -> forall i, a <= i < a + n -> L5.outside Wc i).
  { intros a n X0 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - X0 Hi Hr; lia. }
  assert (OUTB : forall q' m, In (q', m) LBXp -> forall i, q' <= i < q' + m -> L5.outside Wc i).
  { intros q' m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi (INCp _ Hq) (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z0|Z0]; clear - Hi Hr Z0; lia. }
  assert (DEF' : L5.defined M' op 384).
  { intros i Hi. apply (proj2 (proj2 HP')); [clear - Hi O1 O3; lia| | apply PDEF; exact Hi].
    apply (L5SAR.fframe_client L ar _ FF' _ _ fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - Hi Eop; lia]. }
  assert (PA' : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' op ois s').
  { destruct (BRBi _ Iq) as (Q1 & Q2). cbn [fst snd] in Q1, Q2. unfold PM.CHUNK in Q2.
    apply (PMABK.parser_push_updA Mi M' op ois si b' k' (PEC.ps_conv t) PA); [clear - O1; lia| clear - O3; lia| | | exact DEF'| exact VEC'| exact Q1| unfold PM.CHUNK; clear - Q2; lia| |].
    - apply (PMKA.agA_obj L ar _ FF sp 26624 Wc Mi M' EKp WAPPc FRB op 360 (AOF op 360 ltac:(lia) ltac:(lia))). apply OUTc. clear; lia.
    - exact (PMKA.agsh_obj L ar _ FF sp 26624 Wc Mi M' EKp WAPPc FRB op 384 AOP).
    - apply (PMKA.agA_blk L ar _ FF sp 26624 Wc Mi M' EKp WAPPc BRBp _ _ (or_introl eq_refl)). apply OUTB. left; reflexivity.
    - intros c0 n0 p0 Etb. assert (Ip : In (p0, c0) LBXp) by (unfold LBXp; right; apply in_or_app; left; apply in_or_app; left; rewrite Etb; left; reflexivity).
      apply (PMKA.agA_blk L ar _ FF sp 26624 Wc Mi M' EKp WAPPc BRBp _ _ Ip). apply OUTB. exact Ip. }
  assert (KPa : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBXp FF' (sp - 128) 12288 a -> L5.outside Wc a -> M' (Z_to_bv 64 a) = Mi (Z_to_bv 64 a))
    by (intros a X1 X2 X3; apply (proj1 HP'); split; [exact X1| split; assumption]).
  assert (KPR : forall a, sp - 128 <= a < sp -> M' (Z_to_bv 64 a) = Mi (Z_to_bv 64 a)).
  { intros a Ha. apply KPa; [clear - Ha SLO SHI SPT; lia| apply (L5SAR.stack_client L ar _ FF' _ _ a); clear - Ha GSLO GSHI GSPT; lia|]. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O2 SLO Eop; lia. }

  assert (CKp : PMSP.credit_keep cri cr' (PECA.pot_allA L ar P si eni ki) (PECA.pot_allA L ar P s' eni ki)).
  { destruct PO' as [(_ & _ & _ & Eb & Ek & Ecr)|(Hg & Ek & Ecr)].
    - subst cr'. unfold s', PMABK.push_st, PECA.pot_allA, PEC.credit_add, PM.pot_parser. cbn [PM.p_k PM.p_tb PM.p_tg]. rewrite Ek. fold kv. unfold PMSP.credit_keep. cbn [fst snd]. clear; lia.
    - rewrite Bnz in Ek. subst k' cr'.
      destruct (PMABK.stk_credit L ar C LY si cri TBOK Cap) as (_ & CKs).
      { destruct Hg as [Hg|Hg]; [discriminate Hg|]. pose proof (K10 Hg). clear - H Hk'. unfold kv in *. lia. }
      { exact CRL. }
      specialize (CKs s' eq_refl eq_refl eq_refl).
      unfold PMSPA.credit_keep, PMSP.credit_keep, PECA.pot_allA, PEC.credit_add in CKs |- *. cbn [fst snd] in CKs |- *.
      subst kv. clear - CKs. lia. }
  apply (KX fx' R' M' md' LK' Aw' b' k' cr' RP'); [| exact KPR].
  unfold amid. split; [| split; [exact BI'| split; [| split; [exact ST| split; [exact EIMP| exact (credit_keep_trans _ _ _ _ _ _ CK CKp)]]]]].
  - pose proof (fun j Hj => L5SAR.cs_of_preserved Ri R' j RP' Hj) as Rc'.
    split; [rewrite (Rc' 2%nat) by inl; exact J2|]. split; [rewrite (Rc' 8%nat) by inl; exact J8|]. split; [rewrite (Rc' 9%nat) by inl; exact J9|].
    split; [rewrite (Rc' 18%nat) by inl; exact J18|]. split; [rewrite (Rc' 19%nat) by inl; exact J19|]. split; [rewrite (Rc' 20%nat) by inl; exact J20|].
    split; [rewrite (Rc' 21%nat) by inl; exact J21|]. split; [rewrite (Rc' 25%nat) by inl; exact J25|]. split; [rewrite (Rc' 26%nat) by inl; exact J26|].
    split; [rewrite (Rc' 27%nat) by inl; exact J27|].
    intros j Hj. rewrite (Rc' j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  -
    assert (SINC : incl (PM.vs_own str) LBXp) by (intros x Hx; unfold LBXp; right; apply in_or_app; right; exact (INCS x Hx)).
    assert (EINC : incl (PEC.enc_own eni) LBXp) by (intros x Hx; unfold LBXp; right; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hx).
    assert (KINC : incl (PESK.sink_own ki) LBXp) by (intros x Hx; unfold LBXp; right; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx).
    assert (OWo : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op + 360 \/ op + 384 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i)
      by (intros a n _ _ X3; exact (OUTc a n X3)).
    unfold PECA.crun_preA.
    split; [exact PA'|].
    split.
    { apply (PMKA.iss_keepA RSEGS AD L ar LBXp FF sp 26624 Wc Mi M' EKp WAPPc FRB BRBp ois str smi AOI); [exact SINC| apply (OWo ois 272); clear - Eois Eop; lia| | exact IA].
      intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB. apply SINC. unfold PM.vs_own. rewrite E0. left. reflexivity. }
    split.
    { apply (PECFA.enc_keepA RSEGS EE L ar LBXp FF sp 26624 Wc Mi M' EKp WAPPc FRB BRBp ov fb eni (AOF ov 56 ltac:(lia) ltac:(lia))); [apply (OWo ov 56); clear - Eov Eop; lia| exact EINC| | exact EA].
      intros Hp. unfold PMKA.blk_out. apply OUTB. apply EINC. unfold PEC.enc_own. replace (PEC.en_k eni =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    split; [apply (PMKA.u64_keepA RSEGS L ar LBXp FF sp 26624 Wc Mi M' EKp WAPPc FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [apply (OWo (op + 384) 8); clear - Eop; lia| exact VREF]|].
    split.
    { apply (PECFA.sink_keepA RSEGS L ar LBXp FF sp 26624 Wc Mi M' EKp WAPPc FRB BRBp P osk ki (AOF osk 24 ltac:(lia) ltac:(lia))); [apply (OWo osk 24); clear - Eosk Eop; lia| exact KINC| | exact SKA].
      intros Hp. unfold PMKA.blk_out. apply OUTB. apply KINC. unfold PESK.sink_own. replace (PESK.sk_c ki =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    split; [change (PMSTA.base_okA RSEGS PMA.AD M'); apply (PMASK.base_keep L ar C LY LBXp FF sp 26624 Wc Mi M' EKp); [intros a Ha; apply (OUTc a 1); clear - Ha O1 Eop; lia| exact BASE]|].
    split.
    { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBXp FF sp 26624 Wc Mi M' EKp ei PECSA.addrs_wf_A); [| exact ERR].
      intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
      split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply (OUTc a 1); clear - DI O1 Eop; lia. }
    split; [unfold s', PMABK.push_st; cbn [PM.p_tb PM.p_tg]; exact TBOK|].
    split.
    { unfold s', PMABK.push_st. cbn [PM.p_src].
      apply (content_keepA' LBXp FF sp 26624 Wc Mi M' fb p si str smi op EKp WAPPc FRB BRBp AOI); [fold ois; apply (OWo (ois + 80) 24); clear - Eois Eop; lia| exact SINC| left; reflexivity| intros q' m Hq; exact (OUTB q' m Hq)| exact IA| exact PA| exact CONT]. }
    split.
    { destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
      unfold PEC.clink, s', PMABK.push_st. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_stk PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|].
      split; [rewrite Lstk; unfold PEC.stk_conv; cbn [rev]; rewrite map_app; reflexivity|].
      split; [exact Lpos|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad]. }
    split.
    { cbn [s_ec w_stk]. apply (PECFA.ec_state_keepA RSEGS AD L ar LBXp FF sp 26624 Wc Mi M' EKp WAPPc FRB fb (s_ec Y) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
      fold oec. apply (OWo oec 16); clear - Eoec Eop; lia. }
    split; [exact ECI|].
    pose proof BI' as (_ & _ & _ & _ & _ & _ & EKb' & _).
    exact (PMKA.acc_keepA' L ar LBX FF sp 26624 WR M M' EKb' wappR FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CPRE))))))))))))).
Qed.

Lemma finish (v' : Z) (Xf : st) fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fx7 : FPState) R7 M7v (pci : Z) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fx7 R7 (Z_to_bv 64 0xb6dd4) M7v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) M7v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 8 + 1) -> ~ (F + 0 <= i < F + 0 + 8) -> ~ (F / 8 + 2147450880 + 0 <= i < F / 8 + 2147450880 + 0 + 8) ->
      ~ (fl + 0 <= i < fl + 0 + 1) -> M7v (Z_to_bv 64 i) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 i)) ->
  (forall j, In j [3; 4]%nat -> getr R7 (reg j) = getr Ri (reg j)) ->
  (forall j, In j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg j) = getr R (reg j)) ->
  getr R7 (reg 2) = Z_to_bv 64 sp -> L5.u8_at RSEGS M7v fl 0 -> L5.u8_at RSEGS M7v (op + 8) v' -> (v' = 0 \/ v' = 1) ->
  Xf = r_begin p false X -> PEC.clink p Xf (PMPK.set_more si v') smi eni ki -> s_ec Xf = s_ec Y ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID MS7 MG7 FRZ7 K34 REG7 E72 FL0 MO0 Hv' EXF CLF ECF. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold Hi in Zop, Z32, Z20, OWR, OVIS. fold MVi in Zop, Z32, Z20, OWR.
  destruct (APART op 384 0 0) as (ApF & ApSF & ApFL).
  { intros i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
    split; [clear - Eop Hi'; lia| intros Y'; clear - Eop Hi' Y'; lia]. }
  { clear; lia. }
  change (ff_bytes 0) with 64 in ApF, ApSF. change (64 / 8) with 8 in ApSF. unfold SB in ApSF.
  assert (SHop : op / 8 + 2147450880 = fb / 8 + 2147450880 + 74).
  { rewrite Eop. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 592) with ((256 * (fb / 2048) + 74) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  destruct (APART (op / 8 + 2147450880) 48 0 0) as (_ & AsopSF & _).
  { intros i Hi'. unfold aclient, aclient_g. do 5 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. unfold in_shadow_of, S. unfold SB.
    assert (D1 : (fb + 2048 - 1) / 8 = fb / 8 + 255).
    { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
      replace (2048 * (fb / 2048) + 2048 - 1) with (7 + (256 * (fb / 2048) + 255) * 8) by (clear; lia). rewrite Z.div_add by lia.
      replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
    rewrite D1. clear - SHop Hi'. lia. }
  { clear; lia. }
  change (64 / 8) with 8 in AsopSF. unfold SB in AsopSF.
  pose proof OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26.
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  fold Hi in MS7, MG7, FRZ7. fold MVi in MS7, MG7, FRZ7.
  assert (R7ra : getr R7 (reg 1) = Z_to_bv 64 r) by (rewrite (REG7 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx7 R7 M7v 0xb6dd4 W_b6d84 r F_b6d84 eq_refl D_b6d84 R7ra Hr1 Hr2) as MSr.
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
           WR (PEC.owned si eni ki) Mi mdi LKi cri Awi (fun a => op + 8 <= a < op + 9) fxi fx7 Ri pci R7 r M7v K BI).
  { intros a X'. split.
    - apply (L5SAR.fframe_client L ar (PEC.owned si eni ki ++ LBX) FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - X' Eop; lia].
    - intros O. apply (O (PMSP.o_p AD fb + 8, 8)); [unfold WR; wr_mem 0| wr_rng; clear - X' Eop; lia]. }
  { intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [X'|X']; [left; exact X'| right; exact X']. }
  { exact (msteps_trans _ _ _ _ MS7 MSr). }
  { exact MG7. }
  { intros a Ha Nw. unfold PMAUK.WretX, PMAUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw.
    apply FRZ7; [exact Ha| intros X'; apply Nw; right; clear - X'; lia| intros X'; apply Nw; left; left; left; clear - X'; lia
                | intros X'; apply Nw; left; left; right; unfold SB; clear - X'; lia| intros X'; apply Nw; left; right; clear - X'; lia]. }
  { exact FL0. }
  intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict Hi Mf = M7v) in VISf.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  assert (EKf : L5SAR.ek L ar LBi FF 0 0 [(op + 8, 1)] Mi Mf).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k)
             LBi LKi cri Awi Mi Mf _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) G HHi).
    - intros a X' O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X'; lia].
    - exact FZf. }
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  assert (MO0f : L5.u8_at RSEGS Mf (op + 8) v').
  { apply (proj1 (L5A.u8_at_vis Hi Mf (op + 8) v' (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). rewrite VISf. exact MO0. }
  assert (WAPP8 : PMKA.wapp [(op + 8, 1)]).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG; lia. }
  assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
  { intros a n X3 i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi' Hr X3. lia. }
  assert (OUTB8 : forall q' m, In (q', m) LBi -> forall i, q' <= i < q' + m -> L5.outside [(op + 8, 1)] i).
  { intros q' m Hq i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Hr Z'; lia. }
  assert (Iq : In (PM.sr_qc (PM.p_src si), PM.CHUNK) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (Ib : In (PM.p_b si, 32 * 2 ^ PM.p_k si) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  apply (KONT fx7 R7 Mf modelf LKi Awi (PMPK.set_more si v') smi eni ki ei cri).
  - apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite E72; exact (eq_sym Rsp) | apply REG7; inl | rewrite (K34 _) by inl; apply J34; inl ] |]).
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

Lemma finishR fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y (fx7 : FPState) R7 M7v (pci : Z) :
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fx7 R7 (Z_to_bv 64 0xb6dd4) M7v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) M7v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 112 <= i < sp - 112 + 8) -> ~ (F + 0 <= i < F + 0 + 8) -> ~ (F / 8 + 2147450880 + 0 <= i < F / 8 + 2147450880 + 0 + 8) ->
      ~ (fl + 0 <= i < fl + 0 + 1) -> M7v (Z_to_bv 64 i) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 i)) ->
  (forall j, In j [3; 4]%nat -> getr R7 (reg j) = getr Ri (reg j)) ->
  (forall j, In j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg j) = getr R (reg j)) ->
  getr R7 (reg 2) = Z_to_bv 64 sp -> L5.u8_at RSEGS M7v fl 0 ->
  Y = r_begin p false X ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID MS7 MG7 FRZ7 K34 REG7 E72 FL0 EXF. entry_facts. frame_facts. open_amid MID.
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  fold Hi in MS7, MG7, FRZ7. fold MVi in MS7, MG7, FRZ7.
  assert (R7ra : getr R7 (reg 1) = Z_to_bv 64 r) by (rewrite (REG7 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx7 R7 M7v 0xb6dd4 W_b6d84 r F_b6d84 eq_refl D_b6d84 R7ra Hr1 Hr2) as MSr.
  set (LBi := PEC.owned si eni ki ++ LBX) in *.
  apply (PMAUKS.retire_coreS L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
           WR (PEC.owned si eni ki) Mi mdi LKi cri Awi (fun _ => False) (fun a => sp - 112 <= a < sp - 104) fxi fx7 Ri pci R7 r M7v K BI).
  { intros a []. }
  { intros a. right. intros []. }
  { intros a X'. split; [clear - X'; lia|]. apply GNCS. clear - X'; lia. }
  { intros a. destruct (L5SAR.rng_dec a (sp - 112) (sp - 104)) as [X'|X']; [left; exact X'| right; exact X']. }
  { exact (msteps_trans _ _ _ _ MS7 MSr). }
  { exact MG7. }
  { intros a Ha Nw. unfold PMAUKS.WretY, PMAUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw.
    apply FRZ7; [exact Ha| intros X'; apply Nw; right; right; clear - X'; lia| intros X'; apply Nw; left; left; left; clear - X'; lia
                | intros X'; apply Nw; left; left; right; unfold SB; clear - X'; lia| intros X'; apply Nw; left; right; clear - X'; lia]. }
  { exact FL0. }
  intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict Hi Mf = M7v) in VISf.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.

  set (Mf' := fun w : word => if ((sp - 112 <=? bv_unsigned w) && (bv_unsigned w <? sp - 104))%bool then Mi w else Mf w).
  assert (EMf' : forall a, 0 <= a < 2 ^ 64 -> Mf' (Z_to_bv 64 a) = (if ((sp - 112 <=? a) && (a <? sp - 104))%bool then Mi (Z_to_bv 64 a) else Mf (Z_to_bv 64 a)))
    by (intros a Ha; unfold Mf'; rewrite (L5.unsigned_lit a Ha); reflexivity).
  assert (EK0 : L5SAR.ek L ar LBi FF 0 0 [] Mi Mf').
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k)
             LBi LKi cri Awi Mi Mf' _ [] (fun _ => False) G HHi); [intros a []|].
    intros a Ha Nw. rewrite (EMf' a Ha). destruct ((sp - 112 <=? a) && (a <? sp - 104))%bool eqn:Cb; [reflexivity|].
    apply FZf; [exact Ha|]. intros X'. unfold PMAUKS.WretY in X'. unfold PMAUK.WretX in Nw. destruct X' as [X'|[[]|X']]; [exact (Nw (or_introl X'))|].
    apply Bool.andb_false_iff in Cb. destruct Cb as [Cb|Cb]; [apply Z.leb_gt in Cb| apply Z.ltb_ge in Cb]; clear - Cb X'; lia. }
  assert (EKf : L5SAR.ek L ar LBi FF sp 26624 [] Mi Mf).
  { intros a (Ha & Hc & Ho). destruct (L5SAR.rng_dec a (sp - 112) (sp - 104)) as [X'|X'].
    - exfalso. destruct (L5SAR.aclient_cases L ar C HI LYa HIok LBi FF' LKi cri Awi Mi _ sp 26624 a HHi GSPT (L5SAR.aclient_cons L ar LBi FF (F, 0, sp - 128 + 32) sp 26624 a Hc)) as [Y'|Y'];
        clear - X' Y' GSLO; lia.
    - transitivity (Mf' (Z_to_bv 64 a)).
      + rewrite (EMf' a Ha). destruct ((sp - 112 <=? a) && (a <? sp - 104))%bool eqn:Cb; [| reflexivity].
        apply Bool.andb_true_iff in Cb. destruct Cb as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. exfalso. apply X'. clear - C1 C2; lia.
      + apply EK0. split; [exact Ha|]. split; [exact (L5SAR.aclient_00 L ar LBi FF sp 26624 a Hc)| exact Ho]. }
  assert (Iq : In (PM.sr_qc (PM.p_src si), PM.CHUNK) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  apply (KONT fx7 R7 Mf modelf LKi Awi si smi eni ki ei cri).
  - apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite E72; exact (eq_sym Rsp) | apply REG7; inl | rewrite (K34 _) by inl; apply J34; inl ] |]).
    destruct Hj.
  - rewrite <- EXF.
    apply (cpre_keepA LBi sp 26624 [] Mi Mf Y si smi eni ki ei EKf PMKA.wapp_nil BRBi); [unfold LBi; apply incl_appl; apply incl_refl| unfold LBi; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP].
  - exact ST.
  - exact EIMP.
  - exact AHf.
  - exact CK.
  - exact MRTf.
  - exact INCLi.
  - exact INCAi.
  - exact AMf.
  - exact HHf.
Qed.

Lemma clink_fail Y0 s0 sm0 en0 k0 : PEC.clink p Y0 s0 sm0 en0 k0 -> PEC.clink p (w_more false Y0) (PMPK.set_more s0 0) sm0 en0 k0.
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  unfold PEC.clink, PMPK.set_more. destruct Y0; cbn in *.
  split; [reflexivity|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
  split; [intros X' _; discriminate X'|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
Qed.
Lemma clink_failp Y0 q b s0 sm0 en0 k0 : PEC.clink p (w_ec b (w_pos q Y0)) s0 sm0 en0 k0 -> PEC.clink p (w_more false (w_ec b Y0)) (PMPK.set_more s0 0) sm0 en0 k0.
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  unfold PEC.clink, PMPK.set_more. destruct Y0; cbn in *.
  split; [reflexivity|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
  split; [intros X' _; discriminate X'|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
Qed.

Lemma clink_more1 Y0 s0 sm0 en0 k0 : PEC.clink p Y0 s0 sm0 en0 k0 -> s_more Y0 = true -> PEC.clink p Y0 (PMPK.set_more s0 1) sm0 en0 k0.
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9) HM.
  unfold PEC.clink, PMPK.set_more. destruct Y0; cbn in *. rewrite HM in *. cbn.
  split; [reflexivity|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
Qed.

Lemma entry_model :
  bytes_ok p /\ 0 <= s_pos X <= blen p /\ s_lo X <= s_hi X /\ s_bad X = false /\ s_edepth X = s_depth X /\ Forall ei_ok (s_estk X)
  /\ s_more X = true /\ s_done X = false /\ s_halt X = false /\ 0 <= s_depth X <= UbjRef.MAX_DEPTH
  /\ Z.of_nat (length (s_estk X)) <= UbjRef.MAX_DEPTH /\ Z.of_nat (length (s_stk X)) <= s_depth X + 1.
Proof.
  pose proof MP as MP'. unfold PECSPA.mp_run, pre_run, pre in MP'.
  destruct MP' as (((BOK & PPOS & PLH & PBAD & PED & PEOK) & MORE) & DONE & HALT & DEP & EST & STKLE).
  repeat (split; [assumption|]). exact STKLE.
Qed.

Lemma nbhb_of (Z0 : st) : r_begin p false X = w_more true Z0 -> s_bad Z0 = false /\ PESKA.spa_hb P (s_hi Z0).
Proof. intros E. pose proof NB as NB'. pose proof HB as HB'. rewrite E in NB', HB'. destruct Z0; cbn in *. split; assumption. Qed.

Lemma mp_encb_of (Xs : st) : s_estk Xs = s_estk X -> s_edepth Xs = s_edepth X -> s_lo Xs = s_lo X -> s_hi Xs = s_hi X -> s_bad Xs = s_bad X -> PECSPA.mp_encb p Xs.
Proof.
  intros E1 E2 E3 E4 E5. destruct entry_model as (BOK & PPOS & PLH & PBAD & PED & PEOK & MORE & DONE & HALT & DEP & EST & STKLE).
  unfold PECSPA.mp_encb, PECSPA.mp_enc. rewrite E1, E2, E3, E4, E5, PED. split; [|exact EST]. split; [exact PLH|]. split; [exact PBAD|]. split; [exact PEOK| exact DEP].
Qed.

Lemma mod4_of16 a : a mod 16 = 0 -> a mod 4 = 0.
Proof. intros H. apply Z.mod_divide; [lia|]. apply (Z.divide_trans 4 16 a); [exists 4; reflexivity| apply Z.mod_divide; [lia| exact H]]. Qed.

Lemma sub_eof fxi Ri Mi mdi LKi Awi cri si smi eni ki ei :
  s_depth X + 1 <= UbjRef.MAX_DEPTH ->
  amid fxi Ri Mi mdi LKi Awi cri si smi eni ki ei (PECBD.X1 X) -> blen p <= s_pos X ->
  getr Ri (reg 10) = Z_to_bv 64 256 -> getr Ri (reg 23) = Z_to_bv 64 (op + 24) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb6a88 Mi mdi) K.
Proof.
  intros HD MID EOF A0 A23. entry_facts. frame_facts. piece_ctx MID.

  pz PEABAP1.abaKe_conc fxi Ri 0 0 0 0 as PK. L5SAR.feed PK fcl.
  destruct PK as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11).
  assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx3 Ri 0xb6a88 R3 0xae310 MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
  assert (E3 : M3 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
  assert (MID3 : amid fx3 R3 Mi md3 LKi Awi cri si smi eni ki ei (PECBD.X1 X)).
  { apply (amid_regs fxi Ri Mi mdi LKi Awi cri si smi eni ki ei _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
    intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
  apply (call_mkec 0xb6eac 1 fx3 R3 Mi md3 LKi Awi cri si smi eni ki ei _ MID3 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  keep_only HD EOF A23 KS3.
  intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
  assert (B23 : getr R4 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R3 R4 23 RP4) by inl; rewrite (KS3 23%nat) by inl; exact A23).
  clear KS3.

  entry_facts. frame_facts. piece_ctx MID.
  pz PEABAP3.abaZ1_conc fx4 R4 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
  destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
  apply (finish 0 (r_begin p false X) fx4 R4 M4 md4 LK4 Aw4 cri si smi eni ki true _ fx7 R7 M7v 0xb6eac MID MS7 MG7 FRZ7).
  - intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
  - intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R7 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
  - exact E2.
  - exact FL0.
  - exact MO0.
  - left; reflexivity.
  - reflexivity.
  - rewrite (PECBD.rb_eof p false X HD EOF), PECBD.r_fail_eq. pose proof MID as (_ & _ & CPz & _). pose proof CPz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLz & _). exact (clink_fail _ _ _ _ _ CLz).
  - rewrite (PECBD.rb_eof p false X HD EOF), PECBD.r_fail_eq. destruct X; reflexivity.
Qed.

Lemma after_gl (q : Z) (m : pmode) (ty : Z) (Xg : st) fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 e4 :
  (q = 0xb6b80 \/ q = 0xb6b04) ->
  PECSPA.gl_ret p Xg R4 -> amid fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en k e4 (PECSPA.gl_post p Xg) ->
  getr R4 (reg 23) = Z_to_bv 64 (op + 24) ->
  (q = 0xb6b04 -> getr R4 (reg 22) = Z_to_bv 64 (F + 32) /\ getr R4 (reg 24) = Z_to_bv 64 1) ->
  s_more Xg = true -> s_done Xg = false -> 0 <= s_pos Xg <= blen p -> s_ec Xg = s_ec X -> s_stk Xg = s_stk X -> s_estk Xg = s_estk X ->
  s_edepth Xg = s_edepth X -> s_lo Xg = s_lo X -> s_hi Xg = s_hi X -> s_bad Xg = s_bad X ->
  r_begin p false X = r_counted p m ty 2 Xg ->
  (forall n pos1, get_length p (s_pos Xg) = Some (n, pos1) -> s_ec X = false -> 0 <= n <= 16777216 ->
     getr R4 (reg 10) = Z_to_bv 64 n ->
     r_begin p false X = w_more true (e_begin_len 2 n (w_stk (PS m n ty 0 :: s_stk Xg) (w_pos pos1 Xg))) ->
     srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx4) RSEGS R4 q M4 md4) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx4) RSEGS R4 q M4 md4) K.
Proof.
  intros Hq RET MID A23 TYR MORE DONE PPOS EEC ESTK EESTK EED ELO EHI EBAD RB PUSH.
  destruct entry_model as (BOK & _).
  unfold PECSPA.gl_ret, PECSPA.gl_post in RET, MID.

  assert (TAILR : forall Yf, amid fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en k e4 Yf -> s_ec Yf = true -> Yf = r_begin p false X ->
                   srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx4) RSEGS R4 q M4 md4) K).
  { clear MID RET PUSH. intros Yf MID ECf EYf.
    pose proof (bv_unsigned_in_range 64 (getr R4 (reg 10))) as B10. change (bv_modulus 64) with (2 ^ 64) in B10.
    assert (Q10 : getr R4 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R4 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
    destruct (ec_vis1 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECf) as (v & Hv & ECv).
    assert (Q0v : 0 <= v < 2 ^ 64) by (clear - Hv; lia).
    entry_facts. frame_facts. piece_ctx MID.
    destruct Hq as [-> | ->].
    -
      pz PEABAP2.abaCe_conc fx4 R4 0 0 v (bv_unsigned (getr R4 (reg 10))) as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Hv; lia]).
      destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _).
      apply (finishR fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en k e4 Yf fx7 R7 M7v 0xb6b80 MID MS7 MG7 FRZ7).
      + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
      + intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R7 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
      + exact E2.
      + exact FL0.
      + exact EYf.
    -
      destruct (TYR eq_refl) as (A22 & A24).
      pz PEABAP2.abaTe_conc fx4 R4 0 0 v (bv_unsigned (getr R4 (reg 10))) as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Hv; lia]).
      destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _).
      apply (finishR fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en k e4 Yf fx7 R7 M7v 0xb6b04 MID MS7 MG7 FRZ7).
      + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
      + intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R7 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
      + exact E2.
      + exact FL0.
      + exact EYf.
  }
  destruct (get_length p (s_pos Xg)) as [[n pos1]|] eqn:GLE.
  - pose proof (get_length_some p (s_pos Xg) n pos1 BOK ltac:(clear - PPOS; lia) GLE) as (Hn & Hp1 & Hp2).
    change (getr R4 (reg 10) = Z_to_bv 64 n) in RET.
    destruct (s_ec X) eqn:EC.
    +
      apply (TAILR (w_pos pos1 Xg) MID); [destruct Xg; cbn in *; congruence|].
      rewrite RB. symmetry. apply (PECBD.rc_pending p m ty 2 Xg n pos1 GLE). congruence.
    + destruct (Z_lt_le_dec 16777216 n) as [BIG|OK].
      *
        assert (ECY : s_ec (w_pos pos1 Xg) = false) by (destruct Xg; cbn in *; congruence).
        pose proof (ec_vis0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECY) as EC0.
        assert (Q0n : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
        entry_facts. frame_facts. piece_ctx MID.
        destruct Hq as [-> | ->].
        --
        pz PEABAP2.abaCx_conc fx4 R4 0 0 0 n as PK. L5SAR.feed PK ltac:(first [fcl | clear - Hn BIG; lia]).
           destruct PK as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & Y12 & _).
           apply (amid_pieceS fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en k e4 (w_pos pos1 Xg) fx5 R5 0xb6b80 0xae310 M5v (fun a => sp - 112 <= a < sp - 112 + 8) MID MS5 MG5).
           { intros a Ha Na. apply FRZ5; [exact Ha| exact Na]. }
           { intros a X'; clear - X'; lia. }
           { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
           keep_only RB GLE EEC BIG Hn A23 KS5 Y1 Y10 Y11.
           intros M5 md5 VIS5 HID5 MGM5 FR5 MID.
           apply (call_mkec 0xb6bc4 13 fx5 R5 M5 md5 LK4 Aw4 cr4 si4 sm4 en k e4 _ MID Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
           keep_only RB GLE EEC BIG Hn A23 KS5.
           intros fx6 R6 M6 md6 LK6 Aw6 RP6 MID.
           assert (B23 : getr R6 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R5 R6 23 RP6) by inl; rewrite (KS5 23%nat) by inl; exact A23).
           entry_facts. frame_facts. piece_ctx MID.
           pz PEABAP3.abaZc_conc fx6 R6 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
           destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
           apply (finish 0 (r_begin p false X) fx6 R6 M6 md6 LK6 Aw6 cr4 si4 sm4 en k true _ fx7 R7 M7v 0xb6bc4 MID MS7 MG7 FRZ7).
              ++ intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
              ++ intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R7 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
              ++ exact E2.
              ++ exact FL0.
              ++ exact MO0.
              ++ left; reflexivity.
              ++ reflexivity.
              ++ rewrite RB, (PECBD.rc_big p m ty 2 Xg n pos1 GLE EEC BIG), PECBD.r_fail_eq. pose proof MID as (_ & _ & CPz & _). pose proof CPz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLz & _).
              exact (clink_failp _ _ _ _ _ _ _ CLz).
              ++ rewrite RB, (PECBD.rc_big p m ty 2 Xg n pos1 GLE EEC BIG), PECBD.r_fail_eq. destruct Xg; reflexivity.
        --
           destruct (TYR eq_refl) as (A22 & A24).
        pz PEABAP2.abaTx_conc fx4 R4 0 0 0 n as PK. L5SAR.feed PK ltac:(first [fcl | clear - Hn BIG; lia]).
           destruct PK as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & Y12 & _).
           apply (amid_pieceS fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en k e4 (w_pos pos1 Xg) fx5 R5 0xb6b04 0xae310 M5v (fun a => sp - 112 <= a < sp - 112 + 8) MID MS5 MG5).
           { intros a Ha Na. apply FRZ5; [exact Ha| exact Na]. }
           { intros a X'; clear - X'; lia. }
           { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
           keep_only RB GLE EEC BIG Hn A23 KS5 Y1 Y10 Y11 A22 A24.
           intros M5 md5 VIS5 HID5 MGM5 FR5 MID.
           apply (call_mkec 0xb6b48 13 fx5 R5 M5 md5 LK4 Aw4 cr4 si4 sm4 en k e4 _ MID Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
           keep_only RB GLE EEC BIG Hn A23 KS5 A22 A24.
           intros fx6 R6 M6 md6 LK6 Aw6 RP6 MID.
           assert (B23 : getr R6 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R5 R6 23 RP6) by inl; rewrite (KS5 23%nat) by inl; exact A23).
           assert (B22 : getr R6 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved R5 R6 22 RP6) by inl; rewrite (KS5 22%nat) by inl; exact A22).
           assert (B24 : getr R6 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R5 R6 24 RP6) by inl; rewrite (KS5 24%nat) by inl; exact A24).
           entry_facts. frame_facts. piece_ctx MID.
           pz PEABAP3.abaZt13_conc fx6 R6 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
           destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
           apply (finish 0 (r_begin p false X) fx6 R6 M6 md6 LK6 Aw6 cr4 si4 sm4 en k true _ fx7 R7 M7v 0xb6b48 MID MS7 MG7 FRZ7).
              ++ intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
              ++ intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R7 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
              ++ exact E2.
              ++ exact FL0.
              ++ exact MO0.
              ++ left; reflexivity.
              ++ reflexivity.
              ++ rewrite RB, (PECBD.rc_big p m ty 2 Xg n pos1 GLE EEC BIG), PECBD.r_fail_eq. pose proof MID as (_ & _ & CPz & _). pose proof CPz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLz & _).
              exact (clink_failp _ _ _ _ _ _ _ CLz).
              ++ rewrite RB, (PECBD.rc_big p m ty 2 Xg n pos1 GLE EEC BIG), PECBD.r_fail_eq. destruct Xg; reflexivity.
      * apply (PUSH n pos1 eq_refl eq_refl (conj (proj1 Hn) OK) RET). rewrite RB. apply (PECBD.rc_ok p m ty 2 Xg n pos1 GLE EEC OK).
  -
    apply (TAILR (r_fail Xg) MID); [reflexivity|]. rewrite RB. symmetry. apply (PECBD.rc_none p m ty 2 Xg GLE).
Qed.

Lemma push_slot_C (n : Z) (Xg : st) pos1 fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 e4 :
  amid fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en k e4 (w_pos pos1 Xg) -> s_ec X = false -> 0 <= n <= 16777216 ->
  getr R4 (reg 10) = Z_to_bv 64 n -> getr R4 (reg 23) = Z_to_bv 64 (op + 24) ->
  s_more Xg = true -> s_ec Xg = s_ec X -> s_stk Xg = s_stk X -> s_estk Xg = s_estk X -> s_edepth Xg = s_edepth X -> s_lo Xg = s_lo X -> s_hi Xg = s_hi X -> s_bad Xg = s_bad X ->
  Z.of_nat (length (s_stk X)) <= 1024 ->
  r_begin p false X = w_more true (e_begin_len 2 n (w_stk (PS Marray n 0 0 :: s_stk Xg) (w_pos pos1 Xg))) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx4) RSEGS R4 0xb6b80 M4 md4) K.
Proof.
  intros MID EC Hn Q10 A23 MORE EEC ESTK EESTK EED ELO EHI EBAD STKB RB.
  set (Xs := w_stk (PS Marray n 0 0 :: s_stk Xg) (w_pos pos1 Xg)) in *.
  assert (XsF : s_stk Xs = PS Marray n 0 0 :: s_stk (w_pos pos1 Xg) /\ s_estk Xs = s_estk X /\ s_edepth Xs = s_edepth X /\ s_lo Xs = s_lo X /\ s_hi Xs = s_hi X /\ s_bad Xs = s_bad X /\ s_more Xs = true).
  { unfold Xs. destruct Xg; cbn in *; repeat split; congruence. }
  destruct XsF as (XS1 & XS2 & XS3 & XS4 & XS5 & XS6 & XS7).
  destruct (nbhb_of (e_begin_len 2 n Xs) RB) as (NB' & HB').
  pose proof (mp_encb_of Xs XS2 XS3 XS4 XS5 XS6) as MPE.
  assert (ECY : s_ec (w_pos pos1 Xg) = false) by (destruct Xg; cbn in *; congruence).
  assert (HL : Z.of_nat (length (PM.p_stk si4)) <= PM.MAX_DEPTH).
  { pose proof MID as (_ & _ & CPl & _). pose proof CPl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLl & _). destruct CLl as (_ & _ & _ & Lstk & _).
    rewrite Lstk, PEC.stk_conv_length. replace (s_stk (w_pos pos1 Xg)) with (s_stk X) by (destruct Xg; cbn in *; congruence). unfold PM.MAX_DEPTH. clear - STKB; lia. }

  pose proof (ec_vis0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECY) as EC0.
  assert (Q0n : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
  entry_facts. frame_facts. piece_ctx MID.
  pz PEABAP2.abaCf_conc fx4 R4 0 0 0 n as PK. L5SAR.feed PK ltac:(first [fcl | clear - Hn; lia]).
  destruct PK as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & Y12 & C116 & C112).
  apply (amid_pieceS fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en k e4 (w_pos pos1 Xg) fx5 R5 0xb6b80 0xb7d9c M5v (fun a => sp - 116 <= a < sp - 116 + 12) MID MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| exact Na]. }
  { intros a X'; clear - X'; lia. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
  keep_only EC Hn A23 STKB RB XS1 XS7 NB' HB' MPE ECY HL KS5 Y1 Y10 Y11 Y12 C116 C112.
  intros M5 md5 VIS5 HID5 MGM5 FR5 MID.
  entry_facts.
  destruct (stk_cell _ _ _ _ _ _ _ _ _ _ _ _ _ (sp - 116) 4 MID ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (AC1 & BZ1 & AO1 & U1 & _).
  destruct (stk_cell _ _ _ _ _ _ _ _ _ _ _ _ _ (sp - 112) 8 MID ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (AC2 & BZ2 & AO2 & _ & U2).
  rewrite HID5, VIS5 in U1, U2.
  pose proof (U1 2 C116 eq_refl) as C116m. pose proof (U2 n C112 eq_refl) as C112m.
  pose proof PMS as PSH. unfold PECSA.push_ms_spec, PMSAX.push_ms_spec in PSH. cbn [paa_esp_ms AAD PeCLayoutA.CAADDR_A] in PSH.
  apply (call_push 0xb7d9c (PMSAX.cells_ms RSEGS ar) PSH (PS Marray n 0 0) 0xb6c88 fx5 R5 M5 md5 LK4 Aw4 cr4 si4 sm4 en k e4 (w_pos pos1 Xg) MID Y1
           ltac:(split; [clear; lia| reflexivity]) Y10).
  - unfold PMSAX.cells_ms. exists (sp - 116), (sp - 112), 2, n.
    split; [rewrite L5K.rl11; exact Y11|]. split; [rewrite L5K.rl12; exact Y12|].
    split; [replace (sp - 116) with (sp + (-29) * 4) by (clear; lia); rewrite Z_mod_plus_full; apply mod4_of16; exact A16|].
    split; [replace (sp - 112) with (sp + (-14) * 8) by (clear; lia); rewrite Z_mod_plus_full; apply PMKA.mod16_8'; exact A16|].
    split; [exact AC1|]. split; [exact AC2|]. split; [exact AO1|]. split; [exact AO2|]. split; [exact BZ1|]. split; [exact BZ2|].
    split; [exact C116m|]. split; [exact C112m|]. split; [clear; lia|]. split; [clear - Hn; lia| reflexivity].
  - unfold PM.pstate_ok, PEC.ps_conv. cbn [PEC.mode_code ps_mode ps_len ps_type ps_idx PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx].
    split; [clear; lia|]. left. split; [unfold PM.mode_counted; left; reflexivity|]. unfold PM.MAX_ITEMS. clear - Hn; lia.
  - unfold PM.mode_bottom, PEC.ps_conv. cbn [PEC.mode_code ps_mode PM.ps_mode]. clear; lia.
  - exact HL.
  - keep_only EC Hn A23 RB XS1 XS7 NB' HB' MPE ECY KS5 C112m.
    intros fx6 R6 M6 md6 LK6 Aw6 b' k' cr6 RP6 MID KP6.
    set (si6 := PMABK.push_st si4 b' k' (PEC.ps_conv (PS Marray n 0 0))) in *.
    change (w_stk (PS Marray n 0 0 :: s_stk (w_pos pos1 Xg)) (w_pos pos1 Xg)) with Xs in MID.
    assert (B23 : getr R6 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R5 R6 23 RP6) by inl; rewrite (KS5 23%nat) by inl; exact A23).
    clear KS5. entry_facts. frame_facts.
    assert (C112' : L5.u64_at RSEGS M6 (sp - 112) n) by (apply (L5C.u64_at_agree RSEGS M5 M6); [intros i Hi'; apply KP6; clear - Hi'; lia| clear - GSLO GSHI GSPT; lia| clear - GSLO GSHI GSPT; lia| exact C112m]).
    assert (Q0n : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
    piece_ctx MID. vis_amid BI Hi MVi.
    assert (C112v : L5.u64_at RSEGS MVi (sp - 112) n).
    { apply (proj2 (L5A.u64_at_vis Hi M6 (sp - 112) n (L5A.avis_sub Hi (sp - 128) (sp - (sp - 128)) (sp - 112) 8 VSi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GSLO GSHI GSPT; lia) ltac:(clear - GSLO GSHI GSPT; lia))). exact C112'. }

    pz PEABAP2.abaCT_conc fx6 R6 0 0 0 n as PK. L5SAR.feed PK ltac:(first [fcl | clear - Hn; lia]).
    destruct PK as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11 & Y12 & Y13 & Y14 & _).
    assert (E7 : M7v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). subst M7v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK6 cr6 Aw6 M6 md6 fx6 fx7 R6 0xb6c88 R7 0xaad68 MVi K HHi AMi MS7 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M7 md7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7.
    assert (E7 : M7 = M6) by (apply L5SAR.mem_eq_of_agree; exact FR7). subst M7.
    assert (MID7 : amid fx7 R7 M6 md7 LK6 Aw6 cr6 si6 sm4 en k e4 Xs).
    { apply (amid_regs fx6 R6 M6 md6 LK6 Aw6 cr6 si6 sm4 en k e4 _ fx7 R7 md7 MID); [| exact HH7| exact AM7| exact MRT7].
      intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
    pose proof VBL as VX. unfold PECSA.v_begin_arr_len_spec, PECSPA.v_begin_arr_len_spec in VX. cbn [pe_begin_arr_len EE PeCLayoutA.EADDR_A] in VX.
    apply (call_slot Z 0xaad68 (PECSPA.args_len AD) (fun _ => PECSPA.mp_encb) (fun n' _ X' => e_begin_len 2 n' X') VX n 0xb6ccc fx7 R7 M6 md7 LK6 Aw6 cr6 si6 sm4 en k e4 Xs MID7 Y1
             ltac:(split; [clear; lia| reflexivity]) Y10).
    + unfold PECSPA.args_len. rewrite L5K.rl11, L5K.rl14. split; [unfold UbjRef.MAX_ITEMS; clear - Hn; lia|]. split; [exact Y11| exact Y14].
    + exact MPE.
    + exact NB'.
    + exact HB'.
    + keep_only RB XS7 B23 KS7 Hn C112'. intros fx8 R8 M8 md8 LK8 Aw8 en8 k8 e8 cr8 RP8 MID KP8.
      assert (C23 : getr R8 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R7 R8 23 RP8) by inl; rewrite (KS7 23%nat) by inl; exact B23).
      clear KS7. entry_facts. frame_facts.
      assert (C112'' : L5.u64_at RSEGS M8 (sp - 112) n) by (apply (L5C.u64_at_agree RSEGS M6 M8); [intros i Hi'; apply KP8; clear - Hi'; lia| clear - GSLO GSHI GSPT; lia| clear - GSLO GSHI GSPT; lia| exact C112']).
      assert (Q0n : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
      piece_ctx MID. vis_amid BI Hi MVi.
      assert (C112v : L5.u64_at RSEGS MVi (sp - 112) n).
      { apply (proj2 (L5A.u64_at_vis Hi M8 (sp - 112) n (L5A.avis_sub Hi (sp - 128) (sp - (sp - 128)) (sp - 112) 8 VSi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GSLO GSHI GSPT; lia) ltac:(clear - GSLO GSHI GSPT; lia))). exact C112''. }

      pz PEABAP3.abaCTr_conc fx8 R8 0 0 0 n as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Hn; lia]).
      destruct PZ as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & E1 & E2 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
      apply (finish 1 (r_begin p false X) fx8 R8 M8 md8 LK8 Aw8 cr8 si6 sm4 en8 k8 e8 _ fx9 R9 M9v 0xb6ccc MID MS9 MG9 FRZ9).
      * intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
      * intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R9 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
      * exact E2.
      * exact FL0.
      * exact MO0.
      * right; reflexivity.
      * reflexivity.
      * rewrite RB, (PECBD.w_more_e_begin_len 2 n Xs XS7). pose proof MID as (_ & _ & CPz & _). pose proof CPz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLz & _). apply (clink_more1 _ _ _ _ _ CLz). destruct (PECBD.e_begin_len_fields 2 n Xs) as (_ & _ & -> & _); exact XS7.
      * rewrite RB, (PECBD.w_more_e_begin_len 2 n Xs XS7). reflexivity.
Qed.

Lemma sub_C fxi Ri Mi mdi LKi Awi cri si smi :
  s_depth X + 1 <= UbjRef.MAX_DEPTH ->
  amid fxi Ri Mi mdi LKi Awi cri si smi en k e (PECBD.X1 X) -> s_pos X < blen p -> bat p (s_pos X) = 35 ->
  getr Ri (reg 10) = Z_to_bv 64 35 -> getr Ri (reg 23) = Z_to_bv 64 (op + 24) -> 1 <= PM.sr_rem (PM.p_src si) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb6a88 Mi mdi) K.
Proof.
  intros HD MID PLT C35 Q10 A23 REM.
  destruct entry_model as (BOK & PPOS & PLH & PBAD & PED & PEOK & MORE & DONE & HALT & DEP & EST & STKLE).
  pose proof (PECBD.X1_fields X) as (F_stk & F_pos & F_more & F_done & F_halt & F_depth & F_ec & F_estk & F_edepth & F_lo & F_hi & F_bad).
  entry_facts. frame_facts. piece_ctx MID.

  pz PEABAP1.abaKh_conc fxi Ri 0 0 0 0 as PK. L5SAR.feed PK fcl.
  destruct PK as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11).
  assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx3 Ri 0xb6a88 R3 0xb4cf4 MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
  assert (E3 : M3 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
  assert (MID3 : amid fx3 R3 Mi md3 LKi Awi cri si smi en k e (PECBD.X1 X)).
  { apply (amid_regs fxi Ri Mi mdi LKi Awi cri si smi en k e _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
    intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
  apply (call_ignore 0xb6b74 fx3 R3 Mi md3 LKi Awi cri si smi en k e (PECBD.X1 X) MID3 ltac:(rewrite F_more; exact MORE) ltac:(rewrite F_done; exact DONE) ltac:(rewrite F_pos; clear - PPOS PLT; lia)
           Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 REM).
  keep_only HD PLT C35 A23 KS3 BOK PPOS PLH PBAD PED PEOK MORE DONE HALT DEP EST STKLE F_stk F_pos F_more F_done F_halt F_depth F_ec F_estk F_edepth F_lo F_hi F_bad.
  intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 RP4 _ _ MID.
  set (Xc := w_pos (s_pos (PECBD.X1 X) + 1) (PECBD.X1 X)) in *. set (si4 := PMSPA.with_src si src4) in *.
  assert (B23 : getr R4 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R3 R4 23 RP4) by inl; rewrite (KS3 23%nat) by inl; exact A23).
  clear KS3 RP4.
  assert (XcF : s_pos Xc = s_pos X + 1 /\ s_more Xc = true /\ s_done Xc = false /\ s_halt Xc = false /\ s_bad Xc = false /\ s_ec Xc = s_ec X /\ s_stk Xc = s_stk X
                /\ s_estk Xc = s_estk X /\ s_edepth Xc = s_edepth X /\ s_lo Xc = s_lo X /\ s_hi Xc = s_hi X).
  { unfold Xc, PECBD.X1. destruct X; cbn in *; repeat split; assumption. }
  destruct XcF as (C_pos & C_more & C_done & C_halt & C_bad & C_ec & C_stk & C_estk & C_edepth & C_lo & C_hi).

  entry_facts. frame_facts. piece_ctx MID.
  pz PEABAP2.abaC1_conc fx4 R4 0 0 0 0 as PK. L5SAR.feed PK fcl.
  destruct PK as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10 & Z11).
  assert (E5 : M5v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cri Aw4 M4 md4 fx4 fx5 R4 0xb6b74 R5 0xb5f04 MVi K HHi AMi MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
  assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
  assert (MID5 : amid fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 en k e Xc).
  { apply (amid_regs fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 en k e _ fx5 R5 md5 MID); [| exact HH5| exact AM5| exact MRT5].
    intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
  apply (call_gl 0xb6b80 fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 en k e Xc MID5 Z1 ltac:(split; [clear; lia| reflexivity]) Z10 Z11).
  { unfold PECSPA.mp_gl. rewrite C_pos, C_more, C_done, C_halt, C_bad. split; [exact BOK|]. split; [clear - PPOS PLT; lia|]. repeat split; reflexivity. }
  keep_only HD PLT C35 B23 KS5 BOK PPOS PBAD STKLE F_pos C_pos C_more C_done C_halt C_bad C_ec C_stk C_estk C_edepth C_lo C_hi.
  intros fx6 R6 M6 md6 LK6 Aw6 cr6 s6 sm6 e6 RP6 RET6 MID _ _ _ _ _ _.
  assert (C23 : getr R6 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R5 R6 23 RP6) by inl; rewrite (KS5 23%nat) by inl; exact B23).
  apply (after_gl 0xb6b80 Marray 0 Xc fx6 R6 M6 md6 LK6 Aw6 cr6 s6 sm6 e6 ltac:(left; reflexivity) RET6 MID C23 ltac:(intros X'; discriminate X') C_more C_done ltac:(rewrite C_pos; clear - PPOS PLT; lia)
           C_ec C_stk C_estk C_edepth C_lo C_hi ltac:(rewrite C_bad; symmetry; exact PBAD)).
  - unfold Xc. rewrite F_pos. apply (PECBD.rb_count p false X HD PLT C35).
  - intros n pos1 GLn EC Hn Q10n RB. unfold PECSPA.gl_post in MID. rewrite GLn in MID.
    apply (push_slot_C n Xc pos1 fx6 R6 M6 md6 LK6 Aw6 cr6 s6 sm6 e6 MID EC Hn Q10n C23 C_more C_ec C_stk C_estk C_edepth C_lo C_hi ltac:(rewrite C_bad; symmetry; exact PBAD) ltac:(clear - STKLE HD; unfold UbjRef.MAX_DEPTH in HD; lia) RB).
Qed.

Lemma sub_I fxi Ri Mi mdi LKi Awi cri si smi (c : Z) :
  s_depth X + 1 <= UbjRef.MAX_DEPTH ->
  amid fxi Ri Mi mdi LKi Awi cri si smi en k e (PECBD.X1 X) -> s_pos X < blen p -> bat p (s_pos X) = c -> c <> 36 -> c <> 35 ->
  getr Ri (reg 10) = Z_to_bv 64 c -> getr Ri (reg 23) = Z_to_bv 64 (op + 24) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb6a88 Mi mdi) K.
Proof.
  intros HD MID PLT Hc N36 N35 Q10 A23.
  destruct entry_model as (BOK & PPOS & PLH & PBAD & PED & PEOK & MORE & DONE & HALT & DEP & EST & STKLE).
  pose proof (PECBD.X1_fields X) as (F_stk & F_pos & F_more & F_done & F_halt & F_depth & F_ec & F_estk & F_edepth & F_lo & F_hi & F_bad).
  pose proof (bat_range p (s_pos X) BOK) as CR. rewrite Hc in CR. assert (Q0cb : 0 <= c < 2 ^ 64) by (clear - CR; lia).
  set (Xs := w_stk (PS Miarray 0 0 0 :: s_stk (PECBD.X1 X)) (PECBD.X1 X)) in *.
  assert (RB : r_begin p false X = w_more true (e_begin_indef 3 Xs)).
  { unfold Xs. rewrite F_stk. rewrite (PECBD.rb_indef p false X HD PLT); [reflexivity| rewrite Hc; exact N36| rewrite Hc; exact N35]. }
  assert (XsF : s_stk Xs = PS Miarray 0 0 0 :: s_stk (PECBD.X1 X) /\ s_estk Xs = s_estk X /\ s_edepth Xs = s_edepth X /\ s_lo Xs = s_lo X /\ s_hi Xs = s_hi X /\ s_bad Xs = s_bad X /\ s_more Xs = true).
  { unfold Xs, PECBD.X1. destruct X; cbn in *; repeat split; congruence. }
  destruct XsF as (XS1 & XS2 & XS3 & XS4 & XS5 & XS6 & XS7).
  destruct (nbhb_of (e_begin_indef 3 Xs) RB) as (NB' & HB').
  pose proof (mp_encb_of Xs XS2 XS3 XS4 XS5 XS6) as MPE.
  assert (HL : Z.of_nat (length (PM.p_stk si)) <= PM.MAX_DEPTH).
  { pose proof MID as (_ & _ & CPl & _). pose proof CPl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLl & _). destruct CLl as (_ & _ & _ & Lstk & _).
    rewrite Lstk, PEC.stk_conv_length, F_stk. unfold PM.MAX_DEPTH. clear - STKLE HD; unfold UbjRef.MAX_DEPTH in HD; lia. }

  entry_facts. frame_facts. piece_ctx MID.
  assert (PK : exists (fx5 : FPState) R5 M5v, mem_grows MVi M5v /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 116 <= i < sp - 116 + 8) -> M5v (Z_to_bv 64 i) = MVi (Z_to_bv 64 i))
               /\ msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 0xb6a88) MVi (seg_rom RSEGS)) (@mkst fx5 R5 (Z_to_bv 64 0xb1990) M5v (seg_rom RSEGS))
               /\ (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 25; 26; 27]%nat -> getr R5 (reg j) = getr Ri (reg j))
               /\ getr R5 (reg 1) = Z_to_bv 64 0xb6bfc /\ getr R5 (reg 10) = Z_to_bv 64 (op + 360) /\ getr R5 (reg 11) = Z_to_bv 64 (sp - 112) /\ getr R5 (reg 12) = Z_to_bv 64 (sp - 116)
               /\ L5.u32_at RSEGS M5v (sp - 116) 0 /\ L5.u32_at RSEGS M5v (sp - 112) 3).
  { destruct (Z_lt_le_dec c 36) as [LT|GE].
    - pz PEABAP1.abaKl_conc fxi Ri 0 c 0 0 as PK. L5SAR.feed PK ltac:(first [fcl | clear - CR LT N35; lia]).
      destruct PK as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & Y12 & C116 & C112).
      exists fx5, R5, M5v. split; [exact MG5|]. split; [exact FRZ5|]. split; [exact MS5|]. split; [intros j Hj; apply KS5; revert j Hj; apply L5K.incl_b; vm_compute; reflexivity|].
      split; [exact Y1|]. split; [exact Y10|]. split; [exact Y11|]. split; [exact Y12|]. split; [exact C116| exact C112].
    - pz PEABAP1.abaKu_conc fxi Ri 0 c 0 0 as PK. L5SAR.feed PK ltac:(first [fcl | clear - CR GE N36; lia]).
      destruct PK as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & Y12 & C116 & C112).
      exists fx5, R5, M5v. split; [exact MG5|]. split; [exact FRZ5|]. split; [exact MS5|]. split; [intros j Hj; apply KS5; revert j Hj; apply L5K.incl_b; vm_compute; reflexivity|].
      split; [exact Y1|]. split; [exact Y10|]. split; [exact Y11|]. split; [exact Y12|]. split; [exact C116| exact C112]. }
  destruct PK as (fx5 & R5 & M5v & MG5 & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & Y12 & C116 & C112).
  apply (amid_pieceS fxi Ri Mi mdi LKi Awi cri si smi en k e (PECBD.X1 X) fx5 R5 0xb6a88 0xb1990 M5v (fun a => sp - 116 <= a < sp - 116 + 8) MID MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| exact Na]. }
  { intros a X'; clear - X'; lia. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
  keep_only HD A23 RB XS1 XS7 NB' HB' MPE HL KS5 Y1 Y10 Y11 Y12 C116 C112.
  intros M5 md5 VIS5 HID5 MGM5 FR5 MID.
  entry_facts.
  destruct (stk_cell _ _ _ _ _ _ _ _ _ _ _ _ _ (sp - 112) 4 MID ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (AC1 & BZ1 & AO1 & U1 & _).
  destruct (stk_cell _ _ _ _ _ _ _ _ _ _ _ _ _ (sp - 116) 4 MID ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (AC2 & BZ2 & AO2 & U2 & _).
  rewrite HID5, VIS5 in U1, U2.
  pose proof (U1 3 C112 eq_refl) as C112m. pose proof (U2 0 C116 eq_refl) as C116m.
  pose proof PMI as PSH. unfold PECSA.push_mi_spec, PMSAX.push_mi_spec in PSH. cbn [paa_esp_mi AAD PeCLayoutA.CAADDR_A] in PSH.
  apply (call_push 0xb1990 (PMSAX.cells_mi RSEGS ar) PSH (PS Miarray 0 0 0) 0xb6bfc fx5 R5 M5 md5 LKi Awi cri si smi en k e (PECBD.X1 X) MID Y1
           ltac:(split; [clear; lia| reflexivity]) Y10).
  - unfold PMSAX.cells_mi. exists (sp - 112), (sp - 116), 3, 0.
    split; [rewrite L5K.rl11; exact Y11|]. split; [rewrite L5K.rl12; exact Y12|].
    split; [replace (sp - 112) with (sp + (-28) * 4) by (clear; lia); rewrite Z_mod_plus_full; apply mod4_of16; exact A16|].
    split; [replace (sp - 116) with (sp + (-29) * 4) by (clear; lia); rewrite Z_mod_plus_full; apply mod4_of16; exact A16|].
    split; [exact AC1|]. split; [exact AC2|]. split; [exact AO1|]. split; [exact AO2|]. split; [exact BZ1|]. split; [exact BZ2|].
    split; [exact C112m|]. split; [exact C116m|]. split; [clear; lia|]. split; [clear; lia| reflexivity].
  - unfold PM.pstate_ok, PEC.ps_conv. cbn [PEC.mode_code ps_mode ps_len ps_type ps_idx PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx].
    split; [clear; lia|]. right; left. split; [unfold PM.mode_indef; left; reflexivity|]. unfold PM.MAX_ITEMS. clear; lia.
  - unfold PM.mode_bottom, PEC.ps_conv. cbn [PEC.mode_code ps_mode PM.ps_mode]. clear; lia.
  - exact HL.
  - keep_only HD A23 RB XS1 XS7 NB' HB' MPE KS5.
    intros fx6 R6 M6 md6 LK6 Aw6 b' k' cr6 RP6 MID KP6.
    set (si6 := PMABK.push_st si b' k' (PEC.ps_conv (PS Miarray 0 0 0))) in *.
    change (w_stk (PS Miarray 0 0 0 :: s_stk (PECBD.X1 X)) (PECBD.X1 X)) with Xs in MID.
    assert (B23 : getr R6 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R5 R6 23 RP6) by inl; rewrite (KS5 23%nat) by inl; exact A23).
    clear KS5. entry_facts. frame_facts. piece_ctx MID.

    pz PEABAP2.abaIT_conc fx6 R6 0 0 0 0 as PK. L5SAR.feed PK fcl.
    destruct PK as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11 & Y12 & Y13 & _).
    assert (E7 : M7v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). subst M7v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK6 cr6 Aw6 M6 md6 fx6 fx7 R6 0xb6bfc R7 0xabff4 MVi K HHi AMi MS7 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M7 md7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7.
    assert (E7 : M7 = M6) by (apply L5SAR.mem_eq_of_agree; exact FR7). subst M7.
    assert (MID7 : amid fx7 R7 M6 md7 LK6 Aw6 cr6 si6 smi en k e Xs).
    { apply (amid_regs fx6 R6 M6 md6 LK6 Aw6 cr6 si6 smi en k e _ fx7 R7 md7 MID); [| exact HH7| exact AM7| exact MRT7].
      intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
    pose proof VBI as VX. unfold PECSA.v_begin_arr_spec, PECSPA.v_begin_arr_spec in VX. cbn [pe_begin_arr EE PeCLayoutA.EADDR_A] in VX.
    apply (call_slot unit 0xabff4 (PECSPA.args_t3 AD) (fun _ => PECSPA.mp_encb) (fun _ _ X' => e_begin_indef 3 X') VX tt 0xb6c38 fx7 R7 M6 md7 LK6 Aw6 cr6 si6 smi en k e Xs MID7 Y1
             ltac:(split; [clear; lia| reflexivity]) Y10).
    + unfold PECSPA.args_t3. rewrite L5K.rl13. exact Y13.
    + exact MPE.
    + exact NB'.
    + exact HB'.
    + keep_only RB XS7 B23 KS7. intros fx8 R8 M8 md8 LK8 Aw8 en8 k8 e8 cr8 RP8 MID _.
      assert (C23 : getr R8 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R7 R8 23 RP8) by inl; rewrite (KS7 23%nat) by inl; exact B23).
      clear KS7. assert (Hn : 0 <= 0 <= 16777216) by (clear; lia).

      entry_facts. frame_facts. piece_ctx MID.
      pz PEABAP3.abaITr_conc fx8 R8 0 0 0 0 as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Hn; lia]).
      destruct PZ as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & E1 & E2 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
      apply (finish 1 (r_begin p false X) fx8 R8 M8 md8 LK8 Aw8 cr8 si6 smi en8 k8 e8 _ fx9 R9 M9v 0xb6c38 MID MS9 MG9 FRZ9).
      * intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
      * intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R9 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
      * exact E2.
      * exact FL0.
      * exact MO0.
      * right; reflexivity.
      * reflexivity.
      * rewrite RB, (PECBD.w_more_e_begin_indef 3 Xs XS7). pose proof MID as (_ & _ & CPz & _). pose proof CPz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLz & _). apply (clink_more1 _ _ _ _ _ CLz). destruct (PECBD.e_begin_indef_fields 3 Xs) as (_ & _ & -> & _); exact XS7.
      * rewrite RB, (PECBD.w_more_e_begin_indef 3 Xs XS7). reflexivity.
Qed.

Lemma push_slot_T (n ty : Z) (Xg : st) pos1 fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 e4 :
  amid fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en k e4 (w_pos pos1 Xg) -> s_ec X = false -> 0 <= n <= 16777216 ->
  getr R4 (reg 10) = Z_to_bv 64 n -> getr R4 (reg 22) = Z_to_bv 64 (F + 32) -> getr R4 (reg 23) = Z_to_bv 64 (op + 24) -> getr R4 (reg 24) = Z_to_bv 64 1 ->
  L5.u8_at RSEGS M4 (F + 32) ty -> L5.u8_at RSEGS M4 (F / 8 + 2147450880 + 4) 1 -> 0 <= ty < 256 ->
  s_more Xg = true -> s_ec Xg = s_ec X -> s_stk Xg = s_stk X -> s_estk Xg = s_estk X -> s_edepth Xg = s_edepth X -> s_lo Xg = s_lo X -> s_hi Xg = s_hi X -> s_bad Xg = s_bad X ->
  Z.of_nat (length (s_stk X)) <= 1024 ->
  r_begin p false X = w_more true (e_begin_len 2 n (w_stk (PS Mtarray n ty 0 :: s_stk Xg) (w_pos pos1 Xg))) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx4) RSEGS R4 0xb6b04 M4 md4) K.
Proof.
  intros MID EC Hn Q10 A22 A23 A24 TB SHB TYR MORE EEC ESTK EESTK EED ELO EHI EBAD STKB RB.
  set (Xs := w_stk (PS Mtarray n ty 0 :: s_stk Xg) (w_pos pos1 Xg)) in *.
  assert (XsF : s_stk Xs = PS Mtarray n ty 0 :: s_stk (w_pos pos1 Xg) /\ s_estk Xs = s_estk X /\ s_edepth Xs = s_edepth X /\ s_lo Xs = s_lo X /\ s_hi Xs = s_hi X /\ s_bad Xs = s_bad X /\ s_more Xs = true).
  { unfold Xs. destruct Xg; cbn in *; repeat split; congruence. }
  destruct XsF as (XS1 & XS2 & XS3 & XS4 & XS5 & XS6 & XS7).
  destruct (nbhb_of (e_begin_len 2 n Xs) RB) as (NB' & HB').
  pose proof (mp_encb_of Xs XS2 XS3 XS4 XS5 XS6) as MPE.
  assert (ECY : s_ec (w_pos pos1 Xg) = false) by (destruct Xg; cbn in *; congruence).
  assert (HL : Z.of_nat (length (PM.p_stk si4)) <= PM.MAX_DEPTH).
  { pose proof MID as (_ & _ & CPl & _). pose proof CPl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLl & _). destruct CLl as (_ & _ & _ & Lstk & _).
    rewrite Lstk, PEC.stk_conv_length. replace (s_stk (w_pos pos1 Xg)) with (s_stk X) by (destruct Xg; cbn in *; congruence). unfold PM.MAX_DEPTH. clear - STKB; lia. }

  pose proof (ec_vis0 _ _ _ _ _ _ _ _ _ _ _ _ _ MID ECY) as EC0.
  assert (Q0n : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
  entry_facts. frame_facts. piece_ctx MID.
  pz PEABAP2.abaTf_conc fx4 R4 0 0 0 n as PK. L5SAR.feed PK ltac:(first [fcl | clear - Hn; lia]).
  destruct PK as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y10 & Y11 & Y12 & Y13 & C116 & C112).
  apply (amid_pieceS fx4 R4 M4 md4 LK4 Aw4 cr4 si4 sm4 en k e4 (w_pos pos1 Xg) fx5 R5 0xb6b04 0xb79f8 M5v (fun a => sp - 116 <= a < sp - 116 + 12) MID MS5 MG5).
  { intros a Ha Na. apply FRZ5; [exact Ha| exact Na]. }
  { intros a X'; clear - X'; lia. }
  { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
  keep_only EC Hn A22 A23 A24 TB SHB TYR STKB RB XS1 XS7 NB' HB' MPE ECY HL KS5 Y1 Y10 Y11 Y12 Y13 C116 C112.
  intros M5 md5 VIS5 HID5 MGM5 FR5 MID.
  entry_facts. frame_facts.
  pose proof GFR as (GF1 & GF2 & _).
  assert (TB5 : L5.u8_at RSEGS M5 (F + 32) ty) by (apply (L5C.u8_at_agree RSEGS M4 M5); [intros i Hi'; apply FR5; [clear - Hi' GF1 GF2; lia| clear - Hi' GFCEIL GSLO; lia]| clear - GF1; lia| clear - GF2; lia| exact TB]).
  assert (SHB5 : L5.u8_at RSEGS M5 (F / 8 + 2147450880 + 4) 1).
  { assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
    apply (L5C.u8_at_agree RSEGS M4 M5); [intros i Hi'; apply FR5; [clear - Hi' D1 D2; lia| clear - Hi' D1 D2 GSLO GSPT GSHI; lia]| clear - D1; lia| clear - D2; lia| exact SHB]. }
  destruct (stk_cell _ _ _ _ _ _ _ _ _ _ _ _ _ (sp - 116) 4 MID ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (AC1 & BZ1 & AO1 & U1 & _).
  destruct (stk_cell _ _ _ _ _ _ _ _ _ _ _ _ _ (sp - 112) 8 MID ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (AC2 & BZ2 & AO2 & _ & U2).
  rewrite HID5, VIS5 in U1, U2.
  pose proof (U1 4 C116 eq_refl) as C116m. pose proof (U2 n C112 eq_refl) as C112m.
  assert (BZ3 : byte_at M5 (HeapIfaceA.S (F + 32)) 1).
  { unfold HeapIfaceA.S, SB, byte_at. replace ((F + 32) / 8 + 2147450880) with (F / 8 + 2147450880 + 4).
    - apply (L5ADHR.byte_of_u8 M5 _ 1 SHB5); [right; clear - GF1; lia| clear - GF1 GF2; lia].
    - replace (F + 32) with (4 * 8 + F) by (clear; lia). rewrite Z.div_add_l by (clear; lia). clear; lia. }
  assert (F32m : (F + 32) mod 8 = 0) by (replace (F + 32) with ((F / 8 + 4) * 8) by (clear - GF8; lia); apply Z_mod_mult).
  assert (AC3 : PMSPA.accA M5 (F + 32) 1).
  { intros a Ha. right. exists 1. split; [replace a with (F + 32) by (clear - Ha; lia); exact BZ3| split; [clear; lia| replace a with (F + 32) by (clear - Ha; lia); rewrite F32m; clear; lia]]. }
  piece_ctx MID. assert (ApF : op + 384 <= F \/ F + 64 <= op) by sya.
  pose proof PMSU as PSH. unfold PECSA.push_msu_spec, PMSAX.push_msu_spec in PSH. cbn [paa_esp_msu AAD PeCLayoutA.CAADDR_A] in PSH.
  apply (call_push 0xb79f8 (PMSAX.cells_msu RSEGS ar) PSH (PS Mtarray n ty 0) 0xb6df4 fx5 R5 M5 md5 LK4 Aw4 cr4 si4 sm4 en k e4 (w_pos pos1 Xg) MID Y1
           ltac:(split; [clear; lia| reflexivity]) Y10).
  - unfold PMSAX.cells_msu. exists (sp - 116), (sp - 112), (F + 32), 4, n, ty.
    split; [rewrite L5K.rl11; exact Y11|]. split; [rewrite L5K.rl12; exact Y12|]. split; [rewrite L5K.rl13; exact Y13|].
    split; [replace (sp - 116) with (sp + (-29) * 4) by (clear; lia); rewrite Z_mod_plus_full; apply mod4_of16; exact A16|].
    split; [replace (sp - 112) with (sp + (-14) * 8) by (clear; lia); rewrite Z_mod_plus_full; apply PMKA.mod16_8'; exact A16|].
    split; [exact AC1|]. split; [exact AC2|]. split; [exact AC3|]. split; [exact AO1|]. split; [exact AO2|].
    split; [split; [left; exists (F, 0, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; clear; lia]| clear - ApF; lia]|].
    split; [exact BZ1|]. split; [exact BZ2|]. split; [split; [exact BZ3| exact F32m]|].
    split; [exact C116m|]. split; [exact C112m|]. split; [exact TB5|]. split; [clear; lia|]. split; [clear - Hn; lia|]. split; [exact TYR| reflexivity].
  - unfold PM.pstate_ok, PEC.ps_conv. cbn [PEC.mode_code ps_mode ps_len ps_type ps_idx PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx].
    split; [exact TYR|]. left. split; [unfold PM.mode_counted; right; left; reflexivity|]. unfold PM.MAX_ITEMS. clear - Hn; lia.
  - unfold PM.mode_bottom, PEC.ps_conv. cbn [PEC.mode_code ps_mode PM.ps_mode]. clear; lia.
  - exact HL.
  - keep_only EC Hn A22 A23 A24 RB XS1 XS7 NB' HB' MPE ECY KS5 C112m.
    intros fx6 R6 M6 md6 LK6 Aw6 b' k' cr6 RP6 MID KP6.
    set (si6 := PMABK.push_st si4 b' k' (PEC.ps_conv (PS Mtarray n ty 0))) in *.
    change (w_stk (PS Mtarray n ty 0 :: s_stk (w_pos pos1 Xg)) (w_pos pos1 Xg)) with Xs in MID.
    assert (B22 : getr R6 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved R5 R6 22 RP6) by inl; rewrite (KS5 22%nat) by inl; exact A22).
    assert (B23 : getr R6 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R5 R6 23 RP6) by inl; rewrite (KS5 23%nat) by inl; exact A23).
    assert (B24 : getr R6 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R5 R6 24 RP6) by inl; rewrite (KS5 24%nat) by inl; exact A24).
    clear KS5. entry_facts. frame_facts.
    assert (C112' : L5.u64_at RSEGS M6 (sp - 112) n) by (apply (L5C.u64_at_agree RSEGS M5 M6); [intros i Hi'; apply KP6; clear - Hi'; lia| clear - GSLO GSHI GSPT; lia| clear - GSLO GSHI GSPT; lia| exact C112m]).
    assert (Q0n : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
    piece_ctx MID. vis_amid BI Hi MVi.
    assert (C112v : L5.u64_at RSEGS MVi (sp - 112) n).
    { apply (proj2 (L5A.u64_at_vis Hi M6 (sp - 112) n (L5A.avis_sub Hi (sp - 128) (sp - (sp - 128)) (sp - 112) 8 VSi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GSLO GSHI GSPT; lia) ltac:(clear - GSLO GSHI GSPT; lia))). exact C112'. }

    pz PEABAP2.abaTT_conc fx6 R6 0 0 0 n as PK. L5SAR.feed PK ltac:(first [fcl | clear - Hn; lia]).
    destruct PK as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11 & Y12 & Y13 & Y14 & _).
    assert (E7 : M7v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). subst M7v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK6 cr6 Aw6 M6 md6 fx6 fx7 R6 0xb6df4 R7 0xaad68 MVi K HHi AMi MS7 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M7 md7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7.
    assert (E7 : M7 = M6) by (apply L5SAR.mem_eq_of_agree; exact FR7). subst M7.
    assert (MID7 : amid fx7 R7 M6 md7 LK6 Aw6 cr6 si6 sm4 en k e4 Xs).
    { apply (amid_regs fx6 R6 M6 md6 LK6 Aw6 cr6 si6 sm4 en k e4 _ fx7 R7 md7 MID); [| exact HH7| exact AM7| exact MRT7].
      intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
    pose proof VBL as VX. unfold PECSA.v_begin_arr_len_spec, PECSPA.v_begin_arr_len_spec in VX. cbn [pe_begin_arr_len EE PeCLayoutA.EADDR_A] in VX.
    apply (call_slot Z 0xaad68 (PECSPA.args_len AD) (fun _ => PECSPA.mp_encb) (fun n' _ X' => e_begin_len 2 n' X') VX n 0xb6e38 fx7 R7 M6 md7 LK6 Aw6 cr6 si6 sm4 en k e4 Xs MID7 Y1
             ltac:(split; [clear; lia| reflexivity]) Y10).
    + unfold PECSPA.args_len. rewrite L5K.rl11, L5K.rl14. split; [unfold UbjRef.MAX_ITEMS; clear - Hn; lia|]. split; [exact Y11| exact Y14].
    + exact MPE.
    + exact NB'.
    + exact HB'.
    + keep_only RB XS7 B22 B23 B24 KS7 Hn C112'. intros fx8 R8 M8 md8 LK8 Aw8 en8 k8 e8 cr8 RP8 MID KP8.
      assert (C22 : getr R8 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved R7 R8 22 RP8) by inl; rewrite (KS7 22%nat) by inl; exact B22).
      assert (C23 : getr R8 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R7 R8 23 RP8) by inl; rewrite (KS7 23%nat) by inl; exact B23).
      assert (C24 : getr R8 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R7 R8 24 RP8) by inl; rewrite (KS7 24%nat) by inl; exact B24).
      clear KS7. entry_facts. frame_facts.
      assert (C112'' : L5.u64_at RSEGS M8 (sp - 112) n) by (apply (L5C.u64_at_agree RSEGS M6 M8); [intros i Hi'; apply KP8; clear - Hi'; lia| clear - GSLO GSHI GSPT; lia| clear - GSLO GSHI GSPT; lia| exact C112']).
      assert (Q0n : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
      piece_ctx MID. vis_amid BI Hi MVi.
      assert (C112v : L5.u64_at RSEGS MVi (sp - 112) n).
      { apply (proj2 (L5A.u64_at_vis Hi M8 (sp - 112) n (L5A.avis_sub Hi (sp - 128) (sp - (sp - 128)) (sp - 112) 8 VSi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GSLO GSHI GSPT; lia) ltac:(clear - GSLO GSHI GSPT; lia))). exact C112''. }

      pz PEABAP3.abaTTr_conc fx8 R8 0 0 0 n as PZ. L5SAR.feed PZ ltac:(first [fcl | clear - Hn; lia]).
      destruct PZ as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & E1 & E2 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
      apply (finish 1 (r_begin p false X) fx8 R8 M8 md8 LK8 Aw8 cr8 si6 sm4 en8 k8 e8 _ fx9 R9 M9v 0xb6e38 MID MS9 MG9 FRZ9).
      * intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
      * intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R9 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
      * exact E2.
      * exact FL0.
      * exact MO0.
      * right; reflexivity.
      * reflexivity.
      * rewrite RB, (PECBD.w_more_e_begin_len 2 n Xs XS7). pose proof MID as (_ & _ & CPz & _). pose proof CPz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLz & _). apply (clink_more1 _ _ _ _ _ CLz). destruct (PECBD.e_begin_len_fields 2 n Xs) as (_ & _ & -> & _); exact XS7.
      * rewrite RB, (PECBD.w_more_e_begin_len 2 n Xs XS7). reflexivity.
Qed.

Lemma sub_T3 (ty : Z) fx8 R8 M8 md8 LK8 Aw8 cri si8 sm8 :
  s_depth X + 1 <= UbjRef.MAX_DEPTH -> s_pos X < blen p -> bat p (s_pos X) = 36 -> s_pos X + 2 < blen p -> bat p (s_pos X + 2) = 35 -> ty = bat p (s_pos X + 1) ->
  amid fx8 R8 M8 md8 LK8 Aw8 cri si8 sm8 en k e (w_pos (s_pos X + 2) (PECBD.X1 X)) ->
  getr R8 (reg 10) = Z_to_bv 64 35 -> getr R8 (reg 22) = Z_to_bv 64 (F + 32) -> getr R8 (reg 23) = Z_to_bv 64 (op + 24) -> getr R8 (reg 24) = Z_to_bv 64 1 ->
  L5.u8_at RSEGS M8 (F + 32) ty -> L5.u8_at RSEGS M8 (F / 8 + 2147450880 + 4) 1 -> 1 <= PM.sr_rem (PM.p_src si8) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx8) RSEGS R8 0xb6ad8 M8 md8) K.
Proof.
  intros HD PLT C36 PLT2 C35 Hty MID Q10 A22 A23 A24 TB SHB REM.
  destruct entry_model as (BOK & PPOS & PLH & PBAD & PED & PEOK & MORE & DONE & HALT & DEP & EST & STKLE).
  pose proof (PECBD.X1_fields X) as (F_stk & F_pos & F_more & F_done & F_halt & F_depth & F_ec & F_estk & F_edepth & F_lo & F_hi & F_bad).
  pose proof (bat_range p (s_pos X + 1) BOK) as TYR. rewrite <- Hty in TYR.
  set (Xt2 := w_pos (s_pos X + 2) (PECBD.X1 X)) in *.
  assert (Xt2F : s_pos Xt2 = s_pos X + 2 /\ s_more Xt2 = true /\ s_done Xt2 = false /\ s_halt Xt2 = false /\ s_bad Xt2 = false /\ s_ec Xt2 = s_ec X /\ s_stk Xt2 = s_stk X
                /\ s_estk Xt2 = s_estk X /\ s_edepth Xt2 = s_edepth X /\ s_lo Xt2 = s_lo X /\ s_hi Xt2 = s_hi X).
  { unfold Xt2, PECBD.X1. destruct X; cbn in *; repeat split; assumption. }
  destruct Xt2F as (T_pos & T_more & T_done & T_halt & T_bad & T_ec & T_stk & T_estk & T_edepth & T_lo & T_hi).
  entry_facts. frame_facts. piece_ctx MID.

  pz PEABAP1.abaT3h_conc fx8 R8 0 0 0 0 as PK. L5SAR.feed PK fcl.
  destruct PK as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y10 & Y11).
  assert (E9 : M9v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ9; exact Ha). subst M9v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK8 cri Aw8 M8 md8 fx8 fx9 R8 0xb6ad8 R9 0xb4cf4 MVi K HHi AMi MS9 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M9 md9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9.
  assert (E9 : M9 = M8) by (apply L5SAR.mem_eq_of_agree; exact FR9). subst M9.
  assert (MID9 : amid fx9 R9 M8 md9 LK8 Aw8 cri si8 sm8 en k e Xt2).
  { apply (amid_regs fx8 R8 M8 md8 LK8 Aw8 cri si8 sm8 en k e _ fx9 R9 md9 MID); [| exact HH9| exact AM9| exact MRT9].
    intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
  apply (call_ignore 0xb6af8 fx9 R9 M8 md9 LK8 Aw8 cri si8 sm8 en k e Xt2 MID9 T_more T_done ltac:(rewrite T_pos; clear - PPOS PLT2; lia) Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 REM).
  keep_only HD PLT C36 PLT2 C35 Hty A22 A23 A24 TB SHB TYR KS9 T_pos BOK PPOS PLH PBAD PED PEOK MORE DONE HALT DEP EST STKLE F_stk F_pos F_more F_done F_halt F_depth F_ec F_estk F_edepth F_lo F_hi F_bad.
  intros fx10 R10 M10 md10 LK10 Aw10 src10 sm10 RP10 AGS AGD MID.
  unfold Xt2 in MID. rewrite PECBD.w_pos_w_pos in MID. destruct (PECBD.w_pos_fields (s_pos X + 2) (PECBD.X1 X)) as (_ & EQp & _). rewrite EQp in MID. clear EQp.
  replace (s_pos X + 2 + 1) with (s_pos X + 3) in MID by (clear; lia).
  set (Xt3 := w_pos (s_pos X + 3) (PECBD.X1 X)) in *. set (si10 := PMSPA.with_src si8 src10) in *.
  assert (C22 : getr R10 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved R9 R10 22 RP10) by inl; rewrite (KS9 22%nat) by inl; exact A22).
  assert (C23 : getr R10 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R9 R10 23 RP10) by inl; rewrite (KS9 23%nat) by inl; exact A23).
  assert (C24 : getr R10 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R9 R10 24 RP10) by inl; rewrite (KS9 24%nat) by inl; exact A24).
  clear KS9 RP10. entry_facts. frame_facts.
  pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (TB' : L5.u8_at RSEGS M10 (F + 32) ty) by (apply (L5C.u8_at_agree RSEGS M8 M10); [intros i Hi'; apply AGD; clear - Hi'; lia| clear - GF1; lia| clear - GF2; lia| exact TB]).
  assert (SHB' : L5.u8_at RSEGS M10 (F / 8 + 2147450880 + 4) 1) by (apply (L5C.u8_at_agree RSEGS M8 M10); [intros i Hi'; apply AGS; clear - Hi'; lia| clear - D1; lia| clear - D2; lia| exact SHB]).
  clear TB SHB GF1 GF2 D1 D2 AGD AGS. rename TB' into TB. rename SHB' into SHB.
  assert (Xt3F : s_pos Xt3 = s_pos X + 3 /\ s_more Xt3 = true /\ s_done Xt3 = false /\ s_halt Xt3 = false /\ s_bad Xt3 = false /\ s_ec Xt3 = s_ec X /\ s_stk Xt3 = s_stk X
                /\ s_estk Xt3 = s_estk X /\ s_edepth Xt3 = s_edepth X /\ s_lo Xt3 = s_lo X /\ s_hi Xt3 = s_hi X).
  { unfold Xt3, PECBD.X1. destruct X; cbn in *; repeat split; assumption. }
  destruct Xt3F as (U_pos & U_more & U_done & U_halt & U_bad & U_ec & U_stk & U_estk & U_edepth & U_lo & U_hi).

  piece_ctx MID.
  pz PEABAP1.abaT4_conc fx10 R10 0 0 0 0 as PK. L5SAR.feed PK fcl.
  destruct PK as (fx11 & R11 & M11v & MG11 & _ & FRZ11 & MS11 & KS11 & Z1 & Z10 & Z11).
  assert (E11 : M11v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ11; exact Ha). subst M11v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK10 cri Aw10 M10 md10 fx10 fx11 R10 0xb6af8 R11 0xb5f04 MVi K HHi AMi MS11 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M11 md11 HH11 AM11 MRT11 HID11 VIS11 MGM11 FR11.
  assert (E11 : M11 = M10) by (apply L5SAR.mem_eq_of_agree; exact FR11). subst M11.
  assert (MID11 : amid fx11 R11 M10 md11 LK10 Aw10 cri si10 sm10 en k e Xt3).
  { apply (amid_regs fx10 R10 M10 md10 LK10 Aw10 cri si10 sm10 en k e _ fx11 R11 md11 MID); [| exact HH11| exact AM11| exact MRT11].
    intros j Hj. apply KS11. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
  apply (call_gl 0xb6b04 fx11 R11 M10 md11 LK10 Aw10 cri si10 sm10 en k e Xt3 MID11 Z1 ltac:(split; [clear; lia| reflexivity]) Z10 Z11).
  { unfold PECSPA.mp_gl. rewrite U_pos, U_more, U_done, U_halt, U_bad. split; [exact BOK|]. split; [clear - PPOS PLT2; lia|]. repeat split; reflexivity. }
  keep_only HD PLT C36 PLT2 C35 Hty C22 C23 C24 TB SHB TYR KS11 BOK PPOS PBAD STKLE U_pos U_more U_done U_halt U_bad U_ec U_stk U_estk U_edepth U_lo U_hi.
  intros fx12 R12 M12 md12 LK12 Aw12 cr12 s12 sm12 e12 RP12 RET12 MID _ _ _ _ BGS BGD.
  assert (D22 : getr R12 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved R11 R12 22 RP12) by inl; rewrite (KS11 22%nat) by inl; exact C22).
  assert (D23 : getr R12 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R11 R12 23 RP12) by inl; rewrite (KS11 23%nat) by inl; exact C23).
  assert (D24 : getr R12 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R11 R12 24 RP12) by inl; rewrite (KS11 24%nat) by inl; exact C24).
  clear KS11 RP12. entry_facts. frame_facts.
  pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (TB' : L5.u8_at RSEGS M12 (F + 32) ty) by (apply (L5C.u8_at_agree RSEGS M10 M12); [intros i Hi'; apply BGD; clear - Hi'; lia| clear - GF1; lia| clear - GF2; lia| exact TB]).
  assert (SHB' : L5.u8_at RSEGS M12 (F / 8 + 2147450880 + 4) 1) by (apply (L5C.u8_at_agree RSEGS M10 M12); [intros i Hi'; apply BGS; clear - Hi'; lia| clear - D1; lia| clear - D2; lia| exact SHB]).
  clear TB SHB GF1 GF2 D1 D2 BGD BGS. rename TB' into TB. rename SHB' into SHB.
  apply (after_gl 0xb6b04 Mtarray ty Xt3 fx12 R12 M12 md12 LK12 Aw12 cr12 s12 sm12 e12 ltac:(right; reflexivity) RET12 MID D23 ltac:(intros _; exact (conj D22 D24)) U_more U_done ltac:(rewrite U_pos; clear - PPOS PLT2; lia)
           U_ec U_stk U_estk U_edepth U_lo U_hi ltac:(rewrite U_bad; symmetry; exact PBAD)).
  - unfold Xt3. rewrite Hty. apply (PECBD.rb_typed p false X HD PLT C36 PLT2 C35).
  - intros n pos1 GLn EC Hn Q10n RB. unfold PECSPA.gl_post in MID. rewrite GLn in MID.
    apply (push_slot_T n ty Xt3 pos1 fx12 R12 M12 md12 LK12 Aw12 cr12 s12 sm12 e12 MID EC Hn Q10n D22 D23 D24 TB SHB TYR U_more U_ec U_stk U_estk U_edepth U_lo U_hi ltac:(rewrite U_bad; symmetry; exact PBAD)
             ltac:(clear - STKLE HD; unfold UbjRef.MAX_DEPTH in HD; lia) RB).
Qed.

Lemma sub_T2 (ty : Z) fx6 R6 M6 md6 LK6 Aw6 cri si6 sm6 :
  s_depth X + 1 <= UbjRef.MAX_DEPTH -> s_pos X < blen p -> bat p (s_pos X) = 36 -> s_pos X + 2 <= blen p -> ty = bat p (s_pos X + 1) ->
  amid fx6 R6 M6 md6 LK6 Aw6 cri si6 sm6 en k e (w_pos (s_pos X + 2) (PECBD.X1 X)) ->
  getr R6 (reg 10) = Z_to_bv 64 1 -> getr R6 (reg 22) = Z_to_bv 64 (F + 32) -> getr R6 (reg 23) = Z_to_bv 64 (op + 24) -> getr R6 (reg 24) = Z_to_bv 64 1 ->
  L5.u8_at RSEGS M6 (F + 32) ty -> L5.u8_at RSEGS M6 (F / 8 + 2147450880 + 4) 1 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx6) RSEGS R6 0xb6acc M6 md6) K.
Proof.
  intros HD PLT C36 PLE2 Hty MID Q10 A22 A23 A24 TB SHB.
  destruct entry_model as (BOK & PPOS & PLH & PBAD & PED & PEOK & MORE & DONE & HALT & DEP & EST & STKLE).
  pose proof (PECBD.X1_fields X) as (F_stk & F_pos & F_more & F_done & F_halt & F_depth & F_ec & F_estk & F_edepth & F_lo & F_hi & F_bad).
  set (Xt2 := w_pos (s_pos X + 2) (PECBD.X1 X)) in *.
  assert (T2F : s_pos Xt2 = s_pos X + 2 /\ s_more Xt2 = true /\ s_done Xt2 = false).
  { unfold Xt2, PECBD.X1. destruct X; cbn in *; repeat split; assumption. }
  destruct T2F as (T_pos & T_more & T_done).
  entry_facts. frame_facts. piece_ctx MID.

  pz PEABAP1.abaT2p_conc fx6 R6 0 0 0 0 as PK. L5SAR.feed PK fcl.
  destruct PK as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10).
  assert (E7 : M7v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). subst M7v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK6 cri Aw6 M6 md6 fx6 fx7 R6 0xb6acc R7 0xb4bd0 MVi K HHi AMi MS7 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M7 md7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7.
  assert (E7 : M7 = M6) by (apply L5SAR.mem_eq_of_agree; exact FR7). subst M7.
  assert (MID7 : amid fx7 R7 M6 md7 LK6 Aw6 cri si6 sm6 en k e Xt2).
  { apply (amid_regs fx6 R6 M6 md6 LK6 Aw6 cri si6 sm6 en k e _ fx7 R7 md7 MID); [| exact HH7| exact AM7| exact MRT7].
    intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
  apply (call_peek 0xb6ad8 fx7 R7 M6 md7 LK6 Aw6 cri si6 sm6 en k e Xt2 MID7 T_more T_done ltac:(rewrite T_pos; clear - PPOS PLE2; lia) Y1 ltac:(split; [clear; lia| reflexivity]) Y10).
  keep_only HD PLT C36 PLE2 Hty A22 A23 A24 TB SHB KS7 T_pos T_more T_done BOK PPOS PLH PBAD PED PEOK MORE DONE HALT DEP EST STKLE F_stk F_pos F_more F_done F_halt F_depth F_ec F_estk F_edepth F_lo F_hi F_bad.
  intros fx8 R8 M8 md8 LK8 Aw8 src8 sm8 RP8 ALT AGS AGD MID.
  rewrite T_pos in ALT. set (si8 := PMSPA.with_src si6 src8) in *.
  assert (C22 : getr R8 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved R7 R8 22 RP8) by inl; rewrite (KS7 22%nat) by inl; exact A22).
  assert (C23 : getr R8 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R7 R8 23 RP8) by inl; rewrite (KS7 23%nat) by inl; exact A23).
  assert (C24 : getr R8 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R7 R8 24 RP8) by inl; rewrite (KS7 24%nat) by inl; exact A24).
  clear KS7 RP8. entry_facts. frame_facts.
  pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (TB' : L5.u8_at RSEGS M8 (F + 32) ty) by (apply (L5C.u8_at_agree RSEGS M6 M8); [intros i Hi'; apply AGD; clear - Hi'; lia| clear - GF1; lia| clear - GF2; lia| exact TB]).
  assert (SHB' : L5.u8_at RSEGS M8 (F / 8 + 2147450880 + 4) 1) by (apply (L5C.u8_at_agree RSEGS M6 M8); [intros i Hi'; apply AGS; clear - Hi'; lia| clear - D1; lia| clear - D2; lia| exact SHB]).
  clear TB SHB GF1 GF2 D1 D2 AGD AGS. rename TB' into TB. rename SHB' into SHB.
  piece_ctx MID.
  destruct ALT as [(Z10 & EOF)|(PLT2 & Z10 & REM8)].
  -
    pz PEABAP1.abaT3e_conc fx8 R8 0 0 0 0 as PK. L5SAR.feed PK ltac:(first [fcl]).
    destruct PK as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1' & Y10' & Y11').
    assert (E9 : M9v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ9; exact Ha). subst M9v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK8 cri Aw8 M8 md8 fx8 fx9 R8 0xb6ad8 R9 0xae310 MVi K HHi AMi MS9 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M9 md9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9.
    assert (E9 : M9 = M8) by (apply L5SAR.mem_eq_of_agree; exact FR9). subst M9.
    assert (MID9 : amid fx9 R9 M8 md9 LK8 Aw8 cri si8 sm8 en k e Xt2).
    { apply (amid_regs fx8 R8 M8 md8 LK8 Aw8 cri si8 sm8 en k e _ fx9 R9 md9 MID); [| exact HH9| exact AM9| exact MRT9].
      intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec 0xb6d18 1 fx9 R9 M8 md9 LK8 Aw8 cri si8 sm8 en k e _ MID9 Y1' ltac:(split; [clear; lia| reflexivity]) Y10' Y11' ltac:(clear; lia)).
    keep_only HD PLT C36 PLE2 EOF C22 C23 C24 KS9.
    intros fx10 R10 M10 md10 LK10 Aw10 RP10 MID.
    assert (B22 : getr R10 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved R9 R10 22 RP10) by inl; rewrite (KS9 22%nat) by inl; exact C22).
    assert (B23 : getr R10 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R9 R10 23 RP10) by inl; rewrite (KS9 23%nat) by inl; exact C23).
    assert (B24 : getr R10 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R9 R10 24 RP10) by inl; rewrite (KS9 24%nat) by inl; exact C24).
    entry_facts. frame_facts. piece_ctx MID.
    pz PEABAP3.abaZt_conc fx10 R10 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx11 & R11 & M11v & MG11 & _ & FRZ11 & MS11 & KS11 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
    apply (finish 0 (r_begin p false X) fx10 R10 M10 md10 LK10 Aw10 cri si8 sm8 en k true _ fx11 R11 M11v 0xb6d18 MID MS11 MG11 FRZ11).
    + intros j Hj. apply KS11. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
    + intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R11 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
    + exact E2.
    + exact FL0.
    + exact MO0.
    + left; reflexivity.
    + reflexivity.
    + rewrite (PECBD.rb_typed_eof2 p false X HD PLT C36 ltac:(clear - PLE2; lia) ltac:(clear - EOF; lia)), PECBD.r_fail_eq. pose proof MID as (_ & _ & CPz & _). pose proof CPz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLz & _).
      unfold Xt2 in CLz. rewrite ?PECBD.w_pos_w_pos in CLz. exact (clink_failp _ _ _ _ _ _ _ CLz).
    + rewrite (PECBD.rb_typed_eof2 p false X HD PLT C36 ltac:(clear - PLE2; lia) ltac:(clear - EOF; lia)), PECBD.r_fail_eq. destruct X; reflexivity.
  - destruct (Z.eq_dec (bat p (s_pos X + 2)) 35) as [C35|N35].
    + rewrite C35 in Z10. apply (sub_T3 ty fx8 R8 M8 md8 LK8 Aw8 cri si8 sm8 HD PLT C36 PLT2 C35 Hty MID Z10 C22 C23 C24 TB SHB REM8).
    +
      pose proof (bat_range p (s_pos X + 2) BOK) as CR. assert (Q0cb : 0 <= bat p (s_pos X + 2) < 2 ^ 64) by (clear - CR; lia).
      assert (PK : exists (fx9 : FPState) R9 M9v, (forall i, 0 <= i < 2 ^ 64 -> M9v (Z_to_bv 64 i) = MVi (Z_to_bv 64 i))
               /\ msteps RSEGS (@mkst fx8 R8 (Z_to_bv 64 0xb6ad8) MVi (seg_rom RSEGS)) (@mkst fx9 R9 (Z_to_bv 64 0xae310) M9v (seg_rom RSEGS))
               /\ (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat -> getr R9 (reg j) = getr R8 (reg j))
               /\ getr R9 (reg 1) = Z_to_bv 64 0xb6d18 /\ getr R9 (reg 10) = Z_to_bv 64 oec /\ getr R9 (reg 11) = Z_to_bv 64 3).
      { destruct (Z_lt_le_dec (bat p (s_pos X + 2)) 35) as [LT|GE].
        - pz PEABAP1.abaT3l_conc fx8 R8 0 (bat p (s_pos X + 2)) 0 0 as PK. L5SAR.feed PK ltac:(first [fcl | clear - CR LT; lia]).
          destruct PK as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1' & Y10' & Y11' & _).
          exists fx9, R9, M9v. split; [exact FRZ9|]. split; [exact MS9|]. split; [intros j Hj; apply KS9; revert j Hj; apply L5K.incl_b; vm_compute; reflexivity|].
          split; [exact Y1'|]. split; [exact Y10'| exact Y11'].
        - pz PEABAP1.abaT3u_conc fx8 R8 0 (bat p (s_pos X + 2)) 0 0 as PK. L5SAR.feed PK ltac:(first [fcl | clear - CR GE N35; lia]).
          destruct PK as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1' & Y10' & Y11' & _).
          exists fx9, R9, M9v. split; [exact FRZ9|]. split; [exact MS9|]. split; [intros j Hj; apply KS9; revert j Hj; apply L5K.incl_b; vm_compute; reflexivity|].
          split; [exact Y1'|]. split; [exact Y10'| exact Y11']. }
      destruct PK as (fx9 & R9 & M9v & FRZ9 & MS9 & KS9 & Y1' & Y10' & Y11').
      assert (E9 : M9v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ9; exact Ha). subst M9v.
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK8 cri Aw8 M8 md8 fx8 fx9 R8 0xb6ad8 R9 0xae310 MVi K HHi AMi MS9 (fun x Hx => Hx) (fun a Ha => eq_refl)).
      intros M9 md9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9.
      assert (E9 : M9 = M8) by (apply L5SAR.mem_eq_of_agree; exact FR9). subst M9.
      assert (MID9 : amid fx9 R9 M8 md9 LK8 Aw8 cri si8 sm8 en k e Xt2).
      { apply (amid_regs fx8 R8 M8 md8 LK8 Aw8 cri si8 sm8 en k e _ fx9 R9 md9 MID); [| exact HH9| exact AM9| exact MRT9].
        intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
      apply (call_mkec 0xb6d18 3 fx9 R9 M8 md9 LK8 Aw8 cri si8 sm8 en k e _ MID9 Y1' ltac:(split; [clear; lia| reflexivity]) Y10' Y11' ltac:(clear; lia)).
      keep_only HD PLT C36 PLT2 N35 C22 C23 KS9.
      intros fx10 R10 M10 md10 LK10 Aw10 RP10 MID.
      assert (B22 : getr R10 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved R9 R10 22 RP10) by inl; rewrite (KS9 22%nat) by inl; exact C22).
      assert (B23 : getr R10 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R9 R10 23 RP10) by inl; rewrite (KS9 23%nat) by inl; exact C23).
      entry_facts. frame_facts. piece_ctx MID.
      pz PEABAP3.abaZt_conc fx10 R10 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
      destruct PZ as (fx11 & R11 & M11v & MG11 & _ & FRZ11 & MS11 & KS11 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
      apply (finish 0 (r_begin p false X) fx10 R10 M10 md10 LK10 Aw10 cri si8 sm8 en k true _ fx11 R11 M11v 0xb6d18 MID MS11 MG11 FRZ11).
      * intros j Hj. apply KS11. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
      * intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R11 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
      * exact E2.
      * exact FL0.
      * exact MO0.
      * left; reflexivity.
      * reflexivity.
      * rewrite (PECBD.rb_typed_bad p false X HD PLT C36 PLT2 N35), PECBD.r_fail_eq. pose proof MID as (_ & _ & CPz & _). pose proof CPz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLz & _).
        unfold Xt2 in CLz. exact (clink_failp _ _ _ _ _ _ _ CLz).
      * rewrite (PECBD.rb_typed_bad p false X HD PLT C36 PLT2 N35), PECBD.r_fail_eq. destruct X; reflexivity.
Qed.

Lemma sub_T fxi Ri Mi mdi LKi Awi cri si smi :
  s_depth X + 1 <= UbjRef.MAX_DEPTH ->
  amid fxi Ri Mi mdi LKi Awi cri si smi en k e (PECBD.X1 X) -> s_pos X < blen p -> bat p (s_pos X) = 36 ->
  getr Ri (reg 10) = Z_to_bv 64 36 -> getr Ri (reg 23) = Z_to_bv 64 (op + 24) -> 1 <= PM.sr_rem (PM.p_src si) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb6a88 Mi mdi) K.
Proof.
  intros HD MID PLT C36 Q10 A23 REM.
  destruct entry_model as (BOK & PPOS & PLH & PBAD & PED & PEOK & MORE & DONE & HALT & DEP & EST & STKLE).
  pose proof (PECBD.X1_fields X) as (F_stk & F_pos & F_more & F_done & F_halt & F_depth & F_ec & F_estk & F_edepth & F_lo & F_hi & F_bad).
  entry_facts. frame_facts. piece_ctx MID.

  pz PEABAP1.abaKd_conc fxi Ri 0 0 0 0 as PK. L5SAR.feed PK fcl.
  destruct PK as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y22 & Y24).
  assert (E3 : M3v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ3; exact Ha). subst M3v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx3 Ri 0xb6a88 R3 0xb4cf4 MVi K HHi AMi MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
  assert (E3 : M3 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
  assert (MID3 : amid fx3 R3 Mi md3 LKi Awi cri si smi en k e (PECBD.X1 X)).
  { apply (amid_regs fxi Ri Mi mdi LKi Awi cri si smi en k e _ fx3 R3 md3 MID); [| exact HH3| exact AM3| exact MRT3].
    intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
  apply (call_ignore 0xb6ab8 fx3 R3 Mi md3 LKi Awi cri si smi en k e (PECBD.X1 X) MID3 ltac:(rewrite F_more; exact MORE) ltac:(rewrite F_done; exact DONE) ltac:(rewrite F_pos; clear - PPOS PLT; lia)
           Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 REM).
  keep_only HD PLT C36 A23 Y22 Y24 KS3 BOK PPOS PLH PBAD PED PEOK MORE DONE HALT DEP EST STKLE F_stk F_pos F_more F_done F_halt F_depth F_ec F_estk F_edepth F_lo F_hi F_bad.
  intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 RP4 _ _ MID.
  rewrite F_pos in MID. set (Xt1 := w_pos (s_pos X + 1) (PECBD.X1 X)) in *. set (si4 := PMSPA.with_src si src4) in *.
  assert (T1F : s_pos Xt1 = s_pos X + 1 /\ s_more Xt1 = true /\ s_done Xt1 = false).
  { unfold Xt1, PECBD.X1. destruct X; cbn in *; repeat split; assumption. }
  destruct T1F as (T_pos & T_more & T_done).
  assert (B22 : getr R4 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved R3 R4 22 RP4) by inl; exact Y22).
  assert (B23 : getr R4 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R3 R4 23 RP4) by inl; rewrite (KS3 23%nat) by inl; exact A23).
  assert (B24 : getr R4 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R3 R4 24 RP4) by inl; exact Y24).
  clear KS3 RP4.

  entry_facts. frame_facts. piece_ctx MID.
  pz PEABAP1.abaT1_conc fx4 R4 0 0 0 0 as PK. L5SAR.feed PK fcl.
  destruct PK as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10 & Z11 & Z12 & SHB5).
  apply (amid_pieceF fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 en k e Xt1 fx5 R5 0xb6ab8 (pa_src_read AD) M5v (fun a => F / 8 + 2147450880 + 4 <= a < F / 8 + 2147450880 + 4 + 1) MID MS5 MG5 FRZ5
           ltac:(intros a Ha; cbv beta in Ha; unfold SB; clear - Ha; lia) ltac:(intros j Hj; apply KS5; revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat); vm_compute; reflexivity)).
  keep_only HD PLT C36 B22 B23 B24 KS5 Z1 Z10 Z11 Z12 SHB5 T_pos T_more T_done BOK PPOS PLH PBAD PED PEOK MORE DONE HALT DEP EST STKLE F_stk F_pos F_more F_done F_halt F_depth F_ec F_estk F_edepth F_lo F_hi F_bad.
  intros M5 md5 VIS5 HID5 MGM5 MID.
  assert (SHB5' : L5.u8_at RSEGS (mrestrict (ahid Aw4 md5) M5) (F / 8 + 2147450880 + 4) 1) by (rewrite HID5, VIS5; replace (F / 8 + 2147450880 + 4) with (F / 8 + 2147450884) by (clear; lia); exact SHB5).

  apply (call_read 0xb6acc fx5 R5 M5 md5 LK4 Aw4 cri si4 sm4 en k e Xt1 MID T_more T_done ltac:(rewrite T_pos; clear - PPOS PLT; lia) Z1 ltac:(split; [clear; lia| reflexivity]) Z10 Z11 Z12 SHB5').
  keep_only HD PLT C36 B22 B23 B24 KS5 T_pos BOK PPOS PLH PBAD PED PEOK MORE DONE HALT DEP EST STKLE F_stk F_pos F_more F_done F_halt F_depth F_ec F_estk F_edepth F_lo F_hi F_bad.
  intros fx6 R6 M6 md6 LK6 Aw6 src6 sm6 d RP6 W10 Hd SHORT LE BYT SHB MID.
  rewrite T_pos in SHORT, LE, BYT, MID. set (si6 := PMSPA.with_src si4 src6) in *.
  assert (A22 : getr R6 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved R5 R6 22 RP6) by inl; rewrite (KS5 22%nat) by inl; exact B22).
  assert (A23' : getr R6 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R5 R6 23 RP6) by inl; rewrite (KS5 23%nat) by inl; exact B23).
  assert (A24 : getr R6 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R5 R6 24 RP6) by inl; rewrite (KS5 24%nat) by inl; exact B24).
  clear KS5 RP6 B22 B23 B24. rename A23' into A23.
  destruct (Z.eq_dec d 0) as [D0|D1].
  -
    rewrite D0 in W10, SHORT, MID. pose proof (SHORT ltac:(clear; lia)) as EOF1.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEABAP1.abaT2z_conc fx6 R6 0 0 0 0 as PK. L5SAR.feed PK ltac:(first [fcl]).
    destruct PK as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1' & Y10' & Y11').
    assert (E7 : M7v = MVi) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). subst M7v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK6 cri Aw6 M6 md6 fx6 fx7 R6 0xb6acc R7 0xae310 MVi K HHi AMi MS7 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M7 md7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7.
    assert (E7 : M7 = M6) by (apply L5SAR.mem_eq_of_agree; exact FR7). subst M7.
    assert (MID7 : amid fx7 R7 M6 md7 LK6 Aw6 cri si6 sm6 en k e (w_pos (s_pos X + 1 + 0) Xt1)).
    { apply (amid_regs fx6 R6 M6 md6 LK6 Aw6 cri si6 sm6 en k e _ fx7 R7 md7 MID); [| exact HH7| exact AM7| exact MRT7].
      intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec 0xb6d18 1 fx7 R7 M6 md7 LK6 Aw6 cri si6 sm6 en k e _ MID7 Y1' ltac:(split; [clear; lia| reflexivity]) Y10' Y11' ltac:(clear; lia)).
    keep_only HD PLT C36 EOF1 A22 A23 A24 KS7.
    intros fx8 R8 M8 md8 LK8 Aw8 RP8 MID.
    assert (B22 : getr R8 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (L5SAR.cs_of_preserved R7 R8 22 RP8) by inl; rewrite (KS7 22%nat) by inl; exact A22).
    assert (B23 : getr R8 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R7 R8 23 RP8) by inl; rewrite (KS7 23%nat) by inl; exact A23).
    assert (B24 : getr R8 (reg 24) = Z_to_bv 64 1) by (rewrite (L5SAR.cs_of_preserved R7 R8 24 RP8) by inl; rewrite (KS7 24%nat) by inl; exact A24).
    entry_facts. frame_facts. piece_ctx MID.
    pz PEABAP3.abaZt_conc fx8 R8 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
    apply (finish 0 (r_begin p false X) fx8 R8 M8 md8 LK8 Aw8 cri si6 sm6 en k true _ fx9 R9 M9v 0xb6d18 MID MS9 MG9 FRZ9).
    + intros j Hj. apply KS9. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
    + intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R9 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
    + exact E2.
    + exact FL0.
    + exact MO0.
    + left; reflexivity.
    + reflexivity.
    + rewrite (PECBD.rb_typed_eof1 p false X HD PLT C36 ltac:(clear - EOF1; lia)), PECBD.r_fail_eq. pose proof MID as (_ & _ & CPz & _). pose proof CPz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLz & _).
      unfold Xt1 in CLz. rewrite ?PECBD.w_pos_w_pos in CLz. exact (clink_failp _ _ _ _ _ _ _ CLz).
    + rewrite (PECBD.rb_typed_eof1 p false X HD PLT C36 ltac:(clear - EOF1; lia)), PECBD.r_fail_eq. destruct X; reflexivity.
  -
    assert (D1' : d = 1) by (clear - Hd D1; lia). rewrite D1' in W10, LE, BYT, MID.
    rewrite (PECBD.slice_pos_1 p (s_pos X + 1)) in BYT by (clear - PPOS LE; lia).
    pose proof (BYT 0%nat ltac:(cbn; lia)) as TB. cbn [nth] in TB. rewrite Z.add_0_r in TB.
    unfold Xt1 in MID. rewrite PECBD.w_pos_w_pos in MID. replace (s_pos X + 1 + 1) with (s_pos X + 2) in MID by (clear; lia).
    apply (sub_T2 (bat p (s_pos X + 1)) fx6 R6 M6 md6 LK6 Aw6 cri si6 sm6 HD PLT C36 ltac:(clear - LE; lia) eq_refl MID W10 A22 A23 A24 TB SHB).
Qed.

Lemma clink_X1 s0 sm0 en0 k0 : PEC.clink p X s0 sm0 en0 k0 ->
  PEC.clink p (PECBD.X1 X) (PM.PST (PM.p_more s0) (PM.p_done s0) (PM.p_depth s0 + 1) (PM.p_src s0) (PM.p_tb s0) (PM.p_tg s0) (PM.p_b s0) (PM.p_k s0) (PM.p_stk s0)) sm0 en0 k0.
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  unfold PEC.clink, PECBD.X1. destruct X; cbn in *.
  split; [exact L1|]. split; [exact L2|]. split; [rewrite L3; reflexivity|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
Qed.

Lemma frame_body (fx1 : FPState) R1 M1 model1 R2 :
  getr R1 (reg 2) = Z_to_bv 64 (sp - 128) -> getr R1 (reg 8) = Z_to_bv 64 sp -> getr R1 (reg 9) = Z_to_bv 64 (sp - 128) ->
  getr R1 (reg 19) = Z_to_bv 64 op -> getr R1 (reg 20) = Z_to_bv 64 oec -> getr R1 (reg 21) = Z_to_bv 64 ov -> getr R1 (reg 27) = Z_to_bv 64 2147450880 ->
  (forall j, In j [3; 4]%nat -> getr R1 (reg j) = getr R (reg j)) ->
  own sp R M1 -> model_rt model model1 ->
  L5SAR.ek L ar (PEC.owned s en k ++ LBX) FF sp 26624 [] M M1 -> L5SAR.dk L ar (PEC.owned s en k ++ LBX) FF sp 26624 M M1 ->
  getr R2 10%bv = Z_to_bv 64 F -> regs_preserved R1 R2 -> L5CA.amodel_ok Aw model2 -> model_rt model1 model2 ->
  L5CA.astk ar M2 sp 26624 -> L5SAR.ek L ar LBX FF sp 26624 [] M M2 -> L5SAR.dk L ar LBX FF sp 26624 M M2 ->
  L5SAR.ek L ar (PEC.owned s en k ++ LBX) FF sp 26624 [] M1 M2 -> L5SAR.dk L ar (PEC.owned s en k ++ LBX) FF sp 26624 M1 M2 ->
  (forall a, sp - 128 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  L5.writable RSEGS (mrestrict (ahid Aw model2) M2) F 64 ->
  L5.writable RSEGS (mrestrict (ahid Aw model2) M2) (F / 8 + SB) 8 ->
  L5KA.zeros_at (mrestrict (ahid Aw model2) M2) (F / 8 + SB) 8 ->
  L5.u64_at RSEGS (mrestrict (ahid Aw model2) M2) (F + 64 - 8) fl -> L5.writable RSEGS (mrestrict (ahid Aw model2) M2) fl 1 ->
  L5.defined (mrestrict (ahid Aw model2) M2) F 64 ->
  L5A.avis (ahid Aw model2) F 64 -> L5A.avis (ahid Aw model2) (F / 8 + SB) 8 -> L5A.avis (ahid Aw model2) fl 1 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx1) RSEGS R2 0xb69b4 M2 model2) K.
Proof.
  intros T2 T8 T9 T19 T20 T21 T27 K34 OWN1 MRT1 EK01f DK01f G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL.
  entry_facts. frame_facts.
  destruct entry_model as (BOK & PPOS & PLH & PBAD & PED & PEOK & MORE & DONE & HALT & DEP & EST & STKLE).
  pose proof (PECBD.X1_fields X) as (F_stk & F_pos & F_more & F_done & F_halt & F_depth & F_ec & F_estk & F_edepth & F_lo & F_hi & F_bad).
  pose proof CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  pose proof (L5SAR.ek_trans L ar LB FF sp 26624 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 26624 M M1 M2 DK01f DK12f) as DK02f.
  assert (HH2 : ri_inv HI LB FF' LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 26624 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 26624 a HH SPT Hc) as [Y'|Y']; [clear - Xa Y'; lia| clear - Xa Y' SLO; lia]. }
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j))
    by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B19R : getr R2 (reg 19) = Z_to_bv 64 op) by (rewrite (R2c 19%nat) by inl; exact T19).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 oec) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (B21R : getr R2 (reg 21) = Z_to_bv 64 ov) by (rewrite (R2c 21%nat) by inl; exact T21).
  assert (B27R : getr R2 (reg 27) = Z_to_bv 64 2147450880) by (rewrite (R2c 27%nat) by inl; exact T27).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).

  assert (OWN2 : own sp R M2) by (apply (own_agree sp R M1 M2 ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia) OWN1); intros a Ha; unfold ocell in Ha; apply AGF; clear - Ha; lia).
  assert (BI2 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned s en k) M2 model2 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH2|]. split; [exact AM2|]. split; [eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact ASTK2|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 26624 WR [] M M2 EK02); intros a _ r0 []|]. split; [exact DK02|]. split; [exact OWN2|].
    change (ff_bytes 0 / 8) with 8. apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 8 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (CP2 : PECA.crun_preA RSEGS AD AAD EE L ar P M2 fb p X s str sm en k e cat).
  { apply (cpre_keepA LB sp 26624 [] M M2 X s sm en k e EK02f PMKA.wapp_nil BRB); [unfold LB; apply incl_appl; apply incl_refl| unfold LB; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CPRE]. }
  pose proof CP2 as (PA2 & IA2 & EA2 & VREF2 & SKA2 & BASE2 & ERR2 & TBOK2 & CONT2 & CL2 & ECS2 & ECI2 & ACC2).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 128 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 fb _ s HH2 FOK' PA2) as (_ & _ & _ & _ & _ & _ & OVIS2 & _ & _). fold H2 in OVIS2.
  pose proof CL as (_ & _ & Ldepth & _). pose proof PA2 as (_ & _ & _ & _ & _ & PD12 & _). rewrite Ldepth in PD12.
  assert (D12v : L5.u32_at RSEGS MV2 (op + 12) (s_depth X)).
  { apply (proj2 (L5A.u32_at_vis H2 M2 (op + 12) (s_depth X) (OVIS2 (op + 12) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). exact PD12. }
  assert (Q0dp : 0 <= s_depth X < 2 ^ 64) by (clear - DEP; unfold UbjRef.MAX_DEPTH in DEP; lia).
  assert (ZF8 : L5KA.zeros_at MV2 (F / 8 + 2147450880) 8) by (unfold SB in FSHZ; exact FSHZ).
  pose proof (pfacts_bc M2 model2 LK2 cr Aw s sm en k e X BI2 CP2) as VF0. cbv zeta in VF0. fold H2 in VF0. fold MV2 in VF0. open_vf VF0.

  assert (PK : exists (fx3 : FPState) R3 M3v, mem_grows MV2 M3v
     /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 128 <= i < sp - 128 + 8) -> ~ (F + 0 <= i < F + 0 + 24) -> ~ (F / 8 + 2147450880 + 0 <= i < F / 8 + 2147450880 + 0 + 8) -> ~ (op + 12 <= i < op + 12 + 4) -> M3v (Z_to_bv 64 i) = MV2 (Z_to_bv 64 i))
     /\ ((s_depth X <= 1023 /\ msteps RSEGS (@mkst fx1 R2 (Z_to_bv 64 0xb69b4) MV2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0xb4bd0) M3v (seg_rom RSEGS))
             /\ getr R3 (reg 1) = Z_to_bv 64 0xb6a88 /\ getr R3 (reg 10) = Z_to_bv 64 (op + 24) /\ getr R3 (reg 23) = Z_to_bv 64 (op + 24))
         \/ (s_depth X = 1024 /\ msteps RSEGS (@mkst fx1 R2 (Z_to_bv 64 0xb69b4) MV2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0xae310) M3v (seg_rom RSEGS))
             /\ getr R3 (reg 1) = Z_to_bv 64 0xb6e80 /\ getr R3 (reg 10) = Z_to_bv 64 oec /\ getr R3 (reg 11) = Z_to_bv 64 11))
     /\ (forall j, In j [2; 3; 4; 8; 9; 19; 20; 21; 27]%nat -> getr R3 (reg j) = getr R2 (reg j))
     /\ getr R3 (reg 18) = Z_to_bv 64 F /\ getr R3 (reg 25) = Z_to_bv 64 F /\ getr R3 (reg 26) = Z_to_bv 64 (F / 8 + 2147450880)
     /\ L5.u32_at RSEGS M3v (op + 12) (s_depth X + 1)).
  { destruct (Z_lt_le_dec (s_depth X) 1024) as [LT|GE].
    - assert (DLE : 0 <= s_depth X <= 1023) by (clear - LT DEP; lia).
      pz PEABAP1.abaB0_conc fx1 R2 (s_depth X) 0 0 0 as PB. L5SAR.feed PB fcl.
      destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y13 & Y14 & Y18 & Y23 & Y25 & Y26 & C12 & _).
      exists fx3, R3, M3v. split; [exact MG3|]. split; [exact FRZ3|]. split; [left; split; [clear - LT; lia| split; [exact MS3| split; [exact Y1| split; [exact Y10| exact Y23]]]]|].
      split; [intros j Hj; apply KS3; revert j Hj; apply L5K.incl_b; vm_compute; reflexivity|]. split; [exact Y18|]. split; [exact Y25|]. split; [exact Y26| exact C12].
    - assert (D1024 : s_depth X = 1024) by (clear - GE DEP; unfold UbjRef.MAX_DEPTH in DEP; lia). rewrite D1024 in D12v.
      pz PEABAP1.abaB1_conc fx1 R2 0 0 0 0 as PB. L5SAR.feed PB fcl.
      destruct PB as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y13 & Y14 & Y18 & Y25 & Y26 & C12 & _).
      exists fx3, R3, M3v. split; [exact MG3|]. split; [exact FRZ3|]. split; [right; split; [exact D1024| split; [exact MS3| split; [exact Y1| split; [exact Y10| exact Y11]]]]|].
      split; [intros j Hj; apply KS3; revert j Hj; apply L5K.incl_b; vm_compute; reflexivity|]. split; [exact Y18|]. split; [exact Y25|]. split; [exact Y26| rewrite D1024; exact C12]. }
  clear VF1 VF2 VF3 VF4 VF5 VF6 VF7 VF8 VF9 VF10 VF11 VF12 VF13 VF14 VF15 VF16 VF17 VF18 VF19 VF20 VF21 VF22 VF23 VF24 VF25 VF26 VF27 VF28 VF29 VF30 VF31 VF32 VF33 VF34 VF35 VF36 VF37 VF38 VF39 VF40 VF41 VF42 VF43 VF44 VF45 VF46 VF47 VF48 VF49 VF50 VF51 VF52 VF53 VF54 VF55 VF56 VF57 VF58 VF59 VF60 VF61 VF62 VF63 VF64 VF65 VF66 VF67 VF68 VF69 VF70 VF71 VF72 VF73 VF74 VF75 VF76 VF77 VF78 VF79 VF80 VF81 VF82 VF83 VF84 VF85 VF86 VF87 VF88 VF89 VF90.
  destruct PK as (fx3 & R3 & M3v & MG3 & FRZ3 & ALT3 & KS3 & Y18 & Y25 & Y26 & C12).
  assert (MS3 : exists pc3, msteps RSEGS (@mkst fx1 R2 (Z_to_bv 64 0xb69b4) MV2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 pc3) M3v (seg_rom RSEGS))
                 /\ ((s_depth X <= 1023 /\ pc3 = 0xb4bd0 /\ getr R3 (reg 1) = Z_to_bv 64 0xb6a88 /\ getr R3 (reg 10) = Z_to_bv 64 (op + 24) /\ getr R3 (reg 23) = Z_to_bv 64 (op + 24))
                     \/ (s_depth X = 1024 /\ pc3 = 0xae310 /\ getr R3 (reg 1) = Z_to_bv 64 0xb6e80 /\ getr R3 (reg 10) = Z_to_bv 64 oec /\ getr R3 (reg 11) = Z_to_bv 64 11))).
  { destruct ALT3 as [(D & MS & Y1 & Y10 & Y23)|(D & MS & Y1 & Y10 & Y11)]; [exists 0xb4bd0; split; [exact MS| left; repeat split; assumption]| exists 0xae310; split; [exact MS| right; repeat split; assumption]]. }
  clear ALT3. destruct MS3 as (pc3 & MS3 & ALT3).
  set (W3 := fun a => (sp - 128 <= a < sp - 128 + 8) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8) \/ (op + 12 <= a < op + 12 + 4)).
  pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). assert (D2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb69b4 R3 pc3 M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; clear - X'; lia| intros X'; apply Hn; right; left; clear - X'; lia| intros X'; apply Hn; right; right; left; clear - X'; lia| intros X'; apply Hn; right; right; right; clear - X'; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|[X'|X']]].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SLO SHI SPT; lia| intros Y'; clear - Y'; lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X'; lia.
      + unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. clear - X' Eop; lia.
    - destruct Wa as [X'|[X'|[X'|X']]]; [clear - X' SLO SPT; lia| clear - X' GFR; lia| clear - X' D1; lia| clear - X' O1; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23 : L5SAR.ek L ar LB FF sp 26624 [(op + 12, 4)] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 26624 [(op + 12, 4)] M2 M3 W3 FR3). intros a Ha Hc Ho X'. destruct X' as [X'|[X'|[X'|X']]].
    - apply (NCS0 a); [clear - X'; lia| exact Hc].
    - destruct (APART a 1 sp 26624 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y' & _). change (ff_bytes 0) with 64 in Y'. clear - X' Y'; lia.
    - destruct (APART a 1 sp 26624 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y' & _). change (ff_bytes 0 / 8) with 8 in Y'. unfold SB in Y'. clear - X' Y'; lia.
    - apply (Ho (op + 12, 4)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X'; lia]. }
  assert (WAPP12 : PMKA.wapp [(op + 12, 4)]).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG; lia. }
  assert (OUT12 : forall a n, (a + n <= op + 12 \/ op + 16 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 12, 4)] i).
  { intros a n X3 i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi' Hr X3. lia. }
  assert (OUTB12 : forall q' m, In (q', m) LB -> forall i, q' <= i < q' + m -> L5.outside [(op + 12, 4)] i).
  { intros q' m Hq i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HH Hq AOP) as [Z'|Z']; clear - Hi' Hr Z'; lia. }
  assert (OWN3 : own sp R M3).
  { apply (own_agree sp R M2 M3 ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia) OWN2). intros a Ha. unfold ocell in Ha.
    apply FR3; [clear - Ha SLO SHI SPT; lia|]. intros [X'|[X'|[X'|X']]]; [clear - X' Ha; lia| clear - X' Ha GFCEIL GSLO; lia| clear - X' Ha D1 D2 SLO SPT; lia| clear - X' Ha Eop F2 FSCEIL GSLO; lia]. }
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PEC.owned s en k) M3 model3 LK2 cr Aw).
  { apply (PMAUK.binv_pieceW L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR (PEC.owned s en k) M2 model2 LK2 cr Aw M3 model3 W3 BI2 HH3 AM3 MRT3 MGM3 FR3).
    intros a Wa. split.
    - unfold ocell. destruct Wa as [X'|[X'|[X'|X']]]; [clear - X'; lia| clear - X' GFCEIL GSLO; lia| clear - X' D1 D2 SLO SPT; lia| clear - X' Eop F2 FSCEIL GSLO; lia].
    - destruct Wa as [X'|[X'|[X'|X']]]; [left; clear - X'; lia| right; left; change (ff_bytes 0) with 64; clear - X'; lia| right; right; left; change (ff_bytes 0 / 8) with 8; exact X'|].
      right; right; right. intros O. apply (O (PMSP.o_p AD fb + 8, 8)); [unfold WR; wr_mem 0| wr_rng; clear - X' Eop; lia]. }
  set (s3 := PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s + 1) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s)).
  assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB) by (unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (Ib : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LB) by (unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  destruct (BRB _ Iq) as (Xq1 & Xq2). destruct (BRB _ Ib) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2. unfold PM.CHUNK in Xq2.
  assert (C12m : L5.u32_at RSEGS M3 (op + 12) (s_depth X + 1)).
  { apply (proj1 (L5A.u32_at_vis H2 M3 (op + 12) (s_depth X + 1) (OVIS2 (op + 12) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). rewrite VIS3. exact C12. }
  assert (CP3 : PECA.crun_preA RSEGS AD AAD EE L ar P M3 fb p (PECBD.X1 X) s3 str sm en k e cat).
  { apply (cpre_stepA LB sp 26624 [(op + 12, 4)] M2 M3 X s sm en k e (PECBD.X1 X) s3 e EK23 WAPP12 BRB).
    - unfold LB. apply incl_appl. apply incl_refl.
    - unfold LB. apply incl_appr. exact INCS.
    - intros i Hi' Ni _. apply (OUT12 i 1); clear - Hi' Ni; lia.
    - intros q' m Hq. exact (OUTB12 q' m Hq).
    - reflexivity. - reflexivity. - reflexivity.
    - unfold s3. rewrite Ldepth. apply (PECFA.parser_depth_updA RSEGS AD M2 M3 op ois s (s_depth X + 1) PA2).
      + clear - O1; lia.
      + clear - O1 O3; lia.
      + apply (PMKA.agA_obj L ar _ FF sp 26624 _ M2 M3 EK23 WAPP12 FRB op 12 (AOF op 12 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT12. clear; lia.
      + apply (PMKA.agA_obj L ar _ FF sp 26624 _ M2 M3 EK23 WAPP12 FRB (op + 16) 368 (AOF (op + 16) 368 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT12. clear; lia.
      + exact (PMKA.agsh_obj L ar _ FF sp 26624 _ M2 M3 EK23 WAPP12 FRB op 384 AOP).
      + pose proof PA2 as (_ & PDi & _). apply (L5.defined_grows M2 M3 _ _ MGM3 PDi).
      + exact C12m.
      + clear - DEP; unfold UbjRef.MAX_DEPTH in DEP; unfold PM.MAX_DEPTH; lia.
      + exact Xq1.
      + unfold PM.CHUNK. clear - Xq2; lia.
      + apply (PMKA.agA_blk L ar _ FF sp 26624 _ M2 M3 EK23 WAPP12 BRB _ _ Iq). apply OUTB12. exact Iq.
      + exact Xb1.
      + clear - Xb2; lia.
      + apply (PMKA.agA_blk L ar _ FF sp 26624 _ M2 M3 EK23 WAPP12 BRB _ _ Ib). apply OUTB12. exact Ib.
      + intros c0 n0 p0 E0. assert (Ip : In (p0, c0) LB) by (unfold LB, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
        apply (PMKA.agA_blk L ar _ FF sp 26624 _ M2 M3 EK23 WAPP12 BRB _ _ Ip). apply OUTB12. exact Ip.
    - change (PMSTA.base_okA RSEGS PMA.AD M3). apply (PMASK.base_keep L ar C LY LB FF sp 26624 [(op + 12, 4)] M2 M3 EK23); [| exact BASE2]. intros a Ha. apply (OUT12 a 1); clear - Ha O1; lia.
    - apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LB FF sp 26624 [(op + 12, 4)] M2 M3 EK23 e PECSA.addrs_wf_A); [| exact ERR2].
      intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
      split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply (OUT12 a 1); clear - DI O1; lia.
    - unfold s3. exact (clink_X1 _ _ _ _ CL).
    - destruct (PECBD.X1_fields X) as (_ & _ & _ & _ & _ & _ & EX1 & _). rewrite EX1.
      apply (PECFA.ec_state_keepA RSEGS AD L ar LB FF sp 26624 [(op + 12, 4)] M2 M3 EK23 WAPP12 FRB fb (s_ec X) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS2].
      fold oec. apply OUT12. clear - Eop Eoec; lia.
    - destruct (PECBD.X1_fields X) as (_ & _ & _ & _ & _ & _ & EX1 & _). rewrite EX1. exact ECI.
    - exact CP2. }
  assert (AMID3 : amid fx3 R3 M3 model3 LK2 Aw cr s3 sm en k e (PECBD.X1 X)).
  { unfold amid. split; [| split; [exact BI3| split; [exact CP3| split; [| split; [intros X'; exact X'| unfold PMSP.credit_keep, PECA.pot_allA, PEC.credit_add, PM.pot_parser, s3; cbn [PM.p_k PM.p_tb PM.p_tg fst snd]; clear; lia]]]]].
    - split; [rewrite (KS3 2%nat) by inl; exact B2R|]. split; [rewrite (KS3 8%nat) by inl; exact B8R|]. split; [rewrite (KS3 9%nat) by inl; exact B9R|].
      split; [exact Y18|]. split; [rewrite (KS3 19%nat) by inl; exact B19R|]. split; [rewrite (KS3 20%nat) by inl; exact B20R|].
      split; [rewrite (KS3 21%nat) by inl; exact B21R|]. split; [exact Y25|]. split; [exact Y26|]. split; [rewrite (KS3 27%nat) by inl; exact B27R|].
      intros j Hj. rewrite (KS3 j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity).
      rewrite (R2c j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply K34. exact Hj.
    - unfold s3, PMSPA.src_step. cbn [PM.p_src]. split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|]. split; [intros X'; exact X'| clear; lia]. }
  clear FR3 FRZ3 OWN3 OWN2 OWN1 EK23 C12 C12m CP3 BI3 BI2 CP2.
  assert (HD1 : s_depth X <= 1023 -> s_depth X + 1 <= UbjRef.MAX_DEPTH) by (unfold UbjRef.MAX_DEPTH; clear; lia).
  destruct ALT3 as [(DLE & -> & Y1 & Y10 & Y23)|(D1024 & -> & Y1 & Y10 & Y11)].
  -
    apply (call_peek 0xb6a88 fx3 R3 M3 model3 LK2 Aw cr s3 sm en k e (PECBD.X1 X) AMID3 ltac:(rewrite F_more; exact MORE) ltac:(rewrite F_done; exact DONE) ltac:(rewrite F_pos; exact PPOS)
             Y1 ltac:(split; [clear; lia| reflexivity]) Y10).
    keep_only HD1 DLE Y23 KS3 F_pos. intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 RP4 ALT _ _ MID.
    assert (A23 : getr R4 (reg 23) = Z_to_bv 64 (op + 24)) by (rewrite (L5SAR.cs_of_preserved R3 R4 23 RP4) by inl; exact Y23).
    rewrite F_pos in ALT. pose proof (HD1 DLE) as HD.
    destruct ALT as [(Q10 & EOF)|(PLT & Q10 & REM)].
    + exact (sub_eof fx4 R4 M4 md4 LK4 Aw4 cr _ sm4 en k e HD MID ltac:(rewrite EOF; clear; lia) Q10 A23).
    + destruct (Z.eq_dec (bat p (s_pos X)) 36) as [C36|N36]; [rewrite C36 in Q10; exact (sub_T fx4 R4 M4 md4 LK4 Aw4 cr _ sm4 HD MID PLT C36 Q10 A23 REM)|].
      destruct (Z.eq_dec (bat p (s_pos X)) 35) as [C35|N35]; [rewrite C35 in Q10; exact (sub_C fx4 R4 M4 md4 LK4 Aw4 cr _ sm4 HD MID PLT C35 Q10 A23 REM)|].
      exact (sub_I fx4 R4 M4 md4 LK4 Aw4 cr _ sm4 (bat p (s_pos X)) HD MID PLT eq_refl N36 N35 Q10 A23).
  -
    rename AMID3 into MID.
    apply (call_mkec 0xb6e80 11 fx3 R3 M3 model3 LK2 Aw cr s3 sm en k e _ MID Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
    keep_only D1024 KS3 R2c. intros fx4 R4 M4 md4 LK4 Aw4 RP4 MID.
    entry_facts. frame_facts. piece_ctx MID.
    pz PEABAP3.abaZ11_conc fx4 R4 0 0 0 0 as PZ. L5SAR.feed PZ fcl.
    destruct PZ as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
    apply (finish 0 (r_begin p false X) fx4 R4 M4 md4 LK4 Aw4 cr s3 sm en k true _ fx7 R7 M7v 0xb6e80 MID MS7 MG7 FRZ7).
    + intros j Hj. apply KS7. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
    + intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R7 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
    + exact E2.
    + exact FL0.
    + exact MO0.
    + left; reflexivity.
    + reflexivity.
    + rewrite (PECBD.rb_depth p false X ltac:(rewrite D1024; unfold UbjRef.MAX_DEPTH; clear; lia)), PECBD.r_fail_eq. pose proof MID as (_ & _ & CPz & _). pose proof CPz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CLz & _). exact (clink_fail _ _ _ _ _ CLz).
    + rewrite (PECBD.rb_depth p false X ltac:(rewrite D1024; unfold UbjRef.MAX_DEPTH; clear; lia)), PECBD.r_fail_eq. destruct X; reflexivity.
Qed.
End Frame.

Theorem begin_array_call : srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx) RSEGS R (pa_begin_array AD) M model) K.
Proof.
  entry_facts.
  pose proof AM as (Mh & MI).
  pose proof A10 as X10. pose proof A11 as X11. pose proof A12 as X12. rewrite L5K.rl10 in X10. rewrite L5K.rl11 in X11. rewrite L5K.rl12 in X12. fold op in X10. fold ov in X11. fold oec in X12.
  pose proof CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (BASE' : PMSTA.base_okA RSEGS PMA.AD M) by exact BASE.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE') as (IC0 & CSBv & CUARv). fold H in IC0, CSBv, CUARv. fold MV in IC0, CSBv, CUARv.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 26624 160 HH ASTK ltac:(clear; lia)) as (SL160 & SH160 & WS160). fold H in WS160. fold MV in WS160.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & _).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK cr Aw M model fb _ s HH FOK PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold H in Zop, Z32, Z20, OWR, OVIS. fold MV in Zop, Z32, Z20, OWR. fold op in Zop, Z32, Z20, OWR, OVIS.
  assert (ECX : exists v c, PMSPA.ec_at RSEGS M oec v c).
  { pose proof ECS as E0. unfold PECA.ec_stateA in E0. fold oec in E0.
    lazymatch type of E0 with (if ?c then _ else _) => destruct c; [destruct E0 as (v0 & _ & E1); exists v0; eexists; exact E1| exists 0, cat; exact E0] end. }
  destruct ECX as (ecv & ecc & ECat).
  pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK cr Aw M model fb ecv ecc HH FOK ECat) as ((_ & _ & _) & ZE & EW & _ & EU & _ & _). fold H in ZE, EW, EU. fold MV in ZE, EW, EU. fold oec in ZE, EW, EU.
  pose proof EA as (EVT & _ & _ & _ & _ & _ & _ & _ & EACC & _).
  pose proof (PMAPAR.ov_vis L ar C HI LY HIok _ _ LK cr Aw M model fb HH FOK (conj EVT (PMABK.aacc_sub M ov 56 ov 8 EACC ltac:(clear; lia) ltac:(clear; lia))))
    as ((V1 & V8 & VBIG) & ZV & VW & V3 & VVT & _ & _). fold H in ZV, VW, VVT. fold MV in ZV, VW, VVT. fold ov in V1, V8, VBIG, ZV, VW, V3, VVT.
  assert (Q0a : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia). assert (Q0b : 0 <= op < 2 ^ 64) by (clear - O1 O3; lia).
  assert (Q0c : 0 <= ov < 2 ^ 64) by (clear - V1; lia). assert (Q0d : 0 <= oec < 2 ^ 64) by (clear - E1' E3'; lia).

  pose proof (PEABAP1.abaA_conc fx R MV (VAL 0 0 0 0 0 0)) as PP. unfold VAL in PP. cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [sya | unfold PEABAP1.aligned; sya | clear - SL160 SHI SPT; lia | clear - O2 SLO; lia | clear - E2' SLO; lia | clear - V3 SLO; lia
                             | clear - Eop Eoec Eov; lia | clear - O8; lia | clear - C8m; lia | clear - Q8; lia | clear - OBIG; lia | clear - EBIG; lia | clear - VBIG; lia
                             | clear - O1 O3; lia | clear - E1' E3'; lia | clear - V1 V3; lia | clear - O1; lia | clear - E1'; lia | clear - V1; lia]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T19 & T20 & T21 & T27
                 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C128).
  unfold PMSPA.cfg. cbn [pa_begin_array AD PeCLayoutA.CADDR_A].
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb693c R1 0x5e414 M1v (fun a => sp - 128 <= a < sp - 128 + 128) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X'; clear - X' Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL160 SHI SPT; lia| intros X'; clear - X'; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 26624 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 26624 a HH SPT Hc) as [Y'|Y']; [clear - Xa Y'; lia| clear - Xa Y' SL160; lia]. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 26624 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 26624 [] M M1 (fun a => sp - 128 <= a < sp - 128 + 128) FR1). intros a Ha Hc _ X'. apply (NCS0 a); [clear - X'; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 26624 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBX FF sp 26624 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBX FF sp 26624 M M1 INCX DK01f) as DK01.
  assert (SV1 : forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X'. apply (proj1 (L5A.u64_at_vis H M1 a v (VIS a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X'. }
  assert (OWN1 : own sp R M1).
  { unfold own. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
  clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C128 SV1.

  assert (FRk0 : ff_room 0 FF LK) by (pose proof (FRM 0 ltac:(left; reflexivity)) as X'; unfold ff_room; clear - X'; lia).
  change 0x5e414 with (PMA.SM_PC 0).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 0 LBX (PEC.owned s en k) FF LK cr Aw sp 26624 (sp - 128) (sp - 104) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xb69b4 ltac:(left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk0. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 0) with 64 in FW, FSHW, FSHZ, FLC, FLW, FDEF, VF, VSH, APART. change (64 / 8) with 8 in FSHW, FSHZ, VSH, APART.
  fold LB in EK12f, DK12f, APART.
  apply (frame_body F fl LK2 M2 model2 G APART fx1 R1 M1 model1 R2 T2 T8 T9 T19 T20 T21 T27 ltac:(intros j Hj; apply KS1; revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity)
           OWN1 MRT1 EK01f DK01f G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL).
Qed.
End Call.

Theorem begin_array_ok : PECSA.begin_array_spec L ar HI P.
Proof.
  unfold PECSA.begin_array_spec, PECSPA.begin_array_spec, PECSPA.crun_spec.
  intros PMODE [] fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 ARGS CPRE INCS POK MP NB HB CRED KONT.
  destruct ARGS as (A10 & A11 & A12).
  exact (begin_array_call PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 A11 A12 CPRE INCS POK MP NB HB CRED KONT).
Qed.
End WithHeap.
End PEACBA.
