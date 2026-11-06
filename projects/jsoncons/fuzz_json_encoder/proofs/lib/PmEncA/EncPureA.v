(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA EncKitA EncBridgesA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Module EPA.
Import PMES.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
Definition lits_inside (IC : PMLA.consts) : Prop :=
  let lo := PMLA.LIT_LO IC in let hi := PMLA.LIT_HI IC in
  lo <= PMLA.LIT_NULL_S IC /\ PMLA.LIT_NULL_S IC + 16 <= hi /\ lo <= PMLA.LIT_NULL_G IC /\ PMLA.LIT_NULL_G IC + 2 <= hi /\
  lo <= PMLA.LIT_TRUE_S IC /\ PMLA.LIT_TRUE_S IC + 16 <= hi /\ lo <= PMLA.LIT_TRUE_G IC /\ PMLA.LIT_TRUE_G IC + 2 <= hi /\
  lo <= PMLA.LIT_FALSE_S IC /\ PMLA.LIT_FALSE_S IC + 16 <= hi /\ lo <= PMLA.LIT_FALSE_G IC /\ PMLA.LIT_FALSE_G IC + 2 <= hi /\ 0 <= lo /\ hi <= 2 ^ 64.
Lemma lits_inside_xasan : lits_inside PMLA.C_xasan.
Proof. unfold lits_inside, PMLA.LIT_LO, PMLA.LIT_HI. cbn. repeat split; lia. Qed.
Lemma lits_inside_xboth : lits_inside PMLA.C_xboth.
Proof. unfold lits_inside, PMLA.LIT_LO, PMLA.LIT_HI. cbn. repeat split; lia. Qed.

Lemma lit_ok_agree : forall segs (M M' : mem) S G txt len, 0 <= S -> S + 16 <= 2 ^ 64 -> 0 <= G -> G + 2 <= 2 ^ 64 ->
  (forall i, 0 <= i < 16 -> M' (Z_to_bv 64 (S + i)) = M (Z_to_bv 64 (S + i))) -> (forall i, 0 <= i < 2 -> M' (Z_to_bv 64 (G + i)) = M (Z_to_bv 64 (G + i))) ->
  PMLA.lit_ok segs M S G txt len -> PMLA.lit_ok segs M' S G txt len.
Proof.
  intros segs M M' S G txt len HS HS2 HG HG2 AS AG H. unfold PMLA.lit_ok, PMLA.u8, PMLA.u64 in *.
  assert (X8 : forall a v, 0 <= a - G < 2 -> L5.u8_at segs M a v -> L5.u8_at segs M' a v).
  { intros a v Ha Hu. apply (CL5A.u8_same segs M M' a); [lia | lia | | exact Hu]. replace a with (G + (a - G)) by lia. apply AG. lia. }
  assert (X64 : forall a v, 0 <= a - S /\ a - S + 8 <= 16 -> L5.u64_at segs M a v -> L5.u64_at segs M' a v).
  { intros a v Ha Hu. apply (CL5A.u64_same segs M M' a); [lia | lia | | exact Hu]. intros y Hy. replace y with (S + (y - S)) by lia. apply AS. lia. }
  destruct H as [(H1 & H2 & H3 & H4)|(H1 & H2 & H3 & H4)]; [left | right]; repeat split;
    first [apply X8; [lia | assumption] | apply X64; [lia | assumption] | replace (G + 1) with (G + 1) by lia; apply X8; [lia | assumption]].
Qed.
Lemma lits_ok_agree : forall segs IC (M M' : mem), lits_inside IC ->
  (forall a, PMLA.LIT_LO IC <= a < PMLA.LIT_HI IC -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PMLA.lits_ok segs IC M -> PMLA.lits_ok segs IC M'.
Proof.
  intros segs IC M M' HI AG (H1 & H2 & H3). unfold lits_inside in HI. cbv zeta in HI.
  destruct HI as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  split; [|split]; (eapply lit_ok_agree; [| | | | | |eassumption]); try (intros i Hi; apply AG; lia); lia.
Qed.
(* [comment removed for export] *)
Lemma lit_done_agree : forall L (M M' : mem) S G txt n, 0 <= S -> S + 16 <= 2 ^ 64 -> 0 <= G -> G + 2 <= 2 ^ 64 ->
  (forall i, 0 <= i < 16 -> M' (Z_to_bv 64 (S + i)) = M (Z_to_bv 64 (S + i))) -> (forall i, 0 <= i < 2 -> M' (Z_to_bv 64 (G + i)) = M (Z_to_bv 64 (G + i))) ->
  PMESA.lit_done L M S G txt n -> PMESA.lit_done L M' S G txt n.
Proof.
  intros L M M' S G txt n HS HS2 HG HG2 AS AG (H1 & H2 & H3 & H4). unfold PMESA.lit_done, PMSA.u8, PMSA.u64 in *.
  split; [apply (CL5A.u8_same _ M M' G); [lia | lia | replace G with (G + 0) by lia; apply AG; lia | exact H1]|].
  split; [apply (CL5A.u8_same _ M M' (G + 1)); [lia | lia | apply AG; lia | exact H2]|].
  split; [apply (CL5A.u64_same _ M M' S); [lia | lia | intros y Hy; replace y with (S + (y - S)) by lia; apply AS; lia | exact H3]|].
  apply (CL5A.u64_same _ M M' (S + 8)); [lia | lia | intros y Hy; replace y with (S + (y - S)) by lia; apply AS; lia | exact H4].
Qed.

(* [comment removed for export] *)
Lemma retEx0_a1 : forall E' nx R2, ev (CH2.retEx E' nx [] R2) (nx + 5)%nat = getr R2 11%bv.
Proof.
  intros E' nx R2. unfold CH2.retEx, CH2.retE. cbn [length]. rewrite Nat.add_0_r. rewrite APS.ext_list_at by (clear; cbn; lia). cbn [APC.caller_saved map nth]. f_equal.
Qed.

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable IC : PMLA.consts.
Variable EC : PMESA.econsts.
Variable CL : Z.                    (* [comment removed for export] *)
Variable NF : nat.
Variable E0 : env.
Variable M00 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBo : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable D0 : Z.
(* [comment removed for export] *)
Variable GR : list (Z * Z).
Abbreviation gB := (EBA.gB GR).
Variable kx bx : Z.
Abbreviation CredV := (EBA.CredV L CL kx bx).
Variable XIv : eghost -> nat -> env -> list (Z * Z) -> mem -> Model -> Prop.

Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis SCR8 : SCR mod 8 = 0.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBo FFrest sp0 SCR a
                                                       /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FFrest sp0.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LBo FFrest sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Hypothesis DEF0 : L5.defined M00 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M00 sp0 (ar_stack_top ar - sp0).
Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.
(* [comment removed for export] *)
Variable STAT : list kentry.
Hypothesis STAT_ok : forallb (CHA.static_chk SCELLS GLO GHI) STAT = true.
(* [comment removed for export] *)
Hypothesis KPM : 0 <= hl_k_per_malloc L.
Hypothesis BLIN : 0 <= hl_b_lin L.
Hypothesis BOV : 0 <= hl_b_overhead L.
(* [comment removed for export] *)
Variables V S2 : Z.
Hypothesis OBJS0 : PMESA.objs_encA M00 FFrest V S2.
Hypothesis STKSH0 : PMSA.stksh ar M00 sp0 SCR.
Hypothesis IMG0 : PMLA.img_ro IC M00.
Hypothesis IMG_RO_ok : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
(* [comment removed for export] *)
Hypothesis W_app : forall w a, In w W -> L5.in_rng w a -> ~ (BIGSHADOW_LO <= a < BIGSHADOW_HI) /\ ~ (PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC).

Abbreviation FPI := PMSA.fp_ok.
Abbreviation OKV := (CHV.okV L ar M00 LBo FFrest sp0 d W).
Abbreviation AAMBV := (CHV.aambV L ar HI NF E0 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV).
Abbreviation AMBXV := (CHV.ambXV L ar HI NF E0 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv).
Abbreviation AMBV := (CHV.ambV L ar HI NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv).
Abbreviation LEAFOKV := (CHV.leaf_okV L ar HI NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv CPS K FPI).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).
Abbreviation curF := (CHA.curF FFrest sp0 FFS).

(* [comment removed for export] *)
Definition lit_chk (S txt n : Z) (unews : list kentry) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi : CA.blocks) (FFi : list (expr * Z * Z))
  (BLj : CA.blocks) (FFj : list (expr * Z * Z)) : option CH2.cinfo :=
  let nx := (CC.cp_nx cj - APC.NCS)%nat in
  if (CH2.blocks_eqb BLj BLi && CHA.frames_eqb FFj FFi)%bool
  then CHA.custom_chk NF d SCELLS GLO GHI PMESA.LIT_SCRA 0 BLi FFi [(ELit 0, S, ELit 18)] (KRange (EVar (nx + 5)) n n :: ESA.lit_news S txt n ++ STAT ++ unews) (Some (ELit txt)) c ps cj BLi FFi BLj FFj
  else None.

(* [comment removed for export] *)
Lemma lit_leaf_okV : forall (pc S G txt n : Z) unews i c k ps j cj ci g M0c,
  PMESA.literal_specA L ar HI IC pc S G txt n ->
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  lit_chk S txt n unews c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  CH2.blocks_vars_lt NF (nth i BLS []) = true ->
  0 <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (* [comment removed for export] *)
  (forall a, S <= a < S + 18 \/ G <= a < G + 2 -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a) ->
  (forall a, S <= a < S + 18 -> exists w, In w W /\ L5.in_rng w a) ->
  G = S + 16 /\ 0 <= S /\ S + 18 <= 2 ^ 62 /\ 0 <= txt < 2 ^ 64 /\ 0 <= n < 2 ^ 64 ->
  (* [comment removed for export] *)
  (forall E R A (M : mem) model E' R' (M' : mem) model' cr LK, CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model ->
     env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 PMESA.LIT_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     ri_inv HI (CHA.curB (CHV.LBr LBo eghost gB g) BLS i E) (curF i E) LK cr A M' (vml_of model') -> incl LK LK0 -> PMESA.ecreditA L CL cr g kx bx ->
     shadow_zero M' V 51 -> shadow_zero M' S2 3 -> PMSA.stksh ar M' sp0 SCR -> PMLA.img_ro IC M' ->
     (PMLA.lit_ok (hl_segs L) M' S G txt n /\ L5.writable (hl_segs L) M' S 18) /\
     forall R2 (M2 : mem) model2 A2 LK2, PMSA.a0 R2 txt -> PMSA.a1 R2 n -> PMESA.lit_done L M2 S G txt n -> regs_preserved R' R2 ->
       CHA.ahpres L ar (CHA.curB (CHV.LBr LBo eghost gB g) BLS i E) (curF i E) (sp0 + CH2.ci_csp ci) PMESA.LIT_SCRA [(S, 18)] M' M2 -> model_rt model' model2 -> incl A A2 -> CHA.amodel_ok A2 model2 ->
       incl LK2 LK -> ri_inv HI (CHA.curB (CHV.LBr LBo eghost gB g) BLS i E) (curF i E) LK2 cr A2 M2 (vml_of model2) ->
       let E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2 in
       XIv g j E2 A2 M2 model2 /\ (forall X, In X unews -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X)) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc S G txt n unews i c k ps j cj ci g M0c LIT HOKV IL Hret Hcj Hpc Hchk BVN Hdc SCL SW (HG & HS0 & HS1 & HT & HN) CALL.
  intros fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  unfold lit_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [B3 B4]. apply CH2.blocks_eqb_eq in B3.
  set (BLi := nth i BLS []) in *. set (FFi := nth i FFS []) in *.
  apply (CHV.callee_leafV L ar C HI HIok LY_img LY_ro NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W Wo BLS FFS D0 eghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 CRS_ok WRS_ok IMG_ok
           CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok K_nil g M0c pc PMESA.LIT_SCRA 0%nat BLi [(ELit 0, S, ELit 18)] _ (Some (ELit txt)) 0 i c ps j cj ci HOKV Hcj Hchk Hpc B4 Hdc
           fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH).
  intros cr LK CF HH1 HLK1 HC1.
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  destruct (EBA.amb_env L ar C HI HIok LY_img IC CL NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 GR kx bx STK SCR_pos SCR8 NF32 V S2 OBJS0 STKSH0 IMG0 IMG_RO_ok W_app g M0c i E A M1 model1 HOKV HA')
    as (ZV & ZS & ZSTK & ZIMG).
  destruct (CALL E R A M model E' R' M1 model1 cr LK HAt HA HXI Hag HLF CF HH1 HLK1 HC1 ZV ZS ZSTK ZIMG) as ((PRE1 & PRE2) & HPost).
  eexists _, _. split; [exact (LIT (CHA.curB (CHV.LBr LBo eghost gB g) BLS i E) (curF i E) LK cr A (sp0 + CH2.ci_csp ci) (CC.cp_pc cj))|].
  split.
  { split; [exact PRE1|]. split; [exact PRE2|]. split; [exact ZIMG|]. split; [|clear - HG HS0 HS1; lia].
    intros x Hx. exact (SCL x (or_introl Hx)). }
  intros R2 M2 model2 LB' cr' LBk Wc LK2 A2 (Pa0 & Pa1 & Pdone & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  destruct (HPost R2 M2 model2 A2 LK2 Pa0 Pa1 Pdone HRP HP Hrt2 HA2 Hmo2 HLK2 HH2) as (HXI2 & Hunews).
  exists [], g. split; [reflexivity|]. cbv zeta.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE'|]; eapply CC.env_agree_le; [exact Hag2 | clear - V3 V4; lia]).
  assert (ESL0 : forall Ex z, 0 <= z < 2 ^ 63 -> estart Ex (SA (ELit 0) z) = z) by (intros Ex z Hz; unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by (clear; lia); clear; lia).
  split; [unfold PMSA.a0 in Pa0; rewrite Pa0; cbn [edenot]; reflexivity|].
  split.
  { intros bb Hb. unfold CHA.curB, CHV.LBr. fold BLi. fold BLi in HdenB. rewrite <- HdenB.
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb]. }
  split.
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (ELit 0, S, ELit 18). split; [left; reflexivity|].
    unfold CHA.in_reg, elenZ. rewrite (ESL0 E' S) by (clear - HS0 HS1; lia). cbn [edenot]. rewrite (u64_of_Z 18) by (clear; lia). exact Hin. }
  split.
  { intros w a [<-|[]] Hin (_ & _ & Hout). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (SW a Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin'). }
  assert (Hcur : CHA.curB (CHV.LBr LBo eghost gB g) BLS j E2 = CHA.curB (CHV.LBr LBo eghost gB g) BLS i E).
  { unfold CHA.curB. rewrite B3. fold BLi. fold BLi in HdenB. rewrite <- HdenB. rewrite (CH2.den_agree NF E' E2 BLi ltac:(eapply CC.env_agree_le; [exact Hag2 | clear - V3 V4; lia]) BVN). reflexivity. }
  split; [rewrite Hcur; exact HH2|].
  split; [exact HC1|].
  split; [exact HXI2|].
  (* [comment removed for export] *)
  intros X HX HXc. destruct HX as [<-|HX].
  { (* [comment removed for export] *) cbn [kentry_ok]. replace (CC.cp_nx cj - APC.NCS + 5)%nat with (CH2.ci_nx ci + 5)%nat by (rewrite V5; clear; lia). cbn [edenot]. unfold E2. rewrite retEx0_a1.
    unfold PMSA.a1 in Pa1. rewrite Pa1. rewrite u64_of_Z by (clear - HN; lia). clear - HN; lia. }
  apply in_app_or in HX as [HX|HX].
  { (* [comment removed for export] *)
    assert (VIS : forall a, S <= a < S + 18 \/ G <= a < G + 2 -> ahid A2 model2 (Z_to_bv 64 a) = false).
    { intros a Ha. destruct (SCL a Ha) as (R1 & R2' & _).
      apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model2 sp0 0 a HH2); [clear - R1 LY_img; unfold BIGSHADOW_LO in *; lia | right; right; left; exact (conj R1 R2') |].
      intros Hsh. exfalso. destruct STK as (_ & K2 & _). pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a) as SR.
      destruct (CHA.rf_ceil _ _ _ _ (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2))) as (C0 & _).
      destruct (CHA.rf_sptop _ _ _ _ (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2))) as (SP1 & _).
      specialize (SR ltac:(clear - C0; lia) ltac:(clear - K2 SCR_pos SP1 STK; lia) ltac:(clear; lia) Hsh).
      clear - SR R1 LY_img. unfold BIGSHADOW_LO in *. lia. }
    destruct Pdone as (Q1 & Q2 & Q3 & Q4). unfold PMSA.u8, PMSA.u64 in Q1, Q2, Q3, Q4. subst G.
    unfold ESA.lit_news in HX. destruct HX as [<-|[<-|[<-|[<-|[]]]]].
    - eapply CL5A.kword8_intro with (A := S + 16) (z := 1); [apply ESL0; clear - HS0 HS1; lia | clear - HS0; lia | clear - HS1; lia | reflexivity | clear; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - HS0; lia | clear - HS1; lia | intros q Hq; apply VIS; clear - Hq; lia | exact Q1 ].
    - eapply CL5A.kword8_intro with (A := S + 17) (z := 1); [apply ESL0; clear - HS0 HS1; lia | clear - HS0; lia | clear - HS1; lia | reflexivity | clear; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - HS0; lia | clear - HS1; lia | intros q Hq; apply VIS; clear - Hq; lia | replace (S + 17) with (S + 16 + 1) by (clear; lia); exact Q2 ].
    - eapply CL5.kword64_intro with (A := S) (z := txt); [apply ESL0; clear - HS0 HS1; lia | clear - HS0; lia | clear - HS1; lia | cbn [edenot]; reflexivity |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - HS0; lia | clear - HS1; lia | intros q Hq; apply VIS; clear - Hq; lia | exact Q3].
    - eapply CL5.kword64_intro with (A := S + 8) (z := n); [apply ESL0; clear - HS0 HS1; lia | clear - HS0; lia | clear - HS1; lia | cbn [edenot]; reflexivity |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - HS0; lia | clear - HS1; lia | intros q Hq; apply VIS; clear - Hq; lia | exact Q4]. }
  apply in_app_or in HX as [HX|HX]; [|exact (Hunews X HX HXc)].
  rewrite forallb_forall in STAT_ok. exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 (STAT_ok X HX)).
Qed.
End Inst.
End EPA.
