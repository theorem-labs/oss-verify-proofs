(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b L5AFrameKR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnStepA_b PnAReset1_b PnAHarnessStmts_b PnAHarnessKit_b PnAHarnessKit2_b PnAHarnessSK_b PnAHarnessP2_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PNHA7.
Import L5A. Import L5CA. Import L5SAR. Import PNHAS.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
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
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 128) (V2 - 128) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 5 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487360 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.
(* [comment removed for export] *)
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 5, V2 - 128 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 128 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Hypothesis FAL : F mod 2048 = 0.
Hypothesis WERR : forall a, L5.outside W a -> L5.outside (PNST.berr_W PMA.AD PMA.AN) a.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 128 + 32) :: FF).

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PNHAK2.wapart_nil | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil])]])
  | (apply PNHAK2.wapart_nil) | lia ].

Lemma berr_W_hull r : In r (PNST.berr_W PMA.AD PMA.AN) -> (0x6722c0 <= fst r /\ fst r + snd r <= 0x672308) \/ (fst r = 0x693d50 /\ snd r = 544).
Proof.
  unfold PNST.berr_W, PNST.cat_W, PNST.dec_W. cbn. intros Hr.
  repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]). destruct Hr.
Qed.

Lemma stage7 (PARSE : PNRAa.parse_spec L ar HI) (fx8 : FPState) (R8 : bvmap 5 word) (M8 : word -> option byte) (model8 : Model) (K : TSet)
      (LK8 : list fframe) (cr8 : credit) (A8 : list (Z * Z)) (s str : PM.vstr) (sm : PM.strm) (ps : PNM.bpst) (g : PNST.st) (c : Z) :
  Bv W (PNM.bparser_own ps ++ PM.vs_own str ++ PM.vs_own s) M8 model8 LK8 cr8 A8 -> rinvH R R8 V2 cls F -> K [] -> PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M8 ->
  getr R8 (reg 1) = Z_to_bv 64 0xa84c0 -> getr R8 (reg 10) = Z_to_bv 64 (F + 464) -> getr R8 (reg 11) = Z_to_bv 64 (F + 432) ->
  getr R8 (reg 12) = Z_to_bv 64 (F + 1024) -> getr R8 (reg 21) = Z_to_bv 64 (F + 96) ->
  getr R8 (reg 22) = Z_to_bv 64 (F + 464) -> getr R8 (reg 23) = Z_to_bv 64 (F + 1024) -> getr R8 (reg 26) = Z_to_bv 64 18446744073709551608 ->
  PNHAK2.hbase F M8 s str sm -> PNHAK2.hpar F M8 ps -> PNHAK2.hec F M8 0 c ->
  PNRA.binv ps -> PM.unread (PNM.b_src ps) sm < 2 ^ 26 -> PNM.bgrow_ok ps -> PNRA.bb_room ps sm ->
  PMSPA.credit_le (PMSPA.scA L (PNRA.pot_bparser L ar ps)) cr8 ->
  (forall (fx9 : FPState) (R9 : bvmap 5 word) (M9 : word -> option byte) (model9 : Model) (LK9 : list fframe) (cr9 : credit) (A9 : list (Z * Z))
          (ps' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax),
      Bv W (PNM.bparser_own ps' ++ PM.vs_own str ++ PM.vs_own s) M9 model9 LK9 cr9 A9 -> rinvH R R9 V2 cls F ->
      PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN (PNST.ST (PNST.st_loc g) (PNST.st_sys g) ax') M9 -> PNST.bax_le (PNST.st_ax g) ax' ->
      getr R9 (reg 1) = Z_to_bv 64 0xa84e4 -> getr R9 (reg 10) = Z_to_bv 64 (V2 - 104) -> getr R9 (reg 21) = Z_to_bv 64 (F + 96) ->
      getr R9 (reg 22) = Z_to_bv 64 (F + 464) -> getr R9 (reg 23) = Z_to_bv 64 (F + 1024) -> getr R9 (reg 26) = Z_to_bv 64 18446744073709551608 ->
      PNHAK2.hbase F M9 s str sm' -> PNHAK2.hsrc F M9 (PNM.b_src ps') -> PM.vstr_at RSEGS PMSPA.accA M9 (F + 832) (PNM.b_tb ps') ->
      PM.vstr_at RSEGS PMSPA.accA M9 (F + 808) (PNM.b_nb ps') -> PNHAK2.v8_at M9 (F + 784) (PNM.b_bb ps') ->
      PNHAK2.hvec F M9 (PNM.b_sb ps') (PNM.b_sk ps') (PNM.b_stk ps') -> L5.u64_at RSEGS M9 (V2 - 104) (F + 856) ->
      L5.u64_at RSEGS M9 (F + 464) (pa_vp_parser PMA.AD) ->
      PMSPA.credit_keep cr8 cr9 (PMSPA.scA L (PNRA.pot_bparser L ar ps)) PMSPA.cr0 ->
      srealizes RSEGS SCFG (@L5A.cfg fx9 R9 0xab620 M9 model9) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx8 R8 0xade6c M8 model8) K.
Proof.
  intros BI RI K0 LS R1a R10 R11 R12 R21 R22 R23 R26 HB0 HP0 HE0 INV UNR GROW BBR CRD KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PNHAK2.hf F) by (unfold PNHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  assert (FDEF8 : L5.defined M8 F 2048).
  { pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M8 model8 LK8 cr8 A8 BI) as (_ & _ & (VFD & _) & (_ & _ & FV & _)).
    apply (proj1 (L5A.defined_vis (ahid A8 model8) M8 F 2048 FV)); exact VFD. }
  assert (B1' : ri_inv HI (PNM.bparser_own ps ++ ((PM.vs_own str ++ PM.vs_own s) ++ LB)) FF' LK8 cr8 A8 M8 (vml_of model8)) by (rewrite app_assoc; exact B1).
  pose proof HB0 as (VS0 & IS0 & VV0 & VZ0 & VI0). pose proof HP0 as (PA0 & REF0 & ACC0). pose proof HE0 as (EV0 & EC0 & EZ0 & ED0).
  pose proof LS as (LSB & LSL & LSS & LSE).
  unfold PNRAa.parse_spec, PNRA.parse_spec in PARSE.
  unfold PNRA.brun_pre, PNRA.parse_post, PNRA.brun_pre, PNRA.bargs3, PMSPA.ec_at, PMSPA.visitor_at, PNRA.W_brun, PGS.W_srcfG,
         PNRA.o_src, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_p, PNRA.o_is, PNRA.o_ec, PNRA.o_v, PmSpecs.PMSP.o_p, PmSpecs.PMSP.o_is, PmSpecs.PMSP.o_ec, PmSpecs.PMSP.o_v in PARSE.
  cbn [app PNL.pn_parse pa_off_p pa_off_is pa_off_ec pa_off_v pa_vp_visitor PNRAa.AD PNRAa.AN PNRAa.AAD PMA.AD PMA.AN PMA.AAD ADDR_A NADDR_A PNM.OFF_SRC PNM.OFF_BB PNM.OFF_NB PNM.OFF_TB PNM.OFF_STK] in PARSE.
  change PNM.PSIZE with 416 in PARSE.
  apply (PARSE fx8 R8 M8 model8 K ((PM.vs_own str ++ PM.vs_own s) ++ LB) FF' LK8 A8 cr8 (V2 - 128) 0xa84c0 F c 0 ps str sm (PNST.st_ax g) B1' B2 K0).
  { eapply PNHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PNHASK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PNHASK.callee_rs; eassumption. }
  { exact (PNHASK.callee_frame FF V2 F FAL). }
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split; [rewrite L5K.rl10; exact R10|]. split; [rewrite L5K.rl11; exact R11| rewrite L5K.rl12; exact R12]. }
  { split; [exact PA0|]. split; [exact IS0|]. split.
    { split; [cbn [pa_vp_visitor PMA.AD ADDR_A] in VV0; exact VV0|].
      apply (PMARS1.acc_of_shadow_zero M8 (F + 432) 1 (F + 432) 8 VZ0); [clear - FM8; lia| lia| lia]. }
    split; [replace (F + 464 + 416) with (F + 880) by lia; exact REF0|]. split; [replace (416 + 8) with 424 by reflexivity; exact ACC0|].
    split; [exact LSB|]. split; [exact LSE| exact GROW]. }
  { intros x Hx. apply in_or_app. left. apply in_or_app. left. exact Hx. }
  { exact INV. }
  { split; [exact EV0|]. split; [replace (F + 1024 + 8) with (F + 1032) by lia; exact EC0|]. split.
    - exact ED0.
    - apply (PMARS1.acc_of_shadow_zero M8 (F + 1024) 2 (F + 1024) 16 EZ0); [clear - FM8; lia| lia| lia]. }
  { lia. }
  { exact UNR. }
  { exact BBR. }
  { exact CRD. }
  intros fx' R' M' model' LK' Aw' ps' sm' ax' cr' RP' PP HP' CK' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 10) with 32768 in HP'.
  rewrite app_assoc in HH'.
  destruct PP as ((PA' & IS' & (VV' & VA') & REF' & ACC' & BASE' & ERR' & GROW') & SST & AXLE & DEC').
  set (Wc := (F + 464 + 8, 8) :: (F + 464 + 16 + 256, 40) :: (F + 96 + 40, 8) :: (F + 96 + 152, 4) :: (F + 464 + 320, 24) :: (F + 464 + 344, 24) :: (F + 464 + 368, 24) :: (F + 464 + 392, 24)
               :: (F + 1024, 16) :: PNST.berr_W PMA.AD PMA.AN) in *.
  assert (WcL : forall r, In r Wc -> (F + 96 <= fst r /\ fst r + snd r <= F + 1040) \/ In r (PNST.berr_W PMA.AD PMA.AN)).
  { intros r Hr. subst Wc. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd]; (left; lia) || (right; exact Hr). }
  assert (WFI : PNHAK2.wfi F Wc).
  { intros r Hr. destruct (WcL r Hr) as [X|X]; [left; lia| right; destruct (berr_W_hull r X) as [BW|(BW1 & BW2)]; [lia| rewrite BW1, BW2; lia]]. }
  assert (WAF : forall o n, F <= o -> o + n <= F + 2048 -> (forall r, In r Wc -> F + 96 <= fst r -> fst r + snd r <= F + 1040 -> fst r + snd r <= o \/ o + n <= fst r) -> PNHAK2.wapart Wc o n).
  { intros o n H1 H2 H r Hr. destruct (WcL r Hr) as [(Z1 & Z2)|X]; [exact (H r Hr Z1 Z2)| left; destruct (berr_W_hull r X) as [BW|(BW1 & BW2)]; [clear - H1 FR BW; lia| rewrite BW1, BW2; clear - H1 FR; lia]]. }
  assert (LS' : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN (PNST.ST (PNST.st_loc g) (PNST.st_sys g) ax') M').
  { apply (PNHAK.ls_ahpres_err L C LY g ax' ar _ FF' (V2 - 128) 32768 Wc M8 M' HP'); [| exact LS| exact ERR'].
    intros a Ha r Hr Hin. unfold L5.in_rng in Hin. unfold PNHAK.bcell, PNHAK.lcell, PNHAK.scell in Ha.
    destruct (WcL r Hr) as [(Z1 & Z2)|X]; [clear - Ha Hin Z1 Z2 FR; lia| destruct (berr_W_hull r X) as [BW|(BW1 & BW2)]; [clear - Ha Hin BW; lia| rewrite BW1, BW2 in Hin; clear - Ha Hin; lia]]. }
  assert (BI' : Bv W (PNM.bparser_own ps' ++ PM.vs_own str ++ PM.vs_own s) M' model' LK' cr' Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ (PM.vs_own str ++ PM.vs_own s) _ M8 model8 LK8 cr8 A8 M' model' LK' cr' Aw' 32768 Wc BI HP' HH' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a Hr Ha. unfold L5.in_rng in Ha. unfold tocell. destruct (WcL rr Hr) as [(Z1 & Z2)|X].
      + split; [clear - Ha Z1 Z2 FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha Z1 Z2 FR F8 FBIG. lia.
      + destruct (berr_W_hull rr X) as [BW|(BW1 & BW2)].
        * split; [clear - Ha BW SLO SPT; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha BW FR F8. lia.
        * rewrite BW1, BW2 in Ha. split; [clear - Ha SLO SPT; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8. lia.
    - intros a Hc Ho rr Hr Ha. unfold L5.in_rng in Ha. destruct (WcL rr Hr) as [(Z1 & Z2)|X].
      + apply (NCF a); [left; clear - Ha Z1 Z2; lia| exact Hc].
      + exact (WERR a Ho rr X Ha).
    - intros a X. exact X. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R8 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
  assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R8 R' 21 RP') by inl; exact R21).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R8 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 1024)) by (rewrite (cs_of_preserved R8 R' 23 RP') by inl; exact R23).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R8 R' 26 RP') by inl; exact R26).
  assert (FIN8 : In (F, 5, V2 - 128 + 32) (FF' ++ LK8)) by (apply in_or_app; left; left; reflexivity).
  (* [comment removed for export] *)
  assert (VS' : PM.vstr_at RSEGS PMSPA.accA M' (F + 32) s).
  { eapply PNHAK2.vstr_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact VS0 | exact FHF | exact FIN8 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx)
      | (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx)
      | (apply WAF; [lia| lia| intros r Hr Z1 Z2; clear - Z1; lia]) | lia ]. }
  assert (AGV : PMFA.agA M8 M' (F + 432) 8).
  { apply (PNHAK2.ff_callee L ar _ FF' (V2 - 128) 32768 Wc M8 M' (F, 5, V2 - 128 + 32) F (F + 432) 8 HP' (or_introl eq_refl));
      cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFI|].
    apply WAF; [lia| lia|]. intros r Hr Z1 Z2. subst Wc. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd] in *; [clear - Z1 Z2 FR; lia ..|].
    destruct (berr_W_hull _ Hr) as [BW|(BW1 & BW2)]; [clear - BW FR; lia| rewrite BW1, BW2; clear - FR; lia]. }
  assert (VZ' : shadow_zero M' (F + 432) 1) by (apply (PNHAK2.shz_agA M8 M' (F + 432) 8 (F + 432) 1 AGV); [lia| lia| clear - FM8; lia| lia| exact VZ0]).
  assert (VI' : shadow_zero M' (F + 96) 34)
    by (apply (PNHAK2.shz_callee L ar _ FF' (V2 - 128) 32768 Wc M8 M' (F, 5, V2 - 128 + 32) F (F + 96) 34 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
          [lia| lia| clear - FM8; lia| lia| exact VI0]).
  replace (F + 464 + 416) with (F + 880) in REF' by lia. change (416 + 8) with 424 in ACC'.
  destruct (PNHAK2.hdead_of_parser M' F ps' (conj PA' (conj REF' ACC'))) as (HS' & TB' & NB' & BB' & HV').
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 128 + 144 <= F \/ F + 2048 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  LeanFeed.pfeed P (PNAHP2.bhaH_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PNAHP2.aligned; exact V2A) ]).
  destruct P as (fx9 & R9 & M9v & MG9 & hFR & hFZ & (hMS & hKS & hR1 & hR10 & hT & hVP & HQ)).
  set (W9 := fun a => V2 - 104 <= a < V2 - 104 + 8 \/ F + 464 <= a < F + 464 + 8 \/ F / 8 + 2147451008 <= a < F / 8 + 2147451008 + 2).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx9 R' 0xa84c0 R9 0xab620 M9v W9 K HH' AM' hMS MG9).
  { intros a Ha Hna. apply hFZ; [exact Ha|..]; intros X; apply Hna; subst W9; cbn beta; clear - X; lia. }
  { intros a Ha Wa. subst W9; cbn beta in Wa. split.
    - destruct Wa as [Wa|[Wa|Wa]].
      + apply stack_client; clear - Wa SLO SHI SPT CLS V2R; lia.
      + apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
      + apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
        unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR V2R. lia. }
  intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9 VV9. change (mrestrict H' M9 = M9v) in VIS9.
  assert (BI9 : Bv W (PNM.bparser_own ps' ++ PM.vs_own str ++ PM.vs_own s) M9 model9 LK' cr' Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' M9 model9 W9 BI' HH9 AM9 MRT9 MGM9 FR9).
    intros a Wa. subst W9; cbn beta in Wa. change (ff_bytes 5) with 2048. change (2048 / 8) with 256. destruct Wa as [Wa|[Wa|Wa]].
    - left. split; [clear - Wa CLS; lia|]. unfold tocell. clear - Wa CLS. lia.
    - right; left. clear - Wa. lia.
    - right; right. unfold HeapIfaceA.SB. clear - Wa. lia. }
  assert (RI9 : rinvH R R9 V2 cls F) by (apply (rinvH_ks R R' R9 V2 cls F PNAHP2.KS_bhaH RI' hKS); vm_compute; reflexivity).
  assert (LS9 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN (PNST.ST (PNST.st_loc g) (PNST.st_sys g) ax') M9).
  { apply (PNHAK.ls_piece _ M' M9 W9 FR9); [| exact LS']. intros a Wa. subst W9; cbn beta in Wa. clear - Wa FR V2R. lia. }
  assert (PF9 : PNHAK2.pfoot F (V2 - 128) V2 W9) by (intros a Wa; subst W9; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  assert (FIN' : In (F, 5, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (OAX : forall o n, F + 472 <= o -> o + n <= F + 1024 -> PNHAK2.oav W9 o n).
  { intros o n H1 H2 x Hx. subst W9; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR FM8 V2R SLO FCEIL CLS; lia. }
  assert (OAY : forall o n, F + 32 <= o -> o + n <= F + 464 -> PNHAK2.oav W9 o n).
  { intros o n H1 H2 x Hx. subst W9; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X; clear - Hx X H1 H2 SX FBIG FR FM8 V2R SLO FCEIL CLS; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (INCP : incl (PNM.bparser_own ps') ((PNM.bparser_own ps' ++ PM.vs_own str ++ PM.vs_own s) ++ LB)) by (intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx).
  apply (KONT fx9 R9 M9 model9 LK' cr' Aw' ps' sm' ax' BI9 RI9 LS9 AXLE).
  - exact hR1.
  - exact hR10.
  - rewrite (hKS 21%nat) by inl. exact Y21.
  - rewrite (hKS 22%nat) by inl. exact Y22.
  - rewrite (hKS 23%nat) by inl. exact Y23.
  - rewrite (hKS 26%nat) by inl. exact Y26.
  - apply (PNHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W9 M' M9 SLOW SHW FR9 PF9 s str sm');
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx| apply OAY; lia| apply OAY; lia| apply OAY; lia|].
    split; [exact VS'|]. split; [exact IS'|]. split; [cbn [pa_vp_visitor PMA.AD ADDR_A]; exact VV'| split; [exact VZ'| exact VI']].
  - apply (PNHAK2.hsrc_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W9 M' M9 SLOW SHW FR9 PF9 (PNM.b_src ps'));
      [apply INCP; left; reflexivity| apply OAX; lia| exact HS'].
  - apply (PNHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W9 M' M9 SLOW SHW FR9 PF9 (F + 832) (PNM.b_tb ps'));
      [intros x Hx; apply INCP; unfold PNM.bparser_own, PNM.brest_own; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hx
      | clear - FR; lia| clear - FR; lia| apply OAX; lia| exact TB'].
  - apply (PNHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W9 M' M9 SLOW SHW FR9 PF9 (F + 808) (PNM.b_nb ps'));
      [intros x Hx; apply INCP; unfold PNM.bparser_own, PNM.brest_own; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hx
      | clear - FR; lia| clear - FR; lia| apply OAX; lia| exact NB'].
  - apply (PNHAK2.v8_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W9 M' M9 SLOW SHW FR9 PF9 (F + 784) (PNM.b_bb ps'));
      [intros x Hx; apply INCP; unfold PNM.bparser_own, PNM.brest_own; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hx
      | clear - FR; lia| clear - FR; lia| apply OAX; lia| exact BB'].
  - apply (PNHAK2.hvec_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W9 M' M9 SLOW SHW FR9 PF9 (PNM.b_sb ps') (PNM.b_sk ps') (PNM.b_stk ps'));
      [apply INCP; unfold PNM.bparser_own, PNM.brest_own; apply in_or_app; right; apply in_or_app; left; left; reflexivity| apply OAX; lia| exact HV'].
  - apply (PNHAK.u64_vis H' M9 M9v (V2 - 104) _ VV9); [| clear - V2R; lia| clear - V2R; lia| exact hT].
    apply (PNHAK.avis_sub H' (V2 - 128) (V2 + cls - (V2 - 128)) (V2 - 104) 8 SPV'); clear - CLS; lia.
  - apply (PNHAK.u64_vis H' M9 M9v (F + 464) _ VV9); [| clear - FR; lia| clear - FR; lia| cbn [pa_vp_parser PMA.AD ADDR_A]; exact hVP].
    pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' BI') as (_ & _ & _ & (_ & _ & FV'' & _)).
    change (ff_bytes 5) with 2048 in FV''. apply (PNHAK.avis_sub H' F 2048 (F + 464) 8 FV''); lia.
  - assert (E0 : PMSPA.scA L PmSpecs.PMSP.cr0 = PMSPA.cr0) by (unfold PMSPA.scA, PmSpecs.PMSP.cr0, PMSPA.cr0; cbn [fst snd]; rewrite Z.mul_0_r; reflexivity).
    rewrite E0 in CK'. exact CK'.
Qed.
End Stage.
End SCFG_1.
End PNHA7.
