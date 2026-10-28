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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b L5AFrameKR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnStepA_b PnAReset1_b PnAHarnessStmts_b PnAHarnessKit_b PnAHarnessKit2_b PnAHarnessSK_b PnAParKit_b PnAHarnessP2_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PNHA4.
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
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 128 + 32) :: FF).

Lemma stage4 (RDC : PNRAa.reader_ctor_spec L ar HI) (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model) (K : TSet)
      (LK5 : list fframe) (cr5 : credit) (A5 : list (Z * Z)) (s s' : PM.vstr) (sm : PM.strm) (data : Z) (g : PNST.st) :
  Bv W (PM.vs_own s' ++ PM.vs_own s) M5 model5 LK5 cr5 A5 -> rinvH R R5 V2 cls F -> K [] -> PNST.st_loc g = true -> PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M5 ->
  getr R5 (reg 1) = Z_to_bv 64 0xa8474 -> getr R5 (reg 10) = Z_to_bv 64 (F + 464) -> getr R5 (reg 11) = Z_to_bv 64 (F + 96) ->
  getr R5 (reg 12) = Z_to_bv 64 (F + 960) -> getr R5 (reg 13) = Z_to_bv 64 (V2 - 104) ->
  getr R5 (reg 21) = Z_to_bv 64 (F + 96) -> getr R5 (reg 22) = Z_to_bv 64 (F + 464) -> getr R5 (reg 23) = Z_to_bv 64 data -> getr R5 (reg 26) = Z_to_bv 64 (F + 432) ->
  0 <= data < 2 ^ 64 ->
  PM.vstr_at RSEGS PMSPA.accA M5 (F + 32) s -> PM.iss_at RSEGS PMA.AD PMSPA.accA M5 (F + 96) s' sm ->
  PMSPA.credit_le (PMSPA.scA L (PM.credit_add (PM.cost1 (PMSPA.HV L ar) PM.CHUNK) (PM.cost1 (PMSPA.HV L ar) PNM.BSZ))) cr5 ->
  L5.u64_at RSEGS M5 (F + 432) 1251456 -> L5.u64_at RSEGS M5 (F + 960) 1251800 -> L5.u32_at RSEGS M5 (F + 976) 1024 ->
  shadow_zero M5 (F + 432) 1 -> shadow_zero M5 (F + 464) 53 -> shadow_zero M5 (F + 960) 3 -> shadow_zero M5 (F + 96) 34 ->
  (forall (fx6 : FPState) (R6 : bvmap 5 word) (M6 : word -> option byte) (model6 : Model) (LK6 : list fframe) (cr6 : credit) (A6 : list (Z * Z)) (qc b : Z),
      Bv W (PNM.bparser_own (PNRA.bparser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M6 model6 LK6 cr6 A6 -> rinvH R R6 V2 cls F ->
      PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M6 ->
      getr R6 (reg 1) = Z_to_bv 64 0xa84b0 -> getr R6 (reg 21) = Z_to_bv 64 (F + 96) -> getr R6 (reg 22) = Z_to_bv 64 (F + 464) ->
      getr R6 (reg 23) = Z_to_bv 64 (F + 1024) -> getr R6 (reg 26) = Z_to_bv 64 18446744073709551608 ->
      PM.vstr_at RSEGS PMSPA.accA M6 (F + 32) s -> PM.iss_at RSEGS PMA.AD PMSPA.accA M6 (F + 96) s' sm ->
      PNHAK2.bparser_at M6 (F + 464) (F + 96) (PNRA.bparser_init qc b) ->
      PMSPA.credit_keep cr5 cr6 (PMSPA.scA L (PM.credit_add (PM.cost1 (PMSPA.HV L ar) PM.CHUNK) (PM.cost1 (PMSPA.HV L ar) PNM.BSZ))) PMSPA.cr0 ->
      L5.u64_at RSEGS M6 (F + 432) 1251456 -> shadow_zero M6 (F + 432) 1 -> L5.u64_at RSEGS M6 (F + 880) (F + 432) -> PMSPA.accA M6 (F + 464) 424 ->
      L5.u32_at RSEGS M6 (F + 1024) 0 -> shadow_zero M6 (F + 1024) 2 -> shadow_zero M6 (F + 96) 34 ->
      srealizes RSEGS SCFG (@L5A.cfg fx6 R6 0xd950c M6 model6) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx5 R5 0xac78c M5 model5) K.
Proof.
  intros BI RI K0 GL LS R1a R10 R11 R12 R13 R21 R22 R23 R26 Hd VS0 IS0 CRD V432 O960 O976 SZV SZP SZO SZI KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M5 model5 LK5 cr5 A5 BI)
    as ((VW5 & VIC5 & VSB5 & VUAR5 & VMS5) & VOWN5 & (VFD5 & VFW5 & VFSW5 & VFLC5 & VFLW5) & (FLCc5 & FLV5 & FV5 & SPV5 & FSV5)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  assert (FDEF5 : L5.defined M5 F 2048) by (apply (proj1 (L5A.defined_vis (ahid A5 model5) M5 F 2048 FV5)); exact VFD5).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PNHAK2.hf F) by (unfold PNHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  pose proof LS as (LSB & LSL & LSS & LSE). rewrite GL in LSL.
  unfold PNRAa.reader_ctor_spec, PNRA.reader_ctor_spec in RDC. unfold PNRA.o_p, PNRA.o_is, PmSpecs.PMSP.o_p, PmSpecs.PMSP.o_is in RDC. cbn [PNL.pn_reader_ctor pa_off_p pa_off_is pa_vp_opts PNRAa.AD PNRAa.AN PMA.AD PMA.AN ADDR_A NADDR_A] in RDC.
  change PNM.MAX_DEPTH with 1024 in RDC. change PNM.PSIZE with 416 in RDC.
  apply (RDC fx5 R5 M5 model5 K ((PM.vs_own s' ++ PM.vs_own s) ++ LB) FF' LK5 A5 cr5 (V2 - 128) 0xa8474 F (F + 960) (V2 - 104) s' sm B1 B2 K0).
  { eapply PNHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PNHASK.callee_roomB; first [exact BI | eassumption | lia]. }
  { eapply PNHASK.callee_rs; eassumption. }
  { exact (PNHASK.callee_frame FF V2 F FAL). }
  { rewrite L5K.rl10. exact R10. }
  { rewrite L5K.rl11. exact R11. }
  { rewrite L5K.rl12. exact R12. }
  { rewrite L5K.rl13. exact R13. }
  { apply (PNAPAR.aobj_fbB FF' F (F + 960) 24 (PNHASK.callee_frame FF V2 F FAL)); lia. }
  { lia. }
  { clear - FAL. lia. }
  { apply (L5.defined_sub M5 F 2048 (F + 464) 416 FDEF5); lia. }
  { apply (PMARS1.acc_of_shadow_zero M5 (F + 464) 53 (F + 464) 416 SZP); [clear - FM8; lia| lia| lia]. }
  { apply (PMARS1.acc_of_shadow_zero M5 (F + 960) 3 (F + 960) 24 SZO); [clear - FM8; lia| lia| lia]. }
  { exact O960. }
  { replace (F + 960 + 16) with (F + 976) by lia. exact O976. }
  { exact IS0. }
  { exact LSB. }
  { exact LSL. }
  { exact CRD. }
  intros fx' R' M' model' LK' Aw' qc b cr' RP' PAT HP' CK' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 6) with 24576 in HP'. change PNM.PSIZE with 416 in HP'.
  rewrite app_assoc in HH'.
  assert (WFI : PNHAK2.wfi F [(F + 464, 416)]) by (apply PNHAK2.wfi_cons; [cbn [fst snd]; left; lia| apply PNHAK2.wfi_nil]).
  assert (LS' : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M').
  { apply (PNHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) _ [(F + 464, 416)] M5 M' HP'); [| exact LS].
    apply PNHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PNHAK.far_nil]. }
  assert (BI' : Bv W (PNM.bparser_own (PNRA.bparser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W (PM.vs_own s' ++ PM.vs_own s) (PM.vs_own s' ++ PM.vs_own s) _ M5 model5 LK5 cr5 A5 M' model' LK' cr' Aw' 24576 [(F + 464, 416)] BI HP' HH' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
    - intros a X. exact X. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R5 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
  assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R5 R' 21 RP') by inl; exact R21).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R5 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 data) by (rewrite (cs_of_preserved R5 R' 23 RP') by inl; exact R23).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R5 R' 26 RP') by inl; exact R26).
  assert (FIN5 : In (F, 5, V2 - 128 + 32) (FF' ++ LK5)) by (apply in_or_app; left; left; reflexivity).
  (* [comment removed for export] *)
  assert (VS' : PM.vstr_at RSEGS PMSPA.accA M' (F + 32) s).
  { eapply PNHAK2.vstr_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact VS0 | exact FHF | exact FIN5 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | apply incl_refl | (intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx)
      | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil]) | lia ]. }
  assert (IS' : PM.iss_at RSEGS PMA.AD PMSPA.accA M' (F + 96) s' sm).
  { eapply PNHAK2.iss_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact IS0 | exact FHF | exact FIN5 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | apply incl_refl | (intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx)
      | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil]) | lia ]. }
  assert (AGV : PMFA.agA M5 M' (F + 432) 8).
  { apply (PNHAK2.ff_callee L ar _ FF' (V2 - 128) 24576 [(F + 464, 416)] M5 M' (F, 5, V2 - 128 + 32) F (F + 432) 8 HP' (or_introl eq_refl));
      cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; [lia| lia| exact FHF| lia| lia| exact WFI|].
    apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil]. }
  assert (V432' : L5.u64_at RSEGS M' (F + 432) 1251456) by (apply (PNHAK2.u64_agA M5 M' (F + 432) 8 (F + 432) _ AGV); [lia| lia| lia| lia| exact V432]).
  assert (SZV' : shadow_zero M' (F + 432) 1) by (apply (PNHAK2.shz_agA M5 M' (F + 432) 8 (F + 432) 1 AGV); [lia| lia| clear - FM8; lia| lia| exact SZV]).
  assert (SZP' : shadow_zero M' (F + 464) 53)
    by (apply (PNHAK2.shz_callee L ar _ FF' (V2 - 128) 24576 [(F + 464, 416)] M5 M' (F, 5, V2 - 128 + 32) F (F + 464) 53 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
          [lia| lia| clear - FM8; lia| lia| exact SZP]).
  assert (SZE' : shadow_zero M' (F + 880) 1)
    by (apply (PMKA.shadow_zero_sub M' (F + 464) 53); [clear - FM8; lia| clear - FM8; lia| lia| lia| lia| exact SZP']).
  assert (ZE' : L5KA.zeros_at MV' (F / 8 + 2147450990) 1).
  { apply (proj2 (L5A.zeros_at_vis H' M' (F / 8 + 2147450990) 1 (PNHAK.avis_sub H' (F / 8 + HeapIfaceA.SB) 256 (F / 8 + 2147450990) 1 FSV' ltac:(unfold HeapIfaceA.SB; lia) ltac:(unfold HeapIfaceA.SB; lia)))).
    replace (F / 8 + 2147450990) with (HeapIfaceA.S (F + 880)). apply PNHAK2.zeros_of_shz. exact SZE'.
    unfold HeapIfaceA.S, HeapIfaceA.SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - FM8. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SZI' : shadow_zero M' (F + 96) 34)
    by (apply (PNHAK2.shz_callee L ar _ FF' (V2 - 128) 24576 [(F + 464, 416)] M5 M' (F, 5, V2 - 128 + 32) F (F + 96) 34 HP' (or_introl eq_refl) (conj eq_refl eq_refl) FHF WFI);
          [lia| lia| clear - FM8; lia| lia| exact SZI]).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 128 + 144 <= F \/ F + 2048 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  LeanFeed.pfeed P (PNAHP2.bhaE_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 33%nat => data | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - Hd; lia) | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact ZE' | (unfold PNAHP2.aligned; exact V2A) ]).
  destruct P as (fx6 & R6 & M6v & MG6 & eFR & eFZ & (eMS & eKS & eR1 & eR10 & eR11 & eR23 & eR26 & EQ)).
  set (W6 := fun a => F + 880 <= a < F + 880 + 8 \/ F + 1024 <= a < F + 1024 + 4 \/ F / 8 + 2147451000 <= a < F / 8 + 2147451000 + 3
                      \/ F / 8 + 2147451008 <= a < F / 8 + 2147451008 + 2).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr' Aw' M' model' fx' fx6 R' 0xa8474 R6 0xd950c M6v W6 K HH' AM' eMS MG6).
  { intros a Ha Hna. apply eFZ; [exact Ha|..]; intros X; apply Hna; subst W6; cbn beta; clear - X; lia. }
  { intros a Ha Wa. subst W6; cbn beta in Wa. split.
    - destruct Wa as [Wa|[Wa|Wa]].
      + apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
      + apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
      + apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 128 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
        unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
  intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6. change (mrestrict H' M6 = M6v) in VIS6.
  decompose [and] EQ. clear EQ.
  assert (BI6 : Bv W (PNM.bparser_own (PNRA.bparser_init qc b) ++ PM.vs_own s' ++ PM.vs_own s) M6 model6 LK' cr' Aw').
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' Aw' M6 model6 W6 BI' HH6 AM6 MRT6 MGM6 FR6).
    intros a Wa. subst W6; cbn beta in Wa. right. change (ff_bytes 5) with 2048. change (2048 / 8) with 256. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
  assert (RI6 : rinvH R R6 V2 cls F) by (apply (rinvH_ks R R' R6 V2 cls F PNAHP2.KS_bhaE RI' eKS); vm_compute; reflexivity).
  assert (LS6 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M6).
  { apply (PNHAK.ls_piece _ M' M6 W6 FR6); [| exact LS']. intros a Wa. subst W6; cbn beta in Wa. clear - Wa FR. lia. }
  assert (PF6 : PNHAK2.pfoot F (V2 - 128) V2 W6) by (intros a Wa; subst W6; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  assert (FIN' : In (F, 5, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (OA32 : PNHAK2.oav W6 (F + 32) 24) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
  assert (OA96 : PNHAK2.oav W6 (F + 96) 272) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
  assert (OA464 : PNHAK2.oav W6 (F + 464) 416) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
  assert (OA432 : PNHAK2.oav W6 (F + 432) 8) by (intros x Hx; subst W6; cbn beta; unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *; split; intros X; clear - Hx X FR FBIG FM8; lia).
  assert (Q1024 : (F + 1024) / 8 + HeapIfaceA.SB = F / 8 + 2147451008) by (unfold HeapIfaceA.SB; clear - FM8; lia).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (VS6 : PM.vstr_at RSEGS PMSPA.accA M6 (F + 32) s).
  { apply (PNHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W6 M' M6 SLOW SHW FR6 PF6 (F + 32) s);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx| clear - FR; lia| clear - FR; lia| exact OA32| exact VS']. }
  assert (IS6 : PM.iss_at RSEGS PMA.AD PMSPA.accA M6 (F + 96) s' sm).
  { apply (PNHAK2.iss_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W6 M' M6 SLOW SHW FR6 PF6 (F + 96) s' sm);
      [intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hx| clear - FR; lia| clear - FR; lia| exact OA96| exact IS']. }
  assert (PA6 : PNHAK2.bparser_at M6 (F + 464) (F + 96) (PNRA.bparser_init qc b)).
  { apply (PNHAK2.bparser_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 W6 M' M6 SLOW SHW FR6 PF6 (F + 464) (F + 96));
      [intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx| clear - FR; lia| clear - FR; unfold PNM.PSIZE; lia| exact OA464| exact PAT]. }
  assert (AGV6 : PMFA.agA M' M6 (F + 432) 8) by (apply (PNHAK.agA_frame M' M6 W6 (F + 432) 8 FR6); [clear - FR; lia| clear - FR; lia| exact OA432]).
  assert (AVF : forall d k, 0 <= d -> d + k <= 2048 -> L5A.avis H' (F + d) k) by (intros d k Hd1 Hd2; apply (PNHAK.avis_sub H' F 2048 (F + d) k FV'); lia).
  assert (AVS : forall q k, F / 8 + 2147450880 <= q -> q + k <= F / 8 + 2147450880 + 256 -> L5A.avis H' q k)
    by (intros q k Hd1 Hd2; apply (PNHAK.avis_sub H' (F / 8 + HeapIfaceA.SB) 256 q k FSV'); unfold HeapIfaceA.SB; lia).
  apply (KONT fx6 R6 M6 model6 LK' cr' Aw' qc b BI6 RI6 LS6).
  - exact eR1.
  - rewrite (eKS 21%nat) by inl. exact Y21.
  - rewrite (eKS 22%nat) by inl. exact Y22.
  - exact eR23.
  - exact eR26.
  - exact VS6.
  - exact IS6.
  - exact PA6.
  - assert (E0 : PMSPA.scA L PmSpecs.PMSP.cr0 = PMSPA.cr0) by (unfold PMSPA.scA, PmSpecs.PMSP.cr0, PMSPA.cr0; cbn [fst snd]; rewrite Z.mul_0_r; reflexivity).
    rewrite E0 in CK'. exact CK'.
  - apply (PNHAK2.u64_agA M' M6 (F + 432) 8 (F + 432) _ AGV6); [lia| lia| lia| lia| exact V432'].
  - apply (PNHAK2.shz_agA M' M6 (F + 432) 8 (F + 432) 1 AGV6); [lia| lia| clear - FM8; lia| lia| exact SZV'].
  - apply (PNHAK.u64_vis H' M6 M6v (F + 880) _ VV6 (AVF 880 8 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
  - apply (PNHAK2.acc_of_shz M6 (F + 464) 53 (F + 464) 424); [| clear - FM8; lia| clear - FR; lia| lia| lia].
    apply (PNHAK2.shz_frame M' M6 W6 (F + 464) 53 FR6); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZP'].
    intros j Hj X. subst W6; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E464 : (F + 464) / 8 = F / 8 + 58) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E464 in X. clear - X Hj FBD FR FBIG. lia.
  - apply (PNHAK.u32_vis H' M6 M6v (F + 1024) _ VV6 (AVF 1024 4 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)). asm.
  - apply (PNHAK.shz_vis H' M6 M6v (F + 1024) 2 (F / 8 + 2147451008) VV6 (AVS (F / 8 + 2147451008) 2 ltac:(lia) ltac:(lia)) Q1024 ltac:(clear - FBD; lia) ltac:(clear - FBD; lia)).
    intros j Hj. assert (J : j = 0 \/ j = 1) by (clear - Hj; lia).
    destruct J as [J|J]; subst j; gmem.
  - apply (PNHAK2.shz_frame M' M6 W6 (F + 96) 34 FR6); [| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| unfold HeapIfaceA.S, HeapIfaceA.SB; clear - FBD; lia| exact SZI'].
    intros j Hj X. subst W6; cbn beta in X. unfold HeapIfaceA.S, HeapIfaceA.SB in X.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E96 : (F + 96) / 8 = F / 8 + 12) by (clear - FM8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite E96 in X. clear - X Hj FBD FR FBIG. lia.
Qed.
End Stage.
End SCFG_1.
End PNHA4.
