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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b L5AFrameKR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnStepA_b PnAReset1_b PnAHarnessStmts_b PnAHarnessKit_b PnAHarnessKit2_b PnAHarnessSK_b PnAHarnessKit3_b PnSpecsAX_b PnAHarnessP3_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PNHA8.
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

Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
  | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PNHAK2.wapart_nil | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil])]])
  | (apply PNHAK2.wapart_nil) | lia ].

Lemma stage8 (VDT : PNSAX.vec_dtor_spec RSEGS PMA.AD L ar HI 0xab620) (OPD : PMA.opdel_spec L ar HI) (fx9 : FPState) (R9 : bvmap 5 word) (M9 : word -> option byte) (model9 : Model) (K : TSet)
      (LK9 : list fframe) (cr9 : credit) (A9 : list (Z * Z)) (s str tb nb : PM.vstr) (bb : PGV8.v8) (sm : PM.strm) (src : PM.srcst) (b k : Z) (stk : list PNM.bstate) (g : PNST.st) :
  Bv W ((PM.sr_qc src, PM.CHUNK) :: (b, 40 * 2 ^ k) :: PGV8.v8_own bb ++ PM.vs_own nb ++ PM.vs_own tb ++ PM.vs_own str ++ PM.vs_own s) M9 model9 LK9 cr9 A9 -> rinvH R R9 V2 cls F -> K [] ->
  PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M9 ->
  getr R9 (reg 1) = Z_to_bv 64 0xa84e4 -> getr R9 (reg 10) = Z_to_bv 64 (V2 - 104) -> getr R9 (reg 21) = Z_to_bv 64 (F + 96) ->
  getr R9 (reg 22) = Z_to_bv 64 (F + 464) -> getr R9 (reg 23) = Z_to_bv 64 (F + 1024) -> getr R9 (reg 26) = Z_to_bv 64 18446744073709551608 ->
  PNHAK2.hbase F M9 s str sm -> PNHAK2.hsrc F M9 src -> PM.vstr_at RSEGS PMSPA.accA M9 (F + 832) tb -> PM.vstr_at RSEGS PMSPA.accA M9 (F + 808) nb ->
  PNHAK2.v8_at M9 (F + 784) bb -> PNHAK2.hvec F M9 b k stk -> L5.u64_at RSEGS M9 (V2 - 104) (F + 856) ->
  (forall (fx10 : FPState) (R10 : bvmap 5 word) (M10 : word -> option byte) (model10 : Model) (LK10 : list fframe) (A10 : list (Z * Z)),
      Bv W ((PM.sr_qc src, PM.CHUNK) :: PGV8.v8_own bb ++ PM.vs_own nb ++ PM.vs_own str ++ PM.vs_own s) M10 model10 LK10 cr9 A10 -> rinvH R R10 V2 cls F ->
      PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M10 ->
      getr R10 (reg 21) = Z_to_bv 64 (F + 96) -> getr R10 (reg 22) = Z_to_bv 64 (F + 464) -> getr R10 (reg 23) = Z_to_bv 64 (F + 1024) ->
      getr R10 (reg 26) = Z_to_bv 64 18446744073709551608 ->
      PNHAK2.hbase F M10 s str sm -> PNHAK2.hsrc F M10 src -> PM.vstr_at RSEGS PMSPA.accA M10 (F + 808) nb -> PNHAK2.v8_at M10 (F + 784) bb ->
      srealizes RSEGS SCFG (@L5A.cfg fx10 R10 0xa8500 M10 model10) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx9 R9 0xab620 M9 model9) K.
Proof.
  intros BI RI K0 LS R1a R10 R21 R22 R23 R26 HB0 HS0 TB0 NB0 BB0 HV0 FT0 KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PNHAK2.hf F) by (unfold PNHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  set (X := PGV8.v8_own bb ++ PM.vs_own nb ++ PM.vs_own tb ++ PM.vs_own str ++ PM.vs_own s) in *.
  assert (INs : forall x, In x (PM.vs_own str ++ PM.vs_own s) -> In x X) by (intros x Hx; subst X; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hx).
  assert (INtb : forall x, In x (PM.vs_own tb) -> In x X) by (intros x Hx; subst X; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (INnb : forall x, In x (PM.vs_own nb) -> In x X) by (intros x Hx; subst X; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (INbb : forall x, In x (PGV8.v8_own bb) -> In x X) by (intros x Hx; subst X; apply in_or_app; left; exact Hx).
  cbn [app] in B1.
  assert (NQB : PM.sr_qc src <> b).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). cbn [map fst] in ND.
    intros E. rewrite E in ND. inversion ND as [|x0 l0 NI ND1]. apply NI. constructor. }
  assert (OSZ : shadow_zero M9 (V2 - 128) 16) by (eapply PNHASK.own_shz; first [exact BI | eassumption]).
  pose proof HV0 as (VE0 & VD0 & VA0). pose proof LS as (LSB & LSL & LSS & LSE).
  unfold PNSAX.vec_dtor_spec in VDT. change PNM.BSZ with 40 in VDT.
  apply (VDT fx9 R9 M9 model9 K _ FF' LK9 A9 cr9 (V2 - 104) (F + 856) b k (V2 - 128) 0xa84e4 stk B1 B2 K0).
  { eapply PNHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PNHASK.callee_roomB; first [exact BI | eassumption | lia]. }
  { eapply PNHASK.callee_rs; eassumption. }
  { rewrite L5K.rl10. exact R10. }
  { lia. }
  { clear - SHI CLS SPT. lia. }
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (PMARS1.acc_of_shadow_zero M9 (V2 - 128) 16 (V2 - 104) 8 OSZ); [| lia| lia].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). exact FT0. }
  { exists (F, 5, V2 - 128 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  { clear - FM8. lia. }
  { exact VD0. }
  { exact VA0. }
  { exact VE0. }
  { right. left. reflexivity. }
  { exact LSB. }
  intros fx' R' M' model' LK' Aw' RP' BASE' HP' MRT' INCLK' INCA' AM' HH'.
  change (PMSPA.pm_scr 1) with 14336 in HP'.
  rewrite (L5ADHR.lb_remove_skip b (PM.sr_qc src) PM.CHUNK _ NQB), L5ADHR.lb_remove_head in HP', HH'.
  assert (WFI : PNHAK2.wfi F [(F + 856, 24)]) by (apply PNHAK2.wfi_cons; [cbn [fst snd]; left; lia| apply PNHAK2.wfi_nil]).
  assert (LS' : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M').
  { apply (PNHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 14336 [(F + 856, 24)] M9 M' HP'); [| exact LS].
    apply PNHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PNHAK.far_nil]. }
  assert (HH'' : ri_inv HI (((PM.sr_qc src, PM.CHUNK) :: X) ++ LB) FF' LK' cr9 Aw' M' (vml_of model')) by exact HH'.
  assert (BI' : Bv W ((PM.sr_qc src, PM.CHUNK) :: X) M' model' LK' cr9 Aw').
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ ((PM.sr_qc src, PM.CHUNK) :: X) _ M9 model9 LK9 cr9 A9 M' model' LK' cr9 Aw' 14336 [(F + 856, 24)] BI HP' HH'' AM' MRT' INCA' INCLK').
    - lia.
    - clear - CLS; lia.
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
    - intros a X0. exact X0. }
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr9 Aw' BI')
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid Aw' model') in *. set (MV' := mrestrict H' M') in *.
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R9 R' V2 cls F RI RP').
  pose proof RI' as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
  assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R9 R' 21 RP') by inl; exact R21).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 464)) by (rewrite (cs_of_preserved R9 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 1024)) by (rewrite (cs_of_preserved R9 R' 23 RP') by inl; exact R23).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (cs_of_preserved R9 R' 26 RP') by inl; exact R26).
  assert (FIN9 : In (F, 5, V2 - 128 + 32) (FF' ++ LK9)) by (apply in_or_app; left; left; reflexivity).
  assert (INX : forall x, In x X -> In x ((PM.sr_qc src, PM.CHUNK) :: (b, 40 * 2 ^ k) :: X ++ LB) /\ In x ((PM.sr_qc src, PM.CHUNK) :: X ++ LB)).
  { intros x Hx. split; [right; right; apply in_or_app; left; exact Hx| right; apply in_or_app; left; exact Hx]. }
  assert (HB' : PNHAK2.hbase F M' s str sm).
  { eapply PNHAK2.hbase_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HB0 | exact FHF | exact FIN9 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; apply INX; apply INs; exact Hx)
      | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil]) | lia ]. }
  assert (HS' : PNHAK2.hsrc F M' src).
  { eapply PNHAK2.hsrc_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact HS0 | exact FHF | exact FIN9 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | (left; reflexivity) | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil]) | lia ]. }
  assert (TB' : PM.vstr_at RSEGS PMSPA.accA M' (F + 832) tb).
  { eapply PNHAK2.vstr_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact TB0 | exact FHF | exact FIN9 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; apply INX; apply INtb; exact Hx)
      | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil]) | lia ]. }
  assert (NB' : PM.vstr_at RSEGS PMSPA.accA M' (F + 808) nb).
  { eapply PNHAK2.vstr_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact NB0 | exact FHF | exact FIN9 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; apply INX; apply INnb; exact Hx)
      | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil]) | lia ]. }
  assert (BB' : PNHAK2.v8_at M' (F + 784) bb).
  { eapply PNHAK2.v8_keep_callee; first [ exact LY | exact HIok | exact B1 | exact HP' | exact BB0 | exact FHF | exact FIN9 | exact WFI | exact (or_introl eq_refl)
      | (split; reflexivity) | (intros x Hx; apply INX; apply INbb; exact Hx)
      | (apply PNHAK2.wapart_cons; [cbn [fst snd]; lia| apply PNHAK2.wapart_nil]) | lia ]. }
  assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 128 + 144 <= F \/ F + 2048 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  assert (AV832 : L5A.avis H' (F + 832) 8) by (apply (PNHAK.avis_sub H' F 2048 (F + 832) 8 FV'); lia).
  assert (AV848 : L5A.avis H' (F + 848) 8) by (apply (PNHAK.avis_sub H' F 2048 (F + 848) 8 FV'); lia).
  assert (FIN' : In (F, 5, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  assert (PF10 : PNHAK2.pfoot F (V2 - 128) V2 (fun _ => False)) by (intros a []).
  assert (OAX : forall o n, PNHAK2.oav (fun _ => False) o n) by (intros o n x Hx; split; intros []).
  destruct tb as [nt | c nt p].
  - (* [comment removed for export] *)
    destruct TB' as (_ & _ & (Hnt & TBB)).
    assert (TBv : L5.u8_at RSEGS MV' (F + 832) (2 * nt))
      by (apply (proj2 (L5A.u8_at_vis H' M' (F + 832) (2 * nt) (PNHAK.avis_sub H' (F + 832) 8 (F + 832) 1 AV832 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TBB).
    pose proof (PMF.even_byte nt) as EVB.
    LeanFeed.pfeed P (PNAHP3.bhaIs_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 36%nat => 2 * nt | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - Hnt; lia) | exact F32
                       | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact TBv | exact EVB | (unfold PNAHP3.aligned; exact V2A) ]).
    destruct P as (fx10 & R10' & M10v & MG10 & iFR & iFZ & (iMS & iKS & iR10)).
    apply (apiece L ar C HI LYa HIok _ FF' LK' cr9 Aw' M' model' fx' fx10 R' 0xa84e4 R10' 0xa8500 M10v (fun _ => False) K HH' AM' iMS MG10).
    { intros a Ha Hna. apply iFZ; exact Ha. }
    { intros a Ha []. }
    intros M10 model10 HH10 AM10 MRT10 HID10 VIS10 MGM10 FR10 VV10.
    assert (BI10 : Bv W ((PM.sr_qc src, PM.CHUNK) :: X) M10 model10 LK' cr9 Aw').
    { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr9 Aw' M10 model10 (fun _ => False) BI' HH10 AM10 MRT10 MGM10 FR10).
      intros a []. }
    apply (KONT fx10 R10' M10 model10 LK' Aw').
    + subst X. cbn [PM.vs_own app] in BI10. exact BI10.
    + apply (rinvH_ks R R' R10' V2 cls F PNAHP3.KS_bhaIs RI' iKS); vm_compute; reflexivity.
    + apply (PNHAK.ls_piece _ M' M10 (fun _ => False) FR10); [intros a []| exact LS'].
    + rewrite (iKS 21%nat) by inl. exact Y21.
    + rewrite (iKS 22%nat) by inl. exact Y22.
    + rewrite (iKS 23%nat) by inl. exact Y23.
    + rewrite (iKS 26%nat) by inl. exact Y26.
    + apply (PNHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 s str sm);
        [intros x Hx; right; apply in_or_app; left; apply INs; exact Hx| apply OAX| apply OAX| apply OAX| exact HB'].
    + apply (PNHAK2.hsrc_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 src);
        [left; reflexivity| apply OAX| exact HS'].
    + apply (PNHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 (F + 808) nb);
        [intros x Hx; right; apply in_or_app; left; apply INnb; exact Hx| clear - FR; lia| clear - FR; lia| apply OAX| exact NB'].
    + apply (PNHAK2.v8_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 (F + 784) bb);
        [intros x Hx; right; apply in_or_app; left; apply INbb; exact Hx| clear - FR; lia| clear - FR; lia| apply OAX| exact BB'].
  - (* [comment removed for export] *)
    destruct TB' as (_ & _ & (TW0 & TW8 & TW16 & Hnt & Hc & Hc2 & TBP & _)).
    assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by lia.
    pose proof (PMF.u8_of_u64 RSEGS M' _ _ Hc64 TW0) as TBB.
    pose proof (PMF.odd_byte c Hc2 ltac:(lia)) as ODB.
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)) as HVB.
    assert (TBv : L5.u8_at RSEGS MV' (F + 832) ((c + 1) mod 256))
      by (apply (proj2 (L5A.u8_at_vis H' M' (F + 832) _ (PNHAK.avis_sub H' (F + 832) 8 (F + 832) 1 AV832 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TBB).
    assert (TW0v : L5.u64_at RSEGS MV' (F + 832) (c + 1)) by (apply (proj2 (L5A.u64_at_vis H' M' (F + 832) _ AV832 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW0).
    assert (TW16v : L5.u64_at RSEGS MV' (F + 848) p)
      by (apply (proj2 (L5A.u64_at_vis H' M' (F + 848) _ AV848 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); replace (F + 848) with (F + 832 + 16) by lia; exact TW16).
    assert (INP : In (p, c) (((PM.sr_qc src, PM.CHUNK) :: X) ++ LB)) by (right; apply in_or_app; left; apply INtb; left; reflexivity).
    destruct (PNHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ p c HH' INP) as (P0 & _ & _ & _ & _ & P47 & _).
    LeanFeed.pfeed P (PNAHP3.bhaIl_conc fx' R' MV' (fun j => match j with 2%nat => V2 | 36%nat => (c + 1) mod 256 | 37%nat => c + 1 | 38%nat => p
                                                   | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - HVB; lia) | (clear - Hc64; lia) | (clear - P0 P47 Hc; lia)
                       | exact F32 | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact TBv | exact TW0v | exact TW16v | exact ODB
                       | (unfold PNAHP3.aligned; exact V2A) ]).
    destruct P as (fx10 & R10' & M10v & MG10 & iFR & iFZ & (iMS & iKS & iR1 & iR10 & iR11)).
    apply (apiece L ar C HI LYa HIok _ FF' LK' cr9 Aw' M' model' fx' fx10 R' 0xa84e4 R10' 0xd39ac M10v (fun _ => False) K HH' AM' iMS MG10).
    { intros a Ha Hna. apply iFZ; exact Ha. }
    { intros a Ha []. }
    intros M10 model10 HH10 AM10 MRT10 HID10 VIS10 MGM10 FR10 VV10.
    assert (BI10 : Bv W ((PM.sr_qc src, PM.CHUNK) :: X) M10 model10 LK' cr9 Aw').
    { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr9 Aw' M10 model10 (fun _ => False) BI' HH10 AM10 MRT10 MGM10 FR10).
      intros a []. }
    assert (RI10 : rinvH R R10' V2 cls F) by (apply (rinvH_ks R R' R10' V2 cls F PNAHP3.KS_bhaIl RI' iKS); vm_compute; reflexivity).
    assert (LS10 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M10) by (apply (PNHAK.ls_piece _ M' M10 (fun _ => False) FR10); [intros a []| exact LS']).
    assert (HB10 : PNHAK2.hbase F M10 s str sm).
    { apply (PNHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 s str sm);
        [intros x Hx; right; apply in_or_app; left; apply INs; exact Hx| apply OAX| apply OAX| apply OAX| exact HB']. }
    assert (HS10 : PNHAK2.hsrc F M10 src).
    { apply (PNHAK2.hsrc_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 src);
        [left; reflexivity| apply OAX| exact HS']. }
    assert (NB10 : PM.vstr_at RSEGS PMSPA.accA M10 (F + 808) nb).
    { apply (PNHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 (F + 808) nb);
        [intros x Hx; right; apply in_or_app; left; apply INnb; exact Hx| clear - FR; lia| clear - FR; lia| apply OAX| exact NB']. }
    assert (BB10 : PNHAK2.v8_at M10 (F + 784) bb).
    { apply (PNHAK2.v8_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) HH' FIN' FHF (V2 - 128) V2 (fun _ => False) M' M10 SLOW SHW FR10 PF10 (F + 784) bb);
        [intros x Hx; right; apply in_or_app; left; apply INbb; exact Hx| clear - FR; lia| clear - FR; lia| apply OAX| exact BB']. }
    pose proof BI10 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    (* [comment removed for export] *)
    assert (ELB : lb_remove p (((PM.sr_qc src, PM.CHUNK) :: X) ++ LB) = ((PM.sr_qc src, PM.CHUNK) :: PGV8.v8_own bb ++ PM.vs_own nb ++ PM.vs_own str ++ PM.vs_own s) ++ LB).
    { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ C1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
      assert (EL : ((PM.sr_qc src, PM.CHUNK) :: X) ++ LB = ((PM.sr_qc src, PM.CHUNK) :: PGV8.v8_own bb ++ PM.vs_own nb) ++ (p, c) :: ((PM.vs_own str ++ PM.vs_own s) ++ LB))
        by (subst X; cbn [PM.vs_own app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity).
      rewrite (PNHAK3.lb_remove_at p c _ _ _ EL); [| exact ND]. cbn [app]. rewrite <- ?app_assoc. cbn [app]. rewrite <- ?app_assoc. reflexivity. }
    assert (ASX : L5CA.astk ar M10 (V2 - 128) (PMSPA.pm_scr 0) /\ shadow_zero M10 (V2 - 128 - PMSPA.pm_scr 0) (PMSPA.pm_scr 0 / 8))
      by (eapply PNHASK.callee_stack; first [exact BI10 | eassumption | lia]).
    destruct ASX as (AS0 & _).
    change (PMSPA.pm_scr 0) with 12288 in AS0.
    unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMA.AD ADDR_A] in OPD.
    apply (OPD fx10 R10' M10 model10 K _ FF' LK' Aw' cr9 p c (V2 - 128) 0xa8500 C1 C2 K0 INP).
    { rewrite L5K.rl10. exact iR10. }
    { rewrite L5K.rl1. exact iR1. }
    { split; [lia| reflexivity]. }
    { rewrite L5K.rl2. rewrite (iKS 2%nat) by inl. exact Y2. }
    { rewrite L5K.rl4. rewrite (iKS 4%nat) by inl. rewrite Y4. exact TP. }
    { replace (V2 - 128) with (V2 - 128 - 0) by lia. apply (L5SAR.astk_sub ar M10 M10 (V2 - 128) 12288 0 PMSPA.OPDEL_SCR AS0 (fun _ X0 => X0)); [lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia|].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    intros fx2 R2' M2' model2' Aw2 RP2 HPo MRT2 INCA2 AM2 HHo.
    rewrite ELB in HPo, HHo.
    unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HPo.
    set (X2l := PGV8.v8_own bb ++ PM.vs_own nb ++ PM.vs_own str ++ PM.vs_own s) in *.
    assert (BI2 : Bv W ((PM.sr_qc src, PM.CHUNK) :: X2l) M2' model2' LK' cr9 Aw2).
    { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ ((PM.sr_qc src, PM.CHUNK) :: X2l) _ M10 model10 LK' cr9 Aw' M2' model2' LK' cr9 Aw2 4096 [] BI10 HPo HHo AM2 MRT2 INCA2 (incl_refl _)).
      - lia.
      - clear - CLS; lia.
      - intros rr a [].
      - intros a _ _ rr [].
      - intros a X0. exact X0. }
    assert (LS2 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M2') by (apply (PNHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 4096 [] M10 M2' HPo PNHAK.far_nil LS10)).
    assert (FINX : In (F, 5, V2 - 128 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
    assert (WFN : PNHAK2.wfi F []) by apply PNHAK2.wfi_nil.
    assert (IN2s : forall x, In x (PM.vs_own str ++ PM.vs_own s) -> In x (((PM.sr_qc src, PM.CHUNK) :: X2l) ++ LB))
      by (intros x Hx; right; apply in_or_app; left; subst X2l; apply in_or_app; right; apply in_or_app; right; exact Hx).
    assert (IN2nb : forall x, In x (PM.vs_own nb) -> In x (((PM.sr_qc src, PM.CHUNK) :: X2l) ++ LB))
      by (intros x Hx; right; apply in_or_app; left; subst X2l; apply in_or_app; right; apply in_or_app; left; exact Hx).
    assert (IN2bb : forall x, In x (PGV8.v8_own bb) -> In x (((PM.sr_qc src, PM.CHUNK) :: X2l) ++ LB))
      by (intros x Hx; right; apply in_or_app; left; subst X2l; apply in_or_app; left; exact Hx).
    apply (KONT fx2 R2' M2' model2' LK' Aw2).
    + exact BI2.
    + exact (rinvH_pres R R10' R2' V2 cls F RI10 RP2).
    + exact LS2.
    + rewrite (cs_of_preserved R10' R2' 21 RP2) by inl; rewrite (iKS 21%nat) by inl; exact Y21.
    + rewrite (cs_of_preserved R10' R2' 22 RP2) by inl; rewrite (iKS 22%nat) by inl; exact Y22.
    + rewrite (cs_of_preserved R10' R2' 23 RP2) by inl; rewrite (iKS 23%nat) by inl; exact Y23.
    + rewrite (cs_of_preserved R10' R2' 26 RP2) by inl; rewrite (iKS 26%nat) by inl; exact Y26.
    + eapply PNHAK2.hbase_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact HB10 | exact FHF | exact FINX | exact WFN | exact (or_introl eq_refl)
        | (split; reflexivity) | (intros x Hx; right; apply in_or_app; left; apply INs; exact Hx) | (intros x Hx; apply IN2s; exact Hx)
        | apply PNHAK2.wapart_nil | lia ].
    + eapply PNHAK2.hsrc_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact HS10 | exact FHF | exact FINX | exact WFN | exact (or_introl eq_refl)
        | (split; reflexivity) | (left; reflexivity) | apply PNHAK2.wapart_nil | lia ].
    + eapply PNHAK2.vstr_keep_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact NB10 | exact FHF | exact FINX | exact WFN | exact (or_introl eq_refl)
        | (split; reflexivity) | (intros x Hx; right; apply in_or_app; left; apply INnb; exact Hx) | (intros x Hx; apply IN2nb; exact Hx)
        | apply PNHAK2.wapart_nil | lia ].
    + eapply PNHAK2.v8_keep_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact BB10 | exact FHF | exact FINX | exact WFN | exact (or_introl eq_refl)
        | (split; reflexivity) | (intros x Hx; right; apply in_or_app; left; apply INbb; exact Hx) | (intros x Hx; apply IN2bb; exact Hx)
        | apply PNHAK2.wapart_nil | lia ].
Qed.
End Stage.
End SCFG_1.
End PNHA8.
