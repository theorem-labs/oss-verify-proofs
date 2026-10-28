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

Module PNHA8b.
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

(* [comment removed for export] *)
Lemma pieceJ (fx11 : FPState) (R11 : bvmap 5 word) (M11 : word -> option byte) (model11 : Model) (K : TSet)
      (LK11 : list fframe) (cr11 : credit) (A11 : list (Z * Z)) (s str : PM.vstr) (bb : PGV8.v8) (sm : PM.strm) (src : PM.srcst) (g : PNST.st) :
  Bv W ((PM.sr_qc src, PM.CHUNK) :: PGV8.v8_own bb ++ PM.vs_own str ++ PM.vs_own s) M11 model11 LK11 cr11 A11 -> rinvH R R11 V2 cls F -> K [] ->
  PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M11 ->
  getr R11 (reg 21) = Z_to_bv 64 (F + 96) -> getr R11 (reg 22) = Z_to_bv 64 (F + 464) -> getr R11 (reg 23) = Z_to_bv 64 (F + 1024) ->
  getr R11 (reg 26) = Z_to_bv 64 18446744073709551608 ->
  PNHAK2.hbase F M11 s str sm -> PNHAK2.hsrc F M11 src -> PNHAK2.v8_at M11 (F + 784) bb ->
  (forall (fx12 : FPState) (R12 : bvmap 5 word) (M12 : word -> option byte) (model12 : Model) (LK12 : list fframe) (A12 : list (Z * Z)),
      Bv W ((PM.sr_qc src, PM.CHUNK) :: PGV8.v8_own bb ++ PM.vs_own str ++ PM.vs_own s) M12 model12 LK12 cr11 A12 -> rinvH R R12 V2 cls F ->
      PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M12 ->
      getr R12 (reg 1) = Z_to_bv 64 0xa852c -> getr R12 (reg 10) = Z_to_bv 64 (V2 - 104) ->
      getr R12 (reg 21) = Z_to_bv 64 (F + 96) -> getr R12 (reg 22) = Z_to_bv 64 (F + 464) -> getr R12 (reg 23) = Z_to_bv 64 (F + 1024) ->
      getr R12 (reg 26) = Z_to_bv 64 18446744073709551608 ->
      PNHAK2.hbase F M12 s str sm -> PNHAK2.hsrc F M12 src -> PNHAK2.v8_at M12 (F + 784) bb -> L5.u64_at RSEGS M12 (V2 - 104) (F + 784) ->
      srealizes RSEGS SCFG (@L5A.cfg fx12 R12 0xab9e0 M12 model12) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx11 R11 0xa851c M11 model11) K.
Proof.
  intros BI RI K0 LS R21 R22 R23 R26 HB0 HS0 BB0 KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PNHAK2.hf F) by (unfold PNHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  set (X := PGV8.v8_own bb ++ PM.vs_own str ++ PM.vs_own s) in *.
  assert (INs : forall x, In x (PM.vs_own str ++ PM.vs_own s) -> In x X) by (intros x Hx; subst X; apply in_or_app; right; exact Hx).
  assert (INbb : forall x, In x (PGV8.v8_own bb) -> In x X) by (intros x Hx; subst X; apply in_or_app; left; exact Hx).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M11 model11 LK11 cr11 A11 BI)
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid A11 model11) in *. set (MV' := mrestrict H' M11) in *.
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 128 + 144 <= F \/ F + 2048 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  LeanFeed.pfeed P (PNAHP3.bhaJ_conc fx11 R11 MV' (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R11 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                     | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | (unfold PNAHP3.aligned; exact V2A) ]).
  destruct P as (fx12 & R12 & M12v & MG12 & jFR & jFZ & (jMS & jKS & jR1 & jR10 & jT)).
  set (W12 := fun a => V2 - 104 <= a < V2 - 104 + 8).
  apply (apiece L ar C HI LYa HIok _ FF' LK11 cr11 A11 M11 model11 fx11 fx12 R11 0xa851c R12 0xab9e0 M12v W12 K B1 B2 jMS MG12).
  { intros a Ha Hna. apply jFZ; [exact Ha|]. intros X0; apply Hna; subst W12; cbn beta; clear - X0; lia. }
  { intros a Ha Wa. subst W12; cbn beta in Wa. split.
    - apply stack_client; clear - Wa SLO SHI SPT CLS V2R; lia.
    - clear - Wa FR V2R. lia. }
  intros M12 model12 HH12 AM12 MRT12 HID12 VIS12 MGM12 FR12 VV12. change (mrestrict H' M12 = M12v) in VIS12.
  assert (BI12 : Bv W ((PM.sr_qc src, PM.CHUNK) :: X) M12 model12 LK11 cr11 A11).
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M11 model11 LK11 cr11 A11 M12 model12 W12 BI HH12 AM12 MRT12 MGM12 FR12).
    intros a Wa. subst W12; cbn beta in Wa. change (ff_bytes 5) with 2048. change (2048 / 8) with 256.
    left. split; [clear - Wa CLS; lia|]. unfold tocell. clear - Wa CLS. lia. }
  assert (FIN' : In (F, 5, V2 - 128 + 32) (FF' ++ LK11)) by (apply in_or_app; left; left; reflexivity).
  assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  assert (PF12 : PNHAK2.pfoot F (V2 - 128) V2 W12) by (intros a Wa; subst W12; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (OAY : forall o n, F <= o -> o + n <= F + 2048 -> PNHAK2.oav W12 o n).
  { intros o n H1 H2 x Hx. subst W12; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H1 H2 SX FBIG FR FM8 V2R SLO FCEIL CLS; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (KONT fx12 R12 M12 model12 LK11 A11 BI12).
  - apply (rinvH_ks R R11 R12 V2 cls F PNAHP3.KS_bhaJ RI jKS); vm_compute; reflexivity.
  - apply (PNHAK.ls_piece _ M11 M12 W12 FR12); [| exact LS]. intros a Wa. subst W12; cbn beta in Wa. clear - Wa FR V2R. lia.
  - exact jR1.
  - exact jR10.
  - rewrite (jKS 21%nat) by inl. exact R21.
  - rewrite (jKS 22%nat) by inl. exact R22.
  - rewrite (jKS 23%nat) by inl. exact R23.
  - rewrite (jKS 26%nat) by inl. exact R26.
  - apply (PNHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) B1 FIN' FHF (V2 - 128) V2 W12 M11 M12 SLOW SHW FR12 PF12 s str sm);
      [intros x Hx; right; apply in_or_app; left; apply INs; exact Hx| apply OAY; lia| apply OAY; lia| apply OAY; lia| exact HB0].
  - apply (PNHAK2.hsrc_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) B1 FIN' FHF (V2 - 128) V2 W12 M11 M12 SLOW SHW FR12 PF12 src);
      [left; reflexivity| apply OAY; lia| exact HS0].
  - apply (PNHAK2.v8_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) B1 FIN' FHF (V2 - 128) V2 W12 M11 M12 SLOW SHW FR12 PF12 (F + 784) bb);
      [intros x Hx; right; apply in_or_app; left; apply INbb; exact Hx| clear - FR; lia| clear - FR; lia| apply OAY; lia| exact BB0].
  - apply (PNHAK.u64_vis H' M12 M12v (V2 - 104) _ VV12); [| clear - V2R; lia| clear - V2R; lia| exact jT].
    apply (PNHAK.avis_sub H' (V2 - 128) (V2 + cls - (V2 - 128)) (V2 - 104) 8 SPV'); clear - CLS; lia.
Qed.

Lemma stage8b (OPD : PMA.opdel_spec L ar HI) (fx10 : FPState) (R10 : bvmap 5 word) (M10 : word -> option byte) (model10 : Model) (K : TSet)
      (LK10 : list fframe) (cr10 : credit) (A10 : list (Z * Z)) (s str nb : PM.vstr) (bb : PGV8.v8) (sm : PM.strm) (src : PM.srcst) (g : PNST.st) :
  Bv W ((PM.sr_qc src, PM.CHUNK) :: PGV8.v8_own bb ++ PM.vs_own nb ++ PM.vs_own str ++ PM.vs_own s) M10 model10 LK10 cr10 A10 -> rinvH R R10 V2 cls F -> K [] ->
  PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M10 ->
  getr R10 (reg 21) = Z_to_bv 64 (F + 96) -> getr R10 (reg 22) = Z_to_bv 64 (F + 464) -> getr R10 (reg 23) = Z_to_bv 64 (F + 1024) ->
  getr R10 (reg 26) = Z_to_bv 64 18446744073709551608 ->
  PNHAK2.hbase F M10 s str sm -> PNHAK2.hsrc F M10 src -> PM.vstr_at RSEGS PMSPA.accA M10 (F + 808) nb -> PNHAK2.v8_at M10 (F + 784) bb ->
  (forall (fx12 : FPState) (R12 : bvmap 5 word) (M12 : word -> option byte) (model12 : Model) (LK12 : list fframe) (A12 : list (Z * Z)),
      Bv W ((PM.sr_qc src, PM.CHUNK) :: PGV8.v8_own bb ++ PM.vs_own str ++ PM.vs_own s) M12 model12 LK12 cr10 A12 -> rinvH R R12 V2 cls F ->
      PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M12 ->
      getr R12 (reg 1) = Z_to_bv 64 0xa852c -> getr R12 (reg 10) = Z_to_bv 64 (V2 - 104) ->
      getr R12 (reg 21) = Z_to_bv 64 (F + 96) -> getr R12 (reg 22) = Z_to_bv 64 (F + 464) -> getr R12 (reg 23) = Z_to_bv 64 (F + 1024) ->
      getr R12 (reg 26) = Z_to_bv 64 18446744073709551608 ->
      PNHAK2.hbase F M12 s str sm -> PNHAK2.hsrc F M12 src -> PNHAK2.v8_at M12 (F + 784) bb -> L5.u64_at RSEGS M12 (V2 - 104) (F + 784) ->
      srealizes RSEGS SCFG (@L5A.cfg fx12 R12 0xab9e0 M12 model12) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx10 R10 0xa8500 M10 model10) K.
Proof.
  intros BI RI K0 LS R21 R22 R23 R26 HB0 HS0 NB0 BB0 KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PNHAK2.hf F) by (unfold PNHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  set (X := PGV8.v8_own bb ++ PM.vs_own nb ++ PM.vs_own str ++ PM.vs_own s) in *.
  assert (INs : forall x, In x (PM.vs_own str ++ PM.vs_own s) -> In x X) by (intros x Hx; subst X; apply in_or_app; right; apply in_or_app; right; exact Hx).
  assert (INnb : forall x, In x (PM.vs_own nb) -> In x X) by (intros x Hx; subst X; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (INbb : forall x, In x (PGV8.v8_own bb) -> In x X) by (intros x Hx; subst X; apply in_or_app; left; exact Hx).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M10 model10 LK10 cr10 A10 BI)
    as ((VW' & VIC' & VSB' & VUAR' & VMS') & VOWN' & (VFD' & VFW' & VFSW' & VFLC' & VFLW') & (FLCc' & FLV' & FV' & SPV' & FSV')).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid A10 model10) in *. set (MV' := mrestrict H' M10) in *.
  assert (SLOW : ahl_ceil ar <= V2 - 128) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 128) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  assert (Q1 : 4096 <= F <= 140737488353280) by (clear - FR; lia).
  assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
  assert (Q3 : V2 - 128 + 144 <= F \/ F + 2048 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
  assert (Q5 : L5.writable RSEGS MV' (V2 - 128) 128) by (eapply L5.writable_sub; [exact VW'| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV' (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC').
  assert (AV808 : L5A.avis H' (F + 808) 8) by (apply (PNHAK.avis_sub H' F 2048 (F + 808) 8 FV'); lia).
  assert (AV824 : L5A.avis H' (F + 824) 8) by (apply (PNHAK.avis_sub H' F 2048 (F + 824) 8 FV'); lia).
  assert (FIN' : In (F, 5, V2 - 128 + 32) (FF' ++ LK10)) by (apply in_or_app; left; left; reflexivity).
  assert (PF0 : PNHAK2.pfoot F (V2 - 128) V2 (fun _ => False)) by (intros a []).
  assert (OAX : forall o n, PNHAK2.oav (fun _ => False) o n) by (intros o n x Hx; split; intros []).
  destruct nb as [nt | c nt p].
  - (* [comment removed for export] *)
    destruct NB0 as (_ & _ & (Hnt & NBB)).
    assert (NBv : L5.u8_at RSEGS MV' (F + 808) (2 * nt))
      by (apply (proj2 (L5A.u8_at_vis H' M10 (F + 808) (2 * nt) (PNHAK.avis_sub H' (F + 808) 8 (F + 808) 1 AV808 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact NBB).
    pose proof (PMF.even_byte nt) as EVB.
    LeanFeed.pfeed P (PNAHP3.bhaI2s_conc fx10 R10 MV' (fun j => match j with 2%nat => V2 | 36%nat => 2 * nt | 40%nat => F | 41%nat => fl | 58%nat => U R10 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - Hnt; lia) | exact F32
                       | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact NBv | exact EVB | (unfold PNAHP3.aligned; exact V2A) ]).
    destruct P as (fx11 & R11 & M11v & MG11 & iFR & iFZ & (iMS & iKS & iR10)).
    apply (apiece L ar C HI LYa HIok _ FF' LK10 cr10 A10 M10 model10 fx10 fx11 R10 0xa8500 R11 0xa851c M11v (fun _ => False) K B1 B2 iMS MG11).
    { intros a Ha Hna. apply iFZ; exact Ha. }
    { intros a Ha []. }
    intros M11 model11 HH11 AM11 MRT11 HID11 VIS11 MGM11 FR11 VV11.
    assert (BI11 : Bv W ((PM.sr_qc src, PM.CHUNK) :: X) M11 model11 LK10 cr10 A10).
    { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M10 model10 LK10 cr10 A10 M11 model11 (fun _ => False) BI HH11 AM11 MRT11 MGM11 FR11).
      intros a []. }
    apply (pieceJ fx11 R11 M11 model11 K LK10 cr10 A10 s str bb sm src g).
    + subst X. cbn [PM.vs_own app] in BI11. exact BI11.
    + apply (rinvH_ks R R10 R11 V2 cls F PNAHP3.KS_bhaI2s RI iKS); vm_compute; reflexivity.
    + exact K0.
    + apply (PNHAK.ls_piece _ M10 M11 (fun _ => False) FR11); [intros a []| exact LS].
    + rewrite (iKS 21%nat) by inl. exact R21.
    + rewrite (iKS 22%nat) by inl. exact R22.
    + rewrite (iKS 23%nat) by inl. exact R23.
    + rewrite (iKS 26%nat) by inl. exact R26.
    + apply (PNHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) B1 FIN' FHF (V2 - 128) V2 (fun _ => False) M10 M11 SLOW SHW FR11 PF0 s str sm);
        [intros x Hx; right; apply in_or_app; left; apply INs; exact Hx| apply OAX| apply OAX| apply OAX| exact HB0].
    + apply (PNHAK2.hsrc_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) B1 FIN' FHF (V2 - 128) V2 (fun _ => False) M10 M11 SLOW SHW FR11 PF0 src);
        [left; reflexivity| apply OAX| exact HS0].
    + apply (PNHAK2.v8_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) B1 FIN' FHF (V2 - 128) V2 (fun _ => False) M10 M11 SLOW SHW FR11 PF0 (F + 784) bb);
        [intros x Hx; right; apply in_or_app; left; apply INbb; exact Hx| clear - FR; lia| clear - FR; lia| apply OAX| exact BB0].
    + exact KONT.
  - (* [comment removed for export] *)
    destruct NB0 as (_ & _ & (TW0 & TW8 & TW16 & Hnt & Hc & Hc2 & TBP & _)).
    assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by lia.
    pose proof (PMF.u8_of_u64 RSEGS M10 _ _ Hc64 TW0) as NBB.
    pose proof (PMF.odd_byte c Hc2 ltac:(lia)) as ODB.
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)) as HVB.
    assert (NBv : L5.u8_at RSEGS MV' (F + 808) ((c + 1) mod 256))
      by (apply (proj2 (L5A.u8_at_vis H' M10 (F + 808) _ (PNHAK.avis_sub H' (F + 808) 8 (F + 808) 1 AV808 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact NBB).
    assert (TW0v : L5.u64_at RSEGS MV' (F + 808) (c + 1)) by (apply (proj2 (L5A.u64_at_vis H' M10 (F + 808) _ AV808 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW0).
    assert (TW16v : L5.u64_at RSEGS MV' (F + 824) p)
      by (apply (proj2 (L5A.u64_at_vis H' M10 (F + 824) _ AV824 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); replace (F + 824) with (F + 808 + 16) by lia; exact TW16).
    assert (INP : In (p, c) (((PM.sr_qc src, PM.CHUNK) :: X) ++ LB)) by (right; apply in_or_app; left; apply INnb; left; reflexivity).
    destruct (PNHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ p c B1 INP) as (P0 & _ & _ & _ & _ & P47 & _).
    LeanFeed.pfeed P (PNAHP3.bhaI2l_conc fx10 R10 MV' (fun j => match j with 2%nat => V2 | 36%nat => (c + 1) mod 256 | 37%nat => c + 1 | 38%nat => p
                                                   | 40%nat => F | 41%nat => fl | 58%nat => U R10 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - HVB; lia) | (clear - Hc64; lia) | (clear - P0 P47 Hc; lia)
                       | exact F32 | exact VFD' | exact VFW' | exact VFSW' | exact VFLW' | exact Q5 | exact Q6 | exact NBv | exact TW0v | exact TW16v | exact ODB
                       | (unfold PNAHP3.aligned; exact V2A) ]).
    destruct P as (fx11 & R11 & M11v & MG11 & iFR & iFZ & (iMS & iKS & iR1 & iR10 & iR11)).
    apply (apiece L ar C HI LYa HIok _ FF' LK10 cr10 A10 M10 model10 fx10 fx11 R10 0xa8500 R11 0xd39ac M11v (fun _ => False) K B1 B2 iMS MG11).
    { intros a Ha Hna. apply iFZ; exact Ha. }
    { intros a Ha []. }
    intros M11 model11 HH11 AM11 MRT11 HID11 VIS11 MGM11 FR11 VV11.
    assert (BI11 : Bv W ((PM.sr_qc src, PM.CHUNK) :: X) M11 model11 LK10 cr10 A10).
    { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M10 model10 LK10 cr10 A10 M11 model11 (fun _ => False) BI HH11 AM11 MRT11 MGM11 FR11).
      intros a []. }
    assert (RI11 : rinvH R R11 V2 cls F) by (apply (rinvH_ks R R10 R11 V2 cls F PNAHP3.KS_bhaI2l RI iKS); vm_compute; reflexivity).
    pose proof RI11 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
    assert (LS11 : PNSTA.ls_okA RSEGS PMA.AD PMA.AAD PMA.AN g M11) by (apply (PNHAK.ls_piece _ M10 M11 (fun _ => False) FR11); [intros a []| exact LS]).
    assert (HB11 : PNHAK2.hbase F M11 s str sm).
    { apply (PNHAK2.hbase_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) B1 FIN' FHF (V2 - 128) V2 (fun _ => False) M10 M11 SLOW SHW FR11 PF0 s str sm);
        [intros x Hx; right; apply in_or_app; left; apply INs; exact Hx| apply OAX| apply OAX| apply OAX| exact HB0]. }
    assert (HS11 : PNHAK2.hsrc F M11 src).
    { apply (PNHAK2.hsrc_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) B1 FIN' FHF (V2 - 128) V2 (fun _ => False) M10 M11 SLOW SHW FR11 PF0 src);
        [left; reflexivity| apply OAX| exact HS0]. }
    assert (BB11 : PNHAK2.v8_at M11 (F + 784) bb).
    { apply (PNHAK2.v8_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 128 + 32) B1 FIN' FHF (V2 - 128) V2 (fun _ => False) M10 M11 SLOW SHW FR11 PF0 (F + 784) bb);
        [intros x Hx; right; apply in_or_app; left; apply INbb; exact Hx| clear - FR; lia| clear - FR; lia| apply OAX| exact BB0]. }
    pose proof BI11 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    (* [comment removed for export] *)
    assert (ELB : lb_remove p (((PM.sr_qc src, PM.CHUNK) :: X) ++ LB) = ((PM.sr_qc src, PM.CHUNK) :: PGV8.v8_own bb ++ PM.vs_own str ++ PM.vs_own s) ++ LB).
    { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ C1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
      assert (EL : ((PM.sr_qc src, PM.CHUNK) :: X) ++ LB = ((PM.sr_qc src, PM.CHUNK) :: PGV8.v8_own bb) ++ (p, c) :: ((PM.vs_own str ++ PM.vs_own s) ++ LB))
        by (subst X; cbn [PM.vs_own app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity).
      rewrite (PNHAK3.lb_remove_at p c _ _ _ EL); [| exact ND]. cbn [app]. rewrite <- ?app_assoc. cbn [app]. rewrite <- ?app_assoc. reflexivity. }
    assert (ASX : L5CA.astk ar M11 (V2 - 128) (PMSPA.pm_scr 0) /\ shadow_zero M11 (V2 - 128 - PMSPA.pm_scr 0) (PMSPA.pm_scr 0 / 8))
      by (eapply PNHASK.callee_stack; first [exact BI11 | eassumption | lia]).
    destruct ASX as (AS0 & _).
    change (PMSPA.pm_scr 0) with 12288 in AS0.
    unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMA.AD ADDR_A] in OPD.
    apply (OPD fx11 R11 M11 model11 K _ FF' LK10 A10 cr10 p c (V2 - 128) 0xa851c C1 C2 K0 INP).
    { rewrite L5K.rl10. exact iR10. }
    { rewrite L5K.rl1. exact iR1. }
    { split; [lia| reflexivity]. }
    { rewrite L5K.rl2. exact Y2. }
    { rewrite L5K.rl4. rewrite Y4. exact TP. }
    { replace (V2 - 128) with (V2 - 128 - 0) by lia. apply (L5SAR.astk_sub ar M11 M11 (V2 - 128) 12288 0 PMSPA.OPDEL_SCR AS0 (fun _ X0 => X0)); [lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia|].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - V2A. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    intros fx2 R2' M2' model2' Aw2 RP2 HPo MRT2 INCA2 AM2 HHo.
    rewrite ELB in HPo, HHo.
    unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HPo.
    set (X2l := PGV8.v8_own bb ++ PM.vs_own str ++ PM.vs_own s) in *.
    assert (BI2 : Bv W ((PM.sr_qc src, PM.CHUNK) :: X2l) M2' model2' LK10 cr10 Aw2).
    { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ ((PM.sr_qc src, PM.CHUNK) :: X2l) _ M11 model11 LK10 cr10 A10 M2' model2' LK10 cr10 Aw2 4096 [] BI11 HPo HHo AM2 MRT2 INCA2 (incl_refl _)).
      - lia.
      - clear - CLS; lia.
      - intros rr a [].
      - intros a _ _ rr [].
      - intros a X0. exact X0. }
    assert (FINX : In (F, 5, V2 - 128 + 32) (FF' ++ LK10)) by (apply in_or_app; left; left; reflexivity).
    assert (WFN : PNHAK2.wfi F []) by apply PNHAK2.wfi_nil.
    assert (IN2s : forall x, In x (PM.vs_own str ++ PM.vs_own s) -> In x (((PM.sr_qc src, PM.CHUNK) :: X2l) ++ LB))
      by (intros x Hx; right; apply in_or_app; left; subst X2l; apply in_or_app; right; exact Hx).
    assert (IN2bb : forall x, In x (PGV8.v8_own bb) -> In x (((PM.sr_qc src, PM.CHUNK) :: X2l) ++ LB))
      by (intros x Hx; right; apply in_or_app; left; subst X2l; apply in_or_app; left; exact Hx).
    apply (pieceJ fx2 R2' M2' model2' K LK10 cr10 Aw2 s str bb sm src g).
    + exact BI2.
    + exact (rinvH_pres R R11 R2' V2 cls F RI11 RP2).
    + exact K0.
    + exact (PNHAK.ls_ahpres L C LY g ar _ FF' (V2 - 128) 4096 [] M11 M2' HPo PNHAK.far_nil LS11).
    + rewrite (cs_of_preserved R11 R2' 21 RP2) by inl; rewrite (iKS 21%nat) by inl; exact R21.
    + rewrite (cs_of_preserved R11 R2' 22 RP2) by inl; rewrite (iKS 22%nat) by inl; exact R22.
    + rewrite (cs_of_preserved R11 R2' 23 RP2) by inl; rewrite (iKS 23%nat) by inl; exact R23.
    + rewrite (cs_of_preserved R11 R2' 26 RP2) by inl; rewrite (iKS 26%nat) by inl; exact R26.
    + eapply PNHAK2.hbase_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact HB11 | exact FHF | exact FINX | exact WFN | exact (or_introl eq_refl)
        | (split; reflexivity) | (intros x Hx; right; apply in_or_app; left; apply INs; exact Hx) | (intros x Hx; apply IN2s; exact Hx)
        | apply PNHAK2.wapart_nil | lia ].
    + eapply PNHAK2.hsrc_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact HS11 | exact FHF | exact FINX | exact WFN | exact (or_introl eq_refl)
        | (split; reflexivity) | (left; reflexivity) | apply PNHAK2.wapart_nil | lia ].
    + eapply PNHAK2.v8_keep_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact BB11 | exact FHF | exact FINX | exact WFN | exact (or_introl eq_refl)
        | (split; reflexivity) | (intros x Hx; right; apply in_or_app; left; apply INbb; exact Hx) | (intros x Hx; apply IN2bb; exact Hx)
        | apply PNHAK2.wapart_nil | lia ].
    + exact KONT.
Qed.
End Stage.
End SCFG_1.
End PNHA8b.
