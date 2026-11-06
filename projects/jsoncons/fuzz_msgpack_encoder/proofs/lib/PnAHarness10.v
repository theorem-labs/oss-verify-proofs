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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAHarnessSK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5AFrameKR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.PnAHarnessStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarnessSK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAHarnessKit5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAHarnessP3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAHarnessP4.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PQHA10.
Import L5A. Import L5CA. Import L5SAR. Import PQHAS. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PnLayoutA.ADDR_A.
Abbreviation AAD := PnLayoutA.AADDR_A.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
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
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 5, V2 - 160 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 160 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Hypothesis FAL : F mod 2048 = 0.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 160 + 32) :: FF).
Local Notation NEG8 := 18446744073709551608.
Local Notation VTT := 1395264.

Lemma stage10 (LCD : PMA.locale_dtor_spec L ar HI) (IOD : PMA.ios_dtor_spec L ar HI) (OPD : PMA.opdel_spec L ar HI)
      (fx11 : FPState) (R11 : bvmap 5 word) (M11 : word -> option byte) (model11 : Model) (K : TSet)
      (LK11 : list fframe) (cr11 : credit) (A11 : list (Z * Z)) (s : PM.vstr) (st : Z) (g : PMST.st) :
  Bv W (PM.vs_own s) M11 model11 LK11 cr11 A11 -> rinvH R R11 V2 cls F -> K [] -> PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M11 ->
  getr R11 (reg 1) = Z_to_bv 64 0xaf6f0 -> getr R11 (reg 10) = Z_to_bv 64 (F + 120) ->
  getr R11 (reg 18) = Z_to_bv 64 2147450880 -> getr R11 (reg 20) = Z_to_bv 64 VTT -> getr R11 (reg 21) = Z_to_bv 64 (F + 96) ->
  getr R11 (reg 22) = Z_to_bv 64 (F + 432) -> getr R11 (reg 23) = Z_to_bv 64 (F + 520) -> getr R11 (reg 24) = Z_to_bv 64 NEG8 ->
  getr R11 (reg 25) = Z_to_bv 64 (F + 592) -> getr R11 (reg 26) = Z_to_bv 64 (F + 1168) ->
  PQHAK2.hfin F M11 s st ->
  L5.u64_at RSEGS M11 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M11 (V2 - 136) F ->
  (forall (fx12 : FPState) (R12 : bvmap 5 word) (M12 : word -> option byte) (model12 : Model) (LK12 : list fframe) (A12 : list (Z * Z)),
      Bv W [] M12 model12 LK12 cr11 A12 -> rinvH R R12 V2 cls F -> PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M12 ->
      getr R12 (reg 18) = Z_to_bv 64 NEG8 -> getr R12 (reg 20) = Z_to_bv 64 VTT -> getr R12 (reg 21) = Z_to_bv 64 (F + 96) ->
      getr R12 (reg 22) = Z_to_bv 64 (F + 432) -> getr R12 (reg 23) = Z_to_bv 64 (F + 520) -> getr R12 (reg 24) = Z_to_bv 64 NEG8 ->
      getr R12 (reg 25) = Z_to_bv 64 (F + 592) -> getr R12 (reg 26) = Z_to_bv 64 (F + 1168) ->
      L5.u64_at RSEGS M12 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx12 R12 0xaf7b0 M12 model12) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx11 R11 0x11e390 M11 model11) K.
Proof.
  intros BI RI K0 LS R1a R10a R18 R20 R21 R22 R23 R24 R25 R26 HF0 HSTKa HSTKb KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PQHAK2.hf F) by (unfold PQHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  pose proof HF0 as (VS0 & LC0 & IO0).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  assert (SPA16 : (V2 - 160) mod 16 = 0) by (clear - V2A; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  (* [comment removed for export] *)
  unfold PMA.locale_dtor_spec, PMSPA.locale_dtor_spec in LCD. cbn [pa_locale_dtor pa_classic_imp PMA.AD PnLayoutA.ADDR_A] in LCD.
  apply (LCD fx11 R11 M11 model11 K _ FF' LK11 A11 cr11 (F + 120) (V2 - 160) 0xaf6f0 B1 B2 K0).
  { eapply PQHASK.callee_entry; first [exact BI | exact RI | exact R1a | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PQHASK.callee_room; first [exact BI | eassumption | lia]. }
  { eapply PQHASK.callee_rs; eassumption. }
  { rewrite L5K.rl10. exact R10a. }
  { exists (F, 5, V2 - 160 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. clear; lia. }
  { cbn [pa_classic_imp PMA.AD PnLayoutA.ADDR_A] in LC0. exact LC0. }
  intros fx' R' model11d RP' MRTd AMd HHd.   (* [comment removed for export] *)
  assert (BId : Bv W (PM.vs_own s) M11 model11d LK11 cr11 A11).
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M11 model11 LK11 cr11 A11 M11 model11d (fun _ => False) BI HHd AMd MRTd
            (mem_grows_refl M11) (fun a _ _ => eq_refl)). intros a []. }
  clear BI B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 MRTd AMd HHd. clear model11. rename model11d into model11. rename BId into BI.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (RI' : rinvH R R' V2 cls F) by exact (rinvH_pres R R11 R' V2 cls F RI RP').
  pose proof RI' as (X2 & X8 & X9 & X19 & X21 & X27 & X3 & X4).
  assert (Y18 : getr R' (reg 18) = Z_to_bv 64 2147450880) by (rewrite (cs_of_preserved R11 R' 18 RP') by inl; exact R18).
  assert (Y20 : getr R' (reg 20) = Z_to_bv 64 VTT) by (rewrite (cs_of_preserved R11 R' 20 RP') by inl; exact R20).
  assert (Y21 : getr R' (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R11 R' 21 RP') by inl; exact R21).
  assert (Y22 : getr R' (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R11 R' 22 RP') by inl; exact R22).
  assert (Y23 : getr R' (reg 23) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R11 R' 23 RP') by inl; exact R23).
  assert (Y24 : getr R' (reg 24) = Z_to_bv 64 NEG8) by (rewrite (cs_of_preserved R11 R' 24 RP') by inl; exact R24).
  assert (Y25 : getr R' (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R11 R' 25 RP') by inl; exact R25).
  assert (Y26 : getr R' (reg 26) = Z_to_bv 64 (F + 1168)) by (rewrite (cs_of_preserved R11 R' 26 RP') by inl; exact R26).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M11 model11 LK11 cr11 A11 BI)
    as ((VW1 & VIC1 & VSB1 & VUAR1 & VMS1) & VOWN1 & (VFD1 & VFW1 & VFSW1 & VFLC1 & VFLW1) & (FLCc1 & FLV1 & FV1 & SPV1 & FSV1)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H1 := ahid A11 model11) in *. set (MV1 := mrestrict H1 M11) in *.
  assert (Q5 : L5.writable RSEGS MV1 (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW1| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV1 (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC1).
  LeanFeed.pfeed ident:(PP) (PQAHP3.qhaO_conc fx' R' MV1 (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                      | exact VFD1 | exact VFW1 | exact VFSW1 | exact VFLW1 | exact Q5 | exact Q6 | exact VSB1 | exact VUAR1 | exact VIC1 | (unfold PQAHP3.aligned; exact V2A) ]).
  destruct PP as (fx2 & R2 & M2v & MG2 & mFR & mFZ & (mMS & mKS & mR1 & mR10 & mR11)).
  apply (apiece L ar C HI LYa HIok _ FF' LK11 cr11 A11 M11 model11 fx' fx2 R' 0xaf6f0 R2 0xf9bac M2v (fun _ => False) K B1 B2 mMS MG2).
  { intros a Ha Hna. apply mFZ; exact Ha. }
  { intros a Ha []. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (BI3 : Bv W (PM.vs_own s) M3 model3 LK11 cr11 A11).
  { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M11 model11 LK11 cr11 A11 M3 model3 (fun _ => False) BI HH3 AM3 MRT3 MGM3 FR3).
    intros a []. }
  assert (RI3 : rinvH R R2 V2 cls F) by (apply (rinvH_ks R R' R2 V2 cls F PQAHP3.KS_qhaO RI' mKS); vm_compute; reflexivity).
  assert (EQ3 : M3 = M11) by (apply mem_eq_of_agree; intros a Ha; apply FR3; [exact Ha| intros []]). subst M3.
  assert (FIN1 : In (F, 5, V2 - 160 + 32) (FF' ++ LK11)) by (apply in_or_app; left; left; reflexivity).
  pose proof BI3 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  unfold PMA.ios_dtor_spec, PMSPA.ios_dtor_spec in IOD. cbn [pa_ios_dtor PMA.AD PnLayoutA.ADDR_A] in IOD.
  apply (IOD fx2 R2 M11 model3 K _ FF' LK11 A11 cr11 (F + 216) (pa_vp_iss_ios PMA.AD) (F + 112) st (V2 - 160) 0xaf704 C1 C2 K0).
  { eapply PQHASK.callee_entry; first [exact BI3 | exact RI3 | exact mR1 | eassumption | (split; [lia| reflexivity]) | lia]. }
  { eapply PQHASK.callee_room; first [exact BI3 | eassumption | lia]. }
  { eapply PQHASK.callee_rs; eassumption. }
  { rewrite L5K.rl10. exact mR10. }
  { exists (F, 5, V2 - 160 + 32). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. clear; lia. }
  { clear - FM8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  { exact IO0. }
  { exact (proj1 LS). }
  intros fx4 R4 M4 model4 LK4 Aw4 RP4 HP4 MRT4 INCLK4 INCA4 AM4 HH4.
  change (PMSPA.pm_scr 1) with 14336 in HP4.
  assert (WFI : PQHAK2.wfi F [(F + 216, 152)]) by (apply PQHAK2.wfi_cons; [cbn [fst snd]; left; lia| apply PQHAK2.wfi_nil]).
  assert (LS4 : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M4).
  { apply (PQHAK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 14336 [(F + 216, 152)] M11 M4 HP4); [| exact LS].
    apply PQHAK.far_cons; [cbn [fst snd]; clear - FR; lia| apply PQHAK.far_nil]. }
  assert (BI4 : Bv W (PM.vs_own s) M4 model4 LK4 cr11 Aw4).
  { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ (PM.vs_own s) _ M11 model3 LK11 cr11 A11 M4 model4 LK4 cr11 Aw4 14336 [(F + 216, 152)] BI3 HP4 HH4 AM4 MRT4 INCA4 INCLK4).
    - lia.
    - clear - CLS; lia.
    - intros rr a [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. unfold tocell. split; [clear - Ha FCEIL SLO CLS; lia|]. unfold HeapIfaceA.SB. change (ff_bytes 5) with 2048. clear - Ha FR F8 FBIG. lia.
    - intros a Hc _ rr [<-|[]] Ha. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. apply (NCF a); [left; clear - Ha; lia| exact Hc].
    - intros a X0. exact X0. }
  assert (VS4 : PM.vstr_at RSEGS PMSPA.accA M4 (F + 32) s).
  { eapply PQHAK2.vstr_keep_callee; first [ exact LY | exact HIok | exact C1 | exact HP4 | exact VS0 | exact FHF | exact FIN1 | exact WFI | (left; reflexivity)
      | (split; reflexivity) | (intros x Hx; apply in_or_app; left; exact Hx) | (apply PQHAK2.wapart_cons; [cbn [fst snd]; lia| apply PQHAK2.wapart_nil]) | lia ]. }
  assert (AG4 : forall a, V2 - 160 <= a < V2 + cls -> M4 (Z_to_bv 64 a) = M11 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP4 a). split; [clear - Ha V2R V2S CLS; lia| split].
    - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
    - intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Ha FCEIL SLO CLS. lia. }
  assert (HSTKa4 : L5.u64_at RSEGS M4 (V2 - 144) (F + 32))
    by (apply (L5C.u64_at_agree RSEGS M11 M4 (V2 - 144) (F + 32)); [intros i Hi; apply AG4; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]).
  assert (HSTKb4 : L5.u64_at RSEGS M4 (V2 - 136) F)
    by (apply (L5C.u64_at_agree RSEGS M11 M4 (V2 - 136) F); [intros i Hi; apply AG4; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M4 model4 LK4 cr11 Aw4 BI4)
    as ((VW4 & VIC4 & VSB4 & VUAR4 & VMS4) & VOWN4 & (VFD4 & VFW4 & VFSW4 & VFLC4 & VFLW4) & (FLCc4 & FLV4 & FV4 & SPV4 & FSV4)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
  assert (RI4 : rinvH R R4 V2 cls F) by exact (rinvH_pres R R2 R4 V2 cls F RI3 RP4).
  pose proof RI4 as (Z2 & Z8 & Z9 & Z19 & Z21 & Z27 & Z3 & Z4).
  assert (S18 : getr R4 (reg 18) = Z_to_bv 64 2147450880) by (rewrite (cs_of_preserved R2 R4 18 RP4) by inl; rewrite (mKS 18%nat) by inl; exact Y18).
  assert (S20 : getr R4 (reg 20) = Z_to_bv 64 VTT) by (rewrite (cs_of_preserved R2 R4 20 RP4) by inl; rewrite (mKS 20%nat) by inl; exact Y20).
  assert (S21 : getr R4 (reg 21) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R2 R4 21 RP4) by inl; rewrite (mKS 21%nat) by inl; exact Y21).
  assert (S22 : getr R4 (reg 22) = Z_to_bv 64 (F + 432)) by (rewrite (cs_of_preserved R2 R4 22 RP4) by inl; rewrite (mKS 22%nat) by inl; exact Y22).
  assert (S23 : getr R4 (reg 23) = Z_to_bv 64 (F + 520)) by (rewrite (cs_of_preserved R2 R4 23 RP4) by inl; rewrite (mKS 23%nat) by inl; exact Y23).
  assert (S24 : getr R4 (reg 24) = Z_to_bv 64 NEG8) by (rewrite (cs_of_preserved R2 R4 24 RP4) by inl; rewrite (mKS 24%nat) by inl; exact Y24).
  assert (S25 : getr R4 (reg 25) = Z_to_bv 64 (F + 592)) by (rewrite (cs_of_preserved R2 R4 25 RP4) by inl; rewrite (mKS 25%nat) by inl; exact Y25).
  assert (S26 : getr R4 (reg 26) = Z_to_bv 64 (F + 1168)) by (rewrite (cs_of_preserved R2 R4 26 RP4) by inl; rewrite (mKS 26%nat) by inl; exact Y26).
  assert (Q5b : L5.writable RSEGS MV4 (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW4| clear; lia| clear - CLS; lia]).
  assert (Q6b : L5.u64_at RSEGS MV4 (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC4).
  assert (Q7b : L5.u64_at RSEGS MV4 (V2 - 144) (F + 32)).
  { apply (L5C.u64_at_agree RSEGS M4 MV4 (V2 - 144) (F + 32)); [| clear - V2R; lia| clear - V2R; lia| exact HSTKa4].
    intros i Hi. unfold MV4. rewrite (mrestrict_visible H4 M4); [reflexivity|]. replace i with ((V2 - 160) + (i - (V2 - 160))) by (clear; lia). apply SPV4. clear - Hi CLS; lia. }
  assert (AV32 : L5A.avis H4 (F + 32) 8) by (apply (PQHAK.avis_sub H4 F 2048 (F + 32) 8 FV4); lia).
  assert (AV48 : L5A.avis H4 (F + 48) 8) by (apply (PQHAK.avis_sub H4 F 2048 (F + 48) 8 FV4); lia).
  pose proof BI4 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
  set (W5 := fun a => F / 8 + 2147450892 <= a < F / 8 + 2147450892 + 34).
  assert (WC5 : forall a, 0 <= a < 2 ^ 64 -> W5 a -> aclientw L ar (PM.vs_own s ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 7036928)).
  { intros a Ha Wa. subst W5; cbn beta in Wa. split.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FRS : forall M5 : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ W5 a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)) ->
            forall a, V2 - 160 <= a < V2 + cls -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros M5 FR5 a Ha. apply FR5; [clear - Ha V2R V2S CLS; lia|]. subst W5; cbn beta. unfold HeapIfaceA.SB. intros X0. clear - Ha X0 FCEIL SLO CLS FBD V2R. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct s as [n | c n p].
  - (* [comment removed for export] *)
    destruct VS4 as (_ & _ & (Hn & SB0)).
    assert (SBv : L5.u8_at RSEGS MV4 (F + 32) (2 * n))
      by (apply (proj2 (L5A.u8_at_vis H4 M4 (F + 32) (2 * n) (PQHAK.avis_sub H4 (F + 32) 8 (F + 32) 1 AV32 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
    pose proof (PMF.even_byte n) as EVB.
    LeanFeed.pfeed ident:(PP) (PQAHP4.qhaPs_conc fx4 R4 MV4 (fun j => match j with 2%nat => V2 | 36%nat => 2 * n | 40%nat => F | 41%nat => fl | 58%nat => U R4 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - Hn; lia) | exact F32
                        | exact VFD4 | exact VFW4 | exact VFSW4 | exact VFLW4 | exact Q5b | exact Q6b | exact Q7b | exact SBv | exact EVB | exact VSB4 | exact VUAR4 | exact VIC4 | (unfold PQAHP4.aligned; exact V2A) ]).
    destruct PP as (fx5 & R5 & M5v & MG5 & nFR & nFZ & (nMS & nKS & nR10 & nR12 & nR18 & NQ)). clear NQ.
    apply (apiece L ar C HI LYa HIok _ FF' LK4 cr11 Aw4 M4 model4 fx4 fx5 R4 0xaf704 R5 0xaf7b0 M5v W5 K D1 D2 nMS MG5).
    { intros a Ha Hna. apply nFZ; [exact Ha|..]; intros X0; apply Hna; subst W5; cbn beta; clear - X0; lia. }
    { exact WC5. }
    intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
    apply (KONT fx5 R5 M5 model5 LK4 Aw4).
    + apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M4 model4 LK4 cr11 Aw4 M5 model5 W5 BI4 HH5 AM5 MRT5 MGM5 FR5).
      intros a Wa. subst W5; cbn beta in Wa. right; right. change (ff_bytes 5) with 2048. change (2048 / 8) with 256. unfold HeapIfaceA.SB in *. clear - Wa. lia.
    + apply (rinvH_ks R R4 R5 V2 cls F PQAHP4.KS_qhaPs RI4 nKS); vm_compute; reflexivity.
    + apply (PQHAK.ls_piece _ M4 M5 W5 FR5); [intros a Wa; subst W5; cbn beta in Wa; unfold HeapIfaceA.SB in *; clear - Wa FR; lia| exact LS4].
    + exact nR18.
    + rewrite (nKS 20%nat) by inl. exact S20.
    + rewrite (nKS 21%nat) by inl. exact S21.
    + rewrite (nKS 22%nat) by inl. exact S22.
    + rewrite (nKS 23%nat) by inl. exact S23.
    + rewrite (nKS 24%nat) by inl. exact S24.
    + rewrite (nKS 25%nat) by inl. exact S25.
    + rewrite (nKS 26%nat) by inl. exact S26.
    + apply (L5C.u64_at_agree RSEGS M4 M5 (V2 - 136) F); [intros i Hi; apply (FRS M5 FR5); clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb4].
  - (* [comment removed for export] *)
    destruct VS4 as (_ & _ & (TW0 & TW8 & TW16 & Hn & Hc & Hc2 & TBP & _)).
    replace (F + 32 + 16) with (F + 48) in TW16 by (clear; lia).
    assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by (clear - Hc; lia).
    pose proof (PMF.u8_of_u64 RSEGS M4 _ _ Hc64 TW0) as SB0.
    pose proof (PMF.odd_byte c Hc2 ltac:(clear - Hc; lia)) as ODB.
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(clear; lia)) as HVB.
    assert (SBv : L5.u8_at RSEGS MV4 (F + 32) ((c + 1) mod 256))
      by (apply (proj2 (L5A.u8_at_vis H4 M4 (F + 32) _ (PQHAK.avis_sub H4 (F + 32) 8 (F + 32) 1 AV32 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
    assert (TW0v : L5.u64_at RSEGS MV4 (F + 32) (c + 1)) by (apply (proj2 (L5A.u64_at_vis H4 M4 (F + 32) _ AV32 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW0).
    assert (TW16v : L5.u64_at RSEGS MV4 (F + 48) p) by (apply (proj2 (L5A.u64_at_vis H4 M4 (F + 48) _ AV48 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW16).
    assert (INP : In (p, c) (PM.vs_own (PM.VLong c n p) ++ LB)) by (left; reflexivity).
    destruct (PQHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ p c D1 INP) as (P0 & _ & _ & _ & _ & P47 & _).
    LeanFeed.pfeed ident:(PP) (PQAHP4.qhaPl_conc fx4 R4 MV4 (fun j => match j with 2%nat => V2 | 36%nat => (c + 1) mod 256 | 37%nat => c + 1 | 38%nat => p
                                                      | 40%nat => F | 41%nat => fl | 58%nat => U R4 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - HVB; lia) | (clear - Hc64; lia) | (clear - P0 P47 Hc; lia)
                        | exact F32 | exact VFD4 | exact VFW4 | exact VFSW4 | exact VFLW4 | exact Q5b | exact Q6b | exact Q7b | exact SBv | exact TW0v | exact TW16v | exact ODB
                        | exact VSB4 | exact VUAR4 | exact VIC4 | (unfold PQAHP4.aligned; exact V2A) ]).
    destruct PP as (fx5 & R5 & M5v & MG5 & nFR & nFZ & (nMS & nKS & nR1 & nR10 & nR11 & nR12 & nR18 & NQ)). clear NQ.
    apply (apiece L ar C HI LYa HIok _ FF' LK4 cr11 Aw4 M4 model4 fx4 fx5 R4 0xaf704 R5 0xf1fc0 M5v W5 K D1 D2 nMS MG5).
    { intros a Ha Hna. apply nFZ; [exact Ha|..]; intros X0; apply Hna; subst W5; cbn beta; clear - X0; lia. }
    { exact WC5. }
    intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
    assert (BI5 : Bv W (PM.vs_own (PM.VLong c n p)) M5 model5 LK4 cr11 Aw4).
    { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M4 model4 LK4 cr11 Aw4 M5 model5 W5 BI4 HH5 AM5 MRT5 MGM5 FR5).
      intros a Wa. subst W5; cbn beta in Wa. right; right. change (ff_bytes 5) with 2048. change (2048 / 8) with 256. unfold HeapIfaceA.SB in *. clear - Wa. lia. }
    assert (RI5 : rinvH R R5 V2 cls F) by (apply (rinvH_ks R R4 R5 V2 cls F PQAHP4.KS_qhaPl RI4 nKS); vm_compute; reflexivity).
    assert (LS5 : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M5) by (apply (PQHAK.ls_piece _ M4 M5 W5 FR5); [intros a Wa; subst W5; cbn beta in Wa; unfold HeapIfaceA.SB in *; clear - Wa FR; lia| exact LS4]).
    assert (HSTKb5 : L5.u64_at RSEGS M5 (V2 - 136) F)
      by (apply (L5C.u64_at_agree RSEGS M4 M5 (V2 - 136) F); [intros i Hi; apply (FRS M5 FR5); clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb4]).
    pose proof BI5 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
    assert (ASX : L5CA.astk ar M5 (V2 - 160) (PMSPA.pm_scr 0) /\ shadow_zero M5 (V2 - 160 - PMSPA.pm_scr 0) (PMSPA.pm_scr 0 / 8))
      by (eapply PQHASK.callee_stack; first [exact BI5 | eassumption | lia]).
    destruct ASX as (AS0 & _). change (PMSPA.pm_scr 0) with 12288 in AS0.
    pose proof RI5 as (U2' & U8 & U9 & U19 & U21 & U27 & U3 & U4).
    unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMA.AD PnLayoutA.ADDR_A] in OPD.
    apply (OPD fx5 R5 M5 model5 K _ FF' LK4 Aw4 cr11 p c (V2 - 160) 0xaf7b0 E1 E2 K0 INP).
    { rewrite L5K.rl10. exact nR10. }
    { rewrite L5K.rl1. exact nR1. }
    { split; [lia| reflexivity]. }
    { rewrite L5K.rl2. exact U2'. }
    { rewrite L5K.rl4. rewrite U4. exact TP. }
    { replace (V2 - 160) with (V2 - 160 - 0) by lia. apply (L5SAR.astk_sub ar M5 M5 (V2 - 160) 12288 0 PMSPA.OPDEL_SCR AS0 (fun _ X0 => X0));
        [lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| replace (V2 - 160 - 0) with (V2 - 160) by (clear; lia); exact SPA16]. }
    intros fx6 R6 M6 model6 Aw6 RP6 HPo MRT6 INCA6 AM6 HHo.
    cbn [PM.vs_own app] in HPo, HHo.
    rewrite L5ADHR.lb_remove_head in HPo, HHo.
    unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HPo.
    assert (AG6 : forall a, V2 - 160 <= a < V2 + cls -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
    { intros a Ha. apply (proj1 HPo a). split; [clear - Ha V2R V2S CLS; lia| split].
      - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
      - intros rr []. }
    apply (KONT fx6 R6 M6 model6 LK4 Aw6).
    + apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ [] [] M5 model5 LK4 cr11 Aw4 M6 model6 LK4 cr11 Aw6 4096 [] BI5 HPo HHo AM6 MRT6 INCA6 (incl_refl _)).
      * lia.
      * clear - CLS; lia.
      * intros rr a [].
      * intros a _ _ rr [].
      * intros a X0. exact X0.
    + exact (rinvH_pres R R5 R6 V2 cls F RI5 RP6).
    + apply (PQHAK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 4096 [] M5 M6 HPo PQHAK.far_nil LS5).
    + rewrite (cs_of_preserved R5 R6 18 RP6) by inl. exact nR18.
    + rewrite (cs_of_preserved R5 R6 20 RP6) by inl. rewrite (nKS 20%nat) by inl. exact S20.
    + rewrite (cs_of_preserved R5 R6 21 RP6) by inl. rewrite (nKS 21%nat) by inl. exact S21.
    + rewrite (cs_of_preserved R5 R6 22 RP6) by inl. rewrite (nKS 22%nat) by inl. exact S22.
    + rewrite (cs_of_preserved R5 R6 23 RP6) by inl. rewrite (nKS 23%nat) by inl. exact S23.
    + rewrite (cs_of_preserved R5 R6 24 RP6) by inl. rewrite (nKS 24%nat) by inl. exact S24.
    + rewrite (cs_of_preserved R5 R6 25 RP6) by inl. rewrite (nKS 25%nat) by inl. exact S25.
    + rewrite (cs_of_preserved R5 R6 26 RP6) by inl. rewrite (nKS 26%nat) by inl. exact S26.
    + apply (L5C.u64_at_agree RSEGS M5 M6 (V2 - 136) F); [intros i Hi; apply AG6; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb5].
Qed.
End Stage.
End SCFG_1.
End PQHA10.
