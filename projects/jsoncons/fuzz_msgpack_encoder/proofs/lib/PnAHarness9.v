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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAHarnessSK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5AFrameKR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.PnAHarnessStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAHarnessSK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAHarnessKit5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAHarnessP3.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PQHA9.
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
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 160) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 160 + 32) :: FF).
Local Notation NEG8 := 18446744073709551608.
Local Notation VTT := 1395264.

(* [comment removed for export] *)
Lemma stage9_O (fx : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (K : TSet)
      (LK' : list fframe) (cr' : credit) (A' : list (Z * Z)) (s : PM.vstr) (st : Z) (g : PMST.st) :
  Bv W (PM.vs_own s) M' model' LK' cr' A' -> rinvH R R' V2 cls F -> K [] -> PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M' ->
  getr R' (reg 18) = Z_to_bv 64 2147450880 -> getr R' (reg 20) = Z_to_bv 64 VTT -> getr R' (reg 21) = Z_to_bv 64 (F + 96) ->
  getr R' (reg 22) = Z_to_bv 64 (F + 432) -> getr R' (reg 23) = Z_to_bv 64 (F + 520) -> getr R' (reg 24) = Z_to_bv 64 NEG8 ->
  getr R' (reg 25) = Z_to_bv 64 (F + 592) -> getr R' (reg 26) = Z_to_bv 64 (F + 1168) ->
  PQHAK2.hfin F M' s st ->
  L5.u64_at RSEGS M' (V2 - 144) (F + 32) -> L5.u64_at RSEGS M' (V2 - 136) F ->
  (forall (fx11 : FPState) (R11 : bvmap 5 word) (M11 : word -> option byte) (model11 : Model) (LK11 : list fframe) (A11 : list (Z * Z)),
      Bv W (PM.vs_own s) M11 model11 LK11 cr' A11 -> rinvH R R11 V2 cls F -> PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M11 ->
      getr R11 (reg 1) = Z_to_bv 64 0xaf6f0 -> getr R11 (reg 10) = Z_to_bv 64 (F + 120) ->
      getr R11 (reg 18) = Z_to_bv 64 2147450880 -> getr R11 (reg 20) = Z_to_bv 64 VTT -> getr R11 (reg 21) = Z_to_bv 64 (F + 96) ->
      getr R11 (reg 22) = Z_to_bv 64 (F + 432) -> getr R11 (reg 23) = Z_to_bv 64 (F + 520) -> getr R11 (reg 24) = Z_to_bv 64 NEG8 ->
      getr R11 (reg 25) = Z_to_bv 64 (F + 592) -> getr R11 (reg 26) = Z_to_bv 64 (F + 1168) ->
      PQHAK2.hfin F M11 s st ->
      L5.u64_at RSEGS M11 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M11 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx11 R11 0x11e390 M11 model11) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx R' 0xaf6d8 M' model') K.
Proof.
  intros BI RI K0 LS R18 R20 R21 R22 R23 R24 R25 R26 HF0 HSTKa HSTKb KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PQHAK2.hf F) by (unfold PQHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (FIN : In (F, 5, V2 - 160 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' A' BI)
    as ((VW & VIC & VSB & VUAR & VMS) & VOWN & (VFD & VFW & VFSW & VFLC & VFLW) & (FLCc & FLV & FV & SPV & FSV)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid A' model') in *. set (MV := mrestrict H' M') in *.
  pose proof RI as (X2 & X8 & X9 & X19 & X21 & X27 & X3 & X4).
  assert (Q5 : L5.writable RSEGS MV (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC).
  LeanFeed.pfeed ident:(PP) (PQAHP3.qhaN_conc fx R' MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                      | exact VFD | exact VFW | exact VFSW | exact VFLW | exact Q5 | exact Q6 | exact VSB | exact VUAR | exact VIC | (unfold PQAHP3.aligned; exact V2A) ]).
  destruct PP as (fx1 & R1 & M1v & MG1 & oFR & oFZ & (oMS & oKS & oR1 & oR10 & oU112 & oD1 & oD2)).
  set (W1 := fun a => F + 112 <= a < F + 112 + 8).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr' A' M' model' fx fx1 R' 0xaf6d8 R1 0x11e390 M1v W1 K B1 B2 oMS MG1).
  { intros a Ha Hna. apply oFZ; [exact Ha|..]; intros X0; apply Hna; subst W1; cbn beta; clear - X0; lia. }
  { intros a Ha Wa. subst W1; cbn beta in Wa. split.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR. lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (PF1 : PQHAK2.pfoot F (V2 - 160) V2 W1) by (intros a Wa; subst W1; cbn beta in Wa; clear - Wa; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (OA1 : forall o k2, (F + 32 <= o /\ o + k2 <= F + 112) \/ (F + 120 <= o /\ o + k2 <= F + 2040) -> PQHAK2.oav W1 o k2).
  { intros o k2 H12 x Hx. subst W1; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H12 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H12 SX FBIG FR FM8; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (FR1st : forall a, V2 - 160 <= a < V2 + cls -> M1 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha. apply FR1; [clear - Ha V2R V2S CLS; lia|]. subst W1; cbn beta. intros X0. clear - Ha X0 FCEIL SLO CLS. lia. }
  apply (KONT fx1 R1 M1 model1 LK' A').
  - apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' A' M1 model1 W1 BI HH1 AM1 MRT1 MGM1 FR1).
    intros a Wa. subst W1; cbn beta in Wa. right; left. change (ff_bytes 5) with 2048. clear - Wa. lia.
  - apply (rinvH_ks R R' R1 V2 cls F PQAHP3.KS_qhaN RI oKS); vm_compute; reflexivity.
  - apply (PQHAK.ls_piece _ M' M1 W1 FR1); [intros a Wa; subst W1; cbn beta in Wa; clear - Wa FR; lia| exact LS].
  - exact oR1.
  - exact oR10.
  - rewrite (oKS 18%nat) by inl. exact R18.
  - rewrite (oKS 20%nat) by inl. exact R20.
  - rewrite (oKS 21%nat) by inl. exact R21.
  - rewrite (oKS 22%nat) by inl. exact R22.
  - rewrite (oKS 23%nat) by inl. exact R23.
  - rewrite (oKS 24%nat) by inl. exact R24.
  - rewrite (oKS 25%nat) by inl. exact R25.
  - rewrite (oKS 26%nat) by inl. exact R26.
  - apply (PQHAK2.hfin_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) B1 FIN FHF (V2 - 160) V2 W1 M' M1 SLOW SHW FR1 PF1 s st);
      [intros x Hx; apply in_or_app; left; exact Hx| apply OA1; lia| apply OA1; lia| apply OA1; lia| exact HF0].
  - apply (L5C.u64_at_agree RSEGS M' M1 (V2 - 144) (F + 32)); [intros i Hi; apply FR1st; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa].
  - apply (L5C.u64_at_agree RSEGS M' M1 (V2 - 136) F); [intros i Hi; apply FR1st; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb].
Qed.

(* [comment removed for export] *)
Lemma stage9a (OPD : PMA.opdel_spec L ar HI)
      (fx10 : FPState) (R10 : bvmap 5 word) (M10 : word -> option byte) (model10 : Model) (K : TSet)
      (LK10 : list fframe) (cr10 : credit) (A10 : list (Z * Z)) (s s' : PM.vstr) (sm1 : PM.strm) (g : PMST.st) :
  Bv W (PM.vs_own s' ++ PM.vs_own s) M10 model10 LK10 cr10 A10 -> rinvH R R10 V2 cls F -> K [] -> PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M10 ->
  getr R10 (reg 18) = Z_to_bv 64 2147450880 -> getr R10 (reg 20) = Z_to_bv 64 VTT -> getr R10 (reg 21) = Z_to_bv 64 (F + 96) ->
  getr R10 (reg 22) = Z_to_bv 64 (F + 432) -> getr R10 (reg 23) = Z_to_bv 64 (F + 520) -> getr R10 (reg 24) = Z_to_bv 64 NEG8 ->
  getr R10 (reg 25) = Z_to_bv 64 (F + 592) -> getr R10 (reg 26) = Z_to_bv 64 (F + 1168) ->
  PQHAK5.hbaseN F M10 s s' sm1 ->
  L5.u64_at RSEGS M10 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M10 (V2 - 136) F ->
  (forall (fx11 : FPState) (R11 : bvmap 5 word) (M11 : word -> option byte) (model11 : Model) (LK11 : list fframe) (A11 : list (Z * Z)),
      Bv W (PM.vs_own s) M11 model11 LK11 cr10 A11 -> rinvH R R11 V2 cls F -> PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M11 ->
      getr R11 (reg 1) = Z_to_bv 64 0xaf6f0 -> getr R11 (reg 10) = Z_to_bv 64 (F + 120) ->
      getr R11 (reg 18) = Z_to_bv 64 2147450880 -> getr R11 (reg 20) = Z_to_bv 64 VTT -> getr R11 (reg 21) = Z_to_bv 64 (F + 96) ->
      getr R11 (reg 22) = Z_to_bv 64 (F + 432) -> getr R11 (reg 23) = Z_to_bv 64 (F + 520) -> getr R11 (reg 24) = Z_to_bv 64 NEG8 ->
      getr R11 (reg 25) = Z_to_bv 64 (F + 592) -> getr R11 (reg 26) = Z_to_bv 64 (F + 1168) ->
      PQHAK2.hfin F M11 s (PM.sm_st sm1) ->
      L5.u64_at RSEGS M11 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M11 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx11 R11 0x11e390 M11 model11) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx10 R10 0xaf64c M10 model10) K.
Proof.
  intros BI RI K0 LS R18 R20 R21 R22 R23 R24 R25 R26 HB0 HSTKa HSTKb KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PQHAK2.hf F) by (unfold PQHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  assert (SPA16 : (V2 - 160) mod 16 = 0) by (clear - V2A; lia).
  assert (E96 : (F + 96) / 8 = F / 8 + 12) by (clear - FM8; lia).
  assert (Q7 : 65536 + 6971392 <= F \/ F + 2048 <= 65536) by (clear - FR; lia).
  assert (QSH : F / 8 + 2147450880 + 256 <= 2147459072 \/ 2147459072 + 839680 <= F / 8 + 2147450880) by (clear - Q7 FM8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  set (X := PM.vs_own s' ++ PM.vs_own s) in *.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (FIN10 : In (F, 5, V2 - 160 + 32) (FF' ++ LK10)) by (apply in_or_app; left; left; reflexivity).
  assert (INS : incl (PM.vs_own s) (X ++ LB)) by (intros x Hx; apply in_or_app; left; subst X; apply in_or_app; right; exact Hx).
  assert (INT : incl (PM.vs_own s') (X ++ LB)) by (intros x Hx; apply in_or_app; left; subst X; apply in_or_app; left; exact Hx).
  pose proof HB0 as (VS0 & IS0 & VI0).
  pose proof IS0 as (IH0 & ID & IC & IH16 & IH24 & IH32 & IH40 & IH48 & IH64 & IVS & IH104 & IH112 & IOS & IE1 & IE2).
  replace (F + 96 + 24) with (F + 120) in IH24 by (clear; lia). replace (F + 96 + 80) with (F + 176) in IVS by (clear; lia).
  replace (F + 96 + 120) with (F + 216) in IOS by (clear; lia). replace (F + 96 + 16) with (F + 112) in IOS by (clear; lia).
  (* [comment removed for export] *)
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M10 model10 LK10 cr10 A10 BI)
    as ((VW & VIC & VSB & VUAR & VMS) & VOWN & (VFD & VFW & VFSW & VFLC & VFLW) & (FLCc & FLV & FV & SPV & FSV)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H10 := ahid A10 model10) in *. set (MV := mrestrict H10 M10) in *.
  pose proof RI as (X2 & X8 & X9 & X19 & X21 & X27 & X3 & X4).
  assert (Q5 : L5.writable RSEGS MV (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC).
  assert (ZI : L5KA.zeros_at MV (F / 8 + 2147450892) 34).
  { apply (proj2 (L5A.zeros_at_vis H10 M10 (F / 8 + 2147450892) 34 (PQHAK.avis_sub H10 (F / 8 + HeapIfaceA.SB) 256 (F / 8 + 2147450892) 34 FSV ltac:(unfold HeapIfaceA.SB; lia) ltac:(unfold HeapIfaceA.SB; lia)))).
    replace (F / 8 + 2147450892) with (HeapIfaceA.S (F + 96)) by (unfold HeapIfaceA.S, HeapIfaceA.SB; rewrite E96; lia). apply PQHAK2.zeros_of_shz. exact VI0. }
  assert (ZV1 : L5KA.zeros_at MV 2147625288 1)
    by exact (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ _ _ _ _ M10 model10 0x154a40 1 B1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(right; right; left; lia)).
  assert (ZV2 : L5KA.zeros_at MV 2147625291 1)
    by exact (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ _ _ _ _ M10 model10 0x154a58 1 B1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(right; right; left; lia)).
  assert (ZV3 : L5KA.zeros_at MV 2147625278 1)
    by exact (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ _ _ _ _ M10 model10 0x1549f0 1 B1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(right; right; left; lia)).
  assert (FDEF : L5.defined M10 F 2048) by (apply (proj1 (L5A.defined_vis H10 M10 F 2048 FV)); exact VFD).
  assert (AV176 : L5A.avis H10 (F + 176) 8) by (apply (PQHAK.avis_sub H10 F 2048 (F + 176) 8 FV); lia).
  assert (AV192 : L5A.avis H10 (F + 192) 8) by (apply (PQHAK.avis_sub H10 F 2048 (F + 192) 8 FV); lia).
  set (W1 := fun a => F + 96 <= a < F + 96 + 8 \/ F + 112 <= a < F + 112 + 8 \/ F + 216 <= a < F + 216 + 8).
  assert (WC1 : forall a, 0 <= a < 2 ^ 64 -> W1 a -> aclientw L ar (X ++ LB) FF' 0 0 a /\ ~ (65536 <= a < 7036928)).
  { intros a Ha Wa. subst W1; cbn beta in Wa. split.
    - apply (fframe_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048. clear - Wa; lia.
    - clear - Wa FR. lia. }
  assert (PF1 : PQHAK2.pfoot F (V2 - 160) V2 W1) by (intros a Wa; subst W1; cbn beta in Wa; clear - Wa; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (OA1 : forall o k2, (F + 32 <= o /\ o + k2 <= F + 96) \/ (F + 120 <= o /\ o + k2 <= F + 216) -> PQHAK2.oav W1 o k2).
  { intros o k2 H12 x Hx. subst W1; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H12 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H12 SX FBIG FR FM8 FBD; lia. }
  assert (SH1 : forall x, F + 120 <= x < F + 432 -> ~ W1 (HeapIfaceA.S x)).
  { intros x Hx. subst W1; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. intros X0; clear - Hx X0 SX FBIG FR FM8 FBD; lia. }
  (* [comment removed for export] *)
  assert (FRD : forall M1 : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ W1 a -> M1 (Z_to_bv 64 a) = M10 (Z_to_bv 64 a)) ->
            forall i, F <= i < F + 2048 -> ~ (F + 96 <= i < F + 104) -> ~ (F + 112 <= i < F + 120) -> ~ (F + 216 <= i < F + 224) -> M1 (Z_to_bv 64 i) = M10 (Z_to_bv 64 i)).
  { intros M1 FR1 i Hi N1 N2 N3. apply FR1; [clear - Hi FR; lia|]. subst W1; cbn beta. unfold HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *.
    intros [X0|[X0|X0]]; [exact (N1 ltac:(clear - X0; lia))| exact (N2 ltac:(clear - X0; lia))| exact (N3 ltac:(clear - X0; lia))]. }
  assert (FRS : forall M1 : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ W1 a -> M1 (Z_to_bv 64 a) = M10 (Z_to_bv 64 a)) ->
            forall a, V2 - 160 <= a < V2 + cls -> M1 (Z_to_bv 64 a) = M10 (Z_to_bv 64 a)).
  { intros M1 FR1 a Ha. apply FR1; [clear - Ha V2R V2S CLS; lia|]. subst W1; cbn beta. unfold HeapIfaceA.SB. intros X0. clear - Ha X0 FCEIL SLO CLS FBD V2R. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  assert (HFIN : forall M1 : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ W1 a -> M1 (Z_to_bv 64 a) = M10 (Z_to_bv 64 a)) -> mem_grows M10 M1 ->
            L5.u64_at RSEGS M1 (F + 216) 1395248 -> PQHAK2.hfin F M1 s (PM.sm_st sm1)).
  { intros M1 FR1 MGM1 U216. assert (FDEF1 : L5.defined M1 F 2048) by (eapply L5.defined_grows; [exact MGM1| exact FDEF]).
    split; [|split].
    - apply (PQHAK2.vstr_keep_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) B1 FIN10 FHF (V2 - 160) V2 W1 M10 M1 SLOW SHW FR1 PF1 (F + 32) s INS);
        [clear - FR; lia| clear - FR; lia| apply OA1; lia| exact VS0].
    - apply (PQHAK2.u64_agA M10 M1 (F + 120) 8 (F + 120) _ (PQHAK.agA_frame M10 M1 W1 (F + 120) 8 FR1 ltac:(clear - FR; lia) ltac:(clear - FR; lia) (OA1 (F + 120) 8 ltac:(lia))));
        [lia| lia| lia| lia| exact IH24].
    - apply (PQHAK2.iosb_revptr M10 M1 (F + 216) _ _ (F + 112) (PM.sm_st sm1) IOS).
      + exact U216.
      + intros i Hi. apply (FRD M1 FR1); clear - Hi FR; lia.
      + intros x Hx. apply FR1; [pose proof (PMKA.S_in_shadow x ltac:(clear - Hx FR; lia)) as SX; unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia|].
        apply SH1; clear - Hx; lia.
      + apply (L5.defined_sub M1 F 2048 (F + 216) 8 FDEF1); lia.
      + clear - FR; lia.
      + clear - FR; lia. }
  destruct s' as [nt | c nt q].
  - (* [comment removed for export] *)
    destruct IVS as (_ & _ & (Hnt & SB0)).
    assert (SBv : L5.u8_at RSEGS MV (F + 176) (2 * nt))
      by (apply (proj2 (L5A.u8_at_vis H10 M10 (F + 176) (2 * nt) (PQHAK.avis_sub H10 (F + 176) 8 (F + 176) 1 AV176 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
    pose proof (PMF.even_byte nt) as EVB.
    LeanFeed.pfeed ident:(PP) (PQAHP3.qhaMs_conc fx10 R10 MV (fun j => match j with 2%nat => V2 | 36%nat => 2 * nt | 40%nat => F | 41%nat => fl | 58%nat => U R10 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - Hnt; lia) | exact F32
                        | exact VFD | exact VFW | exact VFSW | exact VFLW | exact Q5 | exact Q6 | exact VSB | exact VUAR | exact VIC | exact ZI | exact ZV1 | exact ZV2 | exact ZV3
                        | exact SBv | exact EVB | (unfold PQAHP3.aligned; exact V2A) ]).
    destruct PP as (fx1 & R1 & M1v & MG1 & sFR & sFZ & (sMS & sKS & sR10 & sR11 & sR12 & sU112 & sU216 & sU96 & sD1 & sD2 & sD3 & sD4)).
    apply (apiece L ar C HI LYa HIok _ FF' LK10 cr10 A10 M10 model10 fx10 fx1 R10 0xaf64c R1 0xaf6d8 M1v W1 K B1 B2 sMS MG1).
    { intros a Ha Hna. apply sFZ; [exact Ha|..]; intros X0; apply Hna; subst W1; cbn beta; clear - X0; lia. }
    { exact WC1. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (U216 : L5.u64_at RSEGS M1 (F + 216) 1395248)
      by (apply (PQHAK.u64_vis H10 M1 M1v (F + 216) _ VV1 (PQHAK.avis_sub H10 F 2048 (F + 216) 8 FV ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)); exact sU216).
    subst X. cbn [PM.vs_own app] in BI, B1, INS, KONT, WC1.
    apply (stage9_O fx1 R1 M1 model1 K LK10 cr10 A10 s (PM.sm_st sm1) g).
    + apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M10 model10 LK10 cr10 A10 M1 model1 W1 BI HH1 AM1 MRT1 MGM1 FR1).
      intros a Wa. subst W1; cbn beta in Wa. right; left. change (ff_bytes 5) with 2048. clear - Wa; lia.
    + apply (rinvH_ks R R10 R1 V2 cls F PQAHP3.KS_qhaMs RI sKS); vm_compute; reflexivity.
    + exact K0.
    + apply (PQHAK.ls_piece _ M10 M1 W1 FR1); [| exact LS]. intros a Wa. subst W1; cbn beta in Wa. clear - Wa FR. lia.
    + rewrite (sKS 18%nat) by inl. exact R18.
    + rewrite (sKS 20%nat) by inl. exact R20.
    + rewrite (sKS 21%nat) by inl. exact R21.
    + rewrite (sKS 22%nat) by inl. exact R22.
    + rewrite (sKS 23%nat) by inl. exact R23.
    + rewrite (sKS 24%nat) by inl. exact R24.
    + rewrite (sKS 25%nat) by inl. exact R25.
    + rewrite (sKS 26%nat) by inl. exact R26.
    + exact (HFIN M1 FR1 MGM1 U216).
    + apply (L5C.u64_at_agree RSEGS M10 M1 (V2 - 144) (F + 32)); [intros i Hi; apply (FRS M1 FR1); clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa].
    + apply (L5C.u64_at_agree RSEGS M10 M1 (V2 - 136) F); [intros i Hi; apply (FRS M1 FR1); clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb].
    + exact KONT.
  - (* [comment removed for export] *)
    destruct IVS as (_ & _ & (TW0 & TW8 & TW16 & Hnt & Hc & Hc2 & TBP & _)).
    replace (F + 176 + 16) with (F + 192) in TW16 by (clear; lia).
    assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by (clear - Hc; lia).
    pose proof (PMF.u8_of_u64 RSEGS M10 _ _ Hc64 TW0) as SB0.
    pose proof (PMF.odd_byte c Hc2 ltac:(clear - Hc; lia)) as ODB.
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(clear; lia)) as HVB.
    assert (SBv : L5.u8_at RSEGS MV (F + 176) ((c + 1) mod 256))
      by (apply (proj2 (L5A.u8_at_vis H10 M10 (F + 176) _ (PQHAK.avis_sub H10 (F + 176) 8 (F + 176) 1 AV176 ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact SB0).
    assert (TW0v : L5.u64_at RSEGS MV (F + 176) (c + 1)) by (apply (proj2 (L5A.u64_at_vis H10 M10 (F + 176) _ AV176 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW0).
    assert (TW16v : L5.u64_at RSEGS MV (F + 192) q) by (apply (proj2 (L5A.u64_at_vis H10 M10 (F + 192) _ AV192 ltac:(clear - FR; lia) ltac:(clear - FR; lia))); exact TW16).
    assert (INP : In (q, c) (X ++ LB)) by (subst X; cbn [PM.vs_own app]; left; reflexivity).
    destruct (PQHAK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ q c B1 INP) as (P0 & _ & _ & _ & _ & P47 & _).
    LeanFeed.pfeed ident:(PP) (PQAHP3.qhaMl_conc fx10 R10 MV (fun j => match j with 2%nat => V2 | 36%nat => (c + 1) mod 256 | 37%nat => c + 1 | 38%nat => q
                                                      | 40%nat => F | 41%nat => fl | 58%nat => U R10 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | (clear - HVB; lia) | (clear - Hc64; lia) | (clear - P0 P47 Hc; lia)
                        | exact F32 | exact VFD | exact VFW | exact VFSW | exact VFLW | exact Q5 | exact Q6 | exact VSB | exact VUAR | exact VIC | exact ZI | exact ZV1 | exact ZV2 | exact ZV3
                        | exact SBv | exact TW0v | exact TW16v | exact ODB | (unfold PQAHP3.aligned; exact V2A) ]).
    destruct PP as (fx1 & R1 & M1v & MG1 & lFR & lFZ & (lMS & lKS & lR1 & lR10 & lR11 & lR12 & lU112 & lU216 & lU96 & lD1 & lD2 & lD3 & lD4)).
    apply (apiece L ar C HI LYa HIok _ FF' LK10 cr10 A10 M10 model10 fx10 fx1 R10 0xaf64c R1 0xf1fc0 M1v W1 K B1 B2 lMS MG1).
    { intros a Ha Hna. apply lFZ; [exact Ha|..]; intros X0; apply Hna; subst W1; cbn beta; clear - X0; lia. }
    { exact WC1. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (U216 : L5.u64_at RSEGS M1 (F + 216) 1395248)
      by (apply (PQHAK.u64_vis H10 M1 M1v (F + 216) _ VV1 (PQHAK.avis_sub H10 F 2048 (F + 216) 8 FV ltac:(lia) ltac:(lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia)); exact lU216).
    assert (BI1 : Bv W X M1 model1 LK10 cr10 A10).
    { apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M10 model10 LK10 cr10 A10 M1 model1 W1 BI HH1 AM1 MRT1 MGM1 FR1).
      intros a Wa. subst W1; cbn beta in Wa. right; left. change (ff_bytes 5) with 2048. clear - Wa; lia. }
    assert (RI1 : rinvH R R1 V2 cls F) by (apply (rinvH_ks R R10 R1 V2 cls F PQAHP3.KS_qhaMl RI lKS); vm_compute; reflexivity).
    assert (LS1 : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M1).
    { apply (PQHAK.ls_piece _ M10 M1 W1 FR1); [| exact LS]. intros a Wa. subst W1; cbn beta in Wa. clear - Wa FR. lia. }
    pose proof (HFIN M1 FR1 MGM1 U216) as HF1.
    assert (HSTKa1 : L5.u64_at RSEGS M1 (V2 - 144) (F + 32))
      by (apply (L5C.u64_at_agree RSEGS M10 M1 (V2 - 144) (F + 32)); [intros i Hi; apply (FRS M1 FR1); clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa]).
    assert (HSTKb1 : L5.u64_at RSEGS M1 (V2 - 136) F)
      by (apply (L5C.u64_at_agree RSEGS M10 M1 (V2 - 136) F); [intros i Hi; apply (FRS M1 FR1); clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb]).
    (* [comment removed for export] *)
    pose proof BI1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    assert (ASX : L5CA.astk ar M1 (V2 - 160) (PMSPA.pm_scr 0) /\ shadow_zero M1 (V2 - 160 - PMSPA.pm_scr 0) (PMSPA.pm_scr 0 / 8))
      by (eapply PQHASK.callee_stack; first [exact BI1 | eassumption | lia]).
    destruct ASX as (AS0 & _). change (PMSPA.pm_scr 0) with 12288 in AS0.
    pose proof RI1 as (U2' & U8 & U9 & U19 & U21 & U27 & U3 & U4).
    unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMA.AD PnLayoutA.ADDR_A] in OPD.
    apply (OPD fx1 R1 M1 model1 K _ FF' LK10 A10 cr10 q c (V2 - 160) 0xaf6d8 C1 C2 K0 INP).
    { rewrite L5K.rl10. exact lR10. }
    { rewrite L5K.rl1. exact lR1. }
    { split; [lia| reflexivity]. }
    { rewrite L5K.rl2. exact U2'. }
    { rewrite L5K.rl4. rewrite U4. exact TP. }
    { replace (V2 - 160) with (V2 - 160 - 0) by lia. apply (L5SAR.astk_sub ar M1 M1 (V2 - 160) 12288 0 PMSPA.OPDEL_SCR AS0 (fun _ X0 => X0));
        [lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| replace (V2 - 160 - 0) with (V2 - 160) by (clear; lia); exact SPA16]. }
    intros fxo Ro Mo modo Ao RPo HPo MRTo INCAo AMo HHo.
    subst X. cbn [PM.vs_own app] in HPo, HHo, BI1, C1, INS.
    rewrite L5ADHR.lb_remove_head in HPo, HHo.
    unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HPo.
    assert (BIo : Bv W (PM.vs_own s) Mo modo LK10 cr10 Ao).
    { apply (L5AFKR.binv_callee L ar C HI HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W W _ (PM.vs_own s) _ M1 model1 LK10 cr10 A10 Mo modo LK10 cr10 Ao 4096 [] BI1 HPo HHo AMo MRTo INCAo (incl_refl _)).
      - lia.
      - clear - CLS; lia.
      - intros rr a [].
      - intros a _ _ rr [].
      - intros a X0. exact X0. }
    assert (LSo : PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g Mo) by (apply (PQHAK.ls_ahpres L C LY g ar _ FF' (V2 - 160) 4096 [] M1 Mo HPo PQHAK.far_nil LS1)).
    assert (FIN1 : In (F, 5, V2 - 160 + 32) (FF' ++ LK10)) by (apply in_or_app; left; left; reflexivity).
    assert (AGo : forall a, V2 - 160 <= a < V2 + cls -> Mo (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. apply (proj1 HPo a). split; [clear - Ha V2R V2S CLS; lia| split].
      - apply stack_client; [clear - Ha SLO V2S CLS; lia| clear - Ha; lia].
      - intros rr []. }
    apply (stage9_O fxo Ro Mo modo K LK10 cr10 Ao s (PM.sm_st sm1) g).
    + exact BIo.
    + exact (rinvH_pres R R1 Ro V2 cls F RI1 RPo).
    + exact K0.
    + exact LSo.
    + rewrite (cs_of_preserved R1 Ro 18 RPo) by inl. rewrite (lKS 18%nat) by inl. exact R18.
    + rewrite (cs_of_preserved R1 Ro 20 RPo) by inl. rewrite (lKS 20%nat) by inl. exact R20.
    + rewrite (cs_of_preserved R1 Ro 21 RPo) by inl. rewrite (lKS 21%nat) by inl. exact R21.
    + rewrite (cs_of_preserved R1 Ro 22 RPo) by inl. rewrite (lKS 22%nat) by inl. exact R22.
    + rewrite (cs_of_preserved R1 Ro 23 RPo) by inl. rewrite (lKS 23%nat) by inl. exact R23.
    + rewrite (cs_of_preserved R1 Ro 24 RPo) by inl. rewrite (lKS 24%nat) by inl. exact R24.
    + rewrite (cs_of_preserved R1 Ro 25 RPo) by inl. rewrite (lKS 25%nat) by inl. exact R25.
    + rewrite (cs_of_preserved R1 Ro 26 RPo) by inl. rewrite (lKS 26%nat) by inl. exact R26.
    + eapply PQHAK2.hfin_callee; first [ exact LY | exact HIok | exact C1 | exact HPo | exact HF1 | exact FHF | exact FIN1 | apply PQHAK2.wfi_nil | apply PQHAK2.wapart_nil
        | (left; reflexivity) | (split; reflexivity) | (intros x Hx; right; apply in_or_app; left; exact Hx) | (intros x Hx; apply in_or_app; left; exact Hx) | lia ].
    + apply (L5C.u64_at_agree RSEGS M1 Mo (V2 - 144) (F + 32)); [intros i Hi; apply AGo; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa1].
    + apply (L5C.u64_at_agree RSEGS M1 Mo (V2 - 136) F); [intros i Hi; apply AGo; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb1].
    + exact KONT.
Qed.
(* [comment removed for export] *)
Lemma stage9m (fx : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (K : TSet)
      (LK' : list fframe) (cr' : credit) (A' : list (Z * Z)) (s s' : PM.vstr) (sm1 : PM.strm) (g : PMST.st) :
  Bv W (PM.vs_own s' ++ PM.vs_own s) M' model' LK' cr' A' -> rinvH R R' V2 cls F -> K [] -> PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M' ->
  getr R' (reg 18) = Z_to_bv 64 2147450880 -> getr R' (reg 20) = Z_to_bv 64 NEG8 -> getr R' (reg 21) = Z_to_bv 64 (F + 96) ->
  getr R' (reg 22) = Z_to_bv 64 (F + 432) -> getr R' (reg 23) = Z_to_bv 64 (F + 520) -> getr R' (reg 24) = Z_to_bv 64 NEG8 ->
  getr R' (reg 25) = Z_to_bv 64 (F + 592) -> getr R' (reg 26) = Z_to_bv 64 (F + 1168) ->
  PQHAK5.hbaseN F M' s s' sm1 ->
  L5.u64_at RSEGS M' (V2 - 144) (F + 32) -> L5.u64_at RSEGS M' (V2 - 136) F ->
  (forall (fx11 : FPState) (R11 : bvmap 5 word) (M11 : word -> option byte) (model11 : Model) (LK11 : list fframe) (A11 : list (Z * Z)),
      Bv W (PM.vs_own s' ++ PM.vs_own s) M11 model11 LK11 cr' A11 -> rinvH R R11 V2 cls F -> PQSTA.ls_okA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A g M11 ->
      getr R11 (reg 18) = Z_to_bv 64 2147450880 -> getr R11 (reg 20) = Z_to_bv 64 VTT -> getr R11 (reg 21) = Z_to_bv 64 (F + 96) ->
      getr R11 (reg 22) = Z_to_bv 64 (F + 432) -> getr R11 (reg 23) = Z_to_bv 64 (F + 520) -> getr R11 (reg 24) = Z_to_bv 64 NEG8 ->
      getr R11 (reg 25) = Z_to_bv 64 (F + 592) -> getr R11 (reg 26) = Z_to_bv 64 (F + 1168) ->
      PQHAK5.hbaseN F M11 s s' sm1 ->
      L5.u64_at RSEGS M11 (V2 - 144) (F + 32) -> L5.u64_at RSEGS M11 (V2 - 136) F ->
      srealizes RSEGS SCFG (@L5A.cfg fx11 R11 0xaf64c M11 model11) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx R' 0xaf638 M' model') K.
Proof.
  intros BI RI K0 LS R18 R20 R21 R22 R23 R24 R25 R26 HB0 HSTKa HSTKb KONT.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  assert (FM8 : F mod 8 = 0) by (pose proof (proj1 F8) as E8; clear - E8; lia).
  assert (FHF : PQHAK2.hf F) by (unfold PQHAK2.hf, BIGSHADOW_LO, BIGSHADOW_HI; clear - FR FBIG FM8; lia).
  assert (SLOW : ahl_ceil ar <= V2 - 160) by (clear - SLO CLS; lia).
  assert (SHW : BIGSHADOW_HI <= V2 - 160) by (unfold BIGSHADOW_HI; clear - V2R; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FBD : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by (clear - FR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (Q3 : V2 - 160 + 176 <= F \/ F + 2048 <= V2 - 160) by (clear - FCEIL SLO CLS; lia).
  assert (Q4 : V2 - 160 + 176 <= fl \/ fl + 1 <= V2 - 160) by (clear - FLR SLO CLS; lia).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (FIN : In (F, 5, V2 - 160 + 32) (FF' ++ LK')) by (apply in_or_app; left; left; reflexivity).
  pose proof (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' A' BI)
    as ((VW & VIC & VSB & VUAR & VMS) & VOWN & (VFD & VFW & VFSW & VFLC & VFLW) & (FLCc & FLV & FV & SPV & FSV)).
  change (ff_bytes 5) with 2048 in *. change (2048 / 8) with 256 in *.
  set (H' := ahid A' model') in *. set (MV := mrestrict H' M') in *.
  pose proof RI as (X2 & X8 & X9 & X19 & X21 & X27 & X3 & X4).
  assert (Q5 : L5.writable RSEGS MV (V2 - 160) 160) by (eapply L5.writable_sub; [exact VW| clear; lia| clear - CLS; lia]).
  assert (Q6 : L5.u64_at RSEGS MV (F + 2040) fl) by (replace (F + 2040) with (F + 2048 - 8) by (clear; lia); exact VFLC).
  LeanFeed.pfeed ident:(PP) (PQAHP3.qhaM0_conc fx R' MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R' 1 | _ => 0 end)) ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
                      | exact VFD | exact VFW | exact VFSW | exact VFLW | exact Q5 | exact Q6 | exact VSB | exact VUAR | exact VIC | (unfold PQAHP3.aligned; exact V2A) ]).
  destruct PP as (fx1 & R1 & M1v & MG1 & oFR & oFZ & (oMS & oKS & oR10 & oR20 & OQ)). clear OQ.
  set (W1 := fun a => F / 8 + 2147450934 <= a < F / 8 + 2147450934 + 3).
  apply (apiece L ar C HI LYa HIok _ FF' LK' cr' A' M' model' fx fx1 R' 0xaf638 R1 0xaf64c M1v W1 K B1 B2 oMS MG1).
  { intros a Ha Hna. apply oFZ; [exact Ha|..]; intros X0; apply Hna; subst W1; cbn beta; clear - X0; lia. }
  { intros a Ha Wa. subst W1; cbn beta in Wa. split.
    - apply (fframe_shadow_client L ar _ _ 0 0 F 5 (V2 - 160 + 32)). left; reflexivity. change (ff_bytes 5) with 2048.
      unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). unfold HeapIfaceA.SB. clear - Wa. lia.
    - unfold HeapIfaceA.SB in *. clear - Wa FR. lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (PF1 : PQHAK2.pfoot F (V2 - 160) V2 W1) by (intros a Wa; subst W1; cbn beta in Wa; unfold HeapIfaceA.SB; clear - Wa; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (OA1 : forall o k2, F <= o -> o + k2 <= F + 432 -> PQHAK2.oav W1 o k2).
  { intros o k2 H1 H2 x Hx. subst W1; cbn beta. pose proof (PMKA.S_in_shadow x ltac:(clear - Hx H1 H2 FR; lia)) as SX.
    unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. split; intros X0; clear - Hx X0 H1 H2 SX FBIG FR FM8 FBD; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (FR1st : forall a, V2 - 160 <= a < V2 + cls -> M1 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha. apply FR1; [clear - Ha V2R V2S CLS; lia|]. subst W1; cbn beta. intros X0. clear - Ha X0 FBD V2R. lia. }
  apply (KONT fx1 R1 M1 model1 LK' A').
  - apply (L5AFKR.binv_piece L ar HI M model LB FF LK A _ _ _ _ _ _ _ F fl 5 LK2 M2 model2 cr G W _ M' model' LK' cr' A' M1 model1 W1 BI HH1 AM1 MRT1 MGM1 FR1).
    intros a Wa. subst W1; cbn beta in Wa. right; right. change (ff_bytes 5) with 2048. change (2048 / 8) with 256. unfold HeapIfaceA.SB in *. clear - Wa. lia.
  - apply (rinvH_ks R R' R1 V2 cls F PQAHP3.KS_qhaM0 RI oKS); vm_compute; reflexivity.
  - apply (PQHAK.ls_piece _ M' M1 W1 FR1); [intros a Wa; subst W1; cbn beta in Wa; clear - Wa FR; lia| exact LS].
  - rewrite (oKS 18%nat) by inl. exact R18.
  - exact oR20.
  - rewrite (oKS 21%nat) by inl. exact R21.
  - rewrite (oKS 22%nat) by inl. exact R22.
  - rewrite (oKS 23%nat) by inl. exact R23.
  - rewrite (oKS 24%nat) by inl. exact R24.
  - rewrite (oKS 25%nat) by inl. exact R25.
  - rewrite (oKS 26%nat) by inl. exact R26.
  - apply (PQHAK5.hbaseN_piece L ar C SCFG HI HIok _ _ _ _ _ _ _ F (V2 - 160 + 32) B1 FIN FHF (V2 - 160) V2 W1 M' M1 SLOW SHW FR1 PF1 s s' sm1);
      [intros x Hx; apply in_or_app; left; exact Hx| apply OA1; lia| apply OA1; lia| exact HB0].
  - apply (L5C.u64_at_agree RSEGS M' M1 (V2 - 144) (F + 32)); [intros i Hi; apply FR1st; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKa].
  - apply (L5C.u64_at_agree RSEGS M' M1 (V2 - 136) F); [intros i Hi; apply FR1st; clear - Hi CLS; lia| clear - V2R; lia| clear - V2R; lia| exact HSTKb].
Qed.

End Stage.
End SCFG_1.
End PQHA9.
