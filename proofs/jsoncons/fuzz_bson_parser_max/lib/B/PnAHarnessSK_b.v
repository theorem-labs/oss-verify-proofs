(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b L5AFrameKR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout PmLayoutA PmModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnStepA_b
     PnAHarnessStmts_b PnAHarnessKit_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PNHASK.
Import L5A. Import L5CA. Import L5SAR. Import PNHAS.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.

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
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 5, V2 - 128 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 5, V2 - 128 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 5).
Local Notation FF' := ((F, 5, V2 - 128 + 32) :: FF).

(* [comment removed for export] *)
Lemma callee_stack BX Mc modelc LKc crc Ac h :
  Bv W BX Mc modelc LKc crc Ac -> 0 <= h <= 11 ->
  L5CA.astk ar Mc (V2 - 128) (PMSPA.pm_scr h) /\ shadow_zero Mc (V2 - 128 - PMSPA.pm_scr h) (PMSPA.pm_scr h / 8).
Proof.
  intros BI Hh. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  unfold PMSPA.pm_scr.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (AL1 : (V2 + cls - 36864) mod 8 = 0) by (clear - CLS V2A; lia).
  assert (AL2 : (V2 - 128 - (12288 + 2048 * h)) mod 8 = 0) by (clear - V2A; lia).
  assert (AL3 : (V2 + cls - (128 + cls)) mod 16 = 0) by (clear - V2A; lia).
  assert (DV : (12288 + 2048 * h) / 8 = 1536 + 256 * h) by (clear; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  rewrite DV. split.
  - replace (V2 - 128) with ((V2 + cls) - (128 + cls)) by (clear; lia).
    apply (L5SAR.astk_sub ar Mc Mc (V2 + cls) 36864 (128 + cls) (12288 + 2048 * h) B6 (fun _ X => X)); [clear - CLS; lia| clear - Hh; lia| clear - CLS Hh; lia| exact AL3].
  - apply (PMKA.shadow_zero_sub Mc (V2 + cls - 36864) 4608); [exact AL1| exact AL2| clear - CLS Hh; lia| clear - CLS Hh; lia| clear - Hh; lia|].
    apply (PMKA.stksh_keepA L ar LB FF (V2 + cls) 36864 W M Mc B7 WAPP); [clear - SLO SPT; lia| clear - SLO SPT; lia| clear - V2S CLS; lia| exact AL1| lia| exact STKSH].
Qed.

Lemma callee_entry BX Mc modelc LKc crc Ac Rc r h :
  Bv W BX Mc modelc LKc crc Ac -> rinvH R Rc V2 cls F -> getr Rc (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> 0 <= h <= 11 ->
  PMSPA.entryA PMA.AD L ar Rc Mc (V2 - 128) r h.
Proof.
  intros BI RI R1 RA Hh. pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
  destruct (callee_stack BX Mc modelc LKc crc Ac h BI Hh) as (AS & SZ).
  split; [rewrite L5K.rl1; exact R1|]. split; [exact RA|]. split; [rewrite L5K.rl2; exact X2|].
  split; [rewrite L5K.rl3, X3; exact GP|]. split; [rewrite L5K.rl4, X4; exact TP|]. split; [exact AS| exact SZ].
Qed.

Lemma callee_room BX Mc modelc LKc crc Ac h :
  Bv W BX Mc modelc LKc crc Ac -> h <= 11 -> PMSPA.ffroomA h FF' LKc.
Proof.
  intros BI Hh. pose proof BI as (B1 & B2 & B3 & B4 & B5 & _).
  assert (NDF : NoDup (map ff_addr (FF' ++ LKc))).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  intros k0 Hk0. specialize (ROOM LKc B5 NDF k0 Hk0). lia.
Qed.

Lemma callee_rs : PMSPA.ffrsA FF' (V2 - 128).
Proof. intros f [<-|Hf]; [cbn [ff_rs fst snd]; lia| specialize (FFRS f Hf); clear - Hf FFRS CLS; lia]. Qed.

Lemma callee_frame : F mod 2048 = 0 -> PNRA.frame_okB FF' F.
Proof. intros H. split; [exists (V2 - 128 + 32); left; reflexivity| exact H]. Qed.
Lemma callee_roomB BX Mc modelc LKc crc Ac h :
  Bv W BX Mc modelc LKc crc Ac -> h <= 11 -> PGSA.ffroomB PNRA.FCB h FF' LKc.
Proof. intros BI Hh. exact (callee_room BX Mc modelc LKc crc Ac h BI Hh). Qed.
(* [comment removed for export] *)
Lemma own_shz BX Mc modelc LKc crc Ac : Bv W BX Mc modelc LKc crc Ac -> shadow_zero Mc (V2 - 128) 16.
Proof.
  intros BI. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (AL1 : (V2 + cls - 36864) mod 8 = 0) by (clear - CLS V2A; lia).
  assert (AL2 : (V2 - 128) mod 8 = 0) by (clear - V2A; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (PMKA.shadow_zero_sub Mc (V2 + cls - 36864) 4608); [exact AL1| exact AL2| clear - CLS; lia| clear - CLS; lia| lia|].
  apply (PMKA.stksh_keepA L ar LB FF (V2 + cls) 36864 W M Mc B7 WAPP); [clear - SLO SPT; lia| clear - SLO SPT; lia| clear - V2S CLS; lia| exact AL1| lia| exact STKSH].
Qed.
End Stage.
End SCFG_1.
End PNHASK.
