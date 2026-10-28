(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require MallocShape.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptSlots LeptRecs LeptSel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL LeptCmapArr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptCmap2 O23LeptPixCopyT O23LeptPixCreateT2 O23LeptCloseSpec O23LeptCascW O23LeptTextSelW O23LeptMorphSeqSpec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptPixHdr V23LeptCmapValid V23LeptCmap2 V23LeptPixDestroy V23LeptPixDestroyK V23LeptPixMisc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptPixCopyT V23LeptPixCreateT2 V23LeptSelGP V23LeptMbc V23LeptDilW V23LeptRb2W V23LeptCascW V23LeptCloseSpec V23LeptMorphSeqSpec V23LeptUddSegs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptUddLib O23LeptUddSegs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptSelGP.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac hideH H := lazymatch type of H with ?P => change P with (O23LeptUddLib.hide P) in H end.

(* [comment removed for export] *)


(* [comment removed for export] *)
Section Pix.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.

(* [comment removed for export] *)
Lemma POSTM_src_pw : forall C A s (M1 M2 m' : word -> option byte), (forall a, M1 a = M2 a) -> POSTM C A s M1 m' -> POSTM C A s M2 m'.
Proof.
  intros C A s M1 M2 m' HM [F L]. split.
  - unfold FRM in *. intros x H1 H2 H3 H4 H5. rewrite <- HM. exact (F x H1 H2 H3 H4 H5).
  - unfold LIVK in *. intros q k i Hq Hi. rewrite <- HM. exact (L q k i Hq Hi).
Qed.
Lemma POSTM_both : forall C A s m1 mk (a : word) bs, POSTM C A s m1 mk -> POSTM C A s (wbytes m1 a bs) (wbytes mk a bs).
Proof.
  intros C A s m1 mk a bs [F L].
  assert (WP : forall (x : word) (bs' : list byte) (a' : word) (f g : word -> option byte), f x = g x -> wbytes f a' bs' x = wbytes g a' bs' x).
  { intros x bs'. induction bs' as [|b r IH]; intros a' f g E; cbn [wbytes]; [exact E|].
    apply IH. cbv beta. destruct (bv_eqb x a'); [reflexivity | exact E]. }
  split.
  - unfold FRM in *. intros x H1 H2 H3 H4 H5. apply WP. exact (F x H1 H2 H3 H4 H5).
  - unfold LIVK in *. intros q k i Hq Hi. apply WP. exact (L q k i Hq Hi).
Qed.
(* [comment removed for export] *)
Definition UDC (m : word -> option byte) (s : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 f0 f1 : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) /\
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) /\
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) /\
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) /\
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v5) /\
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v6) /\
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v7) /\
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v8) /\
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v9) /\
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v10) /\
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v11) /\
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 f0) /\
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 f1).

Lemma UDC_UDF : forall m s ret regs fr, (256 <= s)%Z -> (s < 2 ^ 64)%Z ->
  UDC (O23LeptUddSegs.UDF m s ret regs fr) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
      (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (reg_get fr 8) (reg_get fr 9).
Proof.
  intros m s ret regs fr Hs1 Hs2. unfold UDC, O23LeptUddSegs.UDF.
  repeat match goal with |- _ /\ _ => split end; rdn_solve.
Qed.

(* [comment removed for export] *)
Lemma UDC_pw : forall m m' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 f0 f1, (256 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (forall (b : Z) (n : nat), (s - 120 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS m' (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n) ->
  UDC m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 f0 f1 -> UDC m' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 f0 f1.
Proof.
  intros m m' s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 f0 f1 Hs1 Hs2 Hpw HU.
  unfold UDC in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    (erewrite Hpw; [eassumption | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
Qed.

(* [comment removed for export] *)
Lemma dst_rd : forall C A' (m m' : word -> option byte) (s' pp b : Z) (n : nat), Cok C ->
  (c_top C - LSTK <= s')%Z -> (0 <= s')%Z -> (s' <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  POSTM C A' (pp + 8) m m' -> (forall a : word, (s' <= u a < pp)%Z -> m' a = m a) ->
  (s' <= b)%Z -> (b + Z.of_nat n <= 2 ^ 64)%Z -> (b + Z.of_nat n <= pp \/ pp + 8 <= b)%Z ->
  rdn SEGS m' (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n.
Proof.
  intros C A' m m' s' pp b n CK Hlo Hs0 Hsp Hpp [F _] Hlow Hb Hbn Hcase.
  pose proof (ck_sp0 _ CK) as Q1. pose proof (ck_sp0hi _ CK) as Q2.
  destruct Hcase as [Hc | Hc].
  - apply rdn_ext.
    + rewrite u_Z2bv by lia. lia.
    + intros x Hx. rewrite u_Z2bv in Hx by lia. apply Hlow. lia.
  - exact (FRM_rdn16 C (pp + 8) m m' b n CK F Hc Hbn ltac:(lia)).
Qed.

End Pix.
