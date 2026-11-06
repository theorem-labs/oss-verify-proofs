(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec StepTac MmapSim Frame MemSplit CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff LibTail S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DRep DiagPins.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Lemma fld4_of_bytes : forall M a b0 b1 b2 b3 v,
  0 <= a -> a + 4 < 2 ^ 64 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  fld SEGS M a 1 b0 -> fld SEGS M (a + 1) 1 b1 -> fld SEGS M (a + 2) 1 b2 -> fld SEGS M (a + 3) 1 b3 ->
  map bv_unsigned [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 b2; Z_to_bv 8 b3] = map bv_unsigned (word_to_le_bytes 4 (Z_to_bv 64 v)) ->
  fld SEGS M a 4 v.
Proof.
  intros M a b0 b1 b2 b3 v Ha Ha4 H0 H1 H2 H3 F0 F1 F2 F3 HE. unfold fld in *.
  rewrite w1_bytes_small in F0, F1, F2, F3 by lia.
  pose proof (rdn_app_Z SEGS M a 1 1 _ _ F0 ltac:(cbn [Z.of_nat Pos.of_succ_nat]; exact F1) ltac:(lia) ltac:(cbn; lia)) as G1.
  pose proof (rdn_app_Z SEGS M a 2 1 _ _ G1 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; exact F2) ltac:(lia) ltac:(cbn; lia)) as G2.
  pose proof (rdn_app_Z SEGS M a 3 1 _ _ G2 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; exact F3) ltac:(lia) ltac:(cbn; lia)) as G3.
  cbn [Nat.add app] in G3. rewrite G3. f_equal. apply DiagPins.byte_list_eq. exact HE.
Qed.

Lemma ios_inv_refill : forall M M' io sb fl fill fill',
  ios_inv M io sb fl fill -> 0 <= io -> io + 152 <= 2 ^ 47 ->
  agree_on (fun a => zwin io (io + 152) a /\ ~ zwin (io + 24) (io + 32) a /\ ~ zwin (io + 144) (io + 148) a) M M' ->
  fld SEGS M' (io + 24) 8 0 -> fld SEGS M' (io + 144) 4 fill' -> (fill' = 2 ^ 32 - 1 \/ fill' = 32) ->
  ios_inv M' io sb fl fill'.
Proof.
  intros M M' io sb fl fill fill' II Hio0 Hio1 HA HW HF Hf'. destruct II as [Ivt Ifl Iflr Iprec Iwid Ist Iexc Irdbuf Iloc Izero Itie Ifill Ifillr].
  assert (FO : forall a (k : nat) v, io <= a -> (a + Z.of_nat k <= io + 24 \/ io + 32 <= a) -> a + Z.of_nat k <= io + 144 -> fld SEGS M a k v -> fld SEGS M' a k v).
  { intros a k v Ho Hm Hk HF0. eapply (fld_ag M M' (fun a => zwin io (io + 152) a /\ ~ zwin (io + 24) (io + 32) a /\ ~ zwin (io + 144) (io + 148) a)); [lia | lia | | exact HA | exact HF0].
    intros x Hx. unfold zwin. lia. }
  constructor; try assumption.
  - apply FO; [lia | cbn; lia | cbn; lia | assumption].
  - apply FO; [lia | cbn; lia | cbn; lia | assumption].
  - apply FO; [lia | cbn; lia | cbn; lia | assumption].
  - apply FO; [lia | cbn; lia | cbn; lia | assumption].
  - apply FO; [lia | cbn; lia | cbn; lia | assumption].
  - apply FO; [lia | cbn; lia | cbn; lia | assumption].
  - apply FO; [lia | cbn; lia | cbn; lia | assumption].
  - intros i Hi. apply FO; [lia | cbn; lia | cbn; lia |]. apply Izero. exact Hi.
  - apply FO; [lia | cbn; lia | cbn; lia | assumption].
Qed.

Lemma ios_inv_setwidth : forall M io sb fl fill,
  ios_inv M io sb fl fill -> 0 <= io -> io + 152 <= 2 ^ 47 ->
  ios_inv (wbytes M (Z_to_bv 64 (io + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) io sb fl fill.
Proof.
  intros M io sb fl fill II Hio0 Hio1.
  set (M' := wbytes M (Z_to_bv 64 (io + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (OUT : forall x : word, ~ (io + 24 <= bv_unsigned x < io + 32) -> M' x = M x).
  { intros x Hx. subst M'. apply wbytes_outside; rewrite ?length_N_to_le_bytes; [|rewrite u_small by lia; cbn; lia].
    unfold in_rng. rewrite u_small by lia. cbn. lia. }
  assert (FO : forall a (k : nat) v, io <= a -> (a + Z.of_nat k <= io + 24 \/ io + 32 <= a) -> a + Z.of_nat k <= io + 152 ->
               fld SEGS M a k v -> fld SEGS M' a k v).
  { intros a k v Ho Hd Hk HF. eapply (fld_ag M M' (fun x => a <= x < a + Z.of_nat k)); [lia | lia | intros x Hx; exact Hx | | exact HF].
    intros x Hx. apply OUT. rewrite u_small by lia. lia. }
  destruct II as [Ivt Ifl Iflr Iprec Iwid Ist Iexc Irdbuf Iloc Izero Itie Ifill Ifillr].
  constructor; try assumption; try (apply FO; [lia | cbn; lia | cbn; lia | assumption]).
  - subst M'. unfold CRep.fld.
    replace 8%nat with (length (word_to_le_bytes 8 (Z_to_bv 64 0))) at 1 by (rewrite length_N_to_le_bytes; reflexivity).
    apply rdn_wbytes_hit. rewrite length_N_to_le_bytes, u_small by lia. cbn. lia.
  - intros i Hi. apply FO; [lia | cbn; lia | cbn; lia |]. apply Izero. exact Hi.
Qed.

Lemma w2lb_mod : forall (n : nat) v, (n <= 8)%nat ->
  word_to_le_bytes n (Z_to_bv 64 v) = word_to_le_bytes n (Z_to_bv 64 (v mod 2 ^ (8 * Z.of_nat n))).
Proof.
  intros n v Hn. unfold word_to_le_bytes. rewrite !Z_to_bv_unsigned.
  rewrite !(Z_to_le_bytes_wrap n 64) by lia.
  replace (v mod 2 ^ (8 * Z.of_nat n)) with (bv_wrap (N.of_nat (8 * n)) v).
  - symmetry. apply Z_to_le_bytes_wrap. lia.
  - unfold bv_wrap, bv_modulus. f_equal. f_equal. lia.
Qed.

Lemma fld8_zero_b1 : forall M a, 0 <= a -> a + 8 <= 2 ^ 64 -> fld SEGS M a 8 0 -> fld SEGS M (a + 1) 1 0.
Proof.
  intros M a Ha Ha8 H. unfold fld in *.
  pose proof (rdn_sub SEGS M 8 (Z_to_bv 64 a) _ 1 1 H ltac:(lia)) as X. unfold at_ in X. rewrite u64_of_Z in X by lia.
  change (Z.of_nat 1) with 1 in X. rewrite X. first [reflexivity | f_equal; apply DiagPins.byte_list_eq; vm_compute; reflexivity].
Qed.
Lemma fld8_byte0' : forall M a v, fld SEGS M a 8 v -> fld SEGS M a 1 (v mod 256).
Proof.
  intros M a v H. unfold fld. rewrite (fld8_byte0 SEGS M a v H). rewrite w1_bytes_small by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.

Lemma lo16_zero : forall M a v, fld SEGS M a 8 v -> fld SEGS M a 2 0 -> 0 <= v < 2 ^ 64 -> v mod 256 = 0.
Proof.
  intros M a v H8 H2 Hv.
  pose proof (fld8_byte0 SEGS M a v H8) as X1. unfold fld in H2.
  pose proof (SeqExec.rdn_firstn SEGS M 2 (Z_to_bv 64 a) _ 1 H2 ltac:(lia)) as X2.
  rewrite X1 in X2. assert (E : bv_unsigned (Z_to_bv 8 (v mod 256)) = bv_unsigned (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0)))).
  { f_equal. unfold word_to_le_bytes in X2. cbn [Z_to_le_bytes firstn] in X2. congruence. }
  rewrite u64_of_Z in E by lia. rewrite !u8_of_Z in E by (try apply Z.mod_pos_bound; lia). exact E.
Qed.

Lemma fld8_zero_of_repeat : forall M p (N : nat) d,
  0 <= p -> p + Z.of_nat N < 2 ^ 64 -> 0 <= d -> d + 8 <= Z.of_nat N ->
  fld SEGS (wbytes M (Z_to_bv 64 p) (repeat (SumMemsetLib.cbyte (Z_to_bv 64 0)) N)) (p + d) 8 0.
Proof.
  intros M p N d Hp HN Hd Hd8. unfold fld. rewrite (rdn_repeat_sub SEGS M _ p N d 8) by lia.
  first [reflexivity | f_equal; apply DiagPins.byte_list_eq; vm_compute; reflexivity].
Qed.
