(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma byte_list_eq : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x t IH]; intros [|y u] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hx Ht. f_equal; [apply bv_eq; exact Hx | apply IH; exact Ht].
Qed.

Section P.
  Variable SEGS : list Segment.

  Lemma cellw_of_pins : forall rs M (a : Z) (w : N) (v : Z) zs,
    pins rs M -> 0 <= a -> a + Z.of_N w <= 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
    lookup_runs rs a (N.to_nat w) = Some zs ->
    map (fun z => z mod 256) zs = map bv_unsigned (word_to_le_bytes (N.to_nat w) (Z_to_bv 64 v)) ->
    cellw SEGS M a w v.
  Proof using SEGS.
    intros rs M a w v zs HP Ha Hw Hv HL HE. split; [exact Hv|].
    rewrite (rdn_of_pins SEGS rs M (N.to_nat w) a zs HP Ha ltac:(lia) HL). f_equal.
    apply byte_list_eq. rewrite <- HE. rewrite map_map. apply map_ext. intros z.
    rewrite Z_to_bv_unsigned. reflexivity.
  Qed.
End P.

Definition runs_bound (rs : list run) (hi : Z) : bool :=
  forallb (fun r => Z.leb 0 (fst r) && Z.leb (fst r + Z.of_nat (length (snd r))) hi) rs.

Lemma pins_agree_low : forall rs M M' hi,
  pins rs M -> runs_bound rs hi = true -> hi <= 2 ^ 64 ->
  (forall a, 0 <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> pins rs M'.
Proof.
  intros rs M M' hi HP HB Hhi HA. eapply pins_same; [exact HP|]. intros a Ha.
  destruct (in_runs_covered rs (bv_unsigned a) Ha) as ([q bs] & Hin & Hq). cbn [fst snd] in Hq.
  unfold runs_bound in HB. rewrite forallb_forall in HB. specialize (HB (q, bs) Hin). cbn [fst snd] in HB.
  apply andb_prop in HB. destruct HB as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  rewrite <- (Z_to_bv_bv_unsigned 64 a). apply HA. lia.
Qed.

Ltac vm_lhs := lazymatch goal with |- ?l = _ => let v := eval vm_compute in l in change l with v end.
Ltac kpin HP :=
  eapply (cellw_of_pins _ _ _ _ _ _ _ HP); [cbv; lia | cbv; lia | cbv; lia | vm_lhs; reflexivity | vm_compute; reflexivity].

Ltac kc := try unfold A_CTYPE_ID; try unfold A_CTYPE_OBJ; try unfold LOC_IMP; try unfold FACETS_BEG; try unfold FACETS_END;
           try unfold VT_CTYPE; try unfold TD_LOCALE; cbn; lia.
Ltac kabs HP :=
  eapply kword_abs; [ | | | | evs; reflexivity];
  [ eapply (cellw_of_pins _ _ _ _ _ _ _ HP); [kc | kc | kc | vm_lhs; reflexivity | vm_compute; reflexivity]
  | kc | kc | kc ].
