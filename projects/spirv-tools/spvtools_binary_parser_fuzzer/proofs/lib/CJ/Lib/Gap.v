(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require PlacementGap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Fixpoint zsum {A} (f : A -> Z) (l : list A) : Z :=
  match l with [] => 0 | x :: l' => f x + zsum f l' end.

Lemma zsum_app {A} (f : A -> Z) l1 l2 : zsum f (l1 ++ l2) = zsum f l1 + zsum f l2.
Proof. induction l1; cbn; lia. Qed.

Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).

Section SLOTS.
Variables (F n' : Z).
Hypothesis Hn : 0 < n'.

Definition touches (e : Z * Z) (k : Z) : bool :=
  (fst e <? F + (k + 1) * n') && (F + k * n' <? fst e + snd e).

End SLOTS.

Definition wwZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).

Definition bottomup_floor : Z := PlacementGap.bottomup_floor.
Lemma bottomup_floor_val : bottomup_floor = 46912496119808.
Proof. reflexivity. Qed.
Lemma alloc_ceiling_val' : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. exact ac_bounds_lit. Qed.

Theorem kgap_exists (ents : list (word * word)) (nZ E B : Z) :
  0 < nZ -> nZ mod page_size = 0 ->
  zlen ents <= E -> zsum (fun e => bv_unsigned (snd e)) ents <= B -> 0 <= B ->
  B / nZ + 2 * E < (alloc_ceiling - bottomup_floor) / nZ ->
  exists a, bottomup_floor <= a /\ a + nZ <= alloc_ceiling /\ a mod page_size = 0 /\ 0 < a /\
            region_free ents (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true.
Proof.
  intros Hn Hal HE HB HB0 HK.
  pose proof alloc_ceiling_val' as HC.
  assert (EZ : forall l : list (word * word), zlen l = PlacementGap.zlen l) by reflexivity.
  assert (ES : forall l : list (word * word), zsum (fun e => bv_unsigned (snd e)) l
                                            = PlacementGap.zsum (fun e => bv_unsigned (snd e)) l).
  { induction l as [|x l IH]; cbn; [reflexivity | rewrite IH; reflexivity]. }
  apply (PlacementGap.gap_exists ents bottomup_floor alloc_ceiling nZ E B);
    try (unfold bottomup_floor, PlacementGap.bottomup_floor; first [lia | reflexivity]); try assumption.
  all: first [ rewrite <- EZ; exact HE | rewrite <- ES; exact HB ].
Qed.

End AC_1.
