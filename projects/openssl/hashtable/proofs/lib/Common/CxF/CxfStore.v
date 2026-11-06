(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module CXFS.
Import AX2. Import AX2B.
Fixpoint wr_cheap (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if Z.leb kk (a_off a)
          then if expr_eqb (a_base a) kb
               then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
               else false
          else false)
      then true
      else wr_cheap bc rest a n
  | _ :: rest => wr_cheap bc rest a n
  end.
Definition storeok_scF (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  if wr_cheap bc (bc_fk bc) a n then [] else if wr_coveredB bc (bc_fk bc) a n then [] else [SCStoreOk a n].
Lemma wr_cheap_covered : forall bc kn a n, wr_cheap bc kn a n = true -> wr_coveredB bc kn a n = true.
Proof.
  intros bc kn a n. induction kn as [|K rest IH]; intros H; [discriminate|].
  destruct K as [| | | | | |[kb kk] len| | |]; cbn [wr_cheap wr_coveredB] in H |- *; try (apply IH; exact H).
  destruct (Z.leb kk (a_off a)) eqn:E1; destruct (expr_eqb (a_base a) kb) eqn:E2; cbn [andb] in H |- *;
    try (destruct (xinsideB bc (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len); [reflexivity | apply IH; exact H]).
  destruct (match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end); [reflexivity|].
  destruct (xinsideB bc (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len); [reflexivity | apply IH; exact H].
Qed.
Lemma storeok_scF_eq : forall bc a n, storeok_scF bc a n = storeok_scB bc a n.
Proof.
  intros bc a n. unfold storeok_scF, storeok_scB. destruct (wr_cheap bc (bc_fk bc) a n) eqn:E; [|reflexivity].
  rewrite (wr_cheap_covered _ _ _ _ E). reflexivity.
Qed.
Lemma storeok_scF_eqf : storeok_scF = storeok_scB.
Proof. apply functional_extensionality; intros bc. apply functional_extensionality; intros a. apply functional_extensionality; intros n. apply storeok_scF_eq. Qed.
End CXFS.
