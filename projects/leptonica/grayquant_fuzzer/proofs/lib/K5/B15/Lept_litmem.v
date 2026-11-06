(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_gaps_iface.
Import ListNotations.
Open Scope Z_scope.

Lemma lept_lit_In : forall a l, existsb (fun r => andb (Z.eqb (fst r) a) (Z.eqb (snd r) l)) LEPT_LITS = true -> In (a, l) LEPT_LITS.
Proof.
  intros a l H. apply existsb_exists in H as ([a' l'] & Hin & E). cbn [fst snd] in E.
  apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst a' l'. exact Hin.
Qed.

Definition lept_lit_len (a : Z) : option Z := option_map snd (find (fun r => Z.eqb (fst r) a) LEPT_LITS).
Lemma lept_lit_len_In : forall a l, lept_lit_len a = Some l -> In (a, l) LEPT_LITS.
Proof.
  intros a l H. unfold lept_lit_len in H. destruct (find _ LEPT_LITS) as [[a' l']|] eqn:F; [|discriminate].
  cbn in H. injection H as <-. apply find_some in F as [Hin E]. cbn [fst] in E. apply Z.eqb_eq in E. subst a'. exact Hin.
Qed.
Lemma lept_lit_ex : forall a, existsb (fun r => Z.eqb (fst r) a) LEPT_LITS = true -> exists l, In (a, l) LEPT_LITS.
Proof.
  intros a H. apply existsb_exists in H as ([a' l] & Hin & E). cbn [fst] in E. apply Z.eqb_eq in E. subst a'. exists l. exact Hin.
Qed.

Ltac lit_in_fast :=
  first [ apply lept_lit_ex; vm_compute; reflexivity
        | apply lept_lit_In; vm_compute; reflexivity
        | eexists; unfold LEPT_LITS; repeat first [ left; reflexivity | right ] ].
