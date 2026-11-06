(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module PGV.
(* [comment removed for export] *)
Definition pgsel (ne X : expr) : expr :=
  EAlu ALU_ADD (EAlu ALU_AND ne (ELit 7)) (EMd M_MUL (EAlu ALU_SLTU (EAlu ALU_AND ne (ELit 7)) (ELit 1)) X).
(* [comment removed for export] *)
Definition zero_diff (k : list kentry) (a b : expr) : bool :=
  match erange k (mkAlu ALU_SUB a b) with Some (lo, hi) => (Z.eqb lo 0 && Z.eqb hi 0)%bool | None => false end.
Definition pg_match (v : expr) : option (expr * expr * expr) :=
  match v with
  | EAlu ALU_ADD (EAlu ALU_AND ne1 (ELit 7)) (EMd M_MUL (EAlu ALU_SLTU (EAlu ALU_AND ne2 (ELit 7)) (ELit 1)) X) => Some (ne1, ne2, X)
  | _ => None
  end.
Definition pgsel2 (ne1 ne2 X : expr) : expr :=
  EAlu ALU_ADD (EAlu ALU_AND ne1 (ELit 7)) (EMd M_MUL (EAlu ALU_SLTU (EAlu ALU_AND ne2 (ELit 7)) (ELit 1)) X).
Lemma pg_match_eq : forall v ne1 ne2 X, pg_match v = Some (ne1, ne2, X) -> v = pgsel2 ne1 ne2 X.
Proof.
  intros v ne1 ne2 X H. unfold pg_match in H.
  repeat (lazymatch type of H with
          | Some _ = Some _ => fail
          | context [match ?x with _ => _ end] => destruct x; try discriminate
          end).
  injection H as <- <- <-. reflexivity.
Qed.
(* [comment removed for export] *)
Definition strip_b1 (v : expr) : expr := match v with EExt false 0 1 v' => v' | _ => v end.
(* [comment removed for export] *)
Definition partial_val_ok (k : list kentry) (ne v0 : expr) : bool :=
  let v := strip_b1 v0 in
  zero_diff k v (mkAlu ALU_AND ne (ELit 7)) ||
  match pg_match v with
  | Some (ne1, ne2, _) => zero_diff k ne1 ne && zero_diff k ne2 ne
  | None => false
  end.
(* [comment removed for export] *)
Definition zero_diffB (bc : AX2B.bctx) (a b : expr) : bool :=
  match AX2B.erangeB bc (mkAlu ALU_SUB a b) with Some (lo, hi) => (Z.eqb lo 0 && Z.eqb hi 0)%bool | None => false end.
Definition partial_val_okB (bc : AX2B.bctx) (ne v0 : expr) : bool :=
  let v := strip_b1 v0 in
  if zero_diffB bc v (mkAlu ALU_AND ne (ELit 7)) then true else
  match pg_match v with
  | Some (ne1, ne2, _) => if zero_diffB bc ne1 ne then zero_diffB bc ne2 ne else false
  | None => false
  end.
Lemma partial_val_okB_eqf : forall k, partial_val_okB (AX2B.mkbc k) = partial_val_ok k.
Proof.
  intros k. apply functional_extensionality; intros ne. apply functional_extensionality; intros v0.
  unfold partial_val_okB, partial_val_ok, zero_diffB, zero_diff. rewrite AX2B.erangeB_eqf. reflexivity.
Qed.
End PGV.
