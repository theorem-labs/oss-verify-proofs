(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma tset_tset_same {A} : forall (p : positive) (x y : A) t, tset p y (tset p x t) = tset p y t.
Proof.
  induction p; intros x y [|l v r]; cbn; try reflexivity; rewrite ?IHp; reflexivity.
Qed.

Lemma tset_tset_comm {A} : forall (p q : positive) (x y : A) t, p <> q -> tset p x (tset q y t) = tset q y (tset p x t).
Proof.
  induction p; intros q x y t Hne; destruct q; destruct t as [|l v r]; cbn; try reflexivity;
    try (rewrite IHp by congruence; reflexivity); try congruence.
Qed.

Lemma regupd_shadow : forall regs (r : reg) x y, regupd (regupd regs r x) r y = regupd regs r y.
Proof. intros. unfold regupd, bvmap_set. apply tset_tset_same. Qed.

Lemma regupd_comm : forall regs (r s : reg) x y, r <> s -> regupd (regupd regs s y) r x = regupd (regupd regs r x) s y.
Proof.
  intros regs r s x y Hne. unfold regupd, bvmap_set. apply tset_tset_comm.
  intros E. apply Hne. apply bv_key_inj. exact E.
Qed.

Lemma regupd_eq3 : forall rg rg' (i : reg) v v', rg = rg' -> v = v' -> regupd rg i v = regupd rg' i v'.
Proof. intros; subst; reflexivity. Qed.

(* [comment removed for export] *)
Ltac reg_index r := lazymatch r with Z_to_bv 5 ?z => z | @BV 5 ?z _ => z | _ => constr:(100%Z) end.
Ltac rnorm_raw :=
  repeat match goal with
  | |- context [regupd (regupd ?rg ?s ?y) ?r ?x] =>
      first [ constr_eq r s; rewrite (regupd_shadow rg r y x)
            | let zr := eval cbv in (bv_unsigned r) in
              let zs := eval cbv in (bv_unsigned s) in
              lazymatch (eval cbv in (Z.ltb zr zs)) with
              | true => rewrite (regupd_comm rg r s x y) by (let E := fresh in intros E; discriminate E)
              end ]
  end.

(* [comment removed for export] *)
Ltac rnorm :=
  lazymatch goal with
  | |- ?REL ?segs (?mk ?R ?pc ?M ?rom) ?B =>
      let mx := fresh "mx" in let bx := fresh "bx" in
      set (mx := M); set (bx := B); rnorm_raw; subst mx bx
  | |- _ => rnorm_raw
  end.
