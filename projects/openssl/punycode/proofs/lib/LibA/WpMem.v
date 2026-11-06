(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac solve_cell :=
  first [ eassumption
        | eapply cell_store_same'; [lia | lia | lia]
        | apply cell_store_other; [lia | lia | lia | rewrite ?length_N_to_le_bytes; lia
                                  | rewrite ?length_N_to_le_bytes; lia | solve_cell ] ].

(* [comment removed for export] *)
Ltac solve_store :=
  match goal with
  | H : wr_ok _ _ _ _ |- store_ok _ _ _ _ = true =>
      eapply wr_ok_store; [eapply wr_ok_grows; [|exact H]; solve_grows | lia | lia]
  end.

(* [comment removed for export] *)
Ltac name_mem Mn :=
  match goal with
  | |- context [load_ok _ (wbytes ?a ?b ?c) _ _ _] => set (Mn := wbytes a b c) in *
  | |- context [store_ok _ (wbytes ?a ?b ?c) _ _] => set (Mn := wbytes a b c) in *
  | |- context [reach _ _ _ _ (wbytes ?a ?b ?c) _] => set (Mn := wbytes a b c) in *
  end.
Ltac unname_mems := repeat match goal with Mx := wbytes _ _ _ |- _ => subst Mx end.

(* [comment removed for export] *)
Ltac mem_auto :=
  repeat (rewrite ?addi_W;
    lazymatch goal with
    | |- exists v, load_ok _ _ _ 8%nat v /\ _ =>
        eexists; split; [unname_mems; apply load_cell8; solve_cell|]
    | |- exists v, load_ok _ _ _ 1%nat v /\ _ =>
        eexists; split; [unname_mems; apply load_cell; [solve_cell | lia]|]
    | |- store_ok _ _ _ _ = true /\ _ =>
        split; [unname_mems; solve_store|]
    end);
  rewrite ?addi_W.

(* [comment removed for export] *)
Ltac same_ex_lia :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk;
  do 32 (destruct k as [|k];
         [first [ reflexivity
                | exfalso; apply Hk; cbv; repeat (first [left; reflexivity | right]); fail
                | cbn [rget lget]; f_equal; lia ]|]);
  rewrite !rget_beyond by (cbn [length]; lia); reflexivity.

(* [comment removed for export] *)
Lemma notin_b : forall (k : nat) ks, existsb (Nat.eqb k) ks = false -> ~ In k ks.
Proof.
  intros k ks H Hin. assert (E : existsb (Nat.eqb k) ks = true); [|congruence].
  apply existsb_exists. exists k. split; [exact Hin | apply Nat.eqb_refl].
Qed.

Ltac se_one H k :=
  try (let E := fresh "E" in
       lazymatch type of H with
       | same_except ?ks _ _ => pose proof (H k (notin_b k ks (@eq_refl bool false))) as E
       end;
       cbn [rget lget] in E;
       match type of E with ?x = _ => subst x end).
Ltac se_subst H :=
  se_one H 1%nat; se_one H 2%nat; se_one H 3%nat; se_one H 4%nat; se_one H 5%nat; se_one H 6%nat; se_one H 7%nat;
  se_one H 8%nat; se_one H 9%nat; se_one H 10%nat; se_one H 11%nat; se_one H 12%nat; se_one H 13%nat;
  se_one H 14%nat; se_one H 15%nat; se_one H 16%nat; se_one H 17%nat; se_one H 18%nat; se_one H 19%nat;
  se_one H 20%nat; se_one H 21%nat; se_one H 22%nat; se_one H 23%nat; se_one H 24%nat; se_one H 25%nat;
  se_one H 26%nat; se_one H 27%nat; se_one H 28%nat; se_one H 29%nat; se_one H 30%nat; se_one H 31%nat.
