(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Mem Image.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs ECH_AImg ECH_ARep ECH_ALib ECH_AStmt_C4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint img_cstr (A : Z) (fuel : nat) : list byte :=
  match fuel with
  | O => []
  | S f => match seg_rom asegs (wa A) with
           | Some b => if bv_unsigned b =? 0 then [] else b :: img_cstr (A + 1) f
           | None => []
           end
  end.
(* [comment removed for export] *)
Definition img_slack (A : Z) (len : nat) : list byte :=
  let e := A + Z.of_nat len + 1 in
  match image_bytes asegs e (Z.to_nat ((- e) mod 8)) with Some bs => bs | None => [] end.

Definition nonul (bs : list byte) : bool := forallb (fun b => negb (bv_unsigned b =? 0)) bs.
Lemma nonul_sound : forall bs, nonul bs = true -> ~ In (Z_to_bv 8 0) bs.
Proof.
  induction bs as [|b bs IH]; cbn; intros Hn; [tauto|]. apply andb_prop in Hn. destruct Hn as [H1 H2].
  intros [E|K]; [| exact (IH H2 K)]. subst b. vm_compute in H1. discriminate.
Qed.

Section HC.
  Context {HCEIL : HeapCeil}.
Lemma ROSTR_of_image : forall A str slack,
  ro_bytes_b asegs A (str ++ Z_to_bv 8 0 :: slack) = true -> nonul str = true ->
  ((- (A + Z.of_nat (length str) + 1)) mod 8 <=? Z.of_nat (length slack)) = true ->
  ((IMG_LO <=? A) && (A + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <=? IMG_HI)) = true ->
  ROSTR A str slack.
Proof.
  intros A str slack RB NN PD BD. apply andb_prop in BD. destruct BD as [B1 B2]. apply Z.leb_le in B1, B2, PD.
  split; [exact B1|]. split; [exact B2|]. intros m MI. split; [| split; [apply nonul_sound; exact NN| exact PD]].
  apply ro_bytes_at; [exact MI| unfold IMG_LO in B1; lia| |apply ro_bytes_b_sound; exact RB].
  rewrite length_app. cbn [length]. unfold IMG_HI in B2. lia.
Qed.
End HC.
