(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String ZArith List Lia Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Fmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition args_small (B : Z) (args : list farg) : Prop :=
  Forall (fun a => match a with AStr s => zlength s <= B | AInt _ => True end) args.
Definition items_small (B : Z) (items : list fitem) : Prop :=
  Forall (fun it => match it with FLit l => zlength l <= B | FBad s => zlength s <= B | FConv _ => True end) items.

Lemma udigits_aux_length fuel base n acc : (length (udigits_aux fuel base n acc) <= fuel + length acc)%nat.
Proof.
  revert n acc. induction fuel as [|fuel IH]; intros n acc; cbn; [lia|].
  destruct (n <=? 0); [cbn; lia|]. etransitivity; [apply IH|]. cbn. lia.
Qed.

Lemma udigits_small base n : zlength (udigits base n) <= 64.
Proof. unfold udigits, zlength. pose proof (udigits_aux_length 64 base n []) as H. cbn [length] in H. rewrite Nat.add_0_r in H. lia. Qed.

Lemma zeros_length n : 0 <= n -> zlength (zeros n) = n.
Proof. intros Hn. unfold zeros, zrepeat, zlength. rewrite repeat_length. lia. Qed.

Lemma int_pieces_small neg ds : zlength ds <= 64 -> Forall (fun p => zlength p <= 64) (int_pieces neg ds).
Proof.
  intros Hd. unfold int_pieces. constructor; [destruct neg; unfold zlength; cbn; lia|].
  destruct ds; [constructor; [unfold zlength; cbn; lia| constructor; [unfold zlength; cbn; lia| constructor]]| constructor; [exact Hd| constructor]].
Qed.

Lemma conv_pieces_small B c a :
  64 <= B -> match a with AStr s => zlength s <= B | AInt _ => True end -> Forall (fun p => zlength p <= B) (conv_pieces c a).
Proof.
  intros HB Ha. unfold conv_pieces.
  assert (IP : forall neg ds, zlength ds <= 64 -> Forall (fun p => zlength p <= B) (int_pieces neg ds)).
  { intros neg ds Hd. eapply Forall_impl; [| apply (int_pieces_small neg ds Hd)]. cbn. intros; lia. }
  destruct c, a; try (apply IP; apply udigits_small); try (constructor; [unfold zlength; cbn; lia| constructor; [cbn in Ha; exact Ha || (unfold zlength; cbn; lia)| constructor]]).
  - (* [comment removed for export] *) cbv zeta.
    constructor; [unfold zlength; cbn; lia|]. apply Forall_app. split.
    + destruct (_ <? 8) eqn:E; [| constructor]. constructor; [| constructor]. apply Z.ltb_lt in E.
      pose proof (udigits_small 16 (u32 v)) as Hd. assert (Hn : 0 <= zlength (udigits 16 (u32 v))) by (unfold zlength; lia). unfold hex_udigits in *.
      rewrite zeros_length; destruct (u32 v =? 0); lia.
    + unfold hex_udigits. destruct (udigits 16 (u32 v)) eqn:E; [constructor; [unfold zlength; cbn; lia| constructor; [unfold zlength; cbn; lia| constructor]]|].
      constructor; [| constructor]. rewrite <- E. pose proof (udigits_small 16 (u32 v)). lia.
Qed.

Theorem fmt_pieces_small B items : forall args,
  64 <= B -> items_small B items -> args_small B args -> Forall (fun p => zlength p <= B) (fmt_pieces items args).
Proof.
  induction items as [|it items IH]; intros args HB HI HA; cbn; [constructor|].
  apply Forall_cons_iff in HI as [Hit HI]. destruct it as [l|c|s0].
  - constructor; [exact Hit| apply IH; assumption].
  - constructor; [unfold zlength; cbn; lia|]. apply Forall_app. split.
    + apply conv_pieces_small; [exact HB|]. destruct args as [|a args']; cbn; [exact I|]. apply Forall_cons_iff in HA as [Ha _]. exact Ha.
    + apply IH; [exact HB| exact HI|]. destruct args as [|a args']; cbn; [constructor|]. apply Forall_cons_iff in HA as [_ HA]. exact HA.
  - constructor; [exact Hit| constructor].
Qed.

(* [comment removed for export] *)
Theorem pieces_small f args B :
  64 <= B -> items_small B (fmt f) -> args_small B args -> Forall (fun p => zlength p <= B) (pieces f args).
Proof. intros HB HI HA. unfold pieces. apply fmt_pieces_small; assumption. Qed.

(* [comment removed for export] *)
Ltac items_small_tac :=
  lazymatch goal with |- items_small ?B (fmt ?f) =>
    let x := eval vm_compute in (fmt f) in change (fmt f) with x;
    unfold items_small; repeat (apply Forall_cons; [first [exact I | (vm_compute; congruence)] |]); apply Forall_nil
  end.

(* [comment removed for export] *)
Lemma args_small_cons_str B s args : zlength s <= B -> args_small B args -> args_small B (AStr s :: args).
Proof. intros; constructor; assumption. Qed.
Lemma args_small_cons_int B v args : args_small B args -> args_small B (AInt v :: args).
Proof. intros; constructor; [exact I| assumption]. Qed.
Lemma args_small_nil B : args_small B [].
Proof. constructor. Qed.
Ltac args_small_tac := repeat first [apply args_small_nil | apply args_small_cons_int | (apply args_small_cons_str; [first [assumption| (vm_compute; congruence)| idtac]|])].
