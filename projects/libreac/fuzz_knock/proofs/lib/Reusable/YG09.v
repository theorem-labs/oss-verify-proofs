(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG09.v, with its module paths changed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition nsec_l (l : list chunk) : Z := fold_right (fun k acc => match ck_beg k with PSec _ _ => 1 + acc | _ => acc end) 0 l.
Lemma nsec_le_arr : forall U pp cc bb s, WfP U pp cc bb s -> nsec_l (st_chunks s) <= Z.of_nat (length (st_sec_arr s)).
Proof.
intros U pp cc bb s W. pose proof (wf_secondary _ _ _ _ _ W) as X. destruct X as [_ Sac _ _ _].
pose proof (wf_chunks_nodup _ _ _ _ _ W) as ND. pose proof (wf_chunks _ _ _ _ _ W) as CK.
set (idx := fun l : list chunk => flat_map (fun k => match ck_beg k with PSec r _ => [r] | _ => [] end) l).
assert (L : forall l, nsec_l l = Z.of_nat (length (idx l))).
{ induction l as [|k t IH]; [reflexivity|]. unfold nsec_l, idx in *. cbn [fold_right flat_map]. rewrite length_app, Nat2Z.inj_add, <- IH.
destruct (ck_beg k); cbn [length]; lia. }
rewrite L. apply Nat2Z.inj_le. apply NoDup_incl_length.
- assert (G : forall l, Forall (chunk_ok s) l -> NoDup (map ck_beg l) -> NoDup (idx l) /\ (forall r, In r (idx l) -> In (PSec r kPage) (map ck_beg l))).
{ induction l as [|k t IH]; intros Hc Hn; [split; [constructor | intros r []]|].
inversion Hc as [|k' t' Hk Ht]; subst. cbn [map] in Hn. inversion Hn as [|b' m' Hni Hnt]; subst. destruct (IH Ht Hnt) as [I1 I2].
unfold idx in *. cbn [flat_map map]. destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; cbn [app].
- split; [exact I1 | intros r Hr; right; exact (I2 r Hr)].
- split; [exact I1 | intros r Hr; right; exact (I2 r Hr)].
- destruct Hk as [_ Hk]. rewrite Eb in Hk. destruct Hk as (_ & -> & _). split.
+ constructor; [|exact I1]. intros Hin. apply Hni. exact (I2 r Hin).
+ intros r' [<-|Hr]; [left; reflexivity | right; exact (I2 r' Hr)].
- split; [exact I1 | intros r Hr; right; exact (I2 r Hr)]. }
exact (proj1 (G _ CK ND)).
- intros r Hr. apply Sac. unfold idx in Hr. apply in_flat_map in Hr as (k & Hk & Hr).
destruct (ck_beg k) as [|off|r' o|cid pos] eqn:Eb; try destruct Hr as [<-|[]]; try destruct Hr.
pose proof (proj1 (Forall_forall _ _) CK k Hk) as [_ Hok]. rewrite Eb in Hok. destruct Hok as (_ & -> & _). exists k. auto.
Qed.
