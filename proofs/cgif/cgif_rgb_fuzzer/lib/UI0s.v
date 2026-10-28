(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m UO3n
YI00 YI02 YI01 YI07 YI03 YI04 UI26.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma seps_from_of_all : forall b l, (forall c, In c l -> zz_disj b c) -> seps_from b l.
Proof.
intros b l. induction l as [|c l IH]; intros H; cbn; [exact I|].
split; [apply (H c); left; reflexivity | apply IH; intros c' Hc'; apply H; right; exact Hc'].
Qed.
Lemma nz_swap2 : forall (a b : Z * Z) (R bl : list (Z * Z)),
Permutation bl (nz [a; b] ++ R) -> Permutation bl (nz [b; a] ++ R).
Proof.
intros [pa na] [pb nb] R bl H. unfold nz in *. cbn [List.filter fst] in *.
destruct (pa =? 0), (pb =? 0); cbn [negb] in *; try exact H.
eapply Permutation_trans; [exact H|]. apply perm_swap.
Qed.
Lemma nz_swap2_in : forall (a b : Z * Z) (P : Z * Z -> Prop),
(forall x, In x (nz [a; b]) -> P x) -> forall x, In x (nz [b; a]) -> P x.
Proof.
intros a b P H x Hx. apply H. apply (proj2 (In_nz _ _)). apply (proj1 (In_nz _ _)) in Hx as [Hin Hnz].
split; [|exact Hnz]. cbv [In] in Hin |- *. tauto.
Qed.
Lemma sub_cond_of_wtok : forall STK sp0 FP bl0 blc p n,
wtok' STK sp0 FP bl0 (p, n) -> In (p, n) blc -> p + n <= alloc_ceiling -> alloc_ceiling + STK <= sp0 ->
forall a, inFP [(p, p + n)] a ->
(inFP FP a /\ a < alloc_ceiling) \/ (exists b m, In (b, m) blc /\ ~ In (b, m) bl0 /\ b <= a < b + m).
Proof.
intros STK sp0 FP bl0 blc p n HW Hin Hpn Hsp a Ha.
apply inFP_cons in Ha as [Ha | Ha]; [| exfalso; exact (inFP_nil _ Ha)].
destruct (HW blc (a - p) Hin ltac:(cbn [snd]; lia)) as [Hs | [[Hf _] | (b & m & Hb & Hnb & Hr)]]; cbn [fst] in *.
- exfalso. lia.
- left. split; [|lia]. replace a with (p + (a - p)) by lia. exact Hf.
- right. exists b, m. split; [exact Hb|]. split; [exact Hnb|]. lia.
Qed.
Lemma perm_cbb : forall (r2 r1 : Z * Z) (R : list (Z * Z)),
Permutation ([r2; r1] ++ R) (r1 :: r2 :: R).
Proof. intros. cbn [app]. apply perm_swap. Qed.
Definition hideP (P : Prop) : Prop := P.
Lemma hideP_i : forall P : Prop, P -> hideP P. Proof. intros P H; exact H. Qed.
Lemma hideP_e : forall P : Prop, hideP P -> P. Proof. intros P H; exact H. Qed.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
