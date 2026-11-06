(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI62.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0x YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI09 YI08 YI0t YI0m YI0n YI60.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
