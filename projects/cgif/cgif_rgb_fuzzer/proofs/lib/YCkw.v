(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YI0g.
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Lemma g_aftok_fresh : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k res n,
ajournal trbsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
~ In (res, n) (ablocks B lyc Sc) -> aftok FP (ablocks B ly S) (res, n).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k res n HJ Hc H0 i Hi. cbn [fst snd] in *.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
exact (Hgone res n i H0 Hc Hi).
Qed.
Lemma g_awr_fresh_any : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k res n blc i lyq ownq,
ajournal trbsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
~ In (res, n) (ablocks B lyc Sc) -> In (res, n) blc -> 0 <= i < req_size n ->
awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (res + i).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k res n blc i lyq ownq HJ Hc Hin Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, n) (ablocks B ly S)) as [H0 | H0].
- right. left. split; [exact (Hgone res n i H0 Hc Hi)|]. exists res, n. split; [exact Hin | lia].
- right. right. left. exists res, n. split; [exact Hin|]. split; [exact H0 | lia].
Qed.
Lemma g_realloc_fresh : forall (LAWS : AR_laws trbsegs B) ly2 S2 W2 mem2 md2 (old : list (Z * Z)) l1 l2 pa n_old res n,
AR trbsegs B ly2 S2 W2 mem2 md2 -> old = l1 ++ (pa, n_old) :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ++ [(res, n)] -> 0 < n -> n <> n_old ->
~ In (res, n) old.
Proof.
intros LAWS ly2 S2 W2 mem2 md2 old l1 l2 pa n_old res n HAR2 El El2 Hn Hne Hc. rewrite El in Hc.
pose proof (req_size_pos n ltac:(lia)) as Hrq.
apply in_app_iff in Hc as [Hc | [Hc | Hc]].
- apply in_split in Hc as (c1 & c2 & Ec).
assert (EE : ablocks B ly2 S2 = c1 ++ (res, n) :: (c2 ++ l2) ++ (res, n) :: []) by (rewrite El2, Ec, <- !app_assoc; cbn [app]; reflexivity).
pose proof (sep_blocks_pos trbsegs B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) c1 (c2 ++ l2) [] HAR2 EE) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
- injection Hc as _ Hc. exact (Hne (eq_sym Hc)).
- apply in_split in Hc as (c1 & c2 & Ec).
assert (EE : ablocks B ly2 S2 = (l1 ++ c1) ++ (res, n) :: c2 ++ (res, n) :: []) by (rewrite El2, Ec, <- !app_assoc; cbn [app]; reflexivity).
pose proof (sep_blocks_pos trbsegs B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) (l1 ++ c1) c2 [] HAR2 EE) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma g_realloc_perm : forall (old new rest : list (Z * Z)) l1 l2 pa n_old res n,
old = l1 ++ (pa, n_old) :: l2 -> new = l1 ++ l2 ++ [(res, n)] -> Permutation old ((pa, n_old) :: rest) -> Permutation new ((res, n) :: rest).
Proof.
intros old new rest l1 l2 pa n_old res n El El2 HP. rewrite El2. rewrite El in HP.
assert (HP2 : Permutation (l1 ++ l2) rest).
{ apply (Permutation_cons_inv (a := (pa, n_old))). eapply Permutation_trans; [apply Permutation_middle | exact HP]. }
rewrite app_assoc. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|]. apply perm_skip. exact HP2.
Qed.
End b.
