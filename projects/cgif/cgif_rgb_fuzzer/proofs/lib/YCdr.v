(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCe9 YCfu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Lemma mres_kept : forall lyc Sc W memT W2 mem2 ly2 S2 slo shi res n,
(res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ acall_kept trbsegs B lyc Sc W memT W2 mem2 slo shi (fun _ => False))
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept trbsegs B lyc Sc W memT W2 mem2 slo shi (fun a => res <= a < res + req_size n)) ->
acall_kept trbsegs B lyc Sc W memT W2 mem2 slo shi (fun a => res <> 0 /\ res <= a < res + req_size n) /\
(forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2)) /\
(res <> 0 -> In (res, n) (ablocks B ly2 S2)).
Proof.
intros lyc Sc W memT W2 mem2 ly2 S2 slo shi res n [(Hz & Ebl & HK) | (Hnz & Ebl & HK)].
- split; [eapply acall_kept_mono_E; [exact HK | intros a []]|]. split; [intros b Hb; rewrite Ebl; exact Hb | intros H; lia].
- split; [eapply acall_kept_mono_E; [exact HK | intros a Ha; split; [lia | exact Ha]]|].
split; [intros b Hb; rewrite Ebl; apply in_app_iff; left; exact Hb | intros _; rewrite Ebl; apply in_app_iff; right; left; reflexivity].
Qed.
Lemma mres_range : forall ly2 S2 W2 mem2 md2 lyc Sc (res n : Z) (P Q : Prop),
AR trbsegs B ly2 S2 W2 mem2 md2 ->
(res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ P) \/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\ Q) ->
res = 0 \/ (4096 <= res /\ ((res + req_size n <= 65536 \/ 6291456 <= res) /\ (res + req_size n <= 2147446784 \/ 17594333495296 <= res))
/\ res + req_size n <= alloc_ceiling /\ res mod 16 = 0 /\ In (res, n) (ablocks B ly2 S2)).
Proof.
intros ly2 S2 W2 mem2 md2 lyc Sc res n P Q HAR [(-> & _ & _) | (Hr & Ebl & _)]; [left; reflexivity | right].
assert (Hin : In (res, n) (ablocks B ly2 S2)) by (rewrite Ebl; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res n HAR Hin) as (H16 & _ & Hc & [Hh Happ] & _).
pose proof (blk_off_img _ _ _ _ _ _ res n HAR Hin) as Hh_img.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, Hh_img; lia|]. split; [exact Hc|]. split; [exact H16 | exact Hin].
Qed.
Lemma sep_tmp_entry : forall ly3 S3 W3 m3 md3 (entry : list (Z * Z)) pt n b m,
AR trbsegs B ly3 S3 W3 m3 md3 -> Permutation (ablocks B ly3 S3) (entry ++ [(pt, n)]) -> In (b, m) entry ->
b + req_size m <= pt \/ pt + req_size n <= b.
Proof.
intros ly3 S3 W3 m3 md3 entry pt n b m HAR HP Hin.
apply in_split in Hin as (l1 & l2 & El). rewrite El in HP.
assert (HP2 : Permutation (ablocks B ly3 S3) ((pt, n) :: (b, m) :: l1 ++ l2)).
{ eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip.
apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm trbsegs B LAWS _ _ _ _ _ _ _ _ HAR HP2) as Hs. unfold zdisjoint, block_rng in Hs. cbn [fst snd] in Hs. lia.
Qed.
End d.
End c.
