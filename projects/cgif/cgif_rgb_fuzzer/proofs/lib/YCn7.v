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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn6.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Lemma m_cht_arrays_kept : forall (H H' : word -> bool) (m m' : word -> option byte) f h u p x Ht,
cht_arrays trbsegs (mrestrict H m) f h u p x Ht ->
zlen (ht_used Ht) = ht_T Ht -> zlen (ht_keys Ht) = 3 * ht_T Ht -> zlen (ht_frequ Ht) = ht_T Ht ->
zlen (ht_colidx Ht) = ht_T Ht -> zlen (ht_pal Ht) = 3 * ht_T Ht ->
(forall b sz, In (b, sz) (cht_blocks f h u p x (ht_T Ht)) -> rg_blk_kept H H' m m' b sz) ->
cht_arrays trbsegs (mrestrict H' m') f h u p x Ht.
Proof.
intros H H' m m' f h u p x Ht (A1 & A2 & A3 & A4 & A5) L1 L2 L3 L4 L5 K.
assert (Kf := K f (4 * ht_T Ht) ltac:(left; reflexivity)).
assert (Kh := K h (3 * ht_T Ht) ltac:(right; left; reflexivity)).
assert (Ku := K u (ht_T Ht) ltac:(right; right; left; reflexivity)).
assert (Kp := K p (3 * ht_T Ht) ltac:(right; right; right; left; reflexivity)).
assert (Kx := K x (4 * ht_T Ht) ltac:(right; right; right; right; left; reflexivity)).
unfold cht_arrays. split; [|split; [|split; [|split]]].
- apply (arr32_frame trbsegs _ _ f _ A1). intros a Ha. apply (mbyte_of_aview trbsegs). replace a with (f + (a - f)) by lia. apply Kf. lia.
- apply (arr8_frame trbsegs _ _ h _ A2). intros a Ha. apply (mbyte_of_aview trbsegs). replace a with (h + (a - h)) by lia. apply Kh. lia.
- apply (arr8_frame trbsegs _ _ u _ A3). intros a Ha. apply (mbyte_of_aview trbsegs). replace a with (u + (a - u)) by lia. apply Ku. lia.
- apply (arr8_frame trbsegs _ _ p _ A4). intros a Ha. apply (mbyte_of_aview trbsegs). replace a with (p + (a - p)) by lia. apply Kp. lia.
- apply (arr32_frame trbsegs _ _ x _ A5). intros a Ha. apply (mbyte_of_aview trbsegs). replace a with (x + (a - x)) by lia. apply Kx. lia.
Qed.
Lemma m_blk_off_zs2 : forall ly S W m md b n r tb l fpos,
AR trbsegs B ly S W m md -> Permutation (ablocks B ly S) ((r, RGB_SIZE) :: (tb, 48) :: l) -> In (b, n) l -> In (7, fpos) (frames S) ->
forall a, b <= a < b + req_size n -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP (frame_addr ly 7 fpos) r a \/ tb <= a < tb + 48).
Proof.
intros ly S W m md b n r tb l fpos HAR HP Hl Hfin a Ha.
destruct (m_blk_off_zs B LAWS ly S W m md b n r ((tb, 48) :: l) fpos HAR HP ltac:(right; exact Hl) Hfin a Ha) as (H1 & H2).
split; [exact H1|]. intros [Hz | Hz]; [exact (H2 Hz)|].
assert (HP' : Permutation (ablocks B ly S) ((tb, 48) :: (r, RGB_SIZE) :: l)) by (eapply Permutation_trans; [exact HP | apply perm_swap]).
pose proof (m_blk_off_blk B LAWS ly S W m md b n tb 48 _ HAR HP' ltac:(right; exact Hl) a Ha) as H3.
change (req_size 48) with 48 in H3. exact (H3 Hz).
Qed.
End d.
End c.
