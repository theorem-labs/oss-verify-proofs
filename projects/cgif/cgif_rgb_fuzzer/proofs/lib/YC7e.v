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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section L.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Definition rga_blocks_kept (ly : alayout) (S : astate) (H : word -> bool) (m m' : word -> option byte) : Prop :=
forall b n, In (b, n) (ablocks B ly S) -> rg_blk_kept H H m m' b (req_size n).

Lemma rga_blocks_kept_trans : forall ly S H m1 m2 m3,
rga_blocks_kept ly S H m1 m2 -> rga_blocks_kept ly S H m2 m3 -> rga_blocks_kept ly S H m1 m3.
Proof. intros ly S H m1 m2 m3 K1 K2 b n Hin. eapply rg_blk_kept_trans; [apply K1 | apply K2]; exact Hin. Qed.
Lemma rga_blk_byte : forall ly S W m md b n a,
AR trasegs B ly S W m md -> In (b, n) (ablocks B ly S) -> b <= a < b + req_size n ->
0 <= a < 2 ^ 64 /\ a < alloc_ceiling /\ (a < kLowShadowBeg \/ kHighMemBeg <= a) /\ ~ aowned B ly S a.
Proof.
intros ly S W m md b n a HAR Hin Ha.
destruct (al_blocks _ _ LAWS ly S W m md b n HAR Hin) as (_ & H4096 & Hceil & [Hh1 Hh2] & Hpres & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
split; [zlia|]. split; [zlia|]. split; [zlia | exact (proj2 (Hpres a Ha))].
Qed.
Lemma rga_blocks_kept_run : forall E rs ly S W m md m' STK sp0 own,
AR trasegs B ly S W m md ->
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
awr_ok E rs STK sp0 [] (ablocks B ly S) (ablocks B ly S) ly own ->
alloc_ceiling <= sp0 - STK -> (forall c p, In (c, p) own -> In (c, p) (frames S)) ->
rga_blocks_kept ly S (w_H W) m m'.
Proof.
intros E rs ly S W m md m' STK sp0 own HAR HFr Hawr Hstk Hown b n Hin.
apply (rg_blk_kept_frame E rs). { exact HFr. }
intros a Ha. destruct (rga_blk_byte ly S W m md b n a HAR Hin Ha) as (Hr & Hc & Hz & Hno). split; [exact Hr|].
intros Hw. destruct (Hawr a Hw) as [Hs | [[Hf _] | [(b' & n' & Hi1 & Hi2 & _) | (c & p & Hcp & Hfr)]]].
- lia.
- exact (inFP_nil _ Hf).
- exact (Hi2 Hi1).
- pose proof (Hown c p Hcp) as Hcp'.
destruct (al_frames _ _ LAWS ly S W m md c p HAR Hcp') as (_ & _ & Hfb & Hfsh).
destruct Hfr as [Hfr | Hfr]; unfold in_zr in Hfr; cbn [fst snd] in Hfr.
+ pose proof (sep_block_frame trasegs B LAWS ly S W m md b n c p HAR Hin Hcp') as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
+ destruct (frames_bounds trasegs B LAWS ly S W m md c p HAR Hcp') as (Hf0 & Hfc & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg c) as Hnn.
pose proof (shadow_addr_bounds (frame_addr ly c p) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr ly c p + fs_frame_bytes c) ltac:(pose proof (fs_frame_bytes_nonneg c); zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr ly c p) (fs_frame_bytes c) (fs_frame_bytes_nonneg c)) as Hse.
zlia.
Qed.
Lemma rga_blocks_kept_off : forall ly S W m md m' (Wr : Z -> Prop),
AR trasegs B ly S W m md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview trasegs (w_H W) m' a = aview trasegs (w_H W) m a) ->
(forall a, Wr a -> alloc_ceiling <= a \/ (kLowShadowBeg <= a < kHighMemBeg) \/ aowned B ly S a) ->
rga_blocks_kept ly S (w_H W) m m'.
Proof.
intros ly S W m md m' Wr HAR Hfr HWr b n Hin i Hi.
destruct (rga_blk_byte ly S W m md b n (b + i) HAR Hin ltac:(lia)) as (Hr & Hc & Hz & Hno).
apply Hfr; [exact Hr|]. intros Hw. destruct (HWr _ Hw) as [H1 | [H1 | H1]]; [lia | lia | exact (Hno H1)].
Qed.
Lemma ajournal_fp_mono : forall STK sp0 FP FP' ly S W mem md own ly' S' W' mem' md' k,
(forall a, inFP FP a -> inFP FP' a) ->
ajournal trasegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
ajournal trasegs B STK sp0 FP' ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP FP' ly S W mem md own ly' S' W' mem' md' k Hsub
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split; [exact F1|].
split; [intros p n i H1 H2 Hi Hn; apply (F2 p n i H1 H2 Hi); intros Hx; exact (Hn (Hsub _ Hx))|].
split; [exact F3|].
split; [intros cid pos a Hin Hr Hn; apply (F4 cid pos a Hin Hr); intros Hx; exact (Hn (Hsub _ Hx))|].
split; [intros p n i H1 H2 Hi; apply Hsub; exact (Hgone p n i H1 H2 Hi)|].
split; [exact Hpres|]. split; [exact Hstatic | exact HQT].
Qed.
End L.
End d.
