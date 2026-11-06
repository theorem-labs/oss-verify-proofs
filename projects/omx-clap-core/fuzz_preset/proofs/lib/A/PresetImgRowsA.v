(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImgRowsA.v (commit eb934de95d13, blob d6d846006d11) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 8 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); preset's ts_junk bounds the junk region by the NAME YImgTop.IMG_TOP, where reply's text had the literal, so the bound is unfolded before lia. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgA AGImgSA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGis AGjm.
Open Scope Z_scope.

Lemma exh_off_A : @cf_exh_off CfImg_A = 68.
Proof. reflexivity. Qed.

Lemma img_sapart_A : forall B, @im_syms AImg_A B -> forall a,
  ((as_inst B + 680 <= a < as_inst B + 684) \/ (as_inst B + 120 <= a < as_inst B + 129) \/
   (as_inst B + 144 <= a < as_inst B + 160) \/ (as_inst B + 704 <= a < as_inst B + 720)) ->
  ~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\
  ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros B TS a Ha. change (TfibSyms B) in TS.
rewrite (ts_inst B TS) in Ha.
rewrite (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
replace (2 ^ 20) with 1048576 by reflexivity.
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
Qed.

Lemma errb_obj_owned_A : forall B, @im_syms AImg_A B ->
  forall a, @cf_errbuf_obj CfImg_A <= a < @cf_errbuf_obj CfImg_A + 56 -> Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha. change (TfibSyms B) in TS. rewrite (ts_owned B TS).
unfold CfImg_A in Ha. cbn [cf_errbuf_obj] in Ha.
apply Exists_exists. exists (0xaa710, 0x5cd510 - 0xaa710). split.
- apply (nth_error_In Tfib_owned_static 3). reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma img_junk_A : forall B ly r0, @im_syms AImg_A B -> layout_ok ly -> In r0 (as_junk B ly) ->
  forall j, 0 <= j < snd r0 ->
  exists sg, In sg (@im_segs AImg_A) /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
intros B ly r0 TS _ Hr j Hj. change (TfibSyms B) in TS.
destruct (ts_junk B TS ly r0 Hr) as (z & Ez & Hlo & Hhi). unfold YImgTop.IMG_TOP in Hhi. rewrite Ez. cbn [aeval].
destruct (Z.lt_ge_cases (z + j) 0xa3000) as [Hl | Hg].
- exists Asan.Asan_segment_002. split; [change (In Asan.Asan_segment_002 tfibsegs); do 2 right; left; reflexivity|].
  change (Z.of_N (seg_base Asan.Asan_segment_002)) with 0xa1000. change (Z.of_N (seg_size Asan.Asan_segment_002)) with 0x2000. lia.
- exists Asan.Asan_segment_003. split; [change (In Asan.Asan_segment_003 tfibsegs); do 3 right; left; reflexivity|].
  change (Z.of_N (seg_base Asan.Asan_segment_003)) with 0xa3000. change (Z.of_N (seg_size Asan.Asan_segment_003)) with 0x55d000. lia.
Qed.

Lemma errb_sep_A : forall B, @im_syms AImg_A B -> forall ly a, layout_ok ly -> @im_img_cover AImg_A ly -> ly_tsd ly = as_tsd B ->
  @cf_errbuf_obj CfImg_A <= a < @cf_errbuf_obj CfImg_A + 56 ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\
  ~ ims_dzone ly a /\ ~ ag_dzone ly a.
Proof.
intros B TS ly a LY IC _ Ha. change (TfibSyms B) in TS. change (img_cover ly) in IC.
unfold CfImg_A in Ha. cbn [cf_errbuf_obj] in Ha.
rewrite (ts_inst B TS), (ts_oom B TS), (ts_errno B TS).
change (ims_dzone ly a) with (AGjm.DZONE ly a). change (ag_dzone ly a) with (AGis.DZONE ly a).
pose proof (lo_disj ly LY) as D. unfold static_extents, owned_extents in D. cbn [pairwise app] in D.
destruct D as (_ & _ & _ & _ & DNB & DSB & _). rewrite Forall_forall in DNB, DSB.
specialize (DNB (ly_img ly) ltac:(cbn; intuition)). specialize (DSB (ly_img ly) ltac:(cbn; intuition)).
unfold zdisjoint, AGjm.DZONE, AGis.DZONE, img_cover, TFIB_IMG_LO, TFIB_IMG_END, TFIB_INST, TFIB_OOM, TFIB_ERRNO in *.
cbn [fst snd] in *. repeat split; lia.
Qed.

End rows.
