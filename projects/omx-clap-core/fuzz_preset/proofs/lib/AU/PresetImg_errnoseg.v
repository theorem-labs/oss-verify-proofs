(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_errnoseg.v (commit 4d286b2e618d, file sha256 5eebe6efeb37) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 8 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, row img-errnoseg-B of a Theorem Labs lane's internal file REPLY-IMG-ROWS.md, for a Theorem Labs lane's cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: measurement; image rows, closed computations at reply's image B,
   fuzz_reply.asan-ubsan pin 10ffb5f9202a).

   The cf layer states this row as a Definition over its own Section context; reply has not taken that layer file yet.
   So the Lemma below states the layer Definition's body VERBATIM at reply's instance (the image class ImgBase.AImg at
   image B's AImg_cgif, B/AGif2cgif.v:24), and a consumer closes the layer's row with `exact` once the layer is on
   reply.  No Definition of the layer is copied here.
   - errno_seg_t, the cf layer's YGcfInstErrno.v:83-84 (lane F1, commit cadcb4a0f830; the same text at :86-87 of
     commit bdbe5c2a7e5, the line the internal file CF-UNIT-HYPS.md row 35 cites), in Section b (Variable B : asyms; Hypothesis TS :
     im_syms B, :75-76):
       Definition errno_seg_t : Prop :=
       forall a, as_errno B <= a < as_errno B + 4 -> seg_rom im_segs (Z_to_bv 64 a) <> None.
     cgif's discharge: YGcfInstErrnocgif.v:38-42 errno_seg_cgif (commit cadcb4a0f830), through YB13.tfib_rw_rom.
     At image B: errno is TFIB_ERRNO = 0x5d994c (B/YF0m.v:21; ts_errno, B/YF0m.v:863), so its 4 bytes
     [0x5d994c, 0x5d9950) lie in the read-write window [0xa2000, 0x601000), where every byte is a segment byte of the
     image (B/YB13.v:109 tfib_rw_rom: the proof image's segments 2 = [0xa2000, 0xa4000) and 3 = [0xa4000, 0x601000)). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YB13.
Open Scope Z_scope.

(* errno_seg_t at image B (YGcfInstErrno.v:83-84): errno's 4 bytes [0x5d994c, 0x5d9950) (TFIB_ERRNO, B/YF0m.v:21) are
   segment bytes of AImg_reply's im_segs = tfibsegs, by B/YB13.tfib_rw_rom over [0xa2000, 0x601000). *)
Lemma errno_seg_B : forall B, @im_syms AImg_cgif B ->
  forall a, as_errno B <= a < as_errno B + 4 -> seg_rom (@im_segs AImg_cgif) (Z_to_bv 64 a) <> None.
Proof.
intros B TS a Ha. change (TfibSyms B) in TS. rewrite (ts_errno B TS) in Ha.
change (@im_segs AImg_cgif) with tfibsegs. apply YB13.tfib_rw_rom. unfold TFIB_ERRNO in Ha. lia.
Qed.
