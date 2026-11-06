(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply; image row img-errnoseg-A).
   rule 24: no function proved (kind: measurement; an image row, a closed computation at reply's image A,
   fuzz_reply.asan, pin 42c58610e125).

   The cf layer states this row as a Definition over its own Section context; reply has not taken that layer file
   yet.  So the Lemma below states the layer Definition's body VERBATIM at reply's instance (the image class
   ImgBase.AImg at AImg_reply, A/AGif2reply.v:23), for a B with the image's symbol facts (the layer's Section b has
   `Hypothesis TS : im_syms B`), and a consumer closes the layer's row with `exact` once the layer is on reply.  No
   Definition of the layer is copied here.

   The cf text, YGcfInstErrno.v:83-84 (lane F1, a working branch cadcb4a0f83; the same text on a working branch
   89caf2ed683; set in this form by bdbe5c2a7e5, where it was :86-87, the line a Theorem Labs lane's CF-UNIT-HYPS.md:35 (sha256 77b3f94c95d2; internal record)
   cites), in `Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
   Context {IM : AImg} {AG : AGImg} {DI : DImg}. ... Section b. Variable B : asyms. Hypothesis TS : im_syms B.`:
     Definition errno_seg_t : Prop :=
     forall a, as_errno B <= a < as_errno B + 4 -> seg_rom im_segs (Z_to_bv 64 a) <> None.
   cgif's discharge: YGcfInstErrnocgif.v:38-42 errno_seg_cgif (cadcb4a0f83), by YB13.tfib_rw_rom.

   Proof at image A: ts_errno (A/AF0m.v:875) gives as_errno B = TFIB_ERRNO = 0x5d93cc (A/AF0m.v:22), so errno's four
   bytes [0x5d93cc, 0x5d93d0) lie in the image's read-write window [0x9d000, 0x5fb000), where every byte is a segment
   byte (AB13.tfib_rw_rom, A/AB13.v:110: segments 2 = [0x9d000, 0x9f000) and 3 = [0x9f000, 0x5fb000), by scanN over
   the image's own segment bytes; errno is in segment 3); im_segs of AImg_reply is tfibsegs (A/AGif2reply.v:24). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AB13.
Open Scope Z_scope.

(* errno_seg_t at image A (the cf layer's YGcfInstErrno.errno_seg_t, unfolded): errno's 4 bytes are segment bytes. *)
Lemma errno_seg_A : forall B, @im_syms AImg_reply B ->
  forall a, as_errno B <= a < as_errno B + 4 -> seg_rom (@im_segs AImg_reply) (Z_to_bv 64 a) <> None.
Proof.
intros B TS a Ha. change (TfibSyms B) in TS. rewrite (ts_errno B TS) in Ha.
change (@im_segs AImg_reply) with tfibsegs.
apply AB13.tfib_rw_rom. unfold TFIB_ERRNO in Ha. lia.
Qed.
