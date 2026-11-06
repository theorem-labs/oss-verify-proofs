(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_sbconst.v (commit ce1a656b52b7, file sha256 ecde5af6f382) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs: reply image row img-sbconst-B of the cf layer at plugin-hostd/fuzz_reply.
   rule 24: no function proved (kind: closed image fact over the constant-cell table of reply's image B,
   fuzz_reply.asan-ubsan, pin 10ffb5f9202a).

   SB_CONST, proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainQ.v:45 @ 1c81ef042c9 (used as Hypothesis SBC, :154), over the
   image class's field im_const (Context {IM : AImg}).  Reply does not carry YGcfInstDrainQ.v, so the Lemma states the
   body of SB_CONST verbatim at reply's instance IM := AImg_cgif (B/AGif2cgif.v:24, im_const := YF0m.Tfib_const).
   Proof: the space-base cell c8 (AInst o_space) (ASp 0) is found in Tfib_const by cell_lookup, computed by vm_compute
   (cgif's pattern: YFhl.sb_cell, B/YFhl.v:122-126). *)
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
Open Scope Z_scope.

(* SB_CONST at image B: YGcfInstDrainQ.v:45 @ 1c81ef042c9, at IM := AImg_cgif. *)
Lemma SB_CONST_B : forall ly, In (ACell (AInst o_space) 8 (AV (ASp 0))) (@im_const AImg_cgif ly).
Proof.
intros ly. change (In (ACell (AInst o_space) 8 (AV (ASp 0))) (Tfib_const ly)).
apply (cell_lookup_In _ (AInst o_space)). vm_compute. reflexivity.
Qed.
