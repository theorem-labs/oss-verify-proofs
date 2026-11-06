(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_oomowned.v (commit 4d286b2e618d, file sha256 1e47ce18f6fb) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 5 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs: reply image row img-oomowned-B of the cf layer at plugin-hostd/fuzz_reply.
   rule 24: no function proved (kind: closed image fact over the symbol table of reply's image B, fuzz_reply.asan-ubsan,
   pin 10ffb5f9202a).

   oom_owned_img : oom_areas_t, proofs/cgif/cgif_file_fuzzer/lib/YGcfInstMiss.v:291-296 (Definition) / :300
   (Hypothesis) @ 692f71ce28c.  The layer states oom_areas_t over its Section's Variable B, under the hypothesis
   TS : im_syms B (YGcfInstMiss.v:240 @ 692f71ce28c).  Reply does not carry YGcfInstMiss.v, so the Lemma states the body
   of oom_areas_t VERBATIM at a B with image B's symbol facts (im_syms of AImg_cgif, B/AGif2cgif.v:24, which is
   YF0m.TfibSyms).
   At image B (B/YF0m.v:16-19) the OOM byte is TFIB_OOM = 0x12d960: above the instance object [0xa8098, 0xa8ec8) and the
   internal allocator [0xac900, 0x128870), below the flag [0x1360c8, 0x1360ca), the store [0x17d5c8, 0x178528) and the
   depot [0x188518, 0x588538).  cgif's discharge of the same five facts: YFi5.Z_inst / Z_depot / Z_store / Z_ial /
   Z_flag. *)
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

(* oom_owned_img at image B: the body of oom_areas_t (YGcfInstMiss.v:292-296 @ 692f71ce28c), verbatim. *)
Lemma oom_owned_img_B : forall B, @im_syms AImg_cgif B ->
  ~ (as_inst B <= as_oom_byte B < as_inst B + 3632) /\
  ~ (as_depot B <= as_oom_byte B < as_depot B + (4 * 2 ^ 20 + 32)) /\
  ~ (as_store B <= as_oom_byte B < as_store B + 32) /\
  ~ (as_ialloc_lo B <= as_oom_byte B < as_ialloc_hi B) /\
  ~ (as_ialloc_flag B <= as_oom_byte B < as_ialloc_flag B + 2).
Proof.
intros B TS. change (TfibSyms B) in TS.
rewrite (ts_oom B TS), (ts_inst B TS), (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS), (ts_ial_hi B TS),
  (ts_ial_flag B TS).
replace (2 ^ 20) with 1048576 by reflexivity.
unfold TFIB_OOM, TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
Qed.
