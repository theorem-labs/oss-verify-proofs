(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AImgA.v; 15 of its 23 lines of code are new or changed and 4 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGif2cgif.v (cold/c-asan-realloc-c5 ced28ed2383, file sha256 f5aa8e82f671) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/AGif2cgif.v, with its module paths and module names changed; 1 of its 23 lines of code is new or changed and 1 line of the source is left out. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGif2cgif.v (a working branch 95e6f1d72b6, file sha256 f5aa8e82f671; written for cgif_file_fuzzer.asan-ubsan 1c29845fe605) onto libreac/fuzz_decode's asan image (pin 5973b76807d8, unstripped twin 4cb0a852e826); module paths changed, names TfibSyms -> GrantSyms; taken by path: no numeral of it names an image address, none changed. *)
(* The cgif_file instance of the image class ImgBase.AImg: cgif's segments (tfibsegs), data cells (TFIB_TP / TFIB_TSD /
   TFIB_OOM / TFIB_ERRNO), image window (AF0x.img_cover), symbol facts (AF0m.PcapSyms) and constant cells
   (AF0m.Tfib_const).  The image-free interfaces (AGif2, ...) take the class as [Context {IM : AImg}]; a cgif_file
   consumer does [Require Import AGif2cgif] and instance search fills IM with AImg_cgif, so [im_segs] unfolds to
   tfibsegs by delta.  This is the ONE file of the cgif instance: a field added to AImg gets its cgif value here.
   Consumers relocated to another binary declare their own instance in place of this file. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import ImgBase.
Open Scope Z_scope.

#[export] Instance AImg_cgif : AImg := {|
  im_segs := tfibsegs;
  im_tp := TFIB_TP; im_tsd := TFIB_TSD; im_oom := TFIB_OOM; im_errno := TFIB_ERRNO;
  im_img_cover := img_cover;
  im_syms := PcapSyms;
  im_const := Tfib_const;
  im_const_eq := fun B ly TS => ts_const B TS ly
|}.
(* Also a canonical structure: a tactic that elaborates its term without instance search ([apply (AGif2.sv_cell_lit
   B W ...)], [destruct (AGif2.sv_junk_values B W ...)]) must solve [im_segs ?IM = tfibsegs] by unification alone;
   the canonical projection (im_segs, tfibsegs) gives ?IM := AImg_cgif there, so such call sites stay unchanged. *)
Canonical Structure AImg_cgif.
