(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AImgA.v, with its module paths changed; 15 of its 23 lines of code are new or changed and 4 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGif2cgif.v (commit 30a1993588f, c5 + memnorm; file sha256 f5aa8e82f671) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/AGif2reply.v (commit d2dafa219c1, file sha256 e3ebc35d0c7e) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 0 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* The cgif_file instance of the image class ImgBase.AImg: cgif's segments (tfibsegs), data cells (TFIB_TP / TFIB_TSD /
   TFIB_OOM / TFIB_ERRNO), image window (YF0x.img_cover), symbol facts (YF0m.TfibSyms) and constant cells
   (YF0m.Tfib_const).  The image-free interfaces (AGif2, ...) take the class as [Context {IM : AImg}]; a cgif_file
   consumer does [Require Import AGif2cgif] and instance search fills IM with AImg_cgif, so [im_segs] unfolds to
   tfibsegs by delta.  This is the ONE file of the cgif instance: a field added to AImg gets its cgif value here.
   Consumers relocated to another binary declare their own instance in place of this file. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
Open Scope Z_scope.

#[export] Instance AImg_reply : AImg := {|
  im_segs := tfibsegs;
  im_tp := TFIB_TP; im_tsd := TFIB_TSD; im_oom := TFIB_OOM; im_errno := TFIB_ERRNO;
  im_img_cover := img_cover;
  im_syms := TfibSyms;
  im_const := Tfib_const;
  im_const_eq := fun B ly TS => ts_const B TS ly
|}.
(* Also a canonical structure: a tactic that elaborates its term without instance search ([apply (AGif2.sv_cell_lit
   B W ...)], [destruct (AGif2.sv_junk_values B W ...)]) must solve [im_segs ?IM = tfibsegs] by unification alone;
   the canonical projection (im_segs, tfibsegs) gives ?IM := AImg_cgif there, so such call sites stay unchanged. *)
Canonical Structure AImg_reply.
