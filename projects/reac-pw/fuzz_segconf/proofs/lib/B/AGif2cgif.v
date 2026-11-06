(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AImgA.v; 15 of its 23 lines of code are new or changed and 4 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGif2cgif.v (cold/c-asan-realloc-c5 ced28ed2383, file sha256 f5aa8e82f671) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/AGif2cgif.v, with its module paths changed; 7 of its 27 lines of code are new or changed and 3 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGif2cgif.v (cold/c-frame-alloc-dgraw-frozen ced28ed2383, file sha256 f5aa8e82f671) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/AGif2cgif.v (donor image sha256 64b53ff86172), with its module paths changed, names TfibSyms -> SegBSyms. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AGif2cgif.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The cgif_file instance of the image class ImgBase.AImg: cgif's segments (tfibsegs), data cells (TFIB_TP / TFIB_TSD /
   TFIB_OOM / TFIB_ERRNO), image window (YF0x.img_cover), symbol facts (YF0m.SegBSyms) and constant cells
   (YF0m.Tfib_const).  The image-free interfaces (AGif2, ...) take the class as [Context {IM : AImg}]; a cgif_file
   consumer does [Require Import AGif2cgif] and instance search fills IM with AImg_cgif, so [im_segs] unfolds to
   tfibsegs by delta.  This is the ONE file of the cgif instance: a field added to AImg gets its cgif value here.
   Consumers relocated to another binary declare their own instance in place of this file. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import ImgBase.
Open Scope Z_scope.

#[export] Instance AImg_cgif : AImg := {|
  im_segs := tfibsegs;
  im_tp := TFIB_TP; im_tsd := TFIB_TSD; im_oom := TFIB_OOM; im_errno := TFIB_ERRNO;
  im_img_cover := img_cover;
  im_syms := SegBSyms;
  im_const := Tfib_const;
  im_const_eq := fun B ly TS => ts_const B TS ly
|}.
(* Also a canonical structure: a tactic that elaborates its term without instance search ([apply (AGif2.sv_cell_lit
   B W ...)], [destruct (AGif2.sv_junk_values B W ...)]) must solve [im_segs ?IM = tfibsegs] by unification alone;
   the canonical projection (im_segs, tfibsegs) gives ?IM := AImg_cgif there, so such call sites stay unchanged. *)
Canonical Structure AImg_cgif.
