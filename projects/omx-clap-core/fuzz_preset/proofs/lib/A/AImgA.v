(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the image class AImg of a Theorem Labs lane's image-free interface files (Reusable/ImgBase.v) AT IMAGE A,
   preset's ASan binary: the instance AImg_A, moved here from A/ADIfaceA.v without change (Main 10:4xZ), so that the
   instance chain mirrors cgif's three files: AImg here (cgif: AGif2cgif) <- AGImg in A/AGImgA.v (cgif: AGif0cgif) <-
   DImg in A/ADIfaceA.v (cgif: DGif0cgif), and DImg_A can take AGImgA's inst_ok and CZONE without an import cycle.
   Every field is lib/A's name: the segments A/AB1v.v:12 (Asan.M.loaded_segments), the cells TFIB_TP / TFIB_TSD /
   TFIB_OOM / TFIB_ERRNO, the symbol facts TfibSyms and the constant cells Tfib_const (A/AF0m.v), and the image window
   A/AF0x.img_cover (YImgTop.IMG_LO .. IMG_TOP). No address of preset's image is typed here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x.

#[export] Instance AImg_A : AImg := {|
  im_segs := tfibsegs;
  im_tp := TFIB_TP; im_tsd := TFIB_TSD; im_oom := TFIB_OOM; im_errno := TFIB_ERRNO;
  im_img_cover := AF0x.img_cover;
  im_syms := TfibSyms;
  im_const := Tfib_const;
  im_const_eq := fun B ly TS => ts_const B TS ly
|}.
Canonical Structure AImg_A.
