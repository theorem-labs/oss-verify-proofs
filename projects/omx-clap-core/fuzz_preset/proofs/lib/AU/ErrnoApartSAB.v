(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/ErrnoApartScgif.v (a working branch 30a1993588f, file sha256 d5e52a0422bd) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at 74f20580f552) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve resolve-B102.txt (sha256 5cd2316e3413; internal record) (4 lines name this file); 0 numerals changed. *)
(* The cgif_file discharges of ErrnoApartS.v's image facts, at AImg_cgif (AGif2cgif) and AImgS_cgif (AGif4cgif).

   Moved here from ErrnoApartAB.v, names and proofs unchanged: errno_apart_dzone_s_cgif, errno_apart_shadow_s_cgif,
   errno_apart_zone3_s_cgif.  errno is TFIB_ERRNO = 0x5de68c (YF0m.v:16, ts_errno YF0m.v:297):
   - the depot zone AGjm.DZONE (AGjm.v:571-572): [0x17d5c8, 0x5cdd50) ends 0x1093c below errno; the nodes and store
     blocks are owned extents, apart by errno_in_img_cgif (ErrnoApartAB.v) and ErrnoApart.errno_apart_owned;
   - the shadow offset AGjm.SHBv (AGjm.v:163): 0x7fff8000, above errno;
   - zone3 (YF0x.v:64): off the image (zone3_off_img, YF0x.v:72).

   Require hazard: the Require closure reaches YA08 / YA09 / YA0e through ErrnoApartS (ErrnoApartScgif -> ErrnoApartS ->
   AGif4 -> YA09, AGif4 -> YG0b -> YA08 / YA0e), whose non-local
   Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false) (last at YA08.v:1303, YA09.v:3340,
   YA0e.v:3757) escapes Require: a file that Requires this one has lia's conversion of Z.div / Z.modulo to euclidean
   equations switched off, even when it had switched it on.  Consumer fix, one line after its Require block:
   #[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif4cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import ErrnoApartAB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoApartS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma errno_apart_dzone_s_cgif : errno_apart_dzone_s.
Proof.
intros B ly a TS LY IMG Hd. destruct Hd as [Hd|[Hd|Hd]].
- rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia.
- exact (errno_apart_owned errno_in_img_cgif B ly (ly_NB ly, kNodesBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; left; reflexivity) Hd).
- exact (errno_apart_owned errno_in_img_cgif B ly (ly_SB ly, kStoreBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; right; left; reflexivity) Hd).
Qed.

Lemma errno_apart_shadow_s_cgif : errno_apart_shadow_s.
Proof. intros B a TS Ha. change (0x7fff8000 <= a) in Ha. rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia. Qed.

Lemma errno_apart_zone3_s_cgif : errno_apart_zone3_s.
Proof.
intros B x sz a TS Hz Ha. pose proof (zone3_off_img x sz a Hz Ha) as O. rewrite (ts_errno B TS).
unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TFIB_ERRNO in *. lia.
Qed.

End a.
