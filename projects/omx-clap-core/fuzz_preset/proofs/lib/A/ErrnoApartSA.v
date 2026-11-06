(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/ErrnoApartScgif.v (a working branch 30a1993588f, file sha256 d5e52a0422bd) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at 3d44582d342f) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc ced0368250cb6538 (a working branch b85bfdee67c4), --assume-source, --resolve the internal file resolve-102.txt (4 lines name this file); 0 numerals changed. *)
(* The cgif_file discharges of ErrnoApartS.v's image facts, at AImg_A (AGif2cgif) and AImgS_A (AGif4cgif).

   Moved here from ErrnoApartA.v, names and proofs unchanged: errno_apart_dzone_s_cgif, errno_apart_shadow_s_cgif,
   errno_apart_zone3_s_cgif.  errno is TFIB_ERRNO = 0x5dde4c (AF0m.v:16, ts_errno AF0m.v:297):
   - the depot zone AGjm.DZONE (AGjm.v:571-572): [0x17cd88, 0x5cd510) ends 0x1093c below errno; the nodes and store
     blocks are owned extents, apart by errno_in_img_cgif (ErrnoApartA.v) and ErrnoApart.errno_apart_owned;
   - the shadow offset AGjm.SHBv (AGjm.v:163): 0x7fff8000, above errno;
   - zone3 (AF0x.v:64): off the image (zone3_off_img, AF0x.v:72).

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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgSA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoApartS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ErrnoApartA.
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
