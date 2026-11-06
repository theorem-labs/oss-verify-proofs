(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/ErrnoApartcgif.v (a working branch 29b7505aa27, file sha256 6c556421afce) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at 3d44582d342f) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc ced0368250cb6538 (a working branch b85bfdee67c4), --assume-source, --resolve the internal file resolve-102.txt (16 lines name this file); 0 numerals changed. *)
(* The cgif_file discharges of ErrnoApart.v's image facts, at the cgif instances AImg_A (AGif2cgif), AGImg_A
   (AGif0cgif) and DImg_A (DGif0cgif).  errno is TFIB_ERRNO = 0x5dde4c (AF0m.v:19, ts_errno AF0m.v:1798), 4 bytes,
   in the image [TFIB_IMG_LO, TFIB_IMG_END) = [0x10000, 0x600000) (AF0x.v:26, :39):
   - errno_in_img: img_cover (AF0x.v:57) puts the layout's image window around [0x10000, 0x600000);
   - errno_unhidden: errno lies in the image's read-write window [0xa1000, 0x600000), where every byte is a segment
     byte (AB13.tfib_rw_rom, AB13.v:110) and a world hides no segment byte (w_Hoff, YK04.memory_read1_hidden): the
     proof of YFff.rw_unhidden / AGif1m.rw_not_hidden (AGif1m removed in this series).  It Requires YB13 alone, whose closure sets no Zify flag:
     AGif1m reaches YA09 (CLrefillR -> YFkn), and YFff reaches YB15 / YE08, which reset the flag (to true);
   - the depot zone (AGis.v:231-232 = DGgi.v:515-516): [0x17cd88, 0x5cd510) ends 0x1093c below errno; the nodes and
     store blocks are owned extents, apart by errno_in_img (ErrnoApart.errno_apart_owned);
   - the internal allocator's zone (DGgi.v:517): [0xac0c0, 0x12d0f0) and [0x13a948, 0x13a94c), below errno;
   - the shadow offset AGis.SHBv (AGis.v:166): 0x7fff8000, above errno;
   - zone3 (AF0x.v:68): off the image (zone3_off_img, AF0x.v:76);
   - the instance window inst_ok (AGImgA.v:60): [inst, inst + 0xe60) inside [0xa3e98, 0xa86e0), below errno.
   The arms apply ErrnoApart's lemmas with these as the image premises.

   Moved to ErrnoApartScgif.v, names and proofs unchanged, with the Props they discharge (now in ErrnoApartS.v):
   errno_apart_dzone_s_cgif, errno_apart_shadow_s_cgif, errno_apart_zone3_s_cgif.  This file's Require closure
   reaches none of AGif4, YA08, YA09, YA0e (ErrnoApartScgif.v's header names that hazard and the consumer's fix). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoApart.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma errno_in_img_cgif : errno_in_img.
Proof.
intros B ly TS [C1 C2]. rewrite (ts_errno B TS). unfold TFIB_ERRNO, TFIB_IMG_LO, TFIB_IMG_END in *. lia.
Qed.

Lemma errno_unhidden_cgif : errno_unhidden.
Proof.
intros B W a TS Ha. rewrite (ts_errno _ TS) in Ha. unfold TFIB_ERRNO in Ha.
destruct (w_H W (Z_to_bv 64 a)) eqn:Eh; [|reflexivity]. exfalso. apply (AB13.tfib_rw_rom a ltac:(lia)).
unfold seg_rom. rewrite (memory_read1_hidden tfibsegs (w_H W) (w_Hoff W) _ Eh). reflexivity.
Qed.

Lemma errno_apart_dzone_ag_cgif : errno_apart_dzone_ag.
Proof.
intros B ly a TS LY IMG Hd. destruct Hd as [Hd|[Hd|Hd]].
- rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia.
- exact (errno_apart_owned errno_in_img_cgif B ly (ly_NB ly, kNodesBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; left; reflexivity) Hd).
- exact (errno_apart_owned errno_in_img_cgif B ly (ly_SB ly, kStoreBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; right; left; reflexivity) Hd).
Qed.

Lemma errno_apart_dzone_d_cgif : errno_apart_dzone_d.
Proof.
intros B ly a TS LY IMG Hd. destruct Hd as [Hd|[Hd|Hd]].
- rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia.
- exact (errno_apart_owned errno_in_img_cgif B ly (ly_NB ly, kNodesBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; left; reflexivity) Hd).
- exact (errno_apart_owned errno_in_img_cgif B ly (ly_SB ly, kStoreBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; right; left; reflexivity) Hd).
Qed.

Lemma errno_apart_izone_cgif : errno_apart_izone.
Proof.
intros B a TS Hz. rewrite (ts_errno B TS).
destruct Hz as [Hz|Hz]; unfold TFIB_ERRNO, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *; lia.
Qed.

Lemma errno_apart_shadow_ag_cgif : errno_apart_shadow_ag.
Proof. intros B a TS Ha. change (0x7fff8000 <= a) in Ha. rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia. Qed.

Lemma errno_apart_zone3_d_cgif : errno_apart_zone3_d.
Proof.
intros B x sz a TS Hz Ha. pose proof (zone3_off_img x sz a Hz Ha) as O. rewrite (ts_errno B TS).
unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TFIB_ERRNO in *. lia.
Qed.

Lemma errno_apart_inst_ag_cgif : errno_apart_inst_ag.
Proof. intros B inst a TS [H1 [H2 _]] Ha. rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia. Qed.

Lemma errno_apart_inst_d_cgif : errno_apart_inst_d.
Proof. intros B inst a TS [H1 [H2 _]] Ha. rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia. Qed.
End a.
