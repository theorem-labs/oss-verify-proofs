(* Modified by Theorem Labs, 2026-11: made from A/ACeg.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACeg.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
(* Modified by Theorem Labs, 2026-10: proofs open the image bounds the relocation names (pcap_img_end, YImgTop.IMG_LO / IMG_TOP, PcapRelro.PCAP_RLO / PCAP_RHI, and off_img's YImgTop bounds) where lia needs their values; statements unchanged. *)
(* Modified by Theorem Labs, 2026-10: lib_const_addr is stated from fuzz_pcap's own measured constant reads, not relocated
   (the relocation gave `(0x103b0 <= a < 0x103b0) \/ (0x9a4a8 <= a < 0x9a4a8)`, two empty spans). In the donor it names the
   read-only cells that cgif's library walks load (cgif_file_fuzzer A/AI12.v objects 10, 3, 7, 9): the .rodata u64
   0x0101010101010102 at 0x103b0 that LZW_GenerateStream reads (A/AC97.v:105) and the .got words 0x9ec10..0x9ec28 that
   cgif_newgif and cgif_raw_newgif read (A/ACkg.v:31, A/ACee.v:67-76). The shadow and uar .got words have their own fields
   below, and the module dtor's globals pair (donor 0x9ec28) belongs to the exit walk (A/AE37.v).
   MEASURED on fuzz_pcap.asan (pin sha256 b7a91d9b1fb0, symbols from its unstripped twin, RV64C decode of every
   instruction): the walked program functions libreac_fuzz_fopen 0x80738, LLVMFuzzerTestOneInput 0x807c8,
   pcap_source_open 0x8145c, pcap_source_next 0x8181c and pcap_source_close 0x81e90 load only the .got words 0x99830
   (A_GOT_shadow) and 0x99888 (A_GOT_uar) and the .bss cells g_file / g_file_len; they load no .rodata cell and no other
   .got word, and make no indirect jump. The other read-only loads of the listing (lib/A/Prog/PcapAddr.v objects 7, 8)
   are asan.module_ctor / asan.module_dtor's .got 0x9a4a8 / 0x9a4b0 (-> __start_asan_globals / __stop_asan_globals),
   which the start-up and exit walks take from A/AF0m.v's rows (A/AE37.v), as the donor does for its 0x9ec28 pair.
   So the set is empty, and it is stated as False (port_core.py's form for a unit that reads none). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP02 YP0l YP03 YP00 YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YG0n_w YG0s_w YG0d_w YCe5_w.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AF0l ACej.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapRelro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c.
Lemma Hwx_tfa : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
End c.
