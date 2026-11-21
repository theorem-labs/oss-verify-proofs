(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1u.v (theorem-labs/oss-verify-proofs@6b32741d849a), with its module paths changed, names TfibSyms -> PcapSyms and its addresses moved to libreac/fuzz_pcap's ASan build. RESTATED over pcap's read SOURCE (porter a Theorem Labs lane ruling 2): cgif's harness writes a file sink (asink_syms tfib_K, lib/A/AE2k.v, not ported: fuzz_pcap's ASan image holds none of cgif's sink strings), pcap's harness reads a memory stream, so the driver invariant FINV is stated over pcap's source symbols pcap_KS (lib/A/Stdio/PSourceK.v) with the source vocabulary of lib/A/Stdio/PSource.v / PSourceMeta.v: donor AD1u.v:60-63 FINV = ameta_inv tfib_K /\ astdio_env tfib_K /\ ofl head 0 becomes asrc_meta_inv pcap_KS /\ asrc_stdio_env pcap_KS /\ ofl head 0 (the last two are PSource.v's asource_none pcap_KS, the conjunct the program contract lib/A/Prog/PcapEntry.v asks). The donor's image laws tfib_AIL (AD1u.v:34, asink_img_laws) become tfib_ASIL (asource_img_laws, PSourceMeta.v:78, the sink head SK passed explicitly); FINV_IVS lists pcap_KS's cells (the meta pointer pair, "rwa\0", "rb\0", the canary, threaded, need_locks, ofl lock and head) in place of cgif's (no path / trailer string). The two frame lemmas the donor takes from YE00.v (astdio_env_frame, ameta_ok_frame) are restated here for the source record (asrc_stdio_env_frame, asrc_meta_ok_frame), bodies identical up to the field names, and meta_ptr_of_AR is PSourceMeta.v's asrc_meta_ptr_of_AR with the law read off B's constant table. The sink head is the Section's SK; the class pcap_head ties it to pcap's measured ofl_head 0x652308 (instantiated by reflexivity at SK := PcapSinkHeads.asan_sink_head). rule 24: no function proved anew; the image end is pcap_img_end (Reusable/PcapImgEnd.v). *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1u.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK00 YK0s YK15.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0m YP09 YI04 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Import AD1y_w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
