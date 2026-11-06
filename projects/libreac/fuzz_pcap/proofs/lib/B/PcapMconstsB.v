From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap (asan-ubsan image, lib/B); no function walk.
   pcap_mconsts_B is the argument MCONSTS of lib/B/Prog/PcapFuzzFopen.v pb_libreac_fuzz_fopenX (hypothesis at
   PcapFuzzFopen.v:157-159) at the lib/B instance: PI := lib/B/Prog/PcapEntryTop.v PI_pcap, roimg := lib/Reusable/YE3i.v
   ro_img, mc_lo := 0x10350, mc_hi := 0x10370 (.rodata+0x70 .. .rodata+0x90, __strchrnul's two word constants), for
   every rc. The window lies inside YE3i.img_ro_chunks' chunk [0x10330, 0x10398) (YE3i.v:42).
   The proof is the lib/A instance's (lib/A/Prog/PcapEntryInst.v inst_MCONSTS, commit 8994a315428): the second conjunct
   of lib/Reusable/YE2j.v:106 strchr_lit_ro_of_img, which is lib/Reusable/YE39.v:29-30 mconsts_view W mem, whose window
   [MC_LO, MC_HI) is [0x10350, 0x10370) (YE39.v:31 mc_bounds). Those lemmas are stated at segs := tfibsegs
   (lib/Reusable/YB1v.v:14, = AsanUbsan.M.loaded_segments); pa_segs PI_pcap is AsanUbsan.M.loaded_segments
   (PcapEntryTop.v:145, :164 pi_pcap_segs), so the two are convertible by delta and iota only. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YE3i YE39 YE2j.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YD2l YCej YCbp PcapSinkHeads.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapPa PcapList PcapEntryTop PcapFuzzFopen.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require PSourceK.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* lib/A and lib/U load modules of the same short names, so each is named by its full path (as lib/B/PcapCloseB.v
   does). *)
Module RE3i := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE3i.
Module RE39 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE39.
Module RE2j := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE2j.
Module RD2l := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD2l.
Module RCej := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCej.
Module RCbp := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCbp.
Module RPSH := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PcapSinkHeads.
Module PPA := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapPa.
Module PLS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapList.
Module PET := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntryTop.
Module PFF := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapFuzzFopen.
Module KSU := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PSourceK.

(* MCONSTS (PcapFuzzFopen.v:157-159) at SEGS := pa_segs (PI_pcap rc), roimg := YE3i.ro_img, mc_lo := 0x10350,
   mc_hi := 0x10370. *)
Lemma pcap_mconsts_B : forall (rc : YM05.RunCeil)
  (W : world (@PPA.pa_segs rc PLS.pcap_listing (@PET.PI_pcap rc))) (mem : word -> option byte),
  RE3i.ro_img (mrestrict (w_H W) mem) ->
  forall a, (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) <= a < (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x90)%Z) ->
  aview (@PPA.pa_segs rc PLS.pcap_listing (@PET.PI_pcap rc)) (w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b)
    (seg_rom (@PPA.pa_segs rc PLS.pcap_listing (@PET.PI_pcap rc)) (Z_to_bv 64 a)).
Proof.
intros rc W mem HRO a Ha.
pose proof RE39.mc_bounds as [MB1 MB2].
assert (Ha' : RE39.MC_LO <= a < RE39.MC_HI) by (rewrite MB1, MB2; exact Ha).
(* conversion: pa_segs (PI_pcap rc) and tfibsegs are both AsanUbsan.M.loaded_segments (PcapEntryTop.v:145,
   YB1v.v:14); mconsts_view W mem (YE39.v:29-30) is the goal's form at tfibsegs. *)
exact (proj2 (RE2j.strchr_lit_ro_of_img (W : world tfibsegs) mem HRO) a Ha').
Qed.

(* The lemma fills the slot MCONSTS of pb_libreac_fuzz_fopenX at the lib/B instance (the order of PcapFuzzFopen.v:565,
   :568-571; the style of lib/A/Prog/PcapEntryFinal.v:640-641): SK := PcapSinkHeads.asan_ubsan_sink_head,
   PI := PI_pcap rc, B := YD2l.PcapB, K := PSourceK.pcap_KS, FM_RA := 0x8e7d8 (PcapEntryDefs PE_FMEMOPEN_MALLOC_RA),
   CTX := YCej.CTX_pcap_source_open, MT := YCbp.ameter_triv, roimg := YE3i.ro_img, mc_lo := 0x10350,
   mc_hi := 0x10370; the other arguments are the binders. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) ROIMG_LOW LAWS MLAWS FI STRCMP AFMEMOPEN =>
  @PFF.pb_libreac_fuzz_fopenX fx rc RPSH.asan_ubsan_sink_head (@PET.PI_pcap rc) RD2l.PcapB KSU.pcap_KS (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z)
    RCej.CTX_pcap_source_open RCbp.ameter_triv RE3i.ro_img ROIMG_LOW (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x90)%Z) (pcap_mconsts_B rc)
    LAWS MLAWS FI STRCMP AFMEMOPEN).

Print Assumptions pcap_mconsts_B.
