(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane): new file, the asan-ubsan twin of the A fread closure
   (lib/A/Stdio/PFreadC.v, a Theorem Labs lane's sibling lane), in the shape of lib/A/Stdio/PFmemopenC.v
   (a working branch c5180b0bcf1). *)

(* ---------------------------------------------------------------------------------------------- *)
(* PFreadC: pcap's fread interceptor, CLOSED, for the ASAN-UBSAN image.                            *)
(*                                                                                                  *)
(* pcapu_afread_spec (lib/B/Stdio/PFreadI.v) proves __interceptor_fread at FR_ENTRY_U 0x415d0 with  *)
(* ONE premise on its REAL(fread) call: rfread_contract ... PStdioImgB.PFREAD_U.                    *)
(* rfread_contract_asan_ubsan (lib/B/Stdio/PFreadMWB.v) proves that contract from the               *)
(* image facts and three callee contracts:                                                          *)
(*   - the memory-copy trampoline's aintrin_realizes OCpy at PStdioImgB.TRAMP_MEMCPY_U 0x51560:     *)
(*     the asan-ubsan core's memcpy_icpt_realizes (lib/Reusable/YE31.v:145), which states exactly   *)
(*     that predicate at 0x51560 from AR_laws and PcapSyms;                                         *)
(*   - rtoread_contract at PStdioImgB.PTOREAD_U: rtoread_contract_asan_ubsan                        *)
(*     (lib/B/Stdio/PFtoreadMWB.v);                                                                 *)
(*   - rmread_contract at as_read pcap_KS = PCAP_MREAD = PStdioImgB.PMREAD_U 0x8e90c (by            *)
(*     conversion): rmread_contract_asan_ubsan (lib/B/Stdio/PFmreadMWB.v).                          *)
(* The three instances come from their per-image files (the image split); the image-free walks they *)
(* instantiate stay in lib/A/Stdio/PF{read,toread,mread}MW.v, and no asan instance is Required.     *)
(* The image facts are the asan-ubsan core's: YCeg.tfib_segs_low (every segment below kLowMemEnd)   *)
(* and YF0x.Hwx_tfa (wx_segs_nowrap); as_read pcap_KS = 0x8e90c is even and in range by             *)
(* computation. K := pcap_KS is the asan-ubsan instance of lib/B/Stdio/PSourceK.v.                  *)
(* So the theorem below has only the premises of the walks: the AR laws, the image's symbol table   *)
(* and the source-image laws.                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PSourceK PStdioImgB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require PFreadI.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require PFreadMWB PFtoreadMWB PFmreadMWB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YB1v YF0m YF0x YCeg YE31.
Open Scope Z_scope.
(* The core's global Zify flag leak (a Theorem Labs lane 09:00Z: YE2e.v:29, reached here through PStdioImgB, and ~120 other core
   files set this flag to false and never reset it): restore lia's div / mod handling for HMR's `mod 2` below. *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Theorem pcapu_afread_closed {fx : YK11.FPState} {rc : YM05.RunCeil}
    (B : YG0f.asyms) (SK : YI16.sink_head) :
  YG0d.AR_laws YB1v.tfibsegs B ->
  YF0m.PcapSyms B ->
  PSourceMeta.asource_img_laws SK YB1v.tfibsegs B pcap_KS ->
  afread_spec SK YB1v.tfibsegs B pcap_KS PFreadI.FR_ENTRY_U.
Proof.
  intros LAWS TB ASIL.
  (* the memory-copy trampoline: the asan-ubsan core's contract at 0x51560 = PStdioImgB.TRAMP_MEMCPY_U *)
  assert (MEMCPY : YG0d.aintrin_realizes YB1v.tfibsegs B YG0d.OCpy TRAMP_MEMCPY_U)
    by exact (YE31.memcpy_icpt_realizes B LAWS TB).
  (* mread's entry as_read pcap_KS = PCAP_MREAD = 0x8e90c: in range and even *)
  assert (HMR : 0 <= as_read pcap_KS < 2 ^ 64 /\ as_read pcap_KS mod 2 = 0)
    by (cbv [pcap_KS PCAP_MREAD as_read]; lia).
  (* SK is passed by name everywhere: sink_head has a global PLAIN-image instance (lib/Reusable/YI5b.v:12). *)
  apply (PFreadI.pcapu_afread_spec SK B pcap_KS LAWS TB ASIL).
  apply (PFreadMWB.rfread_contract_asan_ubsan (SK:=SK) B pcap_KS LAWS YCeg.tfib_segs_low YF0x.Hwx_tfa HMR ASIL
           MEMCPY).
  - exact (PFtoreadMWB.rtoread_contract_asan_ubsan (SK:=SK) B pcap_KS ASIL).
  - exact (PFmreadMWB.rmread_contract_asan_ubsan (SK:=SK) B pcap_KS LAWS ASIL MEMCPY).
Qed.
