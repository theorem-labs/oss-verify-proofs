From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file (a Theorem Labs lane). *)

(* ---------------------------------------------------------------------------------------------- *)
(* PFmemopenC: pcap's fmemopen interceptor, CLOSED, for the ASAN image.                           *)
(*                                                                                                    *)
(* pcap_afmemopen_spec (PFmemopenI.v) proves __interceptor_fmemopen at FM_ENTRY with                 *)
(* ONE premise on its REAL(fmemopen) call: rfmemopen_contract ... PFMEMOPEN ra 0x10350 0x10370, the  *)
(* contract of musl fmemopen with the read-only mode window [0x10350, 0x10370).                      *)
(* rfmemopen_contract_pcap_noaintr (PFmemopenMW.v) proves that contract for musl fmemopen            *)
(* at K := pcap_KS and ra := FM_MALLOC_RA, with its window FM_MC_LO / FM_MC_HI, which are 0x10350 /  *)
(* 0x10370 by conversion. So the interceptor's REAL-call premise closes by that theorem alone, and   *)
(* the theorem below has only the premises of the two walks: the ARcf laws, the image's symbol      *)
(* table, the source-image laws and the allocator rule.                                              *)
(* ---------------------------------------------------------------------------------------------- *)

From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceK PFmemopenM PFmemopenISpec PStdioImgA.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PFmemopenI PFmemopenMW.
Open Scope Z_scope.

Theorem pcap_afmemopen_closed {fx : YK11.FPState} {rc : YM05.RunCeil}
    (B : YG0f.asyms) (SK : YI16.sink_head) (MT : YC5d.ameter_ops) (CTX : list (list Z)) :
  YG0d.AR_laws AB1v.tfibsegs B ->
  AF0m.PcapSyms B ->
  PSourceMeta.asource_img_laws SK AB1v.tfibsegs B pcap_KS ->
  YC5d.amalloc04_rule AB1v.tfibsegs B MT ->
  afmemopen_spec SK AB1v.tfibsegs B pcap_KS MT CTX PFmemopenI.FM_ENTRY FM_MALLOC_RA (symaddr (Symbols.Asan.Sec.s_rodata + 0x70)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 0x90)%Z).
Proof.
  intros LAWS TB ASIL AMR.
  exact (@PFmemopenI.pcap_afmemopen_spec fx rc B LAWS TB SK pcap_KS MT CTX FM_MALLOC_RA ASIL AMR
           (@PFmemopenMW.rfmemopen_contract_pcap_noaintr fx rc SK B MT CTX ASIL TB)).
Qed.
