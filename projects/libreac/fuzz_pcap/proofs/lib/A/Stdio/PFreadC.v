From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file (a Theorem Labs lane). *)

(* ---------------------------------------------------------------------------------------------- *)
(* PFreadC: pcap's fread interceptor, CLOSED, for the ASAN image.                                   *)
(*                                                                                                    *)
(* pcap_afread_spec (PFreadI.v, a Theorem Labs lane) proves the fread interceptor at FR_ENTRY 0x41580 with  *)
(* ONE premise on its REAL(fread) call: rfread_contract (SK:=SK) tfibsegs B K FR_REAL, the contract  *)
(* of musl fread at 0x8ee5c. rfread_contract_asan (PFreadMWA.v, a Theorem Labs lane) proves that contract at  *)
(* PFREAD, which is 0x8ee5c by conversion, from three callee contracts and three image facts:        *)
(*   - __toread at PTOREAD:  rtoread_contract_asan (PFtoreadMWA.v, a Theorem Labs lane);                      *)
(*   - mread at as_read K:   rmread_contract_asan (PFmreadMWA.v, a Theorem Labs lane), at K := pcap_KS, whose  *)
(*                           as_read is mread 0x8ea40 = PMREAD (PSourceK.v:16) by conversion;         *)
(*   - the image below kLowMemEnd and its nowrap layout: mr_segs_low_asan / mr_wx_asan (PFmreadMWA.v);*)
(*   - as_read pcap_KS in range and even: by computation.                                             *)
(* The memcpy trampoline's contract (aintrin_realizes ... OCpy TRAMP_MEMCPY) is the core runtime's  *)
(* and stays a premise, as amalloc04_rule does in PFmemopenC.v. So the theorem below has only the   *)
(* premises of the walks: the ARcf laws, the image's symbol table, the source-image laws and the    *)
(* memcpy trampoline's contract.                                                                      *)
(*                                                                                                    *)
(* The three file pairs this theorem rests on are in this tree: lib/A/Stdio/PFreadMW.v /          *)
(* PFreadMWA.v, PFtoreadMW.v / PFtoreadMWA.v and PFmreadMW.v / PFmreadMWA.v. The asan instances   *)
(* are Required from the per-image files (a Theorem Labs lane's image split), so no asan-ubsan    *)
(* instance is in this file's closure.                                                            *)
(* ---------------------------------------------------------------------------------------------- *)

From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceK PStdioImgA.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PFreadISpec PFreadI PFreadMWA PFtoreadMWA PFmreadMWA.
Open Scope Z_scope.

Theorem pcap_afread_closed {fx : YK11.FPState} {rc : YM05.RunCeil}
    (SK : YI16.sink_head) (B : YG0f.asyms) :
  YG0d.AR_laws AB1v.tfibsegs B ->
  AF0m.PcapSyms B ->
  PSourceMeta.asource_img_laws SK AB1v.tfibsegs B pcap_KS ->
  YG0d.aintrin_realizes AB1v.tfibsegs B YG0d.OCpy TRAMP_MEMCPY ->
  PFreadISpec.afread_spec SK AB1v.tfibsegs B pcap_KS PFreadI.FR_ENTRY.
Proof.
  intros LAWS TB ASIL MEMCPY.
  (* as_read pcap_KS is mread 0x8ea40: in range and even. *)
  assert (HMR : 0 <= as_read pcap_KS < 2 ^ 64 /\ as_read pcap_KS mod 2 = 0)
    by (change (as_read pcap_KS) with (symaddr Symbols.Asan.s_mread); split; [lia | reflexivity]).
  exact (PFreadI.pcap_afread_spec SK B pcap_KS LAWS TB ASIL
           (PFreadMWA.rfread_contract_asan (SK:=SK) B pcap_KS LAWS
              PFmreadMWA.mr_segs_low_asan PFmreadMWA.mr_wx_asan HMR ASIL MEMCPY
              (PFtoreadMWA.rtoread_contract_asan (SK:=SK) B pcap_KS ASIL)
              (PFmreadMWA.rmread_contract_asan (SK:=SK) B pcap_KS LAWS ASIL MEMCPY))).
Qed.
