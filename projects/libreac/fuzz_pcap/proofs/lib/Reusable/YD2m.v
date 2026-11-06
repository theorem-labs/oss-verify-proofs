(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD2m.v (origin/ossv/recipes c8557374ad2e), with its module paths changed, names TfibSyms -> PcapSyms and its addresses moved to libreac/fuzz_pcap's asan-ubsan build (pinned image fuzz_pcap.asan-ubsan sha256 9e66f771f22a, symbols from its unstripped twin fuzz_pcap.asan-ubsan sha256 c969d83cdd59). It is the asan-ubsan twin of a Theorem Labs lane's lib/A/AD2m.v (a working branch 9700d736a50): every hunk of that file against the donor's A file is mirrored here, each address re-measured on the asan-ubsan image (keyed by symbol + offset or section + offset, never by a delta from the asan value); a Theorem Labs lane's hunks there are module paths and the name PcapSyms only (AD2m holds no image numeral); tfib_AICPY stands on Reusable/YE31.v's memcpy_icpt_realizes and tfib_ARDCHK on Reusable/YE33.v's aread_check_realizes, the asan-ubsan twins of the AE31 / AE33 a Theorem Labs lane cites, so pcap_H_DRIVER's ARDCHK needs no foreign premise here either. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YM05 YB1v YG0f YG00 YG0n YG0d YG0q YF0m YD20 YD1i
YE31 YE33.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO09.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Lemma tfib_AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Proof.
pose proof (memcpy_icpt_realizes B (AR_laws_ok tfibsegs B) HB) as H.
unfold aintrin_realizes. rewrite (ts_code B HB). exact H.
Qed.
Lemma tfib_ARDCHK : aread_check_stmt B.
Proof.
exact (aread_check_realizes B (AR_laws_ok tfibsegs B) HB).
Qed.
End a.
