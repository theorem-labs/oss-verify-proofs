(* Audit file of the asan-ubsan (lib/B) closing tops, for the build of record (cbrec): one Check + Print Assumptions
   pair per name. The four tops of PcapCloseB.v and the two release exports of Theorems.v. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B Require PcapCloseB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Theorems.

Check OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapCloseB.H_PROG_LIBCONTRACT_U_of.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapCloseB.H_PROG_LIBCONTRACT_U_of.
Check OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapCloseB.ASAN_UBSAN_T_of_parts.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapCloseB.ASAN_UBSAN_T_of_parts.
Check OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapCloseB.pcap_asan_ubsan_agrees_of_parts.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapCloseB.pcap_asan_ubsan_agrees_of_parts.
Check OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapCloseB.pcap_asan_ubsan_halts_of_parts.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapCloseB.pcap_asan_ubsan_halts_of_parts.
Check OSSVerify.Proofs.libreac.fuzz_pcap.lib.Theorems.libreac_fuzz_pcap_asan_ubsan_agrees.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_pcap.lib.Theorems.libreac_fuzz_pcap_asan_ubsan_agrees.
Check OSSVerify.Proofs.libreac.fuzz_pcap.lib.Theorems.libreac_fuzz_pcap_asan_ubsan_halts.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_pcap.lib.Theorems.libreac_fuzz_pcap_asan_ubsan_halts.
