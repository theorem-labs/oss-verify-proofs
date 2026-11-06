From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PHolds.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require UEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AgreePcap.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require PcapClose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B Require PcapCloseB.

Definition libreac_fuzz_pcap_plain_halts := PHolds.pcap_plain_halts_holds.

Definition libreac_fuzz_pcap_ubsan_halts := UEntry.ubsan_halts_holds.

Definition libreac_fuzz_pcap_ubsan_agrees := AgreePcap.ubsan_agrees_holds.

Definition libreac_fuzz_pcap_asan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.PcapClose.pcap_asan_agrees_of_parts.

Definition libreac_fuzz_pcap_asan_halts :=
  OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.PcapClose.pcap_asan_halts_of_parts.

Definition libreac_fuzz_pcap_asan_ubsan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapCloseB.pcap_asan_ubsan_agrees_of_parts.

Definition libreac_fuzz_pcap_asan_ubsan_halts :=
  OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapCloseB.pcap_asan_ubsan_halts_of_parts.
