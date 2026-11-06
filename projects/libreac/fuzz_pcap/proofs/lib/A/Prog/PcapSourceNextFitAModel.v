(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: the model's facts at a record that
   the buffer holds (0 < incl <= cap), used by the NP_fit phase (PcapSourceNextFitA.v) and its landing
   at NP_ts (PcapSourceNextFitALand.v). Image-free: only the model of PcapSourceNextDefs.v. *)
(* Modified by Theorem Labs, 2026-10: the lemmas fa_nth_byte .. fa_rec_tagged MOVED unchanged to the image-free
   PcapSourceNextFitAShared.v, which lib/B/Prog/PcapSourceNextFitA.v Requires instead of its own copy; this file
   Require Exports it, so every file that Requires this one sees the same names. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Export PcapSourceNextFitAShared.
