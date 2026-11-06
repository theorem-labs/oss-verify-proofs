(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMrecF.v (commit ce1a656b52b7, file sha256 4ed40e679427) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrecF.v (commit 67fc7ef5787, lane B1 drain composition, DoRecycle chain; the chain's two function pairs, Quarantine::DoRecycle and LocalCache::Deallocate, re-checked EQUAL-mod-pcrel by cmpkit 4bbd3a74be89 strictcmp2 16982e3ef42b; file sha256 dd03b38c17fb) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1 of ReallocPrimary's Theorem Labs walk lanes, slice H2, a prior worker; interface
   DMwalkIF.v at dc3949af11c, frozen): Quarantine::DoRecycle (0x33cf8) at cgif_file_fuzzer's
   asan-ubsan image meets [DMwalkIF.dorecycle_spec_r] over the OPAQUE cut relation ARXr, owned set AOX and recycle
   invariant DRq, with fuel [length P] and the count-0 batch arm, under the six hypotheses of
   [DMwalkIF.dorecycle_ok_t] (TfibSyms, rmaxd_ok, di_frame_t, di_rview_x_t, MnRecycle's two callee contracts).
   The walk: DMrecM.dorecycle_arm_r, with its item step DMrecT5.T_R_r and its count-0 step DMrecT6.T_O0_r.
   rule 24: proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::DoRecycle
   (frame-generic, count-0 arm, fuel length P; lane B1 reuse search the internal file LOOKUP-B1-drain.txt, B1LookupCheck
   CONFIRM). *)
(* Theorem Labs, 2026-10-30 (a prior worker): the image-B (asan-ubsan) twin of lib/A/DMrecF.v at 14a6b2561a69, relocated by a Theorem Labs lane alreloc a5c53bb2bed4ad03 (every moved numeral a DoRecycle / LocalCache::Deallocate pc, +0x58) with the A twins A<r> renamed to the B twins Y<r>; the comment blocks above keep the A file's text and its A pcs. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMwalkIF DMrecM DMrecT5 DMrecT6.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem dorecycle_ok_r : forall B ARXr AOX DRq RMAXD, DMwalkIF.dorecycle_ok_t B ARXr AOX DRq RMAXD.
Proof.
intros B ARXr AOX DRq RMAXD TB HRM FR RV RCH CDH inst ly X P W regs mem md PRE.
pose proof PRE as (_ & Hinst & _). subst inst.
exact (DMrecM.dorecycle_arm_r B ARXr AOX DRq RMAXD TB HRM RV FR ly X P W regs mem md PRE
  (DMrecT5.T_R_r B ARXr AOX DRq RMAXD TB HRM RV FR ly X P W regs mem md PRE)
  (DMrecT6.T_O0_r B ARXr AOX DRq RMAXD TB HRM RV FR ly X P W regs mem md PRE) RCH CDH).
Qed.
End c.
Print Assumptions dorecycle_ok_r.
