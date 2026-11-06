(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Asan.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_closed
  Lept_iface Pm_gaps_iface Pm_iface RT_stackmalloc2 Pm_spix_top Pm_cone Pm_fuzz_adapt.

Theorem s3s_closed : S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof.
  exact (s3s_of_conetop (fun RC GP => pm_fuzz_adapt RTA (pm_cone RTA (AFt RTA RC) RC GP pm_gaps_A (REPt RTA RC GP) (REIt RTA RC GP)
    (SEt RTA RC GP) (PADt RTA RC GP) (VALIDt RTA RC GP) (DESERt RTA RC GP) (DESTROYt RTA RC GP)))).
Qed.
