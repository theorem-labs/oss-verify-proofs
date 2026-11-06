(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Asan.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_closed
  Lept_iface Lept_fuzz_adapt Lept_top Lept_deser.

Theorem s3s_closed : S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof.
  exact (s3s_of_conetop (fun RC GP => fuzz_adapt RTA (cone_of_open RTA RC GP
           (pixDeserialize_ok RTA (AFt RTA RC) RC GP (SEt RTA RC GP) (REPt RTA RC GP) (HDRt RTA RC GP) (CREt RTA RC GP) (DESTROYt RTA RC GP)
                              (CMDESt RTA RC GP) (SETCMt RTA RC GP) (VALIDt RTA RC GP))))).
Qed.

