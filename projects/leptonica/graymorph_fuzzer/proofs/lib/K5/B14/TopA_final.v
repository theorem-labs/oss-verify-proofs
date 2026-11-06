(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.leptonica.graymorph_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_closed
  Lept_iface Lept_fuzz_adapt Gm_iface Gm_gaps_proof Gm_top.

Theorem s3s_closed : S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  exact (s3s_of_conetop (fun RC GP => fuzz_adapt RTA (gm_fuzz_top RTA RC GP rta_gm_gaps))).
Qed.
