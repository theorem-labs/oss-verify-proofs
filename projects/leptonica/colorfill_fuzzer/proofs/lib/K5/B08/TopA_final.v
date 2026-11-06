(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.leptonica.colorfill_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_closed
  Lept_iface Cf_iface Cf_spix_top Cf_cone Cf_fuzz_adapt.

Theorem s3s_closed : S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  exact (s3s_of_conetop (fun RC GP => cf_fuzz_adapt RTA (cf_cone RTA (AFt RTA RC) RC GP (REPt RTA RC GP) (DESERt RTA RC GP) (DESTROYt RTA RC GP)))).
Qed.
