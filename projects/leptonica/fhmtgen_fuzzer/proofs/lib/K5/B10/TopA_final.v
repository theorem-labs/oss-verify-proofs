(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_closed
  RT_strcmp Gm_iface Gm_gaps_proof Fh_iface Fh_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma rta_fh_gaps : fh_gaps RTA.
Proof. exact (mkFhGaps RTA rta_strcmp). Qed.

Theorem s3s_closed : S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  exact (s3s_of_conetop (fun RC GP => fh_fuzz_top RTA RC GP rta_gm_gaps rta_fh_gaps)).
Qed.
