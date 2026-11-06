(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.leptonica.kernel_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA RT_iface RT_rep RT_traces D_libiface RT_gaps_iface RT_gaps_proof TopA_closed
  Lept_iface RT_callocK_ok Km_iface Km_spix_top Km_cone Km_fuzz_adapt.
Import ListNotations.
Open Scope Z_scope.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma km_tr1 : In [0x9198c] CLIENT_TRACES. Proof. vm_compute. tauto. Qed.
Lemma km_tr2 : In [0x91c14] CLIENT_TRACES. Proof. vm_compute. tauto. Qed.
Lemma km_tr3 : In [0x91c3c] CLIENT_TRACES. Proof. vm_compute. tauto. Qed.
Lemma km_tr4 : In [0x91dcc] CLIENT_TRACES. Proof. vm_compute. tauto. Qed.
Lemma km_tr5 : In [0x91e08] CLIENT_TRACES. Proof. vm_compute. tauto. Qed.
Lemma km_tr6 : In [0x91e10] CLIENT_TRACES. Proof. vm_compute. tauto. Qed.

Theorem s3s_closed : S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  exact (s3s_of_conetop (fun RC GP => km_fuzz_adapt RTA (km_cone RTA (AFt RTA RC) RC GP rta_callocK_ok (REPt RTA RC GP) (DESERt RTA RC GP)
    (DESTROYt RTA RC GP) km_tr1 km_tr2 km_tr3 km_tr4 km_tr5 km_tr6))).
Qed.
