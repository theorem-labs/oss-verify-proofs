(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK17.v, with its module paths changed. *)
(* Relocated from proofs/libreac/fuzz_grant/lib/YK17.v at 25e3d17bdb50 by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
Unset Lia Cache. Unset Nia Cache.
Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof. unfold rw_bytes_max. lia. Qed.
Lemma rw_bytes_max_nonneg : (0 <= rw_bytes_max)%Z.
Proof. pose proof rw_bytes_max_ge17. lia. Qed.
