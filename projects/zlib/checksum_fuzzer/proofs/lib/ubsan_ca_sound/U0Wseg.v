(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import WsegFast PropExec StreamSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma data_window_wseg {RCa1 : RunCtx}  : wseg_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments Tgt_checksum_fuzzer_ubsan.M.loaded_segments rc_inp rc_sp rc_mb) (Z_to_bv 64 0x1f000) 204800 = true.
Proof. apply wseg_fast_sound. vm_cast_no_check (@eq_refl bool true). Qed.
