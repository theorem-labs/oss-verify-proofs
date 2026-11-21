(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From LinuxProcessSemantics.LinuxProcessSem Require State Run.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import WsegFast PropExec StreamSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma data_window_wseg {RCa1 : RunCtx}  : wseg_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments rc_inp rc_sp rc_mb) (Z_to_bv 64 0x23000) 466944 = true.
Proof. apply wseg_fast_sound. vm_cast_no_check (@eq_refl bool true). Qed.
