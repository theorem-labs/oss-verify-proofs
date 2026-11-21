(* reloc-zl14c 6d6c62a81c018796080770ed85536fdc *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress3_fuzzer_repro.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Frame OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.FuzzMem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.S8AdlerBase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
(* [comment removed for export] *)
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition S8_adler32_z_null_stmt : Prop :=
  forall regs m rom (retw : word),
    getr regs 1 = retw -> ret_ok retw -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    exists r,
      msteps RSEGS (mkst regs (0x172e0 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r.

(* [comment removed for export] *)

Definition S8_adler32_null_stmt : Prop :=
  forall regs m rom (retw : word),
    getr regs 1 = retw -> ret_ok retw -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    exists r,
      msteps RSEGS (mkst regs (0x176a4 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r.
End FXG.
