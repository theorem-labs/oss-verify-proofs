(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare Frame RefMemcpyLib FuzzMem. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW Require Import S9AdlerBase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
(* [comment removed for export] *)
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition S9_adler32_z_null_stmt : Prop :=
  forall regs m rom (retw : word),
    getr regs 1 = retw -> ret_ok retw -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    exists r,
      msteps RSEGS (mkst regs (0x1725c : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r.

Definition S9_adler32_stmt : Prop :=
  forall regs m rom (retw : word) (usp a adr v len : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 v ->
    0 <= v < 2 ^ 64 -> v mod 2 ^ 32 = len ->
    0 <= a < 2 ^ 64 -> 1 <= adr -> adr + len < 2 ^ 64 -> 32 <= usp < 2 ^ 64 ->
    store_ok RSEGS m (Z_to_bv 64 (usp - 32)) 32 = true ->
    (1 <= len -> adr + len <= usp - 32) ->
    img_ok m ->
    (forall i, 0 <= i < len -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    exists r m',
      msteps RSEGS (mkst regs (0x17620 : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at RSEGS m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 32), 32%Z)].

Definition S9_adler32_null_stmt : Prop :=
  forall regs m rom (retw : word),
    getr regs 1 = retw -> ret_ok retw -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    exists r,
      msteps RSEGS (mkst regs (0x17620 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r.
End FXG.
