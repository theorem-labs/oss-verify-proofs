(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare Frame RefMemcpyLib.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Section FXG. Context {fx : FPState}.

Definition S0_FZ_ENTRY : Z := 0x141f0.
Definition S0_FZ_FRAME : Z := 192.
Definition S0_RO_LO : Z := 0x10554.
Definition S0_RO_LEN : Z := 0x1494.

Definition s0_fuzz_stmt : Prop := forall regs mem rom (ret sp data : word) (n : Z),
  getr regs 1 = ret -> ret_ok ret -> getr regs 2 = sp ->
  getr regs 10 = data -> getr regs 11 = Z_to_bv 64 n ->
  (0 <= n)%Z ->
  (1 <= bv_unsigned data)%Z ->
  (bv_unsigned data + n < 2 ^ 64)%Z ->
  (192 <= bv_unsigned sp)%Z ->
  ((1 <= n <= 1048576)%Z -> forall i, (0 <= i < n)%Z ->
      exists b, rdn Src_zlib_checksum_fuzzer_repro.M.loaded_segments mem (Z_to_bv 64 (bv_unsigned data + i)) 1 = Some [b]) ->
  store_ok Src_zlib_checksum_fuzzer_repro.M.loaded_segments mem (Z_to_bv 64 (bv_unsigned sp - 192)) 192 = true ->
  ((1 <= n <= 1048576)%Z -> (bv_unsigned data + n <= bv_unsigned sp - 192)%Z) ->
  (forall j, (0 <= j < 0x1494)%Z -> mem (Z_to_bv 64 (0x10554 + j)) = None) ->
  exists regs' mem',
    msteps Src_zlib_checksum_fuzzer_repro.M.loaded_segments (mkst regs (0x141f0 : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 192), 192%Z)].
End FXG.
