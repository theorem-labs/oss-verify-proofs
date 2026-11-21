(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Tgt_example_flush_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare Frame RefMemcpyLib FuzzMem U6AdlerBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition U6_adler32_z_stmt : Prop :=
  forall regs m rom (retw : word) (usp a adr len : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 len ->
    0 <= a < 2 ^ 64 -> 1 <= adr -> 0 <= len -> adr + len < 2 ^ 64 -> 128 <= usp < 2 ^ 64 ->
    store_ok USEGS m (Z_to_bv 64 (usp - 128)) 128 = true ->
    (1 <= len -> adr + len <= usp - 128 \/ usp <= adr) ->
    img_ok m ->
    (forall i, 0 <= i < len -> exists b : byte, rdn USEGS m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    exists r m',
      msteps USEGS (mkst regs (0x1aa0c : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at USEGS m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 128), 128%Z)].

Definition U6_adler32_z_null_stmt : Prop :=
  forall regs m rom (retw : word) (usp : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    128 <= usp < 2 ^ 64 ->
    store_ok USEGS m (Z_to_bv 64 (usp - 128)) 128 = true ->
    exists r m',
      msteps USEGS (mkst regs (0x1aa0c : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 128), 128%Z)].

Definition U6_adler32_stmt : Prop :=
  forall regs m rom (retw : word) (usp a adr v len : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 v ->
    0 <= v < 2 ^ 64 -> v mod 2 ^ 32 = len ->
    0 <= a < 2 ^ 64 -> 1 <= adr -> adr + len < 2 ^ 64 -> 128 <= usp < 2 ^ 64 ->
    store_ok USEGS m (Z_to_bv 64 (usp - 128)) 128 = true ->
    (1 <= len -> adr + len <= usp - 128 \/ usp <= adr) ->
    img_ok m ->
    (forall i, 0 <= i < len -> exists b : byte, rdn USEGS m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    exists r m',
      msteps USEGS (mkst regs (0x1af3c : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at USEGS m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 128), 128%Z)].

Definition U6_adler32_null_stmt : Prop :=
  forall regs m rom (retw : word) (usp : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    128 <= usp < 2 ^ 64 ->
    store_ok USEGS m (Z_to_bv 64 (usp - 128)) 128 = true ->
    exists r m',
      msteps USEGS (mkst regs (0x1af3c : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 128), 128%Z)].
End FXG.
