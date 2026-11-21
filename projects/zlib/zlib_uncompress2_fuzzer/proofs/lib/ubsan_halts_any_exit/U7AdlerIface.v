(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare Frame RefMemcpyLib FuzzMem U7AdlerBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Definition U7_adler32_z_stmt {RCa1 : RunCtx}  : Prop :=
  forall regs m rom (retw : word) (usp a adr len : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 len ->
    0 <= a < 2 ^ 64 -> 1 <= adr -> 0 <= len -> adr + len < 2 ^ 64 -> 128 <= usp < 2 ^ 64 ->
    store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) 128 = true ->
    (1 <= len -> adr + len <= usp - 128) ->
    img_ok m ->
    (forall i, 0 <= i < len -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    exists r m',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17da0 : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 128), 128%Z)].

Definition U7_adler32_z_null_stmt {RCa1 : RunCtx}  : Prop :=
  forall regs m rom (retw : word) (usp : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    128 <= usp < 2 ^ 64 ->
    store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) 128 = true ->
    exists r m',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17da0 : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 128), 128%Z)].

Definition U7_adler32_stmt {RCa1 : RunCtx}  : Prop :=
  forall regs m rom (retw : word) (usp a adr v len : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 v ->
    0 <= v < 2 ^ 64 -> v mod 2 ^ 32 = len ->
    0 <= a < 2 ^ 64 -> 1 <= adr -> adr + len < 2 ^ 64 -> 128 <= usp < 2 ^ 64 ->
    store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) 128 = true ->
    (1 <= len -> adr + len <= usp - 128) ->
    img_ok m ->
    (forall i, 0 <= i < len -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    exists r m',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x182d0 : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 128), 128%Z)].

Definition U7_adler32_null_stmt {RCa1 : RunCtx}  : Prop :=
  forall regs m rom (retw : word) (usp : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    128 <= usp < 2 ^ 64 ->
    store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 128)) 128 = true ->
    exists r m',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x182d0 : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 128), 128%Z)].
