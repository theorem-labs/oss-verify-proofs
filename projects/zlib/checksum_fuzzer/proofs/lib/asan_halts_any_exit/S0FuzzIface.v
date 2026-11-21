(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare Frame RefMemcpyLib FuzzMem S0FuzzBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section FXG. Context {fx : FPState}.

Definition S0_CRC_FR : Z := 80.
Definition S0_ADL_FR : Z := 32.


Definition S0_crc32_z_stmt : Prop :=
  forall regs m rom (retw : word) (usp c adr len : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 len ->
    0 <= c < 2 ^ 64 -> 1 <= adr -> 0 <= len -> adr + len < 2 ^ 64 -> 80 <= usp < 2 ^ 64 ->
    store_ok RSEGS m (Z_to_bv 64 (usp - 80)) 80 = true ->
    (1 <= len -> adr + len <= usp - 80) ->
    img_ok m ->
    (forall i, 0 <= i < len -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    exists r m',
      msteps RSEGS (mkst regs (0x14580 : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (crc32_z_model adr c (bytes_at RSEGS m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 80), 80%Z)].

Definition S0_crc32_z_null_stmt : Prop :=
  forall regs m rom (retw : word),
    getr regs 1 = retw -> ret_ok retw -> getr regs 11 = Z_to_bv 64 0 ->
    exists r,
      msteps RSEGS (mkst regs (0x14580 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 0
      /\ keeps_cs regs r.

Definition S0_crc32_stmt : Prop :=
  forall regs m rom (retw : word) (usp c adr v len : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 v ->
    0 <= v < 2 ^ 64 -> v mod 2 ^ 32 = len ->
    0 <= c < 2 ^ 64 -> 1 <= adr -> adr + len < 2 ^ 64 -> 80 <= usp < 2 ^ 64 ->
    store_ok RSEGS m (Z_to_bv 64 (usp - 80)) 80 = true ->
    (1 <= len -> adr + len <= usp - 80) ->
    img_ok m ->
    (forall i, 0 <= i < len -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    exists r m',
      msteps RSEGS (mkst regs (0x14be4 : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (crc32_z_model adr c (bytes_at RSEGS m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 80), 80%Z)].

Definition S0_crc32_null_stmt : Prop :=
  forall regs m rom (retw : word),
    getr regs 1 = retw -> ret_ok retw -> getr regs 11 = Z_to_bv 64 0 ->
    exists r,
      msteps RSEGS (mkst regs (0x14be4 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 0
      /\ keeps_cs regs r.


Definition S0_adler32_z_stmt : Prop :=
  forall regs m rom (retw : word) (usp a adr len : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 len ->
    0 <= a < 2 ^ 64 -> 1 <= adr -> 0 <= len -> adr + len < 2 ^ 64 -> 32 <= usp < 2 ^ 64 ->
    store_ok RSEGS m (Z_to_bv 64 (usp - 32)) 32 = true ->
    (1 <= len -> adr + len <= usp - 32) ->
    img_ok m ->
    (forall i, 0 <= i < len -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    exists r m',
      msteps RSEGS (mkst regs (0x14e14 : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at RSEGS m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 32), 32%Z)].

Definition S0_adler32_z_null_stmt : Prop :=
  forall regs m rom (retw : word),
    getr regs 1 = retw -> ret_ok retw -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    exists r,
      msteps RSEGS (mkst regs (0x14e14 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r.

Definition S0_adler32_stmt : Prop :=
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
      msteps RSEGS (mkst regs (0x151d8 : word) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at RSEGS m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - 32), 32%Z)].

Definition S0_adler32_null_stmt : Prop :=
  forall regs m rom (retw : word),
    getr regs 1 = retw -> ret_ok retw -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    exists r,
      msteps RSEGS (mkst regs (0x151d8 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r.


Definition S0_crc32_combine_stmt : Prop :=
  forall regs m rom (retw : word) (crc1 crc2 len2 : Z),
    getr regs 1 = retw -> ret_ok retw ->
    getr regs 10 = Z_to_bv 64 crc1 -> getr regs 11 = Z_to_bv 64 crc2 -> getr regs 12 = Z_to_bv 64 len2 ->
    0 <= crc1 < 2 ^ 32 -> 0 <= crc2 < 2 ^ 64 -> 0 <= len2 < 2 ^ 63 ->
    img_ok m ->
    exists r,
      msteps RSEGS (mkst regs (0x14d18 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (crc32_combine crc1 crc2 len2)
      /\ keeps_cs regs r.

Definition S0_crc32_combine_gen_stmt : Prop :=
  forall regs m rom (retw : word) (len2 : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 10 = Z_to_bv 64 len2 ->
    0 <= len2 < 2 ^ 63 ->
    img_ok m ->
    exists r,
      msteps RSEGS (mkst regs (0x14bf0 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (crc32_combine_gen len2)
      /\ keeps_cs regs r.

Definition S0_crc32_combine_op_stmt : Prop :=
  forall regs m rom (retw : word) (crc1 crc2 op : Z),
    getr regs 1 = retw -> ret_ok retw ->
    getr regs 10 = Z_to_bv 64 crc1 -> getr regs 11 = Z_to_bv 64 crc2 -> getr regs 12 = Z_to_bv 64 op ->
    0 <= crc1 < 2 ^ 32 -> 0 <= crc2 < 2 ^ 64 -> 0 <= op < 2 ^ 64 -> op mod 2 ^ 32 <> 0 ->
    exists r,
      msteps RSEGS (mkst regs (0x14ca4 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (crc32_combine_op crc1 crc2 op)
      /\ keeps_cs regs r.

Definition S0_adler32_combine_stmt : Prop :=
  forall regs m rom (retw : word) (a1 a2 len2 : Z),
    getr regs 1 = retw -> ret_ok retw ->
    getr regs 10 = Z_to_bv 64 a1 -> getr regs 11 = Z_to_bv 64 a2 -> getr regs 12 = Z_to_bv 64 len2 ->
    0 <= a1 < 2 ^ 64 -> 0 <= a2 < 2 ^ 64 -> 0 <= len2 < 2 ^ 63 ->
    img_ok m ->
    exists r,
      msteps RSEGS (mkst regs (0x151e4 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_combine_model a1 a2 len2)
      /\ keeps_cs regs r.
End FXG.
