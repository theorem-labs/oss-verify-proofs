(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/diginet_meter_segments_c.v, with its module paths and module names changed; 10 of its 21 lines of code are new or changed and 9 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the footprint form of diginet_meter_segments_contract (A/Prog/diginet_meter_segments_c.v) for fuzz_decode.asan, in the form of projects/libreac/fuzz_decode/proofs/lib/A/Prog/reac_upstream_channels_F_c.v. *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/libdiginet/fuzz_decode/lib/A/Prog/diginet_meter_segments_F_c.v (fuzz_decode.asan, image A, a code-identical twin) to fuzz_codec.asan, image A: entry 0x855c8, the image segments lib/A/AWalkFw0.v tfibsegs, module paths changed. *)
(* Footprint form of diginet_meter_segments_contract (image A, entry 0x855c8). The run is an ExecF.evtF run under a
   footprint RNG: every data access of every step lies in RNG. The code has no stack frame, loads nothing and stores
   nothing, so it makes no data access and the contract holds for every RNG: there is no rng premise. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_meter_segments_c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import ExecF.
Open Scope Z_scope.

Definition diginet_meter_segments_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mask : Z),
    0 <= mask < 2^16 ->
    ExecF.evtF tfibsegs RNG
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (diginet_meter_segments mask)) a1' a2' a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom tfibsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mask) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_METER_SEGMENTS_PC) fc None m (seg_rom tfibsegs)).
