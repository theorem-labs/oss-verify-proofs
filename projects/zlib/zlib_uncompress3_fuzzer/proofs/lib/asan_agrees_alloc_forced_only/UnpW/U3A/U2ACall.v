(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg RtCells ABase I_asan_memset I_asan_memcpy.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Tactic Notation "callq" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtF_cut; [ eapply SPEC | post_call segs m ]
  end.
Tactic Notation "callqd" uconstr(SPEC) "dropping" ne_hyp_list(Hs) :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtF_cut; [ eapply SPEC | clear Hs; post_call segs m ]
  end.

Section CANSEC1. Context {rc : runConstT}.

Definition amemset_postz (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV D c n : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(SPV - 2208, SPV); (D, D + n)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo SPV
    /\ rw_cells asegs m' D [CB (Z.to_nat n) (repeat (Z_to_bv 8 (c mod 256)) (Z.to_nat n))].

Lemma asan_memset_callz :
  forall (RLO2 RHI2 : Z) (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SPV D c n lo : Z) (junk : list byte),
  0 <= SPV < 2^64 -> 0 <= D -> D + n < 2^64 -> 0 <= n -> 0 <= c < 2^64 ->
  mem_inv asegs m ->
  stk asegs m lo SPV -> lo <= SPV - 2208 -> KHIGH <= lo ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rw_cells asegs m D [CB (Z.to_nat n) junk] ->
  (D + n <= lo \/ SPV <= D) ->
  app_blk D (D + n) ->
  unpoisoned m D (D + n) ->
  n <= 2^40 ->
  (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND) ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (SPV - lo) -> rng RNG D n ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF asegs RNG (amemset_postz ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV D c n lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 c) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x5d56c) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros RS D0 DN N0 C0. intros.
  eapply evtF_mono; [eapply (asan_memset_spec RNG _ (Z_to_bv 64 SPV) _ _ _ _ _ _ _ (Z_to_bv 64 D) (Z_to_bv 64 c) (Z_to_bv 64 n));
                     rewrite ?unsigned_lit by lia; eassumption|].
  cbv beta. unfold asan_memset_post, amemset_postz. rewrite !unsigned_lit by lia. intros ms' PO. exact PO.
Qed.

Definition amemcpy_postz (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV D S n : Z) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(SPV - 2224, SPV); (D, D + n)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo SPV
    /\ rw_cells asegs m' D [CB (Z.to_nat n) src]
    /\ bytes_at asegs m' S src.

Lemma asan_memcpy_callz :
  forall (RLO1 RHI1 RLO2 RHI2 : Z) (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SPV D S n lo : Z) (src junk : list byte),
  0 <= SPV < 2^64 -> 0 <= D -> D + n < 2^64 -> 0 <= S -> S + n < 2^64 -> 0 <= n ->
  mem_inv asegs m ->
  stk asegs m lo SPV -> lo <= SPV - 2224 -> KHIGH <= lo ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  bytes_at asegs m S src -> length src = Z.to_nat n ->
  rw_cells asegs m D [CB (Z.to_nat n) junk] ->
  (S + n <= D \/ D + n <= S) ->
  (S + n <= SPV - 2224 \/ SPV <= S) ->
  (D + n <= lo \/ SPV <= D) ->
  app_blk S (S + n) -> app_blk D (D + n) ->
  unpoisoned m S (S + n) -> unpoisoned m D (D + n) ->
  n <= 2^40 ->
  (RLO1 <= S /\ S + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND) ->
  (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND) ->
  wr_at asegs m (shad RLO1) (shad RHI1 - shad RLO1) -> wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (SPV - lo) -> rng RNG S n -> rng RNG D n ->
  rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF asegs RNG (amemcpy_postz ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV D S n src lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x5d0d0) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros RS D0 DN S0 SN N0. intros.
  eapply evtF_mono; [eapply (asan_memcpy_spec RNG _ (Z_to_bv 64 SPV) _ _ _ _ _ _ _ (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n));
                     rewrite ?unsigned_lit by lia; eassumption|].
  cbv beta. unfold asan_memcpy_post, amemcpy_postz. rewrite !unsigned_lit by lia. intros ms' PO. exact PO.
Qed.

End CANSEC1.
