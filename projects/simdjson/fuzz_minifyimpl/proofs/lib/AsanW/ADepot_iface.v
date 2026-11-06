(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation ADEPOT_PUT := 0xa2e78 (only parsing).
Notation ADEPOT_LO := 0x242288 (only parsing).     (* [comment removed for export] *)
Notation ADEPOT_HI := 0x6922d0 (only parsing).     (* [comment removed for export] *)
Notation ADEPOT_STACK := 1024 (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
Notation adepot_W L sp :=
  ([(sp - ADEPOT_STACK, sp); (ADEPOT_LO, ADEPOT_HI);
    (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Definition depot_put_post (L : alayout) (ADEPOT : alayout -> amem -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 id) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (adepot_W L (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ ADEPOT L m'.

Definition depot_put_stmt (ADEPOT : alayout -> amem -> Prop) : Prop :=
  forall (L : alayout) RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo T sz pc : Z) (tb : list word) (tr : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ADEPOT_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 sz ->
  (* [comment removed for export] *)
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m T tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) ->
  bv_unsigned sp <= T -> T + 2040 <= 2^47 ->
  ADEPOT L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  rng RNG 0x10000 0x6b7000 (* [comment removed for export] *) -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG T 2040 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  evtF asegs RNG (depot_put_post L ADEPOT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADEPOT_PUT) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition depot_frame_stmt (ADEPOT : alayout -> amem -> Prop) : Prop :=
  forall L m m' (W : list (Z * Z)),
    ADEPOT L m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv ->
                         ~ (ADEPOT_LO <= a < ADEPOT_HI) /\ ~ (al_nodes L <= a < al_nodes L + 1048576)
                         /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
    ADEPOT L m'.

Record ADepotIface := mkADepotIface {
  ADEPOT : alayout -> amem -> Prop;
  adi_put : depot_put_stmt ADEPOT;
  adi_frame : depot_frame_stmt ADEPOT
}.
End CANSEC1.
