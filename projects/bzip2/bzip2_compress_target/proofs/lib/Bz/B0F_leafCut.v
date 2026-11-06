(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac AsanKit AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzDBlock CmpMem.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

(* [comment removed for export] *)
Notation B0_indexIntoF_pc := 0x83de0%Z (only parsing).
Notation B0_makeMaps_d_pc := 0xb5bd8%Z (only parsing).
Notation B0_hbCreate_pc := 0xa8eac%Z (only parsing).
Definition B0_FR_indexIntoF : Z := 16.
Definition B0_FR_makeMaps_d : Z := 16.
Definition B0_FR_hbCreate : Z := 48.

Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition indexIntoF_apostF (fr : Z) (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (indx : Z) (CF : Z) (ws : list word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (index_into_f indx (sv32 ws))) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - fr, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' lo (bv_unsigned sp)
    /\ u32arr segs m' CF ws.

Definition indexIntoF_aspecF (I : acimg) (entry fr : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (CF lo : Z) (ws : list word),
  let segs := aci_segs I in
  let W := [(bv_unsigned sp - fr, bv_unsigned sp)] in
  a1 = Z_to_bv 64 CF ->
  u32arr segs m CF ws -> length ws = 257%nat -> mem_inv segs m ->
  stk segs m lo (bv_unsigned sp) -> lo + fr <= bv_unsigned sp ->
  bv_unsigned sp <= CF \/ CF + 1028 <= bv_unsigned sp - fr ->
  CF mod 4 = 0 ->                                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  aconsts I m -> aci_hi I <= lo -> aci_hi I <= CF ->
  shzW segs W m CF (CF + 1028) ->
  evt segs (indexIntoF_apostF fr segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_signed a0) CF ws lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition makeMaps_d_apostF (fr : Z) (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (c0 c1 c2 k3 k4 k5 k6 : word) (inUse s2u : BzArr.zarr) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(S + 3192, S + 3196); (S + 3468, S + 3724); (bv_unsigned sp - fr, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' lo (bv_unsigned sp)
    /\ rw_cells segs m' (S + 3152) [C8 c0; C8 c1; C8 c2; C4 k3; C4 k4; C4 k5; C4 k6; C4 (Z_to_bv 64 (snd (BzDBlock.mkmaps 256 0 inUse s2u 0)))]
    /\ u8arr segs m' (S + 3196) (CmpMem.zb8 inUse 256)
    /\ u8arr segs m' (S + 3468) (CmpMem.zb8 (fst (BzDBlock.mkmaps 256 0 inUse s2u 0)) 256).

Definition makeMaps_d_aspecF (I : acimg) (entry fr : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (DS lo : Z) (c0 c1 c2 k3 k4 k5 k6 n0 : word) (inUse s2u : BzArr.zarr),
  let segs := aci_segs I in
  let W := [(DS + 3192, DS + 3196); (DS + 3468, DS + 3724); (bv_unsigned sp - fr, bv_unsigned sp)] in
  a0 = Z_to_bv 64 DS ->
  rw_cells segs m (DS + 3152) [C8 c0; C8 c1; C8 c2; C4 k3; C4 k4; C4 k5; C4 k6; C4 n0] ->
  u8arr segs m (DS + 3196) (CmpMem.zb8 inUse 256) -> u8arr segs m (DS + 3468) (CmpMem.zb8 s2u 256) ->
  (forall i, 0 <= i < 256 -> 0 <= BzArr.zget inUse i < 256) ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + fr <= bv_unsigned sp ->
  DS mod 8 = 0 -> 0 < DS -> DS + 64144 <= 18446744073709551616 ->
  bv_unsigned sp <= DS \/ DS + 64144 <= bv_unsigned sp - fr ->
  (* [comment removed for export] *)
  aconsts I m -> aci_hi I <= lo -> aci_hi I <= DS ->
  shzW segs W m DS (DS + 64144) ->
  evt segs (makeMaps_d_apostF fr segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS c0 c1 c2 k3 k4 k5 k6 inUse s2u lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hbCreate_W (fr : Z) (sp : word) (DS t : Z) : list (Z * Z) :=
  [(DS + 45436 + 1032 * t, DS + 45436 + 1032 * t + 1032); (DS + 51628 + 1032 * t, DS + 51628 + 1032 * t + 1032);
   (DS + 57820 + 1032 * t, DS + 57820 + 1032 * t + 1032); (bv_unsigned sp - fr, bv_unsigned sp)].

Definition hbCreateDecodeTables_apostF (fr : Z) (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' lws' bws' pws',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch (hbCreate_W fr sp DS t) m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ u32arr segs m' (DS + 45436 + 1032 * t) lws' /\ length lws' = 258%nat
    /\ u32arr segs m' (DS + 51628 + 1032 * t) bws' /\ length bws' = 258%nat
    /\ u32arr segs m' (DS + 57820 + 1032 * t) pws' /\ length pws' = 258%nat
    /\ u8arr segs m' (DS + 43888 + 258 * t) lbs
    /\ stk segs m' lo (bv_unsigned sp)
    /\ (let '(limit, base, perm) := hb_create (sv32 lws) (sv32 bws) (sv32 pws) (uv8 lbs) minLen maxLen alpha in
        ag32s lws' limit 258 /\ ag32s bws' base 258 /\ ag32s pws' perm 258).

Definition hbCreateDecodeTables_aspecF (I : acimg) (entry fr : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo : Z),
  let segs := aci_segs I in
  let W := hbCreate_W fr sp DS t in
  u32arr segs m (DS + 45436 + 1032 * t) lws -> length lws = 258%nat ->
  u32arr segs m (DS + 51628 + 1032 * t) bws -> length bws = 258%nat ->
  u32arr segs m (DS + 57820 + 1032 * t) pws -> length pws = 258%nat ->
  u8arr segs m (DS + 43888 + 258 * t) lbs -> length lbs = 258%nat ->
  0 < DS /\ DS mod 16 = 0 /\ 0 <= t < 6 ->
  DS + 64144 <= 18446744073709551616 ->
  bv_unsigned sp <= DS \/ DS + 64144 <= bv_unsigned sp - fr ->
  stk segs m lo (bv_unsigned sp) -> lo + fr <= bv_unsigned sp -> mem_inv segs m ->
  1 <= alpha <= 258 -> 1 <= minLen /\ minLen <= maxLen <= 20 ->
  (forall j, 0 <= j < alpha -> minLen <= uv8 lbs j <= maxLen) ->
  a0 = Z_to_bv 64 (DS + 45436 + 1032 * t) -> a1 = Z_to_bv 64 (DS + 51628 + 1032 * t) ->
  a2 = Z_to_bv 64 (DS + 57820 + 1032 * t) -> a3 = Z_to_bv 64 (DS + 43888 + 258 * t) ->
  a4 = Z_to_bv 64 minLen -> a5 = Z_to_bv 64 maxLen -> a6 = Z_to_bv 64 alpha ->
  (* [comment removed for export] *)
  aconsts I m -> aci_hi I <= lo -> aci_hi I <= DS ->
  shzW segs W m DS (DS + 64144) ->
  evt segs (hbCreateDecodeTables_apostF fr segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS t lws bws pws lbs minLen maxLen alpha lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

End ACeilS1.
