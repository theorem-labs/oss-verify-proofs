(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes Decode InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase F_m2s_b.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AKit FsKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_g | solve_load_image ].
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition ASF5_ENTRY : Z := 0x50a40.

(* [comment removed for export] *)
Definition sf5_W (sp flag F : Z) : list (Z * Z) := [(sp - 16, sp); (flag, flag + 1); (shad F, shad F + 256)].

Definition sf5_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo F flag : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sf5_W (bv_unsigned sp) flag F) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' (shad F) (repeat (C8 (Z_to_bv 64 0xf5f5f5f5f5f5f5f5)) 32).

Lemma stack_free5_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo F flag : Z) (fb : byte) (junk : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> ATOP <= lo ->
  a0 = Z_to_bv 64 F ->
  rt_got m -> rt_shbase m -> rt_layout m ->
  (F + 1 <= KLOW \/ (KHIGH <= F /\ F + 1 <= KEND)) ->
  0 <= F -> F + 2048 <= ATOP -> 0x665000 <= flag -> flag + 1 <= ATOP ->
  (flag + 1 <= F + 2040 \/ F + 2048 <= flag) ->
  (flag + 1 <= shad F \/ shad F + 256 <= flag) ->
  (F + 2048 <= shad F \/ shad F + 256 <= F + 2040) ->
  shad F + 256 <= ATOP ->
  rw_cells asegs m (F + 2040) [C8 (Z_to_bv 64 flag)] ->
  rw_cells asegs m flag [C1 fb] ->
  rw_cells asegs m (shad F) [CB 256 junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (F + 2040) 8 -> rng RNG flag 1 -> rng RNG (shad F) 256 ->
  evtF asegs RNG (sf5_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo F flag m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASF5_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until junk.
  intros MI ST LO CEIL A0 GOT SHB LAY APP F0 FT FL0 FLT D1 D2 D3 SHT C2040 CFL CSH RIMG RSTK R2040 RFL RSH.
  subst a0.
  pose proof (munch_refl (sf5_W (bv_unsigned sp) flag F) m) as MU. unfold sf5_W in MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof atop_range as ATR.
  assert (SHF0 : 0x7fff8000 <= shad F) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  unfold ASF5_ENTRY.
  carve_frame 16%nat ST.
  do 3 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. call m2sb_spec; first [ eassumption | (rewrite unsigned_lit by lia; exact APP) | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep.                             (* [comment removed for export] *)
  do 32 zstep.                              (* [comment removed for export] *)
  do 4 zstep.                               (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp).
  finish.
Qed.
End CANSEC1.
