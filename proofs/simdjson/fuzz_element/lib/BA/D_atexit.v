(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import X_aexdefs.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Asan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Import ListNotations.
Open Scope Z_scope.

Local Ltac fold_sx32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  | |- context [sxb (Z_to_bv 8 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sxb (Z_to_bv 8 z))) in
        replace (sxb (Z_to_bv 8 z)) with (Z_to_bv 64 v : word) by (vm_compute; reflexivity)
  end.
Local Ltac xstep := lstep; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Local Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).

Definition atexitA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (func : Z) (p1 p2 : list byte) (a0v : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x6c7eb8, 0x6c7ee8); (0x6c7fd8, 0x6c7fe8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x6c7eb8 (aex_tbl 2 p1 p2 (Z_to_bv 64 X_CALL))
    /\ rw_cells asegs m' 0x6c7fd8 [C8 a0v; C8 (Z_to_bv 64 func)].

Lemma atexitA_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo func : Z) (p1 p2 : list byte) (f1 a0v a1v : word) (cdt thr sec : byte) (tm1 : word),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m 0x6c80f8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  rw_cells asegs m 0x6c7eb8 (aex_tbl 1 p1 p2 f1) ->
  rw_cells asegs m 0x6c7fd8 [C8 a0v; C8 a1v] ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 func -> (0 <= func < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x6ca000 <= lo)%Z ->
  evt asegs (atexitA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo func p1 p2 a0v m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14b384) fc None m (seg_rom asegs)).
Proof.
  intros until tm1. intros ST LCH TBL TA0 MI -> Hf LO LOLO. aex_lits.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6c7eb8, 0x6c7eb8 + 48); (0x6c7fd8, 0x6c7fd8 + 16)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x14b3fc%Z.
  xsteps_to 0x14b420%Z.
  xsteps_to 0x14b42c%Z.
  xsteps_to 0x14b444%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  apply evt_done. unfold atexitA_post. aex_lits. sys_finish.
Time Qed.
