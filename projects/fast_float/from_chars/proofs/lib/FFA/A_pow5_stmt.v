(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_cap A_rt_stmt A_long_mul_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Notation POW5_ENTRY := 0x96778%Z.
Notation A_SMALL_POW5 := 0x25368%Z.    (* [comment removed for export] *)
Notation A_POW5_27 := 0x10370%Z.       (* [comment removed for export] *)

Definition pow5_entry : Z := POW5_ENTRY.
Definition pow5_need : Z := 2592.

Definition pow5_W (sp A FS : Z) : list ivl :=
  [(sp - 2592, sp); (A, A + 498);
   (FS + FK5_HINT, FS + FK5_HINT + 8); (FS + FK5_FLAGS, FS + FK5_FLAGS + FK5_NFLAGS);
   (FS + FK5_LO, FS + FK5_HI); (ASAN_B + FS / 8 + FK5_SLO, ASAN_B + FS / 8 + FK5_SHI)]%Z.

Definition pow5_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A e : Z) (ws : list word) (len : Z) (v : rt_vals)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z) (h5' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ASEGS)
    /\ munch (pow5_W (bv_unsigned sp) A (rt_FS v)) m m'
    /\ wmono ASEGS m m'
    /\ stk ASEGS m' (bv_unsigned sp - 2592) (bv_unsigned sp)
    /\ u64arr ASEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells ASEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (0 <= len' <= 62)%Z
    /\ (len' <= len + pow5_growth e)%Z
    /\ bnorm ws' (Z.to_nat len')
    /\ pristine m' IMG_LO ROD_HI
    /\ RT m' v
    /\ fk5_inv m' (rt_FS v) h5'.

Definition pow5_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z) (v : rt_vals) (h5 : word),
    let FS := rt_FS v in
    stk ASEGS m (bv_unsigned sp - 2592) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (IMG_END <= bv_unsigned sp - 2592)%Z ->
    pristine m IMG_LO ROD_HI ->
    (* [comment removed for export] *)
    u64arr ASEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells ASEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    bnorm ws (Z.to_nat len) ->
    (* [comment removed for export] *)
    (bv_unsigned a1 < 2 ^ 31)%Z ->
    (* [comment removed for export] *)
    (len + pow5_growth (bv_unsigned a1) <= LM_T)%Z ->        (* [comment removed for export] *)
    (* [comment removed for export] *)
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 2592 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (* [comment removed for export] *)
    tp = Z_to_bv 64 TPV ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v ->
    fk5_inv m FS h5 ->
    (* [comment removed for export] *)
    (KHI <= bv_unsigned sp - 2592)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z -> (bv_unsigned a0 + 504 <= KTOP)%Z ->
    (FS + FSSIZE <= bv_unsigned sp - 2592)%Z ->
    (FS + 4231168 <= bv_unsigned a0 /\ bv_unsigned a0 + 632 <= FS + FK5_LO)%Z ->
    rt_disj v (bv_unsigned sp - 2592) (bv_unsigned sp) ->
    rt_disj v (bv_unsigned a0) (bv_unsigned a0 + 498) ->
    rt_disj v FS (FS + FSSIZE) ->
    (* [comment removed for export] *)
    shz ASEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    shz ASEGS m POW5TAB_SH POW5TAB_SHN ->
    rdbl ASEGS m (ASAN_B + bv_unsigned a0 / 8 - 8) 79 ->
    rdbl ASEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N ->
    RTX v fc ->   (* [comment removed for export] *)
    evt ASEGS (pow5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) (bv_unsigned a1) ws len v m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 POW5_ENTRY) fc None m (seg_rom ASEGS)).
