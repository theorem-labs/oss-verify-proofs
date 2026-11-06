(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt.

Module B_fakestack.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

Notation FSSIZE := 11571200%Z.        (* [comment removed for export] *)
Notation FK4_HINT := 32%Z.
Notation FK4_FLAGS := 34816%Z.      Notation FK4_NFLAGS := 1024%Z.
Notation FK4_LO := 4231168%Z.       Notation FK4_HI := 5279744%Z.      (* [comment removed for export] *)
Notation FK4_SLO := 528896%Z.       Notation FK4_SHI := 659968%Z.      (* [comment removed for export] *)
(* [comment removed for export] *)
Notation FK_SH_LO := 397824%Z.      Notation FK_SH_N := 393216%Z.

Definition fk4_inv (m : word -> option byte) (FS : Z) (h4 : word) : Prop :=
     fs_cells_ok FS m
  /\ rw_cells BSEGS m (FS + FK4_HINT) [C8 h4]
  /\ u8arr BSEGS m (FS + FK4_FLAGS) (zeros 1024)
  /\ stk BSEGS m (FS + FK4_LO) (FS + FK4_HI)
  /\ stk BSEGS m (ASAN_B + FS / 8 + FK4_SLO) (ASAN_B + FS / 8 + FK4_SHI).
End B_fakestack.

From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt.B_fakestack OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

Notation NDC_D_ENTRY := 0x96254%Z.
Notation NDC_NEED := 2768%Z.          (* [comment removed for export] *)

Definition negative_digit_comp_d_entry : Z := NDC_D_ENTRY.
Definition negative_digit_comp_d_need  : Z := NDC_NEED.

(* [comment removed for export] *)
Definition fk4_nest (m : word -> option byte) (FS : Z) (h4 : word) (pos0 : Z) : Prop :=
     fs_cells_ok FS m
  /\ rw_cells BSEGS m (FS + FK4_HINT) [C8 h4]
  /\ u8arr BSEGS m (FS + FK4_FLAGS) (upd (zeros 1024) (Z.to_nat pos0) (Z_to_bv 8 1))
  /\ stk BSEGS m (FS + FK4_LO) (FS + FK4_LO + pos0 * 1024)
  /\ stk BSEGS m (FS + FK4_LO + pos0 * 1024 + 1024) (FS + FK4_HI)
  /\ stk BSEGS m (ASAN_B + FS / 8 + FK4_SLO) (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128)
  /\ stk BSEGS m (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128 + 128) (ASAN_B + FS / 8 + FK4_SHI).

(* [comment removed for export] *)
Definition negative_digit_comp_d_W (sp A FS pos0 : Z) : list ivl :=
  [(sp - NDC_NEED, sp); (A, A + 498);
   (FS + 32, FS + 48);
   (FS + FK4_FLAGS, FS + FK4_FLAGS + pos0); (FS + FK4_FLAGS + pos0 + 1, FS + FK5_FLAGS + FK5_NFLAGS);
   (FS + FK4_LO, FS + FK4_LO + pos0 * 1024); (FS + FK4_LO + pos0 * 1024 + 1024, FS + FK5_HI);
   (ASAN_B + FS / 8 + FK4_SLO, ASAN_B + FS / 8 + FK4_SLO + pos0 * 128);
   (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128 + 128, ASAN_B + FS / 8 + FK5_SHI)]%Z.

Definition negative_digit_comp_d_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (v : rt_vals) (pos0 : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z) (h4' h5' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (negative_digit_comp_d_W (bv_unsigned sp) A (rt_FS v) pos0) m m'
    /\ wmono BSEGS m m'
    /\ stk BSEGS m' (bv_unsigned sp - NDC_NEED) (bv_unsigned sp)
    /\ u64arr BSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells BSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (0 <= len' <= 62)%Z
    /\ pristine m' IMG_LO ROD_HI
    /\ RT m' v
    /\ fk4_nest m' (rt_FS v) h4' pos0
    /\ fk5_inv m' (rt_FS v) h5'.

Definition negative_digit_comp_d_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z) (p2 e : Z) (v : rt_vals) (h4 h5 : word) (pos0 : Z),
    let FS := rt_FS v in
    let F0 := (FS + FK4_LO + pos0 * 1024)%Z in
    stk BSEGS m (bv_unsigned sp - NDC_NEED) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (IMG_END <= bv_unsigned sp - NDC_NEED)%Z ->
    pristine m IMG_LO ROD_HI ->
    (* [comment removed for export] *)
    u64arr BSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells BSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    bnorm ws (Z.to_nat len) ->
    (* [comment removed for export] *)
    (bv_unsigned a2 = p2 mod 2 ^ 32)%Z -> (- 2 ^ 14 <= p2 <= 2 ^ 14)%Z ->
    (* [comment removed for export] *)
    a3 = Z_to_bv 64 e -> (-1300 <= e <= -1)%Z ->
    (* [comment removed for export] *)
    tp = Z_to_bv 64 TPV ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v ->
    fk4_nest m FS h4 pos0 -> (0 <= pos0 < 1024)%Z -> (bv_unsigned h4 mod 1024 <> pos0)%Z ->
    fk5_inv m FS h5 ->
    (* [comment removed for export] *)
    (KHI <= bv_unsigned sp - NDC_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (FS + FSSIZE <= bv_unsigned sp - NDC_NEED)%Z ->
    (F0 + 32 <= bv_unsigned a0)%Z -> (bv_unsigned a0 + 504 <= F0 + 1024)%Z ->
    rt_disj v (bv_unsigned sp - NDC_NEED) (bv_unsigned sp) ->
    rt_disj v FS (FS + FSSIZE) ->
    (* [comment removed for export] *)
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    shz BSEGS m POW5TAB_SH POW5TAB_SHN ->
    rdbl BSEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N ->
    RTX v fc ->   (* [comment removed for export] *)
    (* [comment removed for export] *)
    shz BSEGS m (ASAN_B + (bv_unsigned sp - NDC_NEED) / 8) 346 ->
    evt BSEGS (negative_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) v pos0 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 NDC_D_ENTRY) fc None m (seg_rom BSEGS)).
