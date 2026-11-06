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
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt.

Module A_ctlz_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_app2.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Notation CTLZ_ENTRY := 0x97bc0%Z.
Notation IMG_LO := 0x10000%Z.          (* [comment removed for export] *)
Notation ROD_HI := 0x3e000%Z.
Notation RELRO_LO := 0xd9000%Z.       (* [comment removed for export] *)
Notation RELRO_HI := 0xde000%Z.
Notation BCELL := 937400%Z.           (* [comment removed for export] *)
Notation IMG_END := 0x63a000%Z.        (* [comment removed for export] *)

Definition ctlz_entry : Z := CTLZ_ENTRY.
Definition ctlz_FR : Z := 16.

Definition ctlz_post
    (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (z : Z) (a1 a2 a3 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 z) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ASEGS)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m'
    /\ wmono ASEGS m m'
    /\ (0 <= z < 256)%Z
    /\ stk ASEGS m' (bv_unsigned sp - 16) (bv_unsigned sp).

Definition ctlz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    u64arr ASEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells ASEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> bnorm ws (Z.to_nat len) ->
    stk ASEGS m (bv_unsigned sp - 16) (bv_unsigned sp) ->
    pristine m IMG_LO ROD_HI ->
    (IMG_END <= bv_unsigned sp - 16)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (* [comment removed for export] *)
    pristine m RELRO_LO RELRO_HI ->
    ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] ->
    (KHI <= bv_unsigned sp - 16)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z -> (bv_unsigned a0 + 504 <= KTOP)%Z ->
    shz ASEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    evt ASEGS (ctlz_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 CTLZ_ENTRY) fc None m (seg_rom ASEGS)).
End A_ctlz_stmt.

Module A_hi64_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_app2.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Notation HI64_ENTRY := 0x96430%Z.
Notation IMG_LO := 0x10000%Z.          (* [comment removed for export] *)
Notation ROD_HI := 0x3e000%Z.
Notation RELRO_LO := 0xd9000%Z.       (* [comment removed for export] *)
Notation RELRO_HI := 0xde000%Z.
Notation BCELL := 937400%Z.           (* [comment removed for export] *)
Notation IMG_END := 0x63a000%Z.        (* [comment removed for export] *)

Definition hi64_entry : Z := HI64_ENTRY.
Definition hi64_FR : Z := 16.

Definition hi64_post
    (ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t : Z) (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ASEGS)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 1)]%Z m m'
    /\ wmono ASEGS m m'
    /\ (0 <= t <= 1)%Z
    /\ rw_cells ASEGS m' (bv_unsigned a1) [C1 (Z_to_bv 8 t)]
    /\ stk ASEGS m' (bv_unsigned sp - 16) (bv_unsigned sp).

Definition hi64_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z) (tb : byte),
    u64arr ASEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells ASEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> bnorm ws (Z.to_nat len) ->
    rw_cells ASEGS m (bv_unsigned a1) [C1 tb] ->
    stk ASEGS m (bv_unsigned sp - 16) (bv_unsigned sp) ->
    pristine m IMG_LO ROD_HI ->
    (IMG_END <= bv_unsigned sp - 16)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 1 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a1 + 1 <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= bv_unsigned a1)%Z ->
    (* [comment removed for export] *)
    pristine m RELRO_LO RELRO_HI ->
    ro_cells ASEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] ->
    (KHI <= bv_unsigned sp - 16)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z -> (bv_unsigned a0 + 504 <= KTOP)%Z ->
    (KHI <= bv_unsigned a1)%Z -> (bv_unsigned a1 + 1 <= KTOP)%Z ->
    shz ASEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    shz ASEGS m (ASAN_B + bv_unsigned a1 / 8) 1 ->
    evt ASEGS (hi64_post ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 HI64_ENTRY) fc None m (seg_rom ASEGS)).
End A_hi64_stmt.

Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Notation LMUL_ENTRY := 0x96b2c%Z.
Notation IMG_LO := 0x10000%Z.          (* [comment removed for export] *)
Notation ROD_HI := 0x3e000%Z.
Notation A_LARGE_POW5 := 0x25340%Z.    (* [comment removed for export] *)
Notation POW5TAB_SH := 2147469928%Z.   (* [comment removed for export] *)
Notation POW5TAB_SHN := 32%Z.
Notation FSSIZE := 11571200%Z.         (* [comment removed for export] *)
(* [comment removed for export] *)
Notation LM_T := 61%Z.

Definition long_mul_entry : Z := LMUL_ENTRY.
Definition long_mul_need : Z := 2528.
Definition A_LARGE_POW5_ADDR : Z := A_LARGE_POW5.

(* [comment removed for export] *)
Notation FK5_HINT := 40%Z.
Notation FK5_FLAGS := 35840%Z.      Notation FK5_NFLAGS := 512%Z.
Notation FK5_LO := 5279744%Z.       Notation FK5_HI := 6328320%Z.
Notation FK5_SLO := 659968%Z.       Notation FK5_SHI := 791040%Z.
(* [comment removed for export] *)
Notation FK_SH_LO := 397824%Z.      Notation FK_SH_N := 393216%Z.

Definition fk5_inv (m : word -> option byte) (FS : Z) (h5 : word) : Prop :=
     fs_cells_ok FS m
  /\ rw_cells ASEGS m (FS + FK5_HINT) [C8 h5]
  /\ u8arr ASEGS m (FS + FK5_FLAGS) (zeros 512)
  /\ stk ASEGS m (FS + FK5_LO) (FS + FK5_HI)
  /\ stk ASEGS m (ASAN_B + FS / 8 + FK5_SLO) (ASAN_B + FS / 8 + FK5_SHI).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RT_IMG_IVS : list (Z * Z) :=
  [ (0x10000, 0x2e000); (0xe4db8, 12); (0xe4620, 8); (0xe5a98, 2); (0xe5aa0, 24); (0x174858, 4); (0x176971, 1); (0x617f28, 8);
    (0x617f78, 56); (0x639328, 8); (0xd9000, 0x5000); (0xde9d0, 0x188) ]%Z.
Definition RTX (v : rt_vals) (fc : bv 32) : Prop :=
  (6529024 <= rt_ctx v /\ 4096 <= rt_thr v /\ 4096 <= rt_blk v /\ rt_ctx v mod 8 = 0 /\ rt_thr v mod 8 = 0 /\ rt_blk v mod 8 = 0)%Z
  (* [comment removed for export] *)
  /\ (Z.land (Z.shiftr (bv_unsigned fc) 5) 7 = 0)%Z
  (* [comment removed for export] *)
  /\ (rt_ctx v + 160 <= rt_thr v \/ rt_thr v + 80 <= rt_ctx v)%Z /\ (rt_ctx v + 160 <= rt_blk v \/ rt_blk v + 32 <= rt_ctx v)%Z
  /\ (rt_thr v + 80 <= rt_blk v \/ rt_blk v + 32 <= rt_thr v)%Z
  (* [comment removed for export] *)
  /\ (forall b n, In (b, n) RT_IMG_IVS -> b + n <= rt_thr v \/ rt_thr v + 80 <= b)%Z
  /\ (forall b n, In (b, n) RT_IMG_IVS -> b + n <= rt_blk v \/ rt_blk v + 32 <= b)%Z.

Definition long_mul_W (sp A FS : Z) : list ivl :=
  [(sp - 2528, sp); (A, A + 498);
   (FS + FK5_HINT, FS + FK5_HINT + 8); (FS + FK5_FLAGS, FS + FK5_FLAGS + FK5_NFLAGS);
   (FS + FK5_LO, FS + FK5_HI); (ASAN_B + FS / 8 + FK5_SLO, ASAN_B + FS / 8 + FK5_SHI)]%Z.

Definition long_mul_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (ws : list word) (len : Z) (v : rt_vals)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z) (h5' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ASEGS)
    /\ munch (long_mul_W (bv_unsigned sp) A (rt_FS v)) m m'
    /\ wmono ASEGS m m'
    /\ stk ASEGS m' (bv_unsigned sp - 2528) (bv_unsigned sp)
    /\ u64arr ASEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells ASEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (0 <= len' <= 62)%Z
    /\ (len' <= len + 6)%Z
    /\ bnorm ws' (Z.to_nat len')
    /\ pristine m' IMG_LO ROD_HI
    /\ RT m' v
    /\ fk5_inv m' (rt_FS v) h5'.

Definition long_mul_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z) (v : rt_vals) (h5 : word),
    let FS := rt_FS v in
    stk ASEGS m (bv_unsigned sp - 2528) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (IMG_END <= bv_unsigned sp - 2528)%Z ->
    pristine m IMG_LO ROD_HI ->
    u64arr ASEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells ASEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    bnorm ws (Z.to_nat len) ->
    a1 = Z_to_bv 64 A_LARGE_POW5 -> a2 = Z_to_bv 64 5 ->
    (len + 5 <= LM_T)%Z ->                     (* [comment removed for export] *)
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 2528 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (* [comment removed for export] *)
    tp = Z_to_bv 64 TPV ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v ->
    fk5_inv m FS h5 ->
    (* [comment removed for export] *)
    (KHI <= bv_unsigned sp - 2528)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z -> (bv_unsigned a0 + 504 <= KTOP)%Z ->
    (FS + FSSIZE <= bv_unsigned sp - 2528)%Z ->
    (FS + 4231168 <= bv_unsigned a0 /\ bv_unsigned a0 + 632 <= FS + FK5_LO)%Z ->
    rt_disj v (bv_unsigned sp - 2528) (bv_unsigned sp) ->
    rt_disj v (bv_unsigned a0) (bv_unsigned a0 + 498) ->
    rt_disj v FS (FS + FSSIZE) ->
    (* [comment removed for export] *)
    shz ASEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    shz ASEGS m POW5TAB_SH POW5TAB_SHN ->
    rdbl ASEGS m (ASAN_B + bv_unsigned a0 / 8 - 8) 79 ->
    rdbl ASEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N ->
    RTX v fc -> (bv_unsigned ra mod 2 = 0)%Z ->
    evt ASEGS (long_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) ws len v m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LMUL_ENTRY) fc None m (seg_rom ASEGS)).
