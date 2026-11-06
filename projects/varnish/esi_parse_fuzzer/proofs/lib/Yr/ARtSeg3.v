(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ACells ARtStmts ARtSscs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition enqueue_newfull_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c C sto mch size nb fb lb qb nx bsz cnt maxc sb lo : Z) (ks : list word) (kw statv : word) (bj0 bj1 bj2 bj3 : word),
    let b := sb + 24 * 2^32 + 16 * bv_unsigned kw in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    a0 = wz c -> a1 = wz C -> a2 = wz sto -> a3 = wz mch -> a4 = wz size ->
    aobj c 32 -> c + 32 <= alloc_ceiling -> aobj C 3888 -> C + 3888 <= alloc_ceiling -> C mod 16 = 0 ->
    kHighMemBeg <= lb -> lb + 8192 <= alloc_ceiling ->
    (c + 32 <= C + 1920 \/ C + 2584 <= c) -> (c + 32 <= lb \/ lb + 24 <= c) -> (lb + 24 <= C + 1920 \/ C + 2584 <= lb) ->
    0 <= sb -> sb + 2^37 <= 2^47 -> kHighMemBeg <= b -> b + 8192 <= alloc_ceiling ->
    (b + 32 <= c \/ c + 32 <= b) -> (b + 32 <= C + 1920 \/ C + 2584 <= b) -> (b + 32 <= lb \/ lb + 24 <= b) ->
    nb <> 0 -> 0 <= nb < 2^63 ->
    1 <= cnt <= 16 -> length ks = 16%nat -> nth_error ks (Z.to_nat (cnt - 1)) = Some kw -> bv_unsigned kw < 2^32 ->
    0 <= size < 2^64 -> 0 <= mch < 2^64 ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)] ->                                 (* [comment removed for export] *)
    rw_cells rsegs m (C + 1920) [C4 (wz cnt); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    rw_cells rsegs m b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (c, c + 32); (lb, lb + 8); (C + 1920, C + 1924); (C + 2576, C + 2584); (b, b + 32)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ rw_cells rsegs m' c [C8 (wz (nb + 1)); C8 (wz fb); C8 (wz b); C8 (wz (qb + (size + 8192)))]
                 /\ rw_cells rsegs m' lb [C8 (wz b); C8 (wz bsz); C8 (wz 1021)]
                 /\ rw_cells rsegs m' (C + 1920) [C4 (wz (cnt - 1)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)]
                 /\ rw_cells rsegs m' (C + 2576) [C8 statv']
                 /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (size + 8192)); C8 (wz 1); C8 (wz mch)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz enqueue_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qdrain_stack : Z := 48.
Definition qdrain0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (q c cache sto rl hi gf gl gqb qmax nb fb lb qb lo : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
    a0 = wz q -> a1 = wz c -> a2 = wz cache -> a3 = wz sto ->
    0x10000 <= q -> q + 192 <= 0x60a000 -> q mod 8 = 0 -> aobj c 32 -> c + 32 <= alloc_ceiling ->
    0 <= rl < 256 -> 0 <= hi < 2^15 -> 0 <= gqb -> 0 <= qb -> gqb + qb <= qmax -> qmax < 2^64 ->
    nb <> 0 -> 0 <= nb < 2^64 -> 0 <= fb < 2^64 -> 0 <= lb < 2^64 ->
    rw_cells rsegs m (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)] ->
    ro_cells rsegs m (q + 64) [C8 (wz qmax)] ->
    rw_cells rsegs m (q + 160) [C8 (wz 0); C8 (wz gf); C8 (wz gl); C8 (wz gqb)] ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (q + 152, q + 156); (q + 160, q + 192); (c, c + 32)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ rw_cells rsegs m' (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)]
                 /\ rw_cells rsegs m' (q + 160) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz (gqb + qb))]
                 /\ rw_cells rsegs m' c [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz qdrain_entry) fc None m (seg_rom rsegs)).
Definition qdrainA_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (q c cache sto rl hi gn gf gl gqb qmax nb fb lb qb lo : Z) (glnx : word),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
    a0 = wz q -> a1 = wz c -> a2 = wz cache -> a3 = wz sto ->
    0x10000 <= q -> q + 192 <= 0x60a000 -> q mod 8 = 0 -> aobj c 32 -> c + 32 <= alloc_ceiling ->
    kHighMemBeg <= gl -> gl + 24 <= alloc_ceiling -> (c + 32 <= gl \/ gl + 8 <= c) ->
    0 <= rl < 256 -> 0 <= hi < 2^15 -> 0 <= gqb -> 0 <= qb -> gqb + qb <= qmax -> qmax < 2^64 ->
    nb <> 0 -> 0 <= nb < 2^64 -> gn <> 0 -> 0 <= gn < 2^64 -> 0 <= fb < 2^64 -> 0 <= lb < 2^64 ->
    rw_cells rsegs m (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)] ->
    ro_cells rsegs m (q + 64) [C8 (wz qmax)] ->
    rw_cells rsegs m (q + 160) [C8 (wz gn); C8 (wz gf); C8 (wz gl); C8 (wz gqb)] ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m gl [C8 glnx] ->                                                   (* [comment removed for export] *)
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (q + 152, q + 156); (q + 160, q + 192); (c, c + 32); (gl, gl + 8)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ rw_cells rsegs m' (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)]
                 /\ rw_cells rsegs m' (q + 160) [C8 (wz (gn + nb)); C8 (wz gf); C8 (wz lb); C8 (wz (gqb + qb))]
                 /\ rw_cells rsegs m' c [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
                 /\ rw_cells rsegs m' gl [C8 (wz fb)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz qdrain_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition initcache_blk_entry : Z := 0x3c0c8.
Definition initcache_blk_exit : Z := 0x3c164.
Definition initcache_blk_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (C : Z) (cnt mc0 cs0 : Z -> Z) (ks : Z -> list word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> aobj C 3888 -> C + 3888 <= alloc_ceiling ->
    (forall i, 1 <= i <= 31 -> 0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (ks i) = 16%nat /\
       rw_cells rsegs m (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (mc0 i)); C8 (wz (cs0 i)); CB 64 (u32s (ks i))]) ->
    (forall (t3' t4' t5' : word) (m' : word -> option byte),
        (forall i, 1 <= i <= 31 ->
           rw_cells rsegs m' (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s (ks i))]) ->
        munch [(C + 80, C + 2560)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        evt rsegs Q (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 (wz C) (wz (C + 2568)) a2 (wz 1024) a4 (wz 16) (wz 15) (wz 1024)
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (wz initcache_blk_exit) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz C) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz initcache_blk_entry) fc None m (seg_rom rsegs)).

End CEIL.
