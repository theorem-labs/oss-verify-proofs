(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AxSymExec3 AsanPlanCore BigContractSrc0.
Import ListNotations. Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition SHL_ENTRY : Z := 0x22894.
Definition SHR_ENTRY : Z := 0x22b98.
Definition RED_ENTRY : Z := 0x215d0.
Definition DV_SCRATCH : Z := 176.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dv_kept_reg (r : reg) : Prop := r <> 0%bv /\ ~ In (ridx r) APC.caller_saved.

(* [comment removed for export] *)
Definition dyn_obj (M : word -> option byte) (o fl len C q : Z) : Prop :=
  u8_at M o fl /\ u64_at M (o + 8) len /\ u64_at M (o + 16) C /\ u64_at M (o + 24) q.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shl2_dyn_src0 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (s o q C r t fb : Z) (n : nat),
    getr R (2%bv : reg) = Z_to_bv 64 s ->
    getr R (3%bv : reg) = Z_to_bv 64 67584 -> getr R (4%bv : reg) = Z_to_bv 64 459832 ->      (* [comment removed for export] *)
    getr R (1%bv : reg) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->   (* [comment removed for export] *)
    getr R (10%bv : reg) = Z_to_bv 64 o ->                 (* [comment removed for export] *)
    getr R (11%bv : reg) = Z_to_bv 64 2 ->                 (* [comment removed for export] *)
    (forall i, 65536 <= i < 131072 -> M (Z_to_bv 64 i) = None) ->   (* [comment removed for export] *)
    (3 <= n <= 300)%nat -> Z.of_nat n + 1 <= C -> 8 <= C <= 264 ->
    dyn_obj M o fb (Z.of_nat n) C q -> 0 <= fb < 256 -> fb mod 4 = 1 ->     (* [comment removed for export] *)
    u64_at M (q + 8 * (Z.of_nat n - 1)) t -> 1 <= t < 2 ^ 64 ->      (* [comment removed for export] *)
    s mod 16 = 0 -> o mod 8 = 0 -> q mod 8 = 0 ->
    2 ^ 20 <= s - DV_SCRATCH -> s <= 2 ^ 47 -> 2 ^ 20 <= o <= 2 ^ 47 -> 4096 <= q -> q + 8 * C <= 2 ^ 47 ->
    writable M (s - DV_SCRATCH) DV_SCRATCH -> writable M o 32 ->
    defined M q (8 * C) -> writable M q (8 * C) ->
    (o + 32 <= s - DV_SCRATCH \/ s <= o) ->
    (q + 8 * C <= s - DV_SCRATCH \/ s <= q) ->
    (q + 8 * C <= o \/ o + 32 <= q) ->
    exists (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (n' : nat) (t' : Z),
      msteps RSEGS (@mkst fx R (Z_to_bv 64 SHL_ENTRY) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 r) M' (seg_rom RSEGS))
      /\ (forall x : reg, dv_kept_reg x -> getr R' x = getr R x)
      /\ getr R' (10%bv : reg) = Z_to_bv 64 o /\ getr R' (1%bv : reg) = Z_to_bv 64 r
      /\ (n' = n \/ n' = S n)
      /\ dyn_obj M' o fb (Z.of_nat n') C q
      /\ u64_at M' (q + 8 * (Z.of_nat n' - 1)) t' /\ 1 <= t' < 2 ^ 64
      /\ (n' = S n -> t' <= 3)                                          (* [comment removed for export] *)
      /\ defined M' q (8 * C)
      /\ (forall x : word, let a := bv_unsigned x in
            ~ (s - DV_SCRATCH <= a < s) -> ~ (o <= a < o + 16) -> ~ (q <= a < q + 8 * C) -> M' x = M x)
      /\ mem_grows M M'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shr2_dyn_src0 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (s o q C r fb : Z) (n : nat),
    getr R (2%bv : reg) = Z_to_bv 64 s ->
    getr R (3%bv : reg) = Z_to_bv 64 67584 -> getr R (4%bv : reg) = Z_to_bv 64 459832 ->
    getr R (1%bv : reg) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
    getr R (10%bv : reg) = Z_to_bv 64 o ->
    getr R (11%bv : reg) = Z_to_bv 64 2 ->
    (forall i, 65536 <= i < 131072 -> M (Z_to_bv 64 i) = None) ->
    (1 <= n <= 300)%nat -> Z.of_nat n <= C -> 8 <= C <= 264 ->
    dyn_obj M o fb (Z.of_nat n) C q -> 0 <= fb < 256 -> fb mod 4 = 1 ->     (* [comment removed for export] *)
    s mod 16 = 0 -> o mod 8 = 0 -> q mod 8 = 0 ->
    2 ^ 20 <= s - DV_SCRATCH -> s <= 2 ^ 47 -> 2 ^ 20 <= o <= 2 ^ 47 -> 4096 <= q -> q + 8 * C <= 2 ^ 47 ->
    writable M (s - DV_SCRATCH) DV_SCRATCH -> writable M o 32 ->
    defined M q (8 * C) -> writable M q (8 * C) ->
    (o + 32 <= s - DV_SCRATCH \/ s <= o) ->
    (q + 8 * C <= s - DV_SCRATCH \/ s <= q) ->
    (q + 8 * C <= o \/ o + 32 <= q) ->
    exists (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (n' : nat) (t' : Z),
      msteps RSEGS (@mkst fx R (Z_to_bv 64 SHR_ENTRY) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 r) M' (seg_rom RSEGS))
      /\ (forall x : reg, dv_kept_reg x -> getr R' x = getr R x)
      /\ getr R' (10%bv : reg) = Z_to_bv 64 o /\ getr R' (1%bv : reg) = Z_to_bv 64 r
      /\ (n' <= n)%nat
      /\ dyn_obj M' o fb (Z.of_nat n') C q
      /\ ((1 <= n')%nat -> u64_at M' (q + 8 * (Z.of_nat n' - 1)) t' /\ 1 <= t' < 2 ^ 64)
      /\ defined M' q (8 * C)
      /\ (forall x : word, let a := bv_unsigned x in
            ~ (s - DV_SCRATCH <= a < s) -> ~ (o <= a < o + 16) -> ~ (q <= a < q + 8 * C) -> M' x = M x)
      /\ mem_grows M M'.


(* [comment removed for export] *)
Definition shr2_top_dyn_src0 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (s o q C r t fb : Z) (n : nat),
    getr R (2%bv : reg) = Z_to_bv 64 s ->
    getr R (3%bv : reg) = Z_to_bv 64 67584 -> getr R (4%bv : reg) = Z_to_bv 64 459832 ->
    getr R (1%bv : reg) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
    getr R (10%bv : reg) = Z_to_bv 64 o ->
    getr R (11%bv : reg) = Z_to_bv 64 2 ->
    (forall i, 65536 <= i < 131072 -> M (Z_to_bv 64 i) = None) ->
    (1 <= n <= 300)%nat -> Z.of_nat n <= C -> 8 <= C <= 264 ->
    dyn_obj M o fb (Z.of_nat n) C q -> 0 <= fb < 256 -> fb mod 4 = 1 ->     (* [comment removed for export] *)
    u64_at M (q + 8 * (Z.of_nat n - 1)) t -> 1 <= t < 2 ^ 64 ->
    s mod 16 = 0 -> o mod 8 = 0 -> q mod 8 = 0 ->
    2 ^ 20 <= s - DV_SCRATCH -> s <= 2 ^ 47 -> 2 ^ 20 <= o <= 2 ^ 47 -> 4096 <= q -> q + 8 * C <= 2 ^ 47 ->
    writable M (s - DV_SCRATCH) DV_SCRATCH -> writable M o 32 ->
    defined M q (8 * C) -> writable M q (8 * C) ->
    (o + 32 <= s - DV_SCRATCH \/ s <= o) ->
    (q + 8 * C <= s - DV_SCRATCH \/ s <= q) ->
    (q + 8 * C <= o \/ o + 32 <= q) ->
    exists (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (n' : nat) (t' : Z),
      msteps RSEGS (@mkst fx R (Z_to_bv 64 SHR_ENTRY) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 r) M' (seg_rom RSEGS))
      /\ (forall x : reg, dv_kept_reg x -> getr R' x = getr R x)
      /\ getr R' (10%bv : reg) = Z_to_bv 64 o /\ getr R' (1%bv : reg) = Z_to_bv 64 r
      /\ (n' = n \/ S n' = n)
      /\ dyn_obj M' o fb (Z.of_nat n') C q
      /\ ((1 <= n')%nat -> u64_at M' (q + 8 * (Z.of_nat n' - 1)) t' /\ 1 <= t' < 2 ^ 64)
      /\ defined M' q (8 * C)
      /\ (forall x : word, let a := bv_unsigned x in
            ~ (s - DV_SCRATCH <= a < s) -> ~ (o <= a < o + 16) -> ~ (q <= a < q + 8 * C) -> M' x = M x)
      /\ mem_grows M M'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition reduce_dyn_src0 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (s o q C r fb : Z) (n : nat),
    getr R (2%bv : reg) = Z_to_bv 64 s ->                  (* [comment removed for export] *)
    getr R (3%bv : reg) = Z_to_bv 64 67584 -> getr R (4%bv : reg) = Z_to_bv 64 459832 ->
    getr R (1%bv : reg) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
    getr R (10%bv : reg) = Z_to_bv 64 o ->
    (forall i, 65536 <= i < 131072 -> M (Z_to_bv 64 i) = None) ->
    (n <= 300)%nat -> Z.of_nat n <= C -> 8 <= C <= 264 ->
    dyn_obj M o fb (Z.of_nat n) C q -> 0 <= fb < 256 -> fb mod 4 = 1 ->     (* [comment removed for export] *)
    s mod 16 = 0 -> o mod 8 = 0 -> q mod 8 = 0 ->
    2 ^ 20 <= s - DV_SCRATCH -> s <= 2 ^ 47 -> 2 ^ 20 <= o <= 2 ^ 47 -> 4096 <= q -> q + 8 * C <= 2 ^ 47 ->
    writable M (s - DV_SCRATCH) DV_SCRATCH -> writable M o 32 ->
    defined M q (8 * C) -> writable M q (8 * C) ->
    (o + 32 <= s - DV_SCRATCH \/ s <= o) ->
    (q + 8 * C <= s - DV_SCRATCH \/ s <= q) ->
    (q + 8 * C <= o \/ o + 32 <= q) ->
    exists (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (n' : nat) (t' : Z),
      msteps RSEGS (@mkst fx R (Z_to_bv 64 RED_ENTRY) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 r) M' (seg_rom RSEGS))
      /\ (forall x : reg, dv_kept_reg x -> getr R' x = getr R x)
      /\ getr R' (10%bv : reg) = Z_to_bv 64 o /\ getr R' (1%bv : reg) = Z_to_bv 64 r
      /\ (n' <= n)%nat
      /\ dyn_obj M' o fb (Z.of_nat n') C q
      /\ ((1 <= n')%nat -> u64_at M' (q + 8 * (Z.of_nat n' - 1)) t' /\ 1 <= t' < 2 ^ 64)
      /\ (forall x : word, let a := bv_unsigned x in ~ (o <= a < o + 16) -> M' x = M x)
      /\ mem_grows M M'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DIVLOOP_HEAD : Z := 0x221f0.
Definition DIVLOOP_EXIT : Z := 0x2223c.

(* [comment removed for export] *)
Definition divloop_kept_reg (r : reg) : Prop :=
  r <> 0%bv /\ ~ In (ridx r) APC.caller_saved /\ ridx r <> 8%nat /\ ridx r <> 24%nat /\ ridx r <> 25%nat /\ ridx r <> 26%nat.

Definition divloop_dyn_src0 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (s rq qq dq d : Z) (K Cr Cq : nat),
    getr R (2%bv : reg) = Z_to_bv 64 s ->
    getr R (3%bv : reg) = Z_to_bv 64 67584 -> getr R (4%bv : reg) = Z_to_bv 64 459832 ->
    getr R (22%bv : reg) = Z_to_bv 64 1 ->                                  (* [comment removed for export] *)
    getr R (26%bv : reg) = Z_to_bv 64 (Z.of_nat K) ->                       (* [comment removed for export] *)
    getr R (25%bv : reg) = Z_to_bv 64 (rq + 8 * Z.of_nat K) ->              (* [comment removed for export] *)
    getr R (8%bv : reg) = Z_to_bv 64 (qq + 8 * Z.of_nat K - 16) ->          (* [comment removed for export] *)
    getr R (23%bv : reg) = Z_to_bv 64 d -> 2 ^ 63 <= d < 2 ^ 64 ->          (* [comment removed for export] *)
    getr R (20%bv : reg) = Z_to_bv 64 dq ->                                 (* [comment removed for export] *)
    getr R (21%bv : reg) = Z_to_bv 64 2 ->                                  (* [comment removed for export] *)
    getr R (19%bv : reg) = Z_to_bv 64 (2 ^ 64 - 16) ->                      (* [comment removed for export] *)
    (forall i, 65536 <= i < 131072 -> M (Z_to_bv 64 i) = None) ->
    (2 <= K <= 261)%nat -> (K + 1 <= Cr)%nat -> (K - 1 <= Cq)%nat -> (Cr <= 264)%nat -> (Cq <= 264)%nat ->
    defined M rq (8 * Z.of_nat Cr) -> writable M rq (8 * Z.of_nat Cr) -> defined M qq (8 * Z.of_nat Cq) -> writable M qq (8 * Z.of_nat Cq) -> defined M dq 16 ->
    writable M (s - 16) 80 ->                                             (* [comment removed for export] *)
    s mod 16 = 0 -> rq mod 8 = 0 -> qq mod 8 = 0 -> dq mod 8 = 0 ->
    2 ^ 20 <= s - 16 -> s + 64 <= 2 ^ 47 ->
    4096 <= rq -> rq + 8 * Z.of_nat Cr <= 2 ^ 47 -> 4096 <= qq -> qq + 8 * Z.of_nat Cq <= 2 ^ 47 -> 4096 <= dq -> dq + 16 <= 2 ^ 47 ->
    (rq + 8 * Z.of_nat Cr <= s - 16 \/ s + 64 <= rq) -> (qq + 8 * Z.of_nat Cq <= s - 16 \/ s + 64 <= qq) -> (dq + 16 <= s - 16 \/ s + 64 <= dq) ->
    (rq + 8 * Z.of_nat Cr <= qq \/ qq + 8 * Z.of_nat Cq <= rq) -> (rq + 8 * Z.of_nat Cr <= dq \/ dq + 16 <= rq) -> (qq + 8 * Z.of_nat Cq <= dq \/ dq + 16 <= qq) ->
    exists (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
      msteps RSEGS (@mkst fx R (Z_to_bv 64 DIVLOOP_HEAD) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 DIVLOOP_EXIT) M' (seg_rom RSEGS))
      /\ (forall x : reg, divloop_kept_reg x -> getr R' x = getr R x)
      /\ getr R' (26%bv : reg) = Z_to_bv 64 1 /\ getr R' (25%bv : reg) = Z_to_bv 64 (rq + 8) /\ getr R' (8%bv : reg) = Z_to_bv 64 (qq - 8)
      /\ defined M' rq (8 * Z.of_nat Cr) /\ defined M' qq (8 * Z.of_nat Cq)
      /\ (forall x : word, let a := bv_unsigned x in
            ~ (rq <= a < rq + 8 * (Z.of_nat K + 1)) -> ~ (qq <= a < qq + 8 * (Z.of_nat K - 1)) ->
            ~ (s - 16 <= a < s) -> ~ (s + 56 <= a < s + 64) -> M' x = M x)
      /\ mem_grows M M'.

