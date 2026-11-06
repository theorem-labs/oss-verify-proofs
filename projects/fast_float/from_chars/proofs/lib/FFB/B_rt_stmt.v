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
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Export B_app2.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation B_IMEMSET := 0x60644%Z.
Notation B_IMEMCPY := 0xd7b70%Z.   (* [comment removed for export] *)
Notation B_IMEMMOVE := 0x60884%Z.
Notation B_SMALLOC3 := 0x4b068%Z.
Notation B_SMALLOC4 := 0x4b204%Z.
Notation B_SMALLOC5 := 0x4b3d0%Z.
Notation B_SFREE5 := 0x4b5dc%Z.
Notation B_SETSH00 := 0x63d18%Z.
Notation B_SETSHF5 := 0x63e20%Z.
Notation B_MUSL_MEMSET := 0xd4904%Z.
Notation B_MUSL_MEMCPY := 0xd4500%Z.
Notation IMG_END := 0x63c000%Z.
Notation TPV := 0x619840%Z.          (* [comment removed for export] *)
Notation SH_LO := 2147446784%Z.       (* [comment removed for export] *)

(* [comment removed for export] *)
Notation IMEMSET_NEED := 2208%Z.     (* [comment removed for export] *)
Notation IMEMCPY_NEED := 2224%Z.     (* [comment removed for export] *)
Notation IMEMMOVE_NEED := 2224%Z.
Notation SMALLOC_NEED := 208%Z.      (* [comment removed for export] *)
Notation SFREE_NEED := 16%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation RELRO_LO := 0xda000%Z.
Notation RELRO_HI := 0xe0000%Z.
Notation REALTAB_LO := 0xe0250%Z.
Notation REALTAB_HI := 0xe03d8%Z.

(* [comment removed for export] *)
Record rt_vals := RTV {
  rt_FS : Z;     (* [comment removed for export] *)
  rt_ctx : Z;    (* [comment removed for export] *)
  rt_thr : Z;    (* [comment removed for export] *)
  rt_tlsb : Z; rt_tlse : Z;   (* [comment removed for export] *)
  rt_blk : Z;    (* [comment removed for export] *)
  rt_beg : Z     (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RT (m : word -> option byte) (v : rt_vals) : Prop :=
     ro_cells BSEGS m 943736 [C8 (Z_to_bv 64 ASAN_B); C4 (Z_to_bv 64 1)]                 (* [comment removed for export] *)
  /\ ro_cells BSEGS m 941792 [C1 (Z_to_bv 8 1)] /\ ro_cells BSEGS m 941796 [C4 (Z_to_bv 64 0)]   (* [comment removed for export] *)
  /\ ro_cells BSEGS m 947032 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                       (* [comment removed for export] *)
  /\ ro_cells BSEGS m 947040 [C8 (Z_to_bv 64 (KTOP - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]  (* [comment removed for export] *)
  /\ (exists fb, ro_cells BSEGS m 1540657 [C1 fb] /\ bv_unsigned fb <> 0%Z)             (* [comment removed for export] *)
  /\ ro_cells BSEGS m 1532184 [C4 (Z_to_bv 64 0)]                                       (* [comment removed for export] *)
  /\ ro_cells BSEGS m 6395880 [C8 (Z_to_bv 64 0x63abe8)]                                (* [comment removed for export] *)
  /\ ro_cells BSEGS m 6395960 [C8 (Z_to_bv 64 0x619860); C8 (Z_to_bv 64 (rt_FS v))]     (* [comment removed for export] *)
  /\ ro_cells BSEGS m 6395976 [C8 (Z_to_bv 64 (rt_blk v))]                               (* [comment removed for export] *)
  /\ ro_cells BSEGS m 6396008 [C8 (Z_to_bv 64 0x61a040)]                                (* [comment removed for export] *)
  /\ ro_cells BSEGS m 6532072 [C8 (Z_to_bv 64 (rt_ctx v))]                               (* [comment removed for export] *)
  /\ ro_cells BSEGS m (rt_ctx v + 152) [C8 (Z_to_bv 64 (rt_thr v))]
  /\ ro_cells BSEGS m (rt_thr v + 48) [C8 (Z_to_bv 64 (rt_tlsb v)); C8 (Z_to_bv 64 (rt_tlse v))]   (* [comment removed for export] *)
  /\ ro_cells BSEGS m (rt_blk v + 24) [C8 (Z_to_bv 64 (rt_beg v))]
  /\ (0 < rt_beg v < 2^64)%Z /\ (rt_blk v <> 0)%Z /\ (rt_blk v + 1 <> 2^64)%Z /\ (rt_ctx v <> 0)%Z /\ (rt_thr v <> 0)%Z
  (* [comment removed for export] *)
  /\ (app2r (rt_FS v) (rt_FS v + 11571200))%Z /\ (rt_FS v + 11571200 <= KTOP)%Z /\ (rt_FS v mod 4096 = 0)%Z
  /\ rt_app (rt_ctx v) 160 /\ (rt_ctx v + 160 <= KTOP)%Z
  /\ rt_app (rt_thr v) 80 /\ (rt_thr v + 80 <= KTOP)%Z
  /\ rt_app (rt_blk v) 32 /\ (rt_blk v + 32 <= KTOP)%Z.

(* [comment removed for export] *)
Definition rt_disj (v : rt_vals) (lo hi : Z) : Prop :=
     (hi <= rt_ctx v \/ rt_ctx v + 160 <= lo)%Z
  /\ (hi <= rt_thr v \/ rt_thr v + 80 <= lo)%Z
  /\ (hi <= rt_blk v \/ rt_blk v + 32 <= lo)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fk_nframes (k : Z) : Z := Z.shiftl 1 (14 - k).                 (* [comment removed for export] *)
Definition fk_size (k : Z) : Z := Z.shiftl 1 (6 + k).                     (* [comment removed for export] *)
Definition fk_flags (FS k : Z) : Z :=                                    (* [comment removed for export] *)
  FS + 4096 + 32 * Z.shiftl (Z.shiftr 1023 (10 - k)) (10 - k).
Definition fk_frame (FS k pos : Z) : Z := FS + 36864 + k * 1048576 + pos * fk_size k.
Definition fk_hint (FS k : Z) : Z := FS + 8 * k.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition asan_memset_W (sp p : word) (n : Z) : list ivl :=
  [(bv_unsigned sp - IMEMSET_NEED, bv_unsigned sp); (bv_unsigned p, bv_unsigned p + n)]%Z.

Definition asan_memset_post
    (ra sp gp tp s0 s1 p s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (c n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 p a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (asan_memset_W sp p n) m m'
    /\ wmono BSEGS m m'
    /\ u8arr BSEGS m' (bv_unsigned p) (repeat (Z_to_bv 8 c) (Z.to_nat n))
    /\ stk BSEGS m' (bv_unsigned sp - IMEMSET_NEED) (bv_unsigned sp).

Definition asan_memset_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v : rt_vals) (old : list byte) (c : Z) (shlo shn : Z),
    a1 = Z_to_bv 64 c -> (0 <= c <= 255)%Z ->
    u8arr BSEGS m (bv_unsigned a0) old -> Z.of_nat (length old) = bv_unsigned a2 ->
    (bv_unsigned a0 mod 8 = 0)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2 + 8))%Z -> (bv_unsigned a0 + bv_unsigned a2 + 8 <= KTOP)%Z -> (bv_unsigned a2 <= 2^40)%Z ->
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) ((bv_unsigned a2 + 7) / 8) ->
    rdbl BSEGS m shlo shn ->
    (shlo <= ASAN_B + bv_unsigned a0 / 8 - (ASAN_B + bv_unsigned a0 / 8) mod 8)%Z ->
    (ASAN_B + (bv_unsigned a0 + bv_unsigned a2) / 8 + 8 <= shlo + shn)%Z ->
    stk BSEGS m (bv_unsigned sp - IMEMSET_NEED) (bv_unsigned sp) ->
    (IMG_END <= bv_unsigned sp - IMEMSET_NEED)%Z -> (KHI <= bv_unsigned sp - IMEMSET_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - IMEMSET_NEED)%Z ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v -> rt_disj v (bv_unsigned sp - IMEMSET_NEED) (bv_unsigned sp) ->
    rt_disj v (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (asan_memset_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc c (bv_unsigned a2) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 B_IMEMSET) fc None m (seg_rom BSEGS)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition asan_memcpy_W (sp d : word) (n : Z) : list ivl :=
  [(bv_unsigned sp - IMEMCPY_NEED, bv_unsigned sp); (bv_unsigned d, bv_unsigned d + n)]%Z.

Definition asan_memcpy_post
    (ra sp gp tp s0 s1 d s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (src n : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 d a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (asan_memcpy_W sp d n) m m'
    /\ wmono BSEGS m m'
    /\ u8arr BSEGS m' (bv_unsigned d) bs
    /\ bytes_at BSEGS m' src bs
    /\ stk BSEGS m' (bv_unsigned sp - IMEMCPY_NEED) (bv_unsigned sp).

Definition asan_memcpy_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v : rt_vals) (bs old : list byte) (shlo shn : Z),
    bytes_at BSEGS m (bv_unsigned a1) bs ->
    u8arr BSEGS m (bv_unsigned a0) old ->
    length old = length bs ->
    Z.of_nat (length bs) = bv_unsigned a2 ->
    (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2 + 8))%Z -> (bv_unsigned a0 + bv_unsigned a2 + 8 <= KTOP)%Z ->
    (app2r (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2 + 8))%Z -> (bv_unsigned a1 + bv_unsigned a2 + 8 <= KTOP)%Z ->
    (bv_unsigned a2 <= 2^40)%Z ->
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) ((bv_unsigned a0 + bv_unsigned a2 - 1) / 8 - bv_unsigned a0 / 8 + 1) ->
    shz BSEGS m (ASAN_B + bv_unsigned a1 / 8) ((bv_unsigned a1 + bv_unsigned a2 - 1) / 8 - bv_unsigned a1 / 8 + 1) ->
    rdbl BSEGS m shlo shn ->
    (shlo + 8 <= ASAN_B + bv_unsigned a0 / 8)%Z -> (ASAN_B + (bv_unsigned a0 + bv_unsigned a2) / 8 + 8 <= shlo + shn)%Z ->
    (shlo + 8 <= ASAN_B + bv_unsigned a1 / 8)%Z -> (ASAN_B + (bv_unsigned a1 + bv_unsigned a2) / 8 + 8 <= shlo + shn)%Z ->
    stk BSEGS m (bv_unsigned sp - IMEMCPY_NEED) (bv_unsigned sp) ->
    (IMG_END <= bv_unsigned sp - IMEMCPY_NEED)%Z -> (KHI <= bv_unsigned sp - IMEMCPY_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - IMEMCPY_NEED)%Z ->
    (bv_unsigned sp <= bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - IMEMCPY_NEED)%Z ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v -> rt_disj v (bv_unsigned sp - IMEMCPY_NEED) (bv_unsigned sp) ->
    rt_disj v (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (asan_memcpy_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a1) (bv_unsigned a2) bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 B_IMEMCPY) fc None m (seg_rom BSEGS)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition asan_memmove_W (sp d : word) (n : Z) : list ivl :=
  [(bv_unsigned sp - IMEMMOVE_NEED, bv_unsigned sp); (bv_unsigned d, bv_unsigned d + n)]%Z.

Definition asan_memmove_post
    (ra sp gp tp s0 s1 d s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (n : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 d a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (asan_memmove_W sp d n) m m'
    /\ wmono BSEGS m m'
    /\ u8arr BSEGS m' (bv_unsigned d) bs
    /\ stk BSEGS m' (bv_unsigned sp - IMEMMOVE_NEED) (bv_unsigned sp).

Definition asan_memmove_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v : rt_vals) (bs old : list byte) (shlo shn : Z),
    bytes_at BSEGS m (bv_unsigned a1) bs ->
    u8arr BSEGS m (bv_unsigned a0) old ->
    length old = length bs ->
    Z.of_nat (length bs) = bv_unsigned a2 ->
    (bv_unsigned a0 mod 8 = 0)%Z -> (bv_unsigned a1 mod 8 = 0)%Z -> (bv_unsigned a2 mod 8 = 0)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2 + 8))%Z -> (bv_unsigned a0 + bv_unsigned a2 + 8 <= KTOP)%Z ->
    (app2r (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2 + 8))%Z -> (bv_unsigned a1 + bv_unsigned a2 + 8 <= KTOP)%Z ->
    (bv_unsigned a2 <= 2^40)%Z ->
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) (bv_unsigned a2 / 8) ->
    shz BSEGS m (ASAN_B + bv_unsigned a1 / 8) (bv_unsigned a2 / 8) ->
    rdbl BSEGS m shlo shn ->
    (shlo + 8 <= ASAN_B + bv_unsigned a0 / 8)%Z -> (ASAN_B + (bv_unsigned a0 + bv_unsigned a2) / 8 + 8 <= shlo + shn)%Z ->
    (shlo + 8 <= ASAN_B + bv_unsigned a1 / 8)%Z -> (ASAN_B + (bv_unsigned a1 + bv_unsigned a2) / 8 + 8 <= shlo + shn)%Z ->
    stk BSEGS m (bv_unsigned sp - IMEMMOVE_NEED) (bv_unsigned sp) ->
    (IMG_END <= bv_unsigned sp - IMEMMOVE_NEED)%Z -> (KHI <= bv_unsigned sp - IMEMMOVE_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - IMEMMOVE_NEED)%Z ->
    (bv_unsigned sp <= bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - IMEMMOVE_NEED)%Z ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v -> rt_disj v (bv_unsigned sp - IMEMMOVE_NEED) (bv_unsigned sp) ->
    rt_disj v (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (asan_memmove_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a2) bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 B_IMEMMOVE) fc None m (seg_rom BSEGS)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition set_shadow_post
    (ra sp gp tp s0 s1 a s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (c n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch [(bv_unsigned a, bv_unsigned a + n)]%Z m m'
    /\ wmono BSEGS m m'
    /\ u8arr BSEGS m' (bv_unsigned a) (repeat (Z_to_bv 8 c) (Z.to_nat n)).

Definition set_shadow_stmt (entry c : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (old : list byte),
    u8arr BSEGS m (bv_unsigned a0) old ->
    Z.of_nat (length old) = bv_unsigned a1 ->
    (bv_unsigned a0 mod 8 = 0)%Z ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    (bv_unsigned a0 + bv_unsigned a1 <= RELRO_LO \/ REALTAB_HI <= bv_unsigned a0)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (set_shadow_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c (bv_unsigned a1) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom BSEGS)).

Definition set_shadow_00_stmt : Prop := set_shadow_stmt B_SETSH00 0.
Definition set_shadow_f5_stmt : Prop := set_shadow_stmt B_SETSHF5 245.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fs_cells_ok (FS : Z) (m : word -> option byte) : Prop :=
  ro_cells BSEGS m (FS + 88) [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 0)].

Definition smalloc_W (sp : word) (FS k h : Z) : list ivl :=
  let N := fk_nframes k in let pos := (h mod N)%Z in
  let F := fk_frame FS k pos in let SZ := fk_size k in
  [(bv_unsigned sp - SMALLOC_NEED, bv_unsigned sp);
   (fk_hint FS k, fk_hint FS k + 8);
   (fk_flags FS k + pos, fk_flags FS k + pos + 1);
   (F, F + SZ);
   (ASAN_B + F / 8, ASAN_B + F / 8 + SZ / 8)]%Z.

Definition smalloc_post (k : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F0 : bvmap 5 word) (fc : bv 32) (FS h : Z) (fl : list byte) (m : word -> option byte) : machine_state -> Prop :=
  let N := fk_nframes k in let pos := (h mod N)%Z in
  let F := fk_frame FS k pos in let SZ := fk_size k in
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk1 junk2 : list byte) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F0 (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (smalloc_W sp FS k h) m m'
    /\ wmono BSEGS m m'
    /\ stk BSEGS m' (bv_unsigned sp - SMALLOC_NEED) (bv_unsigned sp)
    /\ rw_cells BSEGS m' (fk_hint FS k) [C8 (Z_to_bv 64 ((h + 1) mod 2^64))]
    /\ u8arr BSEGS m' (fk_flags FS k) (upd fl (Z.to_nat pos) (Z_to_bv 8 1))
    /\ rw_cells BSEGS m' F [CB 24 junk1; C8 (Z_to_bv 64 (bv_unsigned sp)); CB (Z.to_nat (SZ - 40)) junk2;
                            C8 (Z_to_bv 64 (fk_flags FS k + pos))]
    /\ rw_cells BSEGS m' (ASAN_B + F / 8) [CB (Z.to_nat (SZ / 8)) (zeros (Z.to_nat (SZ / 8)))].

Definition smalloc_stmt (entry k : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F0 : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v : rt_vals) (h : Z) (fl : list byte),
    let FS := rt_FS v in
    let N := fk_nframes k in let pos := (h mod N)%Z in
    let F := fk_frame FS k pos in let SZ := fk_size k in
    tp = Z_to_bv 64 TPV ->
    RT m v -> fs_cells_ok FS m ->
    rw_cells BSEGS m (fk_hint FS k) [C8 (Z_to_bv 64 h)] -> (0 <= h < 2^64)%Z ->
    u8arr BSEGS m (fk_flags FS k) fl -> Z.of_nat (length fl) = N ->
    nth_error fl (Z.to_nat pos) = Some (Z_to_bv 8 0) ->
    stk BSEGS m F (F + SZ) ->
    stk BSEGS m (ASAN_B + F / 8) (ASAN_B + F / 8 + SZ / 8) ->
    stk BSEGS m (bv_unsigned sp - SMALLOC_NEED) (bv_unsigned sp) ->
    (IMG_END <= bv_unsigned sp - SMALLOC_NEED)%Z -> (KHI <= bv_unsigned sp - SMALLOC_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (bv_unsigned sp <= FS \/ FS + 11571200 <= bv_unsigned sp - SMALLOC_NEED)%Z ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    rt_disj v (bv_unsigned sp - SMALLOC_NEED) (bv_unsigned sp) -> rt_disj v FS (FS + 11571200) ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (smalloc_post k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc FS h fl m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F0 (Z_to_bv 64 entry) fc None m (seg_rom BSEGS)).

Definition smalloc3_stmt : Prop := smalloc_stmt B_SMALLOC3 3.
Definition smalloc4_stmt : Prop := smalloc_stmt B_SMALLOC4 4.
Definition smalloc5_stmt : Prop := smalloc_stmt B_SMALLOC5 5.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sfree5_W (sp : word) (F fladdr : Z) : list ivl :=
  [(bv_unsigned sp - SFREE_NEED, bv_unsigned sp); (fladdr, fladdr + 1); (ASAN_B + F / 8, ASAN_B + F / 8 + 256)]%Z.

Definition sfree5_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F0 : bvmap 5 word) (fc : bv 32) (F fladdr : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F0 (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (sfree5_W sp F fladdr) m m'
    /\ wmono BSEGS m m'
    /\ stk BSEGS m' (bv_unsigned sp - SFREE_NEED) (bv_unsigned sp)
    /\ rw_cells BSEGS m' fladdr [C1 (Z_to_bv 8 0)]
    /\ rw_cells BSEGS m' (ASAN_B + F / 8) [CB 256 (repeat (Z_to_bv 8 245) 256)].

Definition sfree5_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F0 : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v : rt_vals) (fladdr : Z) (flb : byte) (pre : list cell) (junk' : list byte),
    let F := bv_unsigned a0 in
    RT m v ->
    rw_cells BSEGS m F (pre ++ [C8 (Z_to_bv 64 fladdr)]) -> cells_size pre = 2040%nat ->
    rw_cells BSEGS m fladdr [C1 flb] ->
    rw_cells BSEGS m (ASAN_B + F / 8) [CB 256 junk'] ->
    (F mod 2048 = 0)%Z -> (app2r (F) (F + 2048))%Z -> (F + 2048 <= KTOP)%Z ->
    (app2r (fladdr) (fladdr + 1))%Z -> (fladdr + 1 <= KTOP)%Z ->
    stk BSEGS m (bv_unsigned sp - SFREE_NEED) (bv_unsigned sp) ->
    (IMG_END <= bv_unsigned sp - SFREE_NEED)%Z -> (KHI <= bv_unsigned sp - SFREE_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned sp <= F \/ F + 2048 <= bv_unsigned sp - SFREE_NEED)%Z ->
    (bv_unsigned sp <= fladdr \/ fladdr + 1 <= bv_unsigned sp - SFREE_NEED)%Z ->
    pristine m RELRO_LO RELRO_HI -> pristine m 65536 253952 (* [comment removed for export] *) ->
    rt_disj v (bv_unsigned sp - SFREE_NEED) (bv_unsigned sp) -> rt_disj v fladdr (fladdr + 1) ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (sfree5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc F fladdr m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F0 (Z_to_bv 64 B_SFREE5) fc None m (seg_rom BSEGS)).
