(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt.

Module B_normalize_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_app2.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Notation NORMALIZE_ENTRY := 0x981cc%Z.
Notation RELRO_LO := 0xda000%Z.
Notation RELRO_HI := 0xe0000%Z.
Notation BCELL := 943736%Z.           (* [comment removed for export] *)
Notation IMG_END := 0x63c000%Z.

Definition normalize_entry : Z := NORMALIZE_ENTRY.
Definition normalize_FR : Z := 16.

(* [comment removed for export] *)
Fixpoint norm_len (ws : list word) (n : nat) : nat :=
  match n with
  | O => O
  | S n' => if (limbZ ws n' =? 0)%Z then norm_len ws n' else n
  end.
Lemma norm_len_le : forall ws n, (norm_len ws n <= n)%nat.
Proof. induction n as [|n IH]; cbn; [lia|]. destruct (limbZ ws n =? 0)%Z; lia. Qed.
Lemma norm_len_bnorm : forall ws n, bnorm ws (norm_len ws n).
Proof.
  induction n as [|n IH]; cbn. { apply bnorm_0. }
  destruct (Z.eqb_spec (limbZ ws n) 0); [exact IH|]. right. rewrite Nat.sub_1_r. cbn. exact n0.
Qed.
Lemma norm_len_bval : forall ws n, bval ws (norm_len ws n) = bval ws n.
Proof.
  induction n as [|n IH]; cbn -[bval]; [reflexivity|].
  destruct (Z.eqb_spec (limbZ ws n) 0) as [E|]; [|reflexivity]. rewrite IH, bval_S, E. lia.
Qed.

Definition normalize_W (A : Z) (sp : word) : list ivl := [(A + 496, A + 498); (bv_unsigned sp - 16, bv_unsigned sp)]%Z.

Definition normalize_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (normalize_W A sp) m m'
    /\ wmono BSEGS m m'
    /\ u64arr BSEGS m' A ws
    /\ rw_cells BSEGS m' (A + 496) [C2 (Z_to_bv 64 (Z.of_nat (norm_len ws (Z.to_nat len))))]
    /\ stk BSEGS m' (bv_unsigned sp - 16) (bv_unsigned sp).

Definition normalize_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    u64arr BSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells BSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z ->
    (* [comment removed for export] *)
    stk BSEGS m (bv_unsigned sp - 16) (bv_unsigned sp) ->
    (* [comment removed for export] *)
    pristine m RELRO_LO RELRO_HI ->
    ro_cells BSEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] ->
    (* [comment removed for export] *)
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= bv_unsigned sp - 16)%Z ->
    (IMG_END <= bv_unsigned sp - 16)%Z ->
    (KHI <= bv_unsigned sp - 16)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z -> (bv_unsigned a0 + 504 <= KTOP)%Z ->
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    evt BSEGS (normalize_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc (bv_unsigned a0) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 NORMALIZE_ENTRY) fc None m (seg_rom BSEGS)).
End B_normalize_stmt.

Module B_small_add_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_app2.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Notation SADD_ENTRY := 0x96a40%Z.
Notation RELRO_LO := 0xda000%Z.
Notation RELRO_HI := 0xe0000%Z.
Notation BCELL := 943736%Z.           (* [comment removed for export] *)
Notation IMG_END := 0x63c000%Z.

Definition small_add_entry : Z := SADD_ENTRY.
Definition small_add_FR : Z := 16.

Definition small_add_W (A : Z) (sp : word) : list ivl := [(A, A + 498); (bv_unsigned sp - 16, bv_unsigned sp)]%Z.

Definition small_add_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (A y : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 : word) (m' : word -> option byte) (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (small_add_W A sp) m m'
    /\ wmono BSEGS m m'
    /\ u64arr BSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells BSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (len <= len' <= len + 1 /\ len' <= 62)%Z
    /\ bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) + y)%Z
    /\ (bnorm ws (Z.to_nat len) -> bnorm ws' (Z.to_nat len'))
    /\ stk BSEGS m' (bv_unsigned sp - 16) (bv_unsigned sp).

Definition small_add_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    u64arr BSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells BSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z ->
    (bval ws (Z.to_nat len) + bv_unsigned a1 < BIG_CAP)%Z ->
    (* [comment removed for export] *)
    stk BSEGS m (bv_unsigned sp - 16) (bv_unsigned sp) ->
    (* [comment removed for export] *)
    pristine m RELRO_LO RELRO_HI ->
    ro_cells BSEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] ->
    (* [comment removed for export] *)
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= bv_unsigned sp - 16)%Z ->
    (IMG_END <= bv_unsigned sp - 16)%Z ->
    (KHI <= bv_unsigned sp - 16)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z -> (bv_unsigned a0 + 504 <= KTOP)%Z ->
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    evt BSEGS (small_add_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6
                 F fc (bv_unsigned a0) (bv_unsigned a1) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SADD_ENTRY) fc None m (seg_rom BSEGS)).
End B_small_add_stmt.

Module B_small_mul_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_app2.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Notation SMUL_ENTRY := 0x96924%Z.
Notation RELRO_LO := 0xda000%Z.       (* [comment removed for export] *)
Notation RELRO_HI := 0xe0000%Z.
Notation BCELL := 943736%Z.           (* [comment removed for export] *)
Notation IMG_END := 0x63c000%Z.        (* [comment removed for export] *)

Definition small_mul_entry : Z := SMUL_ENTRY.
Definition small_mul_FR : Z := 16.

(* [comment removed for export] *)
Definition small_mul_W (A : Z) (sp : word) : list ivl :=
  [(A, A + 498); (bv_unsigned sp - 16, bv_unsigned sp)]%Z.

Definition small_mul_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A y : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (small_mul_W A sp) m m'
    /\ wmono BSEGS m m'
    /\ u64arr BSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells BSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (len <= len' <= len + 1 /\ len' <= 62)%Z
    /\ bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * y)%Z
    /\ (y <> 0%Z -> bnorm ws (Z.to_nat len) -> bnorm ws' (Z.to_nat len'))
    /\ stk BSEGS m' (bv_unsigned sp - 16) (bv_unsigned sp).

Definition small_mul_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    (* [comment removed for export] *)
    u64arr BSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells BSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z ->
    (bval ws (Z.to_nat len) * bv_unsigned a1 < BIG_CAP)%Z ->
    (* [comment removed for export] *)
    stk BSEGS m (bv_unsigned sp - 16) (bv_unsigned sp) ->
    (* [comment removed for export] *)
    pristine m RELRO_LO RELRO_HI ->
    ro_cells BSEGS m BCELL [C8 (Z_to_bv 64 ASAN_B)] ->
    (* [comment removed for export] *)
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + 498 <= bv_unsigned sp - 16)%Z ->
    (* [comment removed for export] *)
    (IMG_END <= bv_unsigned sp - 16)%Z ->
    (KHI <= bv_unsigned sp - 16)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z -> (bv_unsigned a0 + 504 <= KTOP)%Z ->
    (* [comment removed for export] *)
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    evt BSEGS (small_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) (bv_unsigned a1) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SMUL_ENTRY) fc None m (seg_rom BSEGS)).
End B_small_mul_stmt.

Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Notation LMUL_ENTRY := 0x973b0%Z.
Notation IMG_LO := 0x10000%Z.          (* [comment removed for export] *)
Notation ROD_HI := 0x3e000%Z.
Notation B_LARGE_POW5 := 0x25360%Z.    (* [comment removed for export] *)
Notation POW5TAB_SH := 2147469932%Z.   (* [comment removed for export] *)
Notation POW5TAB_SHN := 32%Z.
Notation FSSIZE := 11571200%Z.
(* [comment removed for export] *)
Notation LM_T := 61%Z.
(* [comment removed for export] *)

Definition long_mul_entry : Z := LMUL_ENTRY.
Definition long_mul_need : Z := 2528.
Definition B_LARGE_POW5_ADDR : Z := B_LARGE_POW5.

(* [comment removed for export] *)
Notation FK5_HINT := 40%Z.
Notation FK5_FLAGS := 35840%Z.      Notation FK5_NFLAGS := 512%Z.
Notation FK5_LO := 5279744%Z.       Notation FK5_HI := 6328320%Z.
Notation FK5_SLO := 659968%Z.       Notation FK5_SHI := 791040%Z.
(* [comment removed for export] *)
Notation FK_SH_LO := 397824%Z.      Notation FK_SH_N := 393216%Z.

Definition fk5_inv (m : word -> option byte) (FS : Z) (h5 : word) : Prop :=
     fs_cells_ok FS m
  /\ rw_cells BSEGS m (FS + FK5_HINT) [C8 h5]
  /\ u8arr BSEGS m (FS + FK5_FLAGS) (zeros 512)
  /\ stk BSEGS m (FS + FK5_LO) (FS + FK5_HI)
  /\ stk BSEGS m (ASAN_B + FS / 8 + FK5_SLO) (ASAN_B + FS / 8 + FK5_SHI).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RT_IMG_IVS : list (Z * Z) :=
  [ (0x10000, 0x2e000); (0xe6678, 12); (0xe5ee0, 8); (0xe7358, 2); (0xe7360, 24); (0x176118, 4); (0x178231, 1); (0x6197e8, 8);
    (0x619838, 56); (0x63abe8, 8); (0xda000, 0x6000); (0xe0250, 0x188) ]%Z.
Definition RTX (v : rt_vals) (fc : bv 32) : Prop :=
  (6537216 <= rt_ctx v /\ 4096 <= rt_thr v /\ 4096 <= rt_blk v /\ rt_ctx v mod 8 = 0 /\ rt_thr v mod 8 = 0 /\ rt_blk v mod 8 = 0)%Z
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
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (long_mul_W (bv_unsigned sp) A (rt_FS v)) m m'
    /\ wmono BSEGS m m'
    /\ stk BSEGS m' (bv_unsigned sp - 2528) (bv_unsigned sp)
    /\ u64arr BSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells BSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
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
    stk BSEGS m (bv_unsigned sp - 2528) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (IMG_END <= bv_unsigned sp - 2528)%Z ->
    pristine m IMG_LO ROD_HI ->
    u64arr BSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells BSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    bnorm ws (Z.to_nat len) ->
    a1 = Z_to_bv 64 B_LARGE_POW5 -> a2 = Z_to_bv 64 5 ->
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
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    shz BSEGS m POW5TAB_SH POW5TAB_SHN ->
    rdbl BSEGS m (ASAN_B + bv_unsigned a0 / 8 - 8) 79 ->
    rdbl BSEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N ->
    RTX v fc -> (bv_unsigned ra mod 2 = 0)%Z ->
    (* [comment removed for export] *)
    shz BSEGS m (ASAN_B + (bv_unsigned sp - 2528) / 8) 316 ->
    evt BSEGS (long_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) ws len v m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LMUL_ENTRY) fc None m (seg_rom BSEGS)).
