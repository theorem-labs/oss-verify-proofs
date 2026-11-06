(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr SysStep Exec TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASTRCMP_STUB : Z := 0x612a4.      (* [comment removed for export] *)
Definition ASTRCMP_ICPT : Z := 0x61888.      (* [comment removed for export] *)
Definition AMEMCMP_STUB : Z := 0x612ac.     (* [comment removed for export] *)
Definition ABCMP_STUB : Z := 0x612b0.       (* [comment removed for export] *)
Definition AMEMCMP_REAL : Z := 0x111a84.    (* [comment removed for export] *)
Definition ABCMP_REAL : Z := 0x1119b4.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMEMCMP_STACK : Z := 2320.       (* [comment removed for export] *)
Definition ABCMP_STACK : Z := 4560.         (* [comment removed for export] *)
Definition ASNPRINTF_STUB : Z := 0x612e0.   (* [comment removed for export] *)
Definition ASTRTOLL_STUB : Z := 0x61354.    (* [comment removed for export] *)
Definition ASNPRINTF_STACK : Z := 6144.     (* [comment removed for export] *)
Definition ASNP_HEAD : Z := 0xf2060000f1f1f1f1.   (* [comment removed for export] *)
Definition ASTRTOLL_STACK : Z := 2304.      (* [comment removed for export] *)
Definition A_STR_FMT_D : Z := 0x252a0.     (* [comment removed for export] *)
Definition A_STR_ONE : Z := 0x25260.       (* [comment removed for export] *)
Definition A_STKCHK_GUARD : Z := 0x681830.  (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint zstrcmp (e t : list Z) : Z :=
  match e, t with
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | c1 :: e', c2 :: t' => if Z.eqb c1 c2 then zstrcmp e' t' else if Z.ltb c1 c2 then -1 else 1
  end.

(* [comment removed for export] *)
Fixpoint zmemcmp (xs ys : list Z) : Z :=
  match xs, ys with
  | x :: xs', y :: ys' => if Z.eqb x y then zmemcmp xs' ys' else x - y
  | _, _ => 0
  end.

(* [comment removed for export] *)
Definition A6CONST (m : word -> option byte) : Prop :=
  rw_cells bsegs m ACF_ISTRCMP_CELL [C1 (b8 1)]
  /\ rw_cells bsegs m ACF_IMEMCMP_CELL [C1 (b8 1); C1 (b8 1)]
  /\ rw_cells bsegs m AREAL_MEMCMP_CELL [C8 (wz AMEMCMP_REAL); C8 (wz ABCMP_REAL)].
Definition a6const_hyp : Prop := forall m, ACONST m -> A6CONST m.
Lemma a6const_of_ACONST : a6const_hyp.
Proof. intros m AC. exact (ACONST_a6 m AC). Qed.

Section Iface6.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition astrcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (r lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ ACONST m'.

  Definition strcmp_icpt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e t rest1 rest2 : list Z) (lo : Z),
      bytes_at bsegs m (bv_unsigned a0) (map b8 (e ++ 0 :: rest1)) -> Forall (fun c => 0 < c < 256) e ->
      bytes_at bsegs m (bv_unsigned a1) (map b8 (t ++ 0 :: rest2)) -> Forall (fun c => 0 < c < 256) t ->
      accessible m (bv_unsigned a0) (Z.of_nat (length e) + 1) ->
      accessible m (bv_unsigned a1) (Z.of_nat (length t) + 1) ->
      shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length e) + 1) ->
      shvis m (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length t) + 1) ->
      stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv bsegs m -> ACONST m ->
      Z.of_nat (length e) + 1 <= 2^40 -> Z.of_nat (length t) + 1 <= 2^40 ->
      in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length e) + 1) ->
      in_app_mem (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length t) + 1) ->
      (bv_unsigned a0 + Z.of_nat (length (e ++ 0 :: rest1)) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a1 + Z.of_nat (length (t ++ 0 :: rest2)) <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      evt bsegs (astrcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (zstrcmp e t) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASTRCMP_STUB) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition amemcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (r stack lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - stack, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ ACONST m'.

  Definition memcmp_icpt_stmt_at (entry stack : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ls rs : list byte) (lo : Z),
      bytes_at bsegs m (bv_unsigned a0) ls -> bytes_at bsegs m (bv_unsigned a1) rs ->
      Z.of_nat (length ls) = bv_unsigned a2 -> length rs = length ls ->
      accessible m (bv_unsigned a0) (bv_unsigned a2) -> accessible m (bv_unsigned a1) (bv_unsigned a2) ->
      shvis m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) -> shvis m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
      stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack ->
      mem_inv bsegs m -> ACONST m ->
      bv_unsigned a2 <= 2^40 ->
      in_app_mem (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) -> in_app_mem (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
      (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      evt bsegs (amemcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                   (zmemcmp (map (@bv_unsigned 8) ls) (map (@bv_unsigned 8) rs)) stack lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).
  Definition memcmp_icpt_stmt : Prop := memcmp_icpt_stmt_at AMEMCMP_STUB AMEMCMP_STACK.
  Definition bcmp_icpt_stmt : Prop := memcmp_icpt_stmt_at ABCMP_STUB ABCMP_STACK.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition acanary (m : mem) : Prop := exists can : word, rw_cells bsegs m A_STKCHK_GUARD [C8 can].

  Definition asnprintf_d_m1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (buf : word) (lo : Z) (junk : list byte) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (bv_unsigned buf, bv_unsigned buf + 22)]%Z m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' (bv_unsigned buf) [C1 (Z_to_bv 8 45); C1 (Z_to_bv 8 49); C1 (Z_to_bv 8 0); CB 19 (skipn 3 junk)]
      /\ ACONST m'.

  (* [comment removed for export] *)
  Definition snprintf_d_m1_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (junk : list byte),
      F = bvmap_empty -> fc = Z_to_bv 32 0 ->
      a1 = Z_to_bv 64 22 -> a2 = Z_to_bv 64 A_STR_FMT_D -> a3 = Z_to_bv 64 18446744073709551615 ->
      bv_unsigned a0 mod 64 = 32 ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 0x7fffffffffc0 ->
      stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo + ASNPRINTF_STACK <= bv_unsigned sp ->
      rw_cells bsegs m (bv_unsigned a0) [CB 22 junk] ->
      aapp (bv_unsigned a0 - 32) 64 ->
      rw_cells bsegs m (sh (bv_unsigned a0 - 32)) [C8 (wz ASNP_HEAD)] ->
      SHAD m (bv_unsigned sp - ASNPRINTF_STACK) (poison_bytes 768 0) ->
      acanary m -> mem_inv bsegs m -> ACONST m ->
      evt bsegs (asnprintf_d_m1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo junk m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASNPRINTF_STUB) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition astrtoll_m1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s endp : word) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 18446744073709551615) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (bv_unsigned endp, bv_unsigned endp + 8)]%Z m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' (bv_unsigned endp) [C8 (Z_to_bv 64 (bv_unsigned s + 2))]
      /\ bytes_at bsegs m' (bv_unsigned s) [Z_to_bv 8 45; Z_to_bv 8 49; Z_to_bv 8 0]
      /\ ACONST m'.

  Definition strtoll_m1_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (e0 : word),
      F = bvmap_empty -> fc = Z_to_bv 32 0 ->
      a2 = Z_to_bv 64 0 ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 0x7fffffffffff ->
      stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo + ASTRTOLL_STACK <= bv_unsigned sp ->
      bytes_at bsegs m (bv_unsigned a0) [Z_to_bv 8 45; Z_to_bv 8 49; Z_to_bv 8 0] -> AIMG_TOP <= bv_unsigned a0 ->
      accessible m (bv_unsigned a0) 3 -> shvis m (bv_unsigned a0) (bv_unsigned a0 + 3) -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + 3) ->
      (bv_unsigned a0 + 3 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      rw_cells bsegs m (bv_unsigned a1) [C8 e0] -> AIMG_TOP <= bv_unsigned a1 ->
      accessible m (bv_unsigned a1) 8 -> shvis m (bv_unsigned a1) (bv_unsigned a1 + 8) -> in_app_mem (bv_unsigned a1) (bv_unsigned a1 + 8) ->
      (bv_unsigned a1 + 8 <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      (bv_unsigned a0 + 3 <= bv_unsigned a1 \/ bv_unsigned a1 + 8 <= bv_unsigned a0) ->
      acanary m -> mem_inv bsegs m -> ACONST m ->
      evt bsegs (astrtoll_m1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASTRTOLL_STUB) fc None m (seg_rom bsegs)).

  Definition astrtoll_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (endp : word) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (bv_unsigned endp, bv_unsigned endp + 8)]%Z m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' (bv_unsigned endp) [C8 (Z_to_bv 64 (A_STR_ONE + 1))]
      /\ ACONST m'.

  Definition strtoll_one_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (e0 : word),
      F = bvmap_empty -> fc = Z_to_bv 32 0 ->
      a0 = Z_to_bv 64 A_STR_ONE -> a2 = Z_to_bv 64 0 ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 0x7fffffffffff ->
      stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo + ASTRTOLL_STACK <= bv_unsigned sp ->
      rw_cells bsegs m (bv_unsigned a1) [C8 e0] -> AIMG_TOP <= bv_unsigned a1 ->
      accessible m (bv_unsigned a1) 8 -> shvis m (bv_unsigned a1) (bv_unsigned a1 + 8) -> in_app_mem (bv_unsigned a1) (bv_unsigned a1 + 8) ->
      (bv_unsigned a1 + 8 <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      acanary m -> mem_inv bsegs m -> ACONST m ->
      evt bsegs (astrtoll_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a1 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASTRTOLL_STUB) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition asan_rt_hyps6 : Prop := strcmp_icpt_stmt /\ memcmp_icpt_stmt /\ bcmp_icpt_stmt.   (* [comment removed for export] *)
  Definition asan_rt_hyps6b : Prop := snprintf_d_m1_stmt /\ strtoll_m1_stmt /\ strtoll_one_stmt.
  (* [comment removed for export] *)
End Iface6.
