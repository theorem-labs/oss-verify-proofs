From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c reac_decode_c reac_upstream_decode_c ReacDecodeLib.
Import ListNotations.
Open Scope Z_scope.

(* The interface between the loop part (reac_upstream_decode_lib.v) and the main theorem (reac_upstream_decode.v)
   of the asan-ubsan reac_upstream_decode proof. sp is the stack pointer at entry; the 96-byte frame starts at
   bv_unsigned sp + -96. *)

(* The post-state of reac_upstream_decode_contract, with len = bv_unsigned a1. *)
Definition PostU (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (bs : list byte) (raw out len lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if up_ok raw out len bs then 12 else -1))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    (if up_ok raw out len bs
     then munch [(bv_unsigned sp - 96, bv_unsigned sp); (out, out + 36 * up_nch len)] m m' /\
          bytes_at rsegs m' out (braid_out bs (up_nch len) 12)
     else munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m').

(* The frame: 32 bytes of scratch (the loop writes sp+8, sp+16, sp+24), then the 8 saved registers
   s6@32 s5@40 s4@48 s3@56 s2@64 s1@72 s0@80 ra@88. *)
Definition FRU (ra sp s0 s1 s2 s3 s4 s5 s6 : word) (mk : word -> option byte) : Prop :=
  exists junk : list byte,
    rw_cells rsegs mk (bv_unsigned sp + -96) [CB 32 junk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* The first j output bytes. *)
Definition bpre (bs : list byte) (nch j : Z) : list byte :=
  map (braid_byte bs nch 12) (map Z.of_nat (seq 0 (Z.to_nat j))).

(* The loop invariant after j output bytes. *)
Definition INVU (ra sp s0 s1 s2 s3 s4 s5 s6 : word) (m : word -> option byte) (bs : list byte) (raw out lo nch : Z)
    (mk : word -> option byte) (j : Z) : Prop :=
  bytes_at rsegs mk raw bs /\ FRU ra sp s0 s1 s2 s3 s4 s5 s6 mk /\ stk rsegs mk lo (bv_unsigned sp + -96) /\
  wr_at rsegs mk out (36 * nch) /\
  munch [(bv_unsigned sp + -96, bv_unsigned sp); (out, out + 36 * nch)] m mk /\ wmono rsegs m mk /\
  bytes_at rsegs mk out (bpre bs nch j).

(* The outer loop head 0x821bc (first arrival, ch = 0) to the post-state. *)
Definition UP_OUTER : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (bs : list byte) (raw out len lo nch : Z),
    lo + 96 <= bv_unsigned sp -> 0 <= lo ->
    up_nch len = nch -> 2 <= nch <= 40 -> nch mod 2 = 0 -> len = 52 + 36 * nch ->
    length bs = Z.to_nat len -> 0 < raw -> raw + len <= 2^64 -> 0 < out -> out + 36 * nch < 2^64 ->
    (out + 36 * nch <= raw \/ raw + len <= out) ->
    (out + 36 * nch <= bv_unsigned sp - 96 \/ bv_unsigned sp <= out) ->
    (raw + len <= bv_unsigned sp - 96 \/ bv_unsigned sp <= raw) ->
    addressable m raw len -> addressable m out (36 * nch) ->
    (forall x, bv_unsigned sp - 96 <= x < bv_unsigned sp -> app_mem x) ->
    up_ok raw out len bs = true ->
    forall (m1 : word -> option byte)
           (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    bv_unsigned x5 = bv_unsigned sp + -88 -> bv_unsigned x6 = 18446744073709551599 ->
    bv_unsigned x7 = 18446744073709551615 -> bv_unsigned x12 = out -> bv_unsigned x13 = raw + 50 ->
    bv_unsigned x14 = 0 -> bv_unsigned x15 = 2147450880 -> bv_unsigned x16 = nch ->
    bv_unsigned x17 = 18446744073709551608 -> bv_unsigned x28 = 12 ->
    bv_unsigned x29 = 18446744073709551615 - (raw + 50) -> bv_unsigned x30 = 2147483646 ->
    bv_unsigned x31 = 18446744073709551607 ->
    INVU ra sp s0 s1 s2 s3 s4 s5 s6 m bs raw out lo nch m1 0 ->
    evt rsegs (PostU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x821bc) fc None m1 (seg_rom rsegs)).

(* The common return path 0x82098 with a0 = 12 (up_ok true) to the post-state. *)
Definition UP_EXIT : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (bs : list byte) (raw out len lo : Z),
    lo + 96 <= bv_unsigned sp -> 0 <= lo ->
    forall (m1 : word -> option byte)
           (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    FRU ra sp s0 s1 s2 s3 s4 s5 s6 m1 -> stk rsegs m1 lo (bv_unsigned sp + -96) -> wmono rsegs m m1 ->
    up_ok raw out len bs = true ->
    munch [(bv_unsigned sp + -96, bv_unsigned sp); (out, out + 36 * up_nch len)] m m1 ->
    bytes_at rsegs m1 out (braid_out bs (up_nch len) 12) ->
    evt rsegs (PostU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 12) x11 x12 x13 x14 x15
               x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x82098) fc None m1 (seg_rom rsegs)).

(* The common return path 0x82098 with a0 = -1 (every early return, up_ok false) to the post-state. *)
Definition UP_FAIL : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (bs : list byte) (raw out len lo : Z),
    lo + 96 <= bv_unsigned sp -> 0 <= lo ->
    forall (m1 : word -> option byte)
           (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    FRU ra sp s0 s1 s2 s3 s4 s5 s6 m1 -> stk rsegs m1 lo (bv_unsigned sp + -96) -> wmono rsegs m m1 ->
    munch [(bv_unsigned sp + -96, bv_unsigned sp)] m m1 ->
    up_ok raw out len bs = false ->
    evt rsegs (PostU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (-1)) x11 x12 x13 x14 x15
               x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x82098) fc None m1 (seg_rom rsegs)).
