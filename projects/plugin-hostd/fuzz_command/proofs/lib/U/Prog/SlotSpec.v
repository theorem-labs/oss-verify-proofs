(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names and addresses changed; 219 of its 261 lines of code are new or changed and 704 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel rec_code_declared_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require strspn_c.
Import ListNotations.
Open Scope Z_scope.

(* The Kind A runs of LLVMFuzzerTestOneInput (ubsan 0x14060, frame 160) between its calls, stated in the MS form of
   the Kind A contracts. The frame base is the word sp (= entry sp - 160): locals at sp (24 bytes: the code table
   address, its complement, the count n - hdr_n n of the current message), the struct words w at sp + 24 (text,
   copy, the pointer array, the word count), the saved registers at sp + 56. *)

Definition MASK : Z := 0x100002600.
Definition GOT_NCODES : Z := 0x22d00.
Definition GOT_CODES : Z := 0x22d08.
Definition NCODES_A : Z := 0x10b80.

Definition SAVE (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition NOT_CODES : Z := 2 ^ 64 - 1 - REC_CODES.

Definition LOC0 (jsv : list byte) : list cell :=
  [C8 (Z_to_bv 64 REC_CODES); C8 (Z_to_bv 64 NOT_CODES); CB 8 jsv].

(* The message header at cursor (p, n), n > 0: hdr is the min(n, 3) bytes at p (fuzz_u8 / fuzz_u16). *)
Definition hdr_n (n : Z) : Z := Z.min n 3.
Definition hbyte (hdr : list byte) (k : nat) : Z := bv_unsigned (nth k hdr (Z_to_bv 8 0)).
Definition msg_len (n : Z) (hdr : list byte) : Z :=
  Z.min (Z.min (hbyte hdr 1 + 256 * hbyte hdr 2) (n - hdr_n n)) 8192.
Definition msg_rf (hdr : list byte) : Z := hbyte hdr 0 mod 2.
Definition msg_cd (hdr : list byte) : Z := nth (Z.to_nat ((hbyte hdr 0 / 2) mod 58)) rec_codes 0.

(* The size of the pointer array of words_of: ((L0 << 2) & ~7) + 16. *)
Definition arr_size (L0 : Z) : Z := 8 * (L0 / 2) + 16.

(* 0x14060 .. jal rec_clear (0x140a8), when a1 < 2^26: the saved registers at sp - 104, s1 = a1, s2 = a0. *)
Definition run_pro_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 160 <= bv_unsigned sp -> IMG_END <= lo ->
  bv_unsigned a1 < 2 ^ 26 ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' jl,
      ms' = MS (mkR (Z_to_bv 64 0x140ac) (Z_to_bv 64 (bv_unsigned sp - 160)) gp tp t0' t1' t2' s0 a1
                    a0' a1' a2' a3' a4' a5' a6' a7' a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x15ab4) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp - 160) [CB 56 jl] /\
      rw_cells rsegs m' (bv_unsigned sp - 104) (SAVE ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14060) fc None m (seg_rom rsegs)).

(* 0x14060 .. ret through 0x143f8, when a1 >= 2^26 (the size refusal: a0 = 0, the saved registers come back). *)
Definition run_big_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 160 <= bv_unsigned sp -> IMG_END <= lo ->
  2 ^ 26 <= bv_unsigned a1 ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14060) fc None m (seg_rom rsegs)).

(* 0x140ac (rec_clear returned) .. the loop head 0x140fc (s1 <> 0) or rec_clear's entry from the jal at 0x143e8
   (s1 = 0): writes g_rec.state = g_rec.host_settings = 0 through a4 = &g_rec, and (s1 <> 0) the code table address and
   its complement at sp, sp + 8, with s7 = 0, a2 = 1, a3 = 58 (the code count), s8 = MASK, s9 = 32, s11 = -1. *)
Definition run_init_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (jsh jl : list byte),
  mem_inv rsegs m ->
  IMG_END <= bv_unsigned sp -> bv_unsigned sp + 160 <= 2 ^ 64 ->
  bytes_at rsegs m GOT_GREC (le8 (Z_to_bv 64 G_REC)) ->
  bytes_at rsegs m GOT_NCODES (le8 (Z_to_bv 64 NCODES_A)) ->
  bytes_at rsegs m GOT_CODES (le8 (Z_to_bv 64 REC_CODES)) ->
  rw_cells rsegs m (G_REC + 944) [CB 16 jsh] ->
  rw_cells rsegs m (bv_unsigned sp) [CB 24 jl] ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' jl' jsv,
      munch [(bv_unsigned sp, bv_unsigned sp + 24); (G_REC + 944, G_REC + 960)] m m' /\ wmono rsegs m m' /\
      mem_inv rsegs m' /\
      rw_cells rsegs m' (G_REC + 944) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] /\
      rw_cells rsegs m' (bv_unsigned sp) [CB 24 jl'] /\
      ((bv_unsigned s1 = 0 /\
        ms' = MS (mkR (Z_to_bv 64 0x143ec) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x15ab4) fc None m' (seg_rom rsegs)) \/
       (bv_unsigned s1 <> 0 /\ rw_cells rsegs m' (bv_unsigned sp) (LOC0 jsv) /\
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' (Z_to_bv 64 1) (Z_to_bv 64 58) (Z_to_bv 64 G_REC)
                      a5' a6' a7' s2 s3 s4 s5 s6 (Z_to_bv 64 0) (Z_to_bv 64 MASK) (Z_to_bv 64 32) s10
                      (Z_to_bv 64 (2 ^ 64 - 1)) t3' t4' t5' t6')
                 F (Z_to_bv 64 0x140fc) fc None m' (seg_rom rsegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x140ac) fc None m (seg_rom rsegs)).

(* 0x143ec (the second rec_clear returned) .. ret: g_quitting = 0 through its GOT slot, a0 = 0, the saved
   registers at sp + 56 come back, sp = sp + 160. *)
Definition run_epi_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ra0 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : word) (jq : list byte),
  mem_inv rsegs m -> IMG_END <= bv_unsigned sp -> bv_unsigned sp + 160 <= 2 ^ 64 ->
  bytes_at rsegs m GOT_GQUIT (le8 (Z_to_bv 64 G_QUIT)) ->
  rw_cells rsegs m G_QUIT [CB 4 jq] ->
  rw_cells rsegs m (bv_unsigned sp + 56) (SAVE ra0 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) ->
  evt rsegs (fun ms' => exists a0' m',
      ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + 160)) gp tp t0 t1 t2 x0 x1 a0' a1 a2 a3 a4 a5 a6 a7
                    x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
      a0' = Z_to_bv 64 0 /\
      munch [(G_QUIT, G_QUIT + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' G_QUIT [C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x143ec) fc None m (seg_rom rsegs)).

(* The locals at sp once the loop head has stored k = n - hdr_n n at sp + 16 (0x14188; read back at 0x143d8). *)
Definition LOC1 (k : Z) : list cell :=
  [C8 (Z_to_bv 64 REC_CODES); C8 (Z_to_bv 64 NOT_CODES); C8 (Z_to_bv 64 k)].

(* The loop head 0x140fc (message mi at cursor (p, n), n > 0) .. jal send_message (0x141c0): decodes the header,
   writes g_rec.refuse and g_rec.code and k = n - hdr_n n at sp + 16, loads g_rec.state and g_rec.host_settings into
   s2 and s3, s6 = the code count 58, s10 = &g_rec. The check branches to 0x14438 at 0x14100, 0x1411c, 0x14140
   (p + 1, p + 2, p + 3 do not wrap), 0x14170 (p + hdr_n n + the length does not wrap), 0x14184 (the code count is not
   0) and 0x1419c (the code table offset does not wrap) are not taken. *)
Definition run_head_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a5 a6 a7 s3 s4 s5 s6 s10 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (mi p n : Z) (hdr jsv jrc : list byte) (sbw hbw : word),
  mem_inv rsegs m ->
  IMG_END <= bv_unsigned sp -> bv_unsigned sp + 160 <= 2 ^ 64 ->
  0 < n -> 0 < p -> p + n < 2 ^ 64 ->
  bytes_at rsegs m p hdr -> length hdr = Z.to_nat (hdr_n n) ->
  rw_cells rsegs m (bv_unsigned sp) (LOC0 jsv) ->
  rw_cells rsegs m G_REC [CB 8 jrc] ->
  bytes_at rsegs m (G_REC + 944) (le8 sbw) -> bytes_at rsegs m (G_REC + 952) (le8 hbw) ->
  evt rsegs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR (Z_to_bv 64 0x141c4) sp gp tp t0' t1' t2'
                    (Z_to_bv 64 (p + hdr_n n)) (Z_to_bv 64 (msg_len n hdr))
                    (Z_to_bv 64 (p + hdr_n n)) (Z_to_bv 64 (msg_len n hdr)) a2' a3' a4' a5' a6' a7'
                    sbw hbw s4 s5 (Z_to_bv 64 58) (Z_to_bv 64 mi) (Z_to_bv 64 MASK) (Z_to_bv 64 32)
                    (Z_to_bv 64 G_REC) (Z_to_bv 64 (2 ^ 64 - 1)) t3' t4' t5' t6')
             F (Z_to_bv 64 0x14444) fc None m' (seg_rom rsegs) /\
      munch [(G_REC, G_REC + 8); (bv_unsigned sp + 16, bv_unsigned sp + 24)] m m' /\ wmono rsegs m m' /\
      mem_inv rsegs m' /\
      rw_cells rsegs m' G_REC [C4 (Z_to_bv 64 (msg_rf hdr)); C4 (Z_to_bv 64 (msg_cd hdr))] /\
      rw_cells rsegs m' (bv_unsigned sp) (LOC1 (n - hdr_n n)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 (Z_to_bv 64 1) (Z_to_bv 64 58) (Z_to_bv 64 G_REC) a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 (Z_to_bv 64 mi) (Z_to_bv 64 MASK) (Z_to_bv 64 32) s10
             (Z_to_bv 64 (2 ^ 64 - 1)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x140fc) fc None m (seg_rom rsegs)).

(* 0x141c4 (send_message returned) .. strnlen entry: a0 = s0, a1 = s1. *)
Definition run_g_strnlen_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x141d0) sp gp tp t0 t1 t2 s0 s1 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x21110) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141c4) fc None m (seg_rom rsegs)).

(* 0x141d0 (strnlen returned L0) .. malloc entry: s4 = L0, s5 = a0 = L0 + 1. *)
Definition run_g_m0_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned a0 + 1 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x141e0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned a0 + 1)) a1 a2 a3 a4 a5 a6 a7
              s2 s3 a0 (Z_to_bv 64 (bv_unsigned a0 + 1)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x18c10) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141d0) fc None m (seg_rom rsegs)).

(* 0x141e0 (first malloc returned text) .. malloc entry: text at sp + 24, a0 = s5. *)
Definition run_g_m1_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j : list byte),
  mem_inv rsegs m -> IMG_END <= bv_unsigned sp -> bv_unsigned sp + 160 <= 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp + 24) [CB 8 j] ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x141ec) sp gp tp t0 t1 t2 s0 s1 s5 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x18c10) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp + 24, bv_unsigned sp + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp + 24) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141e0) fc None m (seg_rom rsegs)).

(* 0x141ec (second malloc returned copy) .. malloc entry: copy at sp + 32, a0 = arr_size L0 (s4 = L0). *)
Definition run_g_m2_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j : list byte) (L0 : Z),
  mem_inv rsegs m -> IMG_END <= bv_unsigned sp -> bv_unsigned sp + 160 <= 2 ^ 64 ->
  0 <= L0 <= 8192 ->
  rw_cells rsegs m (bv_unsigned sp + 32) [CB 8 j] ->
  evt rsegs (fun ms' => exists a0' m',
      ms' = MS (mkR (Z_to_bv 64 0x14200) sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                    s2 s3 (Z_to_bv 64 L0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x18c10) fc None m' (seg_rom rsegs) /\
      a0' = Z_to_bv 64 (arr_size L0) /\
      munch [(bv_unsigned sp + 32, bv_unsigned sp + 40)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp + 32) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 L0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141ec) fc None m (seg_rom rsegs)).

(* 0x14380 (check_reply returned) .. check_arity entry: a0 = &w = sp + 24. *)
Definition run_g_ca_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned sp + 24 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x14388) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 24)) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x14614) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14380) fc None m (seg_rom rsegs)).

(* 0x14388 (check_arity returned) .. check_words entry: a0 = &w. *)
Definition run_g_cw_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned sp + 24 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x14390) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 24)) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x14bac) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14388) fc None m (seg_rom rsegs)).

(* 0x14390 (check_words returned) .. check_refusal entry: a0 = s2. *)
Definition run_g_cr_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x14398) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x14efc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14390) fc None m (seg_rom rsegs)).

(* 0x14398 (check_refusal returned) .. check_round_trip entry: a0 = &w, a1 = s2, a2 = s3. *)
Definition run_g_crt_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned sp + 24 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x143a8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 24)) s2 s3 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x14f60) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14398) fc None m (seg_rom rsegs)).

(* 0x143a8, 0x143b0, 0x143b8 .. free entry with a0 = text, copy, arr (loaded from sp + 24, + 32, + 40). *)
Definition run_g_f1_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (x1 x2 x3 : word),
  IMG_END <= bv_unsigned sp -> bv_unsigned sp + 160 <= 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp + 24) [C8 x1; C8 x2; C8 x3] ->
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x143b0) sp gp tp t0 t1 t2 s0 s1 x1 a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x143a8) fc None m (seg_rom rsegs)).

Definition run_g_f2_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (x1 x2 x3 : word),
  IMG_END <= bv_unsigned sp -> bv_unsigned sp + 160 <= 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp + 24) [C8 x1; C8 x2; C8 x3] ->
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x143b8) sp gp tp t0 t1 t2 s0 s1 x2 a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x143b0) fc None m (seg_rom rsegs)).

Definition run_g_f3_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (x1 x2 x3 : word),
  IMG_END <= bv_unsigned sp -> bv_unsigned sp + 160 <= 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp + 24) [C8 x1; C8 x2; C8 x3] ->
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x143c0) sp gp tp t0 t1 t2 s0 s1 x3 a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x143b8) fc None m (seg_rom rsegs)).

(* 0x143c0 (the third free returned) .. the next loop head (s7 <= 30 and s1 < k: a2 = 1, a3 = s6, a4 = s10,
   s2 = s0 + s1, s1 = k - s1, s7 = s7 + 1) or rec_clear's entry from the jal at 0x143e8 (ra 0x143ec). k is the count
   at sp + 16. *)
Definition run_tail_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (k : Z),
  IMG_END <= bv_unsigned sp -> bv_unsigned sp + 160 <= 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp) (LOC1 k) ->
  bv_unsigned s1 <= k < 2 ^ 64 -> bv_unsigned s0 + bv_unsigned s1 < 2 ^ 64 ->
  evt rsegs (fun ms' =>
      (bv_unsigned s7 <= 30 /\ bv_unsigned s1 < k /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (k - bv_unsigned s1)) (Z_to_bv 64 k) a1 (Z_to_bv 64 1) s6 s10
                     a5 a6 a7 (Z_to_bv 64 (bv_unsigned s0 + bv_unsigned s1)) s3 s4 s5 s6
                     (Z_to_bv 64 (bv_unsigned s7 + 1)) s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x140fc) fc None m (seg_rom rsegs)) \/
      ((30 < bv_unsigned s7 \/ bv_unsigned s1 = k) /\
       exists a0' a2' a3' a4' s1' s2' s7',
       ms' = MS (mkR (Z_to_bv 64 0x143ec) sp gp tp t0 t1 t2 s0 s1' a0' a1 a2' a3' a4' a5 a6 a7
                     s2' s3 s4 s5 s6 s7' s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15ab4) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x143c0) fc None m (seg_rom rsegs)).
