(* the statements of the instruction segments of check_round_trip in fuzz_frame.ubsan, which the walk proves and joins. *)
(* The instruction segments of check_round_trip in fuzz_frame.ubsan (0x131e4, 796 bytes,
   fuzz/fuzz_frame.c:114-200), stated over Exec.evt, between the calls of malloc (0x14f2c) and
   free (0x14dec). U/Prog/crt_top.v joins them with the allocator contracts; the UBSan twin of
   Prog/crt_defs.v.
   The segments:
   - crt_seg1: 0x131e4 .. the jal of malloc at 0x1322c (prologue, the alignment check of w,
               n_want);
   - crt_seg2: 0x13230 .. the jal of malloc at 0x1323c (out);
   - crt_m1:   0x13240 .. 0x1333c (the header h at sp, the inlined spec_system_at with its
               UBSan checks, memset of out with 0xa5, diginet_frame_build in mode 0);
   - crt_m2:   0x1333c .. 0x133c4 (the three tests of the answer, spec_build_frame into want
               with zero_sum 0, bcmp of out and want);
   - crt_m3:   0x133c4 .. either 0x134bc (the body is not built: free of want) or the jal of
               malloc at 0x1344c (spec_build_frame with zero_sum 1, the zero-sum build and its
               bcmp, then shy);
   - crt_mid:  crt_m1, crt_m2 and crt_m3 together;
   - crt_shy:  0x13450 .. the jal of free at 0x134b8 (memset of shy with 0x5a,
               diginet_frame_build with the cap n_want - 1, the test of each byte of shy with
               its UBSan check);
   - crt_segf1: 0x134bc .. the jal of free at 0x134c0 (want);
   - crt_segf2: 0x134c4 .. the jal of free at 0x134c8 (out);
   - crt_segx: 0x134cc .. ret (the epilogue).
   The stack frame is 80 bytes at sp: the header h in the 16 bytes at sp, then s6 .. s0 and ra
   (crt_saved). h + 4, at sp + 4, holds crt_hb b: the 12 bytes that diginet_frame_build reads.
   The function does not use s7 .. s11: each segment keeps them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import check_parse_fields_c memset_c bcmp_c
  diginet_frame_build_c spec_build_frame_c.
Import ListNotations.
Open Scope Z_scope.

Definition CRT_MALLOC : Z := 0x14f2c.
Definition CRT_FREE : Z := 0x14dec.

(* The saved registers in the frame, at sp + 0x10 .. sp + 0x50. *)
Definition crt_saved (ra s0 s1 s2 s3 s4 s5 s6 : word) : list cell :=
  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* h->send_counter, ack_counter, retry, cmd, num_commands (h + 4 .. h + 16). *)
Definition crt_hb (b : list byte) : list byte :=
  Z_to_le_bytes 4 (fr_send b) ++ Z_to_le_bytes 4 (fr_ack b) ++ Z_to_le_bytes 2 (fr_retry b) ++
  [b8 (fr_cmd b); b8 (fr_ncmds b)].

(* fits && !sys (fuzz_frame.c:127-128): the frame is built, and the zero-sum branch runs. *)
Definition crt_ok (b : list byte) : bool :=
  (Z.of_nat (length (fr_body b)) <=? 1484) && negb (system_at (fr_body b)).

(* s6 after the inlined spec_system_at: sys as 0 or 1. *)
Definition crt_sys (b : list byte) : Z := if system_at (fr_body b) then 1 else 0.

(* The places: buf (blen bytes, the input), out and want (n bytes each, from malloc), all below
   the 240 bytes under sp that diginet_frame_build uses; w (80 bytes) in the caller's frame;
   sp 8-aligned (diginet_frame_build reads h at sp, 4-aligned, and needs its sp 8-aligned). *)
Definition crt_lay (sp w buf out want n blen : Z) : Prop :=
  0 < buf /\ buf + blen <= sp - 240 /\
  0 < out /\ out + n <= sp - 240 /\
  0 < want /\ want + n <= sp - 240 /\
  (out + n <= want \/ want + n <= out) /\
  (out + n <= buf \/ buf + blen <= out) /\
  (want + n <= buf \/ buf + blen <= want) /\
  sp + 80 <= w /\ w + 80 <= 2 ^ 64 /\ sp mod 8 = 0.

Definition crt_lay_shy (sp w buf shy n blen : Z) : Prop :=
  0 < buf /\ buf + blen <= sp - 240 /\
  0 < shy /\ shy + (n - 1) <= sp - 240 /\
  (shy + (n - 1) <= buf \/ buf + blen <= shy) /\
  sp + 80 <= w /\ w + 80 <= 2 ^ 64 /\ sp mod 8 = 0.

(** * 0x131e4 .. jal malloc (0x1322c) *)

Definition crt_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (w n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x13230) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n)
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CRT_MALLOC) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
    rw_cells rsegs m1 (bv_unsigned sp - 80) (CB 16 junk :: crt_saved ra s0 s1 s2 s3 s4 s5 s6).

Definition crt_seg1_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (w buf lo : Z) (b : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp ->
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 ->
    bv_unsigned sp <= w -> w mod 8 = 0 -> ro_cells rsegs m w (spec_cells buf b) ->
    evt rsegs (crt_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc w (frame_len (length (fr_body b))) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 w) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x131e4) fc None m (seg_rom rsegs)).

(** * 0x13230 .. jal malloc (0x1323c) *)

Definition crt_seg2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (out : Z),
    0 < out < 2 ^ 64 ->
    evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13240) sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1 s3 a1 a2 a3 a4
                                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CRT_MALLOC) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 out) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x13230) fc None m (seg_rom rsegs)).

(** * 0x13240 .. 0x1333c *)

Definition crt_m1_post (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (w out want n : Z)
    (b : list byte) (sv : list cell) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (j : list byte)
                    (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 want)
               (Z_to_bv 64 (build_code (fr_body b) n)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) (Z_to_bv 64 n) s4
               (Z_to_bv 64 (Z.of_nat (length (fr_body b)))) (Z_to_bv 64 (crt_sys b)) s7 s8 s9 s10 s11
               t3 t4 t5 t6)
             F (Z_to_bv 64 0x1333c) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 240, bv_unsigned sp + 80); (out, out + n)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (bv_unsigned sp) (CB 4 j :: CB 12 (crt_hb b) :: sv) /\
    rw_cells rsegs m' out [CB (Z.to_nat n) (build_out (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                             (fr_cmd b) (fr_ncmds b) (fr_body b) 0 (repeat (b8 0xa5) (Z.to_nat n)))] /\
    stk rsegs m' (bv_unsigned sp - 240) (bv_unsigned sp).

Definition crt_m1_stmt : Prop :=
  memset_contract -> diginet_frame_build_contract ->
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (w buf out want n : Z) (b j : list byte) (sv : list cell),
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 -> n = frame_len (length (fr_body b)) ->
    crt_lay (bv_unsigned sp) w buf out want n (Z.of_nat (length b)) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    bytes_at rsegs m buf b ->
    stk rsegs m out (out + n) ->
    stk rsegs m (bv_unsigned sp - 240) (bv_unsigned sp) ->
    length j = 16%nat -> cells_size sv = 64%nat ->
    rw_cells rsegs m (bv_unsigned sp) (CB 16 j :: sv) ->
    mem_inv rsegs m ->
    evt rsegs (crt_m1_post sp gp tp s7 s8 s9 s10 s11 F fc w out want n b sv m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1 (Z_to_bv 64 want) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w)
               (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13240) fc None m (seg_rom rsegs)).

(** * 0x1333c .. 0x133c4 *)

Definition crt_m2_post (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (w out want n : Z)
    (b : list byte) (sv : list cell) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (j : list byte)
                    (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 want) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w)
               (Z_to_bv 64 n) s4 (Z_to_bv 64 n) (Z_to_bv 64 (if crt_ok b then 0 else 1)) s7 s8 s9 s10 s11
               t3 t4 t5 t6)
             F (Z_to_bv 64 0x133c4) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 240, bv_unsigned sp); (want, want + n)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (bv_unsigned sp) (CB 4 j :: CB 12 (crt_hb b) :: sv) /\
    rw_cells rsegs m' out [CB (Z.to_nat n) (build_out (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                             (fr_cmd b) (fr_ncmds b) (fr_body b) 0 (repeat (b8 0xa5) (Z.to_nat n)))] /\
    rw_cells rsegs m' want [CB (Z.to_nat n) (build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                              (fr_cmd b) (fr_ncmds b) (fr_body b) false)] /\
    stk rsegs m' (bv_unsigned sp - 240) (bv_unsigned sp).

Definition crt_m2_stmt : Prop :=
  bcmp_contract -> spec_build_frame_contract ->
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (w buf out want n : Z) (b j : list byte) (sv : list cell),
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 -> n = frame_len (length (fr_body b)) ->
    crt_lay (bv_unsigned sp) w buf out want n (Z.of_nat (length b)) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    bytes_at rsegs m buf b ->
    rw_cells rsegs m out [CB (Z.to_nat n) (build_out (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                            (fr_cmd b) (fr_ncmds b) (fr_body b) 0 (repeat (b8 0xa5) (Z.to_nat n)))] ->
    stk rsegs m want (want + n) ->
    stk rsegs m (bv_unsigned sp - 240) (bv_unsigned sp) ->
    cells_size sv = 64%nat ->
    rw_cells rsegs m (bv_unsigned sp) (CB 4 j :: CB 12 (crt_hb b) :: sv) ->
    mem_inv rsegs m ->
    evt rsegs (crt_m2_post sp gp tp s7 s8 s9 s10 s11 F fc w out want n b sv m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 want) (Z_to_bv 64 (build_code (fr_body b) n))
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) (Z_to_bv 64 n) s4
               (Z_to_bv 64 (Z.of_nat (length (fr_body b)))) (Z_to_bv 64 (crt_sys b)) s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x1333c) fc None m (seg_rom rsegs)).

(** * 0x133c4 .. 0x134bc or jal malloc (0x1344c) *)

(* The end of crt_m3 and of crt_mid. When crt_ok b is false the walk is at 0x134bc (free of
   want); else at malloc, with ra 0x13450 and n_want - 1 in a0 and s3. *)
Definition crt_mid_post (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (w out want n : Z)
    (b : list byte) (sv : list cell) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 t3 t4 t5 t6 pc : word) (j : list byte)
                    (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 want) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w)
               s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F pc fc None m' (seg_rom rsegs) /\
    ((crt_ok b = false /\ pc = Z_to_bv 64 0x134bc) \/
     (crt_ok b = true /\ pc = Z_to_bv 64 CRT_MALLOC /\ ra' = Z_to_bv 64 0x13450 /\
      a0 = Z_to_bv 64 (n - 1) /\ s3 = Z_to_bv 64 (n - 1))) /\
    munch [(bv_unsigned sp - 240, bv_unsigned sp + 80); (out, out + n); (want, want + n)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (bv_unsigned sp) (CB 4 j :: CB 12 (crt_hb b) :: sv).

Definition crt_m3_stmt : Prop :=
  memset_contract -> bcmp_contract -> diginet_frame_build_contract -> spec_build_frame_contract ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (w buf out want n : Z) (b j jo jw : list byte) (sv : list cell),
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 -> n = frame_len (length (fr_body b)) ->
    crt_lay (bv_unsigned sp) w buf out want n (Z.of_nat (length b)) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    bytes_at rsegs m buf b ->
    rw_cells rsegs m out [CB (Z.to_nat n) jo] ->
    rw_cells rsegs m want [CB (Z.to_nat n) jw] ->
    stk rsegs m (bv_unsigned sp - 240) (bv_unsigned sp) ->
    cells_size sv = 64%nat ->
    rw_cells rsegs m (bv_unsigned sp) (CB 4 j :: CB 12 (crt_hb b) :: sv) ->
    mem_inv rsegs m ->
    evt rsegs (crt_mid_post sp gp tp s7 s8 s9 s10 s11 F fc w out want n b sv m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 want) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w)
               (Z_to_bv 64 n) s4 (Z_to_bv 64 n) (Z_to_bv 64 (if crt_ok b then 0 else 1)) s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x133c4) fc None m (seg_rom rsegs)).

(** * 0x13240 .. 0x134bc or jal malloc (0x1344c): crt_m1, crt_m2, crt_m3 *)

Definition crt_mid_stmt : Prop :=
  memset_contract -> bcmp_contract -> diginet_frame_build_contract -> spec_build_frame_contract ->
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (w buf out want n : Z) (b j : list byte) (sv : list cell),
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 -> n = frame_len (length (fr_body b)) ->
    crt_lay (bv_unsigned sp) w buf out want n (Z.of_nat (length b)) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    bytes_at rsegs m buf b ->
    stk rsegs m out (out + n) -> stk rsegs m want (want + n) ->
    stk rsegs m (bv_unsigned sp - 240) (bv_unsigned sp) ->
    length j = 16%nat -> cells_size sv = 64%nat ->
    rw_cells rsegs m (bv_unsigned sp) (CB 16 j :: sv) ->
    mem_inv rsegs m ->
    evt rsegs (crt_mid_post sp gp tp s7 s8 s9 s10 s11 F fc w out want n b sv m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1 (Z_to_bv 64 want) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w)
               (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13240) fc None m (seg_rom rsegs)).

(** * 0x13450 .. jal free (0x134b8) *)

Definition crt_shy_post (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (w shy want out n : Z)
    (b j : list byte) (sv : list cell) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x134bc) sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 want) (Z_to_bv 64 shy)
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CRT_FREE) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 240, bv_unsigned sp); (shy, shy + (n - 1))] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (bv_unsigned sp) (CB 4 j :: CB 12 (crt_hb b) :: sv).

Definition crt_shy_stmt : Prop :=
  memset_contract -> diginet_frame_build_contract ->
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (w buf shy want out n : Z) (b j : list byte) (sv : list cell),
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 -> n = frame_len (length (fr_body b)) -> crt_ok b = true ->
    crt_lay_shy (bv_unsigned sp) w buf shy n (Z.of_nat (length b)) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    bytes_at rsegs m buf b ->
    stk rsegs m shy (shy + (n - 1)) ->
    stk rsegs m (bv_unsigned sp - 240) (bv_unsigned sp) ->
    cells_size sv = 64%nat ->
    rw_cells rsegs m (bv_unsigned sp) (CB 4 j :: CB 12 (crt_hb b) :: sv) ->
    mem_inv rsegs m ->
    evt rsegs (crt_shy_post sp gp tp s7 s8 s9 s10 s11 F fc w shy want out n b j sv m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 want) (Z_to_bv 64 shy) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 w) (Z_to_bv 64 (n - 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13450) fc None m (seg_rom rsegs)).

(** * 0x134bc .. jal free (0x134c0); 0x134c4 .. jal free (0x134c8); 0x134cc .. ret *)

Definition crt_segf1_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x134c4) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CRT_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x134bc) fc None m (seg_rom rsegs)).

Definition crt_segf2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x134cc) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CRT_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x134c4) fc None m (seg_rom rsegs)).

Definition crt_segx_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j h : list byte)
         (vra v0 v1 v2 v3 v4 v5 v6 : word),
    rw_cells rsegs m (bv_unsigned sp) (CB 4 j :: CB 12 h :: crt_saved vra v0 v1 v2 v3 v4 v5 v6) ->
    evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 80)) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4
                                       a5 a6 a7 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x134cc) fc None m (seg_rom rsegs)).
