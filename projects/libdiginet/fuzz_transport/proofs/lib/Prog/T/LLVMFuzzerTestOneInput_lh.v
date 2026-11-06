(* The program points of LLVMFuzzerTestOneInput's op loop in the plain image, as machine-state predicates:
   the loop head 0x138ac (read the op byte at the cursor), the nine case entries the switch dispatches to,
   the latch 0x1428c (the pass counter test) and the exit 0x14320. The per-op step lemmas go case -> latch;
   LLVMFuzzerTestOneInput.v binds them with the dispatch lemma and the latch.

   The registers at the head, from the entry (0x13664-0x138ac) and the latch (0x14294-0x142a0):
     s4  the cursor: the address of the next input byte (data + fi_off c)
     s7  the cursor's n (fi_n c), nonzero at the head (the latch leaves when it is 0)
     s11 the pass counter ops, 0 at the first head, < OPS_MAX at every head
     s9  W_BASE_PLAIN + OFF_g_fail_next (&g_fail_next; the harness globals are read off it)
     s10 W_BASE_PLAIN + OFF_M           (&M)
     s5  W_BASE_PLAIN + OFF_g_s         (&g_s)
     s8 = 1, s2 = 0x39 (the 57 of the byte / 9 sequence), s1 = 7 (the switch bound)
   and the frame slots the loop reads: sp + 0x00 = 2^32 - 3, sp + 0x08 = &g_s. The 13 saved registers are at
   sp + 0x78 .. sp + 0xd8, the caller's values. The frame's 224 bytes, in cells: sp + 0x00 and sp + 0x08 the
   two constants the loop keeps (llvm_frame_consts), sp + 0x10 eight bytes of scratch, sp + 0x18 = 0x610f and
   sp + 0x20 = 0xffff, which the loop entry stores (0x13894, 0x138a4) and case 4 reads (0x13ec0), sp + 0x28
   .. sp + 0x77 the scratch the ops write, then the 13 saved registers. (The last three cells were measured
   with case 4's walk, LLVMFuzzerTestOneInput_op4k.v.) *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract.
Import ListNotations.
Open Scope Z_scope.

Definition LLVM_ENTRY_PC : Z := 0x13664.
Definition LLVM_HEAD_PC : Z := 0x138ac.
Definition LLVM_LATCH_PC : Z := 0x1428c.
Definition LLVM_OUT_PC : Z := 0x14320.

(* the switch (0x138d0-0x138ec): op < 8 takes the table at 0x10408, op = 8 the branch at 0x138d0 *)
Definition LLVM_CASE (i : Z) : Z :=
  if i =? 0 then 0x138f0 else if i =? 1 then 0x139ec else if i =? 2 then 0x139a4
  else if i =? 3 then 0x139cc else if i =? 4 then 0x13910 else if i =? 5 then 0x13a10
  else if i =? 6 then 0x13a64 else if i =? 7 then 0x139e4 else 0x13ac0.

(* the deepest callee window below the loop's own frame: build_and_receive 9856 *)
Definition LLVM_LOOP_K : Z := 9856.

(* LLVMFuzzerTestOneInput's own frame: addi sp, sp, -0xe0 at 0x13664 *)
Definition LLVM_FRAME : Z := 224.

(* The 13 saved registers of the frame, at sp + 0x78: s11 .. ra, in store order. *)
Definition llvm_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* The two constants the loop keeps in its frame, at sp + 0x00 and sp + 0x08. *)
Definition llvm_frame_consts : list cell :=
  [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))].

Section LH.
Context (data : Z) (D : list byte).

(* The cursor of fuzz.h as the machine keeps it: the address of the next byte and the count left. *)
Definition llvm_cursor (c : fuzz_in) : Prop :=
  0 <= fi_off c /\ 0 <= fi_n c /\ fi_off c + fi_n c <= Z.of_nat (length D) /\
  Z.of_nat (length D) < FUZZ_INPUT_MAX.

(* Everything the loop asks of memory, at every one of its program points: the input buffer, the stack window
   of the frame and its callees, the world, and the frame's own cells. The scratch bytes (sp + 0x10, sp + 0x28)
   are junk: each op writes its own. *)
(* The one footprint the whole walk keeps to: its own frame, its callees' windows and the world. The SR glue's
   g_run asks every evt segment for a munch over it, so llvm_mem carries one from a reference memory m0 (the
   memory the segment started from) and every step of the walk extends it. *)
Definition LLVM_FP (Sp : Z) : list ivl :=
  [(Sp - LLVM_LOOP_K, Sp + LLVM_FRAME); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)].

Definition llvm_mem (Sp lo : Z) (B : list byte) (m0 m : word -> option byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j10 j28 : list byte) : Prop :=
  munch (LLVM_FP Sp) m0 m /\ wmono rsegs m0 m /\
  bytes_at rsegs m data D /\
  Sp mod 16 = 0 /\ stk rsegs m lo Sp /\ lo + LLVM_LOOP_K <= Sp /\ Sp + LLVM_FRAME < 2 ^ 63 /\
  w_off_stack W_BASE_PLAIN (Z_to_bv 64 Sp) LLVM_LOOP_K /\ W_BASE_PLAIN + W_LEN <= lo /\
  off_world data (Z.of_nat (length D)) /\
  off_window (Z_to_bv 64 (Sp + LLVM_FRAME)) (LLVM_LOOP_K + LLVM_FRAME) data (Z.of_nat (length D)) /\
  mem_inv rsegs m /\ relro_img m /\ wmem rsegs m B /\ g_fail_next B <= 1 /\
  length j10 = 8%nat /\ length j28 = 80%nat /\
  rw_cells rsegs m Sp (llvm_frame_consts ++
                       [CB 8 j10; C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); CB 80 j28] ++
                       llvm_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

(* The state at the loop head 0x138ac after `ops` passes, with the world B and the cursor c. *)
Definition llvm_head (m0 : word -> option byte) (gp tp : word) (Sp lo ops : Z) (c : fuzz_in) (B : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r8 r19 r22 t3 t4 t5 t6 : word)
         (m : word -> option byte) (j10 j28 : list byte),
    ms = MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2 r8 (Z_to_bv 64 7) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) r19 (Z_to_bv 64 (data + fi_off c)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
                 r22 (Z_to_bv 64 (fi_n c)) (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 LLVM_HEAD_PC) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ fi_n c <> 0 /\ llvm_cursor c /\
    llvm_mem Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28.

(* The state at the entry of the case for op `i`: the op byte is read and classified, s3 / s6 hold the cursor
   after it (fuzz_u8_m's c1), s4 / s7 still the cursor before. a0 .. a2 are the switch's own scratch. *)
Definition llvm_case (m0 : word -> option byte) (gp tp : word) (i : Z) (Sp lo ops : Z) (c c1 : fuzz_in) (B : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r8 t3 t4 t5 t6 : word)
         (m : word -> option byte) (j10 j28 : list byte),
    ms = MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2 r8 (Z_to_bv 64 7) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c1)) (Z_to_bv 64 (data + fi_off c))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (fi_n c1)) (Z_to_bv 64 (fi_n c))
                 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 (LLVM_CASE i)) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ fi_n c <> 0 /\ llvm_cursor c /\ c1 = fst (fuzz_u8_m D c) /\
    llvm_mem Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28.

(* The state at the latch 0x1428c: the pass is over; s3 is the cursor after it, s6 its n, s11 the pass counter
   before the increment. The next head takes s4 / s7 from s3 / s6 at 0x14298 / 0x1429c. *)
Definition llvm_latch (m0 : word -> option byte) (gp tp : word) (Sp lo ops : Z) (c : fuzz_in) (B : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r8 r20 r23 t3 t4 t5 t6 : word)
         (m : word -> option byte) (j10 j28 : list byte),
    ms = MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2 r8 (Z_to_bv 64 7) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c)) r20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
                 (Z_to_bv 64 (fi_n c)) r23 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 LLVM_LATCH_PC) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ llvm_cursor c /\
    llvm_mem Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28.

(* The state at the exit 0x14320, before the epilogue restores the 13 registers and returns 0. *)
Definition llvm_out (m0 : word -> option byte) (gp tp : word) (Sp lo : Z) (B : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
          t3 t4 t5 t6 : word) (m : word -> option byte) (j10 j28 : list byte),
    ms = MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2 r8 r9 a0 a1 a2 a3 a4 a5 a6 a7
                 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3 t4 t5 t6)
            F (Z_to_bv 64 LLVM_OUT_PC) fc None m (seg_rom rsegs) /\
    llvm_mem Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28.

End LH.
