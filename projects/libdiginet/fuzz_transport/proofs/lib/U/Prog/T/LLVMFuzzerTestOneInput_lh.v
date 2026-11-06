(* The program points of LLVMFuzzerTestOneInput in the ubsan image (0x13760, 4300 bytes; addi sp,sp,-240), as
   machine-state predicates, and the statements of the pieces of its walk (one Prop per piece). Each piece is
   proved in its own file (U/Prog/T/LLVMFuzzerTestOneInput_<piece>.v); U/Prog/T/LLVMFuzzerTestOneInput.v binds them
   with the SR glue (receive and build_and_receive are SR calls, every other callee an evt contract).

   The registers at the loop head 0x139dc (from the entry 0x13760-0x139d8 and the latch 0x14574-0x14588):
     s5  the cursor: the address of the next input byte (data + fi_off c)
     s7  the cursor's n (fi_n c), nonzero at the head (the latch leaves when it is 0)
     s11 the pass counter ops, 0 at the first head, < OPS_MAX at every head
     s1 = 1, s2 = 0x39 (the 57 of the byte / 9 sequence), s4 = 7 (the switch bound)
     s8  W_BASE_UBSAN + OFF_M = 0x33300 (&M), s9 W_BASE_UBSAN + OFF_g_fail_next = 0x430c8 (&g_fail_next; the harness
         scalars are read off it), s10 W_BASE_UBSAN + OFF_g_s = 0x33970 (&g_s)
     gp, tp the entry's (reg_get regs0 3, reg_get regs0 4; never written)
   The frame [Sp, Sp + 240), Sp = the entry sp - 240 (llvm_frame):
     sp+0x00 &g_s (reloaded into s10 after op 4), sp+0x08 2^32 - 3, sp+0x10 16 scratch bytes (op 4),
     sp+0x20 0x610f, sp+0x28 0xffff (op 1's and op 4's % constants), sp+0x30 ~(sp + 0x60), sp+0x38 -(sp + 0x60)
     (the UBSan pointer-overflow bounds of the stack buffer at sp+0x60), sp+0x40 the 32-byte struct diginet_io
     handed to diginet_session_init (dead after it: the session copies it, s->io = *io), sp+0x60 40 scratch bytes
     (op 2's announce body, op 4's struct diginet_cmd), sp+0x88 the 13 saved registers s11 .. s0, ra.
   The switch (0x139e4-0x13a20): op = b mod 9 by mul 57 / srli 9 / subw / subw / andi 255; op 8 branches to
   0x13c44, ops 0-7 jump through the table at 0x10418.
   Callee windows below Sp: build_and_receive 9936 (the deepest; receive 8320, every session function <= 3824). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract.
Import ListNotations.
Open Scope Z_scope.

Definition LH_ENTRY : Z := 0x13760.
Definition LH_HEAD : Z := 0x139dc.
Definition LH_LATCH : Z := 0x14574.
Definition LH_OUT : Z := 0x145e8.
Definition LH_RECV : Z := 0x14d1c.        (* receive_ENTRY, U/Prog/T/receive_c.v *)
Definition LH_BAR : Z := 0x161ac.         (* build_and_receive_ENTRY, U/Prog/T/build_and_receive_c.v *)
Definition LH_RET_RECV : Z := 0x13f70.    (* the return address of receive (ops 0, 8, jal at 0x13f6c) *)
Definition LH_RET_BAR1 : Z := 0x13db0.    (* the return address of build_and_receive in op 1 (jal at 0x13dac) *)
Definition LH_RET_BAR2 : Z := 0x140c4.    (* the return address of build_and_receive in op 2 (jal at 0x140c0) *)

(* the case entries: the jump table at 0x10418 for ops 0-7, the branch at 0x13a04 for op 8 *)
Definition LH_CASE (i : Z) : Z :=
  if i =? 0 then 0x13a24 else if i =? 1 then 0x13b38 else if i =? 2 then 0x13ab8
  else if i =? 3 then 0x13af8 else if i =? 4 then 0x13a48 else if i =? 5 then 0x13b74
  else if i =? 6 then 0x13bcc else if i =? 7 then 0x13b30 else 0x13c44.

Definition LH_FRAME : Z := 240.           (* addi sp, sp, -0xf0 at 0x13760 *)
Definition LH_K : Z := 9936.              (* build_and_receive_FRAME: the deepest callee window below Sp *)

(* The address stream of the model (the text of U/Prog/T/LLVMFuzzerTestOneInput_c.v llvm_heap_ok). *)
Definition lh_heap_ok (A : nat -> Z) : Prop :=
  forall k : nat, Z.of_nat k < OPS_MAX -> 0 < A k /\ A k + 65536 <= 2 ^ 64.

(* The 13 registers the prologue saves at sp + 0x88 .. sp + 0xe8, in address order (s11 first, ra last), as the
   entry's register file regs0 holds them. *)
Definition llvm_saved (regs0 : bvmap 5 word) : list cell :=
  [C8 (reg_get regs0 27); C8 (reg_get regs0 26); C8 (reg_get regs0 25); C8 (reg_get regs0 24);
   C8 (reg_get regs0 23); C8 (reg_get regs0 22); C8 (reg_get regs0 21); C8 (reg_get regs0 20);
   C8 (reg_get regs0 19); C8 (reg_get regs0 18); C8 (reg_get regs0 9); C8 (reg_get regs0 8);
   C8 (reg_get regs0 1)].

(* The loop's frame [Sp, Sp + 240). *)
Definition llvm_frame (regs0 : bvmap 5 word) (Sp : Z) (j10 jio j60 : list byte) : list cell :=
  [C8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)); C8 (Z_to_bv 64 (2 ^ 32 - 3)); CB 16 j10;
   C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
   C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))); C8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96)));
   CB 32 jio; CB 40 j60] ++ llvm_saved regs0.

Section LH.
Context (data : Z) (D : list byte) (regs0 : bvmap 5 word).

(* The cursor of fuzz.h as the machine keeps it: the address of the next byte and the count left. *)
Definition llvm_cursor (c : fuzz_in) : Prop :=
  0 <= fi_off c /\ 0 <= fi_n c /\ fi_off c + fi_n c <= Z.of_nat (length D).

(* Everything the loop asks of memory at each of its program points. m0 is the memory at the start of the current
   run segment: the walk wrote only its window [lo, Sp + 240) (callee windows and its own frame) and the world since.
   The input buffer is a heap block below the window, off the world. *)
Definition llvm_mem (m0 : word -> option byte) (Sp lo : Z) (B : list byte) (m : word -> option byte)
    (j10 jio j60 : list byte) : Prop :=
  0 < data /\ data + Z.of_nat (length D) <= lo /\ off_world data (Z.of_nat (length D)) /\
  bytes_at rsegs m data D /\
  Sp mod 16 = 0 /\ stk rsegs m lo Sp /\ lo + LH_K <= Sp /\ Sp + LH_FRAME <= 2 ^ 63 /\
  W_BASE_UBSAN + W_LEN <= lo /\
  mem_inv rsegs m /\ relro_img m /\ wmem rsegs m B /\ g_fail_next B <= 1 /\
  munch [(lo, Sp + LH_FRAME); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m /\ wmono rsegs m0 m /\
  length j10 = 16%nat /\ length jio = 32%nat /\ length j60 = 40%nat /\
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60).

(* The loop head 0x139dc after `ops` passes, with the world B and the cursor c. *)
Definition llvm_head (m0 : word -> option byte) (Sp lo ops : Z) (c : fuzz_in) (B : list byte)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 t3 t4 t5 t6 : word)
         (m : word -> option byte) (j10 jio j60 : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) s3 (Z_to_bv 64 7) (Z_to_bv 64 (data + fi_off c)) s6 (Z_to_bv 64 (fi_n c))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 LH_HEAD) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ fi_n c <> 0 /\ llvm_cursor c /\
    llvm_mem m0 Sp lo B m j10 jio j60.

(* The entry of the case for op i = (the byte at the cursor) mod 9: s3 / s6 hold the cursor after that byte
   (fuzz_u8_m's c1), s5 / s7 still the cursor before. *)
Definition llvm_case (i : Z) (m0 : word -> option byte) (Sp lo ops : Z) (c c1 : fuzz_in) (B : list byte)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (m : word -> option byte) (j10 jio j60 : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c1)) (Z_to_bv 64 7) (Z_to_bv 64 (data + fi_off c))
                 (Z_to_bv 64 (fi_n c1)) (Z_to_bv 64 (fi_n c))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 (LH_CASE i)) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ fi_n c <> 0 /\ llvm_cursor c /\
    c1 = fst (fuzz_u8_m D c) /\ snd (fuzz_u8_m D c) mod 9 = i /\
    llvm_mem m0 Sp lo B m j10 jio j60.

(* The latch 0x14574 (after the op's settle): the pass is over; s3 is the cursor after it, s6 its n, s11 the pass
   counter before the increment. The next head takes s5 / s7 from s3 / s6 at 0x14580 / 0x14584. *)
Definition llvm_latch (m0 : word -> option byte) (Sp lo ops : Z) (c : fuzz_in) (B : list byte)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 : word)
         (m : word -> option byte) (j10 jio j60 : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c)) (Z_to_bv 64 7) s5 (Z_to_bv 64 (fi_n c)) s7
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 LH_LATCH) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ llvm_cursor c /\
    llvm_mem m0 Sp lo B m j10 jio j60.

(* The exit 0x145e8 (mv a0, zero; the epilogue): only the saved registers matter; the early exit (size >= 2^26,
   0x137c8) reaches it before the frame's other slots are written. *)
Definition llvm_out (m0 : word -> option byte) (Sp lo : Z) (F : bvmap 5 word) (fc : bv 32)
    (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (jlow : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LH_OUT) fc None m (seg_rom rsegs) /\
    Sp mod 16 = 0 /\ lo <= Sp /\ Sp + LH_FRAME <= 2 ^ 63 /\ mem_inv rsegs m /\
    munch [(lo, Sp + LH_FRAME); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m /\ wmono rsegs m0 m /\
    length jlow = 136%nat /\ rw_cells rsegs m Sp (CB 136 jlow :: llvm_saved regs0).

(* At receive's entry, called from the loop (sp = Sp) with return address rret: a0 = p, a1 = n = length bytes,
   a2 = by_poll, a3 = poll_flags; the bytes lie in the input buffer. s0, s2 .. s7 are whatever the op left there;
   receive keeps them (callee-saved). *)
Definition llvm_at_recv (m0 : word -> option byte) (Sp lo ops : Z) (B : list byte) (rret : Z)
    (s0 s2 s3 s4 s5 s6 s7 : word) (p : Z) (bytes : list byte) (by_poll pf : Z)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (j10 jio j60 : list byte),
    ms = MS (mkR (Z_to_bv 64 rret) (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (length bytes))) (Z_to_bv 64 by_poll) (Z_to_bv 64 pf)
                 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 LH_RECV) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\
    data <= p /\ p + Z.of_nat (length bytes) <= data + Z.of_nat (length D) /\ bytes_at rsegs m p bytes /\
    Z.of_nat (length bytes) <= 65535 /\ - 2 ^ 31 <= by_poll < 2 ^ 31 /\ 0 <= pf < 2 ^ 32 /\
    llvm_mem m0 Sp lo B m j10 jio j60.

(* A 6-byte MAC in read-only memory (U/Prog/T/build_and_receive_c.v h_mac_at, as machine facts). *)
Definition lh_mac_at (m : word -> option byte) (p : Z) (mac : list byte) : Prop :=
  length mac = 6%nat /\ 0 <= p /\ p + 6 <= 2 ^ 64 /\ bytes_at rsegs m p mac /\
  forall i, 0 <= i < 6 -> ro_addr rsegs (Z_to_bv 64 (p + i)) = true.

(* At build_and_receive's entry, called from the loop (sp = Sp) with return address rret: a0 = dst, a1 = src,
   a2 = send, a3 = ack (their low 32 bits), a4 = retry, a5 = cmd, a6 = body, a7 = len (U/Prog/T/build_and_receive_c.v
   bar_args). The body lies in the input buffer (op 1) or in the loop's own frame above Sp (op 2's body[]). *)
Definition llvm_at_bar (m0 : word -> option byte) (Sp lo ops : Z) (B : list byte) (rret : Z)
    (s0 s2 s3 s4 s5 s6 s7 : word) (dstp srcp bodyp : Z) (dst src body : list byte) (send ack retry cmd : Z)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a2 a3 t3 t4 t5 t6 : word) (m : word -> option byte) (j10 jio j60 : list byte),
    ms = MS (mkR (Z_to_bv 64 rret) (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                 (Z_to_bv 64 dstp) (Z_to_bv 64 srcp) a2 a3 (Z_to_bv 64 retry) (Z_to_bv 64 cmd)
                 (Z_to_bv 64 bodyp) (Z_to_bv 64 (Z.of_nat (length body))) s2 s3 s4 s5 s6 s7
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 LH_BAR) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\
    lh_mac_at m dstp dst /\ lh_mac_at m srcp src /\
    bv_unsigned a2 mod 2 ^ 32 = send /\ 0 <= send < 2 ^ 16 /\
    bv_unsigned a3 mod 2 ^ 32 = ack /\ 0 <= ack < 2 ^ 32 /\
    0 <= retry < 2 ^ 8 /\ 0 <= cmd < 2 ^ 8 /\
    bytes_at rsegs m bodyp body /\
    ((data <= bodyp /\ bodyp + Z.of_nat (length body) <= data + Z.of_nat (length D)) \/
     (Sp <= bodyp /\ bodyp + Z.of_nat (length body) <= Sp + LH_FRAME)) /\
    llvm_mem m0 Sp lo B m j10 jio j60.

(* After receive / build_and_receive returned to rret: the callee-saved registers as at the call, the world B
   the callee's model gives. *)
Definition llvm_ret (m0 : word -> option byte) (Sp lo ops : Z) (B : list byte) (rret : Z)
    (s0 s2 s3 s4 s5 s6 s7 : word) (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
         (j10 jio j60 : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 rret) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\
    llvm_mem m0 Sp lo B m j10 jio j60.

End LH.

(* ---------------------------------------------------------------- the statements of the pieces *)

(* The entry 0x13760 .. the first loop head: the prologue, the config read from the cursor (:1133-1148), the
   scalars and M (:1150-1158), diginet_session_init (:1165; its abort() at 0x14824 and every UBSan trap of the
   prologue closed by the model premise). It ends at the exit when size >= 2^26 (:1130) or when the cursor is empty
   after the config, else at the loop head with ops = 0 and the model's loop invariant. *)
Definition llvm_entry_stmt : Prop :=
  forall (data : Z) (D : list byte) (regs0 : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (lo : Z) (B : list byte),
    reg_get regs0 10 = Z_to_bv 64 data -> reg_get regs0 11 = Z_to_bv 64 (Z.of_nat (length D)) ->
    bv_unsigned (reg_get regs0 2) mod 16 = 0 -> stk rsegs m lo (bv_unsigned (reg_get regs0 2)) ->
    lo + LH_FRAME + LH_K <= bv_unsigned (reg_get regs0 2) -> bv_unsigned (reg_get regs0 2) < 2 ^ 63 ->
    W_BASE_UBSAN + W_LEN <= lo ->
    (D = [] \/ (0 < data /\ data + Z.of_nat (length D) <= lo /\ off_world data (Z.of_nat (length D)) /\
                bytes_at rsegs m data D)) ->
    mem_inv rsegs m -> relro_img m -> wmem rsegs m B ->
    (forall A, lh_heap_ok A -> exists Bw', LLVMFuzzerTestOneInput_m timg_ubsan B A D = Some (Bw', 0)) ->
    evt rsegs
      (fun ms => llvm_out regs0 m (bv_unsigned (reg_get regs0 2) - LH_FRAME) lo F fc ms \/
         exists (c : fuzz_in) (B' : list byte),
           llvm_head data D regs0 m (bv_unsigned (reg_get regs0 2) - LH_FRAME) lo 0 c B' F fc ms /\
           forall A, lh_heap_ok A ->
             exists Bw', LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) timg_ubsan B' A D c O = Some (Bw', tt))
      (MS (Regs6ss.mkR_of regs0) F (Z_to_bv 64 LH_ENTRY) fc None m (seg_rom rsegs)).

(* The dispatch 0x139dc .. 0x13a20: the op byte read (and its UBSan pointer check), op = b mod 9, the case entry. *)
Definition llvm_disp_stmt : Prop :=
  forall data D regs0 m0 Sp lo ops c B F fc ms (Q : machine_state -> Prop),
    llvm_head data D regs0 m0 Sp lo ops c B F fc ms ->
    (forall ms', llvm_case data D regs0 (snd (fuzz_u8_m D c) mod 9) m0 Sp lo ops c (fst (fuzz_u8_m D c)) B F fc ms' ->
       evt rsegs Q ms') ->
    evt rsegs Q ms.

(* The latch 0x14574 .. 0x1458c: ops < 0x3ff and a nonempty cursor go to the next head, else to the exit. *)
Definition llvm_latch_stmt : Prop :=
  forall data D regs0 m0 Sp lo ops c B F fc ms (Q : machine_state -> Prop),
    llvm_latch data D regs0 m0 Sp lo ops c B F fc ms ->
    (fi_n c <> 0 -> ops + 1 < OPS_MAX -> forall ms', llvm_head data D regs0 m0 Sp lo (ops + 1) c B F fc ms' ->
       evt rsegs Q ms') ->
    ((fi_n c = 0 \/ OPS_MAX <= ops + 1) -> forall ms', llvm_out regs0 m0 Sp lo F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.

(* The epilogue 0x145e8 .. 0x14624: a0 = 0, the 13 registers restored, sp = Sp + 240, ret. Memory unchanged. *)
Definition llvm_exit_stmt : Prop :=
  forall regs0 m0 Sp lo F fc ms,
    llvm_out regs0 m0 Sp lo F fc ms ->
    evt rsegs
      (fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
         ms' = MS (mkR (reg_get regs0 1) (Z_to_bv 64 (Sp + LH_FRAME)) (reg_get regs0 3) (reg_get regs0 4)
                       t0 t1 t2 (reg_get regs0 8) (reg_get regs0 9) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                       (reg_get regs0 18) (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)
                       (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25)
                       (reg_get regs0 26) (reg_get regs0 27) t3 t4 t5 t6)
                  F (ret_pc (reg_get regs0 1)) fc None m (seg_rom rsegs) /\
         munch [(lo, Sp + LH_FRAME); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m /\ wmono rsegs m0 m)
      ms.

(* An op that calls neither receive nor build_and_receive (ops 3 .. 7): from the case entry to the latch, with the
   world and cursor the model's op gives (the model premise closes every UBSan trap and abort of the op). *)
Definition llvm_op_stmt (i : Z) : Prop :=
  forall data D regs0 m0 Sp lo ops c c1 B F fc ms (A : nat -> Z) (k : nat) B1 c2 k1,
    llvm_case data D regs0 i m0 Sp lo ops c c1 B F fc ms ->
    LLVMFuzzerTestOneInput_op_m timg_ubsan B A D c k = Some (B1, (c2, k1)) ->
    evt rsegs (llvm_latch data D regs0 m0 Sp lo ops c2 B1 F fc) ms.

(* An op that receives (ops 0, 8): from the case entry to receive's entry, the model's op as receive_m at the same
   bytes, and the run from receive's return to the latch for any world receive leaves. *)
Definition llvm_op_recv_stmt (i : Z) : Prop :=
  forall data D regs0 m0 Sp lo ops c c1 B F fc ms,
    llvm_case data D regs0 i m0 Sp lo ops c c1 B F fc ms ->
    evt rsegs
      (fun ms' => exists (s0 s2 s3 s4 s5 s6 s7 : word) (p : Z) (bytes : list byte) (by_poll pf : Z) (c2 : fuzz_in),
         llvm_at_recv data D regs0 m0 Sp lo ops B LH_RET_RECV s0 s2 s3 s4 s5 s6 s7 p bytes by_poll pf F fc ms' /\
         (forall I A k, LLVMFuzzerTestOneInput_op_m I B A D c k =
            match receive_m I B (A k) bytes by_poll pf with
            | Some (B1, _) => Some (B1, (c2, S k))
            | None => None
            end) /\
         (forall m0' B' F' fc' ms'' (Q' : machine_state -> Prop), g_fail_next B' <= 1 ->
            llvm_ret data D regs0 m0' Sp lo ops B' LH_RET_RECV s0 s2 s3 s4 s5 s6 s7 F' fc' ms'' ->
            (forall ms3, llvm_latch data D regs0 m0' Sp lo ops c2 B' F' fc' ms3 -> evt rsegs Q' ms3) ->
            evt rsegs Q' ms''))
      ms.

(* An op that calls build_and_receive (ops 1, 2; op_frame / op_announce inlined), the same shape. *)
Definition llvm_op_bar_stmt (i rret : Z) : Prop :=
  forall data D regs0 m0 Sp lo ops c c1 B F fc ms,
    llvm_case data D regs0 i m0 Sp lo ops c c1 B F fc ms ->
    evt rsegs
      (fun ms' => exists (s0 s2 s3 s4 s5 s6 s7 : word) (dstp srcp bodyp : Z) (dst src body : list byte)
                         (send ack retry cmd : Z) (c2 : fuzz_in),
         llvm_at_bar data D regs0 m0 Sp lo ops B rret s0 s2 s3 s4 s5 s6 s7 dstp srcp bodyp dst src body
           send ack retry cmd F fc ms' /\
         (forall I A k, LLVMFuzzerTestOneInput_op_m I B A D c k =
            match build_and_receive_m I B (A k) dst src send ack retry cmd body with
            | Some (B1, _) => Some (B1, (c2, S k))
            | None => None
            end) /\
         (forall m0' B' F' fc' ms'' (Q' : machine_state -> Prop), g_fail_next B' <= 1 ->
            llvm_ret data D regs0 m0' Sp lo ops B' rret s0 s2 s3 s4 s5 s6 s7 F' fc' ms'' ->
            (forall ms3, llvm_latch data D regs0 m0' Sp lo ops c2 B' F' fc' ms3 -> evt rsegs Q' ms3) ->
            evt rsegs Q' ms''))
      ms.
