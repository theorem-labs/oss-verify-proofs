(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the cuts of the UBSan harness walk of LLVMFuzzerTestOneInput (fuzz_decode.ubsan,
   entry 0x12cfc, frame 0x1f0). The walk is cut at four machine states (walks map LTOI-MAP-U.md):
   - 0x12df8, the call set-up of diginet_cursor_init: the front (prologue, fuzz_dup's malloc and memcpy, the frame
     parse) is done, body and len are in s2 and s1;
   - 0x12e8c, the cursor loop has left; 0x13384, the decoder loop has left;
   - 0x14ee8 with ra = 0x13398 and a0 = buf: the entry of free (check_refusal has returned).
   Between the first and the last no instruction reaches the allocator, so these parts are evt walks; the front up to
   0x12df8 and the free / return after 0x14ee8 are SR walks (they call malloc and free).
   At each evt cut the 104 bytes at sp + 0x188 hold the thirteen saved registers (sv), sp + 8 holds buf, the 8 bytes
   at sp and the 376 bytes at sp + 0x10 are junk to the next part (the cursor, the decoder, their messages and events
   are made again by the part that uses them), the len bytes bb at body are the body the loops read (unchanged: no
   part writes below lo), and the memory differs from m0 (the memory at 0x12df8) only in [lo, sp + 0x1f0), the stack
   window of the frame and of its callees. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.

(* the pcs of the cuts *)
Definition LLVM_PC_BODY : Z := 0x12df8.
Definition LLVM_PC_CURSOR_OUT : Z := 0x12e8c.
Definition LLVM_PC_DECODER_OUT : Z := 0x13384.
Definition LLVM_FREE_RA : Z := 0x13398.

(* the thirteen registers the prologue saves at sp + 0x188 .. sp + 0x1e8: s11, s10, .., s2, s1, s0, ra *)
Definition llvm_saved_cells (regs0 : bvmap 5 word) : list cell :=
  [C8 (YK11.getr regs0 27); C8 (YK11.getr regs0 26); C8 (YK11.getr regs0 25); C8 (YK11.getr regs0 24);
   C8 (YK11.getr regs0 23); C8 (YK11.getr regs0 22); C8 (YK11.getr regs0 21); C8 (YK11.getr regs0 20);
   C8 (YK11.getr regs0 19); C8 (YK11.getr regs0 18); C8 (YK11.getr regs0 9); C8 (YK11.getr regs0 8);
   C8 (YK11.getr regs0 1)].

Lemma llvm_saved_cells_size : forall regs0, cells_size (llvm_saved_cells regs0) = 104%nat.
Proof. reflexivity. Qed.

(* The arguments every cut takes, in this order: F, fc the floating-point registers and fcsr; gp, tp; sv the saved
   registers; Sp sp in the frame (entry sp - 0x1f0); lo the low end of the stack window; buf the malloc block, of nn
   bytes; body the body the loops read, whose bytes are bb; m0 the memory at 0x12df8. They are explicit arguments,
   not section variables, so that every lane applies them the same way. *)

Definition mid_len (bb : list byte) : Z := Z.of_nat (length bb).

(* the facts about the numbers that every part may use: the frame and the window (ALLOC_STACK below sp, enough for
   every callee of the evt parts), the block below the window, the body inside the block. 0 < lo, which
   check_refusal's contract needs, follows from 4096 <= buf, 0 < nn and buf + nn <= lo. *)
Definition mid_env (sv : list cell) (Sp lo buf nn body : Z) (bb : list byte) : Prop :=
  0 <= lo /\ lo + ALLOC_STACK <= Sp /\ Sp mod 16 = 0 /\ Sp + LLVM_FRAME <= 2 ^ 47 /\
  4096 <= buf /\ 0 < nn < 2 ^ 26 /\ buf + nn <= lo /\
  buf <= body /\ body + mid_len bb <= buf + nn /\ length sv = 13%nat.

(* the facts every cut holds of its memory m *)
Definition mid_inv (sv : list cell) (Sp lo buf body : Z) (bb : list byte) (m0 m : word -> option byte) : Prop :=
  mem_inv rsegs m /\ stk rsegs m lo Sp /\ rw_cells rsegs m (Sp + 0x188) sv /\
  rw_cells rsegs m (Sp + 8) [C8 (Z_to_bv 64 buf)] /\ bytes_at rsegs m body bb /\
  munch [(lo, Sp + LLVM_FRAME)] m0 m /\ wmono rsegs m0 m.

(* a cut at pc: sp, gp, tp, F, fc as above, s1 = len, s2 = body, every other register any value; the 8 bytes at sp and
   the 376 bytes at sp + 0x10 any bytes *)
Definition mid_at (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (sv : list cell) (Sp lo buf body : Z)
    (bb : list byte) (m0 : word -> option byte) (pc : Z) (ms : machine_state) : Prop :=
  exists (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (j0 j1 : list byte),
    ms = MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 x8 (Z_to_bv 64 (mid_len bb)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 body) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 pc) fc None m (seg_rom rsegs) /\
    mid_inv sv Sp lo buf body bb m0 m /\
    rw_cells rsegs m Sp [CB 8 j0] /\ rw_cells rsegs m (Sp + 0x10) [CB 376 j1].

(* the entry of free(buf) at 0x13394 (`jal free`, ra = 0x13398), the last cut of the evt parts *)
Definition mid_free (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (sv : list cell) (Sp lo buf body : Z)
    (bb : list byte) (m0 : word -> option byte) (ms : machine_state) : Prop :=
  exists (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (j0 j1 : list byte),
    ms = MS (mkR (Z_to_bv 64 LLVM_FREE_RA) (Z_to_bv 64 Sp) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 buf) x11 x12 x13 x14
               x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs) /\
    mid_inv sv Sp lo buf body bb m0 m /\
    rw_cells rsegs m Sp [CB 8 j0] /\ rw_cells rsegs m (Sp + 0x10) [CB 376 j1].

(* the SR state at 0x12df8 that the front leaves: for the size n (1 <= n < 2^26) the block of nn = max (n - 1) 1 bytes
   is new (lf_mine), its address buf is at sp + 8, body and len = length bb are in s2 and s1, the body bytes bb lie in
   the block, the saved registers of the entry state regs0 are at sp + 0x188 *)
Section Front.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Definition llvm_nn (n : Z) : Z := Z.max (n - 1) 1.

Definition front_post (stk : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
    (md0 : Model) (n : Z) (b : sbound) (c : config) : Prop :=
  exists (fx' : YK11.FPState) L A regs mem md (buf body : Z) (bb : list byte),
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 LLVM_PC_BODY) mem (YK11.seg_rom (ms_segs B))) md /\
    frm_zero (@fp_csr fx') /\
    lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md /\
    res_ok_slots A (sb_malloc b (llvm_nn n)) /\
    lf_mine L0 A0 L A buf (llvm_nn n) /\
    YK11.getr regs 2 = Z_to_bv 64 (spZ regs0 - LLVM_FRAME) /\
    YK11.getr regs 3 = YK11.getr regs0 3 /\ YK11.getr regs 4 = YK11.getr regs0 4 /\
    YK11.getr regs 9 = Z_to_bv 64 (Z.of_nat (length bb)) /\ YK11.getr regs 18 = Z_to_bv 64 body /\
    rw_cells rsegs mem (spZ regs0 - LLVM_FRAME + 0x188) (llvm_saved_cells regs0) /\
    rw_cells rsegs mem (spZ regs0 - LLVM_FRAME + 8) [C8 (Z_to_bv 64 buf)] /\
    (exists j0, rw_cells rsegs mem (spZ regs0 - LLVM_FRAME) [CB 8 j0]) /\
    (exists j1, rw_cells rsegs mem (spZ regs0 - LLVM_FRAME + 0x10) [CB 376 j1]) /\
    bytes_at rsegs mem body bb /\
    4096 <= buf /\ buf + llvm_nn n <= YM05.alloc_ceiling /\
    buf <= body /\ body + Z.of_nat (length bb) <= buf + llvm_nn n.

End Front.
