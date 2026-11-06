(* Contract of diginet_cursor_init in fuzz_frame.plain.
   Source: src/diginet_msg.c:10-18 at 835f336c.
   Address 0x13c90, size 36 bytes.
   Arguments: a0 is the address c of a struct diginet_cursor, a1 the address body, a2 the
   length len. The caller is diginet_body_check; it gives a cursor in its stack frame and its
   own two arguments.
   Preconditions: c is not 0. The 25 bytes cj at c (body, len, pos, status) are writable
   (rw_cells). mem_inv holds.
   Result: the function writes c->body = body, c->len = len (0 when body is 0), c->pos = 0
   and c->status = 0, as cursor_cells gives them. It does not write the 7 padding bytes after
   c->status. It writes a2 and a3, and it keeps a0 and a1.
   The function writes only the 25 bytes at c. It keeps all other registers.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_CURSOR_INIT : Z := 0x13c90.

(* The 25 bytes body, len, pos, status of a struct diginet_cursor. *)
Definition cursor_cells (body len : Z) (pos : nat) (st : Z) : list cell :=
  [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 (Z.of_nat pos)); C1 (b8 st)].

Definition diginet_cursor_init_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c body len : Z) (cj : list byte),
    c <> 0 ->
    0 <= body < 2^64 -> 0 <= len < 2^64 ->
    rw_cells rsegs m c [CB 25 cj] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 body) a2' a3'
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(c, c + 25)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' c (cursor_cells body (if body =? 0 then 0 else len) 0 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 body) (Z_to_bv 64 len)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_CURSOR_INIT) fc None m (seg_rom rsegs)).
