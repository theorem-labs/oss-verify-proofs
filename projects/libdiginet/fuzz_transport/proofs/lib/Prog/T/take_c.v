(* take (transport/src/diginet_session.c:353-386) at 0x171bc, 488 bytes. The binary calls memcpy (:365, :374, :379)
   and diginet_body_check (:366). FRAME 272 = its own 128 (addi sp,sp,-128 at 0x171bc) + 144, the deepest callee
   window (diginet_body_check; memcpy 0). Every callee window counted is that callee's full transitive stack
   depth, abort() paths included, so it bounds the window any callee contract asks for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition take_ENTRY : Z := 0x171bc.
Definition take_FRAME : Z := 272.

(* a0 = s = &g_s, a1 = body (tick's uint8_t body[1484]), a2 = body_len (a size_t cell), a3 = allow_display (int), a4
   = has_display (an int cell), as tick passes them (:461-464). Result: the unsigned taken, sign-extended from
   bit 31 as the LP64 ABI returns a 32-bit value; body[0 .. len) holds the model's body bytes (the bytes past len
   are what refused commands left), *body_len = len, *has_display = hd. *)
Definition take_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (bp blp hdp allow len hd taken : Z) (J JL JH body : list byte) (B B' : list byte),
    a0 = Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s) ->
    a1 = Z_to_bv 64 bp ->
    a2 = Z_to_bv 64 blp ->
    a3 = Z_to_bv 64 allow ->
    a4 = Z_to_bv 64 hdp ->
    - 2^31 <= allow < 2^31 ->
    rw_cells rsegs m bp [CB 1484 J] ->
    arg_blk sp take_FRAME bp 1484 ->
    rw_cells rsegs m blp [CB 8 JL] ->
    arg_blk sp take_FRAME blp 8 ->
    blp mod 8 = 0 ->
    rw_cells rsegs m hdp [CB 4 JH] ->
    arg_blk sp take_FRAME hdp 4 ->
    hdp mod 4 = 0 ->
    blk_sep bp 1484 blp 8 ->
    blk_sep bp 1484 hdp 4 ->
    blk_sep blp 8 hdp 4 ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    take_m B allow = Some (B', (body, len, hd, taken)) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + take_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_PLAIN sp take_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (X : list byte)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (bv_swrap 32 taken)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - take_FRAME, bv_unsigned sp);
                (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN);
                (bp, bp + 1484);
                (blp, blp + 8);
                (hdp, hdp + 4)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1 /\
         rw_cells rsegs m' bp [CB 1484 X] /\
         firstn (Z.to_nat len) X = firstn (Z.to_nat len) body /\
         rw_cells rsegs m' blp [CB 8 (put 8 len)] /\
         rw_cells rsegs m' hdp [CB 4 (put 4 hd)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 take_ENTRY) fc None m (seg_rom rsegs)).
