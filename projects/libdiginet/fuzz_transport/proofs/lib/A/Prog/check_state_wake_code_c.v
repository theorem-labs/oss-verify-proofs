(* check_state_wake_code_contract: check_state_wake_code (fuzz/fuzz_transport.c:517-525; model lib/TModel/TCb.v
   check_state_wake_code_m) on fuzz_transport.asan (e89be137db17), a leaf that compares its two int arguments and
   returns nothing. It reads no memory but its own frame and stores into no harness global, so it takes the leaf form.
   Arguments: a0 = rc, a1 = want (ints, sign-extended into the 64-bit registers: a0 = Z_to_bv 64 rc, a1 =
   Z_to_bv 64 want with rc, want in [-2^31, 2^31), the plain contract's argument premises).
   Premises: the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; check_state_wake_code_m Bw rc want =
   Some (Bw', tt), which holds exactly when rc = want (TCb.v:411-412); the caller's stack below sp (stk, with room for
   the 16-byte frame); the frame [sp - 16, sp) outside the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness
   globals (lib/A/TransportG.v), so the frame store does not touch the world.
   Result: the run returns to ra with every register unchanged (the function is void and its one return path writes
   no register but sp, which it restores, and ra, which it reloads with its own value). It writes only its frame
   (munch), every writable byte stays writable (wmono), the stack below sp stays usable (stk), Bw' = Bw, and the world
   relation still holds at the new memory with the same world. These are the plain contract's post facts
   (lib/Prog/T/check_state_wake_code_c.v: B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 32 code bytes of
   this function are equal in both files): symbol check_state_wake_code, value 0x83e48, size 32 (8 words).
     0x83e48          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x83e4c          the 8-byte store of ra at sp - 8 (own frame); 0x83e54 loads it back.
     0x83e50          a0 <> a1 (the full 64-bit registers) goes to 0x83e60; else 0x83e54-0x83e5c: ra reloaded,
                      sp = sp + 16, return. This is the one return; on it every register is as at entry.
     0x83e60          call of __asan_handle_no_return (0x5a4c4, DgnTransportAddr.v TS___asan_handle_no_return), then
                      0x83e64 call of abort (0x93734, TS_abort): the trap path.
   The code loads no byte but the saved ra: no harness global, no shadow byte, no runtime cell.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* entry in this function;
     - the trap path (0x83e60 / 0x83e64) is reached only when a0 <> a1. With a0 = Z_to_bv 64 rc, a1 = Z_to_bv 64 want
       and rc, want in [-2^31, 2^31), a0 = a1 exactly when rc = want, and check_state_wake_code_m Bw rc want = Some _
       gives rc = want.
   Callee texts assumed: none (the only callees, __asan_handle_no_return and abort, are on the trap path).
   The caller is LLVMFuzzerTestOneInput (the call at 0x818e0, return address 0x818e4).
   Form: lib/Prog/T/check_state_wake_code_c.v (the plain contract: argument premises, world premise, model premise,
   B' = B and the world after) in the image-A leaf form of check_state_wake_c.v, with the register arguments of
   fuzz_frame's diginet_cursor_init_c.v (a0 = Z_to_bv 64 c, ...). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_STATE_WAKE_CODE : Z := 0x83e48.
Definition CHECK_STATE_WAKE_CODE_FRAME : Z := 16.

Definition check_state_wake_code_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte) (rc want : Z),
    a0 = Z_to_bv 64 rc ->
    a1 = Z_to_bv 64 want ->
    -2 ^ 31 <= rc < 2 ^ 31 ->
    -2 ^ 31 <= want < 2 ^ 31 ->
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_state_wake_code_m Bw rc want = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_STATE_WAKE_CODE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_STATE_WAKE_CODE_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_STATE_WAKE_CODE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_STATE_WAKE_CODE) fc None m (seg_rom rsegs)).
