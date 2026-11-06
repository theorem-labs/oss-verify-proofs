(* check_state_wake_code_contract: check_state_wake_code (fuzz/fuzz_transport.c:517-525; model lib/TModel/TCb.v
   check_state_wake_code_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that compares its two int arguments
   and returns nothing. It reads no memory but its own frame and stores into no harness global, so it takes the leaf
   form.
   Arguments: a0 = rc, a1 = want (ints, sign-extended into the 64-bit registers: a0 = Z_to_bv 64 rc, a1 =
   Z_to_bv 64 want with rc, want in [-2^31, 2^31), the plain contract's argument premises).
   Premises: the world relation of image B (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; check_state_wake_code_m Bw rc want =
   Some (Bw', tt), which holds exactly when rc = want (TCb.v:411-412); the caller's stack below sp (stk, with room for
   the 16-byte frame); the frame [sp - 16, sp) outside the hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 harness
   globals (lib/B/TransportGB.v), so the frame store does not touch the world.
   Result: the run returns to ra with every register unchanged (the function is void and its one return path writes
   no register but sp, which it restores, and ra, which it reloads with its own value). It writes only its frame
   (munch), every writable byte stays writable (wmono), the stack below sp stays usable (stk), Bw' = Bw, and the world
   relation still holds at the new memory with the same world. These are the plain contract's post facts
   (lib/Prog/T/check_state_wake_code_c.v: B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 36 code bytes of this function are equal in both files):
   symbol check_state_wake_code, value 0x8399c, size 36 (9 words).
     0x8399c          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x839a0          the 8-byte store of ra at sp - 8 (own frame); 0x839a8 loads it back.
     0x839a4          a0 <> a1 (the full 64-bit registers) goes to 0x839b4; else 0x839a8-0x839b0: ra reloaded,
                      sp = sp + 16, return. This is the one return; on it every register is as at entry.
     0x839b4          call of __asan_handle_no_return (0x5a500, DgnTransportBAddr.v TB___asan_handle_no_return),
                      then 0x839b8 call of abort (0x93390, TB_abort), then 0x839bc the word 0xc0001073 (unimp: a write
                      of the read-only CSR cycle, an illegal instruction that traps), reached only if abort returns:
                      the trap path.
   The code loads no byte but the saved ra: no harness global, no shadow byte, no runtime cell.
   Against image A's code (lib/A/Prog/check_state_wake_code_c.v, 8 words): the words at 0x8399c-0x839b8 are the same
   eight instructions with image B's jal immediates; the word at 0x839bc is the one instruction image A's code does
   not have.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* or __ubsan_handle_* entry in this function;
     - the trap path (0x839b4 / 0x839b8 / 0x839bc) is reached only when a0 <> a1. With a0 = Z_to_bv 64 rc, a1 =
       Z_to_bv 64 want and rc, want in [-2^31, 2^31), a0 = a1 exactly when rc = want, and check_state_wake_code_m Bw
       rc want = Some _ gives rc = want. The unimp word at 0x839bc follows the call of abort on this path, so the same
       premise rules it out.
   Callee texts assumed: none (the only callees, __asan_handle_no_return and abort, are on the trap path).
   The caller is LLVMFuzzerTestOneInput (the call at 0x81afc, return address 0x81b00; DgnTransportBList.v PCall
   TB_check_state_wake_code).
   Form: lib/A/Prog/check_state_wake_code_c.v (image A's contract of this function), at image B's entry, world table
   TMAP_B and harness hull. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_STATE_WAKE_CODE : Z := 0x8399c.
Definition CHECK_STATE_WAKE_CODE_FRAME : Z := 16.

Definition check_state_wake_code_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte) (rc want : Z),
    a0 = Z_to_bv 64 rc ->
    a1 = Z_to_bv 64 want ->
    -2 ^ 31 <= rc < 2 ^ 31 ->
    -2 ^ 31 <= want < 2 ^ 31 ->
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_state_wake_code_m Bw rc want = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_STATE_WAKE_CODE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_STATE_WAKE_CODE_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_STATE_WAKE_CODE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_STATE_WAKE_CODE) fc None m (seg_rom rsegs)).
