(* check_latest_submit_contract: check_latest_submit (fuzz/fuzz_transport.c:667-676; model lib/TModel/TCb.v
   check_latest_submit_m) on fuzz_transport.asan (e89be137db17), a leaf that compares its two int arguments and returns
   nothing. It reads no memory but its own frame and stores into no harness global, so it takes the leaf form.
   Arguments: a0 = rc, a1 = want (ints, sign-extended to 64 bits: RV64 psABI).
   Premises: the two argument registers and their int ranges (as the plain contract); the world relation of image A
   (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between the memory m, read through csw_view
   (check_state_wake_c.v), and the world Bw; check_latest_submit_m Bw rc want = Some (Bw', tt), which holds exactly
   when rc = want (TCb.v:561-562); the caller's stack below sp (stk, with room for the 16-byte frame); the frame
   [sp - 16, sp) outside the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so the
   frame store does not touch the world.
   Result: the run returns to ra with every register unchanged (the code writes no register but sp, which it
   restores, and ra, which it reloads with the value it stored). It writes only its frame (munch), every writable byte
   stays writable (wmono), the stack below sp stays usable (stk), Bw' = Bw, and the world relation still holds at the
   new memory with the same world. These are the plain contract's post facts (lib/Prog/T/check_latest_submit_c.v:
   B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 32 code bytes of
   this function are equal in both files): symbol check_latest_submit, value 0x86230, size 32 (8 words).
     0x86230          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x86234          the 8-byte store of ra at sp - 8 (own frame); 0x8623c loads it back.
     0x86238          a0 <> a1 goes to 0x86248; else 0x8623c-0x86244: ra reloaded, sp = sp + 16, return. This is the
                      one return; on it every register is as at entry.
     0x86248          call of __asan_handle_no_return (0x5a4c4, TS___asan_handle_no_return), then 0x8624c call of
                      abort (0x93734): the trap path.
   The code loads no byte but ra's: no shadow byte, no runtime cell, no world byte.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* entry in this function;
     - the trap path (0x86248 / 0x8624c) is reached only when a0 <> a1, i.e. Z_to_bv 64 rc <> Z_to_bv 64 want; both
       are ints, so that is rc <> want, and check_latest_submit_m Bw rc want = Some _ gives rc = want.
   Callee texts assumed: none (the only callees, __asan_handle_no_return and abort, are on the trap path).
   The caller: LLVMFuzzerTestOneInput, the call at 0x823fc (return address 0x82400; DgnTransportList.v PCall
   TS_check_latest_submit), with a0 = s7 and a1 = s6.
   Form: check_state_wake_c.v (the image-A leaf form of the exemplar), with the plain contract
   lib/Prog/T/check_latest_submit_c.v's argument premises, world premise, model premise, B' = B and the world after. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.

Definition CHECK_LATEST_SUBMIT : Z := 0x86230.
Definition CHECK_LATEST_SUBMIT_FRAME : Z := 16.

Definition check_latest_submit_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte) (rc want : Z),
    a0 = Z_to_bv 64 rc ->
    a1 = Z_to_bv 64 want ->
    -2 ^ 31 <= rc < 2 ^ 31 ->
    -2 ^ 31 <= want < 2 ^ 31 ->
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_latest_submit_m Bw rc want = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_SUBMIT_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_SUBMIT_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_SUBMIT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_SUBMIT) fc None m (seg_rom rsegs)).
