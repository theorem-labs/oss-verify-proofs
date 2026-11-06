(* check_refusal_submit_contract: check_refusal_submit (fuzz/fuzz_transport.c:656-665; model lib/TModel/TCb.v
   check_refusal_submit_m) on fuzz_transport.asan (e89be137db17), a leaf that searches the bytes of the struct
   diginet_cmd at its first argument for a system command (spec_system_at, inlined), compares its second argument
   with SPEC_E_REFUSED and, for a system command, g_s.queued with its third argument, and returns nothing. It stores
   into no harness global, so it takes the leaf form.
   Arguments: a0 = cp, the address of the 32 bytes c of a struct diginet_cmd (bytes[24] at 0, len at 24); a1 = rc
   (int); a2 = before, an unsigned int (the sign-extended 32-bit value, RV64 psABI).
   Premises:
   - as the plain contract (lib/Prog/T/check_refusal_submit_c.v): the argument registers and their C ranges; 0 < cp,
     cp mod 4 = 0; the 32 bytes c at cp (bytes_at) with length c = 32; the world relation of image A
     (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between the memory m, read through csw_view
     (check_state_wake_c.v), and the world Bw; check_refusal_submit_m Bw c rc before = Some (Bw', tt), which holds
     exactly when len = c[24] <= 32 and either spec_system_at (zs c) len >= 0 (a system command), rc =
     SPEC_E_REFUSED (-10) and g_s.queued = before, or spec_system_at (zs c) len < 0 and rc <> SPEC_E_REFUSED
     (TCb.v:551-558); the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp)
     outside the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so the frame
     store does not touch the world;
   - for the instrumented checks (lib/A/AsanCells.v): asan_cells m (among others, the 8 bytes at GOT_CELL_K =
     0xa4090 hold CELL_K = 0xac9f8 and the 8 bytes at CELL_K hold 0x7fff8000); both ends of the frame are in
     application memory (app_mem), so the frame is not a shadow byte; GOT_CELL_K 8, CELL_K 8 and the 32 bytes at cp
     are outside the frame (off_stk; off_window of the plain contract, for c); the 32 bytes at cp are marked usable in
     the shadow map (addressable).
   Result: the run returns to ra with every register but a0, a3 .. a7 and t0 .. t3 unchanged (they are not
   specified: the function is void). It writes only its frame (munch), every writable byte stays writable (wmono),
   the stack below sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same
   world. These are the plain contract's post facts (B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 288 code bytes of
   this function are equal in both files): symbol check_refusal_submit, value 0x86110, size 288 (72 words).
     0x86110          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x86114          the 8-byte store of ra at sp - 8 (own frame); 0x861ec loads it back.
     0x86118-0x8611c  a3 = the 8-byte load at GOT_CELL_K = 0xa4090 (.got): CELL_K.
     0x86120          a4 = the 8-byte load at CELL_K = 0xac9f8: 0x7fff8000.
     0x86124-0x86130  the instrumented check of the byte load at cp + 24: a3 = cp + 24; a5 = the signed shadow byte k
                      at ((cp + 24) >> 3) + 0x7fff8000.
     0x86134          k <> 0 goes to 0x86214: a6 = (cp + 24) & 7; a6 < k goes back to 0x86138, else 0x8621c-0x86220:
                      a0 = cp + 24, call of __asan_report_load1 (0x594c8, TS___asan_report_load1): the error path.
     0x86138          a6 = the byte at cp + 24, zero-extended: len.
     0x8613c-0x86140  a3 = 4; len < 4 (unsigned) goes to 0x861e4 (no system command).
     0x86144-0x86154  a5 = cp + 1; a6 = len - 3; a7 = 0xf0; t0 = 0x13; t1 = 0x70.
     0x86158          the loop, for i = 0 .. len - 4 with a0 = cp + i, a5 = cp + i + 1, a6 = len - 3 - i:
     0x86158-0x86164    the instrumented check of the byte load at cp + i (a3 = its signed shadow byte k); k <> 0
                        goes to 0x861bc: t2 = (cp + i) & 7; t2 >= k goes to 0x86224, a call of __asan_report_load1
                        with a0 = cp + i (the error path), else back to 0x86168;
     0x86168-0x8616c    a3 = the byte c[i] at cp + i; a3 <> 0xf0 goes to 0x861a8;
     0x86170-0x86180    a3 = cp + i + 1 and the check of the byte load there (t2 = its signed shadow byte k); k <> 0
                        goes to 0x861c8: t3 = (cp + i + 1) & 7; t3 >= k goes to 0x86228-0x8622c, a0 = cp + i + 1 and
                        a call of __asan_report_load1, else back to 0x86184;
     0x86184-0x86188    a3 = c[i + 1]; a3 <> 0x13 goes to 0x861a8;
     0x8618c-0x8619c    a3 = cp + i + 3 and the check of the byte load there (t2 = its signed shadow byte k); k <> 0
                        goes to 0x861d4: t3 = (cp + i + 3) & 7; t3 < k goes back to 0x861a0, else 0x861dc-0x861e0:
                        a0 = cp + i + 3, call of __asan_report_load1;
     0x861a0-0x861a4    a3 = c[i + 3]; a3 = 0x70 goes to 0x861f8 (a system command at i);
     0x861a8-0x861b8    a0 = a0 + 1, a6 = a6 - 1, a5 = a5 + 1; a6 <> 0 goes back to 0x86158, else to 0x861e4.
     0x861e4-0x861e8  (no system command) a0 = -10; a1 = a0 goes to 0x8620c; else 0x861ec-0x861f4: ra reloaded,
                      sp = sp + 16, return.
     0x861f8-0x861fc  (a system command) a0 = -10; a1 <> a0 goes to 0x8620c.
     0x86200-0x86204  a0 = the 4-byte load at 0x5e40a0, sign-extended: g_s.queued (g_s payload 0x5df9c0, 18264 bytes;
                      TWorld.v A_S_queued = OFF_g_s + 18144). No instrumented check precedes this load.
     0x86208          a0 = a2 goes to 0x861ec (the return); else on to 0x8620c.
     0x8620c          call of __asan_handle_no_return (0x5a4c4, TS___asan_handle_no_return), then 0x86210 call of
                      abort (0x93734): the trap path.
   The return (0x861ec) is the one return; on it every register but a0, a3 .. a7, t0 .. t3 is as at entry.
   The loop is spec_system_at (zs c) len (DgnSpec.v:255-268: for (i = 0; i + 3 < len; i++), F0 13 xx 70), with
   byte_at (zs c) j = c[j].
   Error paths and the premise that rules each out:
     - the four calls of __asan_report_load1 (0x861e0, 0x86220, 0x86224, 0x8622c) are reached only when the signed
       shadow byte k of a loaded byte a is not 0 and (a & 7) >= k. Every loaded byte lies in [cp, cp + 32): cp + 24,
       and cp + i, cp + i + 1, cp + i + 3 with i + 3 < len <= 32 (len <= length c = 32 by the model premise).
       addressable m cp 32 gives k = 0 or a mod 8 < k <= 7 for each: the check passes;
     - the trap path (0x8620c / 0x86210) is reached, with no system command, when rc = -10, and with a system command,
       when rc <> -10 or the sign-extended g_s.queued differs from a2 = bv_swrap 32 before. By tw_at the 4 bytes at
       0x5e40a0 are sub Bw A_S_queued 4 (TWorldG.v tw_read_val, tw_lw); both are 32-bit values, equal exactly when
       S_queued Bw = before. check_refusal_submit_m Bw c rc before = Some _ rules out each case.
   Callee texts assumed: none (the only callees, __asan_report_load1, __asan_handle_no_return and abort, are on the
   error and trap paths).
   The caller: LLVMFuzzerTestOneInput, the calls at 0x81ec8 and 0x823ec (return addresses 0x81ecc and 0x823f0;
   DgnTransportList.v PCall TS_check_refusal_submit), each with a2 = the 8-byte load at s1 + 0x90.
   Form: check_state_wake_c.v (the image-A leaf form of the exemplar) with the instrumented-load premises of fuzz_frame's
   image-A diginet_frame_is_keepalive_c.v (asan_cells, app_mem of the frame ends, off_stk and addressable per loaded
   range), and the plain contract's argument, world and model premises, B' = B and the world after. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.

Definition CHECK_REFUSAL_SUBMIT : Z := 0x86110.
Definition CHECK_REFUSAL_SUBMIT_FRAME : Z := 16.
(* The int of the world the code loads: g_s.queued, at g_s's image-A base plus the member's offset in g_s. *)
Definition CHECK_REFUSAL_SUBMIT_QUEUED : Z := TA_g_s + (TW.A_S_queued - TW.OFF_g_s).
Lemma check_refusal_submit_queued_at : CHECK_REFUSAL_SUBMIT_QUEUED = 0x5e40a0.
Proof. reflexivity. Qed.

Definition check_refusal_submit_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte)
         (cp : Z) (c : list byte) (rc before : Z),
    a0 = Z_to_bv 64 cp ->
    a1 = Z_to_bv 64 rc ->
    a2 = Z_to_bv 64 (bv_swrap 32 before) ->
    -2 ^ 31 <= rc < 2 ^ 31 ->
    0 <= before < 2 ^ 32 ->
    0 < cp ->
    cp mod 4 = 0 ->
    bytes_at rsegs m cp c ->
    length c = 32%nat ->
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_refusal_submit_m Bw c rc before = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_REFUSAL_SUBMIT_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_REFUSAL_SUBMIT_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME CELL_K 8 ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME cp 32 ->
    addressable m cp 32 ->
    evt rsegs
      (fun ms' => exists (a0' a3' a4' a5' a6' a7' t0' t1' t2' t3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1 a2 a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_REFUSAL_SUBMIT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REFUSAL_SUBMIT) fc None m (seg_rom rsegs)).
