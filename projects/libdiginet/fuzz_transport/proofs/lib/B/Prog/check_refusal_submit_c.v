(* check_refusal_submit_contract: check_refusal_submit (fuzz/fuzz_transport.c:656-665; model lib/TModel/TCb.v
   check_refusal_submit_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that searches the bytes of the struct
   diginet_cmd at its first argument for a system command (spec_system_at, inlined), compares its second argument
   with SPEC_E_REFUSED and, for a system command, g_s.queued with its third argument, and returns nothing. It stores
   into no harness global, so it takes the leaf form.
   Arguments: a0 = cp, the address of the 32 bytes c of a struct diginet_cmd (bytes[24] at 0, len at 24); a1 = rc
   (int); a2 = before, an unsigned int (the sign-extended 32-bit value, RV64 psABI).
   Premises:
   - as the plain contract (lib/Prog/T/check_refusal_submit_c.v): the argument registers and their C ranges; 0 < cp,
     cp mod 4 = 0; the 32 bytes c at cp (bytes_at) with length c = 32; the world relation of image B
     (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between the memory m, read through csw_view
     (check_state_wake_c.v), and the world Bw; check_refusal_submit_m Bw c rc before = Some (Bw', tt), which holds
     exactly when len = c[24] <= 32 and either spec_system_at (zs c) len >= 0 (a system command), rc =
     SPEC_E_REFUSED (-10) and g_s.queued = before, or spec_system_at (zs c) len < 0 and rc <> SPEC_E_REFUSED
     (TCb.v:551-558); the caller's stack below sp (stk, with room for the 32-byte frame); the frame [sp - 32, sp)
     outside the hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 harness globals (lib/B/TransportGB.v), so the frame
     stores do not touch the world;
   - for the instrumented checks (lib/B/AsanCells.v): asan_cells m (among others, the 8 bytes at GOT_CELL_K =
     0xa3cf0 hold CELL_K = 0xac678 and the 8 bytes at CELL_K hold 0x7fff8000); both ends of the frame are in
     application memory (app_mem), so the frame is not a shadow byte; GOT_CELL_K 8, CELL_K 8 and the 32 bytes at cp
     are outside the frame (off_stk; off_window of the plain contract, for c); the 32 bytes at cp are marked usable in
     the shadow map (addressable).
   Result: the run returns to ra with every register but a0, a3 .. a7 and t0 .. t6 unchanged (they are not
   specified: the function is void). It writes only its frame (munch), every writable byte stays writable (wmono),
   the stack below sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same
   world. These are the plain contract's post facts (B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 348 code bytes of this function are equal in both files):
   symbol check_refusal_submit, value 0x8640c, size 348 (87 words).
     0x8640c          sp = sp - 32: the frame is 32 bytes. No side-stack frame.
     0x86410-0x86418  the 8-byte stores of ra at sp - 8, s0 at sp - 16 and s1 at sp - 24 (own frame); 0x86514-0x8651c
                      load them back.
     0x8641c-0x86420  a3 = cp & 3; a3 <> 0 goes to 0x86544, the unimp word (the trap path).
     0x86424-0x86428  a3 = the 8-byte load at GOT_CELL_K = 0xa3cf0 (.got): CELL_K = 0xac678.
     0x8642c          a5 = the 8-byte load at CELL_K: 0x7fff8000.
     0x86430-0x8643c  the instrumented check of the byte load at cp + 24: a3 = cp + 24; a4 = the signed shadow byte k
                      at ((cp + 24) >> 3) + 0x7fff8000.
     0x86440          k <> 0 goes to 0x86548: a6 = (cp + 24) & 7; a6 < k goes back to 0x86444, else 0x86550-0x86554:
                      a0 = cp + 24, call of __asan_report_load1 (0x59504, TB___asan_report_load1): the error path.
     0x86444          t1 = the byte at cp + 24, zero-extended: len.
     0x86448-0x8644c  a3 = 4; len < 4 (unsigned) goes to 0x8650c (no system command).
     0x86450-0x8646c  a6 = 0; a7 = the bitwise not of cp, 2^64 - 1 - cp; t0 = cp + 3; t1 = len - 3; t2 = cp + 1;
                      t3 = 0xf0; t4 = 0x13; t5 = 0x70.
     0x86470          the loop, for i = 0 .. len - 4 with a6 = i:
     0x86470            a7 < i (unsigned) goes to 0x86544 (the unimp word);
     0x86474-0x86480    a3 = cp + i and the instrumented check of the byte load there (a4 = its signed shadow byte k);
     0x86484            k <> 0 goes to 0x864e4: t6 = (cp + i) & 7; t6 < k goes back to 0x86488, else 0x864ec jumps to
                        0x86560-0x86564: a0 = cp + i, call of __asan_report_load1 (the error path);
     0x86488-0x8648c    t6 = cp + 1 + i; a4 = c[i], the byte at t6 - 1 = cp + i; 0x86490 a4 <> 0xf0 goes to 0x864d8;
     0x86494            i >= a7 (unsigned) goes to 0x86544 (the unimp word);
     0x86498-0x864a4    a4 = cp + i + 1 and the check of the byte load there (s0 = its signed shadow byte k);
     0x864a8            k <> 0 goes to 0x864f0: s1 = (cp + i + 1) & 7; s1 < k goes back to 0x864ac, else 0x864f8 jumps
                        to 0x86558-0x8655c: a0 = cp + i + 1, call of __asan_report_load1 (the error path);
     0x864ac            a4 = c[i + 1], the byte at t6; 0x864b0 a4 <> 0x13 goes to 0x864d8;
     0x864b4-0x864b8    a4 = i + 3; a7 < a4 (unsigned) goes to 0x86544 (the unimp word);
     0x864bc-0x864c8    a4 = cp + i + 3 and the check of the byte load there (s0 = its signed shadow byte k);
     0x864cc            k <> 0 goes to 0x864fc: a4 = (cp + i + 3) & 7; a4 < k goes back to 0x864d0, else
                        0x86504-0x86508: a0 = cp + i + 3, call of __asan_report_load1 (the error path);
     0x864d0            a3 = c[i + 3], the byte at t6 + 2; 0x864d4 a3 = 0x70 goes to 0x86528 (a system command at i);
     0x864d8-0x864dc    a6 = i + 1; a6 <> len - 3 goes back to 0x86470, else 0x864e0 jumps to 0x8650c.
     0x8650c-0x86510  (no system command) a0 = -10; a1 = a0 goes to 0x8653c; else 0x86514-0x86524: ra, s0 and s1
                      reloaded, sp = sp + 32, return.
     0x86528-0x8652c  (a system command) a0 = -10; a1 <> a0 goes to 0x8653c.
     0x86530-0x86534  a0 = the 4-byte load at 0x5e3d20, sign-extended: g_s.queued (g_s payload 0x5df640 = TB_g_s,
                      18264 bytes; TWorld.v A_S_queued = OFF_g_s + 18144). No instrumented check precedes this load.
     0x86538          a0 = a2 goes to 0x86514 (the return); else on to 0x8653c.
     0x8653c          call of __asan_handle_no_return (0x5a500, TB___asan_handle_no_return), then 0x86540 call of
                      abort (0x93390, TB_abort), then 0x86544 the word 0xc0001073 (unimp: a write of the read-only CSR
                      cycle, an illegal instruction that traps): the trap path.
   The return (0x86514) is the one return; on it every register but a0, a3 .. a7, t0 .. t6 is as at entry (s0 and s1
   hold again the values stored at entry).
   The loop is spec_system_at (zs c) len (DgnSpec.v:255-268: for (i = 0; i + 3 < len; i++), F0 13 xx 70), with
   byte_at (zs c) j = c[j].
   Against image A's code (lib/A/Prog/check_refusal_submit_c.v, 72 words, a 16-byte frame holding ra only): the same
   loads in the same order and the same compares with 0xf0, 0x13, 0x70 and -10; image B's code differs in:
     - its 32-byte frame, which also holds s0 and s1 (the loop keeps the shadow bytes of cp + i + 1 and cp + i + 3 in
       s0 and (cp + i + 1) & 7 in s1), restored before the return;
     - the test of cp & 3 at 0x8641c-0x86420 and the three unsigned compares of i, i and i + 3 with the bitwise not
       of cp at 0x86470, 0x86494 and 0x864b4-0x864b8, each a branch to the unimp word at 0x86544, which a return of
       abort also reaches; image A's code has none of these;
     - its loop counter, i counted up to len - 3 (image A's counts len - 3 - i down to 0), and its use of t4 .. t6,
       so t4, t5 and t6 are also unspecified at the return.
   Error paths and the premise that rules each out:
     - the branch at 0x86420 to the unimp word: taken when cp & 3 <> 0. cp mod 4 = 0 (and 0 < cp, with
       cp + 32 <= APPMEM_END from addressable m cp 32, so a0 = cp exactly) gives cp & 3 = 0;
     - the branches at 0x86470, 0x86494 and 0x864b8 to the unimp word: taken when i > 2^64 - 1 - cp,
       i >= 2^64 - 1 - cp or i + 3 > 2^64 - 1 - cp, i.e. when cp + i, cp + i + 1 or cp + i + 3 is 2^64 or more. In the
       loop i + 3 < len <= 32 (len <= length c = 32 by the model premise), and addressable m cp 32 gives
       cp + 32 <= APPMEM_END = 2^47: none is taken;
     - the four calls of __asan_report_load1 (0x86554, 0x86564, 0x8655c, 0x86508) are reached only when the signed
       shadow byte k of a loaded byte a is not 0 and (a & 7) >= k. Every loaded byte lies in [cp, cp + 32): cp + 24,
       and cp + i, cp + i + 1, cp + i + 3 with i + 3 < len <= 32. addressable m cp 32 gives k = 0 or
       a mod 8 < k <= 7 for each: the check passes;
     - the trap path (0x8653c / 0x86540 / 0x86544) is reached, with no system command, when rc = -10, and with a
       system command, when rc <> -10 or the sign-extended g_s.queued differs from a2 = bv_swrap 32 before. By tw_at
       the 4 bytes at 0x5e3d20 are sub Bw A_S_queued 4 (TWorldG.v tw_read_val, tw_lw); both are 32-bit values, equal
       exactly when S_queued Bw = before. check_refusal_submit_m Bw c rc before = Some _ rules out each case. The
       unimp word at 0x86544, after the call of abort, is on this path too, so the same premise rules it out there.
   Callee texts assumed: none (the only callees, __asan_report_load1, __asan_handle_no_return and abort, are on the
   error and trap paths).
   The caller: LLVMFuzzerTestOneInput, the calls at 0x825dc and 0x82758 (return addresses 0x825e0 and 0x8275c;
   DgnTransportBList.v PCall TB_check_refusal_submit), both with a0 = s4; the first with a1 = the a0 the call at
   0x825cc returns and a2 = s9, the second with a1 = s7 and a2 = the 8-byte load at s1 + 0x18.
   Form: lib/A/Prog/check_refusal_submit_c.v (image A's contract of this function), at image B's entry, frame, load
   addresses, runtime cells (lib/B/AsanCells.v), world table TMAP_B and harness hull, with t4 .. t6 added to the
   registers the post leaves unspecified. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.

Definition CHECK_REFUSAL_SUBMIT : Z := 0x8640c.
Definition CHECK_REFUSAL_SUBMIT_FRAME : Z := 32.
(* The int of the world the code loads: g_s.queued, at g_s's image-B base plus the member's offset in g_s. *)
Definition CHECK_REFUSAL_SUBMIT_QUEUED : Z := TB_g_s + (TW.A_S_queued - TW.OFF_g_s).
Lemma check_refusal_submit_queued_at : CHECK_REFUSAL_SUBMIT_QUEUED = 0x5e3d20.
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
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_refusal_submit_m Bw c rc before = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_REFUSAL_SUBMIT_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_REFUSAL_SUBMIT_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME CELL_K 8 ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME cp 32 ->
    addressable m cp 32 ->
    evt rsegs
      (fun ms' => exists (a0' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1 a2 a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_REFUSAL_SUBMIT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REFUSAL_SUBMIT) fc None m (seg_rom rsegs)).
