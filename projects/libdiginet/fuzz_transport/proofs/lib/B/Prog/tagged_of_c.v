(* tagged_of_contract: tagged_of (fuzz/fuzz_transport.c:609-615; model lib/TModel/TCb.v tagged_of_m) on
   fuzz_transport.asan-ubsan (41113a03c82f), a leaf that reads the first three bytes of a command at its first argument
   and the harness global g_ncmd, and returns &g_cmd[serial] or NULL. It stores into no harness global, so it takes the
   leaf form. Image B only: image A's and the plain image's check_latest_sent and io_send inline it
   (lib/A/Prog/check_latest_sent_cg.v, lib/Prog/T/check_latest_sent_c.v, lib/Prog/T/io_send_c.v), so no plain contract
   or image-A statement of this function exists. Form: the image-A leaf contracts of the family, check_latest_frame_c.v
   (the world relation and the instrumented checks of image B's lib/B/Prog/check_latest_frame_c.v) with the register
   arguments and the result of lib/A/Prog/diginet_mac_is_digidesign_c.v (a byte pointer argument whose first three
   bytes the code reads with instrumented checks, a value in a0).
   Arguments: a0 = b, the address of the command bytes l (the bytes from b to the end of the caller's body;
   tagged_of_m reads at most l[0 .. 2]); a1 = n, a size_t (the bytes left in the body).
   Premises:
   - as a plain contract would state them: a0 = b, a1 = n with 0 <= n < 2^64; the bytes l at b (bytes_at); the world
     relation of image B (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between the memory m, read
     through csw_view (check_state_wake_c.v), and the world Bw; tagged_of_m Bw l n = Some (Bw', t), which holds exactly
     when n < 3, or l has a byte and l[0] <> TAG (0xa0), or l has three bytes, l[0] = TAG and serial = l[1] |
    l[2] << 7 is below CMDS_MAX (1024) when it is below g_ncmd (TCb.v:485-494); the caller's stack below sp
     (stk, with room for the 16-byte frame); the frame [sp - 16, sp) outside the hull [G_HARNESS_B_LO,
     G_HARNESS_B_HI) of the 18 harness globals (lib/B/TransportGB.v), so the frame store does not touch the world;
   - 0 < b: the UBSan check of b[0] (0x846b0) traps on b = 0;
   - for the instrumented checks (lib/B/AsanCells.v): asan_cells m (the 8 bytes at GOT_CELL_K = 0xa3cf0 hold
     CELL_K = 0xac678 and the 8 bytes at CELL_K hold 0x7fff8000); both ends of the frame in application memory
     (app_mem), so the frame is not a shadow byte; GOT_CELL_K 8 and CELL_K 8 outside the frame (off_stk); and, when
     3 <= n (the only runs that read b), [b, b + 3) outside the frame and marked usable in the shadow map
     (addressable). The condition 3 <= n is the code's: its first test (0x846ac) returns NULL at n < 3 before it
     reads anything, and a caller at the end of its body (n = 1 or 2) need not have b + 2 usable.
   Result: the run returns to ra with a0 = tagged_of_res t (TB_g_cmd + 40 s for t = Some s, 0 for t = None) and every
   register but a1 .. a4 unchanged (a1 .. a4 are not specified). It writes only its frame (munch), every writable
   byte stays writable (wmono), the stack below sp stays usable (stk), Bw' = Bw, and the world relation still holds
   at the new memory with the same world.

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 236 code bytes of this function are equal in both files):
   symbol tagged_of, value 0x846a0, size 236 (59 words).
     0x846a0          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x846a4          the 8-byte store of ra at sp - 8 (own frame); 0x84754 loads it back.
     0x846a8 - 0x846ac  n < 3 (unsigned) goes to 0x84750: a0 = 0 and the return.
     0x846b0          b = 0 goes to 0x84760, the unimp word (the trap path).
     0x846b4 - 0x846bc  a2 = the 8-byte load at GOT_CELL_K = 0xa3cf0 (.got): CELL_K; then the 8-byte load at CELL_K:
                      0x7fff8000.
     0x846c0 - 0x846cc  the instrumented check of the byte load at b: the signed shadow byte k at (b >> 3) + 0x7fff8000;
                      k <> 0 goes to 0x84764: (b & 7) < k goes back to 0x846d0, else 0x8476c calls __asan_report_load1
                      (0x59504, TB___asan_report_load1) with a0 = b: the error path.
     0x846d0 - 0x846d8  a1 = the byte at b; a1 <> 0xa0 (TAG) goes to 0x84750 (a0 = 0, the return).
     0x846dc - 0x846e4  a1 = b + 2; a1 <= 1 (unsigned; b + 2 wraps) goes to the unimp word.
     0x846e8 - 0x846f8  a0 = b + 1; the instrumented check of the byte load at b + 1 (k <> 0 goes to 0x84770: ((b + 1) & 7)
                      < k goes back to 0x846fc, else 0x84778 calls __asan_report_load1 with a0 = b + 1).
     0x846fc - 0x8470c  the shadow byte of b + 2 (0x84704); a0 = the byte at b + 1 (0x84708); that shadow byte <> 0 goes
                      to 0x8477c: ((b + 2) & 7) < k goes back to 0x84710, else 0x84788 calls __asan_report_load1 with
                      a0 = b + 2.
     0x84710          a1 = the byte at b + 2.
     0x84714 - 0x84718  a2 = the 4-byte load at 0x5df600, sign-extended: g_ncmd (payload 0x5df600 = TB_g_ncmd, 4 bytes,
                      TWorld.v OFF_g_ncmd). No instrumented check precedes this load.
     0x8471c - 0x84720  a0 = serial = (a1 << 7) | a0.
     0x84724          serial >= a2 (unsigned) goes to 0x84750 (a0 = 0, the return).
     0x84728 - 0x8472c  serial >= 0x401 (unsigned) goes to the unimp word (the UBSan bounds check of g_cmd[serial], 1024
                      elements: the index 1024 is allowed for the address).
     0x84730 - 0x84744  a0 = 40 serial; a1 = 0x5e5080 = TB_g_cmd (payload 40960 bytes); the bitwise not of a1 below a0
                      (unsigned; g_cmd + 40 serial wraps) goes to the unimp word.
     0x84748 - 0x8474c  a0 = g_cmd + 40 serial; the jump to 0x84754.
     0x84754 - 0x8475c  ra reloaded, sp = sp + 16, return: the one return, reached from 0x84750 (a0 = 0) and 0x8474c.
     0x84760          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that traps):
                      the trap path.
   Error paths and the premise that rules each out:
     - __asan_report_load1 at 0x8476c, 0x84778, 0x84788: reached (only when 3 <= n) when the shadow byte k of b + j
       (j = 0, 1, 2) is not 0 and ((b + j) & 7) >= k. addressable m b 3 gives, for each of the 3 bytes, k = 0 or
       (b + j) mod 8 < k <= 7: the check passes. asan_cells gives 0x7fff8000, so the loaded byte is the shadow byte
       addressable speaks of;
     - the trap path (0x84760), from four branches: b = 0 by 0 < b; b + 2 wraps only when b + 2 >= 2^64, and
       addressable m b 3 puts b + 3 below the end of application memory; serial >= 0x401 is reached only after
       serial < g_ncmd, where tagged_of_m Bw l n = Some _ gives serial < CMDS_MAX = 1024; g_cmd + 40 serial wraps only
       when 0x5e5080 + 40 serial >= 2^64, and serial < 1024.
   With l's bytes (bytes_at; tagged_of_m = Some _ gives l a first byte when 3 <= n and three bytes when l[0] = TAG) and
   the world's (tw_at: sub Bw OFF_g_ncmd 4 is the 4 bytes at TB_g_ncmd; TWorldG.v tw_read_val, tw_lw) the branches
   test the model's: n < 3, at8 l 0 <> TAG, serial < g_ncmd Bw (g_ncmd Bw is below 2^32; a value of 2^31 or more
   sign-extends to an unsigned value above any serial, as its unsigned value is above it); so the result register is
   tagged_of_res t.
   Against image A's code: none (inlined there); against its inlined copies in image A's check_latest_sent
   (0x8459c - 0x84608, lib/A/Prog/check_latest_sent_cg.v): the same loads and compares; image B's own code adds the
   UBSan checks (0x846b0, 0x846dc - 0x846e4, 0x84728 - 0x84744) and the unimp word.
   Callee texts assumed: none (the only callees, the three calls of __asan_report_load1, are on the error path).
   The callers: io_send, the call at 0x831c0 (return address 0x831c4; DgnTransportBList.v PCall TB_tagged_of), with
   a0 = the body pointer of its struct spec_frame plus at and a1 = its body length minus at; check_latest_sent, the call
   at 0x84998 (return address 0x8499c), with a0 = s5 = body + at and a1 = s6 = len - at. *)
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

Definition TAGGED_OF : Z := 0x846a0.
Definition TAGGED_OF_FRAME : Z := 16.
(* The int the code loads from the world: g_ncmd, at its image-B base (TWorld.v OFF_g_ncmd in the world). *)
Definition TAGGED_OF_NCMD : Z := TB_g_ncmd.
Lemma tagged_of_ncmd_at : TAGGED_OF_NCMD = 0x5df600.
Proof. reflexivity. Qed.
Lemma tagged_of_cmd_at : TB_g_cmd = 0x5e5080.
Proof. reflexivity. Qed.

(* The result: &g_cmd[s] at image B's g_cmd (struct tagged, 40 bytes) for Some s, NULL for None. *)
Definition tagged_of_res (t : option Z) : Z :=
  match t with Some s => TB_g_cmd + 40 * s | None => 0 end.

Definition tagged_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte)
         (b n : Z) (l : list byte) (t : option Z),
    a0 = Z_to_bv 64 b ->
    a1 = Z_to_bv 64 n ->
    0 <= n < 2 ^ 64 ->
    0 < b ->
    bytes_at rsegs m b l ->
    tw_at TMAP_B (csw_view m) Bw ->
    TC.tagged_of_m Bw l n = Some (Bw', t) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + TAGGED_OF_FRAME <= bv_unsigned sp ->
    off_stk sp TAGGED_OF_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - TAGGED_OF_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp TAGGED_OF_FRAME GOT_CELL_K 8 ->
    off_stk sp TAGGED_OF_FRAME CELL_K 8 ->
    (3 <= n -> off_stk sp TAGGED_OF_FRAME b 3) ->
    (3 <= n -> addressable m b 3) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (tagged_of_res t)) a1' a2' a3' a4' a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - TAGGED_OF_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TAGGED_OF) fc None m (seg_rom rsegs)).
