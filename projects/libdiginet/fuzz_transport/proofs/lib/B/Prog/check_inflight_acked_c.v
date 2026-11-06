(* check_inflight_acked_contract: check_inflight_acked (fuzz/fuzz_transport.c:476-484; model lib/TModel/TCb.v
   check_inflight_acked_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that reads two fields of the struct
   diginet_notice at its argument and four ints of the harness globals GOT and OW, and returns nothing. It stores
   into no harness global, so it takes the leaf form.
   Argument: a0 = p, the address of a struct diginet_notice (include/diginet/transport/diginet_session.h; counter at
   64 (4 bytes), retry at 68 (2)) holding the model's notice n (lib/TModel/TImg.v ntc).
   Premises:
   - the plain contract's struct premise ntc_at m p n sp FRAME (lib/Prog/T/TContract.v:96-111), stated over image
     B's memory for the fields the code reads: 0 < p, p mod 8 = 0, and the bytes at p + 64 and p + 68 are the
     little-endian counter and retry of n (bytes_at of TWorld.v put). The retry is a uint16_t: 0 <= n_retry n < 2^16,
     as the plain contract's u_at NB 68 2 = n_retry n gives. It is a premise here because put 2 keeps only the low
     16 bits while the model compares n_retry n with the 4-byte world value OW.acked_retry; the counter needs none,
     because the model equates it with the 4-byte world value OW.acked_counter;
   - the world relation of image B (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between the
     memory m, read through mrd (csw_view, check_state_wake_c.v), and the world Bw; check_inflight_acked_m Bw n =
     Some (Bw', tt), which holds exactly when GOT.acked <= OW.acked, n_counter n = OW.acked_counter and
     n_retry n = OW.acked_retry (TCb.v:391-394);
   - the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp) outside the hull
     [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 harness globals (lib/B/TransportGB.v), so the frame store does not
     touch the world; both ends of the frame in application memory (app_mem), so the frame is not shadow memory;
   - asan_cells m (lib/B/AsanCells.v: among others the 8 bytes at GOT_CELL_K 0xa3cf0 hold CELL_K 0xac678 and the 8
     bytes at CELL_K hold 0x7fff8000); GOT_CELL_K's 8 bytes, CELL_K's 8 bytes and each field the code loads lie
     outside the frame (off_stk; the plain contract's off_window), and each loaded field is marked usable
     (addressable).
   Result: the run returns to ra with every register but a0-a5 unchanged (they are not specified: the function is
   void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp stays
   usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These are the
   plain contract's post facts (lib/Prog/T/check_inflight_acked_c.v: B' = B, wmem rsegs m' B, munch of the frame
   only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 176 code bytes of this function are equal in both files):
   symbol check_inflight_acked, value 0x85358, size 176 (44 words).
     0x85358          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x8535c          the 8-byte store of ra at sp - 8 (own frame); 0x853cc loads it back.
     0x85360, 0x85368 a1 = the 4-byte load at 0x5e5038, sign-extended: GOT (payload 0x5e4f60 = TB_GOT, 224 bytes, the
                      image's own asan_globals descriptor at 0xa8da0) + 216, the member acked (TWorld.v
                      A_GOT_acked = OFF_GOT + 216).
     0x85364, 0x8536c a2 = 0x5f2ce0, the base of OW (payload 0x5f2ce0 = TB_OW, 304 bytes, descriptor at 0xa8f60).
     0x85370          a3 = the 4-byte load at a2 + 216 = 0x5f2db8, sign-extended: OW.acked (A_OW_acked =
                      OFF_OW + 216).
     0x85374          a3 < a1 (signed) goes to 0x853d8.
     0x85378-0x8537c  a1 = p & 7; a1 <> 0 goes to 0x853e0 (the unimp word below): the trap path.
     0x85380-0x85388  a1 = the 8-byte load at GOT_CELL_K 0xa3cf0 (it holds CELL_K); a3 = the 8-byte load at CELL_K
                      0xac678 (it holds 0x7fff8000).
     0x8538c-0x85398  the instrumented check of the 4-byte load at p + 64: a1 = p + 64; a4 = the signed shadow byte k
                      at ((p + 64) >> 3) + 0x7fff8000. 0x8539c: k = 0 goes on to 0x853a0; else 0x853e4-0x853ec:
                      a5 = ((p + 64) & 7) + 3, and a5 < k (signed) goes back to 0x853a0; else 0x853f0-0x853f4:
                      a0 = p + 64 and the call of __asan_report_load4 (0x59644), the error path.
     0x853a0          a1 = the 4-byte load at p + 64, sign-extended: n->counter.
     0x853a4          a4 = the 4-byte load at a2 + 224 = 0x5f2dc0, sign-extended: OW.acked_counter
                      (A_OW_acked_counter = OFF_OW + 224). 0x853a8: a1 <> a4 goes to 0x853d8.
     0x853ac-0x853b8  the instrumented check of the 2-byte load at p + 68: a0 = p + 68; a1 = the signed shadow byte k
                      at ((p + 68) >> 3) + 0x7fff8000. 0x853bc: k = 0 goes on to 0x853c0; else 0x853f8-0x85400:
                      a3 = ((p + 68) & 7) + 1, and a3 < k (signed) goes back to 0x853c0; else 0x85404: the call of
                      __asan_report_load2 (0x595a4) with a0 = p + 68, the error path.
     0x853c0          a0 = the 2-byte load at p + 68, zero-extended: n->retry.
     0x853c4          a1 = the 4-byte load at a2 + 228 = 0x5f2dc4, sign-extended: OW.acked_retry
                      (A_OW_acked_retry = OFF_OW + 228). 0x853c8: a1 <> a0 goes to 0x853d8.
                      No instrumented check precedes any of the four loads of GOT and OW.
     0x853cc-0x853d4  ra reloaded, sp = sp + 16, return. This is the one return; on it a0-a5 hold values the code
                      loaded or computed (a5 only after the check at 0x853e4) and every other register is as at entry.
     0x853d8          call of __asan_handle_no_return (0x5a500), then 0x853dc call of abort (0x93390), then 0x853e0
                      the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps), reached only if abort returns or from the test at 0x8537c: the trap path.
   Against image A's code (lib/A/Prog/check_inflight_acked_c.v, 41 words): image B's code has three words image A's
   code does not have: the test of p & 7 at 0x85378-0x8537c, and the unimp word at 0x853e0. The other 41 words are
   image A's instructions in the same order with image B's auipc / addi / lw / ld / branch / jal immediates, the same
   registers and the same field offsets 64 and 68.
   Error paths and the premise that rules each out:
     - there is no call of an __ubsan_handle_* entry in this function;
     - the branch at 0x8537c to the unimp word: p mod 8 = 0. The register a0 is Z_to_bv 64 p and 8 divides 2^64, so
       its low three bits are p mod 8 = 0, a1 = 0 and the branch is not taken;
     - __asan_report_load4 (0x853f4): addressable m (p + 64) 4. Each byte x of [p + 64, p + 68) has its shadow
       byte k = 0 or x mod 8 < k <= 7. If the 4 bytes lie in one 8-byte granule, the last one gives k = 0 or
       ((p + 64) & 7) + 3 < k; if they cross a granule boundary, byte 7 of the first granule is in the range and
       gives k = 0. Either way the check passes. asan_cells gives the shadow base 0x7fff8000 the code uses.
     - __asan_report_load2 (0x85404): addressable m (p + 68) 2, the same argument with ((p + 68) & 7) + 1.
     - the trap path (0x853d8 / 0x853dc / 0x853e0): reached from 0x85374, 0x853a8 and 0x853c8 only when OW.acked <
       GOT.acked (signed), or the loaded counter differs from OW.acked_counter, or the loaded retry differs from
       OW.acked_retry. By tw_at the world loads are GOT_acked Bw and OW_acked Bw (s32_at) and OW_acked_counter Bw
       and OW_acked_retry Bw (4-byte u_at) sign-extended (TWorldG.v tw_read_val, tw_lw). check_inflight_acked_m Bw n
       = Some _ gives GOT_acked Bw <= OW_acked Bw, n_counter n = OW_acked_counter Bw (so 0 <= n_counter n < 2^32,
       and the put bytes at p + 64 load to the same sign-extended word) and n_retry n = OW_acked_retry Bw, which
       with 0 <= n_retry n < 2^16 makes the zero-extended 2-byte load equal to the sign-extended 4-byte load. The
       unimp word at 0x853e0 follows the call of abort on this path, so the same premise rules it out there.
   The shadow bytes lie in shadow memory and the frame in application memory (app_mem of both frame ends), so the ra
   store does not change them; off_stk keeps the store off the two fields and the two cells.
   Callee texts assumed: none (the only callees are the error-path entries and __asan_handle_no_return / abort on
   the trap path).
   Caller: notice, by the tail jump at 0x834f0: notice moves its second argument n from a1 to a0 (0x834e4) and
   gives back its own 16-byte frame (0x834e8-0x834ec), so a0 = n (a struct diginet_notice its caller built) and ra
   is notice's return address.
   Form: lib/A/Prog/check_inflight_acked_c.v (image A's contract of this function), at image B's entry, load
   addresses, world table TMAP_B, harness hull and runtime cells (lib/B/AsanCells.v); TW, TC and TG are
   check_state_wake_c.v's module names, TI is TImg. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
Import ListNotations.
Open Scope Z_scope.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.

Definition CHECK_INFLIGHT_ACKED : Z := 0x85358.
Definition CHECK_INFLIGHT_ACKED_FRAME : Z := 16.
(* The world bytes the code loads: the global's image-B base (TWorldB.v), plus, for a member of a struct global,
   the member's offset in the global (TWorld.v; the same in every build). In order: GOT.acked (4 bytes); OW.acked
   (4 bytes); OW.acked_counter (4 bytes); OW.acked_retry (4 bytes). *)
Definition CHECK_INFLIGHT_ACKED_GOT_ACKED : Z := TB_GOT + (TW.A_GOT_acked - TW.OFF_GOT).
Definition CHECK_INFLIGHT_ACKED_OW_ACKED : Z := TB_OW + (TW.A_OW_acked - TW.OFF_OW).
Definition CHECK_INFLIGHT_ACKED_OW_COUNTER : Z := TB_OW + (TW.A_OW_acked_counter - TW.OFF_OW).
Definition CHECK_INFLIGHT_ACKED_OW_RETRY : Z := TB_OW + (TW.A_OW_acked_retry - TW.OFF_OW).
Lemma check_inflight_acked_got_acked_at : CHECK_INFLIGHT_ACKED_GOT_ACKED = 0x5e5038.
Proof. reflexivity. Qed.
Lemma check_inflight_acked_ow_acked_at : CHECK_INFLIGHT_ACKED_OW_ACKED = 0x5f2db8.
Proof. reflexivity. Qed.
Lemma check_inflight_acked_ow_counter_at : CHECK_INFLIGHT_ACKED_OW_COUNTER = 0x5f2dc0.
Proof. reflexivity. Qed.
Lemma check_inflight_acked_ow_retry_at : CHECK_INFLIGHT_ACKED_OW_RETRY = 0x5f2dc4.
Proof. reflexivity. Qed.

Definition check_inflight_acked_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo : Z) (n : TI.ntc) (Bw Bw' : list byte),
    0 < p ->
    p mod 8 = 0 ->
    0 <= TI.n_retry n < 2 ^ 16 ->
    bytes_at rsegs m (p + 64) (TW.put 4 (TI.n_counter n)) ->
    bytes_at rsegs m (p + 68) (TW.put 2 (TI.n_retry n)) ->
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_inflight_acked_m Bw n = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_INFLIGHT_ACKED_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_INFLIGHT_ACKED_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_INFLIGHT_ACKED_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_INFLIGHT_ACKED_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_INFLIGHT_ACKED_FRAME CELL_K 8 ->
    off_stk sp CHECK_INFLIGHT_ACKED_FRAME (p + 64) 4 -> addressable m (p + 64) 4 ->
    off_stk sp CHECK_INFLIGHT_ACKED_FRAME (p + 68) 2 -> addressable m (p + 68) 2 ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_INFLIGHT_ACKED_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_INFLIGHT_ACKED) fc None m (seg_rom rsegs)).
