(* check_inflight_acked_contract: check_inflight_acked (fuzz/fuzz_transport.c:476-484; model lib/TModel/TCb.v
   check_inflight_acked_m) on fuzz_transport.asan (e89be137db17), a leaf that reads two fields of the struct
   diginet_notice at its argument and four ints of the harness globals GOT and OW, and returns nothing. It stores
   into no harness global, so it takes the leaf form.
   Argument: a0 = p, the address of a struct diginet_notice (include/diginet/transport/diginet_session.h; counter at
   64 (4 bytes), retry at 68 (2)) holding the model's notice n (lib/TModel/TImg.v ntc).
   Premises:
   - the plain contract's struct premise ntc_at m p n sp FRAME (lib/Prog/T/TContract.v:96-111), stated over image
     A's memory for the fields the code reads: 0 < p, p mod 8 = 0, and the bytes at p + 64 and p + 68 are the
     little-endian counter and retry of n (bytes_at of TWorld.v put). The retry is a uint16_t: 0 <= n_retry n < 2^16,
     as the plain contract's u_at NB 68 2 = n_retry n gives. It is a premise here because put 2 keeps only the low
     16 bits while the model compares n_retry n with the 4-byte world value OW.acked_retry; the counter needs none,
     because the model equates it with the 4-byte world value OW.acked_counter;
   - the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between the
     memory m, read through mrd (csw_view, check_state_wake_c.v), and the world Bw; check_inflight_acked_m Bw n =
     Some (Bw', tt), which holds exactly when GOT.acked <= OW.acked, n_counter n = OW.acked_counter and
     n_retry n = OW.acked_retry (TCb.v:391-394);
   - the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp) outside the hull
     [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so the frame store does not touch
     the world; both ends of the frame in application memory (app_mem), so the frame is not shadow memory;
   - asan_cells m (lib/A/AsanCells.v: among others the 8 bytes at GOT_CELL_K 0xa4090 hold CELL_K 0xac9f8 and the 8
     bytes at CELL_K hold 0x7fff8000); GOT_CELL_K's 8 bytes, CELL_K's 8 bytes and each field the code loads lie
     outside the frame (off_stk; the plain contract's off_window), and each loaded field is marked usable
     (addressable).
   Result: the run returns to ra with every register but a0-a5 unchanged (they are not specified: the function is
   void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp stays
   usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These are the
   plain contract's post facts (lib/Prog/T/check_inflight_acked_c.v: B' = B, wmem rsegs m' B, munch of the frame
   only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 164 code bytes of
   this function are equal in both files): symbol check_inflight_acked, value 0x85240, size 164 (41 words).
     0x85240          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x85244          the 8-byte store of ra at sp - 8 (own frame); 0x852ac loads it back.
     0x85248, 0x85250 a1 = the 4-byte load at 0x5e53b8, sign-extended: GOT (payload 0x5e52e0, 224 bytes, the image's
                      own asan_globals descriptor at 0xa9140) + 216, the member acked (TWorld.v A_GOT_acked =
                      OFF_GOT + 216).
     0x8524c, 0x85254 a2 = 0x5f3060, the base of OW (payload 0x5f3060, 304 bytes, descriptor at 0xa9300).
     0x85258          a3 = the 4-byte load at a2 + 216 = 0x5f3138, sign-extended: OW.acked (A_OW_acked =
                      OFF_OW + 216).
     0x8525c          a3 < a1 (signed) goes to 0x852b8.
     0x85260-0x85268  a1 = the 8-byte load at GOT_CELL_K 0xa4090 (it holds CELL_K); a3 = the 8-byte load at CELL_K
                      0xac9f8 (it holds 0x7fff8000).
     0x8526c-0x85278  the instrumented check of the 4-byte load at p + 64: a1 = p + 64; a4 = the signed shadow byte k
                      at ((p + 64) >> 3) + 0x7fff8000. 0x8527c: k = 0 goes on to 0x85280; else 0x852c0-0x852c8:
                      a5 = ((p + 64) & 7) + 3, and a5 < k (signed) goes back to 0x85280; else 0x852cc-0x852d0:
                      a0 = p + 64 and the call of TS___asan_report_load4 (0x59608), the error path.
     0x85280          a1 = the 4-byte load at p + 64, sign-extended: n->counter.
     0x85284          a4 = the 4-byte load at a2 + 224 = 0x5f3140, sign-extended: OW.acked_counter
                      (A_OW_acked_counter = OFF_OW + 224). 0x85288: a1 <> a4 goes to 0x852b8.
     0x8528c-0x85298  the instrumented check of the 2-byte load at p + 68: a0 = p + 68; a1 = the signed shadow byte k
                      at ((p + 68) >> 3) + 0x7fff8000. 0x8529c: k = 0 goes on to 0x852a0; else 0x852d4-0x852dc:
                      a3 = ((p + 68) & 7) + 1, and a3 < k (signed) goes back to 0x852a0; else 0x852e0: the call of
                      TS___asan_report_load2 (0x59568) with a0 = p + 68, the error path.
     0x852a0          a0 = the 2-byte load at p + 68, zero-extended: n->retry.
     0x852a4          a1 = the 4-byte load at a2 + 228 = 0x5f3144, sign-extended: OW.acked_retry
                      (A_OW_acked_retry = OFF_OW + 228). 0x852a8: a1 <> a0 goes to 0x852b8.
                      No instrumented check precedes any of the four loads of GOT and OW.
     0x852ac-0x852b4  ra reloaded, sp = sp + 16, return. This is the one return; on it a0-a5 hold values the code
                      loaded or computed (a5 only after the check at 0x852c0) and every other register is as at entry.
     0x852b8          call of TS___asan_handle_no_return (0x5a4c4), then 0x852bc call of TS_abort (0x93734): the
                      trap path.
   Error paths and the premise that rules each out:
     - TS___asan_report_load4 (0x852d0): addressable m (p + 64) 4. Each byte x of [p + 64, p + 68) has its shadow
       byte k = 0 or x mod 8 < k <= 7. If the 4 bytes lie in one 8-byte granule, the last one gives k = 0 or
       ((p + 64) & 7) + 3 < k; if they cross a granule boundary, byte 7 of the first granule is in the range and
       gives k = 0. Either way the check passes. asan_cells gives the shadow base 0x7fff8000 the code uses.
     - TS___asan_report_load2 (0x852e0): addressable m (p + 68) 2, the same argument with ((p + 68) & 7) + 1.
     - the trap path (0x852b8 / 0x852bc): reached only when OW.acked < GOT.acked (signed), or the loaded counter
       differs from OW.acked_counter, or the loaded retry differs from OW.acked_retry. By tw_at the world loads are
       GOT_acked Bw and OW_acked Bw (s32_at) and OW_acked_counter Bw and OW_acked_retry Bw (4-byte u_at) sign-extended
       (TWorldG.v tw_read_val, tw_lw). check_inflight_acked_m Bw n = Some _ gives GOT_acked Bw <= OW_acked Bw,
       n_counter n = OW_acked_counter Bw (so 0 <= n_counter n < 2^32, and the put bytes at p + 64 load to the same
       sign-extended word) and n_retry n = OW_acked_retry Bw, which with 0 <= n_retry n < 2^16 makes the
       zero-extended 2-byte load equal to the sign-extended 4-byte load.
   The shadow bytes lie in shadow memory and the frame in application memory (app_mem of both frame ends), so the ra
   store does not change them; off_stk keeps the store off the two fields and the two cells.
   Callee texts assumed: none (the only callees are the error-path entries and TS___asan_handle_no_return / TS_abort
   on the trap path).
   Caller: notice, by the tail jump at 0x83634: notice moves its second argument n from a1 to a0 (0x83628) and
   gives back its own 16-byte frame (0x8362c-0x83630), so a0 = n (a struct diginet_notice its caller built) and ra
   is notice's return address.
   Form: lib/A/Prog/check_state_wake_c.v (image A's leaf exemplar: the world premise, the model premise, the evt rsegs
   run, the munch / wmono / stk post, Bw' = Bw and the world after) with fuzz_frame's image-A
   diginet_frame_is_keepalive_c.v for a pointer argument read under instrumented checks (the argument as a Z value
   in a0, bytes_at of each field read, asan_cells, app_mem of the frame ends, off_stk and addressable of each range
   loaded); TW, TC and TG are check_state_wake_c.v's module names, TI is TImg. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
Import ListNotations.
Open Scope Z_scope.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.

Definition CHECK_INFLIGHT_ACKED : Z := 0x85240.
Definition CHECK_INFLIGHT_ACKED_FRAME : Z := 16.
(* The world bytes the code loads: the global's image-A base (TWorldA.v), plus, for a member of a struct global,
   the member's offset in the global (TWorld.v; the same in every build). In order: GOT.acked (4 bytes); OW.acked
   (4 bytes); OW.acked_counter (4 bytes); OW.acked_retry (4 bytes). *)
Definition CHECK_INFLIGHT_ACKED_GOT_ACKED : Z := TA_GOT + (TW.A_GOT_acked - TW.OFF_GOT).
Definition CHECK_INFLIGHT_ACKED_OW_ACKED : Z := TA_OW + (TW.A_OW_acked - TW.OFF_OW).
Definition CHECK_INFLIGHT_ACKED_OW_COUNTER : Z := TA_OW + (TW.A_OW_acked_counter - TW.OFF_OW).
Definition CHECK_INFLIGHT_ACKED_OW_RETRY : Z := TA_OW + (TW.A_OW_acked_retry - TW.OFF_OW).
Lemma check_inflight_acked_got_acked_at : CHECK_INFLIGHT_ACKED_GOT_ACKED = 0x5e53b8.
Proof. reflexivity. Qed.
Lemma check_inflight_acked_ow_acked_at : CHECK_INFLIGHT_ACKED_OW_ACKED = 0x5f3138.
Proof. reflexivity. Qed.
Lemma check_inflight_acked_ow_counter_at : CHECK_INFLIGHT_ACKED_OW_COUNTER = 0x5f3140.
Proof. reflexivity. Qed.
Lemma check_inflight_acked_ow_retry_at : CHECK_INFLIGHT_ACKED_OW_RETRY = 0x5f3144.
Proof. reflexivity. Qed.

Definition check_inflight_acked_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo : Z) (n : TI.ntc) (Bw Bw' : list byte),
    0 < p ->
    p mod 8 = 0 ->
    0 <= TI.n_retry n < 2 ^ 16 ->
    bytes_at rsegs m (p + 64) (TW.put 4 (TI.n_counter n)) ->
    bytes_at rsegs m (p + 68) (TW.put 2 (TI.n_retry n)) ->
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_inflight_acked_m Bw n = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_INFLIGHT_ACKED_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_INFLIGHT_ACKED_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
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
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_INFLIGHT_ACKED) fc None m (seg_rom rsegs)).
