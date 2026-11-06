(* check_state_online_contract: check_state_online (fuzz/fuzz_transport.c:497-505; model lib/TModel/TCb.v
   check_state_online_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that reads two ints of the harness global
   M and returns nothing. It stores into no harness global, so it takes the leaf form.
   Arguments: none.
   Premises: the world relation of image B (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; check_state_online_m Bw =
   Some (Bw', tt), which holds exactly when M.e2_acked and M.e1_us are both not 0 (TCb.v:403-404; truth x =
   negb (x =? 0)); the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp) outside
   the hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 harness globals (lib/B/TransportGB.v), so the frame store does
   not touch the world.
   Result: the run returns to ra with every register but a0 and a1 unchanged (a0 and a1 are not specified: the
   function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp
   stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These are
   the plain contract's post facts (lib/Prog/T/check_state_online_c.v: B' = B, wmem rsegs m' B, munch of the frame
   only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 56 code bytes of this function are equal in both files):
   symbol check_state_online, value 0x85320, size 56 (14 words).
     0x85320          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x85324          the 8-byte store of ra at sp - 8 (own frame); 0x85340 loads it back.
     0x85328-0x8532c  a0 = 0x5dede0: M (payload 0x5dede0 = TB_M, 1648 bytes, the image's own asan_globals descriptor
                      at 0xa8c60).
     0x85330          a1 = the 4-byte load at a0 + 16 = 0x5dedf0, sign-extended: the member e2_acked (TWorld.v
                      A_M_e2_acked = OFF_M + 16).
     0x85334          a1 = 0 goes to 0x8534c.
     0x85338          a0 = the 4-byte load at 0x5dedf4, sign-extended: the member e1_us (A_M_e1_us = OFF_M + 20).
     0x8533c          a0 = 0 goes to 0x8534c; else 0x85340-0x85348: ra reloaded, sp = sp + 16, return. This is the
                      one return; on it a0 and a1 hold the two loaded ints and every other register is as at entry.
     0x8534c          call of __asan_handle_no_return (0x5a500, TB___asan_handle_no_return), then 0x85350 call of
                      abort (0x93390), then 0x85354 the word 0xc0001073 (unimp: a write of the read-only CSR cycle,
                      an illegal instruction that traps), reached only if abort returns: the trap path.
   No instrumented check precedes either load: the code reads no shadow byte and no runtime cell.
   Against image A's code (lib/A/Prog/check_state_online_c.v, 13 words): the words at 0x85320-0x85350 are the same
   thirteen instructions with image B's auipc / addi / jal immediates; the word at 0x85354 is the one instruction
   image A's code does not have.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* or __ubsan_handle_* entry in this function;
     - the trap path (0x8534c / 0x85350 / 0x85354) is reached only when one of the two loaded ints is 0. By tw_at the
       4 bytes at 0x5dedf0 are sub Bw A_M_e2_acked 4 and the 4 bytes at 0x5dedf4 are sub Bw A_M_e1_us 4, so the
       loaded values are M_e2_acked Bw and M_e1_us Bw (TWorldG.v tw_read_val, tw_lw), and check_state_online_m Bw =
       Some _ gives both not 0. The unimp word at 0x85354 follows the call of abort on this path, so the same premise
       rules it out.
   Callee texts assumed: none (the only callees, __asan_handle_no_return and abort, are on the trap path).
   The caller: notice reaches it by a tail jump (0x835ec, after notice reloads its ra at 0x835e4 and restores its sp
   at 0x835e8), so ra is notice's return address.
   Form: lib/A/Prog/check_state_online_c.v (image A's contract of this function), at image B's entry, load
   addresses, world table TMAP_B and harness hull. *)
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
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.

Definition CHECK_STATE_ONLINE : Z := 0x85320.
Definition CHECK_STATE_ONLINE_FRAME : Z := 16.
(* The two ints the code loads: M.e2_acked and M.e1_us, at M's image-B base plus the member's offset in M. *)
Definition CHECK_STATE_ONLINE_E2 : Z := TB_M + (TW.A_M_e2_acked - TW.OFF_M).
Definition CHECK_STATE_ONLINE_E1 : Z := TB_M + (TW.A_M_e1_us - TW.OFF_M).
Lemma check_state_online_e2_at : CHECK_STATE_ONLINE_E2 = 0x5dedf0.
Proof. reflexivity. Qed.
Lemma check_state_online_e1_at : CHECK_STATE_ONLINE_E1 = 0x5dedf4.
Proof. reflexivity. Qed.

Definition check_state_online_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_state_online_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_STATE_ONLINE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_STATE_ONLINE_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    evt rsegs
      (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_STATE_ONLINE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_STATE_ONLINE) fc None m (seg_rom rsegs)).
