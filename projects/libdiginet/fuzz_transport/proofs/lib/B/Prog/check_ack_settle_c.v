(* check_ack_settle_contract: check_ack_settle (fuzz/fuzz_transport.c:680-688; model lib/TModel/TCb.v
   check_ack_settle_m) on fuzz_transport.asan-ubsan (41113a03c82f), a leaf that reads one int of the harness global
   GOT and one int of the harness global OW and returns nothing. It stores into no harness global, so it takes the
   leaf form.
   Arguments: none.
   Premises: the world relation of image B (lib/A/Prog/TWorldG.v tw_at, table lib/B/Prog/TWorldB.v TMAP_B) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; check_ack_settle_m Bw =
   Some (Bw', tt), which holds exactly when GOT.acks = OW.acks (TCb.v:565-566); the caller's stack below sp (stk,
   with room for the 16-byte frame); the frame [sp - 16, sp) outside the hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of
   the 18 harness globals (lib/B/TransportGB.v), so the frame store does not touch the world.
   Result: the run returns to ra with every register but a0 and a1 unchanged (a0 and a1 are not specified: the
   function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below
   sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These
   are the plain contract's post facts (lib/Prog/T/check_ack_settle_c.v: B' = B, wmem rsegs m' B, munch of the frame
   only).

   Measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 52 code bytes of this function are equal in both files):
   symbol check_ack_settle, value 0x85d88, size 52 (13 words).
     0x85d88          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x85d8c          the 8-byte store of ra at sp - 8 (own frame); 0x85da4 loads it back.
     0x85d90, 0x85d98 a0 = the 4-byte load at 0x5e502c, sign-extended: GOT (payload 0x5e4f60 = TB_GOT, 224 bytes, the
                      image's own asan_globals descriptor at 0xa8da0) + 204, the member acks (TWorld.v A_GOT_acks =
                      OFF_GOT + 204).
     0x85d94, 0x85d9c a1 = the 4-byte load at 0x5f2dac, sign-extended: OW (payload 0x5f2ce0 = TB_OW, 304 bytes,
                      descriptor at 0xa8f60) + 204, the member acks (A_OW_acks = OFF_OW + 204).
                      No instrumented check precedes either load: the code reads no shadow byte and no runtime cell.
     0x85da0          a0 <> a1 goes to 0x85db0; else 0x85da4-0x85dac: ra reloaded, sp = sp + 16, return. This is
                      the one return; on it a0 and a1 hold the two loaded ints and every other register is as at
                      entry.
     0x85db0          call of __asan_handle_no_return (0x5a500), then 0x85db4 call of abort (0x93390), then 0x85db8
                      the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps), reached only if abort returns: the trap path.
   Against image A's code (lib/A/Prog/check_ack_settle_c.v, 12 words): the words at 0x85d88-0x85db4 are the same
   twelve instructions with image B's auipc / lw / jal immediates; the word at 0x85db8 is the one instruction image
   A's code does not have.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* or __ubsan_handle_* entry in this function;
     - the trap path (0x85db0 / 0x85db4 / 0x85db8) is reached only when the two loaded ints differ. By tw_at the 4
       bytes at 0x5e502c are sub Bw A_GOT_acks 4 and the 4 bytes at 0x5f2dac are sub Bw A_OW_acks 4, so the loaded
       values are GOT_acks Bw and OW_acks Bw sign-extended (TWorldG.v tw_read_val, tw_lw; their view YP09.mbyte
       rsegs m is csw_view m unfolded), and check_ack_settle_m Bw = Some _ gives GOT_acks Bw = OW_acks Bw. The unimp
       word at 0x85db8 follows the call of abort on this path, so the same premise rules it out.
   Callee texts assumed: none (the only callees, __asan_handle_no_return and abort, are on the trap path).
   Caller: settle (the call at 0x838d0, return address 0x838d4).
   Form: lib/A/Prog/check_ack_settle_c.v (image A's contract of this function), at image B's entry, load addresses,
   world table TMAP_B and harness hull; TW, TC and TG are check_state_wake_c.v's module names. *)
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

Definition CHECK_ACK_SETTLE : Z := 0x85d88.
Definition CHECK_ACK_SETTLE_FRAME : Z := 16.
(* The world bytes the code loads: the global's image-B base (TWorldB.v), plus, for a member of a struct global,
   the member's offset in the global (TWorld.v; the same in every build). In order: GOT.acks (4 bytes); OW.acks (4
   bytes). *)
Definition CHECK_ACK_SETTLE_GOT_ACKS : Z := TB_GOT + (TW.A_GOT_acks - TW.OFF_GOT).
Definition CHECK_ACK_SETTLE_OW_ACKS : Z := TB_OW + (TW.A_OW_acks - TW.OFF_OW).
Lemma check_ack_settle_got_acks_at : CHECK_ACK_SETTLE_GOT_ACKS = 0x5e502c.
Proof. reflexivity. Qed.
Lemma check_ack_settle_ow_acks_at : CHECK_ACK_SETTLE_OW_ACKS = 0x5f2dac.
Proof. reflexivity. Qed.

Definition check_ack_settle_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_ack_settle_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_ACK_SETTLE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_ACK_SETTLE_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    evt rsegs
      (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_ACK_SETTLE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ACK_SETTLE) fc None m (seg_rom rsegs)).
