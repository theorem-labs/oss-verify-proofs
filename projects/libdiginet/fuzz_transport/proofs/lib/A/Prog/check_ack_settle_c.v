(* check_ack_settle_contract: check_ack_settle (fuzz/fuzz_transport.c:680-688; model lib/TModel/TCb.v
   check_ack_settle_m) on fuzz_transport.asan (e89be137db17), a leaf that reads one int of the harness global GOT and
   one int of the harness global OW and returns nothing. It stores into no harness global, so it takes the leaf form.
   Arguments: none.
   Premises: the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between
   the memory m, read through mrd (csw_view, check_state_wake_c.v), and the world Bw; check_ack_settle_m Bw =
   Some (Bw', tt), which holds exactly when GOT.acks = OW.acks (TCb.v:565-566); the caller's stack below sp (stk, with
   room for the 16-byte frame); the frame [sp - 16, sp) outside the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18
   harness globals (lib/A/TransportG.v), so the frame store does not touch the world.
   Result: the run returns to ra with every register but a0 and a1 unchanged (a0 and a1 are not specified: the
   function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below
   sp stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These
   are the plain contract's post facts (lib/Prog/T/check_ack_settle_c.v: B' = B, wmem rsegs m' B, munch of the frame
   only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 48 code bytes of
   this function are equal in both files): symbol check_ack_settle, value 0x85b04, size 48 (12 words).
     0x85b04          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x85b08          the 8-byte store of ra at sp - 8 (own frame); 0x85b20 loads it back.
     0x85b0c, 0x85b14 a0 = the 4-byte load at 0x5e53ac, sign-extended: GOT (payload 0x5e52e0, 224 bytes, the image's
                      own asan_globals descriptor at 0xa9140) + 204, the member acks (TWorld.v A_GOT_acks =
                      OFF_GOT + 204).
     0x85b10, 0x85b18 a1 = the 4-byte load at 0x5f312c, sign-extended: OW (payload 0x5f3060, 304 bytes, descriptor
                      at 0xa9300) + 204, the member acks (A_OW_acks = OFF_OW + 204).
                      No instrumented check precedes either load: the code reads no shadow byte and no runtime cell.
     0x85b1c          a0 <> a1 goes to 0x85b2c; else 0x85b20-0x85b28: ra reloaded, sp = sp + 16, return. This is
                      the one return; on it a0 and a1 hold the two loaded ints and every other register is as at
                      entry.
     0x85b2c          call of TS___asan_handle_no_return (0x5a4c4), then 0x85b30 call of TS_abort (0x93734): the
                      trap path.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* entry in this function;
     - the trap path (0x85b2c / 0x85b30) is reached only when the two loaded ints differ. By tw_at the 4 bytes at
       0x5e53ac are sub Bw A_GOT_acks 4 and the 4 bytes at 0x5f312c are sub Bw A_OW_acks 4, so the loaded values
       are GOT_acks Bw and OW_acks Bw sign-extended (TWorldG.v tw_read_val, tw_lw; their view YP09.mbyte rsegs m is
       csw_view m unfolded), and check_ack_settle_m Bw = Some _ gives GOT_acks Bw = OW_acks Bw.
   Callee texts assumed: none (the only callees, TS___asan_handle_no_return and TS_abort, are on the trap path).
   Caller: settle (the call at 0x83cbc, return address 0x83cc0).
   Form: lib/A/Prog/check_state_wake_c.v (image A's leaf exemplar: the world premise, the model premise, the evt rsegs
   run, the munch / wmono / stk post, Bw' = Bw and the world after, the kept registers in the MS (mkR ...) state);
   TW, TC and TG are that file's module names. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_ACK_SETTLE : Z := 0x85b04.
Definition CHECK_ACK_SETTLE_FRAME : Z := 16.
(* The world bytes the code loads: the global's image-A base (TWorldA.v), plus, for a member of a struct global,
   the member's offset in the global (TWorld.v; the same in every build). In order: GOT.acks (4 bytes); OW.acks (4
   bytes). *)
Definition CHECK_ACK_SETTLE_GOT_ACKS : Z := TA_GOT + (TW.A_GOT_acks - TW.OFF_GOT).
Definition CHECK_ACK_SETTLE_OW_ACKS : Z := TA_OW + (TW.A_OW_acks - TW.OFF_OW).
Lemma check_ack_settle_got_acks_at : CHECK_ACK_SETTLE_GOT_ACKS = 0x5e53ac.
Proof. reflexivity. Qed.
Lemma check_ack_settle_ow_acks_at : CHECK_ACK_SETTLE_OW_ACKS = 0x5f312c.
Proof. reflexivity. Qed.

Definition check_ack_settle_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_ack_settle_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_ACK_SETTLE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_ACK_SETTLE_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    evt rsegs
      (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_ACK_SETTLE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ACK_SETTLE) fc None m (seg_rom rsegs)).
