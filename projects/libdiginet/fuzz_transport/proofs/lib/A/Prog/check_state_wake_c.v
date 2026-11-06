(* check_state_wake_contract: check_state_wake (fuzz/fuzz_transport.c:507-515; model lib/TModel/TCb.v
   check_state_wake_m) on fuzz_transport.asan (e89be137db17), a leaf that reads one int of the harness global M and
   returns nothing. It stores into no harness global, so it takes the leaf form.
   Arguments: none.
   Premises: the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between
   the memory m, read through mrd, and the world Bw; check_state_wake_m Bw = Some (Bw', tt), which holds exactly when
   M.foreign is 0 (TCb.v:407-408; truth x = negb (x =? 0)); the caller's stack below sp (stk, with room for the
   16-byte frame); the frame [sp - 16, sp) outside the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals
   (lib/A/TransportG.v), so the frame store does not touch the world.
   Result: the run returns to ra with every register but a0 unchanged (a0 is not specified: the function is void).
   It writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp stays usable
   (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These are the plain
   contract's post facts (lib/Prog/T/check_state_wake_c.v: B' = B, wmem rsegs m' B, munch of the frame only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 40 code bytes of
   this function are equal in both files): symbol check_state_wake, value 0x84370, size 40 (10 words).
     0x84370          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x84374          the 8-byte store of ra at sp - 8 (own frame); 0x84384 loads it back.
     0x84378-0x8437c  a0 = the 4-byte load at 0x5df178, sign-extended: M (payload 0x5df160, 1648 bytes, the
                      image's own asan_globals descriptor at 0xa9000) + 24, the member foreign (TWorld.v
                      A_M_foreign = OFF_M + 24). No instrumented check precedes this load: the code reads no
                      shadow byte and no runtime cell.
     0x84380          a0 <> 0 goes to 0x84390; else 0x84384-0x8438c: ra reloaded, sp = sp + 16, return. This is
                      the one return; on it a0 = 0 and every other register is as at entry.
     0x84390          call of __asan_handle_no_return (0x5a4c4), then 0x84394 call of abort (0x93734): the trap path.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* entry in this function;
     - the trap path (0x84390 / 0x84394) is reached only when the loaded int is not 0. By tw_at the 4 bytes at
       0x5df178 are sub Bw A_M_foreign 4, so the loaded value is M_foreign Bw (TWorldG.v tw_read_val, tw_lw; their
       view YP09.mbyte rsegs m is csw_view m unfolded), and check_state_wake_m Bw = Some _ gives M_foreign Bw = 0.
  Callee texts assumed: none (the only callees, __asan_handle_no_return and abort, are on the trap path).
   Form: lib/Prog/T/check_state_wake_c.v (the plain contract: world premise, model premise, B' = B and the world
   after) in the image-A leaf form of fuzz_frame's check_parse_refusal_c.v (the evt rsegs run, the munch / wmono /
   stk post, the kept registers in the MS (mkR ...) state). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.

Definition CHECK_STATE_WAKE : Z := 0x84370.
Definition CHECK_STATE_WAKE_FRAME : Z := 16.
(* The int the code loads: M.foreign, at M's image-A base plus the member's offset in M. *)
Definition CHECK_STATE_WAKE_FOREIGN : Z := TA_M + (TW.A_M_foreign - TW.OFF_M).
Lemma check_state_wake_foreign_at : CHECK_STATE_WAKE_FOREIGN = 0x5df178.
Proof. reflexivity. Qed.

(* The read view of the leaf form's memory: one byte value per address, through mrd (the code's loads). *)
Definition csw_view (m : word -> option byte) : Z -> option Z :=
  fun a => option_map (fun b : byte => bv_unsigned b) (mrd rsegs m (wa a)).

Definition check_state_wake_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_state_wake_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_STATE_WAKE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_STATE_WAKE_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    evt rsegs
      (fun ms' => exists (a0' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_STATE_WAKE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_STATE_WAKE) fc None m (seg_rom rsegs)).
