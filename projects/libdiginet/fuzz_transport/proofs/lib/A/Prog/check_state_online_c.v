(* check_state_online_contract: check_state_online (fuzz/fuzz_transport.c:497-505; model lib/TModel/TCb.v
   check_state_online_m) on fuzz_transport.asan (e89be137db17), a leaf that reads two ints of the harness global M and
   returns nothing. It stores into no harness global, so it takes the leaf form.
   Arguments: none.
   Premises: the world relation of image A (lib/A/Prog/TWorldG.v tw_at, table lib/A/Prog/TWorldA.v TMAP_A) between
   the memory m, read through csw_view (check_state_wake_c.v), and the world Bw; check_state_online_m Bw =
   Some (Bw', tt), which holds exactly when M.e2_acked and M.e1_us are both not 0 (TCb.v:403-404; truth x =
   negb (x =? 0)); the caller's stack below sp (stk, with room for the 16-byte frame); the frame [sp - 16, sp) outside
   the hull [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (lib/A/TransportG.v), so the frame store does not
   touch the world.
   Result: the run returns to ra with every register but a0 and a1 unchanged (a0 and a1 are not specified: the
   function is void). It writes only its frame (munch), every writable byte stays writable (wmono), the stack below sp
   stays usable (stk), Bw' = Bw, and the world relation still holds at the new memory with the same world. These are
   the plain contract's post facts (lib/Prog/T/check_state_online_c.v: B' = B, wmem rsegs m' B, munch of the frame
   only).

   Measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and the 52 code bytes of
   this function are equal in both files): symbol check_state_online, value 0x8520c, size 52 (13 words).
     0x8520c          sp = sp - 16: the frame is 16 bytes. No side-stack frame.
     0x85210          the 8-byte store of ra at sp - 8 (own frame); 0x8522c loads it back.
     0x85214-0x85218  a0 = 0x5df160: M (payload 0x5df160, 1648 bytes, the image's own asan_globals descriptor).
     0x8521c          a1 = the 4-byte load at a0 + 16 = 0x5df170, sign-extended: the member e2_acked (TWorld.v
                      A_M_e2_acked = OFF_M + 16).
     0x85220          a1 = 0 goes to 0x85238.
     0x85224          a0 = the 4-byte load at 0x5df174, sign-extended: the member e1_us (A_M_e1_us = OFF_M + 20).
     0x85228          a0 = 0 goes to 0x85238; else 0x8522c-0x85234: ra reloaded, sp = sp + 16, return. This is the
                      one return; on it a0 and a1 hold the two loaded ints and every other register is as at entry.
     0x85238          call of __asan_handle_no_return (0x5a4c4, TS___asan_handle_no_return), then 0x8523c call of
                      abort (0x93734): the trap path.
   No instrumented check precedes either load: the code reads no shadow byte and no runtime cell.
   Error paths and the premise that rules each out:
     - there is no call of an __asan_report_* entry in this function;
     - the trap path (0x85238 / 0x8523c) is reached only when one of the two loaded ints is 0. By tw_at the 4 bytes
       at 0x5df170 are sub Bw A_M_e2_acked 4 and the 4 bytes at 0x5df174 are sub Bw A_M_e1_us 4, so the loaded values
       are M_e2_acked Bw and M_e1_us Bw (TWorldG.v tw_read_val, tw_lw), and check_state_online_m Bw = Some _ gives
       both not 0.
   Callee texts assumed: none (the only callees, __asan_handle_no_return and abort, are on the trap path).
   The caller: notice reaches it by a tail jump (0x83718, after notice reloads its ra and restores its sp), so ra is
   notice's return address.
   Form: check_state_wake_c.v (the image-A leaf form of the exemplar), with the plain contract
   lib/Prog/T/check_state_online_c.v's world premise, model premise, B' = B and the world after. *)
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

Definition CHECK_STATE_ONLINE : Z := 0x8520c.
Definition CHECK_STATE_ONLINE_FRAME : Z := 16.
(* The two ints the code loads: M.e2_acked and M.e1_us, at M's image-A base plus the member's offset in M. *)
Definition CHECK_STATE_ONLINE_E2 : Z := TA_M + (TW.A_M_e2_acked - TW.OFF_M).
Definition CHECK_STATE_ONLINE_E1 : Z := TA_M + (TW.A_M_e1_us - TW.OFF_M).
Lemma check_state_online_e2_at : CHECK_STATE_ONLINE_E2 = 0x5df170.
Proof. reflexivity. Qed.
Lemma check_state_online_e1_at : CHECK_STATE_ONLINE_E1 = 0x5df174.
Proof. reflexivity. Qed.

Definition check_state_online_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_state_online_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_STATE_ONLINE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_STATE_ONLINE_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    evt rsegs
      (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_STATE_ONLINE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_STATE_ONLINE) fc None m (seg_rom rsegs)).
