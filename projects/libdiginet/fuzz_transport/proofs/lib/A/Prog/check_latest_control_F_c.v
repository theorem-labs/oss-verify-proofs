(* Footprint form of check_latest_control_contract (check_latest_control_c.v; image A, entry 0x8420c): the same
   premises, then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under
   the footprint RNG (every data access of every step lies in RNG). The code touches every range on its one return
   path (the error path needs a shadow byte the addressable premise rules out), so no rng premise has a condition:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x84210) and its load (0x84244);
     - GOT_CELL_K 8 (0x84218) and CELL_K 8 (0x8421c): the runtime cells that give 0x7fff8000;
     - the shadow byte of fp + 32 at shadow_addr (fp + 32) = ((fp + 32) >> 3) + 0x7fff8000 (0x8422c);
     - [fp + 32, + 4): the 4-byte load of send (0x84234);
     - [CHECK_LATEST_CONTROL_HOST, + 4) = [0x5df1b4, 0x5df1b8): the 4-byte load of M.host_counter (0x8423c).
   The 4-byte load is checked by the one shadow byte of its first address, so the shadow range is one byte. The
   compare at 0x84250-0x84258 touches only registers.
   Form: check_state_wake_F_c.v (the rng premises after the contract's premises, the same post), with fuzz_frame's
   image-A diginet_frame_is_keepalive_F_c.v's rng premises for the runtime cells and the shadow byte. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_latest_control_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.

Definition check_latest_control_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte)
         (fp : Z) (frame : list byte),
    a0 = Z_to_bv 64 fp ->
    0 < fp ->
    fp mod 8 = 0 ->
    bytes_at rsegs m (fp + 32) (TW.put 4 (DgnSpec.sf_send (TC.rf frame))) ->
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_latest_control_m Bw frame = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_CONTROL_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_CONTROL_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_LATEST_CONTROL_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_LATEST_CONTROL_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_LATEST_CONTROL_FRAME CELL_K 8 ->
    off_stk sp CHECK_LATEST_CONTROL_FRAME (fp + 32) 4 ->
    addressable m (fp + 32) 4 ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_LATEST_CONTROL_FRAME) CHECK_LATEST_CONTROL_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (shadow_addr (fp + 32)) 1 ->
    ExecF.rng RNG (fp + 32) 4 ->
    ExecF.rng RNG CHECK_LATEST_CONTROL_HOST 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_CONTROL_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_CONTROL) fc None m (seg_rom rsegs)).
