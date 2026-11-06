(* Footprint form of check_latest_frame_contract (check_latest_frame_c.v; image B, entry 0x8478c): the same premises,
   then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under the
   footprint RNG (every data access of every step lies in RNG). The ranges, in the code's order:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x84790) and its load (0x84828);
     - GOT_CELL_K 8 (0x847a0) and CELL_K 8 (0x847a4): the runtime cells that give 0x7fff8000;
     - the shadow byte of fp + 56 at shadow_addr (fp + 56) (0x847b4) and [fp + 56, + 8), body_len (0x847bc);
     - [CHECK_LATEST_FRAME_MAXBODY, + 4) = [0x5ded38, 0x5ded3c): g_cfg.max_body (0x847c8);
     - the shadow byte of fp + 41 (0x847dc) and [fp + 41, + 1), ncmds (0x847e4);
     - [CHECK_LATEST_FRAME_MAXCMDS, + 4) = [0x5ded34, 0x5ded38): g_cfg.max_cmds (0x847e8);
     - [TB_g_raw, + 4) = [0x5ded60, 0x5ded64): g_raw (0x847f8), loaded only when cmds <> ncmds (0x847f0);
     - the shadow byte of fp + 32 (0x8480c), [CHECK_LATEST_FRAME_HOST, + 4) = [0x5dee34, 0x5dee38): M.host_counter
       (0x84818), and [fp + 32, + 4), send (0x8481c).
   check_latest_frame_m Bw frame cmds = Some _ rules out the branches to the trap, fp mod 8 = 0 rules out the branch
   at 0x84798, and the addressable premises rule out the error paths, so the code reaches every load but g_raw's on
   its one return path. The g_raw premise has no condition either: the range is a harness global's payload, an image
   byte that the call site's footprint RNG_W W always holds, so a condition would only add a case to the walk. Each 8-
   or 4-byte member load is checked by the one shadow byte of its first address, so every shadow range is one byte;
   the test at 0x84794, the compares at 0x84840-0x84844 and 0x84850-0x84858 touch only registers, and the trap path
   (0x84834 - 0x8483c) makes no data access of this function's own.
   Form: lib/A/Prog/check_latest_frame_F_c.v (image A's footprint form: the rng premises after the contract's
   premises, the same post), at image B's load addresses and runtime cells. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_latest_frame_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.

Definition check_latest_frame_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte)
         (fp : Z) (frame : list byte) (cmds : Z),
    a0 = Z_to_bv 64 fp ->
    a1 = Z_to_bv 64 (bv_swrap 32 cmds) ->
    0 <= cmds < 2 ^ 32 ->
    0 < fp ->
    fp mod 8 = 0 ->
    bytes_at rsegs m (fp + 32) (TW.put 4 (DgnSpec.sf_send (TC.rf frame))) ->
    bytes_at rsegs m (fp + 41) (TW.put 1 (DgnSpec.sf_ncmds (TC.rf frame))) ->
    bytes_at rsegs m (fp + 56) (TW.put 8 (DgnSpec.sf_body_len (TC.rf frame))) ->
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_latest_frame_m Bw frame cmds = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_FRAME_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_FRAME_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_LATEST_FRAME_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_LATEST_FRAME_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_LATEST_FRAME_FRAME CELL_K 8 ->
    off_stk sp CHECK_LATEST_FRAME_FRAME (fp + 56) 8 ->
    addressable m (fp + 56) 8 ->
    off_stk sp CHECK_LATEST_FRAME_FRAME (fp + 41) 1 ->
    addressable m (fp + 41) 1 ->
    off_stk sp CHECK_LATEST_FRAME_FRAME (fp + 32) 4 ->
    addressable m (fp + 32) 4 ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_LATEST_FRAME_FRAME) CHECK_LATEST_FRAME_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (shadow_addr (fp + 56)) 1 ->
    ExecF.rng RNG (fp + 56) 8 ->
    ExecF.rng RNG CHECK_LATEST_FRAME_MAXBODY 4 ->
    ExecF.rng RNG (shadow_addr (fp + 41)) 1 ->
    ExecF.rng RNG (fp + 41) 1 ->
    ExecF.rng RNG CHECK_LATEST_FRAME_MAXCMDS 4 ->
    ExecF.rng RNG TB_g_raw 4 ->
    ExecF.rng RNG (shadow_addr (fp + 32)) 1 ->
    ExecF.rng RNG CHECK_LATEST_FRAME_HOST 4 ->
    ExecF.rng RNG (fp + 32) 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_FRAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_FRAME) fc None m (seg_rom rsegs)).
