(* Footprint form of check_latest_frame_contract (check_latest_frame_c.v; image A, entry 0x843e0): the same premises,
   then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under the
   footprint RNG (every data access of every step lies in RNG). The ranges, in the code's order:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x843e4) and its load (0x84474);
     - GOT_CELL_K 8 (0x843ec) and CELL_K 8 (0x843f0): the runtime cells that give 0x7fff8000;
     - the shadow byte of fp + 56 at shadow_addr (fp + 56) (0x84400) and [fp + 56, + 8), body_len (0x84408);
     - [CHECK_LATEST_FRAME_MAXBODY, + 4) = [0x5df0b8, 0x5df0bc): g_cfg.max_body (0x84414);
     - the shadow byte of fp + 41 (0x84428) and [fp + 41, + 1), ncmds (0x84430);
     - [CHECK_LATEST_FRAME_MAXCMDS, + 4) = [0x5df0b4, 0x5df0b8): g_cfg.max_cmds (0x84434);
     - [TA_g_raw, + 4) = [0x5df0e0, 0x5df0e4): g_raw (0x84444), loaded only when cmds <> ncmds (0x8443c);
     - the shadow byte of fp + 32 (0x84458), [CHECK_LATEST_FRAME_HOST, + 4) = [0x5df1b4, 0x5df1b8): M.host_counter
       (0x84464), and [fp + 32, + 4), send (0x84468).
   check_latest_frame_m Bw frame cmds = Some _ rules out the branches to the trap and the addressable premises rule
   out the error paths, so the code reaches every load but g_raw's on its one return path. The g_raw premise has no
   condition either: the range is a harness global's payload, an image byte that the call site's footprint RNG_W W
   always holds, so a condition would only add a case to the walk. Each 8- or 4-byte member load is checked by the one
   shadow byte of its first address, so every shadow range is one byte; the compares at 0x84488-0x8448c and
   0x84498-0x844a0 touch only registers.
   Form: check_state_wake_F_c.v (the rng premises after the contract's premises, the same post), with fuzz_frame's
   image-A diginet_frame_is_keepalive_F_c.v's rng premises for the runtime cells and the shadow bytes. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_latest_frame_c.
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
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_latest_frame_m Bw frame cmds = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_FRAME_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_FRAME_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
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
    ExecF.rng RNG TA_g_raw 4 ->
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
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_FRAME) fc None m (seg_rom rsegs)).
