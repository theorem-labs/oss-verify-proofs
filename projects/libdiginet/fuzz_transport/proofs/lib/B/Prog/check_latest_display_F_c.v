(* Footprint form of check_latest_display_contract (check_latest_display_c.v; image B, entry 0x84bd0): the same
   premises, then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under
   the footprint RNG (every data access of every step lies in RNG). The ranges:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x84bd4) and its load (0x84c04);
     - [CHECK_LATEST_DISPLAY_SENT, + 4) = [0x5dee28, 0x5dee2c): the 4-byte load of M.display_sent (0x84be0);
     - [CHECK_LATEST_DISPLAY_LAST, + 8) = [0x5dee20, 0x5dee28): the 8-byte load of M.last_display (0x84bec);
     - [TB_g_now, + 8) = [0x5ded80, 0x5ded88): the 8-byte load of g_now (0x84bf0);
     - [CHECK_LATEST_DISPLAY_GAP, + 4) = [0x5ded30, 0x5ded34): the 4-byte load of g_cfg.display_gap_us (0x84bf8).
   The last three loads run only when M.display_sent is not 0 (0x84be4). Their rng premises have no condition: each
   range is a part of a harness global's payload, an image byte that the call site's footprint RNG_W W always holds,
   so a condition would only add a case to the walk.
   There is no range of runtime cells and no shadow range: the code reads neither (no instrumented check), so there
   is no asan_cells, addressable or shadow_rw premise. The trap path (0x84c10 - 0x84c18) makes no data access of this
   function's own.
   Form: lib/A/Prog/check_latest_display_F_c.v (image A's footprint form: the rng premises after the contract's
   premises, the same post). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_latest_display_c.
Import ListNotations.
Open Scope Z_scope.

Definition check_latest_display_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_latest_display_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_LATEST_DISPLAY_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_LATEST_DISPLAY_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_LATEST_DISPLAY_FRAME) CHECK_LATEST_DISPLAY_FRAME ->
    ExecF.rng RNG CHECK_LATEST_DISPLAY_SENT 4 ->
    ExecF.rng RNG CHECK_LATEST_DISPLAY_LAST 8 ->
    ExecF.rng RNG TB_g_now 8 ->
    ExecF.rng RNG CHECK_LATEST_DISPLAY_GAP 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_LATEST_DISPLAY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_LATEST_DISPLAY) fc None m (seg_rom rsegs)).
