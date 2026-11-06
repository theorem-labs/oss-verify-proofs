(* rp_meter_counter_F_c: the footprint form of lib/A/Prog/rp_meter_counter_c.v rp_meter_counter_contract (image A, entry
   0x81168), as a STATEMENT (no proof), in the form of reac-repacer/fuzz_uci lib/A/Prog/rp_hot_clamp_F_c.v (without a
   shadow_rw premise, so that its translation lib/A/Prog/rp_meter_counter_cg.v takes no premise a caller cannot
   discharge), with the conditional ranges of libreac/fuzz_decode lib/A/Prog/reac_frame_is_reac_F_c.v and
   reac_decode_F_c.v. The run is an ExecF.evtF run under a footprint RNG: every data access of every step lies in RNG.
   The code (objdump of record of fuzz_wire.asan; full listing in rp_meter_counter_c.v):
     - stores ra at sp - 8 (0x8116c) and loads it back (0x8127c): the stack frame [sp - 16, sp);
     - only when a1 >= 14 (`bltu a1, a3` at 0x81174): loads 8 bytes at GOT_CELL_K 0x987e8 (0x8117c) and 8 bytes at
       CELL_K 0xa0778 (0x81180), then the bytes a0 + 12 (0x81198) and a0 + 13 (0x811b8);
     - only when a1 >= 1000 and a1 >= eo + 6 (0x811d4, 0x811dc): the bytes a0 + eo .. a0 + eo + 3 (0x811f4, 0x81214,
       0x81244, 0x81258), eo in {12, 16}, so inside [a0 + 12, a0 + 20);
     - before each of those byte loads, the shadow byte of its address, (a >> 3) + ASAN_K (0x81190, 0x811b0, 0x811ec,
       0x8120c, 0x8122c, 0x81240);
     - only when meter_ok holds: the shadow byte of a2 (0x81254) and the 2-byte store at a2 (0x81268).
   So RNG holds the stack frame, the two cells, and, under the condition under which the contract states that
   buffer's facts, each buffer and its shadow bytes. The cells are stated without the a1 >= 14 condition, as the
   template states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA rp_meter_counter_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_meter_counter_c.

Definition rp_meter_counter_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (14 <= bv_unsigned a1 -> (14 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs) ->
    (1000 <= bv_unsigned a1 -> (20 <= length bs)%nat) ->
    (PMC.meter_ok (bv_unsigned a1) bs = true -> wr_at rsegs m (bv_unsigned a2) 2) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_METER_COUNTER_FRAME <= bv_unsigned sp ->
    (14 <= bv_unsigned a1 -> off_stk sp RP_METER_COUNTER_FRAME (bv_unsigned a0 + 12) 2) ->
    (1000 <= bv_unsigned a1 -> off_stk sp RP_METER_COUNTER_FRAME (bv_unsigned a0 + 12) 8) ->
    (PMC.meter_ok (bv_unsigned a1) bs = true -> off_stk sp RP_METER_COUNTER_FRAME (bv_unsigned a2) 2) ->
    app_mem (bv_unsigned sp - RP_METER_COUNTER_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RP_METER_COUNTER_FRAME GOT_CELL_K 8 ->
    off_stk sp RP_METER_COUNTER_FRAME CELL_K 8 ->
    (14 <= bv_unsigned a1 -> addressable m (bv_unsigned a0 + 12) 2) ->
    (1000 <= bv_unsigned a1 -> addressable m (bv_unsigned a0 + 12) 8) ->
    (PMC.meter_ok (bv_unsigned a1) bs = true -> addressable m (bv_unsigned a2) 2) ->
    ExecF.rng RNG (bv_unsigned sp - RP_METER_COUNTER_FRAME) RP_METER_COUNTER_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    (14 <= bv_unsigned a1 -> ExecF.rng RNG (bv_unsigned a0 + 12) 2) ->
    (14 <= bv_unsigned a1 ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
         (shadow_addr (bv_unsigned a0 + 12 + 2 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1)) ->
    (1000 <= bv_unsigned a1 -> ExecF.rng RNG (bv_unsigned a0 + 12) 8) ->
    (1000 <= bv_unsigned a1 ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
         (shadow_addr (bv_unsigned a0 + 12 + 8 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1)) ->
    (PMC.meter_ok (bv_unsigned a1) bs = true -> ExecF.rng RNG (bv_unsigned a2) 2) ->
    (PMC.meter_ok (bv_unsigned a1) bs = true ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a2))
         (shadow_addr (bv_unsigned a2 + 2 - 1) - shadow_addr (bv_unsigned a2) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if PMC.meter_ok (bv_unsigned a1) bs then 1 else 0))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if PMC.meter_ok (bv_unsigned a1) bs
          then munch [(bv_unsigned sp - RP_METER_COUNTER_FRAME, bv_unsigned sp);
                      (bv_unsigned a2, bv_unsigned a2 + 2)] m m' /\
               bytes_at rsegs m' (bv_unsigned a2) (le2 (Z_to_bv 64 (PMC.meter_value (bv_unsigned a1) bs)))
          else munch [(bv_unsigned sp - RP_METER_COUNTER_FRAME, bv_unsigned sp)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_METER_COUNTER) fc None m (seg_rom rsegs)).
