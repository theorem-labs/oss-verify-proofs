(* Footprint form of rp_meter_counter_contract (lib/B/Prog/rp_meter_counter_c.v; image B, entry 0x81144), as a
   STATEMENT (no proof). No released ASan statement of this function exists, so nothing is copied: the text is in the
   form of reac-repacer/fuzz_uci lib/B/Prog/rp_hot_clamp_F_c.v (the leaf's footprint contract, without a shadow_rw
   premise, so that its leaf-form translation lib/B/Prog/rp_meter_counter_cg.v takes no premise a caller cannot
   discharge). The run is an ExecF.evtF run under a footprint RNG: every data access of every step lies in RNG. The
   code (DIS of image B; addresses in rp_meter_counter_c.v's header)
     - stores ra at sp - 8 (0x81148) and loads it back (0x81294): stack frame [sp - 16, sp);
     - once n >= 14 (0x81150): loads 8 bytes at GOT_CELL_K (0x98878; 0x81164) and 8 bytes at CELL_K (0xa07f8; 0x81168),
       the shadow base;
     - loads bytes of f (a0) within [f + 12, f + 14) once n >= 14 and within [f + 12, f + 20) once n >= 1000, and
       before each of these loads it loads the shadow byte of that address, (a >> 3) + ASAN_K, which lies in
       [shadow_addr (f + 12), shadow_addr (f + 13)], resp. [shadow_addr (f + 12), shadow_addr (f + 19)];
     - on the counting path (meter_ok) loads the shadow byte of ctr (a2; 0x8126c) and stores ctr's 2 bytes (0x81280).
   So RNG holds the stack frame, the two cells, the bytes of f read and their shadow bytes, and, when it counts, ctr's
   2 bytes and their shadow byte. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA rp_meter_counter_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_meter_counter_c.

Definition rp_meter_counter_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (* Image B's UBSan premises: 0x81154 `beqz a0, 0x812a0` traps (unimp at 0x812a0) on f == NULL past n >= 14, and
       0x81240 `beqz a2` / 0x81244 `andi a3, a2, 1` / 0x81248 `bnez a3` trap on a NULL or misaligned ctr on the
       counting path. *)
    (14 <= bv_unsigned a1 -> bv_unsigned a0 <> 0) ->
    (PMC.meter_ok (bv_unsigned a1) bs = true -> bv_unsigned a2 <> 0 /\ bv_unsigned a2 mod 2 = 0) ->
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
