(* In the form of reac-repacer/fuzz_uci's lib/B/Prog/rp_hot_clamp_F_c.v (recipes commit 0295462466b2; itself without the shadow_rw premise of libreac/fuzz_decode's released footprint forms), for reac-repacer/fuzz_wire's rp_counter in image B: Img0 / AsanCells / AsanKA / rp_counter_c are lib/B's, the addresses in the comments are fuzz_wire.asan-ubsan's, the premises are lib/B/Prog/rp_counter_c.v's (image B's UBSan premise `bv_unsigned a0 <> 0` included) plus the footprint rows, and the footprint is that of the two bytes rp_counter reads, as libreac/fuzz_decode's released lib/B/Prog/reac_frame_counter_F_c.v states it for the same two reads. *)
(* Footprint form of rp_counter_contract (B image, entry 0x81314). The run is an ExecF.evtF run under a footprint RNG:
   every data access of every step lies in RNG. The code (DIS of image B)
     - stores ra at sp - 8 and loads it back (stack frame [sp - 16, sp));
     - loads 8 bytes at GOT_CELL_K (0x98878) and 8 bytes at CELL_K (0xa07f8), the shadow base;
     - loads the bytes at f + 14 and f + 15 (f = a0), and before each of these loads it loads the shadow byte of that
       address, (a >> 3) + ASAN_K, both in [shadow_addr (f + 14), shadow_addr (f + 15)].
   So RNG holds the stack frame, the two cells, the two bytes and their shadow bytes. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA rp_counter_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_counter_c.

Definition rp_counter_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (16 <= length bs)%nat ->
    (* Image B's UBSan premise: 0x8131c `beqz a0, 0x8137c` traps (unimp at 0x8137c) on f == NULL. The overflow traps
       0x81324 / 0x81328 (f >= 2 ^ 64 - 15) are refuted by `addressable` below (f + 16 <= APPMEM_END). *)
    bv_unsigned a0 <> 0 ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_COUNTER_FRAME <= bv_unsigned sp ->
    off_stk sp RP_COUNTER_FRAME (bv_unsigned a0) 16 ->
    app_mem (bv_unsigned sp - RP_COUNTER_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RP_COUNTER_FRAME GOT_CELL_K 8 ->
    off_stk sp RP_COUNTER_FRAME CELL_K 8 ->
    (* the two bytes it reads are addressable: refutes the report branches 0x8138c and 0x8139c *)
    addressable m (bv_unsigned a0 + 14) 2 ->
    ExecF.rng RNG (bv_unsigned sp - RP_COUNTER_FRAME) RP_COUNTER_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (bv_unsigned a0 + 14) 2 ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 14))
      (shadow_addr (bv_unsigned a0 + 15) - shadow_addr (bv_unsigned a0 + 14) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (PRC.counter_result bs)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_COUNTER_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_COUNTER) fc None m (seg_rom rsegs)).

(* The statement the footprint walk will prove; the close takes it as its Section hypothesis. *)
Definition wire_rp_counter_holds_stmt : Prop := rp_counter_contract_F.
