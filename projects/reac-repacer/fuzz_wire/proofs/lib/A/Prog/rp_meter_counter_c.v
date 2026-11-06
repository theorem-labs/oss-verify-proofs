(* rp_meter_counter_c: rp_meter_counter of fuzz_wire.asan (image A), a leaf, as a STATEMENT (no proof). In the form of
   reac-repacer/fuzz_uci lib/A/Prog/rp_hot_clamp_c.v (entry, frame, the ASan runtime cells and addressability premises)
   over the plain contract's model (lib/Prog/rp_meter_counter_c.v meter_ok / meter_value), with the conditional
   buffer and write premises of libreac/fuzz_decode lib/A/Prog/reac_frame_is_reac_c.v and reac_decode_c.v. No
   released ASan statement of rp_meter_counter exists; this is written new.
   The code (objdump of record of fuzz_wire.asan; addresses there):
     0x81168  entry (symbol rp_meter_counter, 396 bytes); `addi sp, sp, -16` (frame 16), `sd ra, 8(sp)` at 0x8116c,
              `ld ra, 8(sp)` at 0x8127c, `addi sp, sp, 16` at 0x81280, `ret` at 0x81284;
     0x81170  `li a3, 14`; `bltu a1, a3` at 0x81174 to the return of 0 at 0x81274: below 14 bytes nothing is read;
     0x81178  `auipc a3, 0x17`; `ld a3, 1648(a3)` at 0x8117c reads the GOT word 0x987e8 (GOT_CELL_K, which holds
              0xa0778 = CELL_K, __asan_shadow_memory_dynamic_address), `ld a4, 0(a3)` at 0x81180 the shadow base;
     0x81198  `lbu` of f[12] (its shadow byte at 0x81190), compared with 0x81 (`li a5, 129` at 0x8119c); 0x811b8
              `lbu` of f[13] (shadow byte at 0x811b0), `beqz` at 0x811bc: eo = 16 (0x811c8) or 12 (0x811c0);
     0x811cc  `li a6, 1000`, `bltu a1, a6` at 0x811d4; `addi a6, a5, 6`, `bltu a1, a6` at 0x811d8 / 0x811dc: below
              1000 or below eo + 6 bytes it returns 0 (0x81278);
     0x811f4  `lbu` of f[eo] (shadow byte at 0x811ec), compared with 0x88 (`li a3, 136` at 0x811f8); 0x81214 `lbu` of
              f[eo + 1] (shadow byte at 0x8120c), compared with 0x19 (`li a3, 25` at 0x81218); 0x81244 / 0x81258
              `lbu` of f[eo + 2] / f[eo + 3] (shadow bytes at 0x8122c / 0x81240);
     0x81254  the shadow byte of a2 (the counter); 0x81268 `sh a0, 0(a2)` stores f[eo + 2] | f[eo + 3] << 8
              (`slli` 0x81260, `or` 0x81264), then `li a3, 1` at 0x8126c: it returns 1.
   Its only calls are the report branches __asan_report_load1 (0x580bc) at 0x81294, 0x812a4, 0x812b0, 0x812c0,
   0x812d0, 0x812dc (one per f byte) and __asan_report_store2 (0x5847c) at 0x812f0 (the counter), each taken only when
   the shadow byte it checks is not addressable: the addressable premises refute them. No `unimp` in the function
   (image A has no UBSan). Its only stores are `sd ra` in its frame and the 2-byte counter store at 0x81268. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_meter_counter_c.

(* Entry (symbol rp_meter_counter, 0x81168) and frame (`addi sp, sp, -16` at 0x81168). *)
Definition RP_METER_COUNTER : Z := 0x81168.
Definition RP_METER_COUNTER_FRAME : Z := 16.

(* f (a0) holds bs, read only past the function's own early exits: bytes 12-13 once n (a1) >= 14, bytes eo .. eo + 3
   (inside [12, 20)) once n >= 1000; *ctr (a2) is written only when the frame is counted (meter_ok). The post is the
   plain contract's, with the frame's bytes munched: the result in a0, and the counter's 2 little-endian bytes at a2
   when meter_ok, else no byte outside the frame changed. *)
Definition rp_meter_counter_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
    evt rsegs
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
