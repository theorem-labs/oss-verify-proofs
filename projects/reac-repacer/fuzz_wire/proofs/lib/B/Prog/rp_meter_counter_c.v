(* rp_meter_counter_c: rp_meter_counter of fuzz_wire.asan-ubsan (0x81144 = wire_sigma WS_rp_meter_counter,
   lib/B/Prog/WirePAddr.v), a leaf, as a STATEMENT (no proof). No released ASan statement of this function exists, so
   nothing is copied: the text is in the form of reac-repacer/fuzz_uci lib/B/Prog/rp_hot_clamp_c.v (the leaf form),
   with the conditional reads and the int result of libreac/fuzz_decode lib/B/Prog/reac_frame_is_reac_c.v. Its model
   is the released plain contract lib/Prog/rp_meter_counter_c.v (meter_ok, meter_value; module PMC below), and its
   first two premises are image B's UBSan premises, in the shape of the UBSan image's lib/U/Prog/rp_meter_counter_c.v.
   Every address below is read from the disassembly of record of fuzz_wire.asan-ubsan; the entry and the size
   (464 bytes) from its unstripped twin's symbol table, the GOT word's value from its .got.
   The code (DIS of image B):
     0x81144 `addi sp, sp, -16`, 0x81148 `sd ra, 8(sp)` .. 0x81294 `ld ra, 8(sp)`, 0x81298 `addi sp, sp, 16`: the
       frame [sp - 16, sp);
     0x8114c / 0x81150 `li a3, 14` / `bltu a1, a3`: n < 14 returns 0 (0x8128c) before any load;
     0x81160 / 0x81164 `auipc a3, 0x17` / `ld a3, 1816(a3)`: the GOT word GOT_CELL_K (0x98878), then 0x81168
       `ld a4, 0(a3)`: the shadow base cell CELL_K (0xa07f8, __asan_shadow_memory_dynamic_address);
     the loads of f (a0): 0x81180 f[12] (0x8116c `addi a3, a0, 12`); 0x811a8 f[13] (0x81194 `addi a3, a0, 13`), only
       when f[12] = 0x81 (0x81184 `li a5, 129`); eo = 12 (0x811b0 `li a5, 12`) or 16 (0x811b8 `li a5, 16`);
       0x811bc .. 0x811cc `li a6, 1000` / `bltu a1, a6` / `addi a6, a5, 6` / `bltu a1, a6`: n < 1000 or n < eo + 6
       returns 0; 0x811ec f[eo], 0x81210 f[eo + 1], 0x8125c f[eo + 2], 0x81270 f[eo + 3]. So it reads bytes within
       [f + 12, f + 14) once n >= 14 and within [f + 12, f + 20) once n >= 1000. Before each load it loads the shadow
       byte of that address, (a >> 3) + base (0x81178, 0x811a0, 0x811e4, 0x81208, 0x81230, 0x81258), and branches to
       __asan_report_load1 (0x57e5c; jal at 0x812b0, 0x812c0, 0x812d0, 0x812e0, 0x812f0, 0x812fc) unless addressable;
     0x81280 `sh a0, 0(a2)`: the 2-byte store of f[eo + 2] | f[eo + 3] << 8 (0x81278 `slli`, 0x8127c `or`) at ctr = a2,
       after its shadow byte (0x8126c `lb`) is checked, branching to __asan_report_store2 (0x5821c; jal at 0x81310)
       unless addressable; then 0x81284 `li a3, 1`; every other exit returns 0 (0x811c0, 0x8128c); 0x81290 `mv a0, a3`.
   It calls nothing else: its seven jal are those report sinks, which the addressable premises refute. Its only stores
   are 0x81148 (its frame) and 0x81280 (ctr's two bytes, only on the counting path).
   UBSan checks, each branching to `unimp` at 0x812a0, and what refutes each:
     0x81154 `beqz a0`: f = NULL past n >= 14                -> `14 <= bv_unsigned a1 -> bv_unsigned a0 <> 0`;
     0x81240 `beqz a2` and 0x81244 / 0x81248 `andi a3, a2, 1` / `bnez a3`: ctr = NULL or ctr misaligned (a uint16_t
       store), on the counting path                        -> `meter_ok -> bv_unsigned a2 <> 0 /\ bv_unsigned a2 mod 2 = 0`;
     0x8115c `bgeu a0, a3` (a3 = -12): f + 12 wraps; 0x81190 `bltu a3, a0` (a3 = -14): f + 13 wraps;
     0x811d4 `bltu a3, a5` (a3 = ~f, 0x811d0): f + eo wraps; 0x811f8 `bgeu a5, a3`: f + eo + 1 wraps;
     0x81220 `bltu a3, a1` (a1 = eo + 2, 0x8121c); 0x8123c `bltu a3, a5` (a5 = eo + 3, 0x81238): f + eo + 2 / + 3 wrap
                                                             -> bytes_at's bound f + length bs <= 2 ^ 64 (lib/Lib/Mem.v)
                                                                with length bs >= 14 (n >= 14), >= 20 (n >= 1000). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_meter_counter_c.

(* The entry (symbol rp_meter_counter, 0x81144) and the frame (`addi sp, sp, -16` at the entry). *)
Definition RP_METER_COUNTER : Z := 0x81144.
Definition RP_METER_COUNTER_FRAME : Z := 16.

Definition rp_meter_counter_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
