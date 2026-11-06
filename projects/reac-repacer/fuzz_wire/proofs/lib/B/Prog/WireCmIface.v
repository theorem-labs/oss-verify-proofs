(* WireCmIface: what the pieces of the image-B walk of check_meter (fuzz_wire.asan-ubsan 0x8016c = wire_sigma
   WS_check_meter, lib/B/Prog/WirePAddr.v) share, for the caller-journal statement lib/B/Prog/check_meter_cg.v. In the
   form of reac-repacer/fuzz_uci's lib/B/Prog/UciCvBIface.v (recipes commit 0295462466b2): check_meter's own body
   runs as footprint runs (lib/Lib/ExecF.v evtF, stepped by lib/Lib/StepF.v), carried into SRr by
   lib/B/Prog/LeafCgFacts.v bridge_evtF_stmt_YA0n; each call is cut by its callee's contract (the class-0 stack
   malloc, the leaf rp_meter_counter through the kit's lib/B/Prog/WireCcLeafb.v).

   Control flow (offsets from the entry, read from the disassembly of record of fuzz_wire.asan-ubsan):
     +0x000 `addi sp, sp, -128`, `sd zero, 0(sp)`, ra and s0 .. s10 at 120(sp) .. 32(sp), s0 := the entry sp,
            `andi sp, sp, -32` (s1 := the realigned sp), s4 := n, the use-after-return flag through GOT_UAR -> UAR
            (`lw` at +0x58, 1 in every state), s8 := the shadow offset through GOT_CELL_K -> CELL_K, s3 := f;
            `beqz a2` at +0x64 not taken; a0 := 64
     +0x06c `jal __asan_stack_malloc_0` (0x3c524), returns +0x070 with the class-0 fake frame F in a0
     +0x070 .. +0x0fc s2 := s6 := F (`bnez s2` at +0x80 taken), the frame header [F, F + 24) (0x41b58ab3, the frame
            description 0x18cc3, the pc 0x8016c), s7 := shadow_addr F and the frame's 8 shadow bytes (0xf1 x4, 0xf8,
            0xf3 x3), `sd s6, 24(s1)`, a0 := 14
     +0x100 .. +0x1b8 the inlined test (no store): n < 14 -> s9 := 12, s10 := 0; else f[12], f[13] (when f[12] =
            0x81), s9 := 16 or 12, n < 1000 -> s10 := 0; else f[s9], f[s9 + 1], s10 := (f[s9] = 0x88 && f[s9 + 1] =
            0x19); each byte load behind its shadow check (report sinks at +0x310 .. +0x350) and the UBSan wrap checks
            of f + 12, f + 13, f + s9, f + s9 + 1 (`unimp` at +0x304)
     +0x1bc .. +0x1dc s5 := F + 32 (ctr), ctr's shadow byte := 2, ctr := 0xa5c3, a0 := f, a1 := n, a2 := ctr
     +0x1e0 `jal rp_meter_counter` (0x81144), returns +0x1e4
     +0x1e4 .. +0x254 `bne a0, s10` to the abort (+0x240); a1 := ctr; when s10, the UBSan checks of f + s9 + 2 / + 3,
            f[s9 + 2], f[s9 + 3] behind their shadow checks, `beq` to +0x258; else ctr against 0xa5c3; a mismatch
            reaches __asan_handle_no_return / abort (+0x240 / +0x244)
     +0x258 .. +0x2f8 ctr's shadow byte := 0xf8, F's first word := 0x45e0360e, `beqz s2` not taken, the 8 shadow bytes
            := 0xf5, a0 := the word at F + 56 (the frame's flag pointer), `sb zero, 0(a0)` (the frame is given back),
            sp := s0 - 128, the twelve reloads, sp += 128, `ret`.
   The statements below are the footprint runs of these pieces; each takes exactly the memory facts its run reads
   and writes, and states what it writes as a munch of its write ranges. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_meter_counter_c.

Definition CM_ENTRY : Z := wire_sigma WS_check_meter.
Definition CM_AT (off : Z) : Z := CM_ENTRY + off.
Definition CM_SMALLOC : Z := wire_sigma WS___asan_stack_malloc_0.
Definition CM_LEAF : Z := wire_sigma WS_rp_meter_counter.

(* The cut points, as offsets from the entry. *)
Definition CM_RET_SM : Z := CM_AT 0x70.
Definition CM_PRE : Z := CM_AT 0x100.
Definition CM_CTR : Z := CM_AT 0x1bc.
Definition CM_RET_LEAF : Z := CM_AT 0x1e4.
Definition CM_REL : Z := CM_AT 0x258.

(* The sp after `addi sp, sp, -128` and `andi sp, sp, -32` (+0x000, +0x03c), for an entry sp. *)
Definition cm_sp1 (sp : Z) : Z := 32 * ((sp - 128) / 32).

(* The want bit and the counter of the model (lib/Prog/rp_meter_counter_c.v). *)
Definition cm_bit (n : Z) (bs : list byte) : Z := if PMC.meter_ok n bs then 1 else 0.
Definition cm_ctr (n : Z) (bs : list byte) : Z := if PMC.meter_ok n bs then PMC.meter_value n bs else 0xa5c3.
(* The i-th byte of the frame. *)
Definition cm_byte (bs : list byte) (i : Z) : byte := nth (Z.to_nat i) bs (Z_to_bv 8 0).

(* +0x000 -> the `jal __asan_stack_malloc_0` at +0x06c (ra = CM_RET_SM): the 128-byte frame, the realign, the two
   runtime cells. The frame's slot at s1 + 24 and the twelve saved words come out as cells. *)
Definition cm_seg1_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    bytes_at rsegs m GOT_UAR (le8 (wa UAR)) -> bytes_at rsegs m UAR (le4 (wa 1)) ->
    UAR + 4 <= bv_unsigned sp - 128 ->
    ExecF.rng RNG (bv_unsigned sp - 128) 128 ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 -> ExecF.rng RNG GOT_UAR 8 -> ExecF.rng RNG UAR 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (m1 : word -> option byte) (v : word),
         ms' = MS (mkR (Z_to_bv 64 CM_RET_SM) (Z_to_bv 64 (cm_sp1 (bv_unsigned sp))) gp tp t0 t1 t2
                    (Z_to_bv 64 (bv_unsigned sp)) (Z_to_bv 64 (cm_sp1 (bv_unsigned sp))) (Z_to_bv 64 64)
                    (Z_to_bv 64 CELL_K) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                    s2 a0 a1 s5 s6 s7 (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CM_SMALLOC) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (cm_sp1 (bv_unsigned sp) + 24) [C8 v] /\
         rw_cells rsegs m1 (bv_unsigned sp - 96)
           [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CM_ENTRY) fc None m (seg_rom rsegs)).

(* CM_RET_SM -> CM_PRE (a0 = the fake frame Fa): the frame header [Fa, Fa + 24), the frame's 8 shadow bytes, the
   slot s1 + 24. *)
Definition cm_seg2a_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fa : Z) (hj sj xj : list byte),
    4096 <= Fa -> Fa + 64 <= bv_unsigned s1 -> bv_unsigned s1 + 32 <= 2 ^ 64 ->
    (shadow_addr Fa + 8 <= Fa \/ Fa + 64 <= shadow_addr Fa) -> shadow_addr Fa + 8 <= bv_unsigned s1 ->
    rw_cells rsegs m Fa [CB 24 hj] ->
    rw_cells rsegs m (shadow_addr Fa) [CB 8 sj] ->
    rw_cells rsegs m (bv_unsigned s1 + 24) [CB 8 xj] ->
    ExecF.rng RNG Fa 24 -> ExecF.rng RNG (shadow_addr Fa) 8 -> ExecF.rng RNG (bv_unsigned s1 + 24) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m',
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14) (Z_to_bv 64 0x18cc3) (Z_to_bv 64 0x8016c)
                    (Z_to_bv 64 (-13)) a4 a5 a6 a7 (Z_to_bv 64 Fa) s3 s4 s5 (Z_to_bv 64 Fa)
                    (Z_to_bv 64 (shadow_addr Fa)) (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CM_PRE) fc None m' (seg_rom rsegs) /\
         munch [(Fa, Fa + 24); (shadow_addr Fa, shadow_addr Fa + 8); (bv_unsigned s1 + 24, bv_unsigned s1 + 32)]
           m m' /\
         wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fa) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
               (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CM_RET_SM) fc None m (seg_rom rsegs)).

(* CM_PRE -> CM_CTR, the inlined test, in continuation form: every path reaches CM_CTR with s9 = meter_eo and
   s10 = the want bit, a0 .. a3 havoced, the memory unchanged. The bytes f[12], f[13] are read once n >= 14, the bytes
   f[12 .. 20) once n >= 1000; each behind its shadow check, which the addressable premise refutes. *)
Definition cm_pre_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n : Z) (bs : list byte)
         (Q : machine_state -> Prop),
    0 <= n < 2 ^ 64 -> Z.of_nat (length bs) = n ->
    (14 <= n -> 4096 <= f /\ f + 20 < 2 ^ 64) ->
    (14 <= n -> forall i, 12 <= i < 14 -> mrd rsegs m (wa (f + i)) = Some (cm_byte bs i)) ->
    (1000 <= n -> forall i, 12 <= i < 20 -> mrd rsegs m (wa (f + i)) = Some (cm_byte bs i)) ->
    (14 <= n -> addressable m (f + 12) 2) ->
    (1000 <= n -> addressable m (f + 12) 8) ->
    (14 <= n -> ExecF.rng RNG (f + 12) 2) ->
    (14 <= n -> ExecF.rng RNG (shadow_addr (f + 12)) (shadow_addr (f + 13) - shadow_addr (f + 12) + 1)) ->
    (1000 <= n -> ExecF.rng RNG (f + 12) 8) ->
    (1000 <= n -> ExecF.rng RNG (shadow_addr (f + 12)) (shadow_addr (f + 19) - shadow_addr (f + 12) + 1)) ->
    (forall a0' a1' a2' a3' : word,
       ExecF.evtF rsegs RNG Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 (Z_to_bv 64 f) (Z_to_bv 64 n) s5 s6 s7
                  (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (Z.of_nat (PMC.meter_eo n bs))) (Z_to_bv 64 (cm_bit n bs))
                  s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CM_CTR) fc None m (seg_rom rsegs))) ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) (Z_to_bv 64 n)
               s5 s6 s7 (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CM_PRE) fc None m (seg_rom rsegs)).

(* CM_CTR -> the `jal rp_meter_counter` at +0x1e0 (ra = CM_RET_LEAF): ctr's shadow byte := 2, ctr := 0xa5c3, the
   three arguments. *)
Definition cm_seg2c_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fa : Z) (kj cj : list byte),
    4096 <= Fa -> Fa + 64 <= 2 ^ 64 -> (shadow_addr Fa + 8 <= Fa \/ Fa + 64 <= shadow_addr Fa) ->
    rw_cells rsegs m (shadow_addr Fa + 4) [CB 1 kj] -> rw_cells rsegs m (Fa + 32) [CB 2 cj] ->
    ExecF.rng RNG (shadow_addr Fa + 4) 1 -> ExecF.rng RNG (Fa + 32) 2 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m',
         ms' = MS (mkR (Z_to_bv 64 CM_RET_LEAF) sp gp tp t0 t1 t2 s0 s1 s3 s4 (Z_to_bv 64 (Fa + 32)) a3 a4 a5 a6 a7
                    s2 s3 s4 (Z_to_bv 64 (Fa + 32)) (Z_to_bv 64 Fa) (Z_to_bv 64 (shadow_addr Fa)) s8 s9 s10 s11
                    t3 t4 t5 t6)
                  F (Z_to_bv 64 CM_LEAF) fc None m' (seg_rom rsegs) /\
         munch [(shadow_addr Fa + 4, shadow_addr Fa + 5); (Fa + 32, Fa + 34)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (shadow_addr Fa + 4) [Z_to_bv 8 2] /\
         bytes_at rsegs m' (Fa + 32) (le2 (Z_to_bv 64 0xa5c3)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 Fa)
               (Z_to_bv 64 (shadow_addr Fa)) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CM_CTR) fc None m (seg_rom rsegs)).

(* CM_RET_LEAF -> CM_REL, the checks after the call, in continuation form: a0 (the leaf's result) equals s10 (the
   want bit), so `bne a0, s10` falls through; ctr holds cm_ctr; when the bit is 1, f[s9 + 2] | f[s9 + 3] << 8 is the
   counter, each byte behind its shadow check, so `beq` is taken; else ctr = 0xa5c3, so `bne` falls through. No
   abort is reached; the memory is unchanged. *)
Definition cm_cmp_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n Fa : Z) (bs : list byte)
         (Q : machine_state -> Prop),
    0 <= n < 2 ^ 64 -> Z.of_nat (length bs) = n ->
    4096 <= Fa -> Fa + 64 <= 2 ^ 64 ->
    bytes_at rsegs m (Fa + 32) (le2 (Z_to_bv 64 (cm_ctr n bs))) ->
    ExecF.rng RNG (Fa + 32) 2 ->
    (PMC.meter_ok n bs = true ->
       4096 <= f /\ f + 20 < 2 ^ 64 /\
       (forall i, 12 <= i < 20 -> mrd rsegs m (wa (f + i)) = Some (cm_byte bs i)) /\
       addressable m (f + 12) 8 /\ ExecF.rng RNG (f + 12) 8 /\
       ExecF.rng RNG (shadow_addr (f + 12)) (shadow_addr (f + 19) - shadow_addr (f + 12) + 1)) ->
    (forall a0' a1' a2' a3' s3' s9' : word,
       ExecF.evtF rsegs RNG Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3' s4 (Z_to_bv 64 (Fa + 32)) s6 s7
                  (Z_to_bv 64 ASAN_K) s9' (Z_to_bv 64 (cm_bit n bs)) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CM_REL) fc None m (seg_rom rsegs))) ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cm_bit n bs)) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 f) s4 (Z_to_bv 64 (Fa + 32)) s6 s7 (Z_to_bv 64 ASAN_K)
               (Z_to_bv 64 (Z.of_nat (PMC.meter_eo n bs))) (Z_to_bv 64 (cm_bit n bs)) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CM_RET_LEAF) fc None m (seg_rom rsegs)).

(* CM_REL -> the return: ctr's shadow byte := 0xf8, F's first word := 0x45e0360e, `beqz s2` not taken (Fa >= 4096),
   the 8 shadow bytes := 0xf5, a0 := the flag pointer FL (the word at Fa + 56), `sb zero, 0(a0)`, the twelve reloads
   from the words the prologue saved below the entry sp sp0 (= s0), sp := sp0, `ret` to the reloaded ra. *)
Definition cm_rel_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fa FL sp0 : Z) (sj hj lj : list byte)
         (cra c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : word),
    4096 <= Fa -> Fa + 64 <= sp0 - 128 ->
    (shadow_addr Fa + 8 <= Fa \/ Fa + 64 <= shadow_addr Fa) -> shadow_addr Fa + 8 <= sp0 - 128 ->
    0 <= FL -> FL + 1 <= sp0 - 128 ->
    (FL + 1 <= Fa \/ Fa + 64 <= FL) -> (FL + 1 <= shadow_addr Fa \/ shadow_addr Fa + 8 <= FL) ->
    sp0 < 2 ^ 64 -> bv_unsigned s0 = sp0 ->
    rw_cells rsegs m (shadow_addr Fa) [CB 8 sj] ->
    rw_cells rsegs m Fa [CB 8 hj] ->
    ro_cells rsegs m (Fa + 56) [C8 (Z_to_bv 64 FL)] ->
    rw_cells rsegs m FL [CB 1 lj] ->
    ro_cells rsegs m (sp0 - 96) [C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra] ->
    ExecF.rng RNG (shadow_addr Fa) 8 -> ExecF.rng RNG Fa 8 -> ExecF.rng RNG (Fa + 56) 8 -> ExecF.rng RNG FL 1 ->
    ExecF.rng RNG (sp0 - 96) 96 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m',
         ms' = MS (mkR cra (Z_to_bv 64 sp0) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 FL) a1 a2 a3 a4 a5 a6 a7
                    c2 c3 c4 c5 c6 c7 c8 c9 c10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m' (seg_rom rsegs) /\
         munch [(shadow_addr Fa, shadow_addr Fa + 8); (Fa, Fa + 8); (FL, FL + 1)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' FL [Z_to_bv 8 0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 Fa) s3 s4 s5 (Z_to_bv 64 Fa)
               (Z_to_bv 64 (shadow_addr Fa)) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CM_REL) fc None m (seg_rom rsegs)).
