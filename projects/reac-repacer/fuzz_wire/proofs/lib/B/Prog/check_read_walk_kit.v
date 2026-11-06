(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 653 of its 721 lines of code are new or changed and 396 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac-repacer/fuzz_wire's check_width in image A, proving the frozen
   statement lib/A/Prog/check_width_cg.v wire_check_width_holds_stmt. The form is reac-repacer/fuzz_uci's
   lib/A/Prog/check_value_cgW.v (footprint runs carried into SRr, an inner journal over the call's stack window, each
   call cut by its callee's statement) with its segment file lib/A/Prog/UciCvSegs.v, and the leaf call of its
   lib/A/Prog/check_clamp_cgW.v (here through lib/A/Prog/WireCcLeafb.v wcc_leafb_journal, the leaf taken by
   WireCg.v wire_leaf_at). The w_width loop and the frame law are this unit's plain walk lib/Prog/check_width.v
   (width_loop, w_width_frame_law, fc_model_neg), restated over image A's rp_frame_channels_model. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/check_width_cgW.v, with its module paths, module names and numbers changed; 1020 of its 1119 lines of code are new or changed and 622 lines of the source are left out. *)
(* check_read_walk_kit: the footprint runs of the image-B walk of reac-repacer/fuzz_wire's check_read
   (fuzz_wire.asan-ubsan 0x805f4 = wire_sigma WS_check_read), which lib/B/Prog/check_read_cgW.v composes into
   wire_check_read_holds. Each run is an ExecF.evtF statement over the raw memory (lib/Lib/StepF.v step), in the form of
   this unit's image-B footprint walks (lib/B/Prog/rp_ret_accept_FW.v: one rng fact per access, the shadow loads read
   from `addressable`, the UBSan traps refuted by if_false).
   - The program points, the realigned sp (crw_sp1), the fake frame's shadow address (crw_sh), the bytes the code
     writes into its frame and shadow (crw_shadow_bytes, crw_fill, crw_slots), and want, the width and v as the plain
     models give them (lib/Prog/rp_slot_read_c.v rp_slot_read_model, lib/Prog/check_read.v w_width_model).
   - crw_segA_F: +0x0 .. `jal __asan_stack_malloc_1` at +0x74: the frame, the thirteen saves, the 32-byte realign,
     the use-after-return flag (1) and the shadow base read through their GOT words, a0 = 0x80.
   - crw_segB_stmt / crw_segB_F: +0x78 .. `jal rp_slot_read` at +0x1c8: the frame header, the frame's shadow, the
     fill of v, the inlined w_width, the c[16] / c[17] tests behind their shadow checks, want in s11.
   - crw_segC_stmt / crw_segC_F: +0x1cc .. the `ret`: the `bne a0, s11` test, the twelve sample comparisons (the fill
     on a declined read, the braid bytes of c behind their shadow checks on an accepted one), the frame's shadow and
     header released, the flag byte cleared, the reloads.
   No report call, abort or UBSan trap is reached: each run refutes it from its premises. The loop invariants and the
   sample arithmetic are the released plain walk's (lib/Prog/check_read.v ww_loop, cr_loop, wsamp_eq, rps,
   width_facts, srm_zero, srm_one, ww_facts), reused where they do not name the plain image's segments. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require check_read rp_slot_read_c rp_slot_width_c.
Module PCR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.check_read.
Module PSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read_c.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Import ListNotations.
Open Scope Z_scope.

(* The program points (fuzz_wire.asan-ubsan). *)
Definition CRW_ENTRY : Z := 0x805f4.   (* check_read *)
Definition CRW_RET0 : Z := 0x8066c.    (* return address of `jal __asan_stack_malloc_1` at +0x74 *)
Definition CRW_SM1 : Z := 0x3c698.     (* __asan_stack_malloc_1 *)
Definition CRW_RET1 : Z := 0x807c0.    (* return address of `jal rp_slot_read` at +0x1c8 *)
Definition CRW_RSR : Z := 0x815ec.     (* rp_slot_read *)
Definition CRW_DESC : Z := 0x16e29.    (* the frame description string the header names (auipc/addi at +0xb4/+0xcc) *)

(* sp after `addi sp, sp, -0xc0` and `andi sp, sp, -0x20`. *)
Definition crw_sp1 (sp : Z) : Z := 32 * ((sp - 192) / 32).
(* The shadow address of the fake frame F (`srli a3, t0, 3`, `add a7, a3, s7`). *)
Definition crw_sh (FR : Z) : Z := FR / 8 + ASAN_K.
(* The frame's 16 shadow bytes as +0xe8 .. +0x128 write them: 0xf1 x4, 0 x6, 0xf3 x6. *)
Definition crw_shadow_bytes : list byte :=
  map (Z_to_bv 8) [0xf1; 0xf1; 0xf1; 0xf1; 0; 0; 0; 0; 0; 0; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3].
(* v[12] filled with UNTOUCHED_SAMPLE 0x5a5a5a5a. *)
Definition crw_fill : list byte := repeat (Z_to_bv 8 90) 48.
(* The 88 bytes [sp1, sp1 + 0x58) of the realigned frame: sp1 + 0x08 = F, + 0x10 = the frame's shadow address,
   + 0x18 = F, + 0x30 = c, + 0x38 = v = F + 32, + 0x48 = F; the rest not read here (+0x20 / +0x28 and the 6-byte buffer at
   +0x52 are written later). *)
Definition crw_slots (FR c : Z) (J0 J1 J2 J3 : list byte) : list cell :=
  [CB 8 J0; C8 (Z_to_bv 64 FR); C8 (Z_to_bv 64 (crw_sh FR)); C8 (Z_to_bv 64 FR); CB 16 J1; C8 (Z_to_bv 64 c);
   C8 (Z_to_bv 64 (FR + 32)); CB 8 J2; C8 (Z_to_bv 64 FR); CB 8 J3].
(* The harness's answer (want) and frame law (w_width), the plain models. *)
Definition crw_want (len : Z) (bs : list byte) (slot : Z) : Z := PSR.rp_slot_read_model len bs slot.
Definition crw_W (len : Z) : Z := PCR.w_width_model len.
(* v after rp_slot_read: the samples on an accepted read, else still the fill. *)
Definition crw_v (len : Z) (bs : list byte) (slot : Z) : list byte :=
  if crw_want len bs slot =? 1 then PSR.rp_slot_bytes bs (crw_W len) slot else crw_fill.

(* lib/Prog/check_read.v rw_cells_app, at image B's segments. *)
Lemma crw_rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at, wr_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] (H1 & H2 & H3)].
    rewrite (cells_bytes_length cs1 W1) in B2.
    split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]).
    + intros i Hi. apply H3. lia.
    + intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply H3. lia.
  - intros [[[W1 B1] (H1 & H2 & H3)] [[W2 B2] (K1 & K2 & K3)]].
    rewrite <- (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption | split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))) as [L|L]; [apply H3; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply K3. lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Segment B: +0x78 (the return of __asan_stack_malloc_1, a0 = the fake frame F) .. `jal rp_slot_read` at +0x1c8.
   The frame header and shadow, the v fill, the inlined w_width, the c[16] / c[17] tests behind their shadow checks
   (the report calls and the UBSan traps refuted), want into s11, the call's arguments. *)
Definition crw_segB_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte)
         (SP1 FR c len slot : Z) (Js Jf Jh : list byte),
    2 ^ 46 <= SP1 -> SP1 + 88 <= 2 ^ 47 -> SP1 mod 32 = 0 ->
    4096 <= FR -> FR mod 64 = 0 -> FR + 128 <= SP1 -> crw_sh FR + 16 <= SP1 ->
    (FR + 128 <= crw_sh FR \/ crw_sh FR + 16 <= FR) ->
    0 <= len <= 1600 -> -2 ^ 31 <= slot < 2 ^ 31 ->
    rw_cells rsegs m SP1 [CB 88 Js] ->
    rw_cells rsegs m FR [CB 80 Jf] ->
    rw_cells rsegs m (crw_sh FR) [CB 16 Jh] ->
    ExecF.rng RNG SP1 88 -> ExecF.rng RNG FR 80 -> ExecF.rng RNG (crw_sh FR) 16 ->
    (50 <= len ->
       Z.of_nat (length bs) = len /\ bytes_at rsegs m c bs /\ addressable m c len /\
       4096 <= c /\ c + len <= SP1 /\
       (c + len <= FR \/ FR + 128 <= c) /\ (c + len <= crw_sh FR \/ crw_sh FR + 16 <= c) /\
       shadow_addr (c + len - 1) < SP1 /\
       (shadow_addr (c + len - 1) < FR \/ FR + 128 <= shadow_addr c) /\
       (shadow_addr (c + len - 1) < crw_sh FR \/ crw_sh FR + 16 <= shadow_addr c) /\
       ExecF.rng RNG c len /\
       ExecF.rng RNG (shadow_addr c) (shadow_addr (c + len - 1) - shadow_addr c + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : word -> option byte)
                    (J0 J1 J2 J3 Jx : list byte),
         ms' = MS (mkR (Z_to_bv 64 CRW_RET1) (Z_to_bv 64 SP1) gp tp t0' t1' t2' s0 (Z_to_bv 64 SP1)
                    (Z_to_bv 64 c) (Z_to_bv 64 len) (Z_to_bv 64 slot) (Z_to_bv 64 (FR + 32)) a4' a5' a6' a7'
                    (Z_to_bv 64 len) (Z_to_bv 64 c) s4 (Z_to_bv 64 slot) s6 (Z_to_bv 64 ASAN_K) s8 s9
                    (Z_to_bv 64 (crw_W len)) (Z_to_bv 64 (crw_want len bs slot)) t3' t4' t5' t6')
                  F (Z_to_bv 64 CRW_RSR) fc None m2 (seg_rom rsegs) /\
         munch [(SP1, SP1 + 88); (FR, FR + 80); (crw_sh FR, crw_sh FR + 16)] m m2 /\
         wmono rsegs m m2 /\
         rw_cells rsegs m2 SP1 (crw_slots FR c J0 J1 J2 J3) /\
         rw_cells rsegs m2 FR [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 CRW_DESC); C8 (Z_to_bv 64 CRW_ENTRY);
                               CB 8 Jx; CB 48 crw_fill] /\
         rw_cells rsegs m2 (crw_sh FR) [CB 16 crw_shadow_bytes])
      (MS (mkR ra (Z_to_bv 64 SP1) gp tp t0 t1 t2 s0 (Z_to_bv 64 SP1) (Z_to_bv 64 FR) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 len) (Z_to_bv 64 c) s4 (Z_to_bv 64 slot) s6 (Z_to_bv 64 ASAN_K) s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 CRW_RET0) fc None m (seg_rom rsegs)).

(* ------------------------------------------------------------------------------------------------------------ *)
(* Segment C: +0x1cc (the return of rp_slot_read, a0 = its answer) .. the `ret`. The `bne a0, s11` test, the twelve
   sample comparisons (the untouched fill on a declined read, the braid bytes of c on an accepted one, each behind
   its shadow check; the report calls, the aborts and the UBSan traps refuted), the frame's shadow set to 0xf8 over v,
   the header retired (0x45e0360e), the shadow set to 0xf5, the flag byte FL (the word at F + 0x78) cleared, the
   thirteen reloads and the `ret`. *)
Definition crw_segC_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 t3 t4 t5 t6 : word)
         (rae s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte)
         (SP0 FR FL c len slot : Z) (J0 J1 J2 J3 Jh Js Jf : list byte),
    SP0 mod 16 = 0 -> 2 ^ 46 <= SP0 <= 2 ^ 47 ->
    4096 <= FR -> FR mod 64 = 0 -> FR + 128 <= crw_sp1 SP0 -> crw_sh FR + 16 <= crw_sp1 SP0 ->
    (FR + 128 <= crw_sh FR \/ crw_sh FR + 16 <= FR) ->
    4096 <= FL -> FL + 1 <= crw_sp1 SP0 -> (FL + 1 <= FR \/ FR + 128 <= FL) ->
    (FL + 1 <= crw_sh FR \/ crw_sh FR + 16 <= FL) ->
    0 <= len <= 1600 -> -2 ^ 31 <= slot < 2 ^ 31 ->
    rw_cells rsegs m (SP0 - 104)
      [C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
    rw_cells rsegs m (crw_sp1 SP0) (crw_slots FR c J0 J1 J2 J3) ->
    rw_cells rsegs m FR [CB 8 Jh] ->
    bytes_at rsegs m (FR + 32) (crw_v len bs slot) ->
    bytes_at rsegs m (FR + 120) (le8 (Z_to_bv 64 FL)) ->
    rw_cells rsegs m (crw_sh FR) [CB 16 Js] ->
    rw_cells rsegs m FL [CB 1 Jf] ->
    ExecF.rng RNG (SP0 - 104) 104 -> ExecF.rng RNG (crw_sp1 SP0) 88 -> ExecF.rng RNG FR 128 ->
    ExecF.rng RNG (crw_sh FR) 16 -> ExecF.rng RNG FL 1 ->
    (crw_want len bs slot = 1 ->
       Z.of_nat (length bs) = len /\ bytes_at rsegs m c bs /\ addressable m c len /\
       4096 <= c /\ c + len <= crw_sp1 SP0 /\
       ExecF.rng RNG c len /\
       ExecF.rng RNG (shadow_addr c) (shadow_addr (c + len - 1) - shadow_addr c + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m4 : word -> option byte),
         ms' = MS (mkR rae (Z_to_bv 64 SP0) gp tp t0' t1' t2' s0e s1e a0' a1' a2' a3' a4' a5' a6' a7'
                    s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3' t4' t5' t6')
                  F (ret_pc rae) fc None m4 (seg_rom rsegs) /\
         munch [(crw_sp1 SP0, crw_sp1 SP0 + 88); (FR, FR + 8); (crw_sh FR, crw_sh FR + 16); (FL, FL + 1)] m m4 /\
         wmono rsegs m m4 /\
         bytes_at rsegs m4 FL [Z_to_bv 8 0])
      (MS (mkR ra (Z_to_bv 64 (crw_sp1 SP0)) gp tp t0 t1 t2 (Z_to_bv 64 SP0) (Z_to_bv 64 (crw_sp1 SP0))
               (Z_to_bv 64 (crw_want len bs slot)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 slot) s6
               (Z_to_bv 64 ASAN_K) s8 s9 (Z_to_bv 64 (crw_W len)) (Z_to_bv 64 (crw_want len bs slot)) t3 t4 t5 t6)
          F (Z_to_bv 64 CRW_RET1) fc None m (seg_rom rsegs)).

Lemma crw_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
  intros x Hx.
  assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
  rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
  rewrite Z.land_ones, Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.

Lemma crw_sp1_eq : forall sp, 2 ^ 46 <= sp <= 2 ^ 47 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (sp + -192))) 18446744073709551584) = Z_to_bv 64 (crw_sp1 sp).
Proof.
  intros sp Hsp. rewrite unsigned_lit by lia. change 18446744073709551584 with (2 ^ 64 - 32).
  rewrite crw_land_m32 by lia. unfold crw_sp1. replace (sp + -192) with (sp - 192) by lia. reflexivity.
Qed.

Lemma crw_sp1_facts : forall sp, 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 ->
  sp - 208 <= crw_sp1 sp <= sp - 192 /\ crw_sp1 sp mod 32 = 0.
Proof.
  intros sp Hsp H16. unfold crw_sp1. pose proof (Z.div_mod (sp - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (sp - 192) 32 ltac:(lia)) as M.
  assert ((sp - 192) mod 32 = 0 \/ (sp - 192) mod 32 = 16) by (Z.div_mod_to_equations; lia).
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma crw_segA_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 192 <= bv_unsigned sp ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 46 <= bv_unsigned sp <= 2 ^ 47 ->
    bytes_at rsegs m GOT_UAR (le8 (wa UAR)) -> bytes_at rsegs m UAR (le4 (wa 1)) ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    ExecF.rng RNG (bv_unsigned sp - 192) 192 ->
    ExecF.rng RNG GOT_UAR 8 -> ExecF.rng RNG UAR 4 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR (Z_to_bv 64 CRW_RET0) (Z_to_bv 64 (crw_sp1 (bv_unsigned sp))) gp tp t0 t1 t2 sp
                    (Z_to_bv 64 (crw_sp1 (bv_unsigned sp))) (Z_to_bv 64 0x80) (Z_to_bv 64 CELL_K) (Z_to_bv 64 1)
                    a3 a4 a5 a6 a7 a1 a0 s4 a2 s6 (Z_to_bv 64 ASAN_K) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CRW_SM1) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 192, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 104)
           [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CRW_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO A16 ASP GU U GC C RFR RGU RU RGC RC.
  unfold CRW_ENTRY, CRW_RET0, CRW_SM1.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold GOT_UAR, UAR, GOT_CELL_K, CELL_K, ASAN_K in *.
  carve_frame 192%nat ST.
  do 15 step.
  do 4 step.
  rewrite (crw_sp1_eq (bv_unsigned sp) ASP).
  match goal with MU' : munch _ m ?m1 |- _ => rename m1 into m0 end.
  assert (RD1 : ov_read_bytes rsegs m0 (wa 0x988d0) 8 = Some (le8 (wa 0xa0800))).
  { replace (wa 0x988d0) with (wa (0x988d0 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 0x988d0 _ 0 8 GU ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RD2 : ov_read_bytes rsegs m0 (wa 0x98878) 8 = Some (le8 (wa 0xa07f8))).
  { replace (wa 0x98878) with (wa (0x98878 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 0x98878 _ 0 8 GC ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RD3 : ov_read_bytes rsegs m0 (wa 0xa0800) 4 = Some (le4 (wa 1))).
  { replace (wa 0xa0800) with (wa (0xa0800 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 0xa0800 _ 0 4 U ltac:(lia)) by (rewrite length_le4; lia). reflexivity. }
  assert (RD4 : ov_read_bytes rsegs m0 (wa 0xa07f8) 8 = Some (le8 (wa 0x7fff8000))).
  { replace (wa 0xa07f8) with (wa (0xa07f8 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 0xa07f8 _ 0 8 C ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  do 5 step.
  do 4 step. if_false.
  do 2 step.
  apply evtF_done. eexists. split; [|split; [exact MU|split; [exact WM|]]].
  - rewrite (PCR.sx32_lit 1) by lia. reflexivity.
  - apply (proj1 (crw_rw_cells_app _ _ [_; _] _)) in FR. destruct FR as [_ FR].
    cbn [cells_size csize Nat.add Z.of_nat] in FR.
    replace (bv_unsigned sp - 104) with (bv_unsigned sp + -192 + 88) by lia. exact FR.
Qed.

Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Byte and shadow helpers (lib/B/Prog/AsanKAProof.v, lib/Prog/FrameBytes.v rd1, at image B's segments). *)

Lemma crwB_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma crwB_zxb_u : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. pose proof (crwB_byte_range b). apply unsigned_lit. lia. Qed.

Lemma crwB_byte_signed_range : forall k : byte, -128 <= bv_signed k < 128.
Proof.
  intros k. pose proof (bv_signed_in_range 8 k ltac:(lia)) as R. unfold bv_half_modulus, bv_modulus in R.
  change (2 ^ Z.of_N 8 / 2) with 128 in R. lia.
Qed.

Lemma crwB_sxb_eq0 : forall k : byte, bv_eqb (sxb k) (Z_to_bv 64 0) = (bv_signed k =? 0).
Proof.
  intros k. unfold sxb, bv_eqb. pose proof (crwB_byte_signed_range k).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  destruct (Z.eqb_spec (bv_signed k) 0) as [E|E].
  - rewrite E. reflexivity.
  - apply Z.eqb_neq. change (0 mod 2^64) with 0. Z.div_mod_to_equations. lia.
Qed.

Lemma crwB_lts_low : forall (x : Z) (k : byte), 0 <= x < 8 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (crwB_byte_signed_range k).
  rewrite !PCR.signed_lit by lia. reflexivity.
Qed.

Lemma crwB_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. exact (Z.land_ones x 3 ltac:(lia)). Qed.

Lemma crwB_rdm : forall m a b, mrd rsegs m (wa a) = Some b -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof. intros m a b H. rewrite ov_rdn, rdn_unfold, H. reflexivity. Qed.

(* A shadow byte outside the run's footprint keeps its value. *)
Lemma crwB_mrd_tp : forall W m m' a b, munch W m m' -> 0 <= a < 2^64 -> outside W a ->
  mrd rsegs m (wa a) = Some b -> mrd rsegs m' (wa a) = Some b.
Proof.
  intros W m m' a b MU Ha Ho H. unfold mrd in *. rewrite MU; [exact H|].
  rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma crwB_firstn1 : forall (bs : list byte) k, (k < length bs)%nat ->
  firstn 1 (skipn k bs) = [nth k bs (Z_to_bv 8 0)].
Proof.
  induction bs as [|b bs IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma crwB_rdz : forall m a bs k, bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk. rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  rewrite crwB_firstn1 by lia. reflexivity.
Qed.

(* Merging a run of written cells into one byte block (Tac.v rw_cells_forget with the bytes named). *)
Lemma crwB_merge_to : forall m A cs n bs, rw_cells rsegs m A cs -> cells_size cs = n -> cells_bytes cs = bs ->
  rw_cells rsegs m A [CB n bs].
Proof.
  intros m A cs n bs H Hn Hb. subst n bs.
  pose proof (rw_cells_merge rsegs m A [] cs []) as M. rewrite app_nil_r in M. cbn [app] in M. apply M. exact H.
Qed.

(* The twelve words of the fill are v[12] = UNTOUCHED_SAMPLE. *)
Lemma crwB_fill_bytes : cells_bytes (repeat (C4 (Z_to_bv 64 1515870810)) 12) = crw_fill.
Proof.
  vm_compute. repeat (apply (f_equal2 (@cons byte)); [apply bv_eq; reflexivity|]). reflexivity.
Qed.

Lemma crwB_fr_merge : forall mk FR v0 v1 v2 Jx,
  rw_cells rsegs mk FR [C8 v0; C8 v1; C8 v2; CB 8 Jx;
    C4 (Z_to_bv 64 1515870810); C4 (Z_to_bv 64 1515870810); C4 (Z_to_bv 64 1515870810);
    C4 (Z_to_bv 64 1515870810); C4 (Z_to_bv 64 1515870810); C4 (Z_to_bv 64 1515870810);
    C4 (Z_to_bv 64 1515870810); C4 (Z_to_bv 64 1515870810); C4 (Z_to_bv 64 1515870810);
    C4 (Z_to_bv 64 1515870810); C4 (Z_to_bv 64 1515870810); C4 (Z_to_bv 64 1515870810)] ->
  rw_cells rsegs mk FR [C8 v0; C8 v1; C8 v2; CB 8 Jx; CB 48 crw_fill].
Proof.
  intros mk FR v0 v1 v2 Jx H.
  pose proof (rw_cells_merge rsegs mk FR [C8 v0; C8 v1; C8 v2; CB 8 Jx]
                (repeat (C4 (Z_to_bv 64 1515870810)) 12) [] H) as M.
  rewrite crwB_fill_bytes in M. exact M.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Tactics. *)

(* bv_unsigned of a literal-free expression whose range lia proves. *)
Ltac crwB_u := repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
  end.

(* A shadow address as the code forms it (`srli`, `add` with s7 = ASAN_K) is crw_sh / shadow_addr. *)
Ltac crwB_shq :=
  try unfold crw_sh; try unfold shadow_addr; try unfold ASAN_K; f_equal; crwB_u;
  rewrite ?Z.shiftr_div_pow2 by lia; reflexivity.

(* A branch condition as a Z fact. *)
Ltac crwB_zc H :=
  try unfold bv_eqb in H; try unfold bv_ltu in H; try unfold bv_lts in H; try unfold zxb in H;
  fold_lit_ux_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 (bv_unsigned ?b))] => rewrite (crwB_zxb_u b) in H
  | context [bv_signed (Z_to_bv 64 ?z)] => rewrite (PCR.signed_lit z) in H by lia
  | context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in H by lia
  end;
  zify_bool H.

(* A symbolic branch that is taken (crwB_t) or not taken (crwB_f); lia refutes the other side. *)
Ltac crwB_t := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let HC := fresh "HC" in destruct c eqn:HC; [ clear HC | exfalso; crwB_zc HC; lia ]
  end.
Ltac crwB_f := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let HC := fresh "HC" in destruct c eqn:HC; [ exfalso; crwB_zc HC; lia | clear HC ]
  end.

Ltac crwB_side := first [ eassumption | lia | reflexivity ].

Ltac crwB_beq := cbv [cells_bytes cbytes app crw_shadow_bytes map];
  repeat (apply (f_equal2 (@cons byte)); [apply bv_eq; reflexivity|]); reflexivity.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The segment's post (crw_segB_stmt's). *)
Definition crwB_post (gp tp s0 s4 s6 s8 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (bs : list byte) (SP1 FR c len slot : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : word -> option byte)
                (J0 J1 J2 J3 Jx : list byte),
         ms' = MS (mkR (Z_to_bv 64 CRW_RET1) (Z_to_bv 64 SP1) gp tp t0' t1' t2' s0 (Z_to_bv 64 SP1)
                    (Z_to_bv 64 c) (Z_to_bv 64 len) (Z_to_bv 64 slot) (Z_to_bv 64 (FR + 32)) a4' a5' a6' a7'
                    (Z_to_bv 64 len) (Z_to_bv 64 c) s4 (Z_to_bv 64 slot) s6 (Z_to_bv 64 ASAN_K) s8 s9
                    (Z_to_bv 64 (crw_W len)) (Z_to_bv 64 (crw_want len bs slot)) t3' t4' t5' t6')
                  F (Z_to_bv 64 CRW_RSR) fc None m2 (seg_rom rsegs) /\
         munch [(SP1, SP1 + 88); (FR, FR + 80); (crw_sh FR, crw_sh FR + 16)] m m2 /\
         wmono rsegs m m2 /\
         rw_cells rsegs m2 SP1 (crw_slots FR c J0 J1 J2 J3) /\
         rw_cells rsegs m2 FR [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 CRW_DESC); C8 (Z_to_bv 64 CRW_ENTRY);
                               CB 8 Jx; CB 48 crw_fill] /\
         rw_cells rsegs m2 (crw_sh FR) [CB 16 crw_shadow_bytes].

(* ------------------------------------------------------------------------------------------------------------ *)
(* +0x1b4 (0x807a8) .. the call: c saved at s1 + 0x30, a0 = c, a1 = len, a2 = slot, a3 = v (`ld` from s1 + 0x38),
   `jal rp_slot_read`. s10 holds the width and s11 want. *)
Lemma crwB_tail : forall (RNG : ExecF.footprint)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m mk : word -> option byte) (bs : list byte)
    (SP1 FR c len slot Wv V : Z) (J0 Jm J2 J3 Jx : list byte),
  2 ^ 46 <= SP1 -> SP1 + 88 <= 2 ^ 47 -> 4096 <= FR -> FR + 128 <= SP1 ->
  2147450880 <= crw_sh FR -> crw_sh FR + 16 <= SP1 ->
  Wv = crw_W len -> V = crw_want len bs slot ->
  munch [(SP1, SP1 + 88); (FR, FR + 80); (crw_sh FR, crw_sh FR + 16)] m mk -> wmono rsegs m mk ->
  rw_cells rsegs mk SP1 [CB 8 J0; C8 (Z_to_bv 64 FR); C8 (Z_to_bv 64 (crw_sh FR)); C8 (Z_to_bv 64 FR); CB 24 Jm;
                         C8 (Z_to_bv 64 (FR + 32)); CB 8 J2; C8 (Z_to_bv 64 FR); CB 8 J3] ->
  rw_cells rsegs mk FR [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 CRW_DESC); C8 (Z_to_bv 64 CRW_ENTRY);
                        CB 8 Jx; CB 48 crw_fill] ->
  rw_cells rsegs mk (crw_sh FR) [CB 16 crw_shadow_bytes] ->
  ExecF.rng RNG SP1 88 ->
  ExecF.evtF rsegs RNG (crwB_post gp tp s0 s4 s6 s8 s9 F fc m bs SP1 FR c len slot)
    (MS (mkR ra (Z_to_bv 64 SP1) gp tp t0 t1 t2 s0 (Z_to_bv 64 SP1) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 len) (Z_to_bv 64 c) s4 (Z_to_bv 64 slot) s6 (Z_to_bv 64 ASAN_K) s8 s9
             (Z_to_bv 64 Wv) (Z_to_bv 64 V) t3 t4 t5 t6)
        F (Z_to_bv 64 0x807a8) fc None mk (seg_rom rsegs)).
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 F fc m mk bs SP1 FR c len slot Wv V
    J0 Jm J2 J3 Jx H46 H47 HF0 HF1 HK HF2 EW EV MU WM CS CF CH RS.
  subst Wv V.
  do 6 step.
  apply evtF_done. unfold crwB_post. cbv beta.
  do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [unfold crw_slots; exact CS|]. split; [exact CF | exact CH].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The inlined w_width, +0x168 .. +0x17c (0x8075c .. 0x80770): a0 = 2k, a3 = 126 + 72k - len, s10 = 2 + 2k; on a match
   it leaves to +0x18c (0x80780) with s10 = the width, after the twentieth pass it falls through to +0x180 (0x80774). *)
Section crwB_Loop.
Variables (RNG : ExecF.footprint)
  (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z) (Q : machine_state -> Prop).
Hypothesis Hn : 0 <= n <= 1600.

Local Abbreviation ST pc a0 a3 s10 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 2) (Z_to_bv 64 38) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Hypothesis KF : forall a0' a3' s10' : word, bv_unsigned s10' = PCR.w_width_model n ->
  ExecF.evtF rsegs RNG Q (ST 0x80780 a0' a3' s10').
Hypothesis KN : forall a0' a3' s10' : word, PCR.w_width_model n = -1 ->
  ExecF.evtF rsegs RNG Q (ST 0x80774 a0' a3' s10').

Lemma crwB_width_loop : forall f k (a0 a3 s10 : word),
  (S f + k = 20)%nat ->
  PCR.ww_go (S f) (2 + 2 * Z.of_nat k) n = PCR.w_width_model n ->
  bv_unsigned a0 = 2 * Z.of_nat k -> bv_unsigned s10 = 2 + 2 * Z.of_nat k ->
  bv_unsigned a3 = (126 + 72 * Z.of_nat k - n) mod 2^64 ->
  ExecF.evtF rsegs RNG Q (ST 0x8075c a0 a3 s10).
Proof.
  induction f as [|f IH]; intros k a0 a3 s10 Hk Hw H0 H10 H3; cbn [PCR.ww_go] in Hw.
  all: step; if_cases HE;
    [ zify_cond HE; rewrite H3 in HE;
      assert (En : n = 52 + (2 + 2 * Z.of_nat k) * 36) by (Z.div_mod_to_equations; lia);
      rewrite (proj2 (Z.eqb_eq _ _) En) in Hw; cbn [orb] in Hw;
      apply KF; rewrite <- Hw, H10; reflexivity
    | step; if_cases HZ ].
  all: zify_cond HE; rewrite H3 in HE.
  1, 3: zify_cond HZ; rewrite H3 in HZ;
    assert (En : n = 52 + (2 + 2 * Z.of_nat k) * 36 + 2) by (Z.div_mod_to_equations; lia);
    rewrite (proj2 (Z.eqb_neq n (52 + (2 + 2 * Z.of_nat k) * 36))) in Hw by lia;
    rewrite (proj2 (Z.eqb_eq _ _) En) in Hw; cbn [orb] in Hw;
    apply KF; rewrite <- Hw, H10; reflexivity.
  all: zify_cond HZ; rewrite H3 in HZ.
  all: assert (N1 : n <> 52 + (2 + 2 * Z.of_nat k) * 36)
         by (intro E; apply HE; replace (126 + 72 * Z.of_nat k - n) with 2 by lia; reflexivity).
  all: assert (N2 : n <> 52 + (2 + 2 * Z.of_nat k) * 36 + 2)
         by (intro E; apply HZ; replace (126 + 72 * Z.of_nat k - n) with 0 by lia; reflexivity).
  all: rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2) in Hw; cbn [orb] in Hw.
  all: do 3 step; step; if_cases HC.
  - (* last pass, back-branch taken: impossible, a0 = 40 > 38 *)
    exfalso. zify_cond HC. rewrite ?unsigned_lit_wrap, ?H0 in HC. Z.div_mod_to_equations. lia.
  - (* last pass, the loop ends: w_width = -1 *)
    apply KN. rewrite <- Hw. reflexivity.
  - apply (IH (S k)).
    + lia.
    + rewrite Nat2Z.inj_succ. replace (2 + 2 * Z.succ (Z.of_nat k)) with (2 + 2 * Z.of_nat k + 2) by lia. exact Hw.
    + rewrite Nat2Z.inj_succ, ?unsigned_lit_wrap, H0. rewrite Z.mod_small by lia. lia.
    + rewrite Nat2Z.inj_succ, ?unsigned_lit_wrap, H10, PCR.sw32 by lia. rewrite Z.mod_small by lia. lia.
    + rewrite Nat2Z.inj_succ, ?unsigned_lit_wrap, H3, Zplus_mod_idemp_l. f_equal. lia.
  - (* the loop ends before the last pass: impossible, a0 <= 38 *)
    exfalso. zify_cond HC. rewrite ?unsigned_lit_wrap, ?H0 in HC. Z.div_mod_to_equations. lia.
Qed.

End crwB_Loop.

(* ------------------------------------------------------------------------------------------------------------ *)
(* +0x18c (0x80780) .. the call, len >= 50, s10 = W the width (-1 or 2 .. 40): the UBSan trap on c + 16 (not
   reached: c + len <= SP1), c[16] behind its shadow check (the report at +0x4b0 not reached: `addressable`);
   c[16] <> 0 gives want = 0 at +0x1b0; else the UBSan trap on c + 17, c[17] behind its shadow check (report at
   +0x4bc), s11 = 0, and the tests slot < 0, c[17] <> 0, W <= 0 (want = 0) before `sltu s11, s5, s10`. *)
Lemma crwB_b16 : forall (RNG : ExecF.footprint)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m mk : word -> option byte) (bs : list byte)
    (SP1 FR c len slot W : Z) (J0 Jm J2 J3 Jx : list byte),
  2 ^ 46 <= SP1 -> SP1 + 88 <= 2 ^ 47 -> 4096 <= FR -> FR + 128 <= SP1 ->
  2147450880 <= crw_sh FR -> crw_sh FR + 16 <= SP1 -> (FR + 128 <= crw_sh FR \/ crw_sh FR + 16 <= FR) ->
  50 <= len <= 1600 -> -2 ^ 31 <= slot < 2 ^ 31 ->
  W = crw_W len -> (W = -1 \/ 2 <= W <= 40) ->
  (50 <= len ->
     Z.of_nat (length bs) = len /\ bytes_at rsegs m c bs /\ addressable m c len /\
     4096 <= c /\ c + len <= SP1 /\
     (c + len <= FR \/ FR + 128 <= c) /\ (c + len <= crw_sh FR \/ crw_sh FR + 16 <= c) /\
     shadow_addr (c + len - 1) < SP1 /\
     (shadow_addr (c + len - 1) < FR \/ FR + 128 <= shadow_addr c) /\
     (shadow_addr (c + len - 1) < crw_sh FR \/ crw_sh FR + 16 <= shadow_addr c) /\
     ExecF.rng RNG c len /\
     ExecF.rng RNG (shadow_addr c) (shadow_addr (c + len - 1) - shadow_addr c + 1)) ->
  munch [(SP1, SP1 + 88); (FR, FR + 80); (crw_sh FR, crw_sh FR + 16)] m mk -> wmono rsegs m mk ->
  rw_cells rsegs mk SP1 [CB 8 J0; C8 (Z_to_bv 64 FR); C8 (Z_to_bv 64 (crw_sh FR)); C8 (Z_to_bv 64 FR); CB 24 Jm;
                         C8 (Z_to_bv 64 (FR + 32)); CB 8 J2; C8 (Z_to_bv 64 FR); CB 8 J3] ->
  rw_cells rsegs mk FR [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 CRW_DESC); C8 (Z_to_bv 64 CRW_ENTRY);
                        CB 8 Jx; CB 48 crw_fill] ->
  rw_cells rsegs mk (crw_sh FR) [CB 16 crw_shadow_bytes] ->
  ExecF.rng RNG SP1 88 ->
  ExecF.evtF rsegs RNG (crwB_post gp tp s0 s4 s6 s8 s9 F fc m bs SP1 FR c len slot)
    (MS (mkR ra (Z_to_bv 64 SP1) gp tp t0 t1 t2 s0 (Z_to_bv 64 SP1) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 len) (Z_to_bv 64 c) s4 (Z_to_bv 64 slot) s6 (Z_to_bv 64 ASAN_K) s8 s9
             (Z_to_bv 64 W) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x80780) fc None mk (seg_rom rsegs)).
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 s11 t3 t4 t5 t6 F fc m mk bs SP1 FR c len slot W
    J0 Jm J2 J3 Jx H46 H47 HF0 HF1 HK HF2 HFD HLEN HSL EW RW P50 MU WM CS CF CH RS.
  destruct (P50 ltac:(lia)) as (HL & BB & AD & C0 & C1 & C2 & C3 & S1 & S2 & S3 & RC & RSH). clear P50.
  destruct AD as (_ & _ & _ & AB).
  destruct (AB 16 ltac:(lia)) as (_ & k16 & MK16 & SK16).
  destruct (AB 17 ltac:(lia)) as (_ & k17 & MK17 & SK17). clear AB.
  unfold shadow_ok in SK16, SK17.
  assert (SA : shadow_addr c <= shadow_addr (c + 16) /\ shadow_addr (c + 16) <= shadow_addr (c + 17) /\
               shadow_addr (c + 17) <= shadow_addr (c + len - 1)).
  { unfold shadow_addr. split; [|split]; apply Z.add_le_mono_r, Z.div_le_mono; lia. }
  assert (SB : 2147450880 <= shadow_addr c)
    by (unfold shadow_addr, ASAN_K; pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)); lia).
  assert (OUT : forall a, shadow_addr c <= a <= shadow_addr (c + len - 1) ->
                outside [(SP1, SP1 + 88); (FR, FR + 80); (crw_sh FR, crw_sh FR + 16)] a).
  { intros a Ha. cbn [outside]. repeat split; try exact I; lia. }
  pose proof (crwB_mrd_tp _ m mk (shadow_addr (c + 16)) k16 MU ltac:(lia)
                (OUT (shadow_addr (c + 16)) ltac:(lia)) MK16) as MK16k.
  pose proof (crwB_mrd_tp _ m mk (shadow_addr (c + 17)) k17 MU ltac:(lia)
                (OUT (shadow_addr (c + 17)) ltac:(lia)) MK17) as MK17k.
  pose proof (bytes_at_transport rsegs _ m mk c bs BB MU
                ltac:(cbn [disjoint_from]; rewrite HL; repeat split; try exact I; lia)) as BBk.
  pose proof (crwB_rdz mk c bs 16 BBk ltac:(lia)) as RB16. change (Z.to_nat 16) with 16%nat in RB16.
  pose proof (crwB_rdz mk c bs 17 BBk ltac:(lia)) as RB17. change (Z.to_nat 17) with 17%nat in RB17.
  pose proof (crwB_rdm _ _ _ MK16k) as RD16. pose proof (crwB_rdm _ _ _ MK17k) as RD17.
  clear OUT MK16 MK17 MK16k MK17k BB BBk.
  pose proof (Z.mod_pos_bound (c + 16) 8 ltac:(lia)) as MB16.
  pose proof (Z.mod_pos_bound (c + 17) 8 ltac:(lia)) as MB17.
  pose proof (crwB_byte_range (nth 16 bs (Z_to_bv 8 0))) as R16.
  pose proof (crwB_byte_range (nth 17 bs (Z_to_bv 8 0))) as R17.
  assert (SW : bv_swrap 64 len = len) by (apply bv_swrap_small; change (bv_half_modulus 64) with (2^63); lia).
  destruct (PCR.ww_facts len ltac:(lia)) as [WF _].
  (* +0x18c `addi a0, zero, -16`, +0x190 `bgeu s3, a0`: the UBSan trap is not reached *)
  step. step. crwB_f.
  (* +0x194 .. +0x1a0: the shadow byte of c + 16; +0x1a4 `bnez a1`, the check at +0x4a8 / +0x4ac returns *)
  step. step. step. setreg 11 (Z_to_bv 64 (shadow_addr (c + 16))) ltac:(crwB_shq).
  step. step. rewrite crwB_sxb_eq0.
  destruct SK16 as [K|[K Ku]].
  1: rewrite (proj2 (Z.eqb_eq _ _) K); cbn [negb].
  2: rewrite (proj2 (Z.eqb_neq (bv_signed k16) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite crwB_land7, (unsigned_lit (c + 16)) by lia;
     rewrite (crwB_lts_low ((c + 16) mod 8) k16) by lia;
     rewrite (proj2 (Z.ltb_lt _ _) K); cbn [negb].
  (* +0x1a8 `lbu a0, 0(a0)` (c[16]), +0x1ac `beqz a0`; c[16] <> 0: +0x1b0 `mv s11, zero` *)
  all: step; step.
  all: destruct (Z.eqb_spec (bv_unsigned (nth 16 bs (Z_to_bv 8 0))) 0) as [B16|B16];
    [ crwB_t
    | crwB_f; step; eapply crwB_tail; try crwB_side;
      unfold crw_want; symmetry; apply PCR.srm_zero; right; left; exact B16 ].
  (* +0x460 `addi a0, zero, -18`, +0x464 `bltu a0, s3`: the UBSan trap is not reached *)
  all: step; step; crwB_f.
  (* +0x468 .. +0x474: the shadow byte of c + 17; +0x478 `bnez a1`, the check at +0x4b4 / +0x4b8 returns *)
  all: step; step; step; setreg 11 (Z_to_bv 64 (shadow_addr (c + 17))) ltac:(crwB_shq).
  all: step; step; rewrite crwB_sxb_eq0.
  all: destruct SK17 as [K'|[K' Ku']].
  all: first
    [ rewrite (proj2 (Z.eqb_eq (bv_signed k17) 0) K'); cbn [negb]
    | rewrite (proj2 (Z.eqb_neq (bv_signed k17) 0) ltac:(lia)); cbn [negb]; step; step;
      rewrite crwB_land7, (unsigned_lit (c + 17)) by lia;
      rewrite (crwB_lts_low ((c + 17) mod 8) k17) by lia;
      rewrite (proj2 (Z.ltb_lt _ _) K'); cbn [negb] ].
  (* +0x47c `mv s11, zero`, +0x480 `bltz s5`: slot < 0 gives want = 0 *)
  all: step; step.
  all: destruct (Z.ltb_spec slot 0) as [SN|SN];
    [ crwB_t; eapply crwB_tail; try crwB_side;
      unfold crw_want; symmetry; apply PCR.srm_zero; right; right; right; left; exact SN
    | crwB_f ].
  (* +0x484 `lbu a0, 0(a0)` (c[17]), +0x488 `bnez a0`: c[17] <> 0 gives want = 0 *)
  all: step; step.
  all: destruct (Z.eqb_spec (bv_unsigned (nth 17 bs (Z_to_bv 8 0))) 0) as [B17|B17];
    [ crwB_f
    | crwB_t; eapply crwB_tail; try crwB_side;
      unfold crw_want; symmetry; apply PCR.srm_zero; right; right; left; exact B17 ].
  (* +0x48c `blez s10`: no width (W = -1) gives want = 0 *)
  all: step.
  all: destruct RW as [RW|RW];
    [ crwB_t; eapply crwB_tail; try crwB_side;
      unfold crw_want; symmetry; apply PCR.srm_zero; right; right; right; right; left;
      rewrite SW, <- WF; unfold crw_W in EW; lia
    | crwB_f ].
  (* +0x490 `sltu s11, s5, s10`, +0x494 `j`: want = (slot < W) *)
  all: step; step.
  all: rewrite v_sltu_b2z, (unsigned_lit slot), (unsigned_lit W) by lia.
  all: eapply crwB_tail; try crwB_side.
  all: unfold crw_want; destruct (Z.ltb_spec slot W) as [LT|GE]; cbn [Z.b2z];
    [ destruct (PCR.srm_one len bs slot ltac:(lia) B16 B17
                  ltac:(rewrite SW, <- WF; unfold crw_W in EW; lia)) as [M1 _]; rewrite M1; reflexivity
    | symmetry; apply PCR.srm_zero; right; right; right; right; right;
      rewrite SW, <- WF; unfold crw_W in EW; lia ].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The segment. *)
Lemma crw_segB_F : crw_segB_stmt.
Proof.
  unfold crw_segB_stmt.
  intros RNG ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs SP1 FR c len slot
    Js Jf Jh H46 H47 H32 HF0 HF64 HF1 HF2 HFD HLEN HSL CS CF CH RS RF RH P50.
  lazymatch goal with |- ExecF.evtF _ _ _ ?ms =>
    change (ExecF.evtF rsegs RNG (crwB_post gp tp s0 s4 s6 s8 s9 F fc m bs SP1 FR c len slot) ms) end.
  clear H32 HF64.
  assert (HK : 2147450880 <= crw_sh FR)
    by (unfold crw_sh, ASAN_K; pose proof (Z.div_pos FR 8 ltac:(lia) ltac:(lia)); lia).
  pose proof (munch_refl [(SP1, SP1 + 88); (FR, FR + 80); (crw_sh FR, crw_sh FR + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold CRW_RET0.
  (* +0x78 `mv a6, a0`, `j`, +0x84 `mv t0, a6`, +0x88 `bnez a6`: taken, F is not null *)
  step. step. step. step. crwB_t.
  (* +0xa8 .. +0xe4: F saved at s1 + 0x48; the header words 0x41b58ab3, 0x16e29, 0x805f4 at F; a7 = the frame's
     shadow address *)
  do 16 step.
  setreg 17 (Z_to_bv 64 (crw_sh FR)) ltac:(crwB_shq).
  (* +0xe8 .. +0x128: the sixteen shadow bytes; +0x12c a1 = 0x5a5a5a5a; +0x130 v saved at s1 + 0x38; `mv a2, t1` *)
  do 20 step.
  (* +0x138 .. +0x140: the twelve words of v filled with 0x5a5a5a5a *)
  do 11 (step; step; step; crwB_t).
  step; step; step; crwB_f.
  apply crwB_fr_merge in CF.
  pose proof (crwB_merge_to _ _ _ 16 crw_shadow_bytes CH eq_refl ltac:(crwB_beq)) as CH'. clear CH.
  rename CH' into CH.
  (* +0x144 .. +0x164: the inlined w_width's set-up; F, the shadow address and F saved at s1 + 0x18 / 0x10 / 0x08 *)
  do 9 step.
  eapply (crwB_width_loop) with (f := 19%nat) (k := 0%nat) (n := len).
  all: lazymatch goal with
       | |- forall _ : word, _ => idtac
       | _ => first [ lia | reflexivity
                    | crwB_u; first [ reflexivity | (rewrite unsigned_lit_wrap; f_equal; cbn [Z.of_nat]; lia) ] ]
       end.
  - (* a width matched: s10 = w_width(len), len = 52 + 36 w or 54 + 36 w *)
    intros a0' a3' s10' H10.
    pose proof (zr_word s10') as R10. unfold inr64 in R10.
    destruct (PCR.ww_facts len HLEN) as [_ [WE|(W1 & W2 & W3)]]; [lia|].
    rewrite <- (Z_to_bv_lit_self s10'), H10.
    eapply crwB_b16 with (W := PCR.w_width_model len); try crwB_side.
  - (* no width: +0x180 `addi a0, zero, 0x31`, `addi s10, zero, -1`, +0x188 `bgeu a0, s2` *)
    intros a0' a3' s10' Hm1.
    step. step. step.
    destruct (Z_le_gt_dec len 49) as [L49|G49].
    + crwB_t. step.
      eapply crwB_tail; try crwB_side.
      all: first [ unfold crw_W; rewrite Hm1; reflexivity
                 | unfold crw_want; symmetry; apply PCR.srm_zero; left; lia ].
    + crwB_f.
      eapply crwB_b16 with (W := -1); try crwB_side.
      all: unfold crw_W; rewrite Hm1; reflexivity.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Byte, word and shadow helpers (lib/B/Prog/AsanKAProof.v, lib/Prog/check_read.v, at image B's segments). *)

Lemma crwC_byte_signed_range : forall k : byte, -128 <= bv_signed k < 128.
Proof.
  intros k. pose proof (bv_signed_in_range 8 k ltac:(lia)) as R. unfold bv_half_modulus, bv_modulus in R.
  change (2 ^ Z.of_N 8 / 2) with 128 in R. lia.
Qed.

Lemma crwC_sxb_eq0 : forall k : byte, bv_eqb (sxb k) (Z_to_bv 64 0) = (bv_signed k =? 0).
Proof.
  intros k. unfold sxb, bv_eqb. pose proof (crwC_byte_signed_range k).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  destruct (Z.eqb_spec (bv_signed k) 0) as [E|E].
  - rewrite E. reflexivity.
  - apply Z.eqb_neq. change (0 mod 2^64) with 0. Z.div_mod_to_equations. lia.
Qed.

Lemma crwC_lts_low : forall (x : Z) (k : byte), 0 <= x < 8 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (crwC_byte_signed_range k).
  rewrite !PCR.signed_lit by lia. reflexivity.
Qed.

Lemma crwC_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. exact (Z.land_ones x 3 ltac:(lia)). Qed.

Lemma crwC_rd1 : forall m a b, mrd rsegs m (wa a) = Some b -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof. intros m a b H. rewrite ov_rdn, rdn_unfold, H. reflexivity. Qed.

Lemma crwC_rdw0 : forall m (w : word) a b, mrd rsegs m (wa a) = Some b -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w 1 = Some [b].
Proof. intros m w a b H E. rewrite <- (Z_to_bv_bv_unsigned w), E. apply crwC_rd1. exact H. Qed.

Lemma crwC_firstn1 : forall (bs : list byte) k, (k < length bs)%nat ->
  firstn 1 (skipn k bs) = [nth k bs (Z_to_bv 8 0)].
Proof.
  induction bs as [|b bs IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma crwC_rdz : forall m a bs k, bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk. rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  rewrite crwC_firstn1 by lia. reflexivity.
Qed.

Lemma crwC_bytes_tp : forall m m' lo hi a bs, munch [(lo, hi)] m m' ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo hi a bs MU Hd H. eapply bytes_at_transport; [exact H | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

(* The shadow byte of a byte x of c, at the memory of the run (it writes only the slot area). *)
Lemma crwC_shadow : forall m mk c len P1 x, addressable m c len -> munch [(P1, P1 + 88)] m mk ->
  c <= x < c + len -> c + len <= P1 -> 2 ^ 46 - 208 <= P1 ->
  exists k, mrd rsegs mk (wa (x / 8 + 2147450880)) = Some k /\ shadow_ok x (bv_signed k).
Proof.
  intros m mk c len P1 x (H0 & H1 & H2 & AB) MU Hx HC HP.
  destruct (AB (x - c) ltac:(lia)) as (_ & k & MK & SK).
  replace (c + (x - c)) with x in MK, SK by lia.
  exists k. split; [|exact SK].
  unfold shadow_addr, ASAN_K in MK. unfold APPMEM_END in H2.
  assert (D : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  unfold mrd in *. rewrite MU; [exact MK|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

Lemma crwC_shrng : forall RNG c len x,
  ExecF.rng RNG (shadow_addr c) (shadow_addr (c + len - 1) - shadow_addr c + 1) ->
  0 <= c -> c <= x < c + len -> ExecF.rng RNG (x / 8 + 2147450880) 1.
Proof.
  intros RNG c len x R Hc Hx. apply (ExecF.rng_sub RNG _ _ _ _ R); unfold shadow_addr, ASAN_K.
  - pose proof (Z.div_le_mono c x 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono x (c + len - 1) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* The shadow address as `srli` / `add s7` form it. *)
Lemma crwC_shq : forall E X, E = X -> 0 <= X < 2 ^ 47 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 E)) 3 + 2147450880)) = X / 8 + 2147450880.
Proof.
  intros E X -> HX. rewrite (unsigned_lit X) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (D : 0 <= X / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  apply unsigned_lit. lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Tactics. *)

(* A branch condition as a Z fact. *)
Ltac crwC_zc H :=
  try unfold bv_eqb in H; try unfold bv_ltu in H; try unfold bv_lts in H; try unfold zxb in H;
  fold_lit_ux_in H;
  repeat match type of H with
  | context [bv_signed (Z_to_bv 64 ?z)] => rewrite (PCR.signed_lit z) in H by lia
  | context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in H by lia
  end;
  zify_bool H.

(* A symbolic branch that is taken (crwC_t) or not taken (crwC_f); lia refutes the other side. *)
Ltac crwC_t := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let HC := fresh "HC" in destruct c eqn:HC; [ clear HC | exfalso; crwC_zc HC; lia ]
  end.
Ltac crwC_f := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let HC := fresh "HC" in destruct c eqn:HC; [ exfalso; crwC_zc HC; lia | clear HC ]
  end.

(* A byte store whose bytes are a zero-extended loaded byte. *)
Ltac crwC_sb := step; rewrite ?le1_zxb; mem_after_store_opt.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The two shadow checks of the braid loop. The fast path (shadow byte 0) and the slow path (the byte's offset in its
   granule below the shadow byte) meet again; the report calls at +0x4c0 / +0x4c4 are refuted from shadow_ok. *)

(* +0x2a8 (0x8089c) `lb a4, 0(a4)`, +0x2ac `bnez a4`; slow path +0x2e8 `andi a5, a0, 7`, `bge a5, a4`, `j`;
   both reach +0x2b0 (0x808a4). *)
Lemma crwC_chk1 : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mk : word -> option byte) (Q : machine_state -> Prop) (X : Z) (k : byte),
  bv_unsigned a0 = X -> bv_unsigned a4 = X / 8 + 2147450880 ->
  mrd rsegs mk (wa (X / 8 + 2147450880)) = Some k -> shadow_ok X (bv_signed k) ->
  ExecF.rng RNG (X / 8 + 2147450880) 1 ->
  (forall a4' a5' : word, ExecF.evtF rsegs RNG Q
     (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x808a4) fc None mk (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8089c) fc None mk (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc mk Q X k H0 H4 MK SK RX K.
  pose proof (crwC_rdw0 mk a4 _ _ MK H4) as R.
  assert (R4 : ExecF.rng RNG (bv_unsigned a4) 1) by (rewrite H4; exact RX).
  clear MK RX.
  step. clear R. step. rewrite crwC_sxb_eq0.
  destruct SK as [C|[C Cu]].
  - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. apply K.
  - pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as MB.
    rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)). cbn [negb].
    step. step. rewrite crwC_land7, H0, (crwC_lts_low (X mod 8) k MB), (proj2 (Z.ltb_lt _ _) C). cbn [negb].
    step. apply K.
Qed.

(* +0x2cc (0x808c0) `lb s3, 0(a3)`, +0x2d0 `bnez s3`; slow path +0x2f4 `andi a3, a0, 7`, `bge a3, s3`, `j`;
   both reach +0x2d4 (0x808c8). *)
Lemma crwC_chk2 : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mk : word -> option byte) (Q : machine_state -> Prop) (X : Z) (k : byte),
  bv_unsigned a0 = X -> bv_unsigned a3 = X / 8 + 2147450880 ->
  mrd rsegs mk (wa (X / 8 + 2147450880)) = Some k -> shadow_ok X (bv_signed k) ->
  ExecF.rng RNG (X / 8 + 2147450880) 1 ->
  (forall a3' s3' : word, ExecF.evtF rsegs RNG Q
     (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3' a4 a5 a6 a7 s2 s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x808c8) fc None mk (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x808c0) fc None mk (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc mk Q X k H0 H3 MK SK RX K.
  pose proof (crwC_rdw0 mk a3 _ _ MK H3) as R.
  assert (R3 : ExecF.rng RNG (bv_unsigned a3) 1) by (rewrite H3; exact RX).
  clear MK RX.
  step. clear R. step. rewrite crwC_sxb_eq0.
  destruct SK as [C|[C Cu]].
  - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. apply K.
  - pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as MB.
    rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)). cbn [negb].
    step. step. rewrite crwC_land7, H0, (crwC_lts_low (X mod 8) k MB), (proj2 (Z.ltb_lt _ _) C). cbn [negb].
    step. apply K.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The braid loop +0x294 .. +0x2e0 (0x80888 .. 0x808d4), three passes s9 = 0, 2, 4: be[s9] := g[s9 + 1] and
   be[s9 + 1] := g[s9], g = G the sample's braid group (at offset G - c in c), be = s1 + 0x52; each read of c behind
   its shadow check (crwC_chk1 / crwC_chk2); `bgeu s9, s4` (s4 = ~g) never traps. *)
Definition crwC_g (bs : list byte) (c G k : Z) : byte := nth (Z.to_nat (G - c + k)) bs (Z_to_bv 8 0).

Ltac crwC_uq := first [ rewrite unsigned_lit by lia; lia | lia ].

(* The byte c[k] as an `ov_read_bytes` fact at the run's memory. *)
Ltac crwC_ldc BB k := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (crwC_rdz mm _ _ k BB ltac:(lia)) as RB
  end.

Lemma crwC_braid : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t2 s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s5 s8 s10 s11 t3 t4 t5 t6
     w8 w16 w24 w32 w40 w48 w56 w72 : word)
    (F : bvmap 5 word) (fc : bv 32) (m mk : word -> option byte) (bs : list byte) (Q : machine_state -> Prop)
    (P1 c len G : Z) (J0 J2 J3 : list byte),
  2 ^ 46 - 208 <= P1 -> P1 + 88 <= 2 ^ 47 ->
  Z.of_nat (length bs) = len -> 4096 <= c -> c + len <= P1 -> c + 50 <= G -> G + 6 <= c + len ->
  rw_cells rsegs mk P1 [CB 8 J0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 8 J2; C8 w72; CB 8 J3] ->
  bytes_at rsegs mk c bs -> munch [(P1, P1 + 88)] m mk -> wmono rsegs m mk -> addressable m c len ->
  ExecF.rng RNG P1 88 -> ExecF.rng RNG c len ->
  ExecF.rng RNG (shadow_addr c) (shadow_addr (c + len - 1) - shadow_addr c + 1) ->
  (forall (a0' a3' a4' a5' s3' : word) mk' x,
     rw_cells rsegs mk' P1 [CB 8 J0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 8 J2; C8 w72;
       CB 2 x; C1 (crwC_g bs c G 1); C1 (crwC_g bs c G 0); C1 (crwC_g bs c G 3); C1 (crwC_g bs c G 2);
       C1 (crwC_g bs c G 5); C1 (crwC_g bs c G 4)] ->
     munch [(P1, P1 + 88)] m mk' -> wmono rsegs m mk' ->
     ExecF.evtF rsegs RNG Q
       (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (G + 1)) t2 s0 s1 a0' a1 a2 a3' a4' a5' (Z_to_bv 64 (P1 + 83))
                (Z_to_bv 64 6) s2 s3' (Z_to_bv 64 (18446744073709551615 - G)) s5 (Z_to_bv 64 (G - 50))
                (Z_to_bv 64 2147450880) s8 (Z_to_bv 64 6) s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x808f4) fc None mk' (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (G + 1)) t2 s0 s1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (P1 + 83))
             (Z_to_bv 64 6) s2 s3 (Z_to_bv 64 (18446744073709551615 - G)) s5 (Z_to_bv 64 (G - 50))
             (Z_to_bv 64 2147450880) s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x80888) fc None mk (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t2 s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s5 s8 s10 s11 t3 t4 t5 t6
    w8 w16 w24 w32 w40 w48 w56 w72 F fc m mk bs Q P1 c len G J0 J2 J3
    HP0 HP1 HL HC0 HC1 HG0 HG1 FRC BB MU WM AD RFR RC RSC K.
  (* pass s9 = 0: +0x294 `bgeu s9, s4` (not taken), +0x298 .. +0x2a4 the shadow address of g + 1 *)
  step. crwC_f. do 4 step.
  destruct (crwC_shadow m _ c len P1 (G + 1) AD MU ltac:(lia) HC1 HP0) as (k1 & MK1 & SK1).
  eapply (crwC_chk1 RNG) with (X := G + 1) (k := k1);
    [ crwC_uq | apply crwC_shq; lia | exact MK1 | exact SK1 | apply (crwC_shrng RNG c len); [exact RSC | lia | lia] | ].
  clear MK1 SK1 k1. intros ? ?.
  (* +0x2b0 `add a4, t1, s9`, +0x2b4 `lbu a3` (g[1]), +0x2b8 `add a5`, +0x2bc `addi a0`, +0x2c0 `sb a3` (be[0]) *)
  step. crwC_ldc BB (G - c + 1). step. clear RB.
  step. step. crwC_sb.
  (* +0x2c4 .. +0x2c8 the shadow address of g + 0 *)
  step. step.
  destruct (crwC_shadow m _ c len P1 (G + 0) AD MU ltac:(lia) HC1 HP0) as (k2 & MK2 & SK2).
  eapply (crwC_chk2 RNG) with (X := G + 0) (k := k2);
    [ crwC_uq | apply crwC_shq; lia | exact MK2 | exact SK2 | apply (crwC_shrng RNG c len); [exact RSC | lia | lia] | ].
  clear MK2 SK2 k2. intros ? ?.
  (* +0x2d4 `lbu a0, -1(a4)` (g[0]), +0x2d8 `addi s9, s9, 2`, +0x2dc `sb a0` (be[1]), +0x2e0 `bne s9, a7` *)
  crwC_ldc BB (G - c + 0). step. clear RB.
  step. crwC_sb.
  step.
  if_true.
  (* pass s9 = 2: +0x294 `bgeu s9, s4` (not taken), +0x298 .. +0x2a4 the shadow address of g + 3 *)
  step. crwC_f. do 4 step.
  destruct (crwC_shadow m _ c len P1 (G + 3) AD MU ltac:(lia) HC1 HP0) as (k1 & MK1 & SK1).
  eapply (crwC_chk1 RNG) with (X := G + 3) (k := k1);
    [ crwC_uq | apply crwC_shq; lia | exact MK1 | exact SK1 | apply (crwC_shrng RNG c len); [exact RSC | lia | lia] | ].
  clear MK1 SK1 k1. intros ? ?.
  (* +0x2b0 `add a4, t1, s9`, +0x2b4 `lbu a3` (g[3]), +0x2b8 `add a5`, +0x2bc `addi a0`, +0x2c0 `sb a3` (be[2]) *)
  step. crwC_ldc BB (G - c + 3). step. clear RB.
  step. step. crwC_sb.
  (* +0x2c4 .. +0x2c8 the shadow address of g + 2 *)
  step. step.
  destruct (crwC_shadow m _ c len P1 (G + 2) AD MU ltac:(lia) HC1 HP0) as (k2 & MK2 & SK2).
  eapply (crwC_chk2 RNG) with (X := G + 2) (k := k2);
    [ crwC_uq | apply crwC_shq; lia | exact MK2 | exact SK2 | apply (crwC_shrng RNG c len); [exact RSC | lia | lia] | ].
  clear MK2 SK2 k2. intros ? ?.
  (* +0x2d4 `lbu a0, -1(a4)` (g[2]), +0x2d8 `addi s9, s9, 2`, +0x2dc `sb a0` (be[3]), +0x2e0 `bne s9, a7` *)
  crwC_ldc BB (G - c + 2). step. clear RB.
  step. crwC_sb.
  step.
  if_true.
  (* pass s9 = 4: +0x294 `bgeu s9, s4` (not taken), +0x298 .. +0x2a4 the shadow address of g + 5 *)
  step. crwC_f. do 4 step.
  destruct (crwC_shadow m _ c len P1 (G + 5) AD MU ltac:(lia) HC1 HP0) as (k1 & MK1 & SK1).
  eapply (crwC_chk1 RNG) with (X := G + 5) (k := k1);
    [ crwC_uq | apply crwC_shq; lia | exact MK1 | exact SK1 | apply (crwC_shrng RNG c len); [exact RSC | lia | lia] | ].
  clear MK1 SK1 k1. intros ? ?.
  (* +0x2b0 `add a4, t1, s9`, +0x2b4 `lbu a3` (g[5]), +0x2b8 `add a5`, +0x2bc `addi a0`, +0x2c0 `sb a3` (be[4]) *)
  step. crwC_ldc BB (G - c + 5). step. clear RB.
  step. step. crwC_sb.
  (* +0x2c4 .. +0x2c8 the shadow address of g + 4 *)
  step. step.
  destruct (crwC_shadow m _ c len P1 (G + 4) AD MU ltac:(lia) HC1 HP0) as (k2 & MK2 & SK2).
  eapply (crwC_chk2 RNG) with (X := G + 4) (k := k2);
    [ crwC_uq | apply crwC_shq; lia | exact MK2 | exact SK2 | apply (crwC_shrng RNG c len); [exact RSC | lia | lia] | ].
  clear MK2 SK2 k2. intros ? ?.
  (* +0x2d4 `lbu a0, -1(a4)` (g[4]), +0x2d8 `addi s9, s9, 2`, +0x2dc `sb a0` (be[5]), +0x2e0 `bne s9, a7` *)
  crwC_ldc BB (G - c + 4). step. clear RB.
  step. crwC_sb.
  step.
  if_false. step.
  eapply K; [exact FRC | exact MU | exact WM].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The twelve samples. *)

Lemma crwC_le4s_len : forall f, length (PCR.le4s f) = 48%nat.
Proof. intros f. unfold PCR.le4s. cbn [seq flat_map]. rewrite !length_app, !length_le4. reflexivity. Qed.

(* lib/Prog/check_read.v le4s_read, at image B's segments. *)
Lemma crwC_le4s_read : forall m A f i, bytes_at rsegs m A (PCR.le4s f) -> 0 <= i < 12 ->
  ov_read_bytes rsegs m (wa (A + 4 * i)) 4 = Some (le4 (Z_to_bv 64 (f i))).
Proof.
  intros m A f i H Hi. pose proof (crwC_le4s_len f) as L.
  rewrite (bytes_at_read rsegs m A (PCR.le4s f) (4 * i) 4 H) by lia. f_equal.
  replace (Z.to_nat (4 * i)) with (4 * Z.to_nat i)%nat by lia.
  unfold PCR.le4s. rewrite (PCR.flat4_nth (fun s => le4 (Z_to_bv 64 (f (Z.of_nat s))))) by (first [intros; apply length_le4 | lia]).
  cbn [Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma crwC_mulb : forall i W, 0 <= i < 12 -> 0 <= W -> 0 <= i * W <= 11 * W.
Proof. intros i W Hi HW. nia. Qed.

(* The slot area during the loop: ~c at +0x28, the fill word at +0x20, the be buffer inside the last eight bytes. *)
Definition crwC_fr (FR c : Z) (NC : word) (J0 J2 J3 : list byte) : list cell :=
  [CB 8 J0; C8 (Z_to_bv 64 FR); C8 (Z_to_bv 64 (crw_sh FR)); C8 (Z_to_bv 64 FR); C8 (Z_to_bv 64 1515870810); C8 NC;
   C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 (FR + 32)); CB 8 J2; C8 (Z_to_bv 64 FR); CB 8 J3].

Lemma crwC_merge : forall mk P1 FR c NC J0 J2 x b0 b1 b2 b3 b4 b5,
  rw_cells rsegs mk P1 [CB 8 J0; C8 (Z_to_bv 64 FR); C8 (Z_to_bv 64 (crw_sh FR)); C8 (Z_to_bv 64 FR);
    C8 (Z_to_bv 64 1515870810); C8 NC; C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 (FR + 32)); CB 8 J2; C8 (Z_to_bv 64 FR);
    CB 2 x; C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5] ->
  exists J3, rw_cells rsegs mk P1 (crwC_fr FR c NC J0 J2 J3).
Proof.
  intros mk P1 FR c NC J0 J2 x b0 b1 b2 b3 b4 b5 H.
  pose proof (rw_cells_merge rsegs mk P1
    [CB 8 J0; C8 (Z_to_bv 64 FR); C8 (Z_to_bv 64 (crw_sh FR)); C8 (Z_to_bv 64 FR);
     C8 (Z_to_bv 64 1515870810); C8 NC; C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 (FR + 32)); CB 8 J2; C8 (Z_to_bv 64 FR)]
    [CB 2 x; C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5] [] H) as M.
  eexists. exact M.
Qed.

(* The sample word as image B builds it (+0x30c .. +0x334), the plain image's wsamp with two `or`s turned round. *)
Lemma crwC_wsamp_eq : forall hi mid lo : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64
    (Z.shiftl (bv_unsigned (zxb mid)) 8))) (bv_unsigned (zxb lo))))) (bv_unsigned (Z_to_bv 64 (Z.shiftl
    (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sxb hi)) 255))) 16))))))
    (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sxb hi)) 18446744073692774400))))
  = Z_to_bv 64 (PCR.samp24 hi mid lo).
Proof.
  intros hi mid lo. rewrite <- PCR.wsamp_eq. unfold PCR.wsamp.
  rewrite (Z.lor_comm (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb mid)) 8))) (bv_unsigned (zxb lo))).
  rewrite (Z.lor_comm (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (zxb lo))
             (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb mid)) 8))))))).
  reflexivity.
Qed.

Section crwC_L.
Variables (RNG : ExecF.footprint) (gp tp T0 A2 NC : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (bs : list byte) (SP0 P1 FR c len slot W want AT : Z) (J0 J2 : list byte)
  (f : Z -> Z) (Q : machine_state -> Prop).

(* The loop's state: the registers the set-up fixed, and the ones a sample changes. *)
Local Abbreviation LST pc ra a0 a1 a3 a4 a5 s2 s3 s4 s6 s9 t1 mk :=
  (MS (mkR ra (Z_to_bv 64 P1) gp tp T0 t1 (Z_to_bv 64 AT) (Z_to_bv 64 SP0) (Z_to_bv 64 P1) a0 a1 A2 a3 a4 a5
     (Z_to_bv 64 (P1 + 83)) (Z_to_bv 64 6) s2 s3 s4 (Z_to_bv 64 (P1 + (84 + AT))) s6 (Z_to_bv 64 2147450880)
     (Z_to_bv 64 (c + 51)) s9 (Z_to_bv 64 W) (Z_to_bv 64 want) (Z_to_bv 64 (P1 + (82 + AT))) (Z_to_bv 64 (AT + 1))
     (Z_to_bv 64 (AT + 2)) (Z_to_bv 64 (P1 + (83 + AT))))
   F (Z_to_bv 64 pc) fc None mk (seg_rom rsegs)).

(* The loop invariant: the slot area, and the run writes nothing else. *)
Definition crwC_linv (mk : word -> option byte) : Prop :=
  (exists J3, rw_cells rsegs mk P1 (crwC_fr FR c NC J0 J2 J3)) /\ munch [(P1, P1 + 88)] m mk /\ wmono rsegs m mk.

Hypothesis HP1 : 2 ^ 46 - 208 <= P1 /\ P1 + 88 <= 2 ^ 47.
Hypothesis HFR : 4096 <= FR /\ FR + 128 <= P1.
Hypothesis HV : bytes_at rsegs m (FR + 32) (PCR.le4s f).
Hypothesis RF : ExecF.rng RNG FR 128.
Hypothesis RFR : ExecF.rng RNG P1 88.
Hypothesis HWNT : want = 0 \/ want = 1.
Hypothesis HW : want = 1 -> 2 <= W <= 40 /\ W mod 2 = 0 /\ 0 <= slot < W /\ 52 + 36 * W <= len.
Hypothesis HF0 : want = 0 -> forall i, 0 <= i < 12 -> f i = 1515870810.
Hypothesis HF1 : want = 1 -> forall i, 0 <= i < 12 -> f i = PSR.rp_sample bs W slot i.
Hypothesis HA2 : want = 1 -> A2 = Z_to_bv 64 (slot - slot mod 2).
Hypothesis HNC : want = 1 -> bv_unsigned NC = 2 ^ 64 - 1 - c.
Hypothesis HT0 : bv_unsigned T0 = 2 ^ 64 - 1 - (P1 + 82).
Hypothesis HAT : AT = 3 * (slot mod 2).
Hypothesis HCC : want = 1 ->
  Z.of_nat (length bs) = len /\ bytes_at rsegs m c bs /\ addressable m c len /\ 4096 <= c /\ c + len <= P1 /\
  ExecF.rng RNG c len /\ ExecF.rng RNG (shadow_addr c) (shadow_addr (c + len - 1) - shadow_addr c + 1).

Lemma crwC_body : forall i RA a0 a3 a4 a5 s2 s3 s4 s6 s9 t1 mk, 0 <= i < 12 ->
  (want = 1 -> RA = Z_to_bv 64 (slot - slot mod 2 + W * i)) -> crwC_linv mk ->
  (forall a0' a3' a4' a5' s2' s3' s4' s6' s9' t1' mk', crwC_linv mk' ->
     ExecF.evtF rsegs RNG Q (LST 0x8093c RA a0' (Z_to_bv 64 i) a3' a4' a5' s2' s3' s4' s6' s9' t1' mk')) ->
  ExecF.evtF rsegs RNG Q (LST 0x8081c RA a0 (Z_to_bv 64 i) a3 a4 a5 s2 s3 s4 s6 s9 t1 mk).
Proof.
  intros i RA a0 a3 a4 a5 s2 s3 s4 s6 s9 t1 mk Hi HRA ((J3 & FRC) & MU & WM) K.
  unfold crwC_fr in FRC.
  assert (HV' : bytes_at rsegs mk (FR + 32) (PCR.le4s f)).
  { apply (crwC_bytes_tp m mk P1 (P1 + 88) _ _ MU); [|exact HV]. rewrite crwC_le4s_len. lia. }
  pose proof (crwC_le4s_read mk (FR + 32) f i HV' Hi) as HR. clear HV'.
  (* +0x228 `slli a0, a1, 2`, +0x22c `ld a3, 0x38(s1)` (v), +0x230 `add`, +0x234 `lw s2` (v[i]) *)
  step. rewrite (unsigned_lit i) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  step. step. step. clear HR.
  destruct HWNT as [G|G].
  - (* a declined read: +0x238 `beqz s11` taken, +0x340 `ld a0, 0x20(s1)` (the fill word), +0x344 `bne s2, a0` *)
    subst want. step. if_true.
    step. rewrite (HF0 eq_refl i Hi), PCR.sx32_lit by lia. step. crwC_f.
    apply K. split; [exists J3; unfold crwC_fr; exact FRC | split; assumption].
  - (* an accepted read *)
    subst want.
    destruct (HW eq_refl) as (W1 & W2 & W3 & W4).
    destruct (HCC eq_refl) as (HL & BB & AD & C0 & C1 & RC & RSC).
    pose proof (HNC eq_refl) as NCU. specialize (HRA eq_refl). subst RA.
    assert (SL : 0 <= slot - slot mod 2 <= W - 2) by (Z.div_mod_to_equations; lia).
    pose proof (crwC_mulb i W Hi ltac:(lia)) as IW.
    specialize (HA2 eq_refl). subst A2.
    step. if_false.
    (* +0x23c `sext.w a4, a1`, +0x240 `mul`, +0x244 `mulw`, +0x248 `bne` (UBSan, not taken) *)
    step. rewrite (unsigned_lit i), Z.add_0_r, (PCR.sw32 i) by lia.
    step. step. rewrite ?(unsigned_lit i), ?(unsigned_lit W) by lia. rewrite (PCR.sw32 (i * W)) by lia.
    step. crwC_f.
    (* +0x24c `sext.w a4, a0`, +0x250 `add a0, a4, a2`, +0x254 `addw a4, a4, a2`, +0x258 `bne` (UBSan, not taken) *)
    step. rewrite (unsigned_lit (i * W)), Z.add_0_r, (PCR.sw32 (i * W)) by lia.
    step. step. rewrite ?(unsigned_lit (i * W)), ?(unsigned_lit (slot - slot mod 2)) by lia.
    rewrite (PCR.sw32 (i * W + (slot - slot mod 2))) by lia.
    step. crwC_f.
    (* +0x25c `sext.w a0, a0`, +0x260 `slli a4, a0, 1`, +0x264 `add a0, a4, a0`, +0x268 `addi a0, a0, 50` *)
    step. rewrite (unsigned_lit (i * W + (slot - slot mod 2))), Z.add_0_r, (PCR.sw32 (i * W + (slot - slot mod 2))) by lia.
    step. rewrite (unsigned_lit (i * W + (slot - slot mod 2))) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. step.
    (* +0x26c `ld a3, 0x28(s1)` (~c), +0x270 `bltu a3, a0` (UBSan, not taken) *)
    step. step. crwC_f.
    (* +0x274 `mv s9, zero` .. +0x290 `not s4, a0` *)
    step. step. rewrite (unsigned_lit (slot - slot mod 2 + W * i)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    do 6 step.
    (* the sample's braid group G = c + 50 + 3 * (i * W + slot - slot mod 2) *)
    remember (c + ((i * W + (slot - slot mod 2)) * 2 + (i * W + (slot - slot mod 2)) + 50)) as G eqn:EG.
    assert (HG0 : c + 50 <= G) by (subst G; lia).
    assert (HG1 : G + 6 <= c + len) by (subst G; lia).
    setreg 6 (Z_to_bv 64 (G + 1)) ltac:(f_equal; subst G; lia).
    setreg 22 (Z_to_bv 64 (G - 50)) ltac:(f_equal; subst G; lia).
    setreg 20 (Z_to_bv 64 (18446744073709551615 - G))
      ltac:(rewrite (unsigned_lit G) by lia; rewrite zb_lxor_ones by lia; reflexivity).
    assert (BBk : bytes_at rsegs mk c bs) by (apply (crwC_bytes_tp m mk P1 (P1 + 88) _ _ MU); [lia | exact BB]).
    eapply (crwC_braid RNG) with (m := m) (bs := bs) (c := c) (len := len) (G := G); try eassumption; try lia.
    intros a0' a3' a4' a5' s3' mk' x FRC' MU' WM'.
    clear FRC MU WM BBk BB.
    assert (EAT : AT = 0 \/ AT = 3) by (subst AT; Z.div_mod_to_equations; lia).
    destruct EAT as [EAT|EAT]; rewrite EAT in HAT, K |- *.
    + (* slot even, at = 0: hi = be[0] = g[1], mid = be[1] = g[0], lo = be[2] = g[3] *)
      assert (P : slot mod 2 = 0) by lia.
      (* +0x300 .. +0x308 three `bltu t0, ...` (UBSan, not taken: be + 5 does not wrap) *)
      step. crwC_f. step. crwC_f. step. crwC_f.
      (* +0x30c .. +0x334 the 24-bit sample from be[at], be[at + 1], be[at + 2] *)
      do 11 step.
      rewrite crwC_wsamp_eq, (HF1 eq_refl i Hi).
      rewrite (PCR.rps bs W slot i (Z.to_nat (G - c + 3)) (Z.to_nat (G - c + 0)) (Z.to_nat (G - c + 1)))
        by (unfold PSR.braid_pos; cbv zeta; rewrite P; cbn [Z.eqb Pos.eqb]; f_equal; subst G; lia).
      unfold crwC_g.
      rewrite PCR.sx32_lit
        by (match goal with |- context [PCR.samp24 ?a ?b ?d] => pose proof (PCR.samp24_range a b d) end; lia).
      (* +0x338 `bne s2, a0` (not taken: v[i] is the sample), +0x33c `j` *)
      step. crwC_f. step.
      destruct (crwC_merge _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRC') as (J3' & FR3).
      apply K. split; [exists J3'; exact FR3 | split; assumption].
    + (* slot odd, at = 3: hi = be[3] = g[2], mid = be[4] = g[5], lo = be[5] = g[4] *)
      assert (P : slot mod 2 = 1) by lia.
      step. crwC_f. step. crwC_f. step. crwC_f.
      do 11 step.
      rewrite crwC_wsamp_eq, (HF1 eq_refl i Hi).
      rewrite (PCR.rps bs W slot i (Z.to_nat (G - c + 4)) (Z.to_nat (G - c + 5)) (Z.to_nat (G - c + 2)))
        by (unfold PSR.braid_pos; cbv zeta; rewrite P; cbn [Z.eqb Pos.eqb]; f_equal; subst G; lia).
      unfold crwC_g.
      rewrite PCR.sx32_lit
        by (match goal with |- context [PCR.samp24 ?a ?b ?d] => pose proof (PCR.samp24_range a b d) end; lia).
      step. crwC_f. step.
      destruct (crwC_merge _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRC') as (J3' & FR3).
      apply K. split; [exists J3'; exact FR3 | split; assumption].
Qed.

(* +0x228 .. +0x354: the samples i .. 11, then +0x358 (0x8094c). *)
Lemma crwC_loop : forall n i RA a0 a3 a4 a5 s2 s3 s4 s6 s9 t1 mk,
  Z.of_nat n = 12 - i -> 0 <= i < 12 ->
  (want = 1 -> RA = Z_to_bv 64 (slot - slot mod 2 + W * i)) -> crwC_linv mk ->
  (forall RA' a0' a1' a3' a4' a5' s2' s3' s4' s6' s9' t1' mk', crwC_linv mk' ->
     ExecF.evtF rsegs RNG Q (LST 0x8094c RA' a0' a1' a3' a4' a5' s2' s3' s4' s6' s9' t1' mk')) ->
  ExecF.evtF rsegs RNG Q (LST 0x8081c RA a0 (Z_to_bv 64 i) a3 a4 a5 s2 s3 s4 s6 s9 t1 mk).
Proof.
  induction n as [|n IH]; intros i RA a0 a3 a4 a5 s2 s3 s4 s6 s9 t1 mk Hn Hi HRA LI KX; [lia|].
  apply (crwC_body i RA a0 a3 a4 a5 s2 s3 s4 s6 s9 t1 mk Hi HRA LI).
  intros a0' a3' a4' a5' s2' s3' s4' s6' s9' t1' mk' LI'.
  (* +0x348 `addi a1, a1, 1`, +0x34c `addw ra, ra, s10`, +0x350 `addi a0, zero, 12`, +0x354 `bne a1, a0` *)
  step. step. step. step.
  destruct n as [|n].
  - crwC_f. apply KX. exact LI'.
  - crwC_t. apply (IH (i + 1)); [lia | lia | | exact LI' | exact KX].
    intros G. rewrite (HRA G). destruct (HW G) as (W1 & W2 & W3 & W4).
    assert (SL : 0 <= slot - slot mod 2 <= W - 2) by (Z.div_mod_to_equations; lia).
    pose proof (crwC_mulb i W Hi ltac:(lia)) as IW.
    rewrite (unsigned_lit (slot - slot mod 2 + W * i)), (unsigned_lit W) by lia.
    rewrite PCR.sw32 by lia. f_equal. lia.
Qed.

End crwC_L.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The epilogue, +0x358 (0x8094c) .. the `ret`: the frame's shadow over v set to 0xf8, the header retired
   (0x45e0360e), the `beqz a1` on the frame (not taken), the sixteen shadow bytes set to 0xf5, the flag byte cleared
   through the word at F + 0x78, the thirteen reloads and the `ret`. *)
Lemma crwC_epi :
  forall (RNG : ExecF.footprint)
         (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
          : word)
         (rae s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
         (F : bvmap 5 word) (fc : bv 32) (m mk : word -> option byte)
         (SP0 FR FL : Z) (Ja Jb Jh Js Jf : list byte),
    SP0 mod 16 = 0 -> 2 ^ 46 <= SP0 <= 2 ^ 47 ->
    4096 <= FR -> FR + 128 <= crw_sp1 SP0 -> crw_sh FR + 16 <= crw_sp1 SP0 ->
    (FR + 128 <= crw_sh FR \/ crw_sh FR + 16 <= FR) ->
    4096 <= FL -> FL + 1 <= crw_sp1 SP0 -> (FL + 1 <= FR \/ FR + 128 <= FL) ->
    (FL + 1 <= crw_sh FR \/ crw_sh FR + 16 <= FL) ->
    rw_cells rsegs mk (SP0 - 104)
      [C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
    rw_cells rsegs mk (crw_sp1 SP0)
      [CB 8 Ja; C8 (Z_to_bv 64 FR); C8 (Z_to_bv 64 (crw_sh FR)); C8 (Z_to_bv 64 FR); CB 56 Jb] ->
    rw_cells rsegs mk FR [CB 8 Jh] ->
    bytes_at rsegs mk (FR + 120) (le8 (Z_to_bv 64 FL)) ->
    rw_cells rsegs mk (crw_sh FR) [CB 16 Js] ->
    rw_cells rsegs mk FL [CB 1 Jf] ->
    ExecF.rng RNG (SP0 - 104) 104 -> ExecF.rng RNG (crw_sp1 SP0) 88 -> ExecF.rng RNG FR 128 ->
    ExecF.rng RNG (crw_sh FR) 16 -> ExecF.rng RNG FL 1 ->
    munch [(crw_sp1 SP0, crw_sp1 SP0 + 88)] m mk -> wmono rsegs m mk ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m4 : word -> option byte),
         ms' = MS (mkR rae (Z_to_bv 64 SP0) gp tp t0' t1' t2' s0e s1e a0' a1' a2' a3' a4' a5' a6' a7'
                    s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3' t4' t5' t6')
                  F (ret_pc rae) fc None m4 (seg_rom rsegs) /\
         munch [(crw_sp1 SP0, crw_sp1 SP0 + 88); (FR, FR + 8); (crw_sh FR, crw_sh FR + 16); (FL, FL + 1)] m m4 /\
         wmono rsegs m m4 /\
         bytes_at rsegs m4 FL [Z_to_bv 8 0])
      (MS (mkR x1 (Z_to_bv 64 (crw_sp1 SP0)) gp tp x5 x6 x7 (Z_to_bv 64 SP0) (Z_to_bv 64 (crw_sp1 SP0)) x10 x11 x12 x13
               x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8094c) fc None mk (seg_rom rsegs)).
Proof.
  intros RNG x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    rae s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m mk SP0 FR FL Ja Jb Jh Js Jf
    H16 HSP HF0 HF1 HS1 HFS HL0 HL1 HLF HLS SV SL FH FLB SHC FLC RSV RSL RFR RSH RFL MU WM.
  set (P1 := crw_sp1 SP0) in *.
  assert (HP1 : SP0 - 208 <= P1 <= SP0 - 192).
  { subst P1. unfold crw_sp1. pose proof (Z.div_mod (SP0 - 192) 32 ltac:(lia)).
    pose proof (Z.mod_pos_bound (SP0 - 192) 32 ltac:(lia)). lia. }
  set (SHA := crw_sh FR) in *.
  assert (HSH : 0 <= SHA) by (subst SHA; unfold crw_sh, ASAN_K; pose proof (Z.div_pos FR 8); lia).
  clearbody P1 SHA.
  (* the run's own footprint is kept apart from the loop's: the stores below are inside the four ranges *)
  pose (MUH := fun x => munch [(P1, P1 + 88)] m x).
  assert (MU0 : MUH mk) by exact MU. clear MU.
  pose proof (munch_refl [(P1, P1 + 88); (FR, FR + 8); (SHA, SHA + 16); (FL, FL + 1)] mk) as MU2.
  pose proof (wmono_refl rsegs mk) as WM2.
  (* +0x358 `addi a0, zero, -8`, +0x35c `ld a2, 0x10(s1)` (the shadow address), six `sb a0` (0xf8 over v) *)
  do 2 step.
  do 6 step.
  (* +0x378 .. +0x384 the retire magic 0x45e0360e at F, +0x388 `ld a1, 0x18(s1)` (F), +0x38c `beqz a1` *)
  do 2 step. step. step. step.
  step. rewrite (PCR.bveqb_lit FR 0) by lia. rewrite (proj2 (Z.eqb_neq FR 0)) by lia. cbv iota.
  (* +0x390 `addi a0, zero, -11`, sixteen `sb a0` (0xf5), +0x3d4 `ld a0, 0x78(a1)` (FL) *)
  do 17 step.
  lazymatch goal with H : bytes_at rsegs ?mm (FR + 120) _ |- _ =>
    assert (RD : ov_read_bytes rsegs mm (wa (FR + 120)) 8 = Some (le8 (Z_to_bv 64 FL)));
    [ replace (wa (FR + 120)) with (wa (FR + 120 + 0)) by (f_equal; lia);
      rewrite (bytes_at_read rsegs mm (FR + 120) _ 0 8 H ltac:(lia)) by (rewrite length_le8; lia); reflexivity | ] end.
  step. clear RD.
  (* +0x3d8 `sb zero, 0(a0)` (the flag byte), +0x3dc `j`, +0x420 `addi sp, s0, -0xc0`, the thirteen reloads,
     +0x458 `addi sp, sp, 0xc0`, +0x45c `ret` *)
  step.
  do 2 step.
  replace (SP0 - 104) with (SP0 + -104) in SV by lia.
  do 13 step.
  do 2 step.
  apply evtF_done. do 15 eexists. eexists. split; [|split; [|split]].
  - reflexivity.
  - unfold MUH in MU0. eapply munch_trans; [|exact MU2].
    eapply munch_weaken; [|exact MU0]. intros x Hx. cbn [outside] in *. tauto.
  - first [eassumption | eapply (wmono_trans rsegs); eassumption].
  - lazymatch goal with H : rw_cells rsegs _ FL _ |- _ => destruct H as [[_ HB] _] end.
    cbn [cells_bytes cbytes app] in HB. exact HB.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The segment. *)

Lemma crwC_sp1_facts : forall sp, 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 ->
  sp - 208 <= crw_sp1 sp <= sp - 192.
Proof.
  intros sp Hsp H16. unfold crw_sp1. pose proof (Z.div_mod (sp - 192) 32 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sp - 192) 32 ltac:(lia)). lia.
Qed.

Lemma crwC_want01 : forall len bs slot, crw_want len bs slot = 0 \/ crw_want len bs slot = 1.
Proof.
  intros len bs slot. unfold crw_want, PSR.rp_slot_read_model.
  destruct (PSW.rp_slot_width_model len bs slot <? 0); [left | right]; reflexivity.
Qed.

Lemma crw_segC_F : crw_segC_stmt.
Proof.
  unfold crw_segC_stmt.
  intros RNG ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 t3 t4 t5 t6
    rae s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m bs SP0 FR FL c len slot J0 J1 J2 J3 Jh Js Jf
    A16 HSP HF0 HF64 HFS HSS HFSH HFL0 HFL1 HFLF HFLS HLEN HSLOT SV FR1 FH FV F120 SH FLC
    RSV RFR RF RSH RFL HC.
  unfold CRW_RET1, ASAN_K.
  pose proof (crwC_sp1_facts SP0 HSP A16) as HP1.
  set (f := fun s => if crw_want len bs slot =? 1 then PSR.rp_sample bs (crw_W len) slot s else 1515870810).
  assert (HV : bytes_at rsegs m (FR + 32) (PCR.le4s f)).
  { unfold f. unfold crw_v in FV. destruct (crw_want len bs slot =? 1).
    - exact FV.
    - unfold crw_fill in FV. rewrite PCR.v0_le4s in FV. exact FV. }
  clear FV.
  (* the facts on the segment's start memory, kept away from the stores' transport *)
  pose proof (conj SV (conj FH (conj F120 (conj SH (conj FLC HV))))) as ORIG. clear SV FH F120 SH FLC HV.
  pose proof (munch_refl [(crw_sp1 SP0, crw_sp1 SP0 + 88)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold crw_slots in FR1.
  (* +0x1cc `bne a0, s11` (not taken), +0x1d0 .. +0x224 the set-up *)
  step. if_false.
  do 22 step.
  rewrite PCR.at_bits, (PCR.signed_lit slot) by lia.
  setreg 28 (Z_to_bv 64 (crw_sp1 SP0 + (82 + 3 * (slot mod 2)))) ltac:(f_equal; lia).
  setreg 31 (Z_to_bv 64 (crw_sp1 SP0 + (83 + 3 * (slot mod 2)))) ltac:(f_equal; lia).
  setreg 21 (Z_to_bv 64 (crw_sp1 SP0 + (84 + 3 * (slot mod 2)))) ltac:(f_equal; lia).
  assert (HWNT := crwC_want01 len bs slot).
  assert (HW : crw_want len bs slot = 1 ->
    2 <= crw_W len <= 40 /\ crw_W len mod 2 = 0 /\ 0 <= slot < crw_W len /\ 52 + 36 * crw_W len <= len).
  { intros G. unfold crw_want, PSR.rp_slot_read_model in G.
    destruct (Z.ltb_spec (PSW.rp_slot_width_model len bs slot) 0) as [L|L]; [discriminate G|].
    destruct (PCR.width_facts len bs slot HLEN L) as (W1 & W2 & W3 & W4 & W5).
    unfold crw_W. rewrite <- W5. lia. }
  assert (HFz : crw_want len bs slot = 0 -> forall i, 0 <= i < 12 -> f i = 1515870810).
  { intros G i _. unfold f. rewrite G. reflexivity. }
  assert (HFo : crw_want len bs slot = 1 -> forall i, 0 <= i < 12 -> f i = PSR.rp_sample bs (crw_W len) slot i).
  { intros G i _. unfold f. rewrite G. reflexivity. }
  assert (HA2 : crw_want len bs slot = 1 ->
    Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 slot)) 18446744073709551614) = Z_to_bv 64 (slot - slot mod 2)).
  { intros G. destruct (HW G) as (_ & _ & W3 & _).
    rewrite (unsigned_lit slot) by lia. rewrite PCR.land_m2 by lia. f_equal. Z.div_mod_to_equations. lia. }
  assert (HNC : crw_want len bs slot = 1 ->
    bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 c)) 18446744073709551615)) = 2 ^ 64 - 1 - c).
  { intros G. destruct (HC G) as (_ & _ & _ & C0 & C1 & _).
    rewrite (unsigned_lit c) by lia. rewrite zb_lxor_ones by lia. apply unsigned_lit. lia. }
  assert (HT0 : bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (crw_sp1 SP0 + 82))) 18446744073709551615))
                = 2 ^ 64 - 1 - (crw_sp1 SP0 + 82)).
  { rewrite (unsigned_lit (crw_sp1 SP0 + 82)) by lia. rewrite zb_lxor_ones by lia. apply unsigned_lit. lia. }
  assert (HP1' : 2 ^ 46 - 208 <= crw_sp1 SP0 /\ crw_sp1 SP0 + 88 <= 2 ^ 47) by lia.
  assert (HFR : 4096 <= FR /\ FR + 128 <= crw_sp1 SP0) by lia.
  destruct ORIG as (SV & FH & F120 & SH & FLC & HV).
  eapply crwC_loop with (n := 12%nat) (i := 0) (m := m) (bs := bs) (FR := FR) (c := c) (len := len) (slot := slot)
    (W := crw_W len) (want := crw_want len bs slot) (AT := 3 * (slot mod 2)) (J0 := J0) (J2 := J2) (f := f)
    (NC := Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 c)) 18446744073709551615)).
  all: try eassumption.
  all: try reflexivity.
  all: try lia.
  - intros G. destruct (HW G) as (_ & _ & W3 & _). rewrite Z.mul_0_r, Z.add_0_r.
    exact (HA2 G).
  - split; [exists J3; unfold crwC_fr; exact FR1 | split; assumption].
  - intros RA' a0' a1' a3' a4' a5' s2' s3' s4' s6' s9' t1' mk' ((J3' & FRk) & MUk & WMk).
    unfold crwC_fr in FRk.
    pose proof (rw_cells_merge rsegs mk' (crw_sp1 SP0)
      [CB 8 J0; C8 (Z_to_bv 64 FR); C8 (Z_to_bv 64 (crw_sh FR)); C8 (Z_to_bv 64 FR)]
      [C8 (Z_to_bv 64 1515870810); C8 (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 c)) 18446744073709551615));
       C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 (FR + 32)); CB 8 J2; C8 (Z_to_bv 64 FR); CB 8 J3'] [] FRk) as FRm.
    cbn [app cells_size csize Nat.add] in FRm.
    assert (Hsh : 0 <= crw_sh FR) by (unfold crw_sh, ASAN_K; pose proof (Z.div_pos FR 8); lia).
    pose proof (rw_cells_transport rsegs _ _ _ _ _ SV MUk WMk
                  ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I])) as SVk.
    pose proof (rw_cells_transport rsegs _ _ _ _ _ FH MUk WMk
                  ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I])) as FHk.
    pose proof (rw_cells_transport rsegs _ _ _ _ _ SH MUk WMk
                  ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I])) as SHk.
    pose proof (rw_cells_transport rsegs _ _ _ _ _ FLC MUk WMk
                  ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I])) as FLk.
    pose proof (bytes_at_transport rsegs _ _ _ _ _ F120 MUk
                  ltac:(cbn [disjoint_from]; rewrite length_le8; split; [lia | exact I])) as F120k.
    eapply crwC_epi; eassumption.
Qed.
