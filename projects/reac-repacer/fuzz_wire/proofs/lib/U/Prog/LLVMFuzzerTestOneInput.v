(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The harness-body walk of LLVMFuzzerTestOneInput, fuzz_wire.c:253-282 (projects/reac-repacer/fuzz_wire/source), on
   the UBSan image fuzz_wire ubsan 6e91fe0b5555: entry 0x12dc0, frame 0x40 bytes (ra, s0..s6 only), 95 instructions
   (0x12dc0..0x12f38). For 1 <= size < 2^26 it walks the 92 instructions 0x12dc0..0x12f2c, both arms of the
   size - 1 < 1600, n = 0 and len = 0 tests; size = 0 or size >= 2^26 is lib/U/Prog/LLVMFuzzerTestOneInput_early.v's
   llvm_early. The three instructions left are dead: the `unimp` at 0x12f30 (the UBSan trap), the `jal abort` at
   0x12f34 (fuzz_dup's `if (!b) abort();`) and the `unimp` at 0x12f38 after that call, which does not return. Every
   branch to them is refuted:
   - 0x12df8 `beqz a0` (data NULL) and 0x12e00 `beq s4, -1` (data + 1 wraps), to 0x12f30: size >= 1, so lib_pre
     makes data the driver's payload block (f_pay: 4096 <= data, data + size <= alloc_ceiling < 2^64 - 1).
   - 0x12e2c and 0x12eb4 `beqz a0` after the two mallocs, to 0x12f34: malloc_contract's result is a fresh block at or
     above 4096 (malloc_ret; the fact lib/U/Prog/FuzzDup.v's fuzz_dup_no_null states).
   The callees and their premises at each call:
   - malloc (0x12e28, 0x12eb0) for fuzz_dup's malloc(n ? n : 1): the room of llvm_room (lf_room), then a block the
     entry blocks are disjoint from (blocks pairwise disjoint, blocks_nodup).
   - memcpy (0x12e50, 0x12ecc), unless n = 0: the fresh block as cells (norm_blk), the source in another block.
   - check_forward .. check_counter (0x12e60-0x12e90, chk_shape / chk_call): f readable for its n bytes, f <> 0, f
     below the stack window, sp 16-aligned; check_width (0x12e98): n <= 1600 and mem_inv, which the five checks before
     it do not state in their posts: they write only stack bytes above the image (mem_inv_hi).
   - check_read (0x12ea8 on f; 0x12ef0 on c with len = copy_untag_result n bs <= n, got_le, and c's first len bytes,
     bytes_at_mid).
   - check_copy (0x12edc), the one SR callee besides malloc / free: its post is call_post_x (c's bytes released);
     lf_fr_call_x / g_above_x carry the frame across it.
   - free (0x12ef8, 0x12f00): c and f are blocks of the state, outside the entry blocks; the budget returns to b
     (sb_free_malloc).
   The SR level is libreac/fuzz_decode's released fd_glue.v / fd_seghelp.v / fd_exit.v glue (recipes 25e3d17bdb5)
   over this unit's lf_fr (lib/U/Prog/LLVMFuzzerTestOneInput_fr.v), in the shape of reac-repacer/fuzz_uci's
   lib/U/Prog/LLVMFuzzerTestOneInput.v (6874bc78b1f).
   rule 24: proves function LLVMFuzzerTestOneInput (reuse search: the released recipes and candidates, the lemma
   index, the live heads): the released LLVMFuzzerTestOneInput proofs are other programs' entries; written new on
   these templates. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import memcpy_c check_forward_c check_ret_c
  check_downstream_c check_meter_c check_counter_c check_width_c check_read_c rp_copy_untag_c FuzzDup check_copy_c
  FrameBytes cc_segs cc_glue LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_early.
Import ListNotations.
Open Scope Z_scope.

(* the frame of LLVMFuzzerTestOneInput at Sp = entry sp - 0x40: the eight saved registers, s6 at Sp .. ra at Sp + 0x38 *)
Definition lsv (ra s0 s1 s2 s3 s4 s5 s6 : word) : list cell :=
  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* n = size - 1, cut to W_RECV_MAX = 1600 (fuzz_wire.c:259-262) *)
Definition nclamp (size : Z) : Z := Z.min (size - 1) 1600.

Lemma nclamp_range : forall size, 1 <= size -> 0 <= nclamp size <= 1600 /\ nclamp size <= size - 1 /\
  (nclamp size = 0 <-> size - 1 = 0).
Proof. intros size H. unfold nclamp. lia. Qed.

Lemma fds_ge : forall n, 0 <= n -> n <= fuzz_dup_size n /\ (0 < n -> fuzz_dup_size n = n).
Proof. intros n H. unfold fuzz_dup_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma en_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x NO. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply NO; cbn [outside]; (split; [lia | exact I]).
Qed.

(* mem_inv survives a write whose window lies above the image: no segment is at or above 0x50000 (cu_noseg). The
   checks check_forward .. check_counter state no mem_inv in their posts; check_width and check_read want it. *)
Lemma mem_inv_hi : forall m m' W, mem_inv rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> 0x50000 <= x) -> mem_inv rsegs m'.
Proof.
  intros m m' W MI MU HW a b E.
  destruct (lf_outside_dec W (bv_unsigned a)) as [O|NO].
  - rewrite (MU a O) in E. exact (MI a b E).
  - pose proof (HW _ (u64_range a) NO) as H. unfold Mem.ro_addr. rewrite (cu_noseg _ H). reflexivity.
Qed.

(* the common shape of check_forward, check_ret, check_downstream, check_meter and check_counter (their *_c.v), for
   a caller whose sp is 16-aligned *)
Definition chk_shape (pc frame : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    Z.of_nat (length bs) = bv_unsigned a1 -> bytes_at rsegs m (bv_unsigned a0) bs -> bv_unsigned a0 <> 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + frame <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - frame \/ bv_unsigned sp <= bv_unsigned a0 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - frame, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma cf_shape : check_forward_contract -> chk_shape CHECK_FORWARD CHECK_FORWARD_FRAME.
Proof. unfold check_forward_contract, chk_shape. intros H. intros. eapply H; eassumption. Qed.
Lemma cr_shape : check_ret_contract -> chk_shape CHECK_RET CHECK_RET_FRAME.
Proof. unfold check_ret_contract, chk_shape. intros H. intros. eapply H; eassumption. Qed.
Lemma cd_shape : check_downstream_contract -> chk_shape CHECK_DOWNSTREAM CHECK_DOWNSTREAM_FRAME.
Proof. unfold check_downstream_contract, chk_shape. intros H. intros. eapply H; eassumption. Qed.
Lemma cm_shape : check_meter_contract -> chk_shape CHECK_METER CHECK_METER_FRAME.
Proof.
  unfold check_meter_contract, chk_shape. intros H. intros. eapply H; try eassumption. Z.div_mod_to_equations. lia.
Qed.
Lemma cn_shape : check_counter_contract -> chk_shape CHECK_COUNTER CHECK_COUNTER_FRAME.
Proof. unfold check_counter_contract, chk_shape. intros H. intros. eapply H; eassumption. Qed.

(* one call of such a check on f (n bytes, a heap block below the stack window [lo, sp)): what the caller keeps *)
Lemma chk_call : forall pc frame (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (W : list (Z * Z)) (lo f n : Z) (bs : list byte)
    (cs : list cell),
  chk_shape pc frame ->
  munch W m0 m -> wmono rsegs m0 m -> bytes_at rsegs m f bs -> stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp) cs ->
  0 <= frame -> lo + frame <= bv_unsigned sp -> 0x50000 <= lo -> bv_unsigned sp mod 16 = 0 ->
  4096 <= f -> f + n <= lo -> Z.of_nat (length bs) = n ->
  (forall x, outside W x -> outside [(lo, bv_unsigned sp)] x) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch W m0 m' -> wmono rsegs m0 m' -> bytes_at rsegs m' f bs -> stk rsegs m' lo (bv_unsigned sp) ->
     mem_inv rsegs m' -> rw_cells rsegs m' (bv_unsigned sp) cs ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros pc frame Q ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m W lo f n bs cs SH MU WM BF ST MI FR HF0 HLF HLO HAL HF HFL HN HW K.
  pose proof (u64_range sp) as Rsp. pose proof (rw_cells_bound _ _ _ _ FR) as FRB.
  pose proof (bytes_at_bound _ _ _ _ BF) as BFB.
  eapply evt_cut.
  { apply (SH ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             s11 t3 t4 t5 t6 F fc m bs lo); rewrite ?(unsigned_lit f), ?(unsigned_lit n) by lia; first [assumption | lia]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
    MU1 & WM1 & ST1).
  apply K.
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU1].
    intros x Hx. destruct (HW x Hx) as [H _]. cbn [outside]. split; [lia | exact I].
  - exact (wmono_trans _ _ _ _ WM WM1).
  - eapply bytes_at_transport; [exact BF | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I].
  - exact ST1.
  - eapply mem_inv_hi; [exact MI | exact MU1 |]. intros x Hx NO. apply en_out1 in NO. lia.
  - eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 |]. cbn [disjoint_from]. split; [lia | exact I].
Qed.

(* ---- the instruction segments (evt level) ---- *)

(* the size test at 0x12df0 (`bltu a3, a2` with a3 = size - 2^26, a2 = 2^64 - 2^26 + 1) is not taken for
   1 <= size < 2^26 *)
Lemma e1_cond : forall size, 1 <= size < 2 ^ 26 ->
  bv_ltu (Z_to_bv 64 (size + -67108864)) (Z_to_bv 64 (-67108863)) = false.
Proof.
  intros size Hs. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

(* 0x12dc0-0x12e28: the prologue, the size test (lui / add / addiw / bltu at 0x12de4-0x12df0: taken iff size = 0 or
   size >= 2^26, lib/U/Prog/LLVMFuzzerTestOneInput_early.v's arm, so not taken here), the two UBSan checks on data,
   both to the unimp at 0x12f30 and neither taken: 0x12df8 `beqz a0` (data NULL) and 0x12e00 `beq s4, -1` (data + 1
   wraps): size >= 1 makes data the driver's payload block, in [4096, alloc_ceiling); then n, data[0], fuzz_dup's
   malloc(n ? n : 1) *)
Definition e1_post (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m : word -> option byte) (size p : Z) (b0 : byte) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 0x12e2c) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (nclamp size))
               (Z_to_bv 64 (fuzz_dup_size (nclamp size))) a1 a2 a3 a4 a5 a6 a7 (zxb b0)
               (Z_to_bv 64 (fuzz_dup_size (nclamp size))) (Z_to_bv 64 p) s5 (Z_to_bv 64 (size - 1))
               s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14898) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' (bv_unsigned sp - 64) (lsv ra s0 s1 s2 s3 s4 s5 s6).

Lemma e1_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p size : Z) (pl : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> mem_inv rsegs m ->
    1 <= size < 2 ^ 26 -> size = Z.of_nat (length pl) ->
    bytes_at rsegs m p pl -> 4096 <= p -> p + size <= lo ->
    evt rsegs (e1_post F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m size p (nth 0 pl (Z_to_bv 8 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
               s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12dc0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p size pl ST LO MI HS Hlen HP HP0 HPL.
  pose proof (u64_range sp) as Rsp.
  pose proof (bytes_at_bound _ _ _ _ HP) as HPB.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  do 13 step.
  take_false ltac:(apply e1_cond; lia).
  do 2 step.
  take_false ltac:(bvc).
  do 2 step.
  take_false ltac:(bvc).
  do 4 step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (R0 : ov_read_bytes rsegs mm (wa (p + Z.of_nat 0)) 1 = Some [nth 0 pl (Z_to_bv 8 0)])
      by (apply rd1; [assumption | lia]) end.
  rewrite Z.add_0_r in R0.
  destruct (Z.ltb_spec (size - 1) 1600) as [Hc|Hc].
  - take_true ltac:(bvc).
    do 5 step.
    rewrite (fds_eq (size + -1)) by lia.
    assert (Ec : nclamp size = size + -1) by (unfold nclamp; lia).
    unfold e1_post. rewrite Ec.
    finish.
  - take_false ltac:(bvc).
    do 6 step.
    rewrite (fds_eq 1600) by lia.
    assert (Ec : nclamp size = 1600) by (unfold nclamp; lia).
    unfold e1_post. rewrite Ec.
    finish.
Qed.

(* 0x12efc-0x12f00: free(f) *)
Lemma e5_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x12f04) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x14758) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12efc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step. apply evt_done. reflexivity.
Qed.

(* 0x12f04-0x12f2c: the return value 0, the epilogue (the eight saved registers reloaded from the frame) and ret *)
Lemma e6_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (vra v0 v1 v2 v3 v4 v5 v6 : word),
    rw_cells rsegs m (bv_unsigned sp) (lsv vra v0 v1 v2 v3 v4 v5 v6) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 v0 v1 (Z_to_bv 64 0) a1 a2 a3
                               a4 a5 a6 a7 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f04) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    vra v0 v1 v2 v3 v4 v5 v6 FR.
  pose proof (u64_range sp) as Rsp. unfold lsv in FR.
  do 11 step.
  apply evt_done. reflexivity.
Qed.

(* the call of one check of chk_shape at the pc it jumps to, then the caller's facts back under the same names *)
Ltac chk_go SH FRM HW MU WM BF ST MI FR :=
  eapply (chk_call _ FRM); [exact SH | exact MU | exact WM | exact BF | exact ST | exact MI | exact FR
    | unfold FRM; lia | unfold FRM; lia | assumption | assumption | assumption | lia | assumption | exact HW |];
  clear MU WM BF ST MI FR; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU WM BF ST MI FR;
  rewrite ret_pc_even by first [lia | reflexivity].

(* 0x12e2c-0x12eb0: fuzz_dup's NULL test on malloc's result (0x12e2c `beqz a0` to the `jal abort` at 0x12f34: not
   taken, malloc returns a block at or above 4096), bcast and slot from data[0], memcpy(f, data + 1, n) unless n = 0,
   the five checks check_forward .. check_counter on (f, n), check_width(n), check_read(f, n, slot), then fuzz_dup's
   malloc(n ? n : 1) for c *)
Section E2.
Variables (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (lo f p size : Z) (src : list byte) (cs : list cell).
Hypothesis CF : check_forward_contract.
Hypothesis CR : check_ret_contract.
Hypothesis CD : check_downstream_contract.
Hypothesis CM : check_meter_contract.
Hypothesis CN : check_counter_contract.
Hypothesis CW : check_width_contract.
Hypothesis CRD : check_read_contract.
Hypothesis MC : memcpy_contract.
Hypothesis HS : 1 <= size < 2 ^ 26.
Hypothesis HLO : 0x50000 <= lo.
Hypothesis HSP : lo + 272 <= bv_unsigned sp.
Hypothesis HAL : bv_unsigned sp mod 16 = 0.
Hypothesis HF : 4096 <= f.
Hypothesis HFL : f + fuzz_dup_size (nclamp size) <= lo.
Hypothesis HL : Z.of_nat (length src) = nclamp size.
Hypothesis HCS : cells_size cs = 64%nat.

Definition e2_post (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 slot bit : word) (m' : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 0x12eb4) sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 (nclamp size))
               (Z_to_bv 64 (fuzz_dup_size (nclamp size))) a1 a2 a3 a4 a5 a6 a7 slot
               (Z_to_bv 64 (fuzz_dup_size (nclamp size))) (Z_to_bv 64 p) bit (Z_to_bv 64 (size - 1))
               s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14898) fc None m' (seg_rom rsegs) /\
    munch [(lo, bv_unsigned sp); (f, f + nclamp size)] m0 m' /\ wmono rsegs m0 m' /\
    bytes_at rsegs m' f src /\ rw_cells rsegs m' (bv_unsigned sp) cs.

(* 0x12e54-0x12eb0 *)
Lemma e2b : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 slot bit x28 x29 x30 x31 : word) m,
  munch [(lo, bv_unsigned sp); (f, f + nclamp size)] m0 m -> wmono rsegs m0 m -> bytes_at rsegs m f src ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m -> rw_cells rsegs m (bv_unsigned sp) cs ->
  evt rsegs e2_post
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 (nclamp size)) x10 x11 x12 x13 x14 x15 x16 x17 slot
             (Z_to_bv 64 (fuzz_dup_size (nclamp size))) (Z_to_bv 64 p) bit (Z_to_bv 64 (size - 1))
             s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12e54) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 slot bit x28 x29 x30 x31 m MU WM BF ST MI FR.
  pose proof (u64_range sp) as Rsp. destruct (nclamp_range size ltac:(lia)) as (N1 & N2 & N3).
  pose proof (fuzz_dup_size_range (nclamp size) ltac:(lia)) as [D1 D2].
  pose proof (fds_ge (nclamp size) ltac:(lia)) as D3.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. rewrite HCS in FRB.
  assert (HW : forall x, outside [(lo, bv_unsigned sp); (f, f + nclamp size)] x -> outside [(lo, bv_unsigned sp)] x)
    by (intros x [H1 _]; split; [exact H1 | exact I]).
  do 4 step. chk_go (cf_shape CF) CHECK_FORWARD_FRAME HW MU WM BF ST MI FR.
  do 3 step. chk_go (cr_shape CR) CHECK_RET_FRAME HW MU WM BF ST MI FR.
  do 3 step. chk_go (cd_shape CD) CHECK_DOWNSTREAM_FRAME HW MU WM BF ST MI FR.
  do 3 step. chk_go (cm_shape CM) CHECK_METER_FRAME HW MU WM BF ST MI FR.
  do 3 step. chk_go (cn_shape CN) CHECK_COUNTER_FRAME HW MU WM BF ST MI FR.
  (* 0x12e94-0x12e98: check_width(n) *)
  do 2 step.
  eapply evt_cut.
  { eapply CW with (lo := lo); [rewrite unsigned_lit by lia; lia | exact MI | exact ST
      | unfold CHECK_WIDTH_STACK, CHECK_WIDTH_FRAME; lia]. }
  intros ms' (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & mw & -> &
    MU1 & WM1 & MI1 & ST1).
  rewrite ret_pc_even by first [lia | reflexivity].
  assert (MU2 : munch [(lo, bv_unsigned sp); (f, f + nclamp size)] m0 mw).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU1].
    intros x [H _]. cbn [outside]. unfold CHECK_WIDTH_STACK, CHECK_WIDTH_FRAME. split; [lia | exact I]. }
  pose proof (bytes_at_transport rsegs _ _ _ _ _ BF MU1
    ltac:(cbn [disjoint_from]; unfold CHECK_WIDTH_STACK, CHECK_WIDTH_FRAME; rewrite HL; split; [lia | exact I])) as BF2.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU1 WM1
    ltac:(cbn [disjoint_from]; rewrite HCS; split; [lia | exact I])) as FR2.
  pose proof (wmono_trans _ _ _ _ WM WM1) as WM2.
  clear MU WM BF ST MI FR MU1 WM1.
  (* 0x12e9c-0x12ea8: check_read(f, n, slot) *)
  do 4 step.
  eapply evt_cut.
  { eapply CRD with (lo := lo) (bs := src);
      rewrite ?(unsigned_lit f), ?(unsigned_lit (nclamp size)) by lia;
      first [assumption | unfold CHECK_READ_STACK; lia | lia]. }
  intros ms' (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & mr & -> &
    MU3 & WM3 & MI3 & ST3).
  rewrite ret_pc_even by first [lia | reflexivity].
  (* 0x12eac-0x12eb0: malloc(n ? n : 1) *)
  do 2 step.
  apply evt_done. unfold e2_post. do 17 eexists. split; [reflexivity|].
  split.
  { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [|exact MU3].
    intros x [H _]. cbn [outside]. unfold CHECK_READ_STACK. split; [lia | exact I]. }
  split; [exact (wmono_trans _ _ _ _ WM2 WM3)|].
  split.
  { eapply bytes_at_transport; [exact BF2 | exact MU3 |].
    cbn [disjoint_from]. unfold CHECK_READ_STACK. rewrite HL. split; [lia | exact I]. }
  eapply rw_cells_transport; [exact FR2 | exact MU3 | exact WM3 |].
  cbn [disjoint_from]. rewrite HCS. split; [lia | exact I].
Qed.

(* 0x12e2c-0x12e50 *)
Lemma e2_evt : forall (x1 x5 x6 x7 s0 x11 x12 x13 x14 x15 x16 x17 s5 x28 x29 x30 x31 : word) (b0 : byte)
    (junk : list byte),
  stk rsegs m0 lo (bv_unsigned sp) -> mem_inv rsegs m0 -> rw_cells rsegs m0 (bv_unsigned sp) cs ->
  bytes_at rsegs m0 (p + 1) src -> 0 <= p -> p + 1 + nclamp size <= f \/ f + nclamp size <= p + 1 ->
  (0 < nclamp size -> rw_cells rsegs m0 f [CB (Z.to_nat (nclamp size)) junk]) ->
  evt rsegs e2_post
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 (Z_to_bv 64 (nclamp size)) (Z_to_bv 64 f) x11 x12 x13 x14 x15 x16 x17 (zxb b0)
             (Z_to_bv 64 (fuzz_dup_size (nclamp size))) (Z_to_bv 64 p) s5 (Z_to_bv 64 (size - 1))
             s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12e2c) fc None m0 (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 s0 x11 x12 x13 x14 x15 x16 x17 s5 x28 x29 x30 x31 b0 junk ST MI FR BS HP0 DJ JK.
  pose proof (u64_range sp) as Rsp. destruct (nclamp_range size ltac:(lia)) as (N1 & N2 & N3).
  pose proof (fuzz_dup_size_range (nclamp size) ltac:(lia)) as [D1 D2].
  pose proof (fds_ge (nclamp size) ltac:(lia)) as D3.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. rewrite HCS in FRB.
  pose proof (bytes_at_bound _ _ _ _ BS) as BSB. rewrite HL in BSB.
  step. take_false ltac:(bvc).
  do 5 step.
  destruct (Z.eq_dec (size - 1) 0) as [Z0|Z0].
  - take_true ltac:(bvc).
    assert (E0 : nclamp size = 0) by (unfold nclamp; lia).
    assert (BF : bytes_at rsegs m0 f src).
    { destruct src as [|x src']; [|cbn [length] in HL; lia].
      split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. }
    eapply e2b; [apply munch_refl | apply wmono_refl | exact BF | exact ST | exact MI | exact FR].
  - take_false ltac:(bvc).
    do 4 step.
    eapply evt_cut.
    { eapply MC with (src := src) (junk := junk);
        rewrite ?(unsigned_lit f), ?(unsigned_lit (p + 1)), ?(unsigned_lit (nclamp size)) by lia.
      - exact BS.
      - lia.
      - apply JK. lia.
      - lia.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
      MU1 & WM1 & MI1 & WF1 & BS1).
    rewrite !(unsigned_lit f), !(unsigned_lit (nclamp size)) in * by lia.
    rewrite ret_pc_even by first [lia | reflexivity].
    eapply e2b.
    + eapply munch_weaken; [|exact MU1]. intros x [_ [H _]]. cbn [outside]. split; [exact H | exact I].
    + exact WM1.
    + exact (rw1_bytes _ _ _ _ WF1).
    + eapply stk_transport_disjoint; [exact ST | exact MU1 | exact WM1 |]. cbn [disjoint_from]. split; [lia | exact I].
    + exact MI1.
    + eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 |].
      cbn [disjoint_from]. rewrite HCS. split; [lia | exact I].
Qed.

End E2.

(* 0x12eb4-0x12edc: fuzz_dup's NULL test on the second malloc's result (0x12eb4 `beqz a0` to the `jal abort` at
   0x12f34: not taken), memcpy(c, f, n) unless n = 0, then the call check_copy(c, f, n) *)
Definition e3_post (F : bvmap 5 word) (fc : bv 32) (sp gp tp s2 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m0 : word -> option byte) (c f n : Z) (src : list byte) (cs : list cell) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 0x12ee0) sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 c) (Z_to_bv 64 f)
               (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 c) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x13550) fc None m' (seg_rom rsegs) /\
    munch [(c, c + n)] m0 m' /\ wmono rsegs m0 m' /\ bytes_at rsegs m' c src /\ bytes_at rsegs m' f src /\
    rw_cells rsegs m' (bv_unsigned sp) cs.

Lemma e3_evt : memcpy_contract ->
  forall (x1 sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (c f size : Z) (src junk : list byte)
         (cs : list cell),
    1 <= size < 2 ^ 26 -> Z.of_nat (length src) = nclamp size -> 4096 <= c -> c + nclamp size <= bv_unsigned sp ->
    0 <= f -> f + nclamp size <= c \/ c + nclamp size <= f -> mem_inv rsegs m0 ->
    bytes_at rsegs m0 f src -> (0 < nclamp size -> rw_cells rsegs m0 c [CB (Z.to_nat (nclamp size)) junk]) ->
    rw_cells rsegs m0 (bv_unsigned sp) cs ->
    evt rsegs (e3_post F fc sp gp tp s2 s4 s5 (Z_to_bv 64 (size - 1)) s7 s8 s9 s10 s11 m0 c f (nclamp size) src cs)
      (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 (nclamp size)) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16
               x17 s2 s3 s4 s5 (Z_to_bv 64 (size - 1)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12eb4) fc None m0 (seg_rom rsegs)).
Proof.
  intros MC x1 sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m0
    c f size src junk cs HS HL HC HCS HF DJ MI BF JK FR.
  pose proof (u64_range sp) as Rsp. destruct (nclamp_range size ltac:(lia)) as (N1 & N2 & N3).
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB.
  pose proof (bytes_at_bound _ _ _ _ BF) as BFB. rewrite HL in BFB.
  step. take_false ltac:(bvc).
  do 2 step.
  destruct (Z.eq_dec (size - 1) 0) as [Z0|Z0].
  - take_true ltac:(bvc).
    assert (E0 : nclamp size = 0) by (unfold nclamp; lia).
    assert (BC : bytes_at rsegs m0 c src).
    { destruct src as [|x src']; [|cbn [length] in HL; lia].
      split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. }
    do 4 step.
    apply evt_done. unfold e3_post. do 13 eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact BC|]. split; [exact BF | exact FR].
  - take_false ltac:(bvc).
    do 4 step.
    eapply evt_cut.
    { eapply MC with (src := src) (junk := junk);
        rewrite ?(unsigned_lit f), ?(unsigned_lit c), ?(unsigned_lit (nclamp size)) by lia.
      - exact BF.
      - lia.
      - apply JK. lia.
      - lia.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
      MU1 & WM1 & MI1 & WC1 & BF1).
    rewrite !(unsigned_lit f), !(unsigned_lit c), !(unsigned_lit (nclamp size)) in * by lia.
    rewrite ret_pc_even by first [lia | reflexivity].
    do 4 step.
    apply evt_done. unfold e3_post. do 13 eexists. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact (rw1_bytes _ _ _ _ WC1)|]. split; [exact BF1|].
    eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 |].
    cbn [disjoint_from]. split; [lia | exact I].
Qed.

(* 0x12ee0-0x12ef8: `if (len) check_read(c, len, slot)`, then free(c) *)
Definition e4_post (F : bvmap 5 word) (fc : bv 32) (sp gp tp s0 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m0 : word -> option byte) (lo c : Z) (cs : list cell) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 0x12efc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 c)
               s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14758) fc None m' (seg_rom rsegs) /\
    munch [(lo, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' (bv_unsigned sp) cs.

Lemma e4_evt : check_read_contract ->
  forall (x1 sp gp tp x5 x6 x7 s0 s1 x11 x12 x13 x14 x15 x16 x17 s2 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (lo c len : Z) (bs : list byte) (cs : list cell),
    0x50000 <= lo -> lo + 272 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 -> 0 <= len <= 1600 ->
    4096 <= c -> c + len <= lo -> Z.of_nat (length bs) = len ->
    mem_inv rsegs m0 -> stk rsegs m0 lo (bv_unsigned sp) -> bytes_at rsegs m0 c bs ->
    rw_cells rsegs m0 (bv_unsigned sp) cs -> (cells_size cs = 64)%nat ->
    evt rsegs (e4_post F fc sp gp tp s0 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 m0 lo c cs)
      (MS (mkR x1 sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 s2 (Z_to_bv 64 c) s4 s5 s6
               s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12ee0) fc None m0 (seg_rom rsegs)).
Proof.
  intros CRD x1 sp gp tp x5 x6 x7 s0 s1 x11 x12 x13 x14 x15 x16 x17 s2 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc
    m0 lo c len bs cs HLO HSP HAL HLEN HC HCL HL MI ST BC FR HCS.
  pose proof (u64_range sp) as Rsp. pose proof (rw_cells_bound _ _ _ _ FR) as FRB. rewrite HCS in FRB.
  step.
  destruct (Z.eq_dec len 0) as [L0|L0].
  - take_true ltac:(bvc).
    do 2 step.
    apply evt_done. unfold e4_post. do 15 eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl | exact FR].
  - take_false ltac:(bvc).
    do 4 step.
    eapply evt_cut.
    { eapply CRD with (lo := lo) (bs := bs);
        rewrite ?(unsigned_lit c), ?(unsigned_lit len) by lia;
        first [assumption | unfold CHECK_READ_STACK; lia | lia]. }
    intros ms' (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m1 & -> &
      MU1 & WM1 & MI1 & ST1).
    rewrite ret_pc_even by first [lia | reflexivity].
    do 2 step.
    apply evt_done. unfold e4_post. do 15 eexists. split; [reflexivity|].
    split.
    { eapply munch_weaken; [|exact MU1]. intros x [H _]. cbn [outside]. unfold CHECK_READ_STACK.
      split; [lia | exact I]. }
    split; [exact WM1|].
    eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 |].
    cbn [disjoint_from]. rewrite HCS. split; [lia | exact I].
Qed.

(* ---- the SR level: libreac/fuzz_decode's released fd_glue.v / fd_seghelp.v glue (g_pre, g_above, g_run,
   g_malloc, g_free, norm_stk, norm_blk, blk_keep: their text over this unit's lf_fr), and g_cc for check_copy, the
   one SR callee, whose post is call_post_x (lib/U/Prog/check_copy_c.v) ---- *)

Lemma lf_rw_cells_frame : forall m m' A cs,
  rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) ->
     mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (H0 & H1 & Hb)] (W0 & W1 & Hw)] HE.
  rewrite cells_bytes_length in H1 by exact Hwf.
  split; [split; [exact Hwf|] |].
  - split; [exact H0|]. split; [rewrite cells_bytes_length by exact Hwf; exact H1|].
    intros i Hi. rewrite <- (Hb i Hi). rewrite cells_bytes_length in Hi by exact Hwf.
    change (mrd rsegs m' (wa (A + Z.of_nat i)) = mrd rsegs m (wa (A + Z.of_nat i))).
    exact (proj1 (HE (A + Z.of_nat i) ltac:(lia))).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    apply (proj1 (proj2 (HE (A + i) ltac:(lia)))). exact (Hw i Hi).
Qed.

Lemma blk_bytes_at : forall B m A bs, ms_segs B = rsegs -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  blk_data B m A bs -> bytes_at rsegs m A bs.
Proof.
  intros B m A bs HS H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, HS. reflexivity.
Qed.

Lemma bytes_at_blk : forall B m A bs, ms_segs B = rsegs -> bytes_at rsegs m A bs -> blk_data B m A bs.
Proof.
  intros B m A bs HS (H0 & H1 & Hb) i Hi. rewrite HS.
  pose proof (Hb (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. exact E.
Qed.

Lemma disj_mid : forall b1 x b2 y, pairwise ranges_disjoint (b1 ++ x :: b2) -> In y (b1 ++ b2) ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros b1 x b2 y HP Hin. destruct (pairwise_app_mid _ b1 x b2 y HP Hin) as [H|H];
    unfold ranges_disjoint in H; lia.
Qed.

Lemma lf_callee_cases : forall x, callee_saved x ->
  x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ x = 9 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/
  x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27.
Proof. intros x Hx. unfold callee_saved in Hx. lia. Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis HGG : ms_got_guard B = LLVM_GUARD_GOT.
Hypothesis HMAL : ms_malloc B = LLVM_MALLOC.
Hypothesis HFRE : ms_free B = LLVM_FREE.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.

Lemma blk_keep : forall stk Sw L A mem md LX AXX memX mdX x bs,
  lf_fr B API stk Sw L A mem md LX AXX memX mdX -> In (x, Z.of_nat (length bs)) (blocks L A) ->
  blk_data B mem x bs -> blk_data B memX x bs.
Proof.
  intros stk Sw L A mem md LX AXX memX mdX x bs (_ & _ & _ & _ & _ & _ & _ & _ & Hbyt & _) Hin HD i Hi.
  rewrite (Hbyt x _ i Hin Hi). exact (HD i Hi).
Qed.

Lemma norm_stk : forall mem lo hi, ro_agree rsegs mem -> LF_RES_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at (ms_segs B) mem a) -> Frame.stk rsegs (normalize rsegs mem) lo hi.
Proof.
  intros mem lo hi Hro Hlo Hhi H. apply lf_stk; [exact Hlo | exact Hhi |]. intros a Ha.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
  unfold writable_at. rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
    (lf_ro_addr_out B a SEGS Hni ltac:(unfold LF_RES_TOP in Hlo; lia))).
  pose proof (H a Ha) as W. rewrite SEGS in W. exact W.
Qed.

Lemma norm_blk : forall L A mem md x n, aa_MR API L A mem md -> In (x, n) (blocks L A) -> 0 < n ->
  ro_agree rsegs mem -> exists junk, rw_cells rsegs (normalize rsegs mem) x [CB (Z.to_nat n) junk].
Proof.
  intros L A mem md x n HM Hin Hn Hro. pose proof Hin as Hin'. apply blocks_In in Hin' as (q & Hq & Hqin).
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q n HM Hqin) as (R1 & R2). rewrite Hq in R1, R2.
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (ST : Frame.stk rsegs (normalize rsegs mem) x (x + n)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (mr_blocks B _ (aa_laws API) L A mem md q n (a - x) HM Hqin ltac:(lia)) as ((v & Hv) & _).
    pose proof (ax_blocks_img AX L A mem md q n (a - x) HM Hqin ltac:(lia)) as Hni.
    rewrite Hq in Hv, Hni. replace (x + (a - x)) with a in Hv, Hni by lia.
    assert (E : normalize rsegs mem (Z_to_bv 64 a) = Some v).
    { rewrite (mem_rel_rw rsegs mem (normalize rsegs mem) (Z_to_bv 64 a) (mem_rel_normalize rsegs mem Hro)
        (lf_ro_addr_out B a SEGS Hni ltac:(lia))). exact Hv. }
    unfold wa. split.
    - unfold wview. rewrite E. discriminate.
    - exists v. unfold mrd. rewrite E. reflexivity. }
  destruct (stk_carve rsegs _ x (x + n) (Z.to_nat n) ST ltac:(rewrite Z2Nat.id by lia; lia)) as [_ [junk HR]].
  rewrite Z2Nat.id in HR by lia. replace (x + n - n) with x in HR by lia. exists junk. exact HR.
Qed.

Lemma g_pre : forall stk S L0 A0 mem0 md0 L A mem md regs K,
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - K -> spZ regs <= S -> 0 <= K ->
  YM05.alloc_ceiling + stk <= S -> spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  call_pre_k B (aa_MR API) K L A regs mem md.
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md regs K
    (HM & HW & HB & HID & _ & _ & _ & _ & _ & Hstw & Herr & _) Hra Hal H1 H2 HK Hc H63 Htp.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
  split; [exact Hal|]. split; [lia|]. split; [exact H63|].
  split; [intros a Ha; apply Hstw; lia|]. split; [exact Htp|]. split; [exact Herr|].
  intros E. rewrite HID in E. discriminate.
Qed.

Lemma g_above : forall stk S L A regs mem md K E L' A' regs' mem' md',
  aa_MR API L A mem md ->
  call_post_k B (aa_MR API) K L A regs mem md E L' A' regs' mem' md' ->
  YM05.alloc_ceiling + stk <= S -> S - stk <= spZ regs - K -> S <= 2 ^ 64 -> 0 <= K ->
  (forall a, E a -> a < YM05.alloc_ceiling) ->
  forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a).
Proof.
  intros stk S L A regs mem md K E L' A' regs' mem' md' HM
    (HM2 & _ & _ & _ & _ & _ & _ & Hfr & _) H1 H2 H3 HK0 HE a Ha.
  pose proof YM05.alloc_ceiling_value as Hac.
  apply Hfr.
  - left. lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
  - unfold scratch_k. intros [Hs|Hs]; [lia | pose proof (lf_errno_low B ERRNO_LOW a Hs); lia].
  - intros He. pose proof (HE a He). lia.
Qed.

(* g_above over check_copy's call_post_x *)
Lemma g_above_x : forall stk S L A regs mem md K gone L' A' regs' mem' md',
  aa_MR API L A mem md ->
  call_post_x B API K L A regs mem md gone L' A' regs' mem' md' ->
  YM05.alloc_ceiling + stk <= S -> S - stk <= spZ regs - K -> S <= 2 ^ 64 -> 0 <= K ->
  forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a).
Proof.
  intros stk S L A regs mem md K gone L' A' regs' mem' md' HM
    (HM2 & _ & _ & _ & _ & _ & _ & Hfr & _) H1 H2 H3 HK0 a Ha.
  pose proof YM05.alloc_ceiling_value as Hac.
  apply Hfr.
  - left. lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
  - unfold scratch_k. intros [Hs|Hs]; [lia | pose proof (lf_errno_low B ERRNO_LOW a Hs); lia].
Qed.

Lemma g_run : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs pc mem md L A
    (Q : machine_state -> Prop) (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m' W, ms = MState.MS R F pc' fc None m' (seg_rom rsegs) /\
     munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
     (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x ->
        (S - stk <= x < S) \/ exists y k, lf_mine L0 A0 L A y k /\ y <= x < y + k)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     lf_fr B API stk S L0 A0 mem0 md0 L A m' md ->
     SR rsegs (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (YK11.seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs pc mem md L A Q P FR Hc HS HE Hform HK.
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  apply (llvm_run_norm fx' regs pc mem md Q P Hh Hl Hro HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F & pc' & fc & m' & W & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R2 & F2 & pc2 & fc2 & m2 & W & HE2 & MU & WM & HW).
    injection HE2 as ER EF EP EC EM. subst R2 F2 pc2 fc2 m2.
    assert (MU' : munch W mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU).
    assert (WM' : wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' Hro Hsame).
    apply (HK R F pc' fc m0' HQ regs' m' Hx Hrel).
    eapply (lf_fr_evt B API SEGS AX HGG); [exact FR | exact Hc | exact HS | exact MU' | exact WM' | exact Hro' | exact HW].
Qed.

Lemma g_malloc : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A n bres (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - ALLOC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK11.getr regs 10 = Z_to_bv 64 n ->
  res_ok_slots A bres -> room_slots bres n ->
  (forall L' A' regs' mem' md' res,
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 res -> 4096 <= res -> res + n <= YM05.alloc_ceiling -> res mod 16 = 0 ->
     (forall i, 0 <= i < n -> ~ in_img B (res + i)) ->
     (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) ->
     res_ok_slots A' (sb_malloc bres n) ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 LLVM_MALLOC) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A n bres P FR Hc HS Hra Hal H1 H2 H63 Htp H10 Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply SR_bind.
  { replace (Z_to_bv 64 LLVM_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite HMAL; reflexivity).
    apply (MALLOC fx' L A regs mem md n bres).
    - apply call_pre_k_alloc. exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
        ltac:(unfold ALLOC_STACK; lia) Hc H63 Htp).
    - rewrite SEGS. exact MI.
    - exact H10.
    - exact Hres.
    - exact Hroom. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & res & -> & Hpost & G10 & Hres0 & Hal16 & (Hf1 & Hf2 & Hf3)
    & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub & Hidt & Hlen & Hres2).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. pose proof (Hblk a0 k0 Hin) as Hin2. rewrite Eb2 in Hin2. rewrite Eb1.
      apply in_app_or in Hin2. apply in_or_app. destruct Hin2 as [Hin2|Hin2]; [left; exact Hin2 | right; right; exact Hin2].
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K L2 A2 regs2 mem2 md2 res FR2 Hrp G10 ltac:(lia) ltac:(lia) Hal16 Hf3 (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2)))
    Hres2).
  - apply (g_above stk S L A regs mem md ALLOC_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM).
    + apply call_post_k_alloc. exact Hpost.
    + exact Hc.
    + exact H1.
    + exact HS.
    + unfold ALLOC_STACK; lia.
    + intros a Ha. destruct Ha.
  - exact Hkept.
Qed.

Lemma g_free : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A x n bres (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - ALLOC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK11.getr regs 10 = Z_to_bv 64 x ->
  In (x, n) (blocks L A) -> 0 < n -> (forall a k, In (a, k) (blocks L0 A0) -> a + k <= x \/ x + n <= a) ->
  res_ok_slots A bres ->
  (forall L' A' regs' mem' md',
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     (exists b1 b2, blocks L A = b1 ++ (x, n) :: b2 /\ blocks L' A' = b1 ++ b2) ->
     res_ok_slots A' (sb_free bres n) ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun a => a = x) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 LLVM_FREE) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A x n bres P FR Hc HS Hra Hal H1 H2 H63 Htp H10 Hin Hn Hd Hres K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hin as Hin'. apply blocks_In in Hin' as (q & Hq & Hqin).
  assert (Hfreed : forall a, x <= a < x + n -> a < YM05.alloc_ceiling /\ ~ in_img B a).
  { intros a Ha.
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q n (a - x) HM Hqin ltac:(lia)) as (_ & R1 & R2 & _).
    pose proof (ax_blocks_img AX L A mem md q n (a - x) HM Hqin ltac:(lia)) as Himgx.
    rewrite Hq in R1, R2, Himgx. replace (x + (a - x)) with a in Himgx by lia. split; [lia | exact Himgx]. }
  eapply SR_bind.
  { replace (Z_to_bv 64 LLVM_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite HFRE; reflexivity).
    apply (FREE fx' L A regs mem md q n bres).
    - apply call_pre_k_alloc. exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
        ltac:(unfold ALLOC_STACK; lia) Hc H63 Htp).
    - rewrite SEGS. exact MI.
    - exact Hqin.
    - rewrite H10, Hq. reflexivity.
    - exact Hres. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & -> & Hpost & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub & Hidt
    & Hlen & Hres2).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  rewrite Hq in Eb1, Hkept.
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold ALLOC_STACK in *; lia | lia | | | | | | exact (Hidt HID) | | ].
    - intros a Ha. right. rewrite Hq in Ha. exact (Hfreed a Ha).
    - intros a Ha. right. intros Hf. rewrite Hq in Hf. destruct (Hfreed a Hf). lia.
    - intros a Hf Ha. rewrite Hq in Hf. destruct (Hfreed a Hf). lia.
    - intros a0 k0 Hin0. pose proof (Hblk a0 k0 Hin0) as Hin2. rewrite Eb1 in Hin2. rewrite Eb2.
      apply in_app_or in Hin2. apply in_or_app.
      destruct Hin2 as [Hin2|[Hin2|Hin2]]; [left; exact Hin2 | | right; exact Hin2].
      exfalso. injection Hin2 as E1 E2. subst a0 k0. destruct (Hd _ _ Hin0); lia.
    - intros a0 k0 i Hin0 Hi. apply (Hkept a0 k0 i (Hblk a0 k0 Hin0)); [|exact Hi].
      intros E. subst a0. destruct (Hd _ _ Hin0); lia.
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K L2 A2 regs2 mem2 md2 FR2 Hrp (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2))) Hres2).
  - apply (g_above stk S L A regs mem md ALLOC_STACK (fun a => ptr_addr L q <= a < ptr_addr L q + n)
      L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS ltac:(unfold ALLOC_STACK; lia)).
    intros a Ha. rewrite Hq in Ha. exact (proj1 (Hfreed a Ha)).
  - exact Hkept.
Qed.

(* check_copy(c, f, n) at 0x13550 (fuzz_wire.c:275): its frame is the caller's frame below spZ regs; c is no entry
   block, so the entry blocks' bytes come from blocks_kept with the exception c *)
Lemma g_cc : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A c f n kc bs bres
    (P : config -> Prop),
  (forall fx'' : YK11.FPState, @check_copy_contract fx'' rc B API) ->
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 c -> YK11.getr regs 11 = Z_to_bv 64 f -> YK11.getr regs 12 = Z_to_bv 64 n ->
  n <= 1600 -> Z.of_nat (length bs) = n -> In (c, kc) (blocks L A) -> n <= kc ->
  (exists qf kf, In (qf, kf) (blocks L A) /\ qf <> c /\ qf <= f /\ f + n <= qf + kf) ->
  Mem.bytes_at (ms_segs B) mem c bs -> Mem.bytes_at (ms_segs B) mem f bs ->
  (forall a k, In (a, k) (blocks L0 A0) -> a <> c) ->
  frm_zero (@fp_csr fx') -> res_ok_slots A bres -> room_slots bres (fuzz_dup_size n) ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 (copy_untag_result n bs) ->
     Mem.bytes_at (ms_segs B) mem' c (cu_bytes n bs) ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_COPY) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A c f n kc bs bres P CC FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 Hn Hlen Hinc Hkc Hinf BC BF Hnc Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply SR_bind.
  { apply (CC fx' L A regs mem md c f n kc bs bres SEGS).
    - exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs CC_STACK FR Hra Hal H1 H2
        ltac:(unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact HID.
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hn.
    - exact Hlen.
    - exact Hinc.
    - exact Hkc.
    - exact Hinf.
    - exact BC.
    - exact BF.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & G210 & BC2 & Eb & Hkept & Hgk & Hro2 & Hres2
    & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & _).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call_x B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK in *; lia | lia | | | exact Hidt | | ].
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (Hnc a0 k0 Hin) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp G210 BC2 Eb Hres2).
  apply (g_above_x stk S L A regs mem md CC_STACK (fun a => a = c) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
    ltac:(unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK; lia)).
Qed.

End G.

Lemma en_out2 : forall lo1 hi1 lo2 hi2 x, ~ outside [(lo1, hi1); (lo2, hi2)] x -> lo1 <= x < hi1 \/ lo2 <= x < hi2.
Proof.
  intros lo1 hi1 lo2 hi2 x NO.
  destruct (Z_le_dec lo1 x); destruct (Z_lt_dec x hi1); destruct (Z_le_dec lo2 x); destruct (Z_lt_dec x hi2);
    try lia; exfalso; apply NO; cbn [outside]; (split; [lia | split; [lia | exact I]]).
Qed.

(* the arithmetic side conditions of a call at the SR level: sp = Sp, ra a code address *)
Ltac sr_side Hsp1 Q1 := first [ lia
  | rewrite Hsp1; unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK; lia
  | rewrite Q1; apply ret_ok_even; reflexivity
  | rewrite Hsp1; Z.div_mod_to_equations; lia ].

Lemma pres_get : forall r1 r2 (k : Z) v, regs_preserved r1 r2 -> callee_saved k ->
  YK11.getr r1 (Z_to_bv 5 k) = v -> YK11.getr r2 (Z_to_bv 5 k) = v.
Proof. intros r1 r2 k v Hp1 Hk1 E. rewrite (Hp1 k Hk1). exact E. Qed.

Ltac cs := unfold callee_saved; lia.

Lemma lf_getr_cs : forall R x, callee_saved x -> YK11.getr R (Z_to_bv 5 x) = reg_get R (Z_to_bv 5 x).
Proof.
  intros R x Hx.
  destruct (lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    reflexivity.
Qed.

(* decode's llvm_n_bound: the payload size is that of a live block, or 0 *)
Lemma llvm_n_bound : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B)
    stk empty L A regs mem md ra p n,
  lib_pre B API stk empty L A regs mem md ra p n -> 0 <= n < 2 ^ 47.
Proof.
  intros fx rc B API stk empty L A regs mem md ra p n (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [Hn (q & Hq & _)]]; [lia|].
  destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia.
Qed.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis BND : blocks_nodup B API.
Hypothesis CT : ctx_owned B API.
Hypothesis MC : memcpy_contract.
Hypothesis CF : check_forward_contract.
Hypothesis CR : check_ret_contract.
Hypothesis CD : check_downstream_contract.
Hypothesis CM : check_meter_contract.
Hypothesis CN : check_counter_contract.
Hypothesis CW : check_width_contract.
Hypothesis CRD : check_read_contract.
Hypothesis CC : forall fx' : YK11.FPState, @check_copy_contract fx' rc B API.

Section Run.
Variables (stk empty : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
  (md0 : Model) (ra p n : Z) (pl : list byte) (b : sbound) (j : nat).
Hypothesis BI : llvm_binds B API.
Hypothesis Hk : LLVM_K <= stk.
Hypothesis Hra : YK0s.ret_ok (Z_to_bv 64 ra).
Hypothesis Hpre : lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n.
Hypothesis Hlen : n = Z.of_nat (length pl).
Hypothesis Hpd : blk_data B mem0 p pl.
Hypothesis Hsn : sink_none B mem0 md0.
Hypothesis Hsp : spZ regs0 <= 2 ^ 47.
Hypothesis Hroom : llvm_room b.
Hypothesis Hro : ro_agree rsegs mem0.
Hypothesis Hn : 1 <= n < 2 ^ 26.

Local Abbreviation Sx := (spZ regs0).
Local Abbreviation Sp := (spZ regs0 - 64).
Local Abbreviation nn := (nclamp n).
Local Abbreviation n1 := (fuzz_dup_size (nclamp n)).
Local Abbreviation sv0 := (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
  (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 22)).
Local Abbreviation Post := (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).

(* the registers the walk never writes and every callee keeps: gp, tp, s7..s11 *)
Definition kp (regs : bvmap 5 word) : Prop :=
  YK11.getr regs 3 = YK11.getr regs0 3 /\ YK11.getr regs 4 = YK11.getr regs0 4 /\
  YK11.getr regs 23 = YK11.getr regs0 23 /\ YK11.getr regs 24 = YK11.getr regs0 24 /\
  YK11.getr regs 25 = YK11.getr regs0 25 /\ YK11.getr regs 26 = YK11.getr regs0 26 /\
  YK11.getr regs 27 = YK11.getr regs0 27.

Lemma kp_pres : forall r r', kp r -> regs_preserved r r' -> kp r'.
Proof.
  intros r r' (H3 & H4 & H23 & H24 & H25 & H26 & H27) Hp.
  assert (X : forall k, callee_saved k -> YK11.getr r' (Z_to_bv 5 k) = YK11.getr r (Z_to_bv 5 k)) by exact Hp.
  split; [exact (eq_trans (X 3 ltac:(unfold callee_saved; lia)) H3)|].
  split; [exact (eq_trans (X 4 ltac:(unfold callee_saved; lia)) H4)|].
  split; [exact (eq_trans (X 23 ltac:(unfold callee_saved; lia)) H23)|].
  split; [exact (eq_trans (X 24 ltac:(unfold callee_saved; lia)) H24)|].
  split; [exact (eq_trans (X 25 ltac:(unfold callee_saved; lia)) H25)|].
  split; [exact (eq_trans (X 26 ltac:(unfold callee_saved; lia)) H26)|].
  exact (eq_trans (X 27 ltac:(unfold callee_saved; lia)) H27).
Qed.

Lemma f_bounds : 8304 <= stk /\ YM05.alloc_ceiling + stk <= Sx /\ Sx mod 16 = 0 /\ Sx <= 2 ^ 47 /\
  LF_RES_TOP < YM05.alloc_ceiling.
Proof.
  pose proof Hpre as (_ & _ & _ & _ & _ & Hal & Hceil & _).
  pose proof Hk as Hk'. unfold LLVM_K, LLVM_FRAME, CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK in Hk'.
  pose proof lf_ceiling as Hrt.
  split; [lia|]. split; [exact Hceil|]. split; [exact Hal|]. split; [exact Hsp | exact Hrt].
Qed.

(* size >= 1: data is the driver's payload block, in [4096, alloc_ceiling) *)
Lemma f_pay : In (p, n) (blocks L0 A0) /\ 4096 <= p /\ p + n <= YM05.alloc_ceiling /\
  reg_get regs0 10 = Z_to_bv 64 p /\ reg_get regs0 11 = Z_to_bv 64 n.
Proof.
  pose proof Hpre as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & Hn1 & Hpl & _).
  destruct Hpl as [[E _] | [_ (q & Hq & Hqp)]]; [lia|].
  pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
  split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. split; [lia|]. split; [lia|].
  split; [exact Hp | exact Hn1].
Qed.

(* the payload is a live block of every later state, with its bytes *)
Lemma f_blk : forall L A mem md, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  In (p, n) (blocks L A) /\ blk_data B mem p pl.
Proof.
  intros L A mem md (HM & _ & _ & _ & _ & _ & _ & Hblk & Hbyt & _).
  destruct f_pay as (Hin & H1 & H2 & _).
  split; [exact (Hblk _ _ Hin)|].
  intros i Hi. rewrite (Hbyt _ _ i Hin ltac:(lia)). exact (Hpd i Hi).
Qed.

Lemma f_norm : forall L A mem md cs, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  (cells_size cs <= 64)%nat -> rw_cells rsegs mem Sp cs -> rw_cells rsegs (normalize rsegs mem) Sp cs.
Proof.
  intros L A mem md cs FR Hsz HC. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  pose proof BI as (SEGS & _).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5).
  apply (lf_rw_cells_norm B mem Sp cs SEGS MI); [|exact HC].
  intros i Hi Himg. pose proof (lf_in_img_top B _ SEGS Himg). pose proof (rw_cells_bound _ _ _ _ HC). lia.
Qed.

Lemma f_stk : forall L A mem md, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  Frame.stk rsegs (normalize rsegs mem) (Sx - stk) Sp.
Proof.
  intros L A mem md FR. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw & _ & _ & MI).
  pose proof BI as (SEGS & _).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  apply lf_stk; [lia | lia |]. intros a Ha. unfold writable_at.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
  rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem MI)
             (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
  rewrite <- SEGS. exact (Hstw a ltac:(lia)).
Qed.

Lemma f_blk_range : forall L A mem md x k, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  In (x, k) (blocks L A) -> 4096 <= x /\ x + k <= YM05.alloc_ceiling.
Proof.
  intros L A mem md x k (HM & _) Hin. apply blocks_In in Hin as (q & Hq & Hqin).
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q k HM Hqin) as (R1 & R2). rewrite Hq in R1, R2. lia.
Qed.

(* 0x12f04: the return value 0, the epilogue and ret *)
Lemma sr_tail : forall (fx' : YK11.FPState) L A regs mem md,
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md -> res_ok_slots A b ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> kp regs -> rw_cells rsegs mem Sp sv0 ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12f04) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md Hfrm FR Hres G2 (G3 & G4 & G23 & G24 & G25 & G26 & G27) HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & _).
  pose proof (f_norm L A mem md sv0 FR ltac:(cbn; lia) HC) as HCn.
  assert (E2 : reg_get regs 2 = Z_to_bv 64 Sp) by exact G2.
  assert (E3 : reg_get regs 3 = reg_get regs0 3) by exact G3.
  assert (E4 : reg_get regs 4 = reg_get regs0 4) by exact G4.
  assert (E23 : reg_get regs 23 = reg_get regs0 23) by exact G23.
  assert (E24 : reg_get regs 24 = reg_get regs0 24) by exact G24.
  assert (E25 : reg_get regs 25 = reg_get regs0 25) by exact G25.
  assert (E26 : reg_get regs 26 = reg_get regs0 26) by exact G26.
  assert (E27 : reg_get regs 27 = reg_get regs0 27) by exact G27.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12f04) mem md L A).
  { exact FR. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E23, E24, E25, E26, E27.
    apply e6_evt. rewrite unsigned_lit by lia. exact HCn. }
  { intros ms ->. do 5 eexists. exists (@nil (Z * Z)).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x Hx NO. exfalso. apply NO. exact I. }
  intros R F pc' fc m0' HQ regs' m' Hx Hrel FR'.
  injection HQ as ER EF EP EC EM. subst R F pc' fc m0'.
  apply SR_ret.
  assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 0) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
  assert (RP : regs_preserved regs0 regs').
  { intros r Hr. rewrite (lf_getr_eqv _ _ _ Hx).
    destruct (lf_callee_cases r Hr) as [-> | Hr'].
    - transitivity (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (spZ regs0 - 64)) + 64)); [reflexivity|].
      rewrite unsigned_lit by lia. replace (spZ regs0 - 64 + 64) with (spZ regs0) by lia. unfold spZ.
      apply Z_to_bv_bv_unsigned.
    - repeat (destruct Hr' as [-> | Hr']; [reflexivity|]). subst. reflexivity. }
  destruct (lf_post B API SINK stk empty L0 A0 regs0 mem0 md0 ra p n L A regs' m' md Hpre Hsn FR' G10 RP)
    as (Hpost & Hsn' & Hpay & MI2).
  exists (mkFP (@fp_regs fx') (@fp_csr fx')), L, A, regs', m', md.
  assert (E1 : YK11.getr regs0 1 = reg_get regs0 1) by reflexivity.
  split; [rewrite SEGS, <- E1, Hra1, (lf_ret_pc _ Hra); reflexivity|].
  split; [exact Hfrm|]. split; [exact Hpost|]. split; [exact Hsn'|].
  split; [exact Hres|]. split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.

(* 0x12efc: free(f) *)
Lemma sr_free2 : forall (fx' : YK11.FPState) L A regs mem md f,
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md -> res_ok_slots A (sb_malloc b n1) ->
  In (f, n1) (blocks L A) -> (forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + n1 <= a) ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> kp regs -> YK11.getr regs 8 = Z_to_bv 64 f -> rw_cells rsegs mem Sp sv0 ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12efc) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md f Hfrm FR Hres Hin Hd G2 KP G8 HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  pose proof FR as (HM & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof (fuzz_dup_size_range nn ltac:(unfold nclamp; lia)) as [D1 D2].
  assert (E8 : reg_get regs 8 = Z_to_bv 64 f) by exact G8.
  rewrite SEGS.
  apply (llvm_run fx' regs (Z_to_bv 64 0x12efc) mem md
    (fun ms => exists R, ms = MS R (@fp_regs fx') (Z_to_bv 64 0x14758) (@fp_csr fx') None mem (YK11.seg_rom rsegs) /\
       reg_get R 1 = Z_to_bv 64 0x12f04 /\ reg_get R 10 = Z_to_bv 64 f /\
       forall x, callee_saved x -> reg_get R (Z_to_bv 5 x) = reg_get regs (Z_to_bv 5 x)));
    [exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of. eapply evt_cut; [apply e5_evt|].
    intros ms' ->. apply evt_done. eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [exact E8|].
    intros x Hx. destruct (lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      reflexivity. }
  { intros ms (R & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R' & HE & H1 & H10 & Hcs) regs' Hx.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  assert (Q1 : YK11.getr regs' 1 = Z_to_bv 64 0x12f04) by (rewrite (lf_getr_eqv _ _ _ Hx); exact H1).
  assert (Q10 : YK11.getr regs' 10 = Z_to_bv 64 f) by (rewrite (lf_getr_eqv _ _ _ Hx); exact H10).
  assert (RP1 : regs_preserved regs regs').
  { intros x Hx2. rewrite (lf_getr_eqv _ _ _ Hx), !lf_getr_cs by exact Hx2. exact (Hcs x Hx2). }
  assert (Q2 : YK11.getr regs' 2 = Z_to_bv 64 Sp) by exact (pres_get regs regs' 2 _ RP1 ltac:(cs) G2).
  assert (Hsp1 : spZ regs' = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  pose proof (kp_pres regs regs' KP RP1) as KP1.
  assert (Q4 : YK11.getr regs' 4 = Z_to_bv 64 (ms_tp B)) by (destruct KP1 as (_ & K4 & _); rewrite K4; exact Htp0).
  rewrite <- SEGS. change (Z_to_bv 64 0x14758) with (Z_to_bv 64 LLVM_FREE).
  eapply g_free with (stk := stk) (S := Sx) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (x := f) (n := n1)
    (bres := sb_malloc b n1).
  all: try eassumption.
  { lia. }
  { rewrite Q1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp1. replace (spZ regs0 - 64) with (spZ regs0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact B3. }
  { rewrite Hsp1. unfold ALLOC_STACK. lia. }
  { lia. } { lia. }
  intros L2 A2 regs2 mem2 md2 FR2 Hrp2 (b1 & b2 & Eb1 & Eb2) Hres2 Hab2 Hkept2.
  rewrite Q1.
  rewrite sb_free_malloc in Hres2.
  apply (sr_tail (mkFP (@fp_regs fx') (@fp_csr fx')) L2 A2 regs2 mem2 md2 Hfrm FR2 Hres2).
  - exact (pres_get regs' regs2 2 _ Hrp2 ltac:(cs) Q2).
  - exact (kp_pres regs' regs2 KP1 Hrp2).
  - apply (lf_rw_cells_frame mem); [exact HC|]. intros a Ha. cbn [cells_size csize lsv Nat.add] in Ha.
    rewrite <- SEGS. apply Hab2. lia.
Qed.

(* 0x12ee0: `if (len) check_read(c, len, slot)` (fuzz_wire.c:277-278), then free(c) *)
Lemma sr_ccr : forall (fx' : YK11.FPState) L A regs mem md f c bs,
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  res_ok_slots A (sb_malloc (sb_malloc b n1) n1) ->
  In (f, n1) (blocks L A) -> In (c, n1) (blocks L A) -> f <> c ->
  (forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + n1 <= a) ->
  (forall a k, In (a, k) (blocks L0 A0) -> a + k <= c \/ c + n1 <= a) ->
  Z.of_nat (length bs) = nn ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> kp regs -> YK11.getr regs 8 = Z_to_bv 64 f ->
  YK11.getr regs 19 = Z_to_bv 64 c -> YK11.getr regs 10 = Z_to_bv 64 (copy_untag_result nn bs) ->
  Mem.bytes_at (ms_segs B) mem c (cu_bytes nn bs) -> rw_cells rsegs mem Sp sv0 ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12ee0) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md f c bs Hfrm FR Hres Hinf Hinc Hfc Hdf Hdc HL G2 KP G8 G19 G10 BC HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  destruct (nclamp_range n ltac:(lia)) as (N1 & N2 & N3).
  pose proof (fds_ge nn ltac:(lia)) as (D3 & D4). pose proof (fuzz_dup_size_range nn ltac:(lia)) as [D1 D2].
  pose proof (got_le nn bs ltac:(lia)) as GL.
  destruct (f_blk_range L A mem md c n1 FR Hinc) as (C1 & C2).
  destruct (f_blk_range L A mem md f n1 FR Hinf) as (F1 & F2).
  assert (BC' : bytes_at rsegs (normalize rsegs mem) c
                  (firstn (Z.to_nat (copy_untag_result nn bs)) (cu_bytes nn bs))).
  { rewrite SEGS in BC. pose proof (bytes_at_normalize rsegs mem c _ MI BC) as X.
    pose proof (bytes_at_mid _ c _ 0 (Z.to_nat (copy_untag_result nn bs)) X) as Y.
    cbn [skipn] in Y. replace (c + Z.of_nat 0) with c in Y by lia. apply Y.
    rewrite cu_bytes_len by exact HL. lia. }
  pose proof (f_norm L A mem md sv0 FR ltac:(cbn; lia) HC) as HCn.
  pose proof (f_stk L A mem md FR) as STn.
  destruct KP as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 Sp) by exact G2.
  assert (E3 : reg_get regs 3 = reg_get regs0 3) by exact G3.
  assert (E4 : reg_get regs 4 = reg_get regs0 4) by exact G4.
  assert (E23 : reg_get regs 23 = reg_get regs0 23) by exact G23.
  assert (E24 : reg_get regs 24 = reg_get regs0 24) by exact G24.
  assert (E25 : reg_get regs 25 = reg_get regs0 25) by exact G25.
  assert (E26 : reg_get regs 26 = reg_get regs0 26) by exact G26.
  assert (E27 : reg_get regs 27 = reg_get regs0 27) by exact G27.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 f) by exact G8.
  assert (E10 : reg_get regs 10 = Z_to_bv 64 (copy_untag_result nn bs)) by exact G10.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 c) by exact G19.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12ee0) mem md L A).
  { exact FR. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E8, E10, E19, E23, E24, E25, E26, E27.
    eapply (e4_evt CRD) with (lo := Sx - stk) (bs := firstn (Z.to_nat (copy_untag_result nn bs)) (cu_bytes nn bs))
      (cs := sv0); rewrite ?(unsigned_lit (spZ regs0 - 64)) by lia.
    - unfold LF_RES_TOP in B5. lia.
    - lia.
    - Z.div_mod_to_equations. lia.
    - lia.
    - lia.
    - lia.
    - rewrite length_firstn, cu_bytes_len by exact HL. lia.
    - exact (mem_inv_normalize rsegs mem).
    - exact STn.
    - exact BC'.
    - exact HCn.
    - reflexivity. }
  { intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & FRc).
    do 5 eexists. exists [(Sx - stk, Sp)].
    split; [reflexivity|]. split; [rewrite unsigned_lit in MU by lia; exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply en_out1 in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & HE & MU & WM & FRc).
  injection HE as ER EF EP EC EM. subst R F pc' fc m''.
  rewrite unsigned_lit in FRc by lia.
  pose proof (lf_rw_cells_rel m1 _ _ _ Hrel1 FRc) as FC1.
  assert (Q1 : YK11.getr regs1 1 = Z_to_bv 64 0x12efc) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q2 : YK11.getr regs1 2 = Z_to_bv 64 Sp) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q8 : YK11.getr regs1 8 = Z_to_bv 64 f) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q10 : YK11.getr regs1 10 = Z_to_bv 64 c) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (KP1 : kp regs1) by (unfold kp; rewrite !(lf_getr_eqv _ _ _ Hx1); repeat split; reflexivity).
  assert (Hsp1 : spZ regs1 = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  assert (Q4 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (destruct KP1 as (_ & K4 & _); rewrite K4; exact Htp0).
  rewrite <- SEGS. change (Z_to_bv 64 0x14758) with (Z_to_bv 64 LLVM_FREE).
  eapply g_free with (stk := stk) (S := Sx) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (x := c) (n := n1)
    (bres := sb_malloc (sb_malloc b n1) n1).
  all: try eassumption.
  all: try sr_side Hsp1 Q1.
  intros L2 A2 regs2 mem2 md2 FR2 Hrp2 (b1 & b2 & Eb1 & Eb2) Hres2 Hab2 Hkept2.
  rewrite Q1. rewrite sb_free_malloc in Hres2.
  apply (sr_free2 (mkFP (@fp_regs fx') (@fp_csr fx')) L2 A2 regs2 mem2 md2 f Hfrm FR2 Hres2).
  - rewrite Eb2. apply (ccg_in_del b1 b2 (c, n1)); [rewrite <- Eb1; exact Hinf|].
    intros E. injection E as E1. exact (Hfc E1).
  - exact Hdf.
  - exact (pres_get regs1 regs2 2 _ Hrp2 ltac:(cs) Q2).
  - exact (kp_pres regs1 regs2 KP1 Hrp2).
  - exact (pres_get regs1 regs2 8 _ Hrp2 ltac:(cs) Q8).
  - apply (lf_rw_cells_frame m1); [exact FC1|]. intros a Ha. cbn [cells_size csize lsv Nat.add] in Ha.
    rewrite <- SEGS. apply Hab2. lia.
Qed.

(* 0x12eb4: fuzz_dup(f, n)'s NULL test and memcpy for c, then check_copy(c, f, n) *)
Lemma sr_mid2 : forall (fx' : YK11.FPState) L A regs mem md f c src,
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  res_ok_slots A (sb_malloc (sb_malloc b n1) n1) ->
  In (f, n1) (blocks L A) -> In (c, n1) (blocks L A) -> f <> c -> f + n1 <= c \/ c + n1 <= f ->
  (forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + n1 <= a) ->
  (forall a k, In (a, k) (blocks L0 A0) -> a + k <= c \/ c + n1 <= a) ->
  (forall a k, In (a, k) (blocks L0 A0) -> a <> c) ->
  Z.of_nat (length src) = nn -> blk_data B mem f src ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> kp regs -> YK11.getr regs 8 = Z_to_bv 64 f ->
  YK11.getr regs 9 = Z_to_bv 64 nn -> YK11.getr regs 10 = Z_to_bv 64 c -> YK11.getr regs 22 = Z_to_bv 64 (n - 1) ->
  rw_cells rsegs mem Sp sv0 ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12eb4) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md f c src Hfrm FR Hres Hinf Hinc Hfc Hdj Hdf Hdc Hnc HL BD G2 KP G8 G9 G10 G22 HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  destruct (nclamp_range n ltac:(lia)) as (N1 & N2 & N3).
  pose proof (fds_ge nn ltac:(lia)) as (D3 & D4). pose proof (fuzz_dup_size_range nn ltac:(lia)) as [D1 D2].
  destruct (f_blk_range L A mem md c n1 FR Hinc) as (C1 & C2).
  destruct (f_blk_range L A mem md f n1 FR Hinf) as (F1 & F2).
  assert (BF : bytes_at rsegs (normalize rsegs mem) f src).
  { apply bytes_at_normalize; [exact MI|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact BD]. }
  assert (JK : exists junk, 0 < nn -> rw_cells rsegs (normalize rsegs mem) c [CB (Z.to_nat nn) junk]).
  { destruct (Z_lt_le_dec 0 nn) as [Hp0|Hp0].
    - destruct (norm_blk B API SEGS AX L A mem md c n1 HM Hinc D1 MI) as [junk HJ].
      rewrite (D4 Hp0) in HJ. exists junk. intros _. exact HJ.
    - exists []. intros H. lia. }
  destruct JK as [junk JK].
  pose proof (f_norm L A mem md sv0 FR ltac:(cbn; lia) HC) as HCn.
  destruct KP as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 Sp) by exact G2.
  assert (E3 : reg_get regs 3 = reg_get regs0 3) by exact G3.
  assert (E4 : reg_get regs 4 = reg_get regs0 4) by exact G4.
  assert (E23 : reg_get regs 23 = reg_get regs0 23) by exact G23.
  assert (E24 : reg_get regs 24 = reg_get regs0 24) by exact G24.
  assert (E25 : reg_get regs 25 = reg_get regs0 25) by exact G25.
  assert (E26 : reg_get regs 26 = reg_get regs0 26) by exact G26.
  assert (E27 : reg_get regs 27 = reg_get regs0 27) by exact G27.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 f) by exact G8.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 nn) by exact G9.
  assert (E10 : reg_get regs 10 = Z_to_bv 64 c) by exact G10.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 (n - 1)) by exact G22.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12eb4) mem md L A).
  { exact FR. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E8, E9, E10, E22, E23, E24, E25, E26, E27.
    eapply (e3_evt MC) with (src := src) (junk := junk) (cs := sv0); rewrite ?(unsigned_lit (spZ regs0 - 64)) by lia.
    - lia.
    - exact HL.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact (mem_inv_normalize rsegs mem).
    - exact BF.
    - exact JK.
    - exact HCn. }
  { intros ms (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & BC0 & BF0 & FRc).
    do 5 eexists. exists [(c, c + nn)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. apply en_out1 in NO. right. exists c, n1. split; [|lia].
    split; [exact Hinc|]. split; [exact D1 | exact Hdc]. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & HE & MU & WM & BC0 & BF0 & FRc).
  injection HE as ER EF EP EC EM. subst R F pc' fc m''.
  rewrite unsigned_lit in FRc by lia.
  pose proof (lf_rw_cells_rel m1 _ _ _ Hrel1 FRc) as FC1.
  assert (BC1 : Mem.bytes_at (ms_segs B) m1 c src)
    by (rewrite SEGS; exact (proj2 (bytes_at_rel rsegs m1 m0' c src Hrel1) BC0)).
  assert (BF1 : Mem.bytes_at (ms_segs B) m1 f src)
    by (rewrite SEGS; exact (proj2 (bytes_at_rel rsegs m1 m0' f src Hrel1) BF0)).
  assert (Q1 : YK11.getr regs1 1 = Z_to_bv 64 0x12ee0) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q2 : YK11.getr regs1 2 = Z_to_bv 64 Sp) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q8 : YK11.getr regs1 8 = Z_to_bv 64 f) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q10 : YK11.getr regs1 10 = Z_to_bv 64 c) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q11 : YK11.getr regs1 11 = Z_to_bv 64 f) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q12 : YK11.getr regs1 12 = Z_to_bv 64 nn) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q19 : YK11.getr regs1 19 = Z_to_bv 64 c) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (KP1 : kp regs1) by (unfold kp; rewrite !(lf_getr_eqv _ _ _ Hx1); repeat split; reflexivity).
  assert (Hsp1 : spZ regs1 = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  assert (Q4 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (destruct KP1 as (_ & K4 & _); rewrite K4; exact Htp0).
  rewrite <- SEGS. change (Z_to_bv 64 0x13550) with (Z_to_bv 64 CHECK_COPY).
  eapply g_cc with (stk := stk) (S := Sx) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (c := c) (f := f)
    (n := nn) (kc := n1) (bs := src) (bres := sb_malloc (sb_malloc b n1) n1).
  all: try eassumption.
  all: try sr_side Hsp1 Q1.
  { exists f, n1. split; [exact Hinf|]. split; [exact Hfc|]. lia. }
  { destruct Hroom as (R1 & R2 & R3). apply lf_room; unfold sb_malloc; cbn [sb_live sb_bytes sb_cap]; lia. }
  intros fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp2 G210 BC2 Eb2 Hres2 Hab2.
  rewrite Q1.
  apply (sr_ccr fx2 L2 A2 regs2 mem2 md2 f c src Hfrm2 FR2 Hres2).
  - rewrite Eb2. exact Hinf.
  - rewrite Eb2. exact Hinc.
  - exact Hfc.
  - exact Hdf.
  - exact Hdc.
  - exact HL.
  - exact (pres_get regs1 regs2 2 _ Hrp2 ltac:(cs) Q2).
  - exact (kp_pres regs1 regs2 KP1 Hrp2).
  - exact (pres_get regs1 regs2 8 _ Hrp2 ltac:(cs) Q8).
  - exact (pres_get regs1 regs2 19 _ Hrp2 ltac:(cs) Q19).
  - exact G210.
  - exact BC2.
  - apply (lf_rw_cells_frame m1); [exact FC1|]. intros a Ha. cbn [cells_size csize lsv Nat.add] in Ha.
    rewrite <- SEGS. apply Hab2. lia.
Qed.

(* 0x12e2c: fuzz_dup(data + 1, n)'s NULL test and memcpy for f, the seven checks, then malloc for c *)
Lemma sr_mid1 : forall (fx' : YK11.FPState) L A regs mem md f (b0 : byte),
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md -> res_ok_slots A (sb_malloc b n1) ->
  In (f, n1) (blocks L A) -> (forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + n1 <= a) ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> kp regs -> YK11.getr regs 9 = Z_to_bv 64 nn ->
  YK11.getr regs 10 = Z_to_bv 64 f -> YK11.getr regs 18 = zxb b0 -> YK11.getr regs 19 = Z_to_bv 64 n1 ->
  YK11.getr regs 20 = Z_to_bv 64 p -> YK11.getr regs 22 = Z_to_bv 64 (n - 1) ->
  rw_cells rsegs mem Sp sv0 ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12e2c) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md f b0 Hfrm FR Hres Hinf Hdf G2 KP G9 G10 G18 G19 G20 G22 HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & Hblk & _ & _ & _ & _ & MI).
  destruct (nclamp_range n ltac:(lia)) as (N1 & N2 & N3).
  pose proof (fds_ge nn ltac:(lia)) as (D3 & D4). pose proof (fuzz_dup_size_range nn ltac:(lia)) as [D1 D2].
  destruct (f_blk_range L A mem md f n1 FR Hinf) as (F1 & F2).
  destruct (f_blk L A mem md FR) as (Hinp & BDp).
  destruct f_pay as (Hinp0 & P1 & P2 & _ & _).
  set (src := firstn (Z.to_nat nn) (skipn 1 pl)).
  assert (HLs : Z.of_nat (length src) = nn) by (unfold src; rewrite length_firstn, length_skipn; lia).
  assert (BS : bytes_at rsegs (normalize rsegs mem) (p + 1) src).
  { assert (X : bytes_at rsegs (normalize rsegs mem) p pl).
    { apply bytes_at_normalize; [exact MI|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact BDp]. }
    exact (bytes_at_mid _ p pl 1 (Z.to_nat nn) X ltac:(lia)). }
  assert (DJ : p + 1 + nn <= f \/ f + nn <= p + 1) by (destruct (Hdf p n Hinp0); lia).
  assert (JK : exists junk, 0 < nn -> rw_cells rsegs (normalize rsegs mem) f [CB (Z.to_nat nn) junk]).
  { destruct (Z_lt_le_dec 0 nn) as [Hp0|Hp0].
    - destruct (norm_blk B API SEGS AX L A mem md f n1 HM Hinf D1 MI) as [junk HJ].
      rewrite (D4 Hp0) in HJ. exists junk. intros _. exact HJ.
    - exists []. intros H. lia. }
  destruct JK as [junk JK].
  pose proof (f_norm L A mem md sv0 FR ltac:(cbn; lia) HC) as HCn.
  pose proof (f_stk L A mem md FR) as STn.
  destruct KP as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 Sp) by exact G2.
  assert (E3 : reg_get regs 3 = reg_get regs0 3) by exact G3.
  assert (E4 : reg_get regs 4 = reg_get regs0 4) by exact G4.
  assert (E23 : reg_get regs 23 = reg_get regs0 23) by exact G23.
  assert (E24 : reg_get regs 24 = reg_get regs0 24) by exact G24.
  assert (E25 : reg_get regs 25 = reg_get regs0 25) by exact G25.
  assert (E26 : reg_get regs 26 = reg_get regs0 26) by exact G26.
  assert (E27 : reg_get regs 27 = reg_get regs0 27) by exact G27.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 nn) by exact G9.
  assert (E10 : reg_get regs 10 = Z_to_bv 64 f) by exact G10.
  assert (E18 : reg_get regs 18 = zxb b0) by exact G18.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 n1) by exact G19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 p) by exact G20.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 (n - 1)) by exact G22.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12e2c) mem md L A).
  { exact FR. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E9, E10, E18, E19, E20, E22, E23, E24, E25, E26, E27.
    eapply e2_evt with (lo := Sx - stk) (src := src) (cs := sv0) (junk := junk);
      rewrite ?(unsigned_lit (spZ regs0 - 64)) by lia;
      first [ eassumption | exact (mem_inv_normalize rsegs mem) | reflexivity | (unfold LF_RES_TOP in B5; lia)
            | lia | (Z.div_mod_to_equations; lia) ]. }
  { intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & sl & bt & m' & -> & MU & WM &
      BF0 & FRc).
    do 5 eexists. exists [(Sx - stk, Sp); (f, f + nn)].
    split; [reflexivity|]. split; [rewrite unsigned_lit in MU by lia; exact MU|]. split; [exact WM|].
    intros x Hx NO. destruct (en_out2 _ _ _ _ _ NO) as [H|H]; [left; lia|].
    right. exists f, n1. split; [|lia]. split; [exact Hinf|]. split; [exact D1 | exact Hdf]. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & sl & bt & m'' & HE & MU & WM &
    BF0 & FRc).
  injection HE as ER EF EP EC EM. subst R F pc' fc m''.
  rewrite unsigned_lit in FRc by lia.
  pose proof (lf_rw_cells_rel m1 _ _ _ Hrel1 FRc) as FC1.
  assert (BD1 : blk_data B m1 f src).
  { apply (bytes_at_blk B); [exact SEGS|]. exact (proj2 (bytes_at_rel rsegs m1 m0' f src Hrel1) BF0). }
  assert (Q1 : YK11.getr regs1 1 = Z_to_bv 64 0x12eb4) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q2 : YK11.getr regs1 2 = Z_to_bv 64 Sp) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q8 : YK11.getr regs1 8 = Z_to_bv 64 f) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q9 : YK11.getr regs1 9 = Z_to_bv 64 nn) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q10 : YK11.getr regs1 10 = Z_to_bv 64 n1) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q22 : YK11.getr regs1 22 = Z_to_bv 64 (n - 1)) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (KP1 : kp regs1) by (unfold kp; rewrite !(lf_getr_eqv _ _ _ Hx1); repeat split; reflexivity).
  assert (Hsp1 : spZ regs1 = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  assert (Q4 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (destruct KP1 as (_ & K4 & _); rewrite K4; exact Htp0).
  rewrite <- SEGS. change (Z_to_bv 64 0x14898) with (Z_to_bv 64 LLVM_MALLOC).
  eapply g_malloc with (stk := stk) (S := Sx) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (n := n1)
    (bres := sb_malloc b n1).
  all: try eassumption.
  all: try sr_side Hsp1 Q1.
  { destruct Hroom as (R1 & R2 & R3). apply lf_room; unfold sb_malloc; cbn [sb_live sb_bytes sb_cap]; lia. }
  intros L2 A2 regs2 mem2 md2 c FR2 Hrp2 G210 Hc1 Hc2 Hc16 Hcimg (b1 & b2 & Eb1 & Eb2) Hres2 Hab2 Hkept2.
  rewrite Q1.
  pose proof FR2 as (HM2 & _).
  pose proof FR1 as (_ & _ & _ & _ & _ & _ & _ & Hblk1 & _).
  assert (PW : pairwise ranges_disjoint (b1 ++ (c, n1) :: b2))
    by (rewrite <- Eb1; exact (mr_blocks_disjoint B _ (aa_laws API) L2 A2 mem2 md2 HM2)).
  assert (Hinf' : In (f, n1) (b1 ++ b2)) by (rewrite <- Eb2; exact Hinf).
  pose proof (disj_mid b1 (c, n1) b2 (f, n1) PW Hinf') as Dcf. cbn [fst snd] in Dcf.
  assert (Hdc : forall a k, In (a, k) (blocks L0 A0) -> a + k <= c \/ c + n1 <= a).
  { intros a k Hak. pose proof (Hblk1 a k Hak) as Hak1. rewrite Eb2 in Hak1.
    pose proof (disj_mid b1 (c, n1) b2 (a, k) PW Hak1) as H. cbn [fst snd] in H. lia. }
  assert (Hnc : forall a k, In (a, k) (blocks L0 A0) -> a <> c).
  { intros a k Hak Ea. subst a. pose proof (BND L2 A2 mem2 md2 HM2) as ND. rewrite Eb1, map_app in ND.
    cbn [map fst] in ND. apply NoDup_ListNoDup in ND. apply NoDup_remove_2 in ND. apply ND. rewrite <- map_app, <- Eb2.
    apply in_map_iff. exists (c, k). split; [reflexivity | exact (Hblk1 _ _ Hak)]. }
  apply (sr_mid2 (mkFP (@fp_regs fx') (@fp_csr fx')) L2 A2 regs2 mem2 md2 f c src Hfrm FR2 Hres2).
  - rewrite Eb1. apply ccg_in_ins. exact Hinf'.
  - rewrite Eb1. apply ccg_in_mid.
  - intros E. rewrite E in Dcf. lia.
  - lia.
  - exact Hdf.
  - exact Hdc.
  - exact Hnc.
  - exact HLs.
  - intros i Hi. rewrite (Hkept2 f n1 i Hinf (fun H => H) ltac:(lia)). exact (BD1 i Hi).
  - exact (pres_get regs1 regs2 2 _ Hrp2 ltac:(cs) Q2).
  - exact (kp_pres regs1 regs2 KP1 Hrp2).
  - exact (pres_get regs1 regs2 8 _ Hrp2 ltac:(cs) Q8).
  - exact (pres_get regs1 regs2 9 _ Hrp2 ltac:(cs) Q9).
  - exact G210.
  - exact (pres_get regs1 regs2 22 _ Hrp2 ltac:(cs) Q22).
  - apply (lf_rw_cells_frame m1); [exact FC1|]. intros a Ha. cbn [cells_size csize lsv Nat.add] in Ha.
    rewrite <- SEGS. apply Hab2. lia.
Qed.

Hypothesis Hres0 : res_ok_slots A0 b.

(* 0x12dc0: the prologue up to f = fuzz_dup(data + 1, n)'s malloc *)
Lemma sr_entry : frm_zero (@fp_csr fx) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0) Post.
Proof.
  intros Hfrm.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  destruct f_pay as (Hinp & P1 & P2 & E10 & E11).
  destruct (nclamp_range n ltac:(lia)) as (N1 & N2 & N3).
  pose proof (fds_ge nn ltac:(lia)) as (D3 & D4). pose proof (fuzz_dup_size_range nn ltac:(lia)) as [D1 D2].
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p n Hpre Hro) as FR0.
  assert (Esp : Sx = bv_unsigned (reg_get regs0 2)) by reflexivity.
  assert (ST0 : Frame.stk rsegs (normalize rsegs mem0) (Sx - stk) (bv_unsigned (reg_get regs0 2))).
  { rewrite <- Esp. apply lf_stk; [unfold LF_RES_TOP in *; lia | lia |].
    intros a Ha. unfold writable_at.
    assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
    rewrite (wview_rel_rw rsegs mem0 (normalize rsegs mem0) _ (mem_rel_normalize rsegs mem0 Hro)
               (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    rewrite <- SEGS. exact (Hstw0 a Ha). }
  assert (HPB : bytes_at rsegs (normalize rsegs mem0) p pl).
  { apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact Hpd]. }
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 md0 L0 A0).
  { exact FR0. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of, LLVM_ENTRY. rewrite E10, E11.
    eapply e1_evt with (lo := Sx - stk) (pl := pl).
    - exact ST0.
    - rewrite <- Esp. lia.
    - exact (mem_inv_normalize rsegs mem0).
    - exact Hn.
    - exact Hlen.
    - exact HPB.
    - exact P1.
    - lia. }
  { intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & FRc).
    do 5 eexists. exists [(bv_unsigned (reg_get regs0 2) - 64, bv_unsigned (reg_get regs0 2))].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply en_out1 in NO. rewrite <- Esp in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & HE & MU & WM & FRc).
  injection HE as ER EF EP EC EM. subst R F pc' fc m''.
  rewrite <- Esp in FRc.
  pose proof (lf_rw_cells_rel m1 _ _ _ Hrel1 FRc) as FC1.
  assert (Q1 : YK11.getr regs1 1 = Z_to_bv 64 0x12e2c) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q2 : YK11.getr regs1 2 = Z_to_bv 64 Sp) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q9 : YK11.getr regs1 9 = Z_to_bv 64 nn) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q10 : YK11.getr regs1 10 = Z_to_bv 64 n1) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q18 : YK11.getr regs1 18 = zxb (nth 0 pl (Z_to_bv 8 0))) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q19 : YK11.getr regs1 19 = Z_to_bv 64 n1) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q20 : YK11.getr regs1 20 = Z_to_bv 64 p) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q22 : YK11.getr regs1 22 = Z_to_bv 64 (n - 1)) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (KP1 : kp regs1) by (unfold kp; rewrite !(lf_getr_eqv _ _ _ Hx1); repeat split; reflexivity).
  assert (Hsp1 : spZ regs1 = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  assert (Q4 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (destruct KP1 as (_ & K4 & _); rewrite K4; exact Htp0).
  rewrite <- SEGS. change (Z_to_bv 64 0x14898) with (Z_to_bv 64 LLVM_MALLOC).
  eapply g_malloc with (stk := stk) (S := Sx) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (n := n1) (bres := b).
  all: try eassumption.
  all: try sr_side Hsp1 Q1.
  { destruct Hroom as (R1 & R2 & R3). apply lf_room; lia. }
  intros L2 A2 regs2 mem2 md2 f FR2 Hrp2 G210 Hf1 Hf2 Hf16 Hfimg (b1 & b2 & Eb1 & Eb2) Hres2 Hab2 Hkept2.
  rewrite Q1.
  pose proof FR2 as (HM2 & _).
  assert (PW : pairwise ranges_disjoint (b1 ++ (f, n1) :: b2))
    by (rewrite <- Eb1; exact (mr_blocks_disjoint B _ (aa_laws API) L2 A2 mem2 md2 HM2)).
  assert (Hdf : forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + n1 <= a).
  { intros a k Hak. rewrite Eb2 in Hak. pose proof (disj_mid b1 (f, n1) b2 (a, k) PW Hak) as H.
    cbn [fst snd] in H. lia. }
  apply (sr_mid1 (mkFP (@fp_regs fx) (@fp_csr fx)) L2 A2 regs2 mem2 md2 f (nth 0 pl (Z_to_bv 8 0)) Hfrm FR2 Hres2).
  - rewrite Eb1. apply ccg_in_mid.
  - exact Hdf.
  - exact (pres_get regs1 regs2 2 _ Hrp2 ltac:(cs) Q2).
  - exact (kp_pres regs1 regs2 KP1 Hrp2).
  - exact (pres_get regs1 regs2 9 _ Hrp2 ltac:(cs) Q9).
  - exact G210.
  - exact (pres_get regs1 regs2 18 _ Hrp2 ltac:(cs) Q18).
  - exact (pres_get regs1 regs2 19 _ Hrp2 ltac:(cs) Q19).
  - exact (pres_get regs1 regs2 20 _ Hrp2 ltac:(cs) Q20).
  - exact (pres_get regs1 regs2 22 _ Hrp2 ltac:(cs) Q22).
  - apply (lf_rw_cells_frame m1); [exact FC1|]. intros a Ha. cbn [cells_size csize lsv Nat.add] in Ha.
    rewrite <- SEGS. apply Hab2. lia.
Qed.

End Run.

Theorem LLVMFuzzerTestOneInput_holds_of : LLVMFuzzerTestOneInput_sr_contract B API.
Proof using MALLOC FREE ERRNO_LOW SINK BND CT MC CF CR CD CM CN CW CRD CC.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof (llvm_n_bound B API stk empty L A regs mem md ra p n Hpre) as Hnb.
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn11 & _).
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig].
  - destruct (Z.eq_dec n 0) as [H0|H0].
    + apply (llvm_early B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      left. rewrite Hn11. rewrite MState.unsigned_lit by lia. exact H0.
    + exact (sr_entry stk empty L A regs mem md ra p n pl b j BI Hk Hra Hpre Hn Hpl Hsn Hsp Hroom Hro ltac:(lia) Hres
               Hfrm).
  - apply (llvm_early B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
    right. rewrite Hn11. rewrite MState.unsigned_lit by lia. exact Hbig.
Qed.

End M.
