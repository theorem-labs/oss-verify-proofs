(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The plain-image walk of the harness body LLVMFuzzerTestOneInput (projects/reac-repacer/fuzz_wire/source/
   fuzz_wire.c:253-282), 0x12d78, 360 bytes, against LLVMFuzzerTestOneInput_c.v's LLVMFuzzerTestOneInput_sr_contract.
   New. Templates (no function ported): reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput.v (6874bc78b1f; the
   skeleton g_pre / g_above / g_run / blk_keep / norm_stk / lf_callee_cases / lf_rw_cells_frame), libreac/fuzz_decode's
   released fd_glue.v / fd_entry.v / fd_exit.v (25e3d17bdb5; the allocator calls at the harness entry: g_malloc, g_free,
   and g_run whose segments may write into a block the walk allocated, lf_mine), this unit's check_copy.v / cc_segs.v.
   `size < 1 || size >= FUZZ_INPUT_MAX` is LLVMFuzzerTestOneInput_early.v's llvm_early. The rest is split at each SR
   call, the straight-line segments are evt proofs bridged to SR by g_run (or llvm_run where no byte is written):
   - e1_evt 0x12d78 -> malloc #1: the frame (64 bytes, ra / s0..s6), n = min (size - 1, W_RECV_MAX), data[0],
     fuzz_dup's malloc(n ? n : 1);
   - e2_evt malloc #1's return 0x12dd8 -> malloc #2: memcpy(f, data + 1, n) (n != 0), check_forward, check_ret,
     check_downstream, check_meter, check_counter, check_width, check_read (their evt contracts), c's malloc. The five
     checks' posts carry no mem_inv, check_width needs it: mem_inv_hi (mem_inv survives a munch of stack bytes);
   - e3_evt malloc #2's return 0x12e60 -> check_copy: memcpy(c, f, n) (n != 0);
   - e4_evt check_copy's return 0x12e8c -> free(c): check_read(c, len, slot) when len != 0; check_copy's post is
     call_post_x (c rewritten), g_cc keeps lf_fr by LLVMFuzzerTestOneInput_fr.v's lf_fr_call_x;
   - e5_evt 0x12ea8 -> free(f); e6_evt 0x12eb0 -> ret: return 0, the saved registers back.
   The `if (!b) abort();` arms of fuzz_dup (0x12dd8, 0x12e60) are dead: malloc's post gives a non-zero block (FuzzDup.v's
   fuzz_dup_no_null).
   rule 24: the released LLVMFuzzerTestOneInput proofs are other programs' entries; written new. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import FrameBytes FuzzDup memcpy_c
  rp_copy_untag_c check_forward_c check_ret_c check_downstream_c check_meter_c check_counter_c check_width_c
  check_read_c check_copy_c cc_segs cc_glue LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_early.
Import ListNotations.
Open Scope Z_scope.

(* ---------------- helpers ---------------- *)

Ltac qreg := split; [first [reflexivity | (simp_regs; f_equal; lia)] |].

(* n = min (size - 1, W_RECV_MAX) *)
Definition wk (n : Z) : Z := Z.min (n - 1) 1600.

Lemma wk_range : forall n, 1 <= n -> 0 <= wk n <= 1600 /\ wk n <= n - 1.
Proof. intros n H. unfold wk. lia. Qed.

(* the early test of fuzz_wire.c:256, not taken *)
Lemma e1_cond : forall u, 1 <= u < 2 ^ 26 ->
  bv_ltu (Z_to_bv 64 (u + -67108864)) (Z_to_bv 64 (-67108863)) = false.
Proof.
  intros u Hu. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Ltac e1_branch u Hu :=
  first [ if_false_by (e1_cond u Hu)
        | lazymatch goal with
          | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
              replace c with false;
              [ cbv iota
              | symmetry; unfold c_ltu, bv_ltu; rewrite ?Z_to_bv_unsigned, ?unsigned_lit_wrap;
                unfold bv_wrap, bv_modulus; apply Z.ltb_ge; Z.div_mod_to_equations; lia ]
          end ].

(* a branch on words whose values lia knows *)
Ltac zcond :=
  unfold c_ltu, c_lts, bv_ltu, bv_lts, bv_leu, bv_eqb, zxb; cbn [negb];
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end;
  fold_lit_ux; solve_cond_rec.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; zcond]
  end.

(* mem_inv survives a munch whose window lies above every loaded segment (the stack) *)
Lemma mem_inv_hi : forall W m m', mem_inv rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> LF_RES_TOP <= x) -> mem_inv rsegs m'.
Proof.
  intros W m m' MI MU HW a b Ha.
  destruct (lf_outside_dec W (bv_unsigned a)) as [O|NO].
  - rewrite (MU a O) in Ha. exact (MI a b Ha).
  - pose proof (u64_range a) as Ra. pose proof (HW (bv_unsigned a) Ra NO) as Hh.
    unfold ro_addr. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
    exfalso. pose proof (lf_find_top (bv_unsigned a) 1 seg E). lia.
Qed.

Lemma en_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x NO. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply NO; cbn [outside]; (split; [lia | exact I]).
Qed.

Lemma en_out2 : forall lo hi lo' hi' x, ~ outside [(lo, hi); (lo', hi')] x -> lo <= x < hi \/ lo' <= x < hi'.
Proof.
  intros lo hi lo' hi' x NO.
  destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); destruct (Z_le_dec lo' x); destruct (Z_lt_dec x hi');
    try lia; exfalso; apply NO; cbn [outside]; (split; [lia | split; [lia | exact I]]).
Qed.

Lemma xget : forall R R' (k : reg) v, Regs6ss.xregs_eqv R R' -> reg_get R k = v -> is_x0 k = false ->
  reg_get R' k = v.
Proof. intros R R' k v Hx H Hk. rewrite <- (Hx k Hk). exact H. Qed.

Lemma lf_callee_cases : forall x, callee_saved x ->
  x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ x = 9 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/
  x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27.
Proof. intros x Hx. unfold callee_saved in Hx. lia. Qed.

Lemma rp_get : forall regs regs' x, regs_preserved regs regs' -> callee_saved x ->
  reg_get regs' (Z_to_bv 5 x) = reg_get regs (Z_to_bv 5 x).
Proof.
  intros regs regs' x Hrp Hx. pose proof (Hrp x Hx) as E.
  destruct (lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    exact E.
Qed.

Lemma cs_nz : forall x, callee_saved x -> is_x0 (Z_to_bv 5 x) = false.
Proof.
  intros x Hx.
  destruct (lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    reflexivity.
Qed.

Lemma lf_getr_cs : forall R x, callee_saved x -> YK11.getr R (Z_to_bv 5 x) = reg_get R (Z_to_bv 5 x).
Proof.
  intros R x Hx.
  destruct (lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    reflexivity.
Qed.

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

Lemma bytes_at_frame : forall m m' A bs,
  bytes_at rsegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> mbyte rsegs m' a = mbyte rsegs m a) ->
  bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs (H0 & H1 & Hb) HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (Hb i Hi).
  change (mrd rsegs m' (wa (A + Z.of_nat i)) = mrd rsegs m (wa (A + Z.of_nat i))).
  exact (HE (A + Z.of_nat i) ltac:(lia)).
Qed.

Lemma blk_bytes_at : forall B m A bs, ms_segs B = rsegs -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  blk_data B m A bs -> bytes_at rsegs m A bs.
Proof.
  intros B m A bs HS H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, HS. reflexivity.
Qed.

Lemma disj_mid : forall b1 x b2 y, pairwise ranges_disjoint (b1 ++ x :: b2) -> In y (b1 ++ b2) ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros b1 x b2 y HP Hin. destruct (pairwise_app_mid _ b1 x b2 y HP Hin) as [H|H];
    unfold ranges_disjoint in H; lia.
Qed.

(* the 8 saved registers of the 64-byte frame, from its base sp up: s6, s5, s4, s3, s2, s1, s0, ra *)
Definition wire_sv (r : bvmap 5 word) : list cell :=
  [C8 (reg_get r 22); C8 (reg_get r 21); C8 (reg_get r 20); C8 (reg_get r 19); C8 (reg_get r 18);
   C8 (reg_get r 9); C8 (reg_get r 8); C8 (reg_get r 1)].

(* ---------------- e1: the entry, 0x12d78 -> malloc #1 ---------------- *)

Definition q1 (F : bvmap 5 word) (fc : bv 32) (gp tp s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (Sp n p : Z) (sv : list cell) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x14484) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12dd8 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 9 = Z_to_bv 64 (wk n) /\ reg_get R 10 = Z_to_bv 64 (fuzz_dup_size (wk n)) /\
    reg_get R 19 = Z_to_bv 64 (fuzz_dup_size (wk n)) /\ reg_get R 20 = Z_to_bv 64 p /\
    reg_get R 22 = Z_to_bv 64 (n - 1) /\
    reg_get R 23 = s7 /\ reg_get R 24 = s8 /\ reg_get R 25 = s9 /\ reg_get R 26 = s10 /\ reg_get R 27 = s11 /\
    munch [(Sp, Sp + 64)] mb m' /\ wmono rsegs mb m' /\ rw_cells rsegs m' Sp sv.

Lemma e1_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p n : Z) (pl : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
    1 <= n < 2 ^ 26 -> n = Z.of_nat (length pl) -> 0 <= p -> bytes_at rsegs m p pl -> p + n <= lo ->
    evt rsegs (q1 F fc gp tp s7 s8 s9 s10 s11 m (bv_unsigned sp + -64) n p
                 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
               s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12d78) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p n pl ST LO H63 Hn Hlen Hp0 HP HPL.
  pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp + -64 + 64)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (u64_range sp) as Rsp.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (wk_range n ltac:(lia)) as Hwk.
  carve_frame 64%nat ST.
  do 13 step.
  e1_branch n Hn.
  do 5 step.
  destruct (Z_lt_le_dec (n - 1) 1600) as [Hk1|Hk1].
  - take true.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (R0 : ov_read_bytes rsegs mm (wa (p + Z.of_nat 0)) 1 = Some [nth 0 pl (Z_to_bv 8 0)])
        by (apply rd1; [assumption | lia]) end.
    do 3 step.
    rewrite fds_eq by lia.
    do 2 step.
    apply evt_done. unfold q1. do 2 eexists.
    split; [reflexivity|].
    replace (wk n) with (n + -1) by (unfold wk; lia).
    do 14 qreg.
    split; [exact MU|]. split; [exact WM | exact FR].
  - take false.
    step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (R0 : ov_read_bytes rsegs mm (wa (p + Z.of_nat 0)) 1 = Some [nth 0 pl (Z_to_bv 8 0)])
        by (apply rd1; [assumption | lia]) end.
    do 3 step.
    rewrite fds_eq by lia.
    do 2 step.
    apply evt_done. unfold q1. do 2 eexists.
    split; [reflexivity|].
    replace (wk n) with 1600 by (unfold wk; lia).
    do 14 qreg.
    split; [exact MU|]. split; [exact WM | exact FR].
Qed.

(* ---------------- e2: malloc #1's return 0x12dd8 -> malloc #2 ---------------- *)

Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac fix_ret := repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n; rewrite (ret_pc_even n) by (first [lia | reflexivity])
  end.

(* the state the seven checks keep: the footprint against the segment's start, the frame, f's n bytes *)
Definition cinv (W : list (Z * Z)) (mb m : word -> option byte) (Sp lo f : Z) (bs : list byte) (sv : list cell)
    : Prop :=
  munch W mb m /\ wmono rsegs mb m /\ mem_inv rsegs m /\ stk rsegs m lo Sp /\ rw_cells rsegs m Sp sv /\
  bytes_at rsegs m f bs.

Lemma cinv_call : forall W mb m m' Sp lo f bs sv X,
  cinv W mb m Sp lo f bs sv ->
  munch [(Sp - X, Sp)] m m' -> wmono rsegs m m' -> stk rsegs m' lo Sp ->
  sub_fp [(Sp - X, Sp)] W -> LF_RES_TOP <= Sp - X -> Sp <= 2 ^ 64 -> f + Z.of_nat (length bs) <= Sp - X ->
  cinv W mb m' Sp lo f bs sv.
Proof.
  intros W mb m m' Sp lo f bs sv X (MU & WM & MI & ST & FR & BF) MU1 WM1 ST1 Hsub Hhi HS Hf.
  split; [exact (munch_trans W mb m m' MU (munch_weaken _ _ m m' Hsub MU1))|].
  split; [exact (wmono_trans rsegs mb m m' WM WM1)|].
  split; [apply (mem_inv_hi [(Sp - X, Sp)] m m' MI MU1); intros x Hx NO; apply en_out1 in NO; lia|].
  split; [exact ST1|].
  split.
  - apply (rw_cells_transport rsegs [(Sp - X, Sp)] m m' Sp sv FR MU1 WM1).
    cbn [disjoint_from]. split; [right; lia | exact I].
  - apply (bytes_at_transport rsegs [(Sp - X, Sp)] m m' f bs BF MU1).
    cbn [disjoint_from]. split; [left; lia | exact I].
Qed.

Definition q2 (F : bvmap 5 word) (fc : bv 32) (gp tp x19 x22 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (Sp f k : Z) (bs : list byte) (sv : list cell) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x14484) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12e60 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 f /\ reg_get R 9 = Z_to_bv 64 k /\ reg_get R 10 = x19 /\ reg_get R 19 = x19 /\
    reg_get R 22 = x22 /\
    reg_get R 23 = s7 /\ reg_get R 24 = s8 /\ reg_get R 25 = s9 /\ reg_get R 26 = s10 /\ reg_get R 27 = s11 /\
    munch [(Sp - 176, Sp); (f, f + k)] mb m' /\ wmono rsegs mb m' /\ rw_cells rsegs m' Sp sv /\
    bytes_at rsegs m' f bs.

Section E2.
Hypothesis CF : check_forward_contract.
Hypothesis CR : check_ret_contract.
Hypothesis CD : check_downstream_contract.
Hypothesis CM : check_meter_contract.
Hypothesis CN : check_counter_contract.
Hypothesis CW : check_width_contract.
Hypothesis CRD : check_read_contract.
Hypothesis MC : memcpy_contract.

Ltac sub_w := intros ?x ?Hx; cbn [outside] in *; split; [lia | exact I].

(* 0x12e00 -> malloc #2: the seven checks on f, n = k *)
Lemma e2_checks :
  forall (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte) (Sp lo f k : Z) (bs : list byte)
         (sv : list cell),
    0 <= lo -> LF_RES_TOP <= lo -> lo + 176 <= Sp -> Sp < 2 ^ 63 -> 0 <= f -> f + k <= lo -> 0 <= k <= 1600 ->
    Z.of_nat (length bs) = k ->
    cinv [(Sp - 176, Sp); (f, f + k)] mb m Sp lo f bs sv ->
    evt rsegs (q2 F fc x3 x4 x19 x22 x23 x24 x25 x26 x27 mb Sp f k bs sv)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 k) x10 x11 x12 x13 x14 x15 x16 x17 x18
               x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12e00) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc mb m Sp lo f k bs sv Hlo0 Hlo LO H63 Hf0 Hfk Hk HL CI.
  (* check_forward (f, n, bcast) *)
  do 4 step.
  pose proof CI as (_ & _ & _ & ST & _ & BF).
  eapply evt_cut.
  { eapply CF with (bs := bs) (lo := lo); usub; try unfold CHECK_FORWARD_FRAME;
      [exact HL | exact BF | exact ST | lia | left; lia]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> & MU1 & WM1 & ST1).
  fix_ret. rewrite unsigned_lit in MU1, ST1 by lia. unfold CHECK_FORWARD_FRAME in MU1.
  pose proof (cinv_call _ _ _ _ _ _ _ _ _ _ CI MU1 WM1 ST1 ltac:(sub_w) ltac:(unfold LF_RES_TOP in *; lia)
    ltac:(lia) ltac:(lia)) as CI1.
  clear CI MU1 WM1 ST1 ST BF.
  (* check_ret (f, n) *)
  do 3 step.
  pose proof CI1 as (_ & _ & _ & ST & _ & BF).
  eapply evt_cut.
  { eapply CR with (bs := bs) (lo := lo); usub; try unfold CHECK_RET_FRAME;
      [exact HL | exact BF | exact ST | lia | left; lia]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MU1 & WM1 & ST1).
  fix_ret. rewrite unsigned_lit in MU1, ST1 by lia. unfold CHECK_RET_FRAME in MU1.
  pose proof (cinv_call _ _ _ _ _ _ _ _ _ _ CI1 MU1 WM1 ST1 ltac:(sub_w) ltac:(unfold LF_RES_TOP in *; lia)
    ltac:(lia) ltac:(lia)) as CI2.
  clear CI1 MU1 WM1 ST1 ST BF.
  (* check_downstream (f, n) *)
  do 3 step.
  pose proof CI2 as (_ & _ & _ & ST & _ & BF).
  eapply evt_cut.
  { eapply CD with (bs := bs) (lo := lo); usub; try unfold CHECK_DOWNSTREAM_FRAME;
      [exact HL | exact BF | exact ST | lia | left; lia]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MU1 & WM1 & ST1).
  fix_ret. rewrite unsigned_lit in MU1, ST1 by lia. unfold CHECK_DOWNSTREAM_FRAME in MU1.
  pose proof (cinv_call _ _ _ _ _ _ _ _ _ _ CI2 MU1 WM1 ST1 ltac:(sub_w) ltac:(unfold LF_RES_TOP in *; lia)
    ltac:(lia) ltac:(lia)) as CI3.
  clear CI2 MU1 WM1 ST1 ST BF.
  (* check_meter (f, n) *)
  do 3 step.
  pose proof CI3 as (_ & _ & _ & ST & _ & BF).
  eapply evt_cut.
  { eapply CM with (bs := bs) (lo := lo); usub; try unfold CHECK_METER_FRAME;
      [exact HL | exact BF | exact ST | lia | left; lia]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU1 & WM1 & ST1).
  fix_ret. rewrite unsigned_lit in MU1, ST1 by lia. unfold CHECK_METER_FRAME in MU1.
  pose proof (cinv_call _ _ _ _ _ _ _ _ _ _ CI3 MU1 WM1 ST1 ltac:(sub_w) ltac:(unfold LF_RES_TOP in *; lia)
    ltac:(lia) ltac:(lia)) as CI4.
  clear CI3 MU1 WM1 ST1 ST BF.
  (* check_counter (f, n) *)
  do 3 step.
  pose proof CI4 as (_ & _ & _ & ST & _ & BF).
  eapply evt_cut.
  { eapply CN with (bs := bs) (lo := lo); usub; try unfold CHECK_COUNTER_FRAME;
      [exact HL | exact BF | exact ST | lia | left; lia]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> & MU1 & WM1 & ST1).
  fix_ret. rewrite unsigned_lit in MU1, ST1 by lia. unfold CHECK_COUNTER_FRAME in MU1.
  pose proof (cinv_call _ _ _ _ _ _ _ _ _ _ CI4 MU1 WM1 ST1 ltac:(sub_w) ltac:(unfold LF_RES_TOP in *; lia)
    ltac:(lia) ltac:(lia)) as CI5.
  clear CI4 MU1 WM1 ST1 ST BF.
  (* check_width (n) *)
  do 2 step.
  pose proof CI5 as (_ & _ & MI & ST & _ & _).
  eapply evt_cut.
  { eapply CW with (lo := lo); usub; try unfold CHECK_WIDTH_STACK, CHECK_WIDTH_FRAME;
      [lia | exact MI | exact ST | lia]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & -> & MU1 & WM1 & _ & ST1).
  fix_ret. rewrite unsigned_lit in MU1, ST1 by lia. unfold CHECK_WIDTH_STACK, CHECK_WIDTH_FRAME in MU1.
  pose proof (cinv_call _ _ _ _ _ _ _ _ _ _ CI5 MU1 WM1 ST1 ltac:(sub_w) ltac:(unfold LF_RES_TOP in *; lia)
    ltac:(lia) ltac:(lia)) as CI6.
  clear CI5 MU1 WM1 ST1 ST MI.
  (* check_read (f, n, slot) *)
  do 4 step.
  pose proof CI6 as (_ & _ & MI & ST & _ & BF).
  eapply evt_cut.
  { eapply CRD with (bs := bs) (lo := lo); usub; try unfold CHECK_READ_STACK;
      [exact MI | exact ST | lia | lia | exact HL | exact BF | left; lia]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & -> & MU1 & WM1 & _ & ST1).
  fix_ret. rewrite unsigned_lit in MU1, ST1 by lia. unfold CHECK_READ_STACK in MU1.
  pose proof (cinv_call _ _ _ _ _ _ _ _ _ _ CI6 MU1 WM1 ST1 ltac:(sub_w) ltac:(unfold LF_RES_TOP in *; lia)
    ltac:(lia) ltac:(lia)) as CI7.
  clear CI6 MU1 WM1 ST1 ST MI BF.
  (* malloc(n ? n : 1) *)
  do 2 step.
  destruct CI7 as (MU & WM & _ & _ & FR & BF).
  apply evt_done. unfold q2. do 2 eexists.
  split; [reflexivity|].
  do 14 qreg.
  split; [exact MU|]. split; [exact WM|]. split; [exact FR | exact BF].
Qed.

Lemma e2_evt :
  forall (x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo p n f : Z) (pl junk : list byte)
         (sv : list cell),
    0 <= lo -> LF_RES_TOP <= lo -> lo + 176 <= Sp -> Sp < 2 ^ 63 ->
    1 <= n < 2 ^ 26 -> n = Z.of_nat (length pl) -> 0 <= p -> p + n <= lo -> bytes_at rsegs m p pl ->
    4096 <= f -> f + fuzz_dup_size (wk n) <= lo -> (f + fuzz_dup_size (wk n) <= p \/ p + n <= f) ->
    (0 < wk n -> rw_cells rsegs m f [CB (Z.to_nat (wk n)) junk]) ->
    mem_inv rsegs m -> stk rsegs m lo Sp -> rw_cells rsegs m Sp sv ->
    evt rsegs (q2 F fc x3 x4 (Z_to_bv 64 (fuzz_dup_size (wk n))) (Z_to_bv 64 (n - 1)) x23 x24 x25 x26 x27 m Sp f
                 (wk n) (firstn (Z.to_nat (wk n)) (skipn 1 pl)) sv)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (wk n)) (Z_to_bv 64 f) x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 (fuzz_dup_size (wk n))) (Z_to_bv 64 p) x21 (Z_to_bv 64 (n - 1)) x23 x24 x25 x26 x27
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x12dd8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp lo p n f pl junk sv Hlo0 Hlo LO H63 Hn Hlen Hp0 HPL HP Hf0 Hfs DSF HO MI ST FR.
  pose proof (wk_range n ltac:(lia)) as Hwk.
  pose proof (fuzz_dup_size_range (wk n) ltac:(lia)) as Hfd.
  pose proof (fds_cases (wk n) ltac:(lia)) as Hfc.
  step. take false.
  do 4 step.
  step.
  destruct (Z.eq_dec n 1) as [N1|N1].
  - (* size = 1: n = 0, no memcpy *)
    take true.
    assert (Ek : wk n = 0) by (unfold wk; lia). rewrite Ek. cbn [Z.to_nat firstn].
    apply (e2_checks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m m Sp lo f 0 [] sv);
      [lia | exact Hlo | lia | lia | lia | lia | lia | reflexivity |].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
    split; [exact FR|]. apply bytes_at_nil. lia.
  - (* memcpy(f, data + 1, n) *)
    take false.
    do 4 step.
    assert (Hk1 : 1 <= wk n) by (unfold wk; lia).
    set (k := wk n) in *.
    set (bs := firstn (Z.to_nat k) (skipn 1 pl)) in *.
    assert (HLb : Z.of_nat (length bs) = k) by (unfold bs; rewrite length_firstn, length_skipn; lia).
    assert (HSRC : bytes_at rsegs m (p + 1) bs).
    { pose proof (bytes_at_mid m p pl 1 (Z.to_nat k) HP ltac:(lia)) as H. change (Z.of_nat 1) with 1 in H. exact H. }
    pose proof (HO ltac:(lia)) as HO1.
    eapply evt_cut.
    { eapply MC with (src := bs) (junk := junk); usub.
      - exact HSRC.
      - rewrite <- (Nat2Z.id (length bs)), HLb. reflexivity.
      - exact HO1.
      - lia.
      - exact MI. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> & MU1 & WM1 & MI1 & CB1 & _).
    fix_ret. rewrite !unsigned_lit in MU1, CB1 by lia.
    pose proof (rw1_bytes m1 f _ bs CB1) as BF1.
    pose proof (stk_transport_disjoint rsegs [(f, f + k)] m m1 lo Sp ST MU1 WM1
      ltac:(cbn [disjoint_from]; split; [right; lia | exact I])) as ST1.
    pose proof (rw_cells_transport rsegs [(f, f + k)] m m1 Sp sv FR MU1 WM1
      ltac:(cbn [disjoint_from]; split; [right; lia | exact I])) as FR1.
    apply (e2_checks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m m1 Sp lo f k bs sv);
      [lia | exact Hlo | lia | lia | lia | lia | lia | exact HLb |].
    split; [apply (munch_weaken [(f, f + k)]); [sub_w | exact MU1]|].
    split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact FR1 | exact BF1].
Qed.

(* ---------------- e3: malloc #2's return 0x12e60 -> check_copy ---------------- *)

Definition q3 (F : bvmap 5 word) (fc : bv 32) (gp tp s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (Sp f c k : Z) (bs : list byte) (sv : list cell) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x13378) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12e8c /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 f /\ reg_get R 10 = Z_to_bv 64 c /\ reg_get R 11 = Z_to_bv 64 f /\
    reg_get R 12 = Z_to_bv 64 k /\ reg_get R 19 = Z_to_bv 64 c /\
    reg_get R 23 = s7 /\ reg_get R 24 = s8 /\ reg_get R 25 = s9 /\ reg_get R 26 = s10 /\ reg_get R 27 = s11 /\
    munch [(c, c + k)] mb m' /\ wmono rsegs mb m' /\ rw_cells rsegs m' Sp sv /\
    bytes_at rsegs m' c bs /\ bytes_at rsegs m' f bs.

Lemma e3_evt :
  forall (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp n f c : Z) (junk bs : list byte)
         (sv : list cell),
    0 <= Sp -> Sp + 64 <= 2 ^ 63 -> 1 <= n < 2 ^ 26 -> Z.of_nat (length bs) = wk n -> 4096 <= f -> 4096 <= c ->
    c + wk n <= Sp -> f + wk n <= Sp -> (f + wk n <= c \/ c + wk n <= f) ->
    (0 < wk n -> rw_cells rsegs m c [CB (Z.to_nat (wk n)) junk]) ->
    mem_inv rsegs m -> bytes_at rsegs m f bs -> rw_cells rsegs m Sp sv ->
    evt rsegs (q3 F fc x3 x4 x23 x24 x25 x26 x27 m Sp f c (wk n) bs sv)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 (wk n)) (Z_to_bv 64 c) x11 x12 x13 x14
               x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 (n - 1)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12e60) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp n f c junk bs sv HSp0 HSp Hn HL Hf Hc Hcs Hfs DCF HO MI BF FR.
  pose proof (wk_range n ltac:(lia)) as Hwk.
  step. take false.
  step. step.
  destruct (Z.eq_dec n 1) as [N1|N1].
  - (* n = 0: no memcpy *)
    take true.
    assert (Ek : wk n = 0) by (unfold wk; lia).
    assert (Eb : bs = []) by (destruct bs; [reflexivity | cbn [length] in HL; lia]). subst bs.
    do 4 step.
    apply evt_done. unfold q3. do 2 eexists.
    split; [reflexivity|].
    do 14 qreg.
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact FR|].
    split; [apply bytes_at_nil; lia | exact BF].
  - (* memcpy(c, f, n) *)
    take false.
    do 4 step.
    assert (Hk1 : 1 <= wk n) by (unfold wk; lia).
    set (k := wk n) in *.
    pose proof (HO ltac:(lia)) as HO1.
    eapply evt_cut.
    { eapply MC with (src := bs) (junk := junk); usub.
      - exact BF.
      - rewrite <- (Nat2Z.id (length bs)), HL. reflexivity.
      - exact HO1.
      - lia.
      - exact MI. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> & MU1 & WM1 & MI1 & CB1 & SB1).
    fix_ret. rewrite !unsigned_lit in MU1, CB1 by lia. rewrite !unsigned_lit in SB1 by lia.
    pose proof (rw1_bytes m1 c _ bs CB1) as BC1.
    pose proof (rw_cells_transport rsegs [(c, c + k)] m m1 Sp sv FR MU1 WM1
      ltac:(cbn [disjoint_from]; split; [right; lia | exact I])) as FR1.
    do 4 step.
    apply evt_done. unfold q3. do 2 eexists.
    split; [reflexivity|].
    do 14 qreg.
    split; [exact MU1|]. split; [exact WM1|]. split; [exact FR1|]. split; [exact BC1 | exact SB1].
Qed.

(* ---------------- e4: check_copy's return 0x12e8c -> free(c) ---------------- *)

Definition q4 (F : bvmap 5 word) (fc : bv 32) (gp tp s0 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (Sp c : Z) (sv : list cell) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x14344) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12ea8 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = s0 /\ reg_get R 10 = Z_to_bv 64 c /\
    reg_get R 23 = s7 /\ reg_get R 24 = s8 /\ reg_get R 25 = s9 /\ reg_get R 26 = s10 /\ reg_get R 27 = s11 /\
    munch [(Sp - 176, Sp)] mb m' /\ wmono rsegs mb m' /\ rw_cells rsegs m' Sp sv.

Lemma e4_evt :
  forall (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo c len : Z) (cb : list byte)
         (sv : list cell),
    0 <= lo -> LF_RES_TOP <= lo -> lo + 176 <= Sp -> Sp < 2 ^ 63 -> 0 <= c -> 0 <= len <= 1600 ->
    len <= Z.of_nat (length cb) -> c + Z.of_nat (length cb) <= lo ->
    mem_inv rsegs m -> stk rsegs m lo Sp -> rw_cells rsegs m Sp sv -> bytes_at rsegs m c cb ->
    evt rsegs (q4 F fc x3 x4 x8 x23 x24 x25 x26 x27 m Sp c sv)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x18
               (Z_to_bv 64 c) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12e8c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp lo c len cb sv Hlo0 Hlo LO H63 Hc0 Hlen Hlc Hcl MI ST FR BC.
  step.
  destruct (Z.eq_dec len 0) as [L0|L0].
  - (* len = 0: no read *)
    take true.
    do 2 step.
    apply evt_done. unfold q4. do 2 eexists.
    split; [reflexivity|].
    do 11 qreg.
    split; [apply munch_refl|]. split; [apply wmono_refl | exact FR].
  - (* check_read (c, len, slot) *)
    take false.
    do 4 step.
    assert (BR : bytes_at rsegs m c (firstn (Z.to_nat len) cb)).
    { pose proof (bytes_at_mid m c cb 0 (Z.to_nat len) BC ltac:(lia)) as H. cbn [skipn Z.of_nat] in H.
      rewrite Z.add_0_r in H. exact H. }
    assert (HLr : Z.of_nat (length (firstn (Z.to_nat len) cb)) = len) by (rewrite length_firstn; lia).
    eapply evt_cut.
    { eapply CRD with (bs := firstn (Z.to_nat len) cb) (lo := lo); usub; try unfold CHECK_READ_STACK;
        [exact MI | exact ST | lia | lia | exact HLr | exact BR | left; lia]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> & MU1 & WM1 & _ & _).
    fix_ret. rewrite unsigned_lit in MU1 by lia. unfold CHECK_READ_STACK in MU1.
    pose proof (rw_cells_transport rsegs [(Sp - 176, Sp)] m m1 Sp sv FR MU1 WM1
      ltac:(cbn [disjoint_from]; split; [right; lia | exact I])) as FR1.
    do 2 step.
    apply evt_done. unfold q4. do 2 eexists.
    split; [reflexivity|].
    do 11 qreg.
    split; [exact MU1|]. split; [exact WM1 | exact FR1].
Qed.

End E2.

(* ---------------- the SR layer: the glue at each call ---------------- *)

(* the registers the walk keeps against the entry: sp at the frame, gp, tp, s7..s11 *)
Definition hk (regs0 regs : bvmap 5 word) : Prop :=
  reg_get regs 2 = Z_to_bv 64 (spZ regs0 - 64) /\ reg_get regs 3 = reg_get regs0 3 /\
  reg_get regs 4 = reg_get regs0 4 /\ reg_get regs 23 = reg_get regs0 23 /\ reg_get regs 24 = reg_get regs0 24 /\
  reg_get regs 25 = reg_get regs0 25 /\ reg_get regs 26 = reg_get regs0 26 /\ reg_get regs 27 = reg_get regs0 27.

Lemma hk_x : forall regs0 R regs', Regs6ss.xregs_eqv R regs' ->
  reg_get R 2 = Z_to_bv 64 (spZ regs0 - 64) -> reg_get R 3 = reg_get regs0 3 -> reg_get R 4 = reg_get regs0 4 ->
  reg_get R 23 = reg_get regs0 23 -> reg_get R 24 = reg_get regs0 24 -> reg_get R 25 = reg_get regs0 25 ->
  reg_get R 26 = reg_get regs0 26 -> reg_get R 27 = reg_get regs0 27 -> hk regs0 regs'.
Proof.
  intros regs0 R regs' Hx H2 H3 H4 H23 H24 H25 H26 H27.
  split; [exact (xget _ _ _ _ Hx H2 eq_refl)|]. split; [exact (xget _ _ _ _ Hx H3 eq_refl)|].
  split; [exact (xget _ _ _ _ Hx H4 eq_refl)|]. split; [exact (xget _ _ _ _ Hx H23 eq_refl)|].
  split; [exact (xget _ _ _ _ Hx H24 eq_refl)|]. split; [exact (xget _ _ _ _ Hx H25 eq_refl)|].
  split; [exact (xget _ _ _ _ Hx H26 eq_refl) | exact (xget _ _ _ _ Hx H27 eq_refl)].
Qed.

Lemma hk_rp : forall regs0 regs regs', hk regs0 regs -> regs_preserved regs regs' -> hk regs0 regs'.
Proof.
  intros regs0 regs regs' (H2 & H3 & H4 & H23 & H24 & H25 & H26 & H27) Hrp.
  split; [exact (eq_trans (rp_get regs regs' 2 Hrp ltac:(unfold callee_saved; lia)) H2)|].
  split; [exact (eq_trans (rp_get regs regs' 3 Hrp ltac:(unfold callee_saved; lia)) H3)|].
  split; [exact (eq_trans (rp_get regs regs' 4 Hrp ltac:(unfold callee_saved; lia)) H4)|].
  split; [exact (eq_trans (rp_get regs regs' 23 Hrp ltac:(unfold callee_saved; lia)) H23)|].
  split; [exact (eq_trans (rp_get regs regs' 24 Hrp ltac:(unfold callee_saved; lia)) H24)|].
  split; [exact (eq_trans (rp_get regs regs' 25 Hrp ltac:(unfold callee_saved; lia)) H25)|].
  split; [exact (eq_trans (rp_get regs regs' 26 Hrp ltac:(unfold callee_saved; lia)) H26)|].
  exact (eq_trans (rp_get regs regs' 27 Hrp ltac:(unfold callee_saved; lia)) H27).
Qed.

Lemma hk_sp : forall regs0 regs, hk regs0 regs -> 64 <= spZ regs0 < 2 ^ 64 -> spZ regs = spZ regs0 - 64.
Proof.
  intros regs0 regs (H2 & _) H. assert (E : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  rewrite E, H2. apply unsigned_lit. lia.
Qed.

Lemma rp_sv : forall regs regs' x v, regs_preserved regs regs' -> callee_saved x ->
  reg_get regs (Z_to_bv 5 x) = v -> reg_get regs' (Z_to_bv 5 x) = v.
Proof. intros regs regs' x v Hrp Hx H. rewrite (rp_get regs regs' x Hrp Hx). exact H. Qed.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
(* the allocator facts and the callees' contracts, in LLVMFuzzerTestOneInput_link.v's order *)
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

Section G.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis HGG : ms_got_guard B = LLVM_GUARD_GOT.
Hypothesis HMAL : ms_malloc B = LLVM_MALLOC.
Hypothesis HFRE : ms_free B = LLVM_FREE.

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

(* a segment may write the stack window and the blocks the walk allocated (lf_mine) *)
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

(* check_copy (c, f, n): its post is call_post_x, the block c released (lf_fr_call_x) *)
Lemma g_cc : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A c f k kc bs bres
    (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 c -> YK11.getr regs 11 = Z_to_bv 64 f -> YK11.getr regs 12 = Z_to_bv 64 k ->
  k <= 1600 -> Z.of_nat (length bs) = k -> In (c, kc) (blocks L A) -> k <= kc ->
  (exists qf kf, In (qf, kf) (blocks L A) /\ qf <> c /\ qf <= f /\ f + k <= qf + kf) ->
  bytes_at rsegs mem c bs -> bytes_at rsegs mem f bs ->
  (forall a j, In (a, j) (blocks L0 A0) -> a <> c) ->
  frm_zero (@fp_csr fx') -> res_ok_slots A bres -> room_slots bres (fuzz_dup_size k) ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') -> lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 (copy_untag_result k bs) ->
     bytes_at rsegs mem' c (cu_bytes k bs) -> blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_COPY) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A c f k kc bs bres P FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 Hk Hlen Hinc Hkc Hinf BC BF Hnc Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply SR_bind.
  { apply (CC fx' L A regs mem md c f k kc bs bres SEGS).
    - exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs CC_STACK FR Hra Hal H1 H2
        ltac:(unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact HID.
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hk.
    - exact Hlen.
    - exact Hinc.
    - exact Hkc.
    - exact Hinf.
    - rewrite SEGS. exact BC.
    - rewrite SEGS. exact BF.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & G210 & BC2 & Eb & Hkept & Hgk & Hro2 & Hres2
    & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call_x B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK in *; lia | lia | | | exact Hidt | | ].
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (Hnc a0 k0 Hin) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp G210).
  - rewrite <- SEGS. exact BC2.
  - exact Eb.
  - exact Hres2.
  - exact (g_above_x stk S L A regs mem md CC_STACK (fun a => a = c) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
      ltac:(unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK; lia)).
Qed.

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

(* a block of the allocator, as one writable cell of the normalized memory *)
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

(* the facts of a block of the allocator the walk uses *)
Lemma blk_range : forall L A mem md x n, aa_MR API L A mem md -> In (x, n) (blocks L A) ->
  4096 <= x /\ x + n <= YM05.alloc_ceiling.
Proof.
  intros L A mem md x n HM Hin. apply blocks_In in Hin as (q & Hq & Hqin).
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q n HM Hqin) as (R1 & R2). rewrite Hq in R1, R2. lia.
Qed.

(* two blocks at different addresses do not overlap *)
Lemma blk_disj : forall L A mem md x y kx ky, aa_MR API L A mem md -> In (x, kx) (blocks L A) ->
  In (y, ky) (blocks L A) -> x <> y -> x + kx <= y \/ y + ky <= x.
Proof.
  intros L A mem md x y kx ky HM Hx Hy N.
  pose proof (ccg_pw_two (blocks L A) (x, kx) (y, ky) (mr_blocks_disjoint B _ (aa_laws API) L A mem md HM) Hx Hy N)
    as D. unfold ranges_disjoint in D. cbn [fst snd] in D. exact D.
Qed.

(* bytes of a block kept by a call whose post is blocks_kept *)
Lemma bk_bytes : forall L A mem mem' gone x k bs, blocks_kept B L A mem mem' gone -> In (x, k) (blocks L A) ->
  ~ gone x -> Z.of_nat (length bs) <= k -> bytes_at rsegs mem x bs -> bytes_at rsegs mem' x bs.
Proof.
  intros L A mem mem' gone x k bs HK Hin Hg Hl BA. apply (bytes_at_frame mem mem' x bs BA).
  intros a Ha. replace a with (x + (a - x)) by lia. rewrite <- SEGS. apply (HK x k (a - x) Hin Hg). lia.
Qed.

(* ---------------- the phases, from the last call back to the entry ---------------- *)

Section Run.
Variables (stk empty : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
  (md0 : Model) (ra p n : Z) (b : sbound) (j : nat).
Hypothesis Hk : LLVM_K <= stk.
Hypothesis Hra : YK0s.ret_ok (Z_to_bv 64 ra).
Hypothesis Hpre : lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n.
Hypothesis Hsn : sink_none B mem0 md0.
Hypothesis Hroom : llvm_room b.

Ltac run_env :=
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra0 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn0
    & Hpl0 & Hrod0);
  pose proof Hk as Hk'; unfold LLVM_K, LLVM_FRAME, CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK in Hk';
  pose proof YM05.alloc_ceiling_value as Hac; pose proof lf_ceiling as Hrt; unfold LF_RES_TOP in Hrt.

Lemma sp16 : forall x, x mod 16 = 0 -> (x - 64) mod 16 = 0.
Proof. intros x H. replace (x - 64) with (x + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact H. Qed.

(* 0x12ea8 (free(c) returned) -> free(f) -> return 0 *)
Lemma sr_tail : forall (fx' : YK11.FPState) regs mem md L A f s,
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md -> frm_zero (@fp_csr fx') -> hk regs0 regs ->
  reg_get regs 8 = Z_to_bv 64 f -> rw_cells rsegs mem (spZ regs0 - 64) (wire_sv regs0) ->
  In (f, s) (blocks L A) -> 0 < s -> (forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + s <= a) ->
  res_ok_slots A (sb_malloc b s) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12ea8) mem (YK11.seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).
Proof.
  intros fx' regs mem md L A f s FR Hfrm HK G8 RW Hin Hs Hmine Hres.
  run_env.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  (* mv a0, s0; jal free *)
  apply (llvm_run fx' regs (Z_to_bv 64 0x12ea8) mem md
    (fun ms => exists R, ms = MS R (@fp_regs fx') (Z_to_bv 64 0x14344) (@fp_csr fx') None mem (seg_rom rsegs) /\
       reg_get R 1 = Z_to_bv 64 0x12eb0 /\ reg_get R 10 = reg_get regs 8 /\
       forall x, callee_saved x -> reg_get R (Z_to_bv 5 x) = reg_get regs (Z_to_bv 5 x)));
    [exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of. do 2 step. apply evt_done. eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    intros x Hx. destruct (lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      reflexivity. }
  { intros ms (R & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R' & HE & H1 & H10 & Hcs) regs1 Hx.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  assert (G11 : YK11.getr regs1 1 = Z_to_bv 64 0x12eb0) by (rewrite (lf_getr_eqv _ _ _ Hx); exact H1).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 f).
  { rewrite (lf_getr_eqv _ _ _ Hx). change (reg_get R' 10 = Z_to_bv 64 f). rewrite H10. exact G8. }
  assert (Hcs1 : forall x, callee_saved x -> reg_get regs1 (Z_to_bv 5 x) = reg_get regs (Z_to_bv 5 x)).
  { intros x Hx1. rewrite <- (Hx _ (cs_nz x Hx1)). exact (Hcs x Hx1). }
  assert (HK1 : hk regs0 regs1) by (apply (hk_rp regs0 regs regs1 HK); intros x Hx1; rewrite !lf_getr_cs by exact Hx1;
    exact (Hcs1 x Hx1)).
  pose proof (hk_sp regs0 regs1 HK1 ltac:(lia)) as Hsp1.
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)).
  { destruct HK1 as (_ & _ & E4 & _). change (reg_get regs1 4 = Z_to_bv 64 (ms_tp B)). rewrite E4. exact Htp0. }
  rewrite <- SEGS. change (Z_to_bv 64 0x14344) with (Z_to_bv 64 LLVM_FREE).
  eapply (g_free stk (spZ regs0) L0 A0 mem0 md0 _ regs1 mem md L A f s (sb_malloc b s));
    [exact FR | lia | lia | rewrite G11; apply ret_ok_even; reflexivity | rewrite Hsp1; apply sp16; exact Hal0
    | rewrite Hsp1; unfold ALLOC_STACK; lia | rewrite Hsp1; lia | rewrite Hsp1; lia | exact Htp1 | exact G110
    | exact Hin | exact Hs | exact Hmine | exact Hres | ].
  intros L2 A2 regs2 mem2 md2 FR2 Hrp2 _ Hres2 Habove2 _.
  pose proof FR2 as (HM2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro2).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  pose proof (hk_rp regs0 regs1 regs2 HK1 Hrp2) as (E2 & E3 & E4 & E23 & E24 & E25 & E26 & E27).
  assert (RW2 : rw_cells rsegs mem2 (spZ regs0 - 64) (wire_sv regs0)).
  { apply (lf_rw_cells_frame mem mem2 _ _ RW). intros a Ha.
    change (Z.of_nat (cells_size (wire_sv regs0))) with 64 in Ha. rewrite <- SEGS. apply Habove2. lia. }
  rewrite G11, SEGS.
  remember (spZ regs0) as S eqn:ES.
  apply (llvm_run (mkFP (@fp_regs fx') (@fp_csr fx')) regs2 (Z_to_bv 64 0x12eb0) mem2 md2
    (fun ms => exists R2, ms = MS R2 (@fp_regs fx') (ret_pc (YK11.getr regs0 1)) (@fp_csr fx') None mem2
                              (YK11.seg_rom rsegs) /\
       reg_get R2 10 = Z_to_bv 64 0 /\
       forall x, callee_saved x -> reg_get R2 (Z_to_bv 5 x) = YK11.getr regs0 (Z_to_bv 5 x)));
    [exact Hh2 | exact Hl2 | | | ].
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E23, E24, E25, E26, E27. unfold wire_sv in RW2.
    do 11 step.
    apply evt_done. eexists. split; [reflexivity|]. split; [reflexivity|].
    intros x Hx2. destruct (lf_callee_cases x Hx2) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      try reflexivity.
    cbn. replace (S - 64 + 64) with S by lia. subst S. unfold spZ. apply Z_to_bv_bv_unsigned. }
  { intros ms (R2 & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R2 & HE & H10' & Hcs') regs3 Hx3.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  apply SR_ret. subst S.
  assert (G10' : YK11.getr regs3 10 = Z_to_bv 64 0) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact H10').
  assert (RP : regs_preserved regs0 regs3).
  { intros x Hx4. rewrite (lf_getr_eqv _ _ _ Hx3), lf_getr_cs by exact Hx4. exact (Hcs' x Hx4). }
  destruct (lf_post B API SINK stk empty L0 A0 regs0 mem0 md0 ra p n L2 A2 regs3 mem2 md2 Hpre Hsn FR2 G10' RP)
    as (Hpost2 & Hsn' & Hpay & MI2).
  exists (mkFP (@fp_regs fx') (@fp_csr fx')), L2, A2, regs3, mem2, md2.
  split; [rewrite Hra0, (lf_ret_pc _ Hra), SEGS; reflexivity|].
  split; [exact Hfrm|]. split; [exact Hpost2|]. split; [exact Hsn'|].
  split; [rewrite sb_free_malloc in Hres2; exact Hres2|].
  split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.

Ltac q_out1 :=
  let ms := fresh "ms" in let HQ := fresh "HQ" in
  intros ms HQ; destruct HQ as (?R & ?m' & -> & HQ);
  repeat match type of HQ with _ /\ _ => let H := fresh "QQ" in destruct HQ as [H HQ] end.

(* 0x12e8c (check_copy returned len) -> check_read (c, len, slot) when len != 0 -> free(c) -> sr_tail *)
Lemma sr_cc_ret : forall (fx' : YK11.FPState) regs mem md L A f c k bs s,
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md -> frm_zero (@fp_csr fx') -> hk regs0 regs ->
  reg_get regs 8 = Z_to_bv 64 f -> reg_get regs 19 = Z_to_bv 64 c ->
  reg_get regs 10 = Z_to_bv 64 (copy_untag_result k bs) ->
  rw_cells rsegs mem (spZ regs0 - 64) (wire_sv regs0) ->
  bytes_at rsegs mem c (cu_bytes k bs) -> Z.of_nat (length bs) = k -> 0 <= k <= 1600 -> k <= s ->
  In (c, s) (blocks L A) -> In (f, s) (blocks L A) -> c <> f -> 0 < s ->
  (forall a q, In (a, q) (blocks L0 A0) -> a + q <= c \/ c + s <= a) ->
  (forall a q, In (a, q) (blocks L0 A0) -> a + q <= f \/ f + s <= a) ->
  res_ok_slots A (sb_malloc (sb_malloc b s) s) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12e8c) mem (YK11.seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).
Proof.
  intros fx' regs mem md L A f c k bs s FR Hfrm HK G8 G19 G10 RW BC HL Hk16 Hks Hinc Hinf Hcf Hs Hmc Hmf Hres.
  run_env.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  pose proof (blk_range L A mem md c s HM Hinc) as (Rc1 & Rc2).
  pose proof (got_le k bs ltac:(lia)) as Hlen.
  pose proof (cu_bytes_len k bs HL) as HLc.
  pose proof HK as (G2 & G3 & G4 & G23 & G24 & G25 & G26 & G27).
  rewrite SEGS.
  eapply g_run with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (Q := q4 (@fp_regs fx') (@fp_csr fx') (reg_get regs0 3) (reg_get regs0 4) (reg_get regs 8) (reg_get regs0 23)
            (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) (normalize rsegs mem)
            (spZ regs0 - 64) c (wire_sv regs0));
    [exact FR | lia | lia | | | ].
  { unfold Regs6ss.mkR_of. rewrite G2, G3, G4, G10, G19, G23, G24, G25, G26, G27.
    apply (e4_evt CRD) with (lo := spZ regs0 - stk) (cb := cu_bytes k bs).
    - lia.
    - unfold LF_RES_TOP. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite HLc. lia.
    - rewrite HLc. lia.
    - apply mem_inv_normalize.
    - apply (norm_stk mem (spZ regs0 - stk) (spZ regs0 - 64) Hro); [unfold LF_RES_TOP; lia | lia |].
      intros a Ha. apply Hstw. lia.
    - apply (lf_rw_cells_norm B mem _ _ SEGS Hro); [|exact RW].
      intros i Hi Himg0. pose proof (lf_in_img_top B _ SEGS Himg0). unfold LF_RES_TOP in *. lia.
    - apply bytes_at_normalize; [exact Hro | exact BC]. }
  { q_out1.
    exists R, (@fp_regs fx'), (Z_to_bv 64 0x14344), (@fp_csr fx'), m', [(spZ regs0 - 64 - 176, spZ regs0 - 64)].
    split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    intros x Hx NO. left. apply en_out1 in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & HE & Q1 & Q2 & Q3 & Q4 & Q8 & Q10 & Q23 & Q24 & Q25 & Q26 & Q27 & MU & WM & RWq).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  pose proof (hk_x regs0 R regs1 Hx Q2 Q3 Q4 Q23 Q24 Q25 Q26 Q27) as HK1.
  assert (G11 : YK11.getr regs1 1 = Z_to_bv 64 0x12ea8) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Q1).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 c) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Q10).
  assert (E18 : reg_get regs1 8 = Z_to_bv 64 f) by exact (eq_trans (xget _ _ _ _ Hx Q8 eq_refl) G8).
  pose proof (hk_sp regs0 regs1 HK1 ltac:(lia)) as Hsp1.
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)).
  { destruct HK1 as (_ & _ & E4 & _). change (reg_get regs1 4 = Z_to_bv 64 (ms_tp B)). rewrite E4. exact Htp0. }
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel RWq) as RW1.
  rewrite <- SEGS. change (Z_to_bv 64 0x14344) with (Z_to_bv 64 LLVM_FREE).
  eapply (g_free stk (spZ regs0) L0 A0 mem0 md0 _ regs1 m1 md L A c s (sb_malloc (sb_malloc b s) s));
    [exact FR1 | lia | lia | rewrite G11; apply ret_ok_even; reflexivity | rewrite Hsp1; apply sp16; exact Hal0
    | rewrite Hsp1; unfold ALLOC_STACK; lia | rewrite Hsp1; lia | rewrite Hsp1; lia | exact Htp1 | exact G110
    | exact Hinc | exact Hs | exact Hmc | exact Hres | ].
  intros L2 A2 regs2 mem2 md2 FR2 Hrp2 (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 _.
  rewrite G11.
  pose proof (hk_rp regs0 regs1 regs2 HK1 Hrp2) as HK2.
  assert (G28 : reg_get regs2 8 = Z_to_bv 64 f) by exact (rp_sv regs1 regs2 8 _ Hrp2 ltac:(unfold callee_saved; lia) E18).
  assert (RW2 : rw_cells rsegs mem2 (spZ regs0 - 64) (wire_sv regs0)).
  { apply (lf_rw_cells_frame m1 mem2 _ _ RW1). intros a Ha.
    change (Z.of_nat (cells_size (wire_sv regs0))) with 64 in Ha. rewrite <- SEGS. apply Habove2. lia. }
  assert (Hinf2 : In (f, s) (blocks L2 A2)).
  { rewrite Eb2. apply (ccg_in_del b1 b2 (c, s) (f, s)); [rewrite <- Eb1; exact Hinf |].
    intros E. apply Hcf. congruence. }
  rewrite sb_free_malloc in Hres2.
  exact (sr_tail (mkFP (@fp_regs fx') (@fp_csr fx')) regs2 mem2 md2 L2 A2 f s FR2 Hfrm HK2 G28 RW2 Hinf2 Hs Hmf
    Hres2).
Qed.

(* 0x12e60 (malloc #2 returned c) -> memcpy(c, f, n) -> check_copy -> sr_cc_ret *)
Lemma sr_mid2 : forall (fx' : YK11.FPState) regs mem md L A f c bs,
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md -> frm_zero (@fp_csr fx') -> hk regs0 regs ->
  reg_get regs 8 = Z_to_bv 64 f -> reg_get regs 9 = Z_to_bv 64 (wk n) -> reg_get regs 10 = Z_to_bv 64 c ->
  reg_get regs 22 = Z_to_bv 64 (n - 1) -> 1 <= n < 2 ^ 26 ->
  rw_cells rsegs mem (spZ regs0 - 64) (wire_sv regs0) ->
  bytes_at rsegs mem f bs -> Z.of_nat (length bs) = wk n ->
  In (c, fuzz_dup_size (wk n)) (blocks L A) -> In (f, fuzz_dup_size (wk n)) (blocks L A) -> c <> f ->
  (forall a q, In (a, q) (blocks L0 A0) -> a + q <= c \/ c + fuzz_dup_size (wk n) <= a) ->
  (forall a q, In (a, q) (blocks L0 A0) -> a + q <= f \/ f + fuzz_dup_size (wk n) <= a) ->
  (forall a q, In (a, q) (blocks L0 A0) -> a <> c) ->
  res_ok_slots A (sb_malloc (sb_malloc b (fuzz_dup_size (wk n))) (fuzz_dup_size (wk n))) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12e60) mem (YK11.seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).
Proof.
  intros fx' regs mem md L A f c bs FR Hfrm HK G8 G9 G10 G22 Hn1 RW BF HL Hinc Hinf Hcf Hmc Hmf Hnc Hres.
  run_env.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  pose proof (wk_range n ltac:(lia)) as Hwk.
  pose proof (fds_cases (wk n) ltac:(lia)) as Hfc.
  pose proof (blk_range L A mem md c _ HM Hinc) as (Rc1 & Rc2).
  pose proof (blk_range L A mem md f _ HM Hinf) as (Rf1 & Rf2).
  pose proof (blk_disj L A mem md f c _ _ HM Hinf Hinc (fun E => Hcf (eq_sym E))) as DCF.
  pose proof Hroom as (Hr1 & Hr2 & Hr3).
  assert (JK : exists junk, 0 < wk n -> rw_cells rsegs (normalize rsegs mem) c [CB (Z.to_nat (wk n)) junk]).
  { destruct (Z_lt_le_dec 0 (wk n)) as [Hk0|Hk0].
    - destruct (norm_blk L A mem md c _ HM Hinc ltac:(lia) Hro) as [junk HJ].
      exists junk. intros _. replace (wk n) with (fuzz_dup_size (wk n)) by lia. exact HJ.
    - exists []. intros H. lia. }
  destruct JK as [junk HO].
  pose proof HK as (G2 & G3 & G4 & G23 & G24 & G25 & G26 & G27).
  rewrite SEGS.
  eapply g_run with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (Q := q3 (@fp_regs fx') (@fp_csr fx') (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 23) (reg_get regs0 24)
            (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) (normalize rsegs mem) (spZ regs0 - 64) f c (wk n)
            bs (wire_sv regs0));
    [exact FR | lia | lia | | | ].
  { unfold Regs6ss.mkR_of. rewrite G2, G3, G4, G8, G9, G10, G22, G23, G24, G25, G26, G27.
    apply (e3_evt MC) with (junk := junk).
    - lia.
    - lia.
    - exact Hn1.
    - exact HL.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact HO.
    - apply mem_inv_normalize.
    - apply bytes_at_normalize; [exact Hro | exact BF].
    - apply (lf_rw_cells_norm B mem _ _ SEGS Hro); [|exact RW].
      intros i Hi Himg0. pose proof (lf_in_img_top B _ SEGS Himg0). unfold LF_RES_TOP in *. lia. }
  { q_out1.
    exists R, (@fp_regs fx'), (Z_to_bv 64 0x13378), (@fp_csr fx'), m', [(c, c + wk n)].
    split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    intros x Hx NO. apply en_out1 in NO. right. exists c, (fuzz_dup_size (wk n)).
    split; [split; [exact Hinc | split; [lia | exact Hmc]] | lia]. }
  intros R F pc' fc m0' HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & HE & Q1 & Q2 & Q3 & Q4 & Q8 & Q10 & Q11 & Q12 & Q19 & Q23 & Q24 & Q25 & Q26 & Q27 & MU & WM
    & RWq & BCq & BFq).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  pose proof (hk_x regs0 R regs1 Hx Q2 Q3 Q4 Q23 Q24 Q25 Q26 Q27) as HK1.
  assert (G11 : YK11.getr regs1 1 = Z_to_bv 64 0x12e8c) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Q1).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 c) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Q10).
  assert (G111 : YK11.getr regs1 11 = Z_to_bv 64 f) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Q11).
  assert (G112 : YK11.getr regs1 12 = Z_to_bv 64 (wk n)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Q12).
  assert (E18 : reg_get regs1 8 = Z_to_bv 64 f) by exact (xget _ _ _ _ Hx Q8 eq_refl).
  assert (E119 : reg_get regs1 19 = Z_to_bv 64 c) by exact (xget _ _ _ _ Hx Q19 eq_refl).
  pose proof (hk_sp regs0 regs1 HK1 ltac:(lia)) as Hsp1.
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)).
  { destruct HK1 as (_ & _ & E4 & _). change (reg_get regs1 4 = Z_to_bv 64 (ms_tp B)). rewrite E4. exact Htp0. }
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel RWq) as RW1.
  pose proof (proj2 (bytes_at_rel rsegs m1 m0' c bs Hrel) BCq) as BC1.
  pose proof (proj2 (bytes_at_rel rsegs m1 m0' f bs Hrel) BFq) as BF1.
  rewrite <- SEGS. change (Z_to_bv 64 0x13378) with (Z_to_bv 64 CHECK_COPY).
  eapply (g_cc stk (spZ regs0) L0 A0 mem0 md0 _ regs1 m1 md L A c f (wk n) (fuzz_dup_size (wk n)) bs
    (sb_malloc (sb_malloc b (fuzz_dup_size (wk n))) (fuzz_dup_size (wk n))));
    [exact FR1 | lia | lia | rewrite G11; apply ret_ok_even; reflexivity | rewrite Hsp1; apply sp16; exact Hal0
    | rewrite Hsp1; unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK; lia | rewrite Hsp1; lia | rewrite Hsp1; lia
    | exact Htp1 | exact G110 | exact G111 | exact G112 | lia | exact HL | exact Hinc | lia | | exact BC1 | exact BF1
    | exact Hnc | exact Hfrm | exact Hres | | ].
  { exists f, (fuzz_dup_size (wk n)). split; [exact Hinf|]. split; [intros E; apply Hcf; symmetry; exact E | lia]. }
  { apply fuzz_dup_room; unfold sb_malloc; cbn [sb_live sb_bytes sb_cap]; unfold CAPMAX in *; lia. }
  intros fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp2 G210 BC2 Eb Hres2 Habove2.
  rewrite G11.
  pose proof (hk_rp regs0 regs1 regs2 HK1 Hrp2) as HK2.
  assert (G28 : reg_get regs2 8 = Z_to_bv 64 f) by exact (rp_sv regs1 regs2 8 _ Hrp2 ltac:(unfold callee_saved; lia) E18).
  assert (G219 : reg_get regs2 19 = Z_to_bv 64 c)
    by exact (rp_sv regs1 regs2 19 _ Hrp2 ltac:(unfold callee_saved; lia) E119).
  assert (RW2 : rw_cells rsegs mem2 (spZ regs0 - 64) (wire_sv regs0)).
  { apply (lf_rw_cells_frame m1 mem2 _ _ RW1). intros a Ha.
    change (Z.of_nat (cells_size (wire_sv regs0))) with 64 in Ha. rewrite <- SEGS. apply Habove2. lia. }
  eapply (sr_cc_ret fx2 regs2 mem2 md2 L2 A2 f c (wk n) bs (fuzz_dup_size (wk n)));
    [exact FR2 | exact Hfrm2 | exact HK2 | exact G28 | exact G219 | exact G210 | exact RW2 | exact BC2 | exact HL
    | lia | lia | rewrite Eb; exact Hinc | rewrite Eb; exact Hinf | exact Hcf | lia | exact Hmc | exact Hmf
    | exact Hres2].
Qed.

(* 0x12dd8 (malloc #1 returned f) -> memcpy(f, data + 1, n), the seven checks -> malloc #2 -> sr_mid2 *)
Lemma sr_mid1 : forall (fx' : YK11.FPState) regs mem md L A f pl,
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md -> frm_zero (@fp_csr fx') -> hk regs0 regs ->
  reg_get regs 9 = Z_to_bv 64 (wk n) -> reg_get regs 10 = Z_to_bv 64 f ->
  reg_get regs 19 = Z_to_bv 64 (fuzz_dup_size (wk n)) -> reg_get regs 20 = Z_to_bv 64 p ->
  reg_get regs 22 = Z_to_bv 64 (n - 1) -> 1 <= n < 2 ^ 26 -> n = Z.of_nat (length pl) -> blk_data B mem0 p pl ->
  rw_cells rsegs mem (spZ regs0 - 64) (wire_sv regs0) ->
  In (f, fuzz_dup_size (wk n)) (blocks L A) ->
  (forall a q, In (a, q) (blocks L0 A0) -> a + q <= f \/ f + fuzz_dup_size (wk n) <= a) ->
  res_ok_slots A (sb_malloc b (fuzz_dup_size (wk n))) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12dd8) mem (YK11.seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).
Proof.
  intros fx' regs mem md L A f pl FR Hfrm HK G9 G10 G19 G20 G22 Hn1 Hn Hpd RW Hinf Hmf Hres.
  run_env.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  pose proof (wk_range n ltac:(lia)) as Hwk.
  pose proof (fds_cases (wk n) ltac:(lia)) as Hfc.
  pose proof (blk_range L A mem md f _ HM Hinf) as (Rf1 & Rf2).
  pose proof Hroom as (Hr1 & Hr2 & Hr3).
  assert (PAY : In (p, n) (blocks L0 A0) /\ 4096 <= p /\ p + n <= YM05.alloc_ceiling).
  { destruct Hpl0 as [[E _] | [_ (q & Hq & Hqp)]]; [lia|].
    pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM0 Hq) as (R1 & R2). rewrite Hqp in R1, R2.
    split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia. }
  destruct PAY as (Hpin & Hp1 & Hp2).
  assert (HPD : blk_data B mem p pl).
  { apply (blk_keep stk (spZ regs0) L0 A0 mem0 md0 L A mem md p pl FR); [rewrite <- Hn; exact Hpin | exact Hpd]. }
  assert (HP : bytes_at rsegs (normalize rsegs mem) p pl).
  { apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact HPD]. }
  pose proof (Hmf p n Hpin) as DSF.
  assert (JK : exists junk, 0 < wk n -> rw_cells rsegs (normalize rsegs mem) f [CB (Z.to_nat (wk n)) junk]).
  { destruct (Z_lt_le_dec 0 (wk n)) as [Hk0|Hk0].
    - destruct (norm_blk L A mem md f _ HM Hinf ltac:(lia) Hro) as [junk HJ].
      exists junk. intros _. replace (wk n) with (fuzz_dup_size (wk n)) by lia. exact HJ.
    - exists []. intros H. lia. }
  destruct JK as [junk HO].
  pose proof HK as (G2 & G3 & G4 & G23 & G24 & G25 & G26 & G27).
  rewrite SEGS.
  eapply g_run with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (Q := q2 (@fp_regs fx') (@fp_csr fx') (reg_get regs0 3) (reg_get regs0 4) (Z_to_bv 64 (fuzz_dup_size (wk n)))
            (Z_to_bv 64 (n - 1)) (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26)
            (reg_get regs0 27) (normalize rsegs mem) (spZ regs0 - 64) f (wk n)
            (firstn (Z.to_nat (wk n)) (skipn 1 pl)) (wire_sv regs0));
    [exact FR | lia | lia | | | ].
  { unfold Regs6ss.mkR_of. rewrite G2, G3, G4, G9, G10, G19, G20, G22, G23, G24, G25, G26, G27.
    apply (e2_evt CF CR CD CM CN CW CRD MC) with (lo := spZ regs0 - stk) (pl := pl) (junk := junk).
    - lia.
    - unfold LF_RES_TOP. lia.
    - lia.
    - lia.
    - exact Hn1.
    - exact Hn.
    - lia.
    - lia.
    - exact HP.
    - lia.
    - lia.
    - lia.
    - exact HO.
    - apply mem_inv_normalize.
    - apply (norm_stk mem (spZ regs0 - stk) (spZ regs0 - 64) Hro); [unfold LF_RES_TOP; lia | lia |].
      intros a Ha. apply Hstw. lia.
    - apply (lf_rw_cells_norm B mem _ _ SEGS Hro); [|exact RW].
      intros i Hi Himg0. pose proof (lf_in_img_top B _ SEGS Himg0). unfold LF_RES_TOP in *. lia. }
  { q_out1.
    exists R, (@fp_regs fx'), (Z_to_bv 64 0x14484), (@fp_csr fx'), m',
      [(spZ regs0 - 64 - 176, spZ regs0 - 64); (f, f + wk n)].
    split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    intros x Hx NO. apply en_out2 in NO. destruct NO as [NO|NO]; [left; lia | right].
    exists f, (fuzz_dup_size (wk n)). split; [split; [exact Hinf | split; [lia | exact Hmf]] | lia]. }
  intros R F pc' fc m0' HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & HE & Q1 & Q2 & Q3 & Q4 & Q8 & Q9 & Q10 & Q19 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & MU & WM
    & RWq & BFq).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  set (bs := firstn (Z.to_nat (wk n)) (skipn 1 pl)) in *.
  assert (HLb : Z.of_nat (length bs) = wk n) by (unfold bs; rewrite length_firstn, length_skipn; lia).
  pose proof (hk_x regs0 R regs1 Hx Q2 Q3 Q4 Q23 Q24 Q25 Q26 Q27) as HK1.
  assert (G11 : YK11.getr regs1 1 = Z_to_bv 64 0x12e60) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Q1).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 (fuzz_dup_size (wk n)))
    by (rewrite (lf_getr_eqv _ _ _ Hx); exact Q10).
  assert (E18 : reg_get regs1 8 = Z_to_bv 64 f) by exact (xget _ _ _ _ Hx Q8 eq_refl).
  assert (E19 : reg_get regs1 9 = Z_to_bv 64 (wk n)) by exact (xget _ _ _ _ Hx Q9 eq_refl).
  assert (E122 : reg_get regs1 22 = Z_to_bv 64 (n - 1)) by exact (xget _ _ _ _ Hx Q22 eq_refl).
  pose proof (hk_sp regs0 regs1 HK1 ltac:(lia)) as Hsp1.
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)).
  { destruct HK1 as (_ & _ & E4 & _). change (reg_get regs1 4 = Z_to_bv 64 (ms_tp B)). rewrite E4. exact Htp0. }
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel RWq) as RW1.
  pose proof (proj2 (bytes_at_rel rsegs m1 m0' f bs Hrel) BFq) as BF1.
  rewrite <- SEGS. change (Z_to_bv 64 0x14484) with (Z_to_bv 64 LLVM_MALLOC).
  eapply (g_malloc stk (spZ regs0) L0 A0 mem0 md0 _ regs1 m1 md L A (fuzz_dup_size (wk n))
    (sb_malloc b (fuzz_dup_size (wk n))));
    [exact FR1 | lia | lia | rewrite G11; apply ret_ok_even; reflexivity | rewrite Hsp1; apply sp16; exact Hal0
    | rewrite Hsp1; unfold ALLOC_STACK; lia | rewrite Hsp1; lia | rewrite Hsp1; lia | exact Htp1 | exact G110
    | exact Hres | | ].
  { apply fuzz_dup_room; unfold sb_malloc; cbn [sb_live sb_bytes sb_cap]; unfold CAPMAX in *; lia. }
  intros L2 A2 regs2 mem2 md2 c FR2 Hrp2 G210 Hc1 Hc2 Hc16 Hcimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2.
  rewrite G11.
  pose proof FR1 as (HM1 & _ & _ & _ & _ & _ & _ & Hblk1 & _).
  pose proof FR2 as (HM2 & _).
  assert (Hinc2 : In (c, fuzz_dup_size (wk n)) (blocks L2 A2)) by (rewrite Eb1; apply ccg_in_mid).
  assert (Hinf2 : In (f, fuzz_dup_size (wk n)) (blocks L2 A2)) by (rewrite Eb1; apply ccg_in_ins; rewrite <- Eb2; exact Hinf).
  assert (PW : pairwise ranges_disjoint (b1 ++ (c, fuzz_dup_size (wk n)) :: b2)).
  { rewrite <- Eb1. exact (mr_blocks_disjoint B _ (aa_laws API) L2 A2 mem2 md2 HM2). }
  assert (Hcf : c <> f).
  { intros E. subst c. pose proof (disj_mid b1 _ b2 _ PW ltac:(rewrite <- Eb2; exact Hinf)) as D.
    cbn [fst snd] in D. lia. }
  assert (Hmc : forall a q, In (a, q) (blocks L0 A0) -> a + q <= c \/ c + fuzz_dup_size (wk n) <= a).
  { intros a q Haq. pose proof (Hblk1 a q Haq) as Hin1. rewrite Eb2 in Hin1.
    pose proof (disj_mid b1 _ b2 _ PW Hin1) as D. cbn [fst snd] in D. lia. }
  assert (Hnc : forall a q, In (a, q) (blocks L0 A0) -> a <> c).
  { intros a q Haq Ea. subst a. pose proof (BND L2 A2 mem2 md2 HM2) as ND. rewrite Eb1, map_app in ND.
    cbn [map fst] in ND. apply NoDup_ListNoDup in ND. apply NoDup_remove_2 in ND. apply ND.
    rewrite <- map_app, <- Eb2. apply in_map_iff. exists (c, q). split; [reflexivity | exact (Hblk1 c q Haq)]. }
  pose proof (hk_rp regs0 regs1 regs2 HK1 Hrp2) as HK2.
  assert (G28 : reg_get regs2 8 = Z_to_bv 64 f) by exact (rp_sv regs1 regs2 8 _ Hrp2 ltac:(unfold callee_saved; lia) E18).
  assert (G29 : reg_get regs2 9 = Z_to_bv 64 (wk n))
    by exact (rp_sv regs1 regs2 9 _ Hrp2 ltac:(unfold callee_saved; lia) E19).
  assert (G222 : reg_get regs2 22 = Z_to_bv 64 (n - 1))
    by exact (rp_sv regs1 regs2 22 _ Hrp2 ltac:(unfold callee_saved; lia) E122).
  assert (RW2 : rw_cells rsegs mem2 (spZ regs0 - 64) (wire_sv regs0)).
  { apply (lf_rw_cells_frame m1 mem2 _ _ RW1). intros a Ha.
    change (Z.of_nat (cells_size (wire_sv regs0))) with 64 in Ha. rewrite <- SEGS. apply Habove2. lia. }
  assert (BF2 : bytes_at rsegs mem2 f bs).
  { apply (bk_bytes L A m1 mem2 (fun _ => False) f (fuzz_dup_size (wk n)) bs Hkept2 Hinf (fun H => H)); [lia | exact BF1]. }
  eapply (sr_mid2 (mkFP (@fp_regs fx') (@fp_csr fx')) regs2 mem2 md2 L2 A2 f c bs);
    [exact FR2 | exact Hfrm | exact HK2 | exact G28 | exact G29 | exact G210 | exact G222 | exact Hn1 | exact RW2
    | exact BF2 | exact HLb | exact Hinc2 | exact Hinf2 | exact Hcf | exact Hmc | exact Hmf | exact Hnc | exact Hres2].
Qed.

(* the entry 0x12d78, 1 <= size < 2^26: the frame -> malloc #1 -> sr_mid1 *)
Lemma sr_entry : forall pl, n = Z.of_nat (length pl) -> blk_data B mem0 p pl -> 1 <= n < 2 ^ 26 ->
  ro_agree rsegs mem0 -> frm_zero (@fp_csr fx) -> res_ok_slots A0 b ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0)
    (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).
Proof.
  intros pl Hn Hpd Hn1 Hro Hfrm Hres.
  run_env.
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p n Hpre Hro) as FR0.
  pose proof (wk_range n ltac:(lia)) as Hwk.
  pose proof (fds_cases (wk n) ltac:(lia)) as Hfc.
  pose proof Hroom as (Hr1 & Hr2 & Hr3).
  assert (PAY : In (p, n) (blocks L0 A0) /\ 4096 <= p /\ p + n <= YM05.alloc_ceiling).
  { destruct Hpl0 as [[E _] | [_ (q & Hq & Hqp)]]; [lia|].
    pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM0 Hq) as (R1 & R2). rewrite Hqp in R1, R2.
    split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia. }
  destruct PAY as (Hpin & Hp1 & Hp2).
  assert (Esp : spZ regs0 = bv_unsigned (reg_get regs0 2)) by reflexivity.
  assert (E10 : reg_get regs0 10 = Z_to_bv 64 p) by exact Hp0.
  assert (E11 : reg_get regs0 11 = Z_to_bv 64 n) by exact Hn0.
  rewrite SEGS.
  eapply g_run with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (Q := q1 (@fp_regs fx) (@fp_csr fx) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 23) (reg_get regs0 24)
            (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) (normalize rsegs mem0)
            (bv_unsigned (reg_get regs0 2) + -64) n p (wire_sv regs0));
    [exact FR0 | lia | lia | | | ].
  { unfold Regs6ss.mkR_of. rewrite E10, E11. unfold LLVM_ENTRY.
    apply e1_evt with (lo := spZ regs0 - stk) (pl := pl).
    - rewrite <- Esp. apply (norm_stk mem0 (spZ regs0 - stk) (spZ regs0) Hro); [unfold LF_RES_TOP; lia | lia |].
      exact Hstw0.
    - rewrite <- Esp. lia.
    - rewrite <- Esp. lia.
    - exact Hn1.
    - exact Hn.
    - lia.
    - apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact Hpd].
    - lia. }
  { q_out1.
    exists R, (@fp_regs fx), (Z_to_bv 64 0x14484), (@fp_csr fx), m',
      [(bv_unsigned (reg_get regs0 2) + -64, bv_unsigned (reg_get regs0 2) + -64 + 64)].
    split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    intros x Hx NO. left. apply en_out1 in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & HE & Q1 & Q2 & Q3 & Q4 & Q9 & Q10 & Q19 & Q20 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & MU & WM
    & RWq).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  replace (bv_unsigned (reg_get regs0 2) + -64) with (spZ regs0 - 64) in Q2, RWq by lia.
  pose proof (hk_x regs0 R regs1 Hx Q2 Q3 Q4 Q23 Q24 Q25 Q26 Q27) as HK1.
  assert (G11 : YK11.getr regs1 1 = Z_to_bv 64 0x12dd8) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Q1).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 (fuzz_dup_size (wk n)))
    by (rewrite (lf_getr_eqv _ _ _ Hx); exact Q10).
  assert (E19 : reg_get regs1 9 = Z_to_bv 64 (wk n)) by exact (xget _ _ _ _ Hx Q9 eq_refl).
  assert (E119 : reg_get regs1 19 = Z_to_bv 64 (fuzz_dup_size (wk n))) by exact (xget _ _ _ _ Hx Q19 eq_refl).
  assert (E120 : reg_get regs1 20 = Z_to_bv 64 p) by exact (xget _ _ _ _ Hx Q20 eq_refl).
  assert (E122 : reg_get regs1 22 = Z_to_bv 64 (n - 1)) by exact (xget _ _ _ _ Hx Q22 eq_refl).
  pose proof (hk_sp regs0 regs1 HK1 ltac:(lia)) as Hsp1.
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)).
  { destruct HK1 as (_ & _ & E4 & _). change (reg_get regs1 4 = Z_to_bv 64 (ms_tp B)). rewrite E4. exact Htp0. }
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel RWq) as RW1.
  rewrite <- SEGS. change (Z_to_bv 64 0x14484) with (Z_to_bv 64 LLVM_MALLOC).
  eapply (g_malloc stk (spZ regs0) L0 A0 mem0 md0 _ regs1 m1 md0 L0 A0 (fuzz_dup_size (wk n)) b);
    [exact FR1 | lia | lia | rewrite G11; apply ret_ok_even; reflexivity | rewrite Hsp1; apply sp16; exact Hal0
    | rewrite Hsp1; unfold ALLOC_STACK; lia | rewrite Hsp1; lia | rewrite Hsp1; lia | exact Htp1 | exact G110
    | exact Hres | | ].
  { apply fuzz_dup_room; unfold CAPMAX in *; lia. }
  intros L2 A2 regs2 mem2 md2 f FR2 Hrp2 G210 Hf1 Hf2 Hf16 Hfimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 _.
  rewrite G11.
  pose proof FR2 as (HM2 & _).
  assert (Hinf2 : In (f, fuzz_dup_size (wk n)) (blocks L2 A2)) by (rewrite Eb1; apply ccg_in_mid).
  assert (PW : pairwise ranges_disjoint (b1 ++ (f, fuzz_dup_size (wk n)) :: b2)).
  { rewrite <- Eb1. exact (mr_blocks_disjoint B _ (aa_laws API) L2 A2 mem2 md2 HM2). }
  assert (Hmf : forall a q, In (a, q) (blocks L0 A0) -> a + q <= f \/ f + fuzz_dup_size (wk n) <= a).
  { intros a q Haq. rewrite Eb2 in Haq. pose proof (disj_mid b1 _ b2 _ PW Haq) as D. cbn [fst snd] in D. lia. }
  pose proof (hk_rp regs0 regs1 regs2 HK1 Hrp2) as HK2.
  assert (G29 : reg_get regs2 9 = Z_to_bv 64 (wk n))
    by exact (rp_sv regs1 regs2 9 _ Hrp2 ltac:(unfold callee_saved; lia) E19).
  assert (G219 : reg_get regs2 19 = Z_to_bv 64 (fuzz_dup_size (wk n)))
    by exact (rp_sv regs1 regs2 19 _ Hrp2 ltac:(unfold callee_saved; lia) E119).
  assert (G220 : reg_get regs2 20 = Z_to_bv 64 p)
    by exact (rp_sv regs1 regs2 20 _ Hrp2 ltac:(unfold callee_saved; lia) E120).
  assert (G222 : reg_get regs2 22 = Z_to_bv 64 (n - 1))
    by exact (rp_sv regs1 regs2 22 _ Hrp2 ltac:(unfold callee_saved; lia) E122).
  assert (RW2 : rw_cells rsegs mem2 (spZ regs0 - 64) (wire_sv regs0)).
  { apply (lf_rw_cells_frame m1 mem2 _ _ RW1). intros a Ha.
    change (Z.of_nat (cells_size (wire_sv regs0))) with 64 in Ha. rewrite <- SEGS. apply Habove2. lia. }
  eapply (sr_mid1 _ regs2 mem2 md2 L2 A2 f pl);
    [exact FR2 | exact Hfrm | exact HK2 | exact G29 | exact G210 | exact G219 | exact G220 | exact G222 | exact Hn1
    | exact Hn | exact Hpd | exact RW2 | exact Hinf2 | exact Hmf | exact Hres2].
Qed.

End Run.

End G.

Theorem LLVMFuzzerTestOneInput_holds_of : LLVMFuzzerTestOneInput_sr_contract B API.
Proof using MALLOC FREE ERRNO_LOW SINK BND CT MC CF CR CD CM CN CW CRD CC.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn11 & Hpl0 & Hrod).
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (Hnb : 0 <= n < 2 ^ 47).
  { destruct Hpl0 as [[-> _] | [Hn0 (q & Hq & _)]]; [lia|].
    destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia. }
  destruct (Z_lt_le_dec 0 n) as [Hpos|Hz]; [destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig]|].
  2, 3: apply (llvm_early B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm);
        rewrite Hn11; rewrite MState.unsigned_lit by lia; lia.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  enough (HL : SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 LLVM_ENTRY) mem (YK11.seg_rom (ms_segs B))) md)
                 (llvm_sr_post B API stk L A regs mem md ra p n b j)).
  { unfold llvm_sr_post in HL. first [exact HL | rewrite SEGS in HL; exact HL]. }
  eapply sr_entry; try eassumption. lia.
Qed.

End M.
