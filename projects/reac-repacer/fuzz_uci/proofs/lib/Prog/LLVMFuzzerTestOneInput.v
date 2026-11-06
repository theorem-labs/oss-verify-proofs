(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the plain-image walk of the harness body
   LLVMFuzzerTestOneInput (fuzz_uci.c), 0x12b64, 384 bytes, against LLVMFuzzerTestOneInput_c.v's
   LLVMFuzzerTestOneInput_sr_contract. Same shape as libreac/fuzz_decode's released lib/Prog/LLVMFuzzerTestOneInput.v
   (with its fd_entry.v / fd_glue.v / fd_exit.v helpers): the `size >= 2^26` return is LLVMFuzzerTestOneInput_early.v's
   llvm_early; the rest is split at each call. Straight-line segments are evt proofs (e0_evt: prologue, bit, MARGIN_MAX
   from .rodata; e_head: the four cur bytes, len, n = min (size - at, len), (int)fuzz_le32(cur); e_back: v[i] = got,
   at += n; e_last: v[4], the struct copy, check_clamp through its evt contract, return 0) bridged to SR by g_run; the
   SR calls check_no_overread and check_value go through g_cno / g_cv (decode's g_crt at these contracts). The five
   iterations are loop_sr, by induction on 5 - i. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require Import rp_uci_int_c rp_hot_clamp_c
  check_no_overread_c check_value_c check_clamp_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_early.
Import ListNotations.
Open Scope Z_scope.

Lemma rd_pl : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi.
  change (Z_to_bv 64 (a + Z.of_nat i)) with (wa (a + Z.of_nat i)).
  rewrite (bytes_at_ov_read rsegs m a bs i 1 H ltac:(lia)).
  f_equal. clear H. revert i Hi. induction bs as [|x bs IH]; intros [|i] Hi; cbn [length] in Hi.
  - lia.
  - lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_leu, bv_lts; cbn [negb]; usub; fold_lit_ux; solve_cond_rec.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.

Lemma e0_cond : forall u, 0 <= u < 2 ^ 26 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = false.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma sltu0 : forall n, 0 <= n < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 n) = Z_to_bv 64 (if n =? 0 then 0 else 1).
Proof.
  intros n Hn. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
  destruct (Z.eqb_spec n 0); destruct (Z.ltb_spec 0 n); try reflexivity; lia.
Qed.

Lemma zxb_land1 : forall b : byte, Z.land (bv_unsigned (zxb b)) 1 = bv_unsigned b mod 2.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold zxb. rewrite unsigned_lit by lia. exact (Z.land_ones (bv_unsigned b) 1 ltac:(lia)).
Qed.

Ltac qreg := split; [first [reflexivity | (simp_regs; f_equal; lia)] |].

(* the entry segment's end state: the loop head 0x12be4, i = 0 *)
Definition q0 (F : bvmap 5 word) (fc : bv 32) (gp tp s11 : word) (m0 : word -> option byte) (Sp n p : Z)
    (sv : list cell) (ms : machine_state) : Prop :=
  exists R m' mm at0 j, ms = MS R F (Z_to_bv 64 0x12be4) fc None m' (seg_rom rsegs) /\
    reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\ reg_get R 8 = Z_to_bv 64 n /\
    reg_get R 9 = Z_to_bv 64 p /\ reg_get R 18 = Z_to_bv 64 mm /\ reg_get R 22 = Z_to_bv 64 0 /\
    reg_get R 23 = Z_to_bv 64 at0 /\ reg_get R 24 = Z_to_bv 64 (Sp + 12) /\ reg_get R 25 = Z_to_bv 64 (Sp + 28) /\
    reg_get R 26 = Z_to_bv 64 5 /\ reg_get R 27 = s11 /\
    (mm = 1984 \/ mm = 16320) /\ 0 <= at0 <= n /\
    munch [(Sp, Sp + 144)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' Sp (CB 48 j :: sv).

Lemma e0_tail :
  forall (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte) (Sp n p bit at0 : Z) (j : list byte)
         (sv : list cell),
    0 <= Sp -> Sp + 144 <= 2 ^ 63 -> 0 <= n < 2 ^ 26 -> 0 <= p < 2 ^ 64 -> (bit = 0 \/ bit = 1) -> 0 <= at0 <= n ->
    rw_cells rsegs m Sp (CB 48 j :: sv) -> cells_size sv = 96%nat -> mem_inv rsegs m ->
    munch [(Sp, Sp + 144)] mb m -> wmono rsegs mb m ->
    evt rsegs (q0 F fc x3 x4 x27 mb Sp n p sv)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 p) (Z_to_bv 64 bit) x11 x12 x13 x14 x15
               x16 x17 x18 x19 x20 x21 (Z_to_bv 64 0) (Z_to_bv 64 at0) x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12bc4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31
    F fc mb m Sp n p bit at0 j sv H0 H1 Hn Hp Hbit Hat FR Hsv MI MU WM.
  destruct Hbit as [-> | ->].
  - do 8 step.
    apply evt_done. unfold q0. do 5 eexists.
    split; [reflexivity|]. do 12 qreg.
    split; [left; reflexivity|]. split; [lia|]. split; [exact MU|]. split; [exact WM | exact FR].
  - do 8 step.
    apply evt_done. unfold q0. do 5 eexists.
    split; [reflexivity|]. do 12 qreg.
    split; [right; reflexivity|]. split; [lia|]. split; [exact MU|]. split; [exact WM | exact FR].
Qed.

Lemma e0_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p n : Z) (pl : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp -> mem_inv rsegs m -> bv_unsigned sp < 2 ^ 63 ->
    0 <= n < 2 ^ 26 -> 0 <= p < 2 ^ 64 -> n = Z.of_nat (length pl) ->
    (0 < n -> bytes_at rsegs m p pl) -> (0 < n -> p + n <= lo) ->
    evt rsegs (q0 F fc gp tp s11 m (bv_unsigned sp + -144) n p
                 [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
               s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12b64) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p n pl ST LO MI H63 Hn Hp Hlen HP HPL.
  pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp + -144 + 144)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo0 & _ & _).
  destruct (Z.eq_dec n 0) as [N0|N0].
  - carve_frame 144%nat ST.
    do 16 step.
    rewrite (unsigned_lit n) by lia. if_false_by (e0_cond n ltac:(lia)).
    step. step. take true.
    do 3 step.
    rewrite (sltu0 n) by lia.
    eapply e0_tail with (bit := 0) (at0 := if n =? 0 then 0 else 1); try eassumption; try lia.
    + destruct (Z.eqb_spec n 0); lia.
    + reflexivity.
  - pose proof (HP ltac:(lia)) as HP1. pose proof (HPL ltac:(lia)) as HPL1.
    carve_frame 144%nat ST.
    do 16 step.
    rewrite (unsigned_lit n) by lia. if_false_by (e0_cond n ltac:(lia)).
    step. step. take false.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (R0 : ov_read_bytes rsegs mm (Z_to_bv 64 (p + Z.of_nat 0)) 1 = Some [nth 0 pl (Z_to_bv 8 0)])
        by (apply rd_pl; [assumption | lia]) end.
    rewrite Z.add_0_r in R0.
    do 5 step.
    rewrite (sltu0 n), zxb_land1 by lia.
    eapply e0_tail with (bit := bv_unsigned (nth 0 pl (Z_to_bv 8 0)) mod 2) (at0 := if n =? 0 then 0 else 1);
      try eassumption; try lia.
    + destruct (Z.eqb_spec n 0); lia.
    + reflexivity.
Qed.

(* the reply bytes, read one at a time by `at < size ? data[at++] : 0` *)
Section RD.
Variables (x1 x2 x3 x4 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte) (n p : Z) (pl : list byte) (W : list (Z * Z))
  (Q : machine_state -> Prop).
Hypothesis Hlen : n = Z.of_nat (length pl).
Hypothesis HN : 0 <= n < 2 ^ 26.
Hypothesis HP : 0 <= p < 2 ^ 64.
Hypothesis HPB : 0 < n -> bytes_at rsegs mb p pl.
Hypothesis HPW : 0 < n -> disjoint_from W p n.
Hypothesis MU : munch W mb m.

Lemma rd_at : forall pos, 0 <= pos < n ->
  ov_read_bytes rsegs m (Z_to_bv 64 (p + pos)) 1 = Some [nth (Z.to_nat pos) pl (Z_to_bv 8 0)].
Proof.
  intros pos Hat.
  assert (BA : bytes_at rsegs m p pl).
  { apply (bytes_at_transport rsegs W mb m p pl (HPB ltac:(lia)) MU). rewrite <- Hlen. exact (HPW ltac:(lia)). }
  pose proof (rd_pl m p pl (Z.to_nat pos) BA ltac:(lia)) as R. rewrite Z2Nat.id in R by lia. exact R.
Qed.

Lemma rd_cur : forall pos x10 x11, 0 <= pos <= n ->
  (forall (b : byte) pos', pos <= pos' <= n -> pos' <= pos + 1 ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 p) x10 (zxb b) x12 x13 x14 x15 x16 x17 x18
                        x19 x20 x21 x22 (Z_to_bv 64 pos') x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x12c04) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 p) x10 x11 x12 x13 x14 x15 x16 x17 x18
                     x19 x20 x21 x22 (Z_to_bv 64 pos) x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x12bec) fc None m (seg_rom rsegs)).
Proof.
  intros pos x10 x11 Hat K.
  step.
  destruct (Z_lt_le_dec pos n) as [Hlt|Hge].
  - take false.
    pose proof (rd_at pos ltac:(lia)) as R.
    do 4 step.
    apply K; lia.
  - take true.
    step.
    assert (E0 : Z_to_bv 64 0 = zxb (Z_to_bv 8 0)) by reflexivity. rewrite E0.
    apply K; lia.
Qed.

Lemma rd_len : forall pos x10 x11, 0 <= pos <= n ->
  (forall (b : byte) pos', pos <= pos' <= n -> pos' <= pos + 1 ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 p) (zxb b) x11 x12 x13 x14 x15 x16 x17 x18
                        x19 x20 x21 x22 (Z_to_bv 64 pos') x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x12c28) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 p) x10 x11 x12 x13 x14 x15 x16 x17 x18
                     x19 x20 x21 x22 (Z_to_bv 64 pos) x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x12c10) fc None m (seg_rom rsegs)).
Proof.
  intros pos x10 x11 Hat K.
  step.
  destruct (Z_lt_le_dec pos n) as [Hlt|Hge].
  - take false.
    pose proof (rd_at pos ltac:(lia)) as R.
    do 4 step.
    apply K; lia.
  - take true.
    step.
    assert (E0 : Z_to_bv 64 0 = zxb (Z_to_bv 8 0)) by reflexivity. rewrite E0.
    apply K; lia.
Qed.

End RD.

(* n = min (size - at, len) *)
Lemma min_k : forall (x1 x2 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29
    x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n pos : Z) (lb : byte)
    (Q : machine_state -> Prop),
  0 <= pos <= n -> n < 2 ^ 26 ->
  (forall nsl, 0 <= nsl <= 255 -> pos + nsl <= n ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 n) x9 (zxb lb) x11 x12 x13 x14 x15 x16 x17 x18
                        (Z_to_bv 64 nsl) x20 x21 x22 (Z_to_bv 64 pos) x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x12c34) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 n) x9 (zxb lb) x11 x12 x13 x14 x15 x16 x17 x18
                     x19 x20 x21 x22 (Z_to_bv 64 pos) x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x12c28) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m n pos lb Q Hpos Hn K.
  step. step.
  rewrite (unsigned_lit n), (unsigned_lit pos) by lia.
  pose proof (bv_unsigned_in_range 8 lb) as Rlb. unfold bv_modulus in Rlb. change (2 ^ Z.of_N 8) with 256 in Rlb.
  destruct (Z_lt_le_dec (n - pos) (bv_unsigned lb)) as [Hl|Hl].
  - assert (C : bv_ltu (Z_to_bv 64 (n - pos)) (zxb lb) = true)
      by (unfold bv_ltu, zxb; rewrite !unsigned_lit by lia; apply Z.ltb_lt; lia).
    rewrite C. cbv iota.
    apply (K (n - pos)); lia.
  - assert (C : bv_ltu (Z_to_bv 64 (n - pos)) (zxb lb) = false)
      by (unfold bv_ltu, zxb; rewrite !unsigned_lit by lia; apply Z.ltb_ge; lia).
    rewrite C. cbv iota.
    step.
    apply (K (bv_unsigned lb)); lia.
Qed.

(* a cell list's meaning is its bytes: reshape it freely *)
Lemma rwc_bytes : forall segs m A cs cs', rw_cells segs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' E.
  split; [split; [exact Hwf' | rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma cur_open : forall segs m A c0 z rest, rw_cells segs m A (c0 :: C4 z :: rest) ->
  rw_cells segs m A (c0 :: CB 4 (le4 z) :: rest).
Proof.
  intros segs m A c0 z rest H. apply (rwc_bytes segs m A _ _ H); [|reflexivity].
  destruct H as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf |- *. rewrite length_le4. tauto.
Qed.

(* (int)fuzz_le32(cur), as lw sign-extends it *)
Definition cur4 (b0 b1 b2 b3 : byte) : Z :=
  let u := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3 in
  if u <? 2 ^ 31 then u else u - 2 ^ 32.

Lemma byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma cur4_range : forall b0 b1 b2 b3, INT_MIN <= cur4 b0 b1 b2 b3 <= INT_MAX.
Proof.
  intros. unfold cur4, INT_MIN, INT_MAX.
  pose proof (byte_rng b0). pose proof (byte_rng b1). pose proof (byte_rng b2). pose proof (byte_rng b3).
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end;
    [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.

Lemma lw4 : forall b0 b1 b2 b3,
  sext 64 (bv_extract 0 32 (le_bytes_to_word [b0; b1; b2; b3])) = Z_to_bv 64 (cur4 b0 b1 b2 b3).
Proof.
  intros. apply bv_eq. rewrite StrFun.lw_unsigned4, Z_to_bv_unsigned. unfold cur4, bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64).
  pose proof (byte_rng b0). pose proof (byte_rng b1). pose proof (byte_rng b2). pose proof (byte_rng b3).
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end;
    [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
  - rewrite Z.mod_small by lia. replace (bv_unsigned b3 / 128) with 0 by (symmetry; apply Z.div_small; lia). lia.
  - replace (bv_unsigned b3 / 128) with 1 by (apply Z.div_unique with (bv_unsigned b3 - 128); lia).
    rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma cur_close : forall segs m A c0 b0 b1 b2 b3 rest,
  rw_cells segs m A (c0 :: C1 b0 :: C1 b1 :: C1 b2 :: C1 b3 :: rest) ->
  rw_cells segs m A (c0 :: C4 (Z_to_bv 64 (cur4 b0 b1 b2 b3)) :: rest).
Proof.
  intros segs m A c0 b0 b1 b2 b3 rest H. apply (rwc_bytes segs m A _ _ H).
  - destruct H as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf |- *. tauto.
  - cbn [cells_bytes cbytes app]. rewrite <- lw4, StrFun.le4_lw by reflexivity. reflexivity.
Qed.

Lemma sx32_int : forall x, INT_MIN <= x <= INT_MAX -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32, INT_MIN, INT_MAX in *. f_equal. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
  destruct (Z_le_gt_dec 0 x) as [H|H].
  - rewrite (Z.mod_small x) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite (Z.mod_small (x + 1 * 2 ^ 64)) by lia.
    replace (x + 1 * 2 ^ 64 + 2 ^ 31) with (x + 2 ^ 31 + 2 ^ 32 * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Ltac rdk := lazymatch goal with |- forall _ : byte, _ => idtac | _ => first [eassumption | lia] end.

Ltac sbstep := step; rewrite ?le1_zxb; mem_after_store_opt.

(* the loop head's end state: the call of check_no_overread (data + at, n, (int)fuzz_le32(cur)) *)
Definition q_head (F : bvmap 5 word) (fc : bv 32) (x3 x4 x18 x22 x25 x26 x27 : word) (mb : word -> option byte)
    (Sp n p pos : Z) (j0 : list byte) (rest : list cell) (ms : machine_state) : Prop :=
  exists R m' pos' nsl cur, ms = MS R F (Z_to_bv 64 0x12ce4) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12c4c /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = x3 /\ reg_get R 4 = x4 /\
    reg_get R 8 = Z_to_bv 64 n /\ reg_get R 9 = Z_to_bv 64 p /\ reg_get R 10 = Z_to_bv 64 (p + pos') /\
    reg_get R 11 = Z_to_bv 64 nsl /\ reg_get R 12 = Z_to_bv 64 cur /\ reg_get R 18 = x18 /\
    reg_get R 19 = Z_to_bv 64 nsl /\ reg_get R 20 = Z_to_bv 64 cur /\ reg_get R 21 = Z_to_bv 64 (p + pos') /\
    reg_get R 22 = x22 /\ reg_get R 23 = Z_to_bv 64 pos' /\ reg_get R 24 = Z_to_bv 64 (Sp + 12) /\
    reg_get R 25 = x25 /\ reg_get R 26 = x26 /\ reg_get R 27 = x27 /\
    pos <= pos' /\ pos' + nsl <= n /\ 0 <= nsl <= REPLY_MAX /\ INT_MIN <= cur <= INT_MAX /\
    munch [(Sp, Sp + 144)] mb m' /\ wmono rsegs mb m' /\
    rw_cells rsegs m' Sp (CB 8 j0 :: C4 (Z_to_bv 64 cur) :: rest).

Lemma e_head :
  forall (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte) (Sp n p pos : Z) (pl j0 : list byte)
         (wc : word) (rest : list cell),
    0 <= Sp -> Sp + 144 <= 2 ^ 63 -> 0 <= n < 2 ^ 26 -> 0 <= p < 2 ^ 64 -> n = Z.of_nat (length pl) ->
    0 <= pos <= n -> (0 < n -> bytes_at rsegs mb p pl) -> (0 < n -> p + n <= Sp) ->
    rw_cells rsegs m Sp (CB 8 j0 :: C4 wc :: rest) -> munch [(Sp, Sp + 144)] mb m -> wmono rsegs mb m ->
    evt rsegs (q_head F fc x3 x4 x18 x22 x25 x26 x27 mb Sp n p pos j0 rest)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 p) x10 x11 x12 x13 x14 x15 x16 x17 x18
               x19 x20 x21 x22 (Z_to_bv 64 pos) (Z_to_bv 64 (Sp + 12)) x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12be4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31
    F fc mb m Sp n p pos pl j0 wc rest H0 H1 Hn Hp Hlen Hpos HPB HPL FR MU WM.
  assert (HPW : 0 < n -> disjoint_from [(Sp, Sp + 144)] p n) by (intros Hn0; cbn; specialize (HPL Hn0); split; [lia | exact I]).
  step.
  apply cur_open in FR.
  step.
  eapply rd_cur with (W := [(Sp, Sp + 144)]) (mb := mb) (pl := pl); rdk.
  intros b0 q1 Hq1 Hq1'.
  sbstep. step. step. take true.
  eapply rd_cur with (W := [(Sp, Sp + 144)]) (mb := mb) (pl := pl); rdk.
  intros b1 q2 Hq2 Hq2'.
  sbstep. step. step. take true.
  eapply rd_cur with (W := [(Sp, Sp + 144)]) (mb := mb) (pl := pl); rdk.
  intros b2 q3 Hq3 Hq3'.
  sbstep. step. step. take true.
  eapply rd_cur with (W := [(Sp, Sp + 144)]) (mb := mb) (pl := pl); rdk.
  intros b3 q4 Hq4 Hq4'.
  sbstep. step. step. take false.
  eapply rd_len with (W := [(Sp, Sp + 144)]) (mb := mb) (pl := pl); rdk.
  intros lb q5 Hq5 Hq5'.
  eapply min_k; [lia | lia |].
  intros nsl Hnsl Hnsl'.
  apply cur_close in FR.
  step.
  rewrite (sx32_int _ (cur4_range b0 b1 b2 b3)).
  do 5 step.
  pose proof (cur4_range b0 b1 b2 b3) as Hcur.
  apply evt_done. unfold q_head. eexists. eexists. exists q5, nsl, (cur4 b0 b1 b2 b3).
  split; [reflexivity|]. do 19 qreg.
  split; [lia|]. split; [lia|]. split; [unfold REPLY_MAX; lia|]. split; [exact Hcur|].
  split; [exact MU|]. split; [exact WM | exact FR].
Qed.

Definition wsel (i k : Z) (x w : word) : word := if Z.eqb k i then x else w.

(* the loop latch for i < 4: v[i] = got; at += n; back to the loop head *)
Definition q_back (F : bvmap 5 word) (fc : bv 32) (x3 x4 x8 x9 x18 x24 x27 : word) (mb : word -> option byte)
    (Sp i pos nsl : Z) (v : word) (j0 : list byte) (wc : word) (jr : list byte) (w0 w1 w2 w3 w4 : word)
    (sv : list cell) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x12be4) fc None m' (seg_rom rsegs) /\
    reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = x3 /\ reg_get R 4 = x4 /\ reg_get R 8 = x8 /\
    reg_get R 9 = x9 /\ reg_get R 18 = x18 /\ reg_get R 22 = Z_to_bv 64 (i + 1) /\
    reg_get R 23 = Z_to_bv 64 (pos + nsl) /\ reg_get R 24 = x24 /\ reg_get R 25 = Z_to_bv 64 (Sp + 28) /\
    reg_get R 26 = Z_to_bv 64 5 /\ reg_get R 27 = x27 /\
    munch [(Sp, Sp + 144)] mb m' /\ wmono rsegs mb m' /\
    rw_cells rsegs m' Sp (CB 8 j0 :: C4 wc :: CB 16 jr :: C4 (wsel i 0 v w0) :: C4 (wsel i 1 v w1) ::
      C4 (wsel i 2 v w2) :: C4 (wsel i 3 v w3) :: C4 (wsel i 4 v w4) :: sv).

Lemma e_back :
  forall (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte) (Sp i pos nsl : Z) (v : word)
         (j0 : list byte) (wc : word) (jr : list byte) (w0 w1 w2 w3 w4 : word) (sv : list cell),
    0 <= Sp -> Sp + 144 <= 2 ^ 63 -> 0 <= i < 4 -> 0 <= pos -> 0 <= nsl -> pos + nsl < 2 ^ 26 ->
    rw_cells rsegs m Sp (CB 8 j0 :: C4 wc :: CB 16 jr :: C4 w0 :: C4 w1 :: C4 w2 :: C4 w3 :: C4 w4 :: sv) ->
    munch [(Sp, Sp + 144)] mb m -> wmono rsegs mb m ->
    evt rsegs (q_back F fc x3 x4 x8 x9 x18 x24 x27 mb Sp i pos nsl v j0 wc jr w0 w1 w2 w3 w4 sv)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 nsl) x20 x21
               (Z_to_bv 64 i) (Z_to_bv 64 pos) x24 (Z_to_bv 64 (Sp + 28)) (Z_to_bv 64 5) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12c5c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x27 x28 x29 x30 x31
    F fc mb m Sp i pos nsl v j0 wc jr w0 w1 w2 w3 w4 sv H0 H1 Hi Hpos Hnsl Hpn FR MU WM.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]].
  all: do 6 step; take true.
  all: apply evt_done; unfold q_back, wsel; cbn [Z.eqb Pos.eqb]; do 2 eexists.
  all: split; [reflexivity|]; do 12 qreg.
  all: split; [exact MU|]; split; [exact WM | exact FR].
Qed.

Lemma ro_sub : forall segs m A c0 mid rest, rw_cells segs m A (c0 :: mid ++ rest) ->
  ro_cells segs m (A + Z.of_nat (csize c0)) mid.
Proof.
  intros segs m A c0 mid rest [[Hwf Hb] _]. unfold ro_cells, cells_at. cbn [cells_wf] in Hwf.
  destruct Hwf as [Hc Hw]. apply cells_wf_app in Hw as [Hm _]. split; [exact Hm|].
  cbn [cells_bytes] in Hb. rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb].
  rewrite cbytes_length in Hb by exact Hc. apply bytes_at_app in Hb as [Hb _]. exact Hb.
Qed.

(* check_clamp's evt contract at this call site *)
Lemma cc_call : check_clamp_contract ->
  forall (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo mm v0 v1 v2 v3 v4 : Z)
         (Q : machine_state -> Prop),
    hot_int (RpHot v0 v1 v2 v3 v4) -> 0 <= mm <= INT_MAX -> 0 <= lo -> lo + 48 <= Sp -> Sp + 144 <= 2 ^ 63 ->
    ro_cells rsegs m (Sp + 8) [C4 (Z_to_bv 64 v0); C4 (Z_to_bv 64 v1); C4 (Z_to_bv 64 v2); C4 (Z_to_bv 64 v3);
                               C4 (Z_to_bv 64 v4)] ->
    mem_inv rsegs m -> stk rsegs m lo Sp ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
       munch [(Sp - 48, Sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
       evt rsegs Q (MS (mkR (Z_to_bv 64 0x12ca8) (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6'
                          a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (Z_to_bv 64 0x12ca8) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x12ca8) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Sp + 8))
                       (Z_to_bv 64 mm) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x12f88) fc None m (seg_rom rsegs)).
Proof.
  intros CC gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sp lo mm v0 v1 v2 v3 v4 Q HI Hmm Hlo HloS HSp RO MI ST K.
  unfold INT_MAX in Hmm.
  eapply evt_cut.
  - apply (CC (Z_to_bv 64 0x12ca8) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Sp + 8)) (Z_to_bv 64 mm)
      a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (RpHot v0 v1 v2 v3 v4) mm lo).
    + exact HI.
    + unfold INT_MAX. lia.
    + apply unsigned_lit. lia.
    + rewrite unsigned_lit by lia. exact RO.
    + exact MI.
    + rewrite unsigned_lit by lia. exact ST.
    + rewrite unsigned_lit by lia. unfold CHECK_CLAMP_FRAME. lia.
    + rewrite unsigned_lit by lia. lia.
    + right. rewrite !unsigned_lit by lia. lia.
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      -> & MU & WM & MI' & _).
    replace (ret_pc (Z_to_bv 64 0x12ca8)) with (Z_to_bv 64 0x12ca8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite unsigned_lit in MU by lia. unfold CHECK_CLAMP_FRAME in MU.
    apply K; assumption.
Qed.

Definition int_of (x : Z) : Prop := INT_MIN <= x <= INT_MAX.

(* the last latch, i = 4: v[4] = got, the struct copy, check_clamp, return 0 *)
Definition q_last (F : bvmap 5 word) (fc : bv 32) (x3 x4 x27 y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 : word)
    (mb : word -> option byte) (Sp : Z) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (ret_pc y1) fc None m' (seg_rom rsegs) /\
    reg_get R 10 = Z_to_bv 64 0 /\ reg_get R 2 = Z_to_bv 64 (Sp + 144) /\ reg_get R 3 = x3 /\ reg_get R 4 = x4 /\
    reg_get R 8 = y8 /\ reg_get R 9 = y9 /\ reg_get R 18 = y18 /\ reg_get R 19 = y19 /\ reg_get R 20 = y20 /\
    reg_get R 21 = y21 /\ reg_get R 22 = y22 /\ reg_get R 23 = y23 /\ reg_get R 24 = y24 /\ reg_get R 25 = y25 /\
    reg_get R 26 = y26 /\ reg_get R 27 = x27 /\
    munch [(Sp - 48, Sp + 144)] mb m' /\ wmono rsegs mb m'.

Lemma e_last : check_clamp_contract ->
  forall (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x24 x27 x28 x29 x30 x31 : word)
         (y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 : word)
         (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte) (Sp lo pos nsl mm v0 v1 v2 v3 v4 : Z)
         (j0 : list byte) (wc : word) (jr : list byte) (w4 : word),
    0 <= lo -> lo + 48 <= Sp -> Sp + 144 <= 2 ^ 63 -> 0 <= pos -> 0 <= nsl -> pos + nsl < 2 ^ 26 ->
    0 <= mm <= INT_MAX -> int_of v0 -> int_of v1 -> int_of v2 -> int_of v3 -> int_of v4 ->
    rw_cells rsegs m Sp (CB 8 j0 :: C4 wc :: CB 16 jr :: C4 (Z_to_bv 64 v0) :: C4 (Z_to_bv 64 v1) ::
      C4 (Z_to_bv 64 v2) :: C4 (Z_to_bv 64 v3) :: C4 w4 ::
      [C8 y26; C8 y25; C8 y24; C8 y23; C8 y22; C8 y21; C8 y20; C8 y19; C8 y18; C8 y9; C8 y8; C8 y1]) ->
    stk rsegs m lo Sp -> mem_inv rsegs m ->
    munch [(Sp - 48, Sp + 144)] mb m -> wmono rsegs mb m ->
    evt rsegs (q_last F fc x3 x4 x27 y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 mb Sp)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 v4) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 mm)
               (Z_to_bv 64 nsl) x20 x21 (Z_to_bv 64 4) (Z_to_bv 64 pos) x24 (Z_to_bv 64 (Sp + 28)) (Z_to_bv 64 5)
               x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12c5c) fc None m (seg_rom rsegs)).
Proof.
  intros CC x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x24 x27 x28 x29 x30 x31
    y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 F fc mb m Sp lo pos nsl mm v0 v1 v2 v3 v4 j0 wc jr w4
    Hlo HloS HSp Hpos Hnsl Hpn Hmm I0 I1 I2 I3 I4 FR ST MI MU WM.
  do 6 step. take false.
  do 5 step.
  rewrite (sx32_int v0 I0), (sx32_int v1 I1), (sx32_int v2 I2), (sx32_int v3 I3), (sx32_int v4 I4).
  do 8 step.
  match type of FR with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: ?rest) =>
    pose proof (ro_sub rsegs _ Sp (CB 8 j0) [C4 (Z_to_bv 64 v0); C4 (Z_to_bv 64 v1); C4 (Z_to_bv 64 v2);
      C4 (Z_to_bv 64 v3); C4 (Z_to_bv 64 v4)] rest FR) as RO end.
  change (Sp + Z.of_nat (csize (CB 8 j0))) with (Sp + 8) in RO.
  eapply (cc_call CC) with (lo := lo); [ | exact Hmm | exact Hlo | exact HloS | exact HSp | exact RO | exact MI
    | exact ST | ].
  { unfold hot_int, int_of in *. cbn [prefill_ms adapt_min_ms adapt_max_ms adapt_margin servo_clamp_ppm].
    repeat split; lia. }
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MUc WMc MIc.
  apply (rw_cells_transport rsegs [(Sp - 48, Sp)] _ m' Sp _) in FR;
    [ | exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I] ].
  pose proof (munch_trans _ mb _ m' MU (munch_weaken [(Sp - 48, Sp)] [(Sp - 48, Sp + 144)] _ m'
    ltac:(unfold sub_fp; cbn [outside]; intros x [Hx _]; split; [lia | exact I]) MUc)) as MU'.
  pose proof (wmono_trans rsegs mb _ m' WM WMc) as WM'.
  clear MU WM MUc WMc RO ST MI.
  do 15 step.
  apply evt_done. unfold q_last. do 2 eexists.
  split; [reflexivity|]. do 16 qreg.
  split; [exact MU' | exact WM'].
Qed.

(* ---------------- the SR layer: the walk between the calls ---------------- *)

Definition uci_sv (r : bvmap 5 word) : list cell :=
  [C8 (reg_get r 26); C8 (reg_get r 25); C8 (reg_get r 24); C8 (reg_get r 23); C8 (reg_get r 22);
   C8 (reg_get r 21); C8 (reg_get r 20); C8 (reg_get r 19); C8 (reg_get r 18); C8 (reg_get r 9);
   C8 (reg_get r 8); C8 (reg_get r 1)].

Definition iw (w : word) : Prop := exists x, int_of x /\ w = Z_to_bv 64 x.

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

Lemma en_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x NO. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply NO; cbn [outside]; (split; [lia | exact I]).
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

Lemma blk_bytes_at : forall B m A bs, ms_segs B = rsegs -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  blk_data B m A bs -> bytes_at rsegs m A bs.
Proof.
  intros B m A bs HS H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, HS. reflexivity.
Qed.

Definition lw32 (bs : list byte) : word := sext 64 (bv_extract 0 32 (le_bytes_to_word bs)).

(* the 48 bytes below the saved registers, as the loop's cells *)
Lemma frame_init : forall segs m A j sv, rw_cells segs m A (CB 48 j :: sv) ->
  exists j0 wc jr w0 w1 w2 w3 w4,
    rw_cells segs m A (CB 8 j0 :: C4 wc :: CB 16 jr :: C4 w0 :: C4 w1 :: C4 w2 :: C4 w3 :: C4 w4 :: sv).
Proof.
  intros segs m A j sv H.
  apply (rw_cells_split_CB segs m A [] 48 j sv [8; 4; 16; 4; 4; 4; 4; 4]%nat) in H; [|reflexivity].
  cbn [app mk_CB_cells] in H.
  match type of H with rw_cells _ _ _ (CB 8 ?a :: CB 4 ?b :: CB 16 ?c :: CB 4 ?d0 :: CB 4 ?d1 :: CB 4 ?d2 ::
                                       CB 4 ?d3 :: CB 4 ?d4 :: _) =>
    exists a, (lw32 b), c, (lw32 d0), (lw32 d1), (lw32 d2), (lw32 d3), (lw32 d4) end.
  pose proof H as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf.
  apply (rwc_bytes segs m A _ _ H).
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes]. unfold lw32. rewrite !StrFun.le4_lw by tauto. reflexivity.
Qed.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
(* the listed Section hypotheses, in the order LLVMFuzzerTestOneInput_link.v passes them; the walk itself uses
   ERRNO_LOW, SINK, CNO, CV and CC (it calls no allocator directly), the theorem takes all nine (Proof using) *)
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis BND : blocks_nodup B API.
Hypothesis CT : ctx_owned B API.
Hypothesis CNO : forall fx' : YK11.FPState, @check_no_overread_contract fx' rc B API.
Hypothesis CV : forall fx' : YK11.FPState, @check_value_contract fx' rc B API.
Hypothesis CC : check_clamp_contract.

Section G.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis HGG : ms_got_guard B = LLVM_GUARD_GOT.

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

Lemma g_run : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs pc mem md L A
    (Q : machine_state -> Prop) (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m' W, ms = MState.MS R F pc' fc None m' (seg_rom rsegs) /\
     munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
     (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> S - stk <= x < S)) ->
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
    eapply (lf_fr_evt B API SEGS AX HGG); [exact FR | exact Hc | exact HS | exact MU' | exact WM' | exact Hro' |].
    intros x Hx0 NO. left. exact (HW x Hx0 NO).
Qed.

Lemma g_cno : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A r nsl cur bs bres
    (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CNO_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 r -> YK11.getr regs 11 = Z_to_bv 64 nsl -> YK11.getr regs 12 = Z_to_bv 64 cur ->
  INT_MIN <= cur <= INT_MAX -> 0 <= nsl <= REPLY_MAX -> Z.of_nat (length bs) = nsl -> blk_data B mem r bs ->
  (0 < nsl -> in_block L A r nsl) -> frm_zero (@fp_csr fx') -> res_ok_slots A bres -> cno_room bres nsl ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') -> lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A r nsl cur bs bres P FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 Hcur Hnsl Hlen Hbd Hib Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply SR_bind.
  { apply (CNO fx' L A regs mem md r nsl cur bs bres SEGS).
    - exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs CNO_STACK FR Hra Hal H1 H2
        ltac:(unfold CNO_STACK, CNO_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hcur.
    - exact Hnsl.
    - exact Hlen.
    - exact Hbd.
    - exact Hib.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & Eb & Hkept & Hgk & Hro2 & Hres2 & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold CNO_STACK, CNO_FRAME, ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp Hres2).
  apply (g_above stk S L A regs mem md CNO_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
    ltac:(unfold CNO_STACK, CNO_FRAME, ALLOC_STACK; lia)).
  intros a Ha. destruct Ha.
Qed.

Lemma g_cv : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A r nsl cur bs bres
    (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CV_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 r -> YK11.getr regs 11 = Z_to_bv 64 nsl -> YK11.getr regs 12 = Z_to_bv 64 cur ->
  INT_MIN <= cur <= INT_MAX -> 0 <= nsl <= REPLY_MAX -> Z.of_nat (length bs) = nsl -> blk_data B mem r bs ->
  (0 < nsl -> in_block L A r nsl) -> frm_zero (@fp_csr fx') -> res_ok_slots A bres -> cv_room bres nsl ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') -> lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur) ->
     res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_VALUE) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A r nsl cur bs bres P FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 Hcur Hnsl Hlen Hbd Hib Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply SR_bind.
  { apply (CV fx' L A regs mem md r nsl cur bs bres SEGS).
    - exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs CV_STACK FR Hra Hal H1 H2
        ltac:(unfold CV_STACK, CV_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hcur.
    - exact Hnsl.
    - exact Hlen.
    - exact Hbd.
    - exact Hib.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & Gv & Eb & Hkept & Hgk & Hro2 & Hres2 & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold CV_STACK, CV_FRAME, ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp Gv Hres2).
  apply (g_above stk S L A regs mem md CV_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
    ltac:(unfold CV_STACK, CV_FRAME, ALLOC_STACK; lia)).
  intros a Ha. destruct Ha.
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

Lemma cs_nz : forall x, callee_saved x -> is_x0 (Z_to_bv 5 x) = false.
Proof.
  intros x Hx.
  destruct (lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    reflexivity.
Qed.

(* one turn of the loop up to v[i] = check_value (...): the head segment, check_no_overread, the three moves,
   check_value *)
Lemma body_sr : forall stk empty L0 A0 regs0 mem0 md0 ra p n pl b p',
  LLVM_K <= stk -> lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n -> n = Z.of_nat (length pl) ->
  blk_data B mem0 p pl -> llvm_room b -> n < 2 ^ 26 -> 0 <= p' < 2 ^ 64 -> (0 < n -> p' = p) ->
  forall pos (fx' : YK11.FPState) regs mem md L A j0 wc jr w0 w1 w2 w3 w4 (P : config -> Prop),
  0 <= pos <= n ->
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md -> frm_zero (@fp_csr fx') -> res_ok_slots A b ->
  reg_get regs 2 = Z_to_bv 64 (spZ regs0 - 144) -> reg_get regs 4 = reg_get regs0 4 ->
  reg_get regs 8 = Z_to_bv 64 n -> reg_get regs 9 = Z_to_bv 64 p' -> reg_get regs 23 = Z_to_bv 64 pos ->
  reg_get regs 24 = Z_to_bv 64 (spZ regs0 - 144 + 12) ->
  rw_cells rsegs mem (spZ regs0 - 144)
    (CB 8 j0 :: C4 wc :: CB 16 jr :: C4 w0 :: C4 w1 :: C4 w2 :: C4 w3 :: C4 w4 :: uci_sv regs0) ->
  (forall (fx3 : YK11.FPState) regs3 mem3 md3 L3 A3 pos4 nsl v wc',
     lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L3 A3 mem3 md3 -> frm_zero (@fp_csr fx3) -> res_ok_slots A3 b ->
     (forall x, callee_saved x -> x <> 19 -> x <> 20 -> x <> 21 -> x <> 23 ->
        reg_get regs3 (Z_to_bv 5 x) = reg_get regs (Z_to_bv 5 x)) ->
     reg_get regs3 19 = Z_to_bv 64 nsl -> reg_get regs3 23 = Z_to_bv 64 pos4 -> reg_get regs3 10 = Z_to_bv 64 v ->
     int_of v -> pos <= pos4 -> pos4 + nsl <= n -> 0 <= nsl ->
     rw_cells rsegs mem3 (spZ regs0 - 144)
       (CB 8 j0 :: C4 wc' :: CB 16 jr :: C4 w0 :: C4 w1 :: C4 w2 :: C4 w3 :: C4 w4 :: uci_sv regs0) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx3 regs3 (Z_to_bv 64 0x12c5c) mem3 (YK11.seg_rom (ms_segs B))) md3) P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12be4) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n pl b p' Hk Hpre Hn Hpd Hroom H26 Hp' Hpp
    pos fx' regs mem md L A j0 wc jr w0 w1 w2 w3 w4 P Hpos FR Hfrm Hres G2 G4 G8 G9 G23 G24 RW K.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal & Hceil & H63 & Hstw0 & Htp & Herr0 & Hp & Hn11
    & Hpl0 & Hrod).
  unfold LLVM_K, LLVM_FRAME, CNO_STACK, CNO_FRAME, ALLOC_STACK in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. unfold LF_RES_TOP in Hrt.
  remember (spZ regs0) as S eqn:ES.
  assert (PAY : 0 < n -> In (p, n) (blocks L0 A0) /\ 4096 <= p /\ p + n <= YM05.alloc_ceiling).
  { intros Hn0. destruct Hpl0 as [[-> _] | [_ (q & Hq & Hqp)]]; [lia|].
    pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM0 Hq) as (R1 & R2). rewrite Hqp in R1, R2.
    split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia. }
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  assert (HPD : 0 < n -> blk_data B mem p pl).
  { intros Hn0. apply (blk_keep stk S L0 A0 mem0 md0 L A mem md p pl FR); [rewrite <- Hn; exact (proj1 (PAY Hn0)) | exact Hpd]. }
  (* the head segment, 0x12be4 -> check_no_overread *)
  rewrite SEGS.
  eapply g_run with (stk := stk) (S := S) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (Q := q_head (@fp_regs fx') (@fp_csr fx') (reg_get regs 3) (reg_get regs 4) (reg_get regs 18) (reg_get regs 22)
            (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (normalize rsegs mem) (S - 144) n p' pos j0
            (CB 16 jr :: C4 w0 :: C4 w1 :: C4 w2 :: C4 w3 :: C4 w4 :: uci_sv regs0));
    [exact FR | lia | lia | | | ].
  { unfold Regs6ss.mkR_of. rewrite G2, G8, G9, G23, G24.
    eapply e_head with (pl := pl) (wc := wc); [lia | lia | lia | lia | exact Hn | lia | | | | apply munch_refl
      | apply wmono_refl].
    - intros Hn0. rewrite (Hpp Hn0). destruct (PAY Hn0) as (_ & R1 & R2).
      apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact (HPD Hn0)].
    - intros Hn0. rewrite (Hpp Hn0). destruct (PAY Hn0) as (_ & R1 & R2). lia.
    - apply (lf_rw_cells_norm B mem _ _ SEGS Hro); [|exact RW].
      intros i Hi Himg0. pose proof (lf_in_img_top B _ SEGS Himg0). unfold LF_RES_TOP in *. lia. }
  { intros ms HQ. destruct HQ as (R & m' & pos' & nsl & cur & -> & HQ).
    repeat match type of HQ with _ /\ _ => let H := fresh "QQ" in destruct HQ as [H HQ] end.
    exists R, (@fp_regs fx'), (Z_to_bv 64 0x12ce4), (@fp_csr fx'), m', [(S - 144, S - 144 + 144)].
    split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    intros x Hx NO. apply en_out1 in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & pos4 & nsl & cur & HE & Q1 & Q2 & Q3 & Q4 & Q8 & Q9 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20
    & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & Hp4 & Hp4n & Hnsl & Hcur & MU1 & WM1 & RW1).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  assert (E11 : reg_get regs1 1 = Z_to_bv 64 0x12c4c) by exact (xget _ _ _ _ Hx Q1 eq_refl).
  assert (E12 : reg_get regs1 2 = Z_to_bv 64 (S - 144)) by exact (xget _ _ _ _ Hx Q2 eq_refl).
  assert (E14 : reg_get regs1 4 = reg_get regs 4) by exact (xget _ _ _ _ Hx Q4 eq_refl).
  assert (E110 : reg_get regs1 10 = Z_to_bv 64 (p' + pos4)) by exact (xget _ _ _ _ Hx Q10 eq_refl).
  assert (E111 : reg_get regs1 11 = Z_to_bv 64 nsl) by exact (xget _ _ _ _ Hx Q11 eq_refl).
  assert (E112 : reg_get regs1 12 = Z_to_bv 64 cur) by exact (xget _ _ _ _ Hx Q12 eq_refl).
  assert (E119 : reg_get regs1 19 = Z_to_bv 64 nsl) by exact (xget _ _ _ _ Hx Q19 eq_refl).
  assert (E120 : reg_get regs1 20 = Z_to_bv 64 cur) by exact (xget _ _ _ _ Hx Q20 eq_refl).
  assert (E121 : reg_get regs1 21 = Z_to_bv 64 (p' + pos4)) by exact (xget _ _ _ _ Hx Q21 eq_refl).
  assert (E123 : reg_get regs1 23 = Z_to_bv 64 pos4) by exact (xget _ _ _ _ Hx Q23 eq_refl).
  assert (Hcs1 : forall x, callee_saved x -> x <> 19 -> x <> 20 -> x <> 21 -> x <> 23 ->
     reg_get regs1 (Z_to_bv 5 x) = reg_get regs (Z_to_bv 5 x)).
  { intros x Hx1 N19 N20 N21 N23. rewrite <- (Hx (Z_to_bv 5 x) (cs_nz x Hx1)).
    destruct (lf_callee_cases x Hx1) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      try lia.
    - exact (eq_trans Q2 (eq_sym G2)).
    - exact Q3.
    - exact Q4.
    - exact (eq_trans Q8 (eq_sym G8)).
    - exact (eq_trans Q9 (eq_sym G9)).
    - exact Q18.
    - exact Q22.
    - exact (eq_trans Q24 (eq_sym G24)).
    - exact Q25.
    - exact Q26.
    - exact Q27. }
  assert (Hsp1 : spZ regs1 = S - 144).
  { assert (Esp : spZ regs1 = bv_unsigned (reg_get regs1 2)) by reflexivity. rewrite Esp, E12. apply unsigned_lit. lia. }
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel RW1) as RW1'.
  pose proof FR1 as (HM1 & _ & _ & _ & _ & _ & _ & Hblk1 & _ & _ & _ & _ & Hro1).
  assert (Hbs : Z.of_nat (length (firstn (Z.to_nat nsl) (skipn (Z.to_nat pos4) pl))) = nsl)
    by (rewrite length_firstn, length_skipn; lia).
  assert (HBD : forall L' A' m' md', lf_fr B API stk S L0 A0 mem0 md0 L' A' m' md' ->
     blk_data B m' (p' + pos4) (firstn (Z.to_nat nsl) (skipn (Z.to_nat pos4) pl))).
  { intros L' A' m' md' FRx. destruct (Z_lt_le_dec 0 nsl) as [Hn0|Hn0].
    - assert (Hn1 : 0 < n) by lia. rewrite (Hpp Hn1).
      pose proof (blk_keep stk S L0 A0 mem0 md0 L' A' m' md' p pl FRx) as HD1.
      specialize (HD1 ltac:(rewrite <- Hn; exact (proj1 (PAY Hn1))) Hpd).
      pose proof (blk_data_sub B m' p pl (Z.to_nat pos4) (Z.to_nat nsl) HD1 ltac:(lia)) as HS.
      rewrite Z2Nat.id in HS by lia. exact HS.
    - replace (Z.to_nat nsl) with 0%nat by lia. cbn [firstn]. apply blk_data_nil. }
  assert (HIB : forall L' A', (forall a k, In (a, k) (blocks L0 A0) -> In (a, k) (blocks L' A')) ->
     0 < nsl -> in_block L' A' (p' + pos4) nsl).
  { intros L' A' Hb' Hn0. assert (Hn1 : 0 < n) by lia. rewrite (Hpp Hn1).
    exists p, n. split; [exact (Hb' p n (proj1 (PAY Hn1)))|]. lia. }
  (* check_no_overread *)
  rewrite <- SEGS. change (Z_to_bv 64 0x12ce4) with (Z_to_bv 64 CHECK_NO_OVERREAD).
  eapply (g_cno stk S L0 A0 mem0 md0 _ regs1 m1 md L A (p' + pos4) nsl cur
    (firstn (Z.to_nat nsl) (skipn (Z.to_nat pos4) pl)) b).
  - exact FR1.
  - lia.
  - lia.
  - change (YK11.getr regs1 1) with (reg_get regs1 1). rewrite E11. apply ret_ok_even. reflexivity.
  - rewrite Hsp1. replace (S - 144) with (S + (-9) * 16) by lia. rewrite Z.mod_add by lia. exact Hal.
  - rewrite Hsp1. unfold CNO_STACK, CNO_FRAME, ALLOC_STACK. lia.
  - rewrite Hsp1. lia.
  - rewrite Hsp1. lia.
  - change (YK11.getr regs1 4) with (reg_get regs1 4). rewrite E14, G4. exact Htp.
  - change (YK11.getr regs1 10) with (reg_get regs1 10). exact E110.
  - change (YK11.getr regs1 11) with (reg_get regs1 11). exact E111.
  - change (YK11.getr regs1 12) with (reg_get regs1 12). exact E112.
  - exact Hcur.
  - exact Hnsl.
  - exact Hbs.
  - exact (HBD L A m1 md FR1).
  - exact (HIB L A Hblk1).
  - exact Hfrm.
  - exact Hres.
  - destruct Hroom as (Hl1 & Hl2 & Hl3). unfold cno_room. unfold REPLY_MAX in Hnsl. lia.
  - intros fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp2 Hres2 Hab2.
    assert (RW2 : rw_cells rsegs mem2 (S - 144) (CB 8 j0 :: C4 (Z_to_bv 64 cur) :: CB 16 jr :: C4 w0 :: C4 w1 ::
      C4 w2 :: C4 w3 :: C4 w4 :: uci_sv regs0)).
    { apply (lf_rw_cells_frame m1 mem2 _ _ RW1'). intros a Ha. rewrite <- SEGS. apply Hab2. rewrite Hsp1.
      cbn in Ha. lia. }
    pose proof FR2 as (HM2 & _ & _ & _ & _ & _ & _ & Hblk2 & _).
    destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
    (* mv a0, s5; mv a1, s3; mv a2, s4; jal check_value *)
    change (YK11.getr regs1 1) with (reg_get regs1 1). rewrite E11. rewrite SEGS.
    apply (llvm_run fx2 regs2 (Z_to_bv 64 0x12c4c) mem2 md2
      (fun ms => exists R2, ms = MS R2 (@fp_regs fx2) (Z_to_bv 64 0x12dc4) (@fp_csr fx2) None mem2 (seg_rom rsegs) /\
         reg_get R2 1 = Z_to_bv 64 0x12c5c /\ reg_get R2 10 = reg_get regs2 21 /\ reg_get R2 11 = reg_get regs2 19 /\
         reg_get R2 12 = reg_get regs2 20 /\
         forall x, callee_saved x -> reg_get R2 (Z_to_bv 5 x) = reg_get regs2 (Z_to_bv 5 x))
      P Hh2 Hl2).
    { unfold Regs6ss.mkR_of. do 4 step. apply evt_done. eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      intros x Hx2.
      destruct (lf_callee_cases x Hx2) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        reflexivity. }
    { intros ms (R2 & -> & _). do 5 eexists. reflexivity. }
    intros R2 F2 pc2 fc2 m2' (R2' & HE2 & M1 & M10 & M11 & M12 & Mcs) regsm Hxm.
    injection HE2 as ER2 EF2 EP2 EC2 EM2. subst R2' F2 pc2 fc2 m2'.
    assert (Em : forall x, callee_saved x -> reg_get regsm (Z_to_bv 5 x) = reg_get regs2 (Z_to_bv 5 x))
      by (intros x Hx3; exact (xget _ _ _ _ Hxm (Mcs x Hx3) (cs_nz x Hx3))).
    assert (Ech : forall x, callee_saved x -> reg_get regsm (Z_to_bv 5 x) = reg_get regs1 (Z_to_bv 5 x))
      by (intros x Hx3; rewrite (Em x Hx3); exact (rp_get regs1 regs2 x Hrp2 Hx3)).
    assert (Em1 : reg_get regsm 1 = Z_to_bv 64 0x12c5c) by exact (xget _ _ _ _ Hxm M1 eq_refl).
    assert (Em10 : reg_get regsm 10 = Z_to_bv 64 (p' + pos4)).
    { rewrite (xget _ _ _ _ Hxm M10 eq_refl).
      exact (eq_trans (rp_get regs1 regs2 21 Hrp2 ltac:(unfold callee_saved; lia)) E121). }
    assert (Em11 : reg_get regsm 11 = Z_to_bv 64 nsl).
    { rewrite (xget _ _ _ _ Hxm M11 eq_refl).
      exact (eq_trans (rp_get regs1 regs2 19 Hrp2 ltac:(unfold callee_saved; lia)) E119). }
    assert (Em12 : reg_get regsm 12 = Z_to_bv 64 cur).
    { rewrite (xget _ _ _ _ Hxm M12 eq_refl).
      exact (eq_trans (rp_get regs1 regs2 20 Hrp2 ltac:(unfold callee_saved; lia)) E120). }
    assert (Em2 : reg_get regsm 2 = Z_to_bv 64 (S - 144))
      by exact (eq_trans (Ech 2 ltac:(unfold callee_saved; lia)) E12).
    assert (Em4 : reg_get regsm 4 = reg_get regs0 4)
      by exact (eq_trans (Ech 4 ltac:(unfold callee_saved; lia)) (eq_trans E14 G4)).
    assert (Hspm : spZ regsm = S - 144).
    { assert (Esp : spZ regsm = bv_unsigned (reg_get regsm 2)) by reflexivity.
      rewrite Esp, Em2. apply unsigned_lit. lia. }
    (* check_value *)
    rewrite <- SEGS. change (Z_to_bv 64 0x12dc4) with (Z_to_bv 64 CHECK_VALUE).
    eapply (g_cv stk S L0 A0 mem0 md0 _ regsm mem2 md2 L2 A2 (p' + pos4) nsl cur
      (firstn (Z.to_nat nsl) (skipn (Z.to_nat pos4) pl)) b).
    + exact FR2.
    + lia.
    + lia.
    + change (YK11.getr regsm 1) with (reg_get regsm 1). rewrite Em1. apply ret_ok_even. reflexivity.
    + rewrite Hspm. replace (S - 144) with (S + (-9) * 16) by lia. rewrite Z.mod_add by lia. exact Hal.
    + rewrite Hspm. unfold CV_STACK, CV_FRAME, ALLOC_STACK. lia.
    + rewrite Hspm. lia.
    + rewrite Hspm. lia.
    + change (YK11.getr regsm 4) with (reg_get regsm 4). rewrite Em4. exact Htp.
    + change (YK11.getr regsm 10) with (reg_get regsm 10). exact Em10.
    + change (YK11.getr regsm 11) with (reg_get regsm 11). exact Em11.
    + change (YK11.getr regsm 12) with (reg_get regsm 12). exact Em12.
    + exact Hcur.
    + exact Hnsl.
    + exact Hbs.
    + exact (HBD L2 A2 mem2 md2 FR2).
    + exact (HIB L2 A2 Hblk2).
    + exact Hfrm2.
    + exact Hres2.
    + destruct Hroom as (Hl1 & Hl2' & Hl3). unfold cv_room. unfold REPLY_MAX in Hnsl. lia.
    + intros fx3 L3 A3 regs3 mem3 md3 Hfrm3 FR3 Hrp3 Gv Hres3 Hab3.
      assert (RW3 : rw_cells rsegs mem3 (S - 144) (CB 8 j0 :: C4 (Z_to_bv 64 cur) :: CB 16 jr :: C4 w0 :: C4 w1 ::
        C4 w2 :: C4 w3 :: C4 w4 :: uci_sv regs0)).
      { apply (lf_rw_cells_frame mem2 mem3 _ _ RW2). intros a Ha. rewrite <- SEGS. apply Hab3. rewrite Hspm.
        cbn in Ha. lia. }
      assert (E3 : forall x, callee_saved x -> reg_get regs3 (Z_to_bv 5 x) = reg_get regs1 (Z_to_bv 5 x))
        by (intros x Hx3; rewrite (rp_get regsm regs3 x Hrp3 Hx3); exact (Ech x Hx3)).
      change (YK11.getr regsm 1) with (reg_get regsm 1). rewrite Em1.
      apply (K fx3 regs3 mem3 md3 L3 A3 pos4 nsl (rp_uci_int_m (zbytes (firstn (Z.to_nat nsl)
        (skipn (Z.to_nat pos4) pl))) cur) (Z_to_bv 64 cur) FR3 Hfrm3 Hres3).
      * intros x Hx3 N19 N20 N21 N23. rewrite (E3 x Hx3). exact (Hcs1 x Hx3 N19 N20 N21 N23).
      * exact (eq_trans (E3 19 ltac:(unfold callee_saved; lia)) E119).
      * exact (eq_trans (E3 23 ltac:(unfold callee_saved; lia)) E123).
      * exact Gv.
      * unfold int_of. apply rp_uci_int_range. exact Hcur.
      * lia.
      * lia.
      * lia.
      * exact RW3.
Qed.

Lemma lf_getr_cs : forall R x, callee_saved x -> YK11.getr R (Z_to_bv 5 x) = reg_get R (Z_to_bv 5 x).
Proof.
  intros R x Hx.
  destruct (lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    reflexivity.
Qed.

(* the loop at its head 0x12be4, i = 5 - k: by induction on k *)
Lemma loop_sr : forall stk empty L0 A0 regs0 mem0 md0 ra p n pl b j p' mm,
  LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n -> n = Z.of_nat (length pl) -> blk_data B mem0 p pl ->
  sink_none B mem0 md0 -> llvm_room b -> n < 2 ^ 26 -> 0 <= p' < 2 ^ 64 -> (0 < n -> p' = p) ->
  0 <= mm <= INT_MAX ->
  forall k i pos (fx' : YK11.FPState) regs mem md L A j0 wc jr w0 w1 w2 w3 w4,
  Z.of_nat k + i = 5 -> 0 <= i < 5 -> 0 <= pos <= n ->
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md -> frm_zero (@fp_csr fx') -> res_ok_slots A b ->
  reg_get regs 2 = Z_to_bv 64 (spZ regs0 - 144) -> reg_get regs 3 = reg_get regs0 3 ->
  reg_get regs 4 = reg_get regs0 4 -> reg_get regs 8 = Z_to_bv 64 n -> reg_get regs 9 = Z_to_bv 64 p' ->
  reg_get regs 18 = Z_to_bv 64 mm -> reg_get regs 22 = Z_to_bv 64 i -> reg_get regs 23 = Z_to_bv 64 pos ->
  reg_get regs 24 = Z_to_bv 64 (spZ regs0 - 144 + 12) -> reg_get regs 25 = Z_to_bv 64 (spZ regs0 - 144 + 28) ->
  reg_get regs 26 = Z_to_bv 64 5 -> reg_get regs 27 = reg_get regs0 27 ->
  rw_cells rsegs mem (spZ regs0 - 144)
    (CB 8 j0 :: C4 wc :: CB 16 jr :: C4 w0 :: C4 w1 :: C4 w2 :: C4 w3 :: C4 w4 :: uci_sv regs0) ->
  (0 < i -> iw w0) -> (1 < i -> iw w1) -> (2 < i -> iw w2) -> (3 < i -> iw w3) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12be4) mem (YK11.seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n pl b j p' mm Hk Hra Hpre Hn Hpd Hsn Hroom H26 Hp' Hpp Hmm k.
  induction k as [|k IH]; intros i pos fx' regs mem md L A j0 wc jr w0 w1 w2 w3 w4 Hki Hi Hpos FR Hfrm Hres
    G2 G3 G4 G8 G9 G18 G22 G23 G24 G25 G26 G27 RW I0 I1 I2 I3.
  { lia. }
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal & Hceil & H63 & Hstw0 & Htp & Herr0 & Hp & Hn11
    & Hpl0 & Hrod).
  pose proof Hk as Hk'. unfold LLVM_K, LLVM_FRAME, CNO_STACK, CNO_FRAME, ALLOC_STACK in Hk'.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. unfold LF_RES_TOP in Hrt.
  apply (body_sr stk empty L0 A0 regs0 mem0 md0 ra p n pl b p' Hk Hpre Hn Hpd Hroom H26 Hp' Hpp pos fx' regs mem md
    L A j0 wc jr w0 w1 w2 w3 w4 _ Hpos FR Hfrm Hres G2 G4 G8 G9 G23 G24 RW).
  intros fx3 regs3 mem3 md3 L3 A3 pos4 nsl v wc' FR3 Hfrm3 Hres3 Hcs3 G319 G323 G310 Hv Hp4 Hp4n Hnsl RW3.
  set (S := spZ regs0) in *.
  assert (CS : forall x, callee_saved x -> x <> 19 -> x <> 20 -> x <> 21 -> x <> 23 ->
    reg_get regs3 (Z_to_bv 5 x) = reg_get regs (Z_to_bv 5 x)) by exact Hcs3.
  assert (C2 : reg_get regs3 2 = Z_to_bv 64 (S - 144))
    by exact (eq_trans (CS 2 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) G2).
  assert (C3 : reg_get regs3 3 = reg_get regs0 3)
    by exact (eq_trans (CS 3 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) G3).
  assert (C4' : reg_get regs3 4 = reg_get regs0 4)
    by exact (eq_trans (CS 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) G4).
  assert (C8' : reg_get regs3 8 = Z_to_bv 64 n)
    by exact (eq_trans (CS 8 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) G8).
  assert (C9 : reg_get regs3 9 = Z_to_bv 64 p')
    by exact (eq_trans (CS 9 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) G9).
  assert (C18 : reg_get regs3 18 = Z_to_bv 64 mm)
    by exact (eq_trans (CS 18 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) G18).
  assert (C22 : reg_get regs3 22 = Z_to_bv 64 i)
    by exact (eq_trans (CS 22 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) G22).
  assert (C24 : reg_get regs3 24 = Z_to_bv 64 (S - 144 + 12))
    by exact (eq_trans (CS 24 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) G24).
  assert (C25 : reg_get regs3 25 = Z_to_bv 64 (S - 144 + 28))
    by exact (eq_trans (CS 25 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) G25).
  assert (C26 : reg_get regs3 26 = Z_to_bv 64 5)
    by exact (eq_trans (CS 26 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) G26).
  assert (C27 : reg_get regs3 27 = reg_get regs0 27)
    by exact (eq_trans (CS 27 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) G27).
  pose proof FR3 as (HM3 & HW3 & HB3 & HID3 & Hmd3 & Hhigh3 & Himg3 & Hblk3 & Hbyt3 & Hstw3 & Herr3 & Hgd3 & Hro3).
  assert (RW3n : rw_cells rsegs (normalize rsegs mem3) (S - 144)
    (CB 8 j0 :: C4 wc' :: CB 16 jr :: C4 w0 :: C4 w1 :: C4 w2 :: C4 w3 :: C4 w4 :: uci_sv regs0)).
  { apply (lf_rw_cells_norm B mem3 _ _ SEGS Hro3); [|exact RW3].
    intros i0 Hi0 Himg0. pose proof (lf_in_img_top B _ SEGS Himg0). unfold LF_RES_TOP in *. lia. }
  destruct (Z.eq_dec i 4) as [Ei|Ei].
  - (* i = 4: v[4] = got, the struct, check_clamp, return 0 *)
    subst i.
    destruct (I0 ltac:(lia)) as (v0 & Iv0 & ->). destruct (I1 ltac:(lia)) as (v1 & Iv1 & ->).
    destruct (I2 ltac:(lia)) as (v2 & Iv2 & ->). destruct (I3 ltac:(lia)) as (v3 & Iv3 & ->).
    rewrite SEGS.
    eapply g_run with (stk := stk) (S := S) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
      (Q := q_last (@fp_regs fx3) (@fp_csr fx3) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 27)
              (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19)
              (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24)
              (reg_get regs0 25) (reg_get regs0 26) (normalize rsegs mem3) (S - 144));
      [exact FR3 | lia | lia | | | ].
    { unfold Regs6ss.mkR_of. rewrite C2, G310, C18, G319, C22, G323, C25, C26.
      eapply e_last with (lo := S - stk) (j0 := j0) (wc := wc') (jr := jr);
        [exact CC | lia | lia | lia | lia | lia | lia | exact Hmm | exact Iv0 | exact Iv1 | exact Iv2 | exact Iv3
        | exact Hv | exact RW3n | | apply mem_inv_normalize | apply munch_refl | apply wmono_refl].
      apply (norm_stk mem3 (S - stk) (S - 144) Hro3); [unfold LF_RES_TOP; lia | lia |].
      intros a Ha. apply Hstw3. lia. }
    { intros ms HQ. destruct HQ as (R & m' & -> & HQ).
      repeat match type of HQ with _ /\ _ => let H := fresh "QQ" in destruct HQ as [H HQ] end.
      exists R, (@fp_regs fx3), (ret_pc (reg_get regs0 1)), (@fp_csr fx3), m', [(S - 144 - 48, S - 144 + 144)].
      split; [reflexivity|]. split; [assumption|]. split; [assumption|].
      intros x Hx NO. apply en_out1 in NO. lia. }
    intros R F pc' fc m0' HQ regsf mf Hx Hrel FRf.
    destruct HQ as (R' & m'' & HE & F10 & F2 & F3 & F4 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25
      & F26 & F27 & MUf & WMf).
    injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
    apply SR_ret.
    assert (G10f : YK11.getr regsf 10 = Z_to_bv 64 0) by exact (xget _ _ _ _ Hx F10 eq_refl).
    assert (RP : regs_preserved regs0 regsf).
    { intros x Hx4. rewrite !lf_getr_cs by exact Hx4. rewrite <- (Hx _ (cs_nz x Hx4)).
      destruct (lf_callee_cases x Hx4) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
      - etransitivity; [exact F2|]. replace (S - 144 + 144) with S by lia. subst S. unfold spZ.
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      - exact (eq_trans F3 C3).
      - exact (eq_trans F4 C4').
      - exact F8.
      - exact F9.
      - exact F18.
      - exact F19.
      - exact F20.
      - exact F21.
      - exact F22.
      - exact F23.
      - exact F24.
      - exact F25.
      - exact F26.
      - exact (eq_trans F27 C27). }
    destruct (lf_post B API SINK stk empty L0 A0 regs0 mem0 md0 ra p n L3 A3 regsf mf md3 Hpre Hsn FRf G10f RP)
      as (Hpost & Hsn' & Hpay & MI2).
    exists (mkFP (@fp_regs fx3) (@fp_csr fx3)), L3, A3, regsf, mf, md3.
    assert (E1 : YK11.getr regs0 1 = reg_get regs0 1) by reflexivity.
    split; [rewrite SEGS, <- E1, Hra1, (lf_ret_pc _ Hra); reflexivity|].
    split; [exact Hfrm3|]. split; [exact Hpost|]. split; [exact Hsn'|].
    split; [exact Hres3|]. split; [exact Hpay|]. split; [exact MI2 | exact I].
  - (* i < 4: v[i] = got; at += n; back to the head *)
    rewrite SEGS.
    eapply g_run with (stk := stk) (S := S) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
      (Q := q_back (@fp_regs fx3) (@fp_csr fx3) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 8)
              (reg_get regs3 9) (reg_get regs3 18) (reg_get regs3 24) (reg_get regs3 27) (normalize rsegs mem3)
              (S - 144) i pos4 nsl (Z_to_bv 64 v) j0 wc' jr w0 w1 w2 w3 w4 (uci_sv regs0));
      [exact FR3 | lia | lia | | | ].
    { unfold Regs6ss.mkR_of. rewrite C2, G310, G319, C22, G323, C25, C26.
      eapply e_back; [lia | lia | lia | lia | lia | lia | exact RW3n | apply munch_refl | apply wmono_refl]. }
    { intros ms HQ. destruct HQ as (R & m' & -> & HQ).
      repeat match type of HQ with _ /\ _ => let H := fresh "QQ" in destruct HQ as [H HQ] end.
      exists R, (@fp_regs fx3), (Z_to_bv 64 0x12be4), (@fp_csr fx3), m', [(S - 144, S - 144 + 144)].
      split; [reflexivity|]. split; [assumption|]. split; [assumption|].
      intros x Hx NO. apply en_out1 in NO. lia. }
    intros R F pc' fc m0' HQ regs4 m4 Hx Hrel FR4.
    destruct HQ as (R' & m'' & HE & B2 & B3 & B4 & B8 & B9 & B18 & B22 & B23 & B24 & B25 & B26 & B27 & MU4 & WM4
      & RW4).
    injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
    rewrite <- SEGS.
    apply (IH (i + 1) (pos4 + nsl) (mkFP (@fp_regs fx3) (@fp_csr fx3)) regs4 m4 md3 L3 A3 j0 wc' jr
      (wsel i 0 (Z_to_bv 64 v) w0) (wsel i 1 (Z_to_bv 64 v) w1) (wsel i 2 (Z_to_bv 64 v) w2)
      (wsel i 3 (Z_to_bv 64 v) w3) (wsel i 4 (Z_to_bv 64 v) w4)).
    + lia.
    + lia.
    + lia.
    + exact FR4.
    + exact Hfrm3.
    + exact Hres3.
    + exact (xget _ _ _ _ Hx B2 eq_refl).
    + exact (xget _ _ _ _ Hx (eq_trans B3 C3) eq_refl).
    + exact (xget _ _ _ _ Hx (eq_trans B4 C4') eq_refl).
    + exact (xget _ _ _ _ Hx (eq_trans B8 C8') eq_refl).
    + exact (xget _ _ _ _ Hx (eq_trans B9 C9) eq_refl).
    + exact (xget _ _ _ _ Hx (eq_trans B18 C18) eq_refl).
    + exact (xget _ _ _ _ Hx B22 eq_refl).
    + exact (xget _ _ _ _ Hx B23 eq_refl).
    + exact (xget _ _ _ _ Hx (eq_trans B24 C24) eq_refl).
    + exact (xget _ _ _ _ Hx B25 eq_refl).
    + exact (xget _ _ _ _ Hx B26 eq_refl).
    + exact (xget _ _ _ _ Hx (eq_trans B27 C27) eq_refl).
    + exact (lf_rw_cells_rel m4 m0' _ _ Hrel RW4).
    + intros H0'. unfold wsel. destruct (Z.eqb_spec 0 i) as [E|E];
        [exists v; split; [exact Hv | reflexivity] | apply I0; lia].
    + intros H0'. unfold wsel. destruct (Z.eqb_spec 1 i) as [E|E];
        [exists v; split; [exact Hv | reflexivity] | apply I1; lia].
    + intros H0'. unfold wsel. destruct (Z.eqb_spec 2 i) as [E|E];
        [exists v; split; [exact Hv | reflexivity] | apply I2; lia].
    + intros H0'. unfold wsel. destruct (Z.eqb_spec 3 i) as [E|E];
        [exists v; split; [exact Hv | reflexivity] | apply I3; lia].
Qed.

End G.

Theorem LLVMFuzzerTestOneInput_holds_of : LLVMFuzzerTestOneInput_sr_contract B API.
Proof using MALLOC FREE ERRNO_LOW SINK BND CT CNO CV CC.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn11 & Hpl0 & Hrod).
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (Hnb : 0 <= n < 2 ^ 47).
  { destruct Hpl0 as [[-> _] | [Hn0 (q & Hq & _)]]; [lia|].
    destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia. }
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig].
  2:{ apply (llvm_early B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      rewrite Hn11. rewrite MState.unsigned_lit by lia. exact Hbig. }
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof Hk as Hk'. unfold LLVM_K, LLVM_FRAME, CNO_STACK, CNO_FRAME, ALLOC_STACK in Hk'.
  pose proof lf_ceiling as Hrt. unfold LF_RES_TOP in Hrt.
  pose proof (lf_fr_init B API stk empty L A regs mem md ra p n Hpre Hro) as FR0.
  assert (Esp : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  set (p' := bv_unsigned (reg_get regs 10)).
  assert (HP01 : 0 <= p' < 2 ^ 64).
  { unfold p'. pose proof (bv_unsigned_in_range _ (reg_get regs 10)) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in R. exact R. }
  assert (E10 : reg_get regs 10 = Z_to_bv 64 p') by (unfold p'; symmetry; apply Z_to_bv_bv_unsigned).
  assert (E11 : reg_get regs 11 = Z_to_bv 64 n) by exact Hn11.
  assert (PAY : 0 < n -> In (p, n) (blocks L A) /\ 4096 <= p /\ p + n <= YM05.alloc_ceiling).
  { intros Hn0. destruct Hpl0 as [[-> _] | [_ (q & Hq & Hqp)]]; [lia|].
    pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
    split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia. }
  assert (Hpp : 0 < n -> p' = p).
  { intros Hn0. destruct (PAY Hn0) as (_ & R1 & R2). unfold p'.
    assert (E : reg_get regs 10 = Z_to_bv 64 p) by exact Hp. rewrite E. apply MState.unsigned_lit. lia. }
  rewrite SEGS.
  eapply (g_run SEGS AX HGG) with (stk := stk) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := q0 (@fp_regs fx) (@fp_csr fx) (reg_get regs 3) (reg_get regs 4) (reg_get regs 27) (normalize rsegs mem)
            (bv_unsigned (reg_get regs 2) + -144) n p' (uci_sv regs)); [exact FR0 | lia | lia | | | ].
  { unfold Regs6ss.mkR_of. rewrite E10, E11. unfold LLVM_ENTRY.
    apply (e0_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - stk) p' n pl).
    - rewrite <- Esp. apply (norm_stk SEGS mem (spZ regs - stk) (spZ regs) Hro); [unfold LF_RES_TOP; lia | lia |].
      exact Hstw.
    - rewrite <- Esp. lia.
    - apply mem_inv_normalize.
    - rewrite <- Esp. lia.
    - lia.
    - exact HP01.
    - exact Hn.
    - intros Hn0. rewrite (Hpp Hn0). destruct (PAY Hn0) as (_ & R1 & R2).
      apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact Hpl].
    - intros Hn0. rewrite (Hpp Hn0). destruct (PAY Hn0) as (_ & R1 & R2). lia. }
  { intros ms HQ. destruct HQ as (R & m' & mm & at0 & jj & -> & HQ).
    repeat match type of HQ with _ /\ _ => let H := fresh "QQ" in destruct HQ as [H HQ] end.
    exists R, (@fp_regs fx), (Z_to_bv 64 0x12be4), (@fp_csr fx), m',
      [(bv_unsigned (reg_get regs 2) + -144, bv_unsigned (reg_get regs 2) + -144 + 144)].
    split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    intros x Hx NO. apply en_out1 in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & mm & at0 & jj & HE & Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27
    & Hmm & Hat0 & MU & WM & RW).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  replace (bv_unsigned (reg_get regs 2) + -144) with (spZ regs - 144) in Q2, Q24, Q25, RW by lia.
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel RW) as RW1.
  destruct (frame_init rsegs m1 _ jj _ RW1) as (j0 & wc & jr & w0 & w1 & w2 & w3 & w4 & RW2).
  enough (HL : SR (ms_segs B) (mkCfg (@YK11.mkst (mkFP (@fp_regs fx) (@fp_csr fx)) regs1 (Z_to_bv 64 0x12be4) m1
                 (YK11.seg_rom (ms_segs B))) md) (llvm_sr_post B API stk L A regs mem md ra p n b j)).
  { unfold llvm_sr_post in HL. rewrite SEGS in HL. exact HL. }
  apply (loop_sr SEGS AX HGG stk empty L A regs mem md ra p n pl b j p' mm Hk Hra Hpre Hn Hpl Hsn Hroom Hsmall HP01
    Hpp ltac:(unfold INT_MAX; lia) 5 0 at0 (mkFP (@fp_regs fx) (@fp_csr fx)) regs1 m1 md L A j0 wc jr w0 w1 w2 w3 w4).
  - lia.
  - lia.
  - lia.
  - exact FR1.
  - exact Hfrm.
  - exact Hres.
  - exact (xget _ _ _ _ Hx Q2 eq_refl).
  - exact (xget _ _ _ _ Hx Q3 eq_refl).
  - exact (xget _ _ _ _ Hx Q4 eq_refl).
  - exact (xget _ _ _ _ Hx Q8 eq_refl).
  - exact (xget _ _ _ _ Hx Q9 eq_refl).
  - exact (xget _ _ _ _ Hx Q18 eq_refl).
  - exact (xget _ _ _ _ Hx Q22 eq_refl).
  - exact (xget _ _ _ _ Hx Q23 eq_refl).
  - exact (xget _ _ _ _ Hx Q24 eq_refl).
  - exact (xget _ _ _ _ Hx Q25 eq_refl).
  - exact (xget _ _ _ _ Hx Q26 eq_refl).
  - exact (xget _ _ _ _ Hx Q27 eq_refl).
  - exact RW2.
  - intros H0. lia.
  - intros H0. lia.
  - intros H0. lia.
  - intros H0. lia.
Qed.

End M.
