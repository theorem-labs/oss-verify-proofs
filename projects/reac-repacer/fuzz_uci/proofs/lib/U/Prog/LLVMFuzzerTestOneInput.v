(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the harness-body walk of LLVMFuzzerTestOneInput on the
   UBSan image (fuzz_uci.ubsan: entry 0x12b68, frame 0x80, check_no_overread 0x12d54, check_value 0x12e48,
   check_clamp 0x1305c), the UBSan twin of lib/Prog/LLVMFuzzerTestOneInput.v at this image's values. Its SR level is
   libreac/fuzz_decode's released lib/U/Prog/LLVMFuzzerTestOneInput.v, fd_glue.v and fd_exit.v (g_pre, g_above,
   g_run, lf_rw_cells_frame and blk_bytes_at are fd_glue.v's text; g_cno / g_cv are its g_crt for this program's two
   SR callees); the entry and byte-read lemmas follow the plain twin.
   It walks 122 of the function's 123 instructions: all but the unimp at 0x12d50 (the size >= 2^26 return is
   lib/U/Prog/LLVMFuzzerTestOneInput_early.v's llvm_early). The function calls no abort; every UBSan check branches
   to the unimp at 0x12d50, and none is taken:
   - 0x12bac `beqz s2` (data NULL with size > 0): lib_pre makes data a live block, at or above 4096 (f_pay).
   - 0x12bc4 / 0x12bc8 `not` / `bltu` (MARGIN_MAX + 4 * (data[0] & 1) wraps): constants, 0x10390 + 4 < 2^64.
   - 0x12c08 / 0x12c44 `bltu` (data + at wraps), 0x12c0c-0x12c14 / 0x12c48-0x12c50 `seqz`/`xor`/`beqz` (data + at
     NULL with data non-NULL, nzx), 0x12c18 / 0x12c54 `beqz s2` (data NULL): a read runs only for at < size, so
     size > 0 and data + at < data + size <= alloc_ceiling < 2^63, data >= 4096 (rd_cur, rd_len).
   - 0x12c6c `bltu` and 0x12c70-0x12c78 `seqz`/`xor`/`beqz` on data + at for the calls: for size = 0, at = 0 and
     data + at = data, whatever data is; for size > 0 as above (sa_tail).
   - 0x12cd0 `beq` on -4, 0x12ce0 / 0x12cf0 / 0x12d00 `bltu` on -9 / -13 / -17 (&v[i] wraps): &v[0] = sp + 0x14 with
     sp < 2^47 (sx_evt).
   The callees' premises are discharged at each call: check_no_overread / check_value (0x12c94 / 0x12ca4) get the
   slice data[at, at + n) of the payload block (in_block, n <= 255, blk_data, cur an int, the room of llvm_room),
   check_clamp (0x12d14) gets a0 = sp and sp 4-aligned (the entry sp is 16-aligned and sp = entry sp - 0x80),
   48 < sp (sp >= alloc_ceiling + stk - 0x80), the five ints of v[] (rp_uci_int_range) and its frame below sp. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import rp_uci_int_c rp_hot_clamp_c
  check_no_overread_c check_value_c check_clamp_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_early.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require CheckGlue.
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

Lemma sltu0_pos : forall n, 0 < n < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 n) = Z_to_bv 64 1.
Proof. intros n Hn. rewrite sltu0 by lia. destruct (Z.eqb_spec n 0); [lia | reflexivity]. Qed.

Lemma zxb_land1 : forall b : byte, Z.land (bv_unsigned (zxb b)) 1 = bv_unsigned b mod 2.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold zxb. rewrite unsigned_lit by lia. exact (Z.land_ones (bv_unsigned b) 1 ltac:(lia)).
Qed.

Ltac qreg := split; [first [reflexivity | simp_regs; first [reflexivity | f_equal; lia]] |].

(* the frame of LLVMFuzzerTestOneInput (0x80 bytes at Sp): cur[4] / p.prefill_ms at Sp, the rest of struct p at
   Sp + 4, v[5] at Sp + 0x14 (the first length vs stored, the rest junk), the eleven saved registers at Sp + 0x28 *)
Definition hcells (jc jp : list byte) (vs : list Z) (jv : list byte) (sv : list cell) : list cell :=
  CB 4 jc :: CB 16 jp :: map (fun v => C4 (Z_to_bv 64 v)) vs ++ CB (20 - 4 * length vs) jv :: sv.

Definition lsv (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : list cell :=
  [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition nzb (p : Z) : Z := if p =? 0 then 0 else 1.

(* the loop head 0x12bf4 with i = length vs *)
Definition qh (F : bvmap 5 word) (fc : bv 32) (gp tp s10 s11 : word) (m0 : word -> option byte)
    (W : list (Z * Z)) (sv : list cell) (Sp n p : Z) (i : nat) (ms : machine_state) : Prop :=
  exists R m' mm at0 vs jc jp jv, ms = MS R F (Z_to_bv 64 0x12bf4) fc None m' (seg_rom rsegs) /\
    reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\ reg_get R 8 = Z_to_bv 64 mm /\
    reg_get R 9 = Z_to_bv 64 n /\ reg_get R 18 = Z_to_bv 64 p /\ reg_get R 21 = Z_to_bv 64 (Z.of_nat i) /\
    reg_get R 22 = Z_to_bv 64 at0 /\ reg_get R 23 = Z_to_bv 64 (nzb p) /\ reg_get R 24 = Z_to_bv 64 (Sp + 20) /\
    reg_get R 25 = Z_to_bv 64 5 /\ reg_get R 26 = s10 /\ reg_get R 27 = s11 /\
    (mm = 1984 \/ mm = 16320) /\ 0 <= at0 <= n /\ length vs = i /\ (i < 5)%nat /\
    Forall (fun v => INT_MIN <= v <= INT_MAX) vs /\
    munch W m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' Sp (hcells jc jp vs jv sv).

Lemma hcells0 : forall segs m Sp j sv, rw_cells segs m Sp (CB 40 j :: sv) ->
  exists jc jp jv, rw_cells segs m Sp (hcells jc jp [] jv sv).
Proof.
  intros segs m Sp j sv H.
  pose proof (rw_cells_split_CB segs m Sp [] 40 j sv [4; 16; 20]%nat H eq_refl) as H2.
  cbn [app mk_CB_cells] in H2. do 3 eexists. exact H2.
Qed.

(* 0x12bc0-0x12bf0: a0 = &MARGIN_MAX[bit], the UBSan wrap check on it (0x12bc4 / 0x12bc8, a constant: not taken),
   i = 0, at = (size != 0), margin_max, (data != 0), &v[0], 5 *)
Lemma e0_tail :
  forall (x1 x3 x4 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (W : list (Z * Z)) (Sp n p bit : Z)
         (j : list byte) (sv : list cell),
    (bit = 0 \/ bit = 1) -> 0 <= Sp -> Sp + 128 <= 2 ^ 63 -> 0 < n < 2 ^ 26 -> 0 <= p < 2 ^ 64 ->
    mem_inv rsegs m -> rw_cells rsegs m Sp (CB 40 j :: sv) -> munch W m0 m -> wmono rsegs m0 m ->
    evt rsegs (qh F fc x3 x4 x26 x27 m0 W sv Sp n p 0)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 n) (Z_to_bv 64 66448) (Z_to_bv 64 bit) x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 p) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12bc0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m0 m W Sp n p bit j sv Hbit H0 H1 Hn Hp MI FR MU WM.
  destruct (hcells0 rsegs m Sp j sv FR) as (jc & jp & jv & FR2).
  destruct Hbit as [-> | ->].
  - do 3 step. try take false. do 4 step.
    rewrite (sltu0_pos n) by lia. do 4 step. rewrite (sltu0 p) by lia.
    apply evt_done. unfold qh. eexists; exists m, 1984, 1, [], jc, jp, jv.
    split; [reflexivity|]. do 13 qreg.
    split; [left; reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
    split; [constructor|]. split; [exact MU|]. split; [exact WM | exact FR2].
  - do 3 step. try take false. do 4 step.
    rewrite (sltu0_pos n) by lia. do 4 step. rewrite (sltu0 p) by lia.
    apply evt_done. unfold qh. eexists; exists m, 16320, 1, [], jc, jp, jv.
    split; [reflexivity|]. do 13 qreg.
    split; [right; reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
    split; [constructor|]. split; [exact MU|]. split; [exact WM | exact FR2].
Qed.

(* 0x12b68-0x12bf0: the prologue, the size >= 2^26 test (not taken here: llvm_early takes it), and the MARGIN_MAX
   read; 0x12bac `beqz s2` to the trap at 0x12d50 is not taken: size > 0 there, so data is a block at or above 4096 *)
Lemma e0_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p n : Z) (pl : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> mem_inv rsegs m -> bv_unsigned sp < 2 ^ 63 ->
    0 <= n < 2 ^ 26 -> 0 <= p < 2 ^ 64 -> n = Z.of_nat (length pl) ->
    (0 < n -> bytes_at rsegs m p pl) -> (0 < n -> p + n <= lo) -> (0 < n -> 4096 <= p) ->
    evt rsegs (qh F fc gp tp s10 s11 m [(bv_unsigned sp - 128, bv_unsigned sp)]
                 (lsv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) (bv_unsigned sp - 128) n p 0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
               s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12b68) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p n pl ST LO MI H63 Hn Hp Hlen HP HPL HP0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (Z.eq_dec n 0) as [N0|N0].
  - rewrite N0 in *. carve_frame 128%nat ST.
    do 15 step.
    try if_false.
    step. step. try take true.
    do 8 step.
    rewrite (sltu0 0), (sltu0 p) by lia.
    replace (bv_unsigned sp + -128) with (bv_unsigned sp - 128) in * by lia.
    destruct (hcells0 rsegs _ _ _ _ FR) as (jc & jp & jv & FR2).
    apply evt_done. unfold qh. do 2 eexists; exists 1984, 0, [], jc, jp, jv.
    split; [reflexivity|]. do 13 qreg.
    split; [left; reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
    split; [constructor|]. split; [exact MU|]. split; [exact WM | exact FR2].
  - pose proof (HP ltac:(lia)) as HP1. pose proof (HPL ltac:(lia)) as HPL1. pose proof (HP0 ltac:(lia)) as HP2.
    carve_frame 128%nat ST.
    do 15 step.
    rewrite (unsigned_lit n) by lia. if_false_by (e0_cond n ltac:(lia)).
    step. step. take false. step. take false.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (R0 : ov_read_bytes rsegs mm (Z_to_bv 64 (p + Z.of_nat 0)) 1 = Some [nth 0 pl (Z_to_bv 8 0)])
        by (apply rd_pl; [assumption | lia]) end.
    rewrite Z.add_0_r in R0.
    do 4 step.
    rewrite zxb_land1.
    replace (bv_unsigned sp + -128) with (bv_unsigned sp - 128) in * by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned (nth 0 pl (Z_to_bv 8 0))) 2 ltac:(lia)) as Hb2.
    eapply e0_tail; try eassumption; lia.
Qed.

(* the UBSan null-arithmetic check `seqz t, a` / `xor t, s7, t` / `beqz t` with s7 = (data != 0): a = data + at
   is NULL exactly when data is *)
Lemma nzx : forall p a, 0 <= p < 2 ^ 64 -> 0 <= a < 2 ^ 64 -> (p = 0 <-> a = 0) ->
  bv_eqb (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (nzb p))) (bv_unsigned (v_sltiu (Z_to_bv 64 a) 1))))
    (Z_to_bv 64 0) = false.
Proof.
  intros p a Hp Ha Hiff. unfold v_sltiu, nzb. rewrite (unsigned_lit a) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec p 0); destruct (Z.ltb_spec a 1); try lia; reflexivity.
Qed.

(* the reply bytes, read one at a time by `at < size ? data[at++] : 0`, each read behind the UBSan checks of
   data + at (0x12c08 / 0x12c44 `bltu` on a wrap, 0x12c0c-0x12c14 / 0x12c48-0x12c50 `seqz`/`xor`/`beqz` on a NULL
   result of a non-NULL base, 0x12c18 / 0x12c54 `beqz s2` on data NULL), all to the unimp at 0x12d50; a read runs
   only for at < size, where size > 0 puts data in a block in [4096, alloc_ceiling): none of them is taken *)
Section RD.
Variables (x1 x2 x3 x4 x5 x6 x7 x8 x14 x15 x16 x17 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte) (n p : Z) (pl : list byte) (W : list (Z * Z))
  (Q : machine_state -> Prop).
Hypothesis Hlen : n = Z.of_nat (length pl).
Hypothesis HN : 0 <= n < 2 ^ 26.
Hypothesis HP : 0 <= p < 2 ^ 64.
Hypothesis HPB : 0 < n -> bytes_at rsegs mb p pl.
Hypothesis HPW : 0 < n -> disjoint_from W p n.
Hypothesis HP0 : 0 < n -> 4096 <= p /\ p + n <= 2 ^ 63.
Hypothesis H23 : x23 = Z_to_bv 64 (nzb p).
Hypothesis MU : munch W mb m.

Lemma rd_at : forall pos, 0 <= pos < n ->
  ov_read_bytes rsegs m (Z_to_bv 64 (p + pos)) 1 = Some [nth (Z.to_nat pos) pl (Z_to_bv 8 0)].
Proof.
  intros pos Hat.
  assert (BA : bytes_at rsegs m p pl).
  { apply (bytes_at_transport rsegs W mb m p pl (HPB ltac:(lia)) MU). rewrite <- Hlen. exact (HPW ltac:(lia)). }
  pose proof (rd_pl m p pl (Z.to_nat pos) BA ltac:(lia)) as R. rewrite Z2Nat.id in R by lia. exact R.
Qed.

Lemma rd_cur : forall pos x10 x11 x12 x13, 0 <= pos <= n ->
  (forall (b : byte) pos' x13', pos <= pos' <= n -> pos' <= pos + 1 ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 n) x10 x11 (zxb b) x13' x14 x15 x16 x17
                        (Z_to_bv 64 p) x19 x20 x21 (Z_to_bv 64 pos') x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x12c2c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 p) x19 x20 x21 (Z_to_bv 64 pos) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x12c00) fc None m (seg_rom rsegs)).
Proof.
  intros pos x10 x11 x12 x13 Hat K. subst x23.
  step.
  destruct (Z_lt_le_dec pos n) as [Hlt|Hge].
  - take false.
    pose proof (rd_at pos ltac:(lia)) as R. destruct (HP0 ltac:(lia)) as [P1 P2].
    step. step. take false. step. step. step.
    if_false_by (nzx p (p + pos) ltac:(lia) ltac:(lia) ltac:(lia)).
    step. take false.
    do 3 step.
    apply K; lia.
  - take true.
    step.
    assert (E0 : Z_to_bv 64 0 = zxb (Z_to_bv 8 0)) by reflexivity. rewrite E0.
    apply K; lia.
Qed.

Lemma rd_len : forall pos x10 x11 x12 x13, 0 <= pos <= n ->
  (forall (b : byte) pos' x11', pos <= pos' <= n -> pos' <= pos + 1 ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 n) (zxb b) x11' x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 p) x19 x20 x21 (Z_to_bv 64 pos') x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x12c68) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 p) x19 x20 x21 (Z_to_bv 64 pos) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x12c3c) fc None m (seg_rom rsegs)).
Proof.
  intros pos x10 x11 x12 x13 Hat K. subst x23.
  step.
  destruct (Z_lt_le_dec pos n) as [Hlt|Hge].
  - take false.
    pose proof (rd_at pos ltac:(lia)) as R. destruct (HP0 ltac:(lia)) as [P1 P2].
    step. step. take false. step. step. step.
    if_false_by (nzx p (p + pos) ltac:(lia) ltac:(lia) ltac:(lia)).
    step. take false.
    do 3 step.
    apply K; lia.
  - take true.
    step.
    assert (E0 : Z_to_bv 64 0 = zxb (Z_to_bv 8 0)) by reflexivity. rewrite E0.
    apply K; lia.
Qed.

End RD.

(* 0x12c7c-0x12c84: n = min (size - at, len) *)
Lemma min_k : forall (x1 x2 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28
    x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n pos : Z) (lb : byte)
    (Q : machine_state -> Prop),
  0 <= pos <= n -> n < 2 ^ 26 ->
  (forall nsl, 0 <= nsl <= 255 -> pos + nsl <= n ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 n) (zxb lb) x11 x12 x13 x14 x15 x16 x17 x18
                        (Z_to_bv 64 nsl) x20 x21 (Z_to_bv 64 pos) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x12c88) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 n) (zxb lb) x11 x12 x13 x14 x15 x16 x17 x18
                     x19 x20 x21 (Z_to_bv 64 pos) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x12c7c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31
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

Lemma cur_open : forall segs m A z rest, rw_cells segs m A (C4 z :: rest) -> rw_cells segs m A (CB 4 (le4 z) :: rest).
Proof.
  intros segs m A z rest H. apply (rwc_bytes segs m A _ _ H); [|reflexivity].
  destruct H as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf |- *. rewrite length_le4. tauto.
Qed.

Lemma cur_close : forall segs m A b0 b1 b2 b3 rest,
  rw_cells segs m A (C1 b0 :: C1 b1 :: C1 b2 :: C1 b3 :: rest) -> rw_cells segs m A (CB 4 [b0; b1; b2; b3] :: rest).
Proof.
  intros segs m A b0 b1 b2 b3 rest H. apply (rwc_bytes segs m A _ _ H); [|reflexivity].
  destruct H as [[Hwf _] _]. cbn [cells_wf cell_wf length] in Hwf |- *. tauto.
Qed.

Lemma lw_int : forall bs : list byte, exists c, INT_MIN <= c <= INT_MAX /\
  sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) = Z_to_bv 64 c.
Proof.
  intros bs. exists (bv_signed (bv_extract 0 32 (le_bytes_to_word bs))). split; [|apply sext_small].
  pose proof (bv_signed_in_range 32 (bv_extract 0 32 (le_bytes_to_word bs)) ltac:(lia)) as R.
  unfold bv_half_modulus, bv_modulus in R. change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31) in R.
  unfold INT_MIN, INT_MAX. lia.
Qed.

(* the call check_no_overread(data + at, n, cur) at 0x12c94 *)
Definition qa (F : bvmap 5 word) (fc : bv 32) (gp tp x8 x21 x24 x25 s10 s11 : word) (m0 : word -> option byte)
    (Sp n p at0 : Z) (rest : list cell) (ms : machine_state) : Prop :=
  exists R m' jc at1 nsl cur, ms = MS R F (Z_to_bv 64 0x12d54) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12c98 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = x8 /\ reg_get R 9 = Z_to_bv 64 n /\ reg_get R 10 = Z_to_bv 64 (at1 + p) /\
    reg_get R 11 = Z_to_bv 64 nsl /\ reg_get R 12 = Z_to_bv 64 cur /\ reg_get R 18 = Z_to_bv 64 p /\
    reg_get R 19 = Z_to_bv 64 nsl /\ reg_get R 20 = Z_to_bv 64 (at1 + p) /\ reg_get R 21 = x21 /\
    reg_get R 22 = Z_to_bv 64 at1 /\ reg_get R 23 = Z_to_bv 64 (nzb p) /\ reg_get R 24 = x24 /\
    reg_get R 25 = x25 /\ reg_get R 26 = s10 /\ reg_get R 27 = s11 /\
    INT_MIN <= cur <= INT_MAX /\ at0 <= at1 /\ 0 <= nsl <= 255 /\ at1 + nsl <= n /\
    munch [(Sp, Sp + 128)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' Sp (CB 4 jc :: rest).

(* 0x12c68-0x12c94: data + at with its UBSan checks (0x12c6c `bltu` wrap, 0x12c70-0x12c78 null arithmetic: for
   size = 0, at = 0 and data + at = data; else data >= 4096 and data + at <= data + size < 2^63), the min, the
   reload of cur and the call *)
Lemma sa_tail :
  forall (x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte) (Sp n p at0 at1 : Z) (lb : byte)
         (jc : list byte) (rest : list cell),
    0 <= Sp -> Sp + 128 <= 2 ^ 63 -> 0 <= n < 2 ^ 26 -> 0 <= p < 2 ^ 64 ->
    (0 < n -> 4096 <= p /\ p + n <= Sp) -> 0 <= at0 <= at1 -> at1 <= n ->
    rw_cells rsegs m Sp (CB 4 jc :: rest) -> munch [(Sp, Sp + 128)] mb m -> wmono rsegs mb m ->
    evt rsegs (qa F fc x3 x4 x8 x21 x24 x25 x26 x27 mb Sp n p at0 rest)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 n) (zxb lb) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p) x19 x20 x21 (Z_to_bv 64 at1) (Z_to_bv 64 (nzb p)) x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12c68) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31
    F fc mb m Sp n p at0 at1 lb jc rest H0 H1 Hn Hp HP0 Hat Hat1 FR MU WM.
  assert (Hw : at1 + p < 2 ^ 64 /\ (p = 0 <-> at1 + p = 0)).
  { destruct (Z.eq_dec n 0) as [N0|N0]; [split; [lia | split; intros; lia]|].
    destruct (HP0 ltac:(lia)). split; [lia | split; intros; lia]. }
  step. step. take false. step. step. step.
  if_false_by (nzx p (at1 + p) ltac:(lia) ltac:(lia) ltac:(tauto)).
  apply min_k; [lia | lia |]. intros nsl Hs1 Hs2.
  step.
  destruct (lw_int jc) as (cur & Hcur & Ecur). rewrite Ecur.
  do 3 step.
  apply evt_done. unfold qa. eexists; exists m, jc, at1, nsl, cur.
  split; [reflexivity|]. do 19 qreg.
  split; [exact Hcur|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact MU|]. split; [exact WM | exact FR].
Qed.

(* 0x12bf4-0x12c64: cur = 0, the four bytes of cur (0x12c00-0x12c38, a loop of four rounds over a0 = sp .. sp + 3),
   then len; then sa_tail *)
Lemma sa_evt :
  forall (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte) (Sp n p at0 : Z) (pl jc : list byte)
         (rest : list cell),
    0 <= Sp -> Sp + 128 <= 2 ^ 63 -> n = Z.of_nat (length pl) -> 0 <= n < 2 ^ 26 -> 0 <= p < 2 ^ 64 ->
    (0 < n -> bytes_at rsegs mb p pl) -> (0 < n -> 4096 <= p /\ p + n <= Sp) -> 0 <= at0 <= n ->
    rw_cells rsegs m Sp (CB 4 jc :: rest) -> munch [(Sp, Sp + 128)] mb m -> wmono rsegs mb m ->
    evt rsegs (qa F fc x3 x4 x8 x21 x24 x25 x26 x27 mb Sp n p at0 rest)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p) x19 x20 x21 (Z_to_bv 64 at0) (Z_to_bv 64 (nzb p)) x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12bf4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31
    F fc mb m Sp n p at0 pl jc rest H0 H1 Hlen Hn Hp HPB HP0 Hat FR MU WM.
  assert (HPW : 0 < n -> disjoint_from [(Sp, Sp + 128)] p n).
  { intros Hn0. destruct (HP0 Hn0). cbn [disjoint_from]. split; [lia | exact I]. }
  assert (HP1 : 0 < n -> 4096 <= p /\ p + n <= 2 ^ 63) by (intros Hn0; destruct (HP0 Hn0); lia).
  step.
  apply cur_open in FR.
  step. step.
  eapply rd_cur with (pl := pl) (mb := mb) (W := [(Sp, Sp + 128)]) (pos := at0);
    [solve [eassumption | reflexivity | lia] .. |].
  intros b0 pos1 y13 Hq1 Hq1'.
  step. rewrite le1_zxb. mem_after_store. step. step. step. try take true.
  eapply rd_cur with (pl := pl) (mb := mb) (W := [(Sp, Sp + 128)]) (pos := pos1);
    [solve [eassumption | reflexivity | lia] .. |].
  intros b1 pos2 y13' Hq2 Hq2'.
  step. rewrite le1_zxb. mem_after_store. step. step. step. try take true.
  eapply rd_cur with (pl := pl) (mb := mb) (W := [(Sp, Sp + 128)]) (pos := pos2);
    [solve [eassumption | reflexivity | lia] .. |].
  intros b2 pos3 y13'' Hq3 Hq3'.
  step. rewrite le1_zxb. mem_after_store. step. step. step. try take true.
  eapply rd_cur with (pl := pl) (mb := mb) (W := [(Sp, Sp + 128)]) (pos := pos3);
    [solve [eassumption | reflexivity | lia] .. |].
  intros b3 pos4 y13''' Hq4 Hq4'.
  step. rewrite le1_zxb. mem_after_store. step. step. step. try take false.
  apply cur_close in FR.
  eapply rd_len with (pl := pl) (mb := mb) (W := [(Sp, Sp + 128)]) (pos := pos4);
    [solve [eassumption | reflexivity | lia] .. |].
  intros lb pos5 y11 Hq5 Hq5'.
  eapply sa_tail; try eassumption; lia.
Qed.

(* 0x12c98-0x12ca4: cur reloaded, the call check_value(data + at, n, cur) *)
Lemma sb_evt :
  forall (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
          x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp : Z) (jc : list byte)
         (rest : list cell),
    rw_cells rsegs m Sp (CB 4 jc :: rest) ->
    evt rsegs (fun ms => exists cur, INT_MIN <= cur <= INT_MAX /\
                 ms = MS (mkR (Z_to_bv 64 0x12ca8) (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 x20 x19 (Z_to_bv 64 cur) x13
                            x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x12e48) fc None m (seg_rom rsegs))
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
               x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12c98) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m Sp jc rest FR.
  step.
  destruct (lw_int jc) as (cur & Hcur & Ecur). rewrite Ecur.
  do 3 step.
  apply evt_done. exists cur. split; [exact Hcur | reflexivity].
Qed.

(* the loop exit 0x12cc0: v[0..4] stored *)
Definition qx (F : bvmap 5 word) (fc : bv 32) (gp tp s10 s11 : word) (m0 : word -> option byte)
    (sv : list cell) (Sp : Z) (ms : machine_state) : Prop :=
  exists R m' mm vs jc jp, ms = MS R F (Z_to_bv 64 0x12cc0) fc None m' (seg_rom rsegs) /\
    reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\ reg_get R 8 = Z_to_bv 64 mm /\
    reg_get R 26 = s10 /\ reg_get R 27 = s11 /\
    (mm = 1984 \/ mm = 16320) /\ length vs = 5%nat /\ Forall (fun v => INT_MIN <= v <= INT_MAX) vs /\
    munch [(Sp, Sp + 128)] m0 m' /\ wmono rsegs m0 m' /\
    rw_cells rsegs m' Sp (CB 4 jc :: CB 16 jp :: map (fun v => C4 (Z_to_bv 64 v)) vs ++ sv).

(* 0x12ca8-0x12cbc: v[i] = the value, i + 1, at += n, the loop test *)
Lemma sc_evt :
  forall (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp n p mm at1 nsl v : Z) (vs : list Z)
         (jc jp jv : list byte) (sv : list cell),
    0 <= Sp -> Sp + 128 <= 2 ^ 63 -> (mm = 1984 \/ mm = 16320) -> 0 <= at1 -> 0 <= nsl -> at1 + nsl <= n ->
    INT_MIN <= v <= INT_MAX -> Forall (fun v => INT_MIN <= v <= INT_MAX) vs -> (length vs < 5)%nat ->
    rw_cells rsegs m Sp (hcells jc jp vs jv sv) ->
    evt rsegs (fun ms => qh F fc x3 x4 x26 x27 m [(Sp, Sp + 128)] sv Sp n p (S (length vs)) ms \/
                         qx F fc x3 x4 x26 x27 m sv Sp ms)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 mm) (Z_to_bv 64 n) (Z_to_bv 64 v) x11 x12 x13 x14 x15
               x16 x17 (Z_to_bv 64 p) (Z_to_bv 64 nsl) x20 (Z_to_bv 64 (Z.of_nat (length vs))) (Z_to_bv 64 at1)
               (Z_to_bv 64 (nzb p)) (Z_to_bv 64 (Sp + 20)) (Z_to_bv 64 5) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12ca8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x26 x27 x28 x29 x30 x31 F fc m Sp n p mm at1 nsl v vs
    jc jp jv sv H0 H1 Hmm Ha1 Hn1 Hs Hv Hvs Hl FR.
  pose proof (munch_refl [(Sp, Sp + 128)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Hvs' : Forall (fun v => INT_MIN <= v <= INT_MAX) (vs ++ [v])) by (apply Forall_app; split; auto).
  destruct vs as [|v0 [|v1 [|v2 [|v3 [|v4 vs']]]]]; cbn [length] in Hl, Hvs' |- *; try lia.
  - unfold hcells in FR. cbn [map app length Nat.mul Nat.add Nat.sub] in FR.
    change (Z.of_nat 0) with 0.
    do 6 step. try take true.
    apply evt_done. cbv beta. left. unfold qh. do 2 eexists; exists mm, (nsl + at1), [v]; do 3 eexists.
    split; [reflexivity|]. do 13 qreg.
    split; [exact Hmm|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [exact Hvs'|].
    split; [exact MU|]. split; [exact WM | exact FR].
  - unfold hcells in FR. cbn [map app length Nat.mul Nat.add Nat.sub] in FR.
    change (Z.of_nat 1) with 1.
    do 6 step. try take true.
    apply evt_done. cbv beta. left. unfold qh. do 2 eexists; exists mm, (nsl + at1), [v0; v]; do 3 eexists.
    split; [reflexivity|]. do 13 qreg.
    split; [exact Hmm|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [exact Hvs'|].
    split; [exact MU|]. split; [exact WM | exact FR].
  - unfold hcells in FR. cbn [map app length Nat.mul Nat.add Nat.sub] in FR.
    change (Z.of_nat 2) with 2.
    do 6 step. try take true.
    apply evt_done. cbv beta. left. unfold qh. do 2 eexists; exists mm, (nsl + at1), [v0; v1; v]; do 3 eexists.
    split; [reflexivity|]. do 13 qreg.
    split; [exact Hmm|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [exact Hvs'|].
    split; [exact MU|]. split; [exact WM | exact FR].
  - unfold hcells in FR. cbn [map app length Nat.mul Nat.add Nat.sub] in FR.
    change (Z.of_nat 3) with 3.
    do 6 step. try take true.
    apply evt_done. cbv beta. left. unfold qh. do 2 eexists; exists mm, (nsl + at1), [v0; v1; v2; v]; do 3 eexists.
    split; [reflexivity|]. do 13 qreg.
    split; [exact Hmm|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [exact Hvs'|].
    split; [exact MU|]. split; [exact WM | exact FR].
  - unfold hcells in FR. cbn [map app length Nat.mul Nat.add Nat.sub] in FR.
    change (Z.of_nat 4) with 4.
    do 6 step. try take false.
    apply evt_done. cbv beta. right. unfold qx. do 2 eexists; exists mm, [v0; v1; v2; v3; v]; do 2 eexists.
    split; [reflexivity|]. do 6 qreg.
    split; [exact Hmm|]. split; [reflexivity|]. split; [exact Hvs'|].
    split; [exact MU|]. split; [exact WM | exact FR].
Qed.

Lemma sx32_int : forall x, INT_MIN <= x <= INT_MAX -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32, INT_MIN, INT_MAX in *. f_equal. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  destruct (Z_lt_le_dec x 0) as [Hn|Hn].
  - rewrite <- (Z.mod_unique x (2 ^ 64) (-1) (x + 2 ^ 64)) by lia.
    rewrite <- (Z.mod_unique (x + 2 ^ 64 + 2 ^ 31) (2 ^ 32) (2 ^ 32) (x + 2 ^ 31)) by lia. lia.
  - rewrite (Z.mod_small x (2 ^ 64)) by lia. rewrite (Z.mod_small (x + 2 ^ 31) (2 ^ 32)) by lia. lia.
Qed.

Lemma rw_ro5 : forall segs m A c1 c2 c3 c4 c5 rest, rw_cells segs m A (c1 :: c2 :: c3 :: c4 :: c5 :: rest) ->
  ro_cells segs m A [c1; c2; c3; c4; c5].
Proof.
  intros segs m A c1 c2 c3 c4 c5 rest [[Hwf Hb] _]. unfold ro_cells, cells_at.
  change (c1 :: c2 :: c3 :: c4 :: c5 :: rest) with ([c1; c2; c3; c4; c5] ++ rest) in Hwf, Hb.
  apply cells_wf_app in Hwf. rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb.
  split; [exact (proj1 Hwf) | exact (proj1 Hb)].
Qed.

(* 0x12cc0-0x12d4c: the copy p = {v[0..4]} with the UBSan pointer checks on &v[i] (0x12cd0 `beq` on -4,
   0x12ce0 / 0x12cf0 / 0x12d00 `bltu` on -9 / -13 / -17, all to the unimp at 0x12d50: &v[0] = sp + 0x14 < 2^63, not
   taken), check_clamp(&p, margin_max), the return value 0, the epilogue and the return *)
Lemma sx_evt : check_clamp_contract ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word)
         (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 gp tp s10 s11 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo Sp mm v0 v1 v2 v3 v4 : Z) (jc jp : list byte),
    lo + 48 <= Sp -> 48 < Sp -> Sp mod 16 = 0 -> Sp + 128 <= 2 ^ 63 -> (mm = 1984 \/ mm = 16320) ->
    INT_MIN <= v0 <= INT_MAX -> INT_MIN <= v1 <= INT_MAX -> INT_MIN <= v2 <= INT_MAX ->
    INT_MIN <= v3 <= INT_MAX -> INT_MIN <= v4 <= INT_MAX ->
    mem_inv rsegs m -> stk rsegs m lo Sp ->
    rw_cells rsegs m Sp (CB 4 jc :: CB 16 jp :: C4 (Z_to_bv 64 v0) :: C4 (Z_to_bv 64 v1) :: C4 (Z_to_bv 64 v2) ::
      C4 (Z_to_bv 64 v3) :: C4 (Z_to_bv 64 v4) :: lsv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra (Z_to_bv 64 (Sp + 128)) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(lo, Sp + 128)] m m' /\ wmono rsegs m m')
      (MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 (Z_to_bv 64 mm) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12cc0) fc None m (seg_rom rsegs)).
Proof.
  intros CC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 gp tp s10 s11 F fc m lo Sp mm v0 v1 v2 v3 v4 jc jp
    HLO H48 H16 H63 Hmm Hv0 Hv1 Hv2 Hv3 Hv4 MI ST FR.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (munch_refl [(lo, Sp + 128)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite (sx32_int v0) by exact Hv0. do 4 step. take false.
  step. rewrite (sx32_int v1) by exact Hv1. do 3 step. take false.
  step. rewrite (sx32_int v2) by exact Hv2. do 3 step. take false.
  step. rewrite (sx32_int v3) by exact Hv3. do 3 step. take false.
  step. rewrite (sx32_int v4) by exact Hv4. step.
  do 3 step.
  pose proof (rw_ro5 _ _ _ _ _ _ _ _ _ FR) as RO.
  assert (Hm4 : Sp mod 4 = 0) by (Z.div_mod_to_equations; lia).
  eapply evt_cut.
  { eapply CC with (p := RpHot v0 v1 v2 v3 v4) (mm := mm) (lo := lo);
      rewrite ?unsigned_lit by lia; unfold CHECK_CLAMP_FRAME, RP_HOT_SIZE.
    - exact Hm4.
    - exact Hm4.
    - lia.
    - unfold hot_int; cbn [prefill_ms adapt_min_ms adapt_max_ms adapt_margin servo_clamp_ppm]; lia.
    - unfold INT_MAX; lia.
    - reflexivity.
    - exact RO.
    - exact MI.
    - exact ST.
    - lia.
    - lia.
    - right; lia. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
    MU' & WM' & MI' & ST' & RO').
  rewrite ret_pc_even by first [lia | reflexivity].
  rewrite !unsigned_lit in MU' by lia. unfold CHECK_CLAMP_FRAME in MU'.
  pose proof (rw_cells_transport rsegs _ _ m' Sp _ FR MU' WM' ltac:(cbn [disjoint_from]; split; [lia | exact I]))
    as FR'.
  pose proof (munch_trans _ m m0 m' MU (munch_weaken [(Sp - 48, Sp)] [(lo, Sp + 128)] m0 m'
    ltac:(unfold sub_fp; cbn [outside]; intros x [Hx _]; split; [lia | exact I]) MU')) as MU2.
  pose proof (wmono_trans rsegs m m0 m' WM WM') as WM2.
  clear FR MU WM MU' WM' RO RO' ST'.
  unfold lsv in FR'.
  do 14 step.
  apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU2 | exact WM2].
Qed.

(* ---- the SR level: decode's released lib/U/Prog/fd_glue.v glue (g_pre, g_above, g_run), with g_cno / g_cv for
   this program's two SR callees in the shape of its g_crt ---- *)

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

Lemma nth_firstn_lt : forall {X : Type} (l : list X) k i, (i < k)%nat -> nth_error (firstn k l) i = nth_error l i.
Proof.
  intros X l. induction l as [|x l IH]; intros [|k] [|i] H; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

Lemma nth_skipn : forall {X : Type} (l : list X) a i, nth_error (skipn a l) i = nth_error l (a + i).
Proof.
  intros X l. induction l as [|x l IH]; intros [|a] i.
  - destruct i; reflexivity.
  - destruct i; reflexivity.
  - reflexivity.
  - cbn. apply IH.
Qed.

Lemma blk_slice : forall B m A bs a k, blk_data B m A bs -> 0 <= a -> 0 <= k -> a + k <= Z.of_nat (length bs) ->
  blk_data B m (A + a) (firstn (Z.to_nat k) (skipn (Z.to_nat a) bs)).
Proof.
  intros B m A bs a k HD Ha Hk Hak i Hi.
  rewrite firstn_length_le in Hi by (rewrite length_skipn; lia).
  rewrite nth_firstn_lt by lia. rewrite nth_skipn.
  replace (A + a + i) with (A + (a + i)) by lia. rewrite (HD (a + i) ltac:(lia)). f_equal. lia.
Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
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

(* the two SR callees of the loop body: a call's frame is the caller's frame below spZ regs *)
Lemma g_cno : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A r nn cur bs bres
    (P : config -> Prop),
  (forall fx'' : YK11.FPState, @check_no_overread_contract fx'' rc B API) ->
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CNO_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 r -> YK11.getr regs 11 = Z_to_bv 64 nn -> YK11.getr regs 12 = Z_to_bv 64 cur ->
  INT_MIN <= cur <= INT_MAX -> 0 <= nn <= REPLY_MAX -> Z.of_nat (length bs) = nn -> blk_data B mem r bs ->
  (0 < nn -> in_block L A r nn) -> frm_zero (@fp_csr fx') -> res_ok_slots A bres -> cno_room bres nn ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A r nn cur bs bres P CNO FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 Hcur Hnn Hlen BD IB Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply SR_bind.
  { apply (CNO fx' L A regs mem md r nn cur bs bres SEGS).
    - exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs CNO_STACK FR Hra Hal H1 H2
        ltac:(unfold CNO_STACK, CNO_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hcur.
    - exact Hnn.
    - exact Hlen.
    - exact BD.
    - exact IB.
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
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp Eb Hres2).
  apply (g_above stk S L A regs mem md CNO_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
    ltac:(unfold CNO_STACK, CNO_FRAME, ALLOC_STACK; lia)).
  intros a Ha. destruct Ha.
Qed.

Lemma g_cv : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A r nn cur bs bres
    (P : config -> Prop),
  (forall fx'' : YK11.FPState, @check_value_contract fx'' rc B API) ->
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CV_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 r -> YK11.getr regs 11 = Z_to_bv 64 nn -> YK11.getr regs 12 = Z_to_bv 64 cur ->
  INT_MIN <= cur <= INT_MAX -> 0 <= nn <= REPLY_MAX -> Z.of_nat (length bs) = nn -> blk_data B mem r bs ->
  (0 < nn -> in_block L A r nn) -> frm_zero (@fp_csr fx') -> res_ok_slots A bres -> cv_room bres nn ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur) ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_VALUE) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A r nn cur bs bres P CV FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 Hcur Hnn Hlen BD IB Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply SR_bind.
  { apply (CV fx' L A regs mem md r nn cur bs bres SEGS).
    - exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs CV_STACK FR Hra Hal H1 H2
        ltac:(unfold CV_STACK, CV_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hcur.
    - exact Hnn.
    - exact Hlen.
    - exact BD.
    - exact IB.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & G210 & Eb & Hkept & Hgk & Hro2 & Hres2 & Hidt).
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
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp G210 Eb Hres2).
  apply (g_above stk S L A regs mem md CV_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
    ltac:(unfold CV_STACK, CV_FRAME, ALLOC_STACK; lia)).
  intros a Ha. destruct Ha.
Qed.

End G.

Lemma en_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x NO. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply NO; cbn [outside]; (split; [lia | exact I]).
Qed.

Lemma lf_callee_cases : forall x, callee_saved x ->
  x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ x = 9 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/
  x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27.
Proof. intros x Hx. unfold callee_saved in Hx. lia. Qed.

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
Hypothesis CNO : forall fx' : YK11.FPState, @check_no_overread_contract fx' rc B API.
Hypothesis CV : forall fx' : YK11.FPState, @check_value_contract fx' rc B API.
Hypothesis CC : check_clamp_contract.

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
Hypothesis Hn26 : n < 2 ^ 26.

Local Abbreviation Sx := (spZ regs0).
Local Abbreviation Sp := (spZ regs0 - 128).
Local Abbreviation P' := (bv_unsigned (reg_get regs0 10)).
Local Abbreviation sv0 := (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
  (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24)
  (reg_get regs0 25)).
Local Abbreviation Post := (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).

Lemma f_bounds : 8368 <= stk /\ YM05.alloc_ceiling + stk <= Sx /\ Sx mod 16 = 0 /\ Sx <= 2 ^ 47 /\
  LF_RES_TOP < YM05.alloc_ceiling /\ 0 <= n.
Proof.
  pose proof Hpre as (_ & _ & _ & _ & _ & Hal & Hceil & _).
  pose proof Hk as Hk'. unfold LLVM_K, LLVM_FRAME, CNO_STACK, CNO_FRAME, ALLOC_STACK in Hk'.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  split; [lia|]. split; [exact Hceil|]. split; [exact Hal|]. split; [exact Hsp|]. split; [exact Hrt | lia].
Qed.

Lemma f_pay : 0 < n -> In (P', n) (blocks L0 A0) /\ 4096 <= P' /\ P' + n <= YM05.alloc_ceiling /\ P' = p.
Proof.
  intros Hn0.
  pose proof Hpre as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [_ (q & Hq & Hqp)]]; [lia|].
  pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
  assert (E : P' = p).
  { assert (E10 : reg_get regs0 10 = Z_to_bv 64 p) by exact Hp. rewrite E10. apply MState.unsigned_lit. lia. }
  rewrite E. split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia.
Qed.

Lemma f_p'range : 0 <= P' < 2 ^ 64.
Proof.
  pose proof (bv_unsigned_in_range _ (reg_get regs0 10)) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in R. exact R.
Qed.

(* the payload is a live block of every later state, with its bytes *)
Lemma f_blk : forall L A mem md, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md -> 0 < n ->
  In (P', n) (blocks L A) /\ blk_data B mem P' pl.
Proof.
  intros L A mem md (HM & _ & _ & _ & _ & _ & _ & Hblk & Hbyt & _) Hn0.
  destruct (f_pay Hn0) as (Hin & H1 & H2 & E).
  split; [exact (Hblk _ _ Hin)|].
  intros i Hi. rewrite (Hbyt _ _ i Hin ltac:(lia)). rewrite E. exact (Hpd i Hi).
Qed.

Lemma f_norm : forall L A mem md cs, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  (cells_size cs <= 128)%nat ->
  rw_cells rsegs mem Sp cs -> rw_cells rsegs (normalize rsegs mem) Sp cs.
Proof.
  intros L A mem md cs FR Hsz HC. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  pose proof BI as (SEGS & _).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6).
  apply (lf_rw_cells_norm B mem Sp cs SEGS MI); [|exact HC].
  intros i Hi Himg. pose proof (lf_in_img_top B _ SEGS Himg). pose proof (rw_cells_bound _ _ _ _ HC). lia.
Qed.

Lemma f_stk : forall L A mem md, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  Frame.stk rsegs (normalize rsegs mem) (Sx - stk) Sp.
Proof.
  intros L A mem md FR. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw & _ & _ & MI).
  pose proof BI as (SEGS & _).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  apply lf_stk; [lia | lia |]. intros a Ha. unfold writable_at.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
  rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem MI)
             (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
  rewrite <- SEGS. exact (Hstw a ltac:(lia)).
Qed.

Lemma sr_exit : forall (fx' : YK11.FPState) L A regs mem md mm vs jc jp,
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md -> res_ok_slots A b ->
  reg_get regs 2 = Z_to_bv 64 Sp -> reg_get regs 3 = reg_get regs0 3 -> reg_get regs 4 = reg_get regs0 4 ->
  reg_get regs 8 = Z_to_bv 64 mm -> reg_get regs 26 = reg_get regs0 26 -> reg_get regs 27 = reg_get regs0 27 ->
  (mm = 1984 \/ mm = 16320) -> length vs = 5%nat -> Forall (fun v => INT_MIN <= v <= INT_MAX) vs ->
  rw_cells rsegs mem Sp (CB 4 jc :: CB 16 jp :: map (fun v => C4 (Z_to_bv 64 v)) vs ++ sv0) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12cc0) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md mm vs jc jp Hfrm FR Hres R2 R3 R4 R8 R26 R27 Hmm Hl Hvs HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & _).
  destruct vs as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 vs']]]]]]; cbn [length] in Hl; try discriminate.
  apply Forall_cons_iff in Hvs as [Hv0 Hvs]. apply Forall_cons_iff in Hvs as [Hv1 Hvs].
  apply Forall_cons_iff in Hvs as [Hv2 Hvs]. apply Forall_cons_iff in Hvs as [Hv3 Hvs].
  apply Forall_cons_iff in Hvs as [Hv4 _].
  cbn [map app] in HC.
  pose proof (fun H => f_norm L A mem md _ FR H HC) as HCn.
  specialize (HCn ltac:(cbn [cells_size csize lsv Nat.add]; lia)).
  pose proof (f_stk L A mem md FR) as STn.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12cc0) mem md L A).
  - exact FR.
  - lia.
  - lia.
  - unfold Regs6ss.mkR_of. rewrite R2, R3, R4, R8, R26, R27.
    eapply (sx_evt CC); [| | | | exact Hmm | exact Hv0 | exact Hv1 | exact Hv2 | exact Hv3 | exact Hv4
      | exact (mem_inv_normalize rsegs mem) | exact STn | exact HCn]; lia.
  - intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM).
    do 5 eexists. exists [(Sx - stk, Sp + 128)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply en_out1 in NO. lia.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel FR'.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' &
      HE & _ & _).
    injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
    apply SR_ret.
    assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 0) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (RP : regs_preserved regs0 regs').
    { intros r Hr. rewrite (lf_getr_eqv _ _ _ Hx).
      destruct (lf_callee_cases r Hr) as [-> | Hr'].
      - cbn. replace (spZ regs0 - 128 + 128) with (spZ regs0) by lia. unfold spZ.
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

Lemma map_c4_size : forall vs, cells_size (map (fun v => C4 (Z_to_bv 64 v)) vs) = (4 * length vs)%nat.
Proof. induction vs as [|v vs IH]; cbn [map cells_size csize length]; [reflexivity | rewrite IH; lia]. Qed.

Lemma hcells_size : forall jc jp vs jv, (length vs <= 5)%nat -> cells_size (hcells jc jp vs jv sv0) = 128%nat.
Proof.
  intros jc jp vs jv Hl. unfold hcells. cbn [cells_size csize]. rewrite cells_size_app, map_c4_size.
  cbn [cells_size csize lsv]. lia.
Qed.

(* the loop head 0x12bf4 at the SR level *)
Definition LH (i : nat) (fx' : YK11.FPState) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) : Prop :=
  exists mm at0 vs jc jp jv,
    frm_zero (@fp_csr fx') /\ lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md /\ res_ok_slots A b /\
    YK11.getr regs 2 = Z_to_bv 64 Sp /\ YK11.getr regs 3 = YK11.getr regs0 3 /\
    YK11.getr regs 4 = YK11.getr regs0 4 /\ YK11.getr regs 8 = Z_to_bv 64 mm /\ YK11.getr regs 9 = Z_to_bv 64 n /\
    YK11.getr regs 18 = Z_to_bv 64 P' /\ YK11.getr regs 21 = Z_to_bv 64 (Z.of_nat i) /\
    YK11.getr regs 22 = Z_to_bv 64 at0 /\ YK11.getr regs 23 = Z_to_bv 64 (nzb P') /\
    YK11.getr regs 24 = Z_to_bv 64 (Sp + 20) /\ YK11.getr regs 25 = Z_to_bv 64 5 /\
    YK11.getr regs 26 = YK11.getr regs0 26 /\ YK11.getr regs 27 = YK11.getr regs0 27 /\
    (mm = 1984 \/ mm = 16320) /\ 0 <= at0 <= n /\ length vs = i /\ (i < 5)%nat /\
    Forall (fun v => INT_MIN <= v <= INT_MAX) vs /\
    rw_cells rsegs mem Sp (hcells jc jp vs jv sv0).

Lemma pres_get : forall r1 r2 (k : Z) v, regs_preserved r1 r2 -> callee_saved k ->
  YK11.getr r1 (Z_to_bv 5 k) = v -> YK11.getr r2 (Z_to_bv 5 k) = v.
Proof. intros r1 r2 k v Hp1 Hk1 E. rewrite (Hp1 k Hk1). exact E. Qed.

Ltac cs := unfold callee_saved; lia.

(* reg_get facts of a machine state carried to the config registers it is equivalent to *)
Ltac xr Hx Rk E := lazymatch type of Rk with reg_get _ ?k = ?v => lazymatch type of Hx with Regs6ss.xregs_eqv _ ?r' =>
  assert (E : reg_get r' k = v) by (rewrite <- (Hx k eq_refl); exact Rk) end end.
(* a callee-saved register across a call *)
Tactic Notation "pz" constr(Hrp) constr(E) constr(kz) ident(E') :=
  lazymatch type of E with _ ?r1 _ = ?v => lazymatch type of Hrp with regs_preserved r1 ?r2 =>
  assert (E' : YK11.getr r2 (Z_to_bv 5 kz) = v) by (rewrite (Hrp kz ltac:(cs)); exact E) end end.

(* the reply slice data[at, at + n) as the two calls see it *)
Lemma f_slice : forall L A mem md at1 nsl, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  0 <= at1 -> 0 <= nsl -> at1 + nsl <= n ->
  blk_data B mem (at1 + P') (firstn (Z.to_nat nsl) (skipn (Z.to_nat at1) pl)) /\
  (0 < nsl -> in_block L A (at1 + P') nsl) /\
  Z.of_nat (length (firstn (Z.to_nat nsl) (skipn (Z.to_nat at1) pl))) = nsl.
Proof.
  intros L A mem md at1 nsl FR H1 H2 H3.
  split; [|split].
  - destruct (Z.eq_dec nsl 0) as [Z0|Z0].
    + rewrite Z0. cbn [Z.to_nat firstn]. apply blk_data_nil.
    + destruct (f_blk L A mem md FR ltac:(lia)) as (_ & BD). rewrite Z.add_comm.
      apply blk_slice; [exact BD | lia | lia | lia].
  - intros Hs0. destruct (f_blk L A mem md FR ltac:(lia)) as (Hin & _). exists P', n. split; [exact Hin | lia].
  - rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia.
Qed.

Lemma room_cno : forall nsl, 0 <= nsl <= 255 -> cno_room b nsl.
Proof. intros nsl Hs. destruct Hroom as (R1 & R2 & R3). unfold cno_room, CAPMAX in *. lia. Qed.

Lemma room_cv : forall nsl, 0 <= nsl <= 255 -> cv_room b nsl.
Proof. intros nsl Hs. destruct Hroom as (R1 & R2 & R3). unfold cv_room, CAPMAX in *. lia. Qed.

Lemma sr_step : forall i fx' L A regs mem md, LH i fx' L A regs mem md ->
  (forall fx'' L' A' regs' mem' md', LH (S i) fx'' L' A' regs' mem' md' ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx'' regs' (Z_to_bv 64 0x12bf4) mem' (YK11.seg_rom (ms_segs B))) md') Post) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12bf4) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros i fx' L A regs mem md (mm & at0 & vs & jc & jp & jv & Hfrm & FR & Hres & G2 & G3 & G4 & G8 & G9 & G18 &
    G21 & G22 & G23 & G24 & G25 & G26 & G27 & Hmm & Hat & Hl & Hi & Hvs & HC) IH.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof f_p'range as HP'.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  assert (HPB : 0 < n -> bytes_at rsegs (normalize rsegs mem) P' pl).
  { intros Hn0. destruct (f_blk L A mem md FR Hn0) as (_ & BD). destruct (f_pay Hn0) as (_ & P1 & P2 & _).
    apply bytes_at_normalize; [exact MI|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact BD]. }
  assert (HP0 : 0 < n -> 4096 <= P' /\ P' + n <= Sp).
  { intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & _). lia. }
  pose proof (fun H => f_norm L A mem md _ FR H HC) as HCn.
  specialize (HCn ltac:(rewrite hcells_size by lia; lia)).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 Sp) by exact G2.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 n) by exact G9.
  assert (E18 : reg_get regs 18 = Z_to_bv 64 P') by exact G18.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 at0) by exact G22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (nzb P')) by exact G23.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12bf4) mem md L A).
  { exact FR. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2, E9, E18, E22, E23.
    unfold hcells in HCn.
    eapply sa_evt with (pl := pl); [lia | lia | exact Hlen | lia | exact HP' | exact HPB | exact HP0 | lia
      | exact HCn | exact (munch_refl _ _) | exact (wmono_refl _ _)]. }
  { intros ms (R & m' & jc' & at1 & nsl & cur & -> & R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & R12 & R18 & R19 & R20 &
      R21 & R22 & R23 & R24 & R25 & R26 & R27 & Hcur & Hat1 & Hnsl & Hsum & MU & WM & FRc).
    do 5 eexists. exists [(Sp, Sp + 128)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply en_out1 in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (R' & m'' & jc' & at1 & nsl & cur & HE & R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & R12 & R18 & R19 &
    R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & Hcur & Hat1 & Hnsl & Hsum & MU & WM & FRc).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  xr Hx1 R1 F1. xr Hx1 R2 F2. xr Hx1 R3 F3. xr Hx1 R4 F4. xr Hx1 R8 F8. xr Hx1 R9 F9. xr Hx1 R10 F10.
  xr Hx1 R11 F11. xr Hx1 R12 F12. xr Hx1 R18 F18. xr Hx1 R19 F19. xr Hx1 R20 F20. xr Hx1 R21 F21. xr Hx1 R22 F22.
  xr Hx1 R23 F23. xr Hx1 R24 F24. xr Hx1 R25 F25. xr Hx1 R26 F26. xr Hx1 R27 F27.
  clear R1 R2 R3 R4 R8 R9 R10 R11 R12 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel1 FRc) as FC1. clear FRc.
  fold (hcells jc' jp vs jv sv0) in FC1.
  assert (G2' : YK11.getr regs1 2 = Z_to_bv 64 Sp) by exact F2.
  assert (Hsp1 : spZ regs1 = Sp) by (unfold spZ at 1; rewrite G2'; apply MState.unsigned_lit; lia).
  destruct (f_slice L A m1 md at1 nsl FR1 ltac:(lia) ltac:(lia) ltac:(lia)) as (BD1 & IB1 & Hbs).
  set (bs := firstn (Z.to_nat nsl) (skipn (Z.to_nat at1) pl)) in *.
  assert (H1 : YK11.getr regs1 1 = Z_to_bv 64 0x12c98) by exact F1.
  rewrite <- SEGS. change (Z_to_bv 64 77140) with (Z_to_bv 64 CHECK_NO_OVERREAD).
  eapply (g_cno B API SEGS AX ERRNO_LOW stk Sx L0 A0 mem0 md0 _ regs1 m1 md L A (at1 + P') nsl cur bs b).
  { exact CNO. } { exact FR1. } { lia. } { lia. }
  { rewrite H1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp1. replace (Sx - 128) with (Sx + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact B3. }
  { rewrite Hsp1. unfold CNO_STACK, CNO_FRAME, ALLOC_STACK. lia. }
  { lia. } { lia. }
  { change (YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)). rewrite <- Htp0. exact (eq_trans F4 G4). }
  { exact F10. } { exact F11. } { exact F12. } { exact Hcur. }
  { unfold REPLY_MAX. lia. } { exact Hbs. } { exact BD1. } { exact IB1. } { exact Hfrm. } { exact Hres. }
  { apply room_cno. lia. }
  intros fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp2 Eb2 Hres2 Hab2.
  rewrite H1.
  rewrite SEGS in Hab2.
  assert (FC2 : rw_cells rsegs mem2 Sp (hcells jc' jp vs jv sv0)).
  { apply (lf_rw_cells_frame m1); [exact FC1|]. intros a Ha. rewrite hcells_size in Ha by lia.
    apply Hab2. lia. }
  pz Hrp2 F2 2 P2. pz Hrp2 F3 3 P3. pz Hrp2 F4 4 P4. pz Hrp2 F8 8 P8. pz Hrp2 F9 9 P9. pz Hrp2 F18 18 P18.
  pz Hrp2 F19 19 P19. pz Hrp2 F20 20 P20. pz Hrp2 F21 21 P21. pz Hrp2 F22 22 P22. pz Hrp2 F23 23 P23.
  pz Hrp2 F24 24 P24. pz Hrp2 F25 25 P25. pz Hrp2 F26 26 P26. pz Hrp2 F27 27 P27.
  (* 0x12c98-0x12ca4 *)
  pose proof (fun H => f_norm L2 A2 mem2 md2 _ FR2 H FC2) as FC2n.
  specialize (FC2n ltac:(rewrite hcells_size by lia; lia)).
  assert (E2' : reg_get regs2 2 = Z_to_bv 64 Sp) by exact P2.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx2 regs2 (Z_to_bv 64 0x12c98) mem2 md2 L2 A2).
  { exact FR2. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2'. eapply sb_evt. exact FC2n. }
  { intros ms (cur' & Hcur' & ->). do 5 eexists. exists (@nil (Z * Z)).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x Hx NO. exfalso. apply NO. exact I. }
  intros Rb Fb pcb fcb m0'' HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as (cur' & Hcur' & HE). injection HE as ER EF EP EC EM. subst Rb Fb pcb fcb m0''.
  assert (Q1 : YK11.getr regs3 1 = Z_to_bv 64 0x12ca8) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
  assert (Q10 : YK11.getr regs3 10 = Z_to_bv 64 (at1 + P'))
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P20).
  assert (Q11 : YK11.getr regs3 11 = Z_to_bv 64 nsl) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P19).
  assert (Q12 : YK11.getr regs3 12 = Z_to_bv 64 cur') by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
  assert (Q2 : YK11.getr regs3 2 = Z_to_bv 64 Sp) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
  assert (Q3 : YK11.getr regs3 3 = YK11.getr regs0 3)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P3 G3)).
  assert (Q4 : YK11.getr regs3 4 = YK11.getr regs0 4)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P4 G4)).
  assert (Q8 : YK11.getr regs3 8 = Z_to_bv 64 mm)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P8 G8)).
  assert (Q9 : YK11.getr regs3 9 = Z_to_bv 64 n) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P9).
  assert (Q18 : YK11.getr regs3 18 = Z_to_bv 64 P') by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P18).
  assert (Q19 : YK11.getr regs3 19 = Z_to_bv 64 nsl) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P19).
  assert (Q21 : YK11.getr regs3 21 = Z_to_bv 64 (Z.of_nat i))
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P21 G21)).
  assert (Q22 : YK11.getr regs3 22 = Z_to_bv 64 at1) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P22).
  assert (Q23 : YK11.getr regs3 23 = Z_to_bv 64 (nzb P')) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P23).
  assert (Q24 : YK11.getr regs3 24 = Z_to_bv 64 (Sp + 20))
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P24 G24)).
  assert (Q25 : YK11.getr regs3 25 = Z_to_bv 64 5)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P25 G25)).
  assert (Q26 : YK11.getr regs3 26 = YK11.getr regs0 26)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P26 G26)).
  assert (Q27 : YK11.getr regs3 27 = YK11.getr regs0 27)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P27 G27)).
  pose proof (lf_rw_cells_rel m3 _ _ _ Hrel3 FC2n) as FC3.
  assert (Hsp3 : spZ regs3 = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  destruct (f_slice L2 A2 m3 md2 at1 nsl FR3 ltac:(lia) ltac:(lia) ltac:(lia)) as (BD3 & IB3 & _).
  fold bs in BD3, IB3.
  rewrite <- SEGS. change (Z_to_bv 64 77384) with (Z_to_bv 64 CHECK_VALUE).
  eapply (g_cv B API SEGS AX ERRNO_LOW stk Sx L0 A0 mem0 md0 _ regs3 m3 md2 L2 A2 (at1 + P') nsl cur' bs b).
  { exact CV. } { exact FR3. } { lia. } { lia. }
  { rewrite Q1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp3. replace (Sx - 128) with (Sx + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact B3. }
  { rewrite Hsp3. unfold CV_STACK, CV_FRAME, ALLOC_STACK. lia. }
  { lia. } { lia. }
  { rewrite Q4. exact Htp0. }
  { exact Q10. } { exact Q11. } { exact Q12. } { exact Hcur'. }
  { unfold REPLY_MAX. lia. } { exact Hbs. } { exact BD3. } { exact IB3. } { exact Hfrm2. } { exact Hres2. }
  { apply room_cv. lia. }
  intros fx4 L4 A4 regs4 mem4 md4 Hfrm4 FR4 Hrp4 G410 Eb4 Hres4 Hab4.
  rewrite Q1.
  rewrite SEGS in Hab4.
  assert (FC4 : rw_cells rsegs mem4 Sp (hcells jc' jp vs jv sv0)).
  { apply (lf_rw_cells_frame m3); [exact FC3|]. intros a Ha. rewrite hcells_size in Ha by lia.
    apply Hab4. lia. }
  pz Hrp4 Q2 2 S2. pz Hrp4 Q3 3 S3. pz Hrp4 Q4 4 S4. pz Hrp4 Q8 8 S8. pz Hrp4 Q9 9 S9. pz Hrp4 Q18 18 S18.
  pz Hrp4 Q19 19 S19. pz Hrp4 Q21 21 S21. pz Hrp4 Q22 22 S22. pz Hrp4 Q23 23 S23. pz Hrp4 Q24 24 S24.
  pz Hrp4 Q25 25 S25. pz Hrp4 Q26 26 S26. pz Hrp4 Q27 27 S27.
  assert (T2 : reg_get regs4 2 = Z_to_bv 64 Sp) by exact S2.
  assert (T3 : reg_get regs4 3 = YK11.getr regs0 3) by exact S3.
  assert (T4 : reg_get regs4 4 = YK11.getr regs0 4) by exact S4.
  assert (T8 : reg_get regs4 8 = Z_to_bv 64 mm) by exact S8.
  assert (T9 : reg_get regs4 9 = Z_to_bv 64 n) by exact S9.
  assert (T10 : reg_get regs4 10 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur')) by exact G410.
  assert (T18 : reg_get regs4 18 = Z_to_bv 64 P') by exact S18.
  assert (T19 : reg_get regs4 19 = Z_to_bv 64 nsl) by exact S19.
  assert (T21 : reg_get regs4 21 = Z_to_bv 64 (Z.of_nat i)) by exact S21.
  assert (T22 : reg_get regs4 22 = Z_to_bv 64 at1) by exact S22.
  assert (T23 : reg_get regs4 23 = Z_to_bv 64 (nzb P')) by exact S23.
  assert (T24 : reg_get regs4 24 = Z_to_bv 64 (Sp + 20)) by exact S24.
  assert (T25 : reg_get regs4 25 = Z_to_bv 64 5) by exact S25.
  assert (T26 : reg_get regs4 26 = YK11.getr regs0 26) by exact S26.
  assert (T27 : reg_get regs4 27 = YK11.getr regs0 27) by exact S27.
  pose proof (rp_uci_int_range (zbytes bs) cur' Hcur') as Hv.
  pose proof (fun H => f_norm L4 A4 mem4 md4 _ FR4 H FC4) as FC4n.
  specialize (FC4n ltac:(rewrite hcells_size by lia; lia)).
  subst i.
  (* 0x12ca8-0x12cbc *)
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx4 regs4 (Z_to_bv 64 0x12ca8) mem4 md4 L4 A4).
  { exact FR4. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite T2, T3, T4, T8, T9, T10, T18, T19, T21, T22, T23, T24, T25, T26, T27.
    eapply sc_evt; [lia | lia | exact Hmm | lia | lia | lia | exact Hv | exact Hvs | exact Hi | exact FC4n]. }
  { intros ms [(Rq & m' & mm' & at0' & vs' & jc'' & jp' & jv' & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & _ & _ & _ & _ & MUq & WMq & _)
      | (Rq & m' & mm' & vs' & jc'' & jp' & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & MUq & WMq & _)].
    - do 5 eexists. exists [(Sp, Sp + 128)].
      split; [reflexivity|]. split; [exact MUq|]. split; [exact WMq|].
      intros x Hx NO. left. apply en_out1 in NO. lia.
    - do 5 eexists. exists [(Sp, Sp + 128)].
      split; [reflexivity|]. split; [exact MUq|]. split; [exact WMq|].
      intros x Hx NO. left. apply en_out1 in NO. lia. }
  intros Rc Fc pcc fcc m0c HQ regs5 m5 Hx5 Hrel5 FR5.
  destruct HQ as [(Rq & m'' & mm' & at0' & vs' & jc'' & jp' & jv' & HE & V2 & V3 & V4 & V8 & V9 & V18 & V21 & V22 &
      V23 & V24 & V25 & V26 & V27 & Hmm' & Hat' & Hlv & Hi' & Hvs' & _ & _ & FRc)
    | (Rq & m'' & mm' & vs' & jc'' & jp' & HE & V2 & V3 & V4 & V8 & V26 & V27 & Hmm' & Hlv & Hvs' & _ & _ & FRc)].
  - injection HE as ER EF EP EC EM. subst Rq Fc pcc fcc m''.
    pose proof (lf_rw_cells_rel m5 _ _ _ Hrel5 FRc) as FC5.
    rewrite <- SEGS. apply (IH (mkFP (@fp_regs fx4) (@fp_csr fx4)) L4 A4 regs5 m5 md4).
    exists mm', at0', vs', jc'', jp', jv'.
    split; [exact Hfrm4|]. split; [exact FR5|]. split; [exact Hres4|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V2|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V3|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V4|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V8|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V9|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V18|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V21|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V22|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V23|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V24|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V25|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V26|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V27|].
    split; [exact Hmm'|]. split; [exact Hat'|]. split; [exact Hlv|]. split; [exact Hi'|].
    split; [exact Hvs' | exact FC5].
  - injection HE as ER EF EP EC EM. subst Rq Fc pcc fcc m''.
    pose proof (lf_rw_cells_rel m5 _ _ _ Hrel5 FRc) as FC5.
    rewrite <- SEGS.
    xr Hx5 V2 W2. xr Hx5 V3 W3. xr Hx5 V4 W4. xr Hx5 V8 W8. xr Hx5 V26 W26. xr Hx5 V27 W27.
    apply (sr_exit (mkFP (@fp_regs fx4) (@fp_csr fx4)) L4 A4 regs5 m5 md4 mm' vs' jc'' jp'); try assumption.
Qed.


Lemma sr_loop : forall k i fx' L A regs mem md, k = (5 - i)%nat -> LH i fx' L A regs mem md ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12bf4) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  induction k as [|k IHk]; intros i fx' L A regs mem md Hk5 HL.
  - exfalso. destruct HL as (mm & at0 & vs & jc & jp & jv & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & Hi & _ & _). lia.
  - apply (sr_step i fx' L A regs mem md HL). intros fx'' L' A' regs' mem' md' HL'.
    apply (IHk (S i) fx'' L' A' regs' mem' md'); [lia | exact HL'].
Qed.

Hypothesis Hres0 : res_ok_slots A0 b.

(* 0x12b68: the prologue and the first loop head *)
Lemma sr_entry : frm_zero (@fp_csr fx) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0) Post.
Proof.
  intros Hfrm.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof f_p'range as HP'.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn11 &
    Hpl0 & Hrod0).
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p n Hpre Hro) as FR0.
  assert (Esp : Sx = bv_unsigned (reg_get regs0 2)) by reflexivity.
  assert (E10 : reg_get regs0 10 = Z_to_bv 64 P') by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (E11 : reg_get regs0 11 = Z_to_bv 64 n) by exact Hn11.
  assert (ST0 : Frame.stk rsegs (normalize rsegs mem0) (Sx - stk) (bv_unsigned (reg_get regs0 2))).
  { rewrite <- Esp. apply lf_stk; [lia | lia |].
    intros a Ha. unfold writable_at.
    assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
    rewrite (wview_rel_rw rsegs mem0 (normalize rsegs mem0) _ (mem_rel_normalize rsegs mem0 Hro)
               (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    rewrite <- SEGS. exact (Hstw0 a Ha). }
  assert (HPB : 0 < n -> bytes_at rsegs (normalize rsegs mem0) P' pl).
  { intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & E). rewrite E in *.
    apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact Hpd]. }
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 md0 L0 A0).
  { exact FR0. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of, LLVM_ENTRY. rewrite E10, E11.
    eapply e0_evt with (pl := pl).
    - exact ST0.
    - rewrite <- Esp. lia.
    - exact (mem_inv_normalize rsegs mem0).
    - rewrite <- Esp. lia.
    - lia.
    - exact HP'.
    - exact Hlen.
    - exact HPB.
    - intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & _). lia.
    - intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & _). lia. }
  { intros ms (R & m' & mm & at0 & vs & jc & jp & jv & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & MU & WM & _).
    do 5 eexists. exists [(bv_unsigned (reg_get regs0 2) - 128, bv_unsigned (reg_get regs0 2))].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply en_out1 in NO. rewrite <- Esp in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (R' & m'' & mm & at0 & vs & jc & jp & jv & HE & V2 & V3 & V4 & V8 & V9 & V18 & V21 & V22 & V23 &
    V24 & V25 & V26 & V27 & Hmm & Hat & Hlv & Hi & Hvs & _ & _ & FRc).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  pose proof (lf_rw_cells_rel m1 _ _ _ Hrel1 FRc) as FC1.
  rewrite <- Esp in V2, V24, FC1.
  rewrite <- SEGS.
  apply (sr_loop 5 0 (mkFP (@fp_regs fx) (@fp_csr fx)) L0 A0 regs1 m1 md0 eq_refl).
  exists mm, at0, vs, jc, jp, jv.
  split; [exact Hfrm|]. split; [exact FR1|]. split; [exact Hres0|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V2|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V3|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V4|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V8|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V9|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V18|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V21|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V22|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V23|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V24|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V25|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V26|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V27|].
  split; [exact Hmm|]. split; [exact Hat|]. split; [exact Hlv|]. split; [exact Hi|].
  split; [exact Hvs | exact FC1].
Qed.

End Run.

(* decode's llvm_n_bound: the payload size is that of a live block, or 0 *)
Lemma llvm_n_bound : forall stk empty L A regs mem md ra p n,
  lib_pre B API stk empty L A regs mem md ra p n -> 0 <= n < 2 ^ 47.
Proof.
  intros stk empty L A regs mem md ra p n (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [Hn (q & Hq & _)]]; [lia|].
  destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia.
Qed.

Theorem LLVMFuzzerTestOneInput_holds_of : LLVMFuzzerTestOneInput_sr_contract B API.
Proof using MALLOC FREE ERRNO_LOW SINK BND CT CNO CV CC.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof (llvm_n_bound stk empty L A regs mem md ra p n Hpre) as Hnb.
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn11 & _).
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig].
  2:{ apply (llvm_early B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      rewrite Hn11. rewrite MState.unsigned_lit by lia. exact Hbig. }
  exact (sr_entry stk empty L A regs mem md ra p n pl b j BI Hk Hra Hpre Hn Hpl Hsn Hsp Hroom Hro Hsmall Hres Hfrm).
Qed.

End M.
