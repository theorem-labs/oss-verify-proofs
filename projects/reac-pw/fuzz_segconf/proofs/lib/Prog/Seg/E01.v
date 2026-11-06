(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 397 of its 449 lines of code are new or changed and 522 lines of the source are left out. *)
(* Segment E01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): [0x137c4, 0x138a0],
   ENTRY -> K138a4 (Prog/LLVMFuzzerTestOneInput_c.v's S_E01), proved at the cut record CPseg.
   The run from ENTRY: the prologue (0x137c4 `addi sp,sp,-0xd0`; ra, s0 .. s11 saved at S - 8 .. S - 104), the
   n >= 2^26 exit not taken (0x137fc `srli a2,a1,26`, 0x13800 `bnez a2`: GV bounds n below 2^26), 0x13804
   `mv s3,a0`, then the three header bytes of fuzz_u8 (fuzz.h:39-42) on four paths, n = 0, 1, 2 and >= 3:
   s1 = b0 mod 40 (0x1380c-0x13828: `ld a2` of the .rodata word K = 0x0666666666666667 at 0x10a08, `mulhu`, `mul`
   by 40, `sub`; e01_mulhu: mulhu(b, K) = b / 40 for every byte b), the flags byte or 0 in the frame cell sp + 8
   (0x13830 / 0x13840 `sd zero`, 0x13858 `sd a0`), s5 = n - 3 or 0, s3 = p + min(3, n), s2 = (b2 & 3) + 1 or 1;
   a0 = 0x40e8 and malloc(16616) at 0x1388c (ra 0x13890) through Tac_b1.b1_malloc_call from hb = []. From malloc's
   return a second run (0x13890 `mv s8,a0`, `lui s10,2`, `addiw a1,s10,0x414`, `addi a0,zero,1`) reaches
   calloc(1, 9236) at 0x138a0 (ra 0x138a4), taken through Tac_b1.b1_calloc_call from hb = [(c, 16616)] with
   CallocBigC.calloc_contract_big (the premise of SegEnd.seg_E01_stmt). Its continuation closes Inv_K138a4 with
   seg_cuts.P_K138a4: a0 = m, s8 = c, s1 = seg_cap, s2 = seg_nfiles, s3 / s5 the cursor after the header
   (seg_cur_at / seg_cur_n at 0), s10 = MC_N, the flags cell (kept by both calls' stack clause), c's 16616 bytes as
   cells over the cut memory (Tac_b1.b1_hb on the normalized memory, Tac_slot.sl_rw_of_stk, then back through
   mem_rel), m's 9236 zero bytes (calloc), both blocks 16-aligned and outside the reserved pages
   (Tac_b1.b1_blk_noimg_segs). The payload facts (e01_*_ok) relate the run's values to seg_spec's decode.
   Adapted from reac-pw/fuzz_role's Prog/Seg/E01.v and U/Prog/Seg/E01.v (commit cb8205fb6109:
   the run from Inv_ENTRY on the normalized memory, FR with hb = [], malloc as a Kind B step, the frame cell carved
   apart from the saved registers).
   Part of the proof of LLVMFuzzerTestOneInput (its segment E01); no released proof of fuzz_segconf's
   LLVMFuzzerTestOneInput exists; written new. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require CallocBigC.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec seg_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c SegEnd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import Tac_slot Tac_b1 SegWalkMainA.
Import ListNotations.
Open Scope Z_scope.

(* ---- The payload values the run computes, by the number of input bytes (fuzz.h:39-42, fuzz_segconf.c:584-586) ---- *)
Definition e01_cap (inp : list byte) : Z := match inp with [] => 0 | b :: _ => bv_unsigned b mod 40 end.
Definition e01_fl (inp : list byte) : Z := match inp with _ :: b :: _ => bv_unsigned b | _ => 0 end.
Definition e01_nf (inp : list byte) : Z := match inp with _ :: _ :: b :: _ => bv_unsigned b mod 4 + 1 | _ => 1 end.
Definition e01_h (inp : list byte) : Z := Z.min 3 (Z.of_nat (length inp)).
Definition e01_rest (inp : list byte) : Z := Z.of_nat (length inp) - Z.min 3 (Z.of_nat (length inp)).

(* dec_files k makes exactly k files. *)
Lemma e01_dec_len : forall k l, length (SegModel.dec_files k l) = k.
Proof.
  induction k as [|k IH]; intros l; [reflexivity|].
  cbn [SegModel.dec_files].
  destruct (SegModel.fuzz_u8 l) as [lb i1]. destruct (SegModel.fuzz_u16 i1) as [len i2].
  destruct (SegModel.fuzz_take i2 len) as [q i3]. cbn [length]. rewrite IH. reflexivity.
Qed.

Lemma e01_cap_ok : forall inp, seg_spec.seg_cap inp = e01_cap inp.
Proof. intros [|b0 [|b1 [|b2 l]]]; reflexivity. Qed.

Lemma e01_fl_ok : forall inp, seg_spec.seg_flags inp = e01_fl inp.
Proof. intros [|b0 [|b1 [|b2 l]]]; reflexivity. Qed.

Lemma e01_nf_ok : forall inp, seg_spec.seg_nfiles inp = e01_nf inp.
Proof.
  intros [|b0 [|b1 [|b2 l]]].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, seg_spec.seg_in, seg_spec.zs,
      SegModel.decode.
    cbn [map SegModel.fuzz_u8 SegModel.p_files].
    rewrite e01_dec_len. cbn [e01_nf].
    pose proof (b1_byte_rng b2) as R. pose proof (Z.mod_pos_bound (bv_unsigned b2) 4 ltac:(lia)) as M.
    rewrite Z2Nat.id by lia. lia.
Qed.

Lemma e01_hdr_len : forall inp, Z.of_nat (length (seg_spec.seg_cur inp 0)) = e01_rest inp.
Proof.
  intros [|b0 [|b1 [|b2 l]]]; unfold seg_spec.seg_cur, seg_spec.seg_hdr, seg_spec.seg_in, seg_spec.zs, e01_rest;
    cbn [seg_spec.seg_skip map SegModel.fuzz_u8 snd length]; rewrite ?length_map; lia.
Qed.

Lemma e01_cur_at_ok : forall inp p, seg_spec.seg_cur_at inp p 0 = p + e01_h inp.
Proof.
  intros inp p. unfold seg_spec.seg_cur_at. rewrite e01_hdr_len. unfold e01_rest, e01_h. lia.
Qed.

Lemma e01_cur_n_ok : forall inp, seg_spec.seg_cur_n inp 0 = e01_rest inp.
Proof. intros inp. unfold seg_spec.seg_cur_n. apply e01_hdr_len. Qed.

(* ---- The arithmetic of 0x1381c-0x13828 and 0x1387c ---- *)
(* K = 0x0666666666666667, the .rodata word at 0x10a08 (40 K = 2^64 + 24): mulhu(b, K) = b / 40 for every byte. *)
Lemma e01_mulhu_tab : forallb (fun k => Z.shiftr (Z.of_nat k * 461168601842738791) 64 =? Z.of_nat k / 40)
  (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma e01_mulhu : forall x y, 0 <= x < 256 -> y = 461168601842738791 -> Z.shiftr (x * y) 64 = x / 40.
Proof.
  intros x y Hx ->. pose proof e01_mulhu_tab as T. rewrite forallb_forall in T.
  specialize (T (Z.to_nat x)). cbv beta in T. rewrite Z2Nat.id in T by lia.
  apply Z.eqb_eq. apply T. apply in_seq. lia.
Qed.

Lemma e01_land : forall x c, 0 <= x -> c = 3 -> Z.land x c = x mod 4.
Proof. intros x c Hx ->. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

(* ---- Bytes and words ---- *)
Lemma e01_b0 : forall m a b l, bytes_at rsegs m a (b :: l) -> bytes_at rsegs m a [b].
Proof.
  intros m a b l (H1 & H2 & H). cbn [length] in H2. split; [exact H1|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia]. exact (H 0%nat ltac:(cbn [length]; lia)).
Qed.

Lemma e01_bk : forall m a bs (k : Z) b, bytes_at rsegs m a bs -> nth_error bs (Z.to_nat k) = Some b -> 0 <= k ->
  bytes_at rsegs m (a + k) [b].
Proof.
  intros m a bs k b (H1 & H2 & H) E Hk.
  assert (Hl : (Z.to_nat k < length bs)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
  cbn [nth_error]. rewrite <- E. rewrite <- (H (Z.to_nat k) Hl). f_equal. unfold wa. f_equal. lia.
Qed.

Lemma e01_rd0 : forall m (a : word) b, bytes_at rsegs m (bv_unsigned a) [b] -> ov_read_bytes rsegs m a 1 = Some [b].
Proof.
  intros m a b H.
  assert (E : a = wa (bv_unsigned a + Z.of_nat 0)).
  { unfold wa. rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self. }
  rewrite E. rewrite (bytes_at_ov_read rsegs m (bv_unsigned a) [b] 0 1 H) by (cbn; lia). reflexivity.
Qed.

Lemma e01_rdz : forall m x b, bytes_at rsegs m x [b] -> ov_read_bytes rsegs m (Z_to_bv 64 x) 1 = Some [b].
Proof.
  intros m x b H.
  replace (Z_to_bv 64 x) with (wa (x + Z.of_nat 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m x [b] 0 1 H) by (cbn; lia). reflexivity.
Qed.

(* lbu's zero extension (Mem.zxb) keeps the byte's value. *)
Lemma e01_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply MState.unsigned_lit. pose proof (b1_byte_rng b). lia. Qed.

Lemma e01_weq_l : forall (x : word) e, bv_unsigned x mod 2 ^ 64 = e mod 2 ^ 64 -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- (Z_to_bv_lit_self x). apply Z_to_bv_eqm. exact H. Qed.

(* 0x137fc `srli a2,a1,26`; 0x13800 `bnez a2`: not taken for n < 2^26. *)
Lemma e01_cond : forall u, 0 <= u < 2 ^ 26 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = false.
Proof. intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. Qed.

Ltac e01_side := first [ lia | rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

(* The quotient of the `mulhu` and the `andi 3`, as / 40 and mod 4. *)
Ltac e01_arith :=
  repeat match goal with
  | |- context [Z.shiftr (?x * ?y) 64] => rewrite (e01_mulhu x y) by e01_side
  | |- context [Z.land ?x ?c] => rewrite (e01_land x c) by e01_side
  end.

Ltac e01_weq :=
  first [ reflexivity
        | apply e01_weq_l; rewrite ?e01_zxb; e01_arith; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia
        | symmetry; apply e01_weq_l; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

(* A branch: keep the side the facts allow. *)
Ltac e01_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "EC" in if_cases H; zify_cond H; try (exfalso; lia)
  | _ => idtac
  end.

(* ---- The run: ENTRY to malloc's entry with ra = 0x13890 ---- *)
Definition e01_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p : Z) (inp : list byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s5' t3' t4' t5' t6' : word)
         (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x13890) (Z_to_bv 64 (bv_unsigned sp + -208)) gp tp t0' t1' t2' s0 s1' a0' a1' a2'
                  a3' a4' a5' a6' a7' s2' s3' s4 s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x16b7c) fc None m' (seg_rom rsegs) /\
    a0' = Z_to_bv 64 C_SIZE /\ s1' = Z_to_bv 64 (e01_cap inp) /\ s2' = Z_to_bv 64 (e01_nf inp) /\
    s3' = Z_to_bv 64 (p + e01_h inp) /\ s5' = Z_to_bv 64 (e01_rest inp) /\
    Frame.munch [(bv_unsigned sp - 208, bv_unsigned sp)] m m' /\ Frame.wmono rsegs m m' /\
    bytes_at rsegs m' (bv_unsigned sp - 200) (le8 (Z_to_bv 64 (e01_fl inp))) /\
    bytes_at rsegs m' (bv_unsigned sp - 104)
      (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
       le8 s1 ++ le8 s0 ++ le8 ra).

(* The frame is carved in two: the thirteen saved registers at S - 104 (FRS) and, below them, the eight-byte
   flags cell at S - 200 = sp + 8 with the rest of [S - 200, S - 104) above it (FRC). *)
Ltac e01_fin sp FRS FRC :=
  let SB := fresh "SB" in let SF := fresh "SF" in
  pose proof (sl_cells_bytes _ _ _ FRS) as SB;
  pose proof (sl_cells_bytes _ _ _ FRC) as SF;
  cbn [Cells.cells_bytes Cells.cbytes] in SB, SF; rewrite ?app_nil_r in SB, SF;
  apply bytes_at_app in SF; destruct SF as [SF _];
  lazymatch type of SB with bytes_at _ _ ?x _ => replace x with (bv_unsigned sp - 104) in SB by lia end;
  lazymatch type of SF with bytes_at _ _ ?y _ => replace y with (bv_unsigned sp - 200) in SF by lia end;
  apply evt_done; unfold e01_post;
  do 20 eexists; split; [reflexivity|];
  split; [|split; [|split; [|split; [|split; [|split; [assumption|split; [assumption|
    split; [exact SF|exact SB]]]]]]]].

Ltac e01_eqs := cbv beta iota delta [e01_cap e01_nf e01_fl e01_h e01_rest]; cbn [length]; try unfold C_SIZE; e01_weq.

Lemma e01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (inp : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 208 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned a0 = p -> bv_unsigned a1 = Z.of_nat (length inp) -> Z.of_nat (length inp) < 2 ^ 26 ->
    p + Z.of_nat (length inp) <= lo -> bytes_at rsegs m p inp ->
    evt rsegs (e01_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p inp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x137c4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p inp ST LO HMI0 Ep Ha1 H26 Hin Hb.
  subst p.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)] m) as MU.
  assert (Hlo : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 104%nat ST.
  rename FR into FRS.
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 96%nat _ [] [8%nat; 88%nat]) in FR; [|reflexivity].
  cbn [app mk_CB_cells] in FR.
  rename FR into FRC.
  do 16 step.
  if_false_by (e01_cond (bv_unsigned a1) ltac:(lia)).
  step. step.
  destruct inp as [|b0 [|b1 [|b2 rest]]]; cbn [length] in Ha1, H26, Hin.
  - (* n = 0: 0x13840 .. 0x1388c *)
    e01_if.
    do 8 step.
    e01_fin sp FRS FRC.
    all: e01_eqs.
  - (* n = 1: cap = b0 mod 40, flags 0, nfiles 1, the cursor p + 1 *)
    e01_if.
    pose proof (b1_byte_rng b0) as R0.
    pose proof (e01_rd0 _ _ _ (e01_b0 _ _ _ _ Hb)) as HB0.
    clear Hb.
    do 9 step. e01_if.
    do 7 step.
    e01_fin sp FRS FRC.
    all: e01_eqs.
  - (* n = 2: the flags byte b1 into the frame cell, the cursor p + 2 *)
    e01_if.
    pose proof (b1_byte_rng b0) as R0. pose proof (b1_byte_rng b1) as R1.
    pose proof (e01_rd0 _ _ _ (e01_b0 _ _ _ _ Hb)) as HB0.
    pose proof (e01_bk _ _ _ 1 b1 Hb eq_refl ltac:(lia)) as Hb1.
    clear Hb.
    do 9 step. e01_if.
    pose proof (e01_rdz _ _ _ Hb1) as HB1.
    do 4 step. e01_if.
    do 6 step.
    e01_fin sp FRS FRC.
    all: e01_eqs.
  - (* n >= 3: nfiles = (b2 & 3) + 1, the cursor p + 3, n - 3 bytes left *)
    e01_if.
    pose proof (b1_byte_rng b0) as R0. pose proof (b1_byte_rng b1) as R1. pose proof (b1_byte_rng b2) as R2.
    pose proof (e01_rd0 _ _ _ (e01_b0 _ _ _ _ Hb)) as HB0.
    pose proof (e01_bk _ _ _ 1 b1 Hb eq_refl ltac:(lia)) as Hb1.
    pose proof (e01_bk _ _ _ 2 b2 Hb eq_refl ltac:(lia)) as Hb2.
    clear Hb.
    do 9 step. e01_if.
    pose proof (e01_rdz _ _ _ Hb1) as HB1.
    do 4 step. e01_if.
    pose proof (e01_rdz _ _ _ Hb2) as HB2.
    do 8 step.
    e01_fin sp FRS FRC.
    all: e01_eqs.
Qed.

(* ---- The second run: malloc's return 0x13890 to calloc's entry with ra = 0x138a4 (no store) ---- *)
Definition e01_post2 (sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ms' : machine_state) : Prop :=
  exists ra' a0' a1' s8' s10' : word,
    ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8' s9 s10' s11
                  t3 t4 t5 t6) F (Z_to_bv 64 0x16904) fc None m (seg_rom rsegs) /\
    ra' = Z_to_bv 64 0x138a4 /\ a0' = Z_to_bv 64 1 /\ a1' = Z_to_bv 64 M_SIZE /\ s8' = a0 /\
    s10' = Z_to_bv 64 0x2000.

Lemma e01_evt2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs (e01_post2 sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13890) fc None m (seg_rom rsegs)).
Proof.
  intros. do 5 step.
  apply evt_done. unfold e01_post2.
  do 5 eexists. split; [reflexivity|].
  unfold M_SIZE.
  split; [e01_weq|]. split; [e01_weq|]. split; [e01_weq|]. split; e01_weq.
Qed.

(* ---- Cells and zeros over the cut memory ---- *)
Lemma e01_rw_norm : forall m A cs, ro_agree rsegs m -> rw_cells rsegs (normalize rsegs m) A cs -> rw_cells rsegs m A cs.
Proof.
  intros m A cs Hro [[Hwf Hb] Hw]. pose proof (mem_rel_normalize rsegs m Hro) as HR.
  split; [split; [exact Hwf|] |].
  - exact (proj2 (bytes_at_rel rsegs m (normalize rsegs m) _ _ HR) Hb).
  - exact (wr_at_rel rsegs m (normalize rsegs m) _ _ HR Hw).
Qed.

Lemma e01_nth_rep : forall (T : Type) (x : T) n i, (i < n)%nat -> nth_error (repeat x n) i = Some x.
Proof.
  intros T x n. induction n as [|n IH]; intros i Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [repeat nth_error]. apply IH. lia.
Qed.

Lemma e01_zeros : forall m a n, 0 <= a -> a + n <= 2 ^ 64 -> 0 <= n ->
  (forall i, 0 <= i < n -> mbyte rsegs m (a + i) = Some (Z_to_bv 8 0)) ->
  bytes_at rsegs m a (repeat seg_spec.ZERO (Z.to_nat n)).
Proof.
  intros m a n H0 H1 H2 H. split; [exact H0|]. rewrite repeat_length. split; [lia|].
  intros i Hi. rewrite e01_nth_rep by exact Hi.
  pose proof (H (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E. unfold Mem.mrd, wa, seg_spec.ZERO. exact E.
Qed.

(* ---- The segment ---- *)
Section E01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis CAL : CallocBigC.calloc_contract_big B (APIf rc) CallocBigC.CALLOC_PC.

Lemma seg_E01 : S_E01 B APIf ra empty CPseg.
Proof.
  unfold S_E01. intros H1 g c (Ec & HGV & Hpre & Hsp & Hsn & HMI & Hrel & Hres & Hfrm).
  subst c.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSK & HS47 & _ & HGsp & HGtp & _).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  pose proof alloc_ceiling_lt as Hlt.
  pose proof sl_ceil as Hct.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Esp2 : bv_unsigned (YK11.getr (g_regs g) 2) = g_S g).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (Esp : spZ (g_regs g) = g_S g) by exact Esp2.
  (* The input block lies below alloc_ceiling, so below the stack window. *)
  assert (Hpb : 0 <= g_p g /\ g_p g + g_n g <= g_S g - 65536).
  { destruct Hpl as [(Hn0 & Hpe) | (Hn0 & Hin)].
    - rewrite Hn0, Hpe, (ff_empty_val B APIf ra empty FF). lia.
    - destruct (b1_blk B APIf ra empty FF _ _ _ _ _ _ HM Hin) as (_ & Hb1 & Hb2). lia. }
  assert (Ep : bv_unsigned (YK11.getr (g_regs g) 10) = g_p g).
  { rewrite Hp. apply MState.unsigned_lit. lia. }
  assert (En : bv_unsigned (YK11.getr (g_regs g) 11) = Z.of_nat (length (g_in g))).
  { rewrite Hn. apply MState.unsigned_lit. unfold g_n in *. lia. }
  unfold MI in HMI. rewrite SEGS in HMI.
  assert (Hdat' : bytes_at rsegs (normalize rsegs (g_mem g)) (g_p g) (g_in g)).
  { apply (proj1 (bytes_at_rel rsegs _ _ _ _ (mem_rel_normalize rsegs (g_mem g) HMI))).
    split; [lia|]. split; [unfold g_n in Hpb; lia|].
    intros k Hk. pose proof (Hdat (Z.of_nat k) ltac:(lia)) as E. rewrite Nat2Z.id, SEGS in E. exact E. }
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sl_mkR_of. unfold ENTRY.
    apply e01_evt with (lo := g_S g - 65536) (p := g_p g) (inp := g_in g).
    + rewrite Esp2. apply sl_stk_norm; [exact HMI | unfold SL_TOP; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + rewrite Esp2. lia.
    + exact (mem_inv_normalize rsegs (g_mem g)).
    + exact Ep.
    + exact En.
    + unfold g_n in Hn26. lia.
    + unfold g_n in Hpb. lia.
    + exact Hdat'.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s5' &
                    t3' & t4' & t5' & t6' & m'' & HE & E10 & E9 & E18 & E19 & E21 & MU & WM & SF & SB).
    injection HE; intros; subst.
    rewrite Esp2 in MU, SB, SF.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 208, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' _ HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' _ HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    pose proof (proj2 (bytes_at_rel rsegs m' _ _ _ Hrel') SB) as SB'.
    pose proof (proj2 (bytes_at_rel rsegs m' _ _ _ Hrel') SF) as SF'.
    assert (HFR : FR B APIf ra empty g [] (g_L g) (g_A g) regs' m' (g_md g)).
    { apply (sl_fr_of B APIf ra empty FF) with (mem0 := g_mem g).
      - exact HGV.
      - exact HM.
      - exact HW.
      - exact HB.
      - exact HID.
      - exists (m_vmmaps (g_md g)). apply with_vmmaps_self.
      - intros a _ _ _. split; [reflexivity | tauto].
      - intros a _ _ _ _ _. split; [reflexivity | tauto].
      - intros a k i _ _. reflexivity.
      - intros a k Hin. exact Hin.
      - exact Herr.
      - exact Hsn.
      - exact (resb_start (g_b g) (g_A g) Hres).
      - intros a Ha. apply Hstw. rewrite Esp. unfold SLOT_K, SLOT_STACK in Ha. exact Ha.
      - exact Hrel.
      - apply (sl_unch _ _ _ (g_S g - 65536) (g_S g) MU').
        intros x Hx0 O. destruct (Z_le_dec (g_S g - 208) x); destruct (Z_lt_dec x (g_S g)); try lia;
          exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx).
        transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr (g_regs g) 2) + -208)); [reflexivity|].
        rewrite Esp2. unfold fsp, SLOT_FRAME. f_equal; lia.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - unfold saved_bytes, SLOT_SAVE. rewrite <- Hra. exact SB'. }
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x13890) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10' : YK11.getr regs' 10 = Z_to_bv 64 C_SIZE) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g [] (g_L g) (g_A g) regs' m' (g_md g) regs' C_SIZE);
      [exact HFR | cbn [app]; apply Permutation_refl | cbn; lia | unfold hb_bytes; cbn; lia | reflexivity
      | reflexivity | reflexivity
      | rewrite E1; vm_compute; reflexivity | exact E10' | unfold C_SIZE; lia |].
    intros L' A' regs'' mem'' md' res HF'' HP'' RP Hres10 Hres0 Hres16 HK HKH.
    rewrite E1.
    pose proof HF'' as (_ & _ & _ & _ & _ & _ & HMI'' & _).
    unfold MI in HMI''. rewrite SEGS in HMI''.
    (* 0x13890 .. 0x138a0: s8 = c, s10 = 0x2000, a1 = 9236, a0 = 1, `jal calloc` (sl_mid keeps FR). *)
    eapply (sl_mid B APIf ra empty FF g [(res, C_SIZE)] L' A' regs'' mem'' md' (Z_to_bv 64 0x13890));
      [exact HF'' | exact HP'' | rewrite sl_mkR_of; apply e01_evt2 | |].
    + intros ms (ra2 & a02 & a12 & s82 & s102 & -> & _).
      do 3 eexists. split; [reflexivity|].
      split; [exists []; split; [apply munch_refl | split; [apply wmono_refl | intros x _ O; exfalso; apply O; exact I]]|].
      split; [reflexivity|]. split; reflexivity.
    + intros R2 pc2 m02 regs3 m3 HQ2 Hx2 Hrel2 HF3.
      destruct HQ2 as (ra2 & a02 & a12 & s82 & s102 & HE2 & Era2 & Ea02 & Ea12 & Es82 & Es102).
      injection HE2; intros; subst.
      assert (E1b : YK11.getr regs3 1 = Z_to_bv 64 0x138a4) by (rewrite (sl_getr_eqv _ _ _ Hx2); reflexivity).
      assert (E10b : YK11.getr regs3 10 = Z_to_bv 64 1) by (rewrite (sl_getr_eqv _ _ _ Hx2); reflexivity).
      assert (E11b : YK11.getr regs3 11 = Z_to_bv 64 M_SIZE) by (rewrite (sl_getr_eqv _ _ _ Hx2); reflexivity).
      change (Z_to_bv 64 0x16904) with (Z_to_bv 64 CallocBigC.CALLOC_PC).
      apply (b1_calloc_call B APIf ra empty FF g [(res, C_SIZE)] L' A' regs3 m3 md' regs3 1 M_SIZE);
        [exact CAL | exact HF3 | exact HP'' | cbn; lia | unfold hb_bytes, C_SIZE; cbn; lia | reflexivity | reflexivity
        | reflexivity | rewrite E1b; vm_compute; reflexivity | exact E10b | exact E11b | lia | unfold M_SIZE; lia
        | unfold M_SIZE, CallocBigC.CALLOC_BIG_CAP; lia |].
      intros L3 A3 regs4 mem4 md4 res2 HF4 HP4 RP4 Hr10 Hr0 Hr16 HK4 HKH4 HZ4.
      rewrite E1b.
      pose proof HF4 as (_ & _ & _ & _ & _ & _ & HMI4 & _).
      unfold MI in HMI4. rewrite SEGS in HMI4.
      assert (Hinc : In (res, C_SIZE) (hb_cm res res2)) by (unfold hb_cm; right; left; reflexivity).
      assert (Hinm : In (res2, M_SIZE) (hb_cm res res2)) by (unfold hb_cm; left; reflexivity).
      destruct (b1_hb B APIf ra empty FF g (hb_cm res res2) res C_SIZE L3 A3 regs4 mem4 md4 HF4 HP4 Hinc)
        as (STc & Hc4096 & Hcc).
      destruct (b1_hb B APIf ra empty FF g (hb_cm res res2) res2 M_SIZE L3 A3 regs4 mem4 md4 HF4 HP4 Hinm)
        as (_ & Hm4096 & Hmc).
      (* The flags cell sp + 8 = S - 200: kept by malloc, the run and calloc. *)
      assert (SF2 : bytes_at rsegs mem'' (g_S g - 200) (le8 (Z_to_bv 64 (e01_fl (g_in g))))).
      { apply (b1_ba_mbyte m'); [exact SF'|]. intros i Hi. rewrite length_le8 in Hi.
        apply HK. unfold fsp, SLOT_FRAME. lia. }
      assert (SF3 : bytes_at rsegs m3 (g_S g - 200) (le8 (Z_to_bv 64 (e01_fl (g_in g))))).
      { apply (proj2 (bytes_at_rel rsegs m3 _ _ _ Hrel2)). exact (bytes_at_normalize rsegs mem'' _ _ HMI'' SF2). }
      assert (SF4 : bytes_at rsegs mem4 (g_S g - 200) (le8 (Z_to_bv 64 (e01_fl (g_in g))))).
      { apply (b1_ba_mbyte m3); [exact SF3|]. intros i Hi. rewrite length_le8 in Hi.
        apply HK4. unfold fsp, SLOT_FRAME. lia. }
      apply H1. exists res, res2. exists fx, L3, A3, regs4, mem4, md4.
      split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF4|]. split; [exact HP4|].
      unfold CPseg. cbn [cp_K138a4]. unfold seg_cuts.P_K138a4, seg_cuts.rgz, seg_cuts.celz.
      rewrite e01_cap_ok, e01_nf_ok, e01_cur_at_ok, e01_cur_n_ok, e01_fl_ok.
      split; [exact Hr10|].
      split.
      { etransitivity; [exact (RP4 24 ltac:(unfold callee_saved; lia))|]. rewrite (sl_getr_eqv _ _ _ Hx2).
        transitivity (YK11.getr regs'' 10); [reflexivity | exact Hres10]. }
      split.
      { etransitivity; [exact (RP4 9 ltac:(unfold callee_saved; lia))|]. rewrite (sl_getr_eqv _ _ _ Hx2).
        transitivity (YK11.getr regs'' 9); [reflexivity|].
        etransitivity; [exact (RP 9 ltac:(unfold callee_saved; lia))|]. rewrite (sl_getr_eqv _ _ _ Hx).
        reflexivity. }
      split.
      { etransitivity; [exact (RP4 18 ltac:(unfold callee_saved; lia))|]. rewrite (sl_getr_eqv _ _ _ Hx2).
        transitivity (YK11.getr regs'' 18); [reflexivity|].
        etransitivity; [exact (RP 18 ltac:(unfold callee_saved; lia))|]. rewrite (sl_getr_eqv _ _ _ Hx).
        reflexivity. }
      split.
      { etransitivity; [exact (RP4 19 ltac:(unfold callee_saved; lia))|]. rewrite (sl_getr_eqv _ _ _ Hx2).
        transitivity (YK11.getr regs'' 19); [reflexivity|].
        etransitivity; [exact (RP 19 ltac:(unfold callee_saved; lia))|]. rewrite (sl_getr_eqv _ _ _ Hx).
        reflexivity. }
      split.
      { etransitivity; [exact (RP4 21 ltac:(unfold callee_saved; lia))|]. rewrite (sl_getr_eqv _ _ _ Hx2).
        transitivity (YK11.getr regs'' 21); [reflexivity|].
        etransitivity; [exact (RP 21 ltac:(unfold callee_saved; lia))|]. rewrite (sl_getr_eqv _ _ _ Hx).
        reflexivity. }
      split.
      { etransitivity; [exact (RP4 26 ltac:(unfold callee_saved; lia))|]. rewrite (sl_getr_eqv _ _ _ Hx2).
        reflexivity. }
      split.
      { unfold seg_cuts.SEG_FRAME. replace (g_S g - 208 + 8) with (g_S g - 200) by lia. exact SF4. }
      split.
      { destruct (sl_rw_of_stk _ _ _ res (Z.to_nat seg_spec.SEG_C_SIZE) STc ltac:(lia)
                    ltac:(unfold seg_spec.SEG_C_SIZE, C_SIZE in *; lia)) as (junk & HRW).
        exists junk. exact (e01_rw_norm mem4 res _ HMI4 HRW). }
      split.
      { apply e01_zeros; [lia | unfold seg_spec.SEG_M_SIZE, M_SIZE in *; lia | unfold seg_spec.SEG_M_SIZE; lia |].
        intros i Hi. apply HZ4. unfold seg_spec.SEG_M_SIZE in Hi. unfold M_SIZE. lia. }
      split; [exact Hres16|]. split; [exact Hr16|].
      split.
      { exact (b1_blk_noimg_segs B APIf ra empty FF g (hb_cm res res2) res C_SIZE L3 A3 regs4 mem4 md4 HF4 HP4
                 Hinc). }
      exact (b1_blk_noimg_segs B APIf ra empty FF g (hb_cm res res2) res2 M_SIZE L3 A3 regs4 mem4 md4 HF4 HP4
               Hinm).
Qed.

End E01.

Theorem seg_E01_holds : seg_E01_stmt CPseg.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF CAL.
  eapply seg_E01; eassumption.
Qed.
