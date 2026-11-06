(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 372 of its 389 lines of code are new or changed and 43 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require Import qdisc_spec.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Prog Require Import reac_qdisc_etf_catchup_slots_c
  check_slots_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of fuzz_qdisc.c:89-102 in the ubsan image (0x12ad0, frame 96 bytes), against
    U/Prog/LLVMFuzzerTestOneInput_c.v, with the contracts of the two callees as premises. The structure
    (frame cells [saved], exit lemma, fuel-indexed loop lemma, [Qk]) is ported from libreac/fuzz_knock's
    released U/Prog/LLVMFuzzerTestOneInput.v; the loop body steps are qdisc's. The UBSan pointer-overflow
    traps (unimp at 0x12c28) are refuted from the contract's bounds on the data pointer. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma rw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hl, Hw.
  rewrite cells_bytes_length in B2 by exact W1.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma rw_cells_app_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma bytes_at_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma lor_lt_pow : forall x y n, 0 < n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lor x y < 2 ^ n.
Proof.
  intros x y n Hn Hx Hy. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor x y) 0) as [E|E]; [pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)); lia|].
  assert (Hpos : 0 < Z.lor x y) by (pose proof (Z.lor_nonneg x y); lia).
  pose proof (Z.log2_spec (Z.lor x y) Hpos) as [_ Hup].
  rewrite Z.log2_lor in Hup by lia.
  assert (Lx : Z.log2 x < n).
  { destruct (Z.eq_dec x 0) as [Ex|Ex]; [subst x; rewrite Z.log2_nonpos by lia; lia | apply Z.log2_lt_pow2; lia]. }
  assert (Ly : Z.log2 y < n).
  { destruct (Z.eq_dec y 0) as [Ey|Ey]; [subst y; rewrite Z.log2_nonpos by lia; lia | apply Z.log2_lt_pow2; lia]. }
  assert (2 ^ Z.succ (Z.max (Z.log2 x) (Z.log2 y)) <= 2 ^ n) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Ltac refute_trap T := exfalso; zify_cond T; repeat (rewrite Z.mod_small in T by lia); lia.

Ltac sd := first [ eassumption | reflexivity | lia
                 | (rewrite unsigned_lit by lia; lia)
                 | (rewrite !unsigned_lit by lia; lia)
                 | (rewrite unsigned_lit_wrap; rewrite ?Z.mod_small by lia; lia)
                 | (apply bv_eq; vm_compute; reflexivity) ].

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(** The early return: [size - 2^26] compared unsigned against [-2^26 + 1] is not below it only when
    [1 <= size < 2^26]. *)
Lemma big_check : forall x, 0 <= x < 2 ^ 64 ->
  18446744073642442753 <= (x + -67108864) mod 18446744073709551616 -> 1 <= x.
Proof.
  intros x Hx H. destruct (Z.eq_dec x 0) as [E|E]; [subst x; cbn in H; lia | lia].
Qed.

Lemma land7 : forall x, 0 <= x -> 0 <= Z.land x 7 <= 7.
Proof.
  intros x Hx. replace (Z.land x 7) with (x mod 8).
  - pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
  - symmetry. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

(** The u16 lead [b0 | b1 << 8]. *)
Lemma lead2_bound : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  0 <= Z.lor (Z.shiftl x 8 mod 18446744073709551616) y < 2 ^ 16.
Proof.
  intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  apply lor_lt_pow; lia.
Qed.

(** A fact about every byte, checked on all 256 of them. *)
Lemma all256 : forall (f g : Z -> Z),
  forallb (fun y => Z.eqb (f y) (g y)) (map Z.of_nat (seq 0 256)) = true ->
  forall x, 0 <= x < 2 ^ Z.of_N 8 -> f x = g x.
Proof.
  intros f g H x Hx. change (2 ^ Z.of_N 8) with 256 in Hx. rewrite forallb_forall in H.
  apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat x). split; [lia |]. apply in_seq. lia.
Qed.

(** [addiw s2, s2, -1] on the budget counter (1 to 7). *)
Lemma sw_dec : forall x, 1 <= x <= 7 -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 (x + -1))) = x - 1.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity. replace (bv_modulus 32) with (2^32) by reflexivity.
  rewrite (Z.mod_small (x + -1 + 2^31) (2^32)) by lia.
  replace (x + -1 + 2 ^ 31 - 2 ^ 31) with (x - 1) by lia. apply unsigned_lit. lia.
Qed.

Section QdiscRun.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo : Z).
Hypothesis LO : lo + 96 <= bv_unsigned sp.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HMI0 : mem_inv rsegs m.
Hypothesis ST0 : stk rsegs m lo (bv_unsigned sp).

(** The prologue saves s9 .. s0 and ra at sp-88 .. sp-8 (8 unused bytes at sp-96). *)
Definition saved : list cell :=
  [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition Qk (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

(** The epilogue at 0x12bf0: a0 := 0, restore, return. *)
Lemma qdisc_exit : forall (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
                          x18 x19 x20 x21 x22 x23 x24 x25 t3' t4' t5' t6' : word)
                          (m1 : word -> option byte) (cs8 : list cell),
  cells_size cs8 = 8%nat ->
  rw_cells rsegs m1 (bv_unsigned sp + -96) (cs8 ++ saved) ->
  stk rsegs m1 lo (bv_unsigned sp + -96) ->
  munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 ->
  wmono rsegs m m1 ->
  mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
             x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x12bf0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25
         t3' t4' t5' t6' m1 cs8 HS FR ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  apply rw_cells_app_split in FR. destruct FR as [F8 FS]. rewrite HS in FS.
  replace (bv_unsigned sp + -96 + Z.of_nat 8) with (bv_unsigned sp + -88) in FS by lia.
  unfold saved in FS.
  do 13 zstep.
  assert (FR : rw_cells rsegs m1 (bv_unsigned sp + -96) (cs8 ++ saved)).
  { apply rw_cells_app_join; [exact F8|]. rewrite HS.
    replace (bv_unsigned sp + -96 + Z.of_nat 8) with (bv_unsigned sp + -88) by lia. exact FS. }
  clear F8 FS.
  eapply stk_release in FR; [ | exact ST | lia ].
  rewrite cells_size_app, HS in FR. cbn [saved cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in FR by lia.
  clear ST.
  zstep.
  finish.
Qed.

Variables (p : word) (data : list byte).
Hypothesis DJ : bv_unsigned p + Z.of_nat (length data) <= lo \/ bv_unsigned sp <= bv_unsigned p.
Hypothesis HPB : bv_unsigned p + Z.of_nat (length data) < 2 ^ 63.
Hypothesis HPNZ : 0 < Z.of_nat (length data) -> 0 < bv_unsigned p.
Hypothesis SLOTS : qdisc_slots_contract.
Hypothesis CHECK : qdisc_check_contract.

(** The loop head 0x12b44: s2 the budgets left, s3 the cursor at offset c of data, s9 the bytes left;
    s4 .. s8 the constants 1, 2, &fps (0x103e8), 0xab and ~&fps the setup put there. *)
Definition loop_ok (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (bw cur rem : word) (c : Z) (m1 : word -> option byte) (cs8 : list cell),
  (Z.to_nat (bv_unsigned bw) <= fuel)%nat -> 1 <= bv_unsigned bw <= 7 ->
  bv_unsigned cur = bv_unsigned p + c -> 0 <= c -> c + bv_unsigned rem = Z.of_nat (length data) ->
  cells_size cs8 = 8%nat ->
  rw_cells rsegs m1 (bv_unsigned sp + -96) (cs8 ++ saved) ->
  bytes_at rsegs m1 (bv_unsigned p) data ->
  stk rsegs m1 lo (bv_unsigned sp + -96) ->
  munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
             bw cur (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 66536) (Z_to_bv 64 171)
             (Z_to_bv 64 18446744073709485079) rem s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x12b44) fc None m1 (seg_rom rsegs)).

(** 0x12b8c, after the frame rate is loaded: the two calls, then the budget count-down. *)
Lemma qdisc_after_lw : forall (fuel : nat), loop_ok fuel ->
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (s0w s1w bw cur rem : word) (f c : Z) (m1 : word -> option byte) (cs8 : list cell),
  (Z.to_nat (bv_unsigned bw) <= S fuel)%nat -> 1 <= bv_unsigned bw <= 7 ->
  bv_unsigned cur = bv_unsigned p + c -> 0 <= c -> c + bv_unsigned rem = Z.of_nat (length data) ->
  bv_unsigned s0w < 2 ^ 16 ->
  -2^31 <= f < 2^31 -> s1w = Z_to_bv 64 f ->
  cells_size cs8 = 8%nat ->
  rw_cells rsegs m1 (bv_unsigned sp + -96) (cs8 ++ saved) ->
  bytes_at rsegs m1 (bv_unsigned p) data ->
  stk rsegs m1 lo (bv_unsigned sp + -96) ->
  munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' s0w s1w a0' a1' a2' a3' a4' a5' a6' a7'
             bw cur (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 66536) (Z_to_bv 64 171)
             (Z_to_bv 64 18446744073709485079) rem s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x12b8c) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel LOOP ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s0w s1w bw cur rem f c m1 cs8
    HF HB HC HC0 HCN HS0 Hf Es1 HS8 FR HDATA ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 s0w) as R0. pose proof (bv_unsigned_in_range 64 bw) as Rbw.
  unfold bv_modulus in R0, Rbw.
  pose proof SLOTS as SL. unfold qdisc_slots_contract, QDISC_SLOTS in SL.
  pose proof CHECK as CK. unfold qdisc_check_contract, QDISC_CHECK in CK.
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply SL with (lead := bv_unsigned s0w) (fps := f); first [ lia | reflexivity | eassumption ]. }
  intros ms' (y1 & y2 & y3 & E). subst ms'.
  fix_ret.
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply CK with (lead := bv_unsigned s0w) (fps := f); first [ lia | reflexivity | eassumption ]. }
  intros ms' (z1 & z2 & z3 & E). subst ms'.
  fix_ret.
  zstep.
  match goal with |- context [Z_to_bv 64 (bv_swrap 32 (bv_unsigned bw + -1))] =>
    pose proof (sw_dec (bv_unsigned bw) HB) as Ubw';
    remember (Z_to_bv 64 (bv_swrap 32 (bv_unsigned bw + -1))) as bw' eqn:Ebw';
    clear Ebw'
  end.
  zstep.
  if_cases EZ.
  - zify_cond EZ.
    eapply LOOP; try eassumption; sd.
  - zify_cond EZ.
    zstep.
    eapply qdisc_exit; eassumption.
Qed.

(** 0x12b88, the load of fps[k]: one case per table entry. *)
Lemma qdisc_calls : forall (fuel : nat), loop_ok fuel ->
  forall (ra' t0' t1' t2' x9 a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (aw s0w bw cur rem : word) (k c : Z) (m1 : word -> option byte) (cs8 : list cell),
  (Z.to_nat (bv_unsigned bw) <= S fuel)%nat -> 1 <= bv_unsigned bw <= 7 ->
  bv_unsigned cur = bv_unsigned p + c -> 0 <= c -> c + bv_unsigned rem = Z.of_nat (length data) ->
  bv_unsigned aw = 66536 + 4 * k -> 0 <= k < 6 ->
  bv_unsigned s0w < 2 ^ 16 ->
  cells_size cs8 = 8%nat ->
  rw_cells rsegs m1 (bv_unsigned sp + -96) (cs8 ++ saved) ->
  bytes_at rsegs m1 (bv_unsigned p) data ->
  stk rsegs m1 lo (bv_unsigned sp + -96) ->
  munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' s0w x9 aw a1' a2' a3' a4' a5' a6' a7'
             bw cur (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 66536) (Z_to_bv 64 171)
             (Z_to_bv 64 18446744073709485079) rem s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x12b88) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel LOOP ra' t0' t1' t2' x9 a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' aw s0w bw cur rem k c m1 cs8
    HF HB HC HC0 HCN HA Hk HS0 HS8 FR HDATA ST MU WM HMI.
  assert (Hk6 : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
  destruct Hk6 as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  - replace aw with (Z_to_bv 64 66536) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
    zstep. eapply (qdisc_after_lw fuel LOOP) with (f := 8000) (c := c); try eassumption; sd.
  - replace aw with (Z_to_bv 64 66540) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
    zstep. eapply (qdisc_after_lw fuel LOOP) with (f := 4000) (c := c); try eassumption; sd.
  - replace aw with (Z_to_bv 64 66544) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
    zstep. eapply (qdisc_after_lw fuel LOOP) with (f := 0) (c := c); try eassumption; sd.
  - replace aw with (Z_to_bv 64 66548) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
    zstep. eapply (qdisc_after_lw fuel LOOP) with (f := -1) (c := c); try eassumption; sd.
  - replace aw with (Z_to_bv 64 66552) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
    zstep. eapply (qdisc_after_lw fuel LOOP) with (f := 96000) (c := c); try eassumption; sd.
  - replace aw with (Z_to_bv 64 66556) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
    zstep. eapply (qdisc_after_lw fuel LOOP) with (f := 2147483647) (c := c); try eassumption; sd.
Qed.

Lemma qdisc_loop : forall fuel, loop_ok fuel.
Proof.
  induction fuel as [|fuel IH]; unfold loop_ok;
    intros ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' bw cur rem c m1 cs8
           HF HB HC HC0 HCN HS8 FR HDATA ST MU WM HMI.
  { exfalso. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 rem) as Rrem.
  pose proof (bv_unsigned_in_range 64 cur) as Rcur.
  pose proof (bv_unsigned_in_range 64 p) as Rp.
  pose proof (bytes_at_bound rsegs m1 (bv_unsigned p) data HDATA) as Bd.
  unfold bv_modulus in Rsp, Rrem, Rcur, Rp.
  zstep.
  if_cases R0.
  { zify_cond R0. zstep. zstep.
    eapply (qdisc_calls fuel IH) with (k := 0) (c := c); try eassumption; sd. }
  zify_cond R0.
  assert (Hp1 : 0 < bv_unsigned p) by (apply HPNZ; lia).
  assert (HB0 : ov_read_bytes rsegs m1 cur 1 = Some [nth (Z.to_nat c) data (Z_to_bv 8 0)]).
  { rewrite <- (Z_to_bv_bv_unsigned cur). rewrite HC. apply (bytes_at_byte m1 (bv_unsigned p) data c); [exact HDATA | lia]. }
  remember (nth (Z.to_nat c) data (Z_to_bv 8 0)) as b0 eqn:Eb0.
  pose proof (bv_unsigned_in_range 8 b0) as Rb0. unfold bv_modulus in Rb0.
  zstep. zstep.
  if_cases T1; [refute_trap T1 |].
  zstep. zstep.
  if_cases R1.
  { zify_cond R1. do 4 zstep.
    eapply (qdisc_calls fuel IH) with (k := 0) (c := c + 1); try eassumption; sd. }
  zify_cond R1.
  assert (HB1 : ov_read_bytes rsegs m1 (Z_to_bv 64 (bv_unsigned cur + 1)) 1
                = Some [nth (Z.to_nat (c + 1)) data (Z_to_bv 8 0)]).
  { rewrite HC. replace (bv_unsigned p + c + 1) with (bv_unsigned p + (c + 1)) by lia.
    apply bytes_at_byte; [exact HDATA | lia]. }
  remember (nth (Z.to_nat (c + 1)) data (Z_to_bv 8 0)) as b1 eqn:Eb1.
  pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1.
  zstep. zstep.
  if_cases T2; [refute_trap T2 |].
  do 5 zstep.
  match goal with |- context [Z_to_bv 64 (Z.lor ?A ?B)] =>
    assert (L16 : 0 <= Z.lor A B < 2 ^ 16) by (apply lead2_bound; lia);
    remember (Z_to_bv 64 (Z.lor A B)) as s0w eqn:Es0;
    assert (HS0 : bv_unsigned s0w < 2 ^ 16) by (subst s0w; rewrite unsigned_lit by lia; lia);
    clear Es0
  end.
  if_cases R2.
  2: { zify_cond R2. do 4 zstep.
       eapply (qdisc_calls fuel IH) with (k := 0) (c := c + 2); try eassumption; sd. }
  zify_cond R2.
  assert (HB2 : ov_read_bytes rsegs m1 (Z_to_bv 64 (bv_unsigned cur + 2)) 1
                = Some [nth (Z.to_nat (c + 2)) data (Z_to_bv 8 0)]).
  { rewrite HC. replace (bv_unsigned p + c + 2) with (bv_unsigned p + (c + 2)) by lia.
    apply bytes_at_byte; [exact HDATA | lia]. }
  remember (nth (Z.to_nat (c + 2)) data (Z_to_bv 8 0)) as b2 eqn:Eb2.
  pose proof (bv_unsigned_in_range 8 b2) as Rb2. unfold bv_modulus in Rb2.
  zstep. zstep.
  if_cases T3; [refute_trap T3 |].
  do 9 zstep.
  match goal with |- context [Z_to_bv 64 (Z.shiftl (Z.land ?E 255) 2)] =>
    assert (Hsel : Z.shiftl (Z.land E 255) 2 = 4 * (bv_unsigned b2 mod 6))
      by (clear - Rb2; revert Rb2; generalize (bv_unsigned b2);
          match goal with |- forall z, _ -> @?L z = @?R z =>
            apply (all256 L R); vm_compute; reflexivity
          end);
    rewrite Hsel; clear Hsel
  end.
  assert (Hk : 0 <= bv_unsigned b2 mod 6 < 6) by (apply Z.mod_pos_bound; lia).
  remember (bv_unsigned b2 mod 6) as k eqn:Ek.
  zstep.
  if_cases T4; [refute_trap T4 |].
  do 4 zstep.
  eapply (qdisc_calls fuel IH) with (k := k) (c := c + 3); try eassumption; sd.
Qed.

Lemma qdisc_entry : forall (m1 : word -> option byte), m1 = m ->
  forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  bytes_at rsegs m1 (bv_unsigned p) data ->
  bv_unsigned a1 = Z.of_nat (length data) ->
  evt rsegs Qk
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 p a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12ad0) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 Em t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HD HN.
  assert (MU : munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1) by (rewrite Em; apply munch_refl).
  assert (WM : wmono rsegs m m1) by (rewrite Em; apply wmono_refl).
  pose proof HMI0 as HMI. rewrite <- Em in HMI. pose proof ST0 as ST. rewrite <- Em in ST.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  pose proof (bv_unsigned_in_range 64 p) as Rp.
  pose proof ST as [Hlo _].
  unfold bv_modulus in Rsp, Ra1, Rp.
  carve_frame 96%nat ST.
  do 12 zstep.
  do 4 zstep.
  if_cases EBIG.
  { eapply qdisc_exit with (cs8 := [CB 8 _]); [reflexivity | exact FR | exact ST | exact MU | exact WM | exact HMI]. }
  zify_cond EBIG.
  assert (HL1 : 1 <= bv_unsigned a1) by (apply (big_check (bv_unsigned a1)); [lia | exact EBIG]).
  assert (Hp1 : 0 < bv_unsigned p) by (apply HPNZ; lia).
  do 3 zstep.
  if_cases T0; [refute_trap T0 |].
  match goal with HDm : bytes_at rsegs ?mm (bv_unsigned p) data |- _ =>
    pose proof (bytes_at_byte mm (bv_unsigned p) data 0 HDm ltac:(lia)) as HB0
  end.
  unfold wa in HB0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in HB0.
  remember (nth (Z.to_nat 0) data (Z_to_bv 8 0)) as b0 eqn:Eb0.
  pose proof (bv_unsigned_in_range 8 b0) as Rb0. unfold bv_modulus in Rb0.
  zstep. zstep.
  match goal with |- context [Z_to_bv 64 (Z.land ?X 7)] =>
    assert (Hb7 : 0 <= Z.land X 7 <= 7) by (apply land7; lia);
    remember (Z_to_bv 64 (Z.land X 7)) as bw eqn:Ebw;
    assert (Ubw : 0 <= bv_unsigned bw <= 7) by (subst bw; rewrite unsigned_lit by lia; lia);
    clear Ebw
  end.
  zstep.
  if_cases EB0.
  { eapply qdisc_exit with (cs8 := [CB 8 _]); [reflexivity | exact FR | exact ST | exact MU | exact WM | exact HMI]. }
  zify_cond EB0.
  do 7 zstep.
  eapply (qdisc_loop (Z.to_nat (bv_unsigned bw))) with (c := 1) (cs8 := [CB 8 _]); try eassumption; sd.
Qed.

End QdiscRun.

Theorem qdisc_main_holds : qdisc_slots_contract -> qdisc_check_contract -> qdisc_main_contract.
Proof.
  intros SL CK. unfold qdisc_main_contract, LLVM_QDISC, LLVM_QDISC_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo data HD HN HMI ST LO SPA DJ HPB HPNZ.
  change (evt rsegs (Qk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12ad0) fc None m (seg_rom rsegs))).
  eapply qdisc_entry; first [ exact eq_refl | eassumption ].
Qed.
