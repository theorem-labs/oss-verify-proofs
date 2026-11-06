(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Step.v; 317 of its 350 lines of code are new or changed and 668 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/Prog/RcBraidLib.v, with its module paths, module names and numbers changed; 642 of its 674 lines of code are new or changed and 318 lines of the source are left out. *)
(* reac_braid_encode of the fuzz_decode asan-ubsan image (B), entry 0x81cfc, frame 128 bytes:
   reac_braid_encode_exact_holds proves reac_braid_encode_exact_contract of crt_braid_need.v.

   A relocation of the fuzz_ctrl asan-ubsan proof (proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_braid_encode_exact.v of
   a working branch, commit f227c3e2d1b, entry 0x879ec). The entry point: the fuzz_ctrl proof image is the patched
   build (internal path, the binaries cb uses for fuzz_ctrl), where reac_braid_encode STARTS at 0x879ec
   (its nm.txt: 0x879ec, size 0x2ec). The released fuzz_ctrl build puts it at 0x879a0, so the +0x4c is only the
   difference between the two fuzz_ctrl builds, not a skipped prologue. In fuzz_decode the function starts at 0x81cfc
   (nm.txt: 0x81cfc, size 0x2ec), and both statements enter at the first instruction (addi sp, sp, -128) with the
   same premises, so the donor run applies from the start. The two functions are 187 instructions, 178 words equal;
   the 9 others are pc-relative only: auipc/ld of the GOT cell of the shadow offset (GOT_CELL_K 0xa07f0 -> 0x992e8,
   holding CELL_K 0xa95b8 -> 0xa1338), auipc/flw of the float 8388607.0 (0x21ab8 -> 0x20dcc, both 0x4afffffe), and
   the five jal to the report stubs, which the run does not reach.
   Moved numerals (pc in the function, old - 0x5cf0): 0x87a3c -> 0x81d4c (+0x50), 0x87ab4 -> 0x81dc4 (+0xc8),
   0x87b94 -> 0x81ea4 (+0x1a8); by hand: 693688 (CELL_K of fuzz_ctrl, 0xa95b8) -> 0xa1338 (CELL_K of fuzz_decode). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact RcBraid RcBraidLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import RcAsanRT crt_braid_need.
Import ListNotations.
Open Scope Z_scope.

Definition rbb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (a N P ns : Z) (K : Z -> Z -> Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 N)
                  a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc None m' (seg_rom rsegs) /\
    (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get F' k = reg_get F k) /\
    munch [(bv_unsigned sp - 128, bv_unsigned sp); (a, a + 3 * N * ns)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' (bv_unsigned sp - 128) (bv_unsigned sp) /\
    (forall x : word, outside [(bv_unsigned sp - 128, bv_unsigned sp)] (bv_unsigned x) ->
       m' x = rb_enc m (rb_rows a N K (Z.to_nat ns)) x).

(* The fall-through of a shadow check and its slow path meet at J with only register r changed. *)
Ltac rbb_join r CONT :=
  lazymatch goal with
  | |- evt ?S ?Qp (MS ?R ?Fr (if _ then _ else ?J) ?fc' ?sv ?mm' ?rom) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    assert (CONT : forall y : word, evt S Qp (MS (tset p y R) Fr J fc' sv mm' rom))
  end.
Ltac rbb_join_use CONT :=
  lazymatch type of CONT with forall y : word, evt _ _ (MS (tset ?p _ _) _ _ _ _ _ _) =>
  lazymatch goal with |- evt _ _ (MS ?R0 _ _ _ _ _ _) =>
    let v := eval cbv beta iota delta [tget] in (match tget p R0 with Some v => v | None => w0 end) in
    exact (CONT v) end end.

Lemma rbb_chk0 : forall X (k : byte), bv_signed k <> 0 -> (bv_signed k = 0 \/ X mod 8 < bv_signed k) ->
  bv_lts (Z_to_bv 64 (X mod 8)) (Z_to_bv 64 (bv_signed k)) = true.
Proof.
  intros X k H0 H. pose proof (Z.mod_pos_bound X 8 ltac:(lia)). pose proof (rc_byte_signed k).
  rewrite rc_lts_signed by lia. apply Z.ltb_lt. destruct H as [H|H]; [contradiction | exact H].
Qed.

Lemma rbb_chk3 : forall X (k : byte), bv_signed k <> 0 -> (bv_signed k = 0 \/ X mod 8 + 3 < bv_signed k) ->
  bv_lts (Z_to_bv 64 (X mod 8 + 3)) (Z_to_bv 64 (bv_signed k)) = true.
Proof.
  intros X k H0 H. pose proof (Z.mod_pos_bound X 8 ltac:(lia)). pose proof (rc_byte_signed k).
  rewrite rc_lts_signed by lia. apply Z.ltb_lt. destruct H as [H|H]; [contradiction | exact H].
Qed.

Lemma rbb_eqb0b : forall k : byte, bv_eqb (Z_to_bv 64 (bv_signed k)) (Z_to_bv 64 0) = (bv_signed k =? 0).
Proof. intros k. pose proof (rc_byte_signed k). apply rc_eqb0_signed. lia. Qed.

Lemma rbb_swrap32 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma rbb_land_m2 : forall x, 0 <= x < 2^63 -> Z.land x 18446744073709551614 = x - x mod 2.
Proof.
  intros x Hx.
  replace (x - x mod 2) with (Z.shiftl (Z.shiftr x 1) 1)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_eq by lia; change (2^1) with 2; lia).
  change 18446744073709551614 with (Z.shiftl (Z.ones 63) 1).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. replace (i - 1 + 1) with i by lia.
    destruct (Z.lt_ge_cases (i - 1) 63).
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.testbit_0_l|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 63; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma rbb_land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma rbb_sltiu1 : forall x, 0 < x < 2^64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia.
  replace (bv_wrap 64 1) with 1 by reflexivity.
  replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma rbb_snez1 : forall x, 0 < x < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 1.
Proof.
  intros x Hx. unfold v_sltu, c_ltu. rewrite (rbe_ltu 0 x) by lia.
  replace (0 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma rbb_snez0 : v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. unfold v_sltu, c_ltu. rewrite (rbe_ltu 0 0) by lia. reflexivity. Qed.

Ltac bzfix := repeat match goal with
  | |- context [Z.land ?x 18446744073709551614] => rewrite (rbb_land_m2 x) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  | |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by lia
  | |- context [Z.land ?x 7] => rewrite (rbb_land7 x) by lia
  | |- context [Z.land ?x 3] => rewrite (rbe_land3 x) by lia
  | |- context [Z.land ?x 1] => rewrite (rbe_land1 x) by lia
  | |- context [bv_swrap 32 ?z] => rewrite (rbb_swrap32 z) by lia
  | |- context [v_sltiu (Z_to_bv 64 ?x) 1] => rewrite (rbb_sltiu1 x) by lia
  | |- context [v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)] => rewrite rbb_snez0
  | |- context [v_sltu (Z_to_bv 64 0) (Z_to_bv 64 ?x)] => rewrite (rbb_snez1 x) by lia
  | |- context [Z.lxor ?x ?x] => rewrite (Z.lxor_nilpotent x)
  | |- context [Z.lxor 1 0] => change (Z.lxor 1 0) with 1
  end.
(* The register equations at a loop entry or a join, in a context cleared down to the bounds they need. *)
Ltac bweq := bzfix; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.pow_1_r;
  first [ reflexivity | f_equal; lia | f_equal; nia ].
Ltac bfp v w HM HL1 HL2 HC := rbe_fpc; rewrite ?(rbe_ld4 v) by lia; rewrite ?(rbe_u32 v) by lia;
  rewrite ?(rbe_u32 w) by lia; rewrite ?HM, ?HL1, ?HL2, ?HC; cbn [fst snd]; rewrite ?rbe_fc_same.
Ltac bcond := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  first [ replace c with false by (symmetry; rewrite ?rbe_lts by lia; unfold bv_eqb, bv_ltu; bzfix; solve_cond_rec); cbv iota
        | replace c with true by (symmetry; rewrite ?rbe_lts by lia; unfold bv_eqb, bv_ltu; bzfix; solve_cond_rec); cbv iota ]
  end.
Ltac bgo := repeat first [ bcond | rbe_st ].
Ltac bjeq := bzfix; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.pow_1_r; f_equal;
  unfold rb_lo, rb_mid, rb_hi, rb_G; lia.
Ltac bct := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true by (symmetry; rewrite ?rbe_lts by lia; unfold bv_eqb, bv_ltu; bzfix; solve_cond_rec); cbv iota end.
Ltac bcf := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false by (symmetry; rewrite ?rbe_lts by lia; unfold bv_eqb, bv_ltu; bzfix; solve_cond_rec); cbv iota end.

Section Run.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (a N P ns off : Z) (Q : Z -> Z) (V K : Z -> Z -> Z).
  Hypothesis HN : 2 <= N <= 127.
  Hypothesis HNe : N mod 2 = 0.
  Hypothesis Hns : 1 <= ns <= 12.
  Hypothesis FRM : frm0 fc.
  Hypothesis Ha : 0 < a.
  Hypothesis HaE : a + 3 * N * ns <= 2^64.
  Hypothesis HP0 : 0 < P.
  Hypothesis HP8m : P mod 8 = 0.
  Hypothesis HP8 : P + 8 * N <= 2^64.
  Hypothesis HQ : forall ch, 0 <= ch < N -> 0 < Q ch /\ Q ch mod 4 = 0 /\ Q ch + 4 * ns <= 2^64.
  Hypothesis HV : forall s ch, 0 <= s < ns -> 0 <= ch < N ->
    bytes_at rsegs m (Q ch + 4 * s) (le4 (Z_to_bv 64 (V s ch))) /\ rb_sample (V s ch) (K s ch).
  Hypothesis HD1 : a + 3 * N * ns <= P \/ P + 8 * N <= a.
  Hypothesis HD2 : forall ch, 0 <= ch < N -> a + 3 * N * ns <= Q ch \/ Q ch + 4 * ns <= a.
  Hypothesis HD3 : a + 3 * N * ns <= bv_unsigned sp + -128 \/ bv_unsigned sp <= a.
  Hypothesis HD4 : P + 8 * N <= bv_unsigned sp + -128 \/ bv_unsigned sp <= P.
  Hypothesis HD5 : forall ch, 0 <= ch < N -> Q ch + 4 * ns <= bv_unsigned sp + -128 \/ bv_unsigned sp <= Q ch.
  Hypothesis Hsp : 128 <= bv_unsigned sp.
  Hypothesis Hsp2 : bv_unsigned sp < 2^64.
  Hypothesis Hoff : 0 <= off < 2^63.
  Hypothesis HSRa : asan_shadow_rd rsegs m off a (3 * N * ns)
    [(bv_unsigned sp + -128, bv_unsigned sp); (a, a + 3 * N * ns)].
  Hypothesis HADa : asan_addressable rsegs m off a (3 * N * ns).
  Hypothesis HSRP : asan_shadow_rd rsegs m off P (8 * N)
    [(bv_unsigned sp + -128, bv_unsigned sp); (a, a + 3 * N * ns)].
  Hypothesis HADP : asan_addressable rsegs m off P (8 * N).
  Hypothesis HR3P : asan_rt3 rsegs m off P (8 * N).
  Hypothesis HSRQ : forall ch, 0 <= ch < N -> asan_shadow_rd rsegs m off (Q ch) (4 * ns)
    [(bv_unsigned sp + -128, bv_unsigned sp); (a, a + 3 * N * ns)].
  Hypothesis HADQ : forall ch, 0 <= ch < N -> asan_addressable rsegs m off (Q ch) (4 * ns).

  (* The shadow byte of P + 8 ch is 0 (an aligned 8-byte load). *)
  Lemma shP : forall mm ch, munch [(bv_unsigned sp + -128, bv_unsigned sp); (a, a + 3 * N * ns)] m mm ->
    0 <= ch < N -> ov_read_bytes rsegs mm (wa ((P + 8 * ch) / 8 + off)) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros mm ch HM Hch.
    pose proof (asan_shadow_rd_munch rsegs m mm off P (8 * N) _ _ HSRP HM (fun x Hx => Hx)) as HS.
    pose proof (asan_addressable_munch rsegs m mm off P (8 * N) _ _ HADP HSRP HM (fun x Hx => Hx)) as HA.
    pose proof (asan_rt3_munch rsegs m mm off P (8 * N) _ _ HR3P HSRP HM (fun x Hx => Hx)) as H3.
    destruct (asan_shadow_read rsegs mm off P (8 * N) _ (8 * ch) HS ltac:(lia)) as (k & RK & BK).
    assert (HM8 : (P + 8 * ch) mod 8 = 0).
    { replace (P + 8 * ch) with (P + ch * 8) by ring. rewrite Z_mod_plus_full. exact HP8m. }
    pose proof (asan_check_8 rsegs mm off P (8 * N) (8 * ch) k HA H3 ltac:(lia) ltac:(lia) HM8 BK) as K0.
    assert (E : k = Z_to_bv 8 0) by (apply bv_eq; rewrite (rc_signed0_unsigned0 k K0); reflexivity).
    subst k. exact RK.
  Qed.

  (* The shadow byte of Q ch + 4 s lets the 4-byte load pass. *)
  Lemma shQ : forall mm s ch, munch [(bv_unsigned sp + -128, bv_unsigned sp); (a, a + 3 * N * ns)] m mm ->
    0 <= s < ns -> 0 <= ch < N ->
    exists k : byte, ov_read_bytes rsegs mm (wa ((Q ch + 4 * s) / 8 + off)) 1 = Some [k] /\
      (bv_signed k = 0 \/ (Q ch + 4 * s) mod 8 + 3 < bv_signed k).
  Proof.
    intros mm s ch HM Hs Hch. destruct (HQ ch Hch) as (HQ0 & HQ4 & HQE).
    pose proof (asan_shadow_rd_munch rsegs m mm off (Q ch) (4 * ns) _ _ (HSRQ ch Hch) HM (fun x Hx => Hx)) as HS.
    pose proof (asan_addressable_munch rsegs m mm off (Q ch) (4 * ns) _ _ (HADQ ch Hch) (HSRQ ch Hch) HM
                  (fun x Hx => Hx)) as HA.
    destruct (asan_shadow_read rsegs mm off (Q ch) (4 * ns) _ (4 * s) HS ltac:(lia)) as (k & RK & BK).
    exists k. split; [exact RK|].
    assert (HW4 : (Q ch + 4 * s) mod 8 + 4 <= 8) by (clear - HQ4; Z.div_mod_to_equations; lia).
    exact (asan_check_lt rsegs mm off (Q ch) (4 * ns) (4 * s) 4 k HA ltac:(lia) ltac:(lia) ltac:(lia) HW4 BK).
  Qed.

  (* The shadow byte of an audio byte lets the 1-byte store pass. *)
  Lemma shA : forall mm X, munch [(bv_unsigned sp + -128, bv_unsigned sp); (a, a + 3 * N * ns)] m mm ->
    a <= X < a + 3 * N * ns ->
    exists k : byte, ov_read_bytes rsegs mm (wa (X / 8 + off)) 1 = Some [k] /\
      (bv_signed k = 0 \/ X mod 8 < bv_signed k).
  Proof.
    intros mm X HM HX.
    pose proof (asan_shadow_rd_munch rsegs m mm off a (3 * N * ns) _ _ HSRa HM (fun x Hx => Hx)) as HS.
    pose proof (asan_addressable_munch rsegs m mm off a (3 * N * ns) _ _ HADa HSRa HM (fun x Hx => Hx)) as HA.
    destruct (asan_shadow_read rsegs mm off a (3 * N * ns) _ (X - a) HS ltac:(lia)) as (k & RK & BK).
    replace (a + (X - a)) with X in RK, BK by lia.
    exists k. split; [exact RK|].
    pose proof (HA (X - a) k ltac:(lia)) as OK. replace (a + (X - a)) with X in OK by lia.
    exact (OK BK).
  Qed.

  Definition INVB (mm : word -> option byte) (L : list (Z * byte)) : Prop :=
    (forall ch, 0 <= ch < N -> bytes_at rsegs mm (P + 8 * ch) (le8 (Z_to_bv 64 (Q ch)))) /\
    (forall s ch, 0 <= s < ns -> 0 <= ch < N -> bytes_at rsegs mm (Q ch + 4 * s) (le4 (Z_to_bv 64 (V s ch)))) /\
    wr_at rsegs mm a (3 * N * ns) /\ mem_inv rsegs mm /\
    (forall x, outside [(bv_unsigned sp + -128, bv_unsigned sp)] (bv_unsigned x) -> mm x = rb_enc m L x) /\
    munch [(bv_unsigned sp + -128, bv_unsigned sp); (a, a + 3 * N * ns)] m mm /\ wmono rsegs m mm.

  Lemma INVB_store : forall mm L X b, INVB mm L -> a <= X < a + 3 * N * ns ->
    INVB (write_to_mem mm (wa X) [b]) (L ++ [(X, b)]).
  Proof.
    intros mm L X b (I1 & I2 & I3 & I4 & I5 & I6 & I7) HX.
    assert (HL : X + Z.of_nat (length [b]) <= 2^64) by (cbn [length Z.of_nat]; lia).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - intros ch Hch. apply bytes_at_write_other; [apply I1; exact Hch | lia | exact HL |].
      rewrite length_le8. cbn [length Z.of_nat]. destruct HD1; lia.
    - intros s ch Hs Hch. apply bytes_at_write_other; [apply I2; assumption | lia | exact HL |].
      rewrite length_le4. cbn [length Z.of_nat]. destruct (HD2 ch Hch); lia.
    - apply wr_at_write. exact I3.
    - apply mem_inv_store; [exact I4|]. cbn [length].
      replace (wa X) with (wa (a + (X - a))) by (f_equal; lia).
      apply (wr_at_store_ok rsegs mm a (3 * N * ns) (X - a) 1 I3); lia.
    - intros x Hx. rewrite rb_enc_app.
      change (rb_enc (rb_enc m L) [(X, b)]) with (write_to_mem (rb_enc m L) (wa X) [b]).
      apply (rbe_wr_agree [(bv_unsigned sp + -128, bv_unsigned sp)]); [lia | exact I5 | exact Hx].
    - apply munch_write; [exact I6 | lia | exact HL | cbn [inside length Z.of_nat]; lia].
    - apply wmono_write. exact I7.
  Qed.

  Lemma INVB_spill : forall mm L X v, INVB mm L -> bv_unsigned sp + -128 <= X -> X + 8 <= bv_unsigned sp + -104 ->
    stk rsegs mm (bv_unsigned sp + -128) (bv_unsigned sp + -104) ->
    INVB (write_to_mem mm (wa X) (le8 v)) L.
  Proof.
    intros mm L X v (I1 & I2 & I3 & I4 & I5 & I6 & I7) HX1 HX2 SP.
    assert (HL : X + Z.of_nat (length (le8 v)) <= 2^64) by (rewrite length_le8; cbn [Z.of_nat]; lia).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - intros ch Hch. apply bytes_at_write_other; [apply I1; exact Hch | lia | exact HL |].
      rewrite !length_le8. cbn [Z.of_nat]. destruct HD4; lia.
    - intros s ch Hs Hch. apply bytes_at_write_other; [apply I2; assumption | lia | exact HL |].
      rewrite length_le4, length_le8. cbn [Z.of_nat]. destruct (HD5 ch Hch); lia.
    - apply wr_at_write. exact I3.
    - apply mem_inv_store; [exact I4|]. rewrite length_le8.
      pose proof (rbe_stk_wr rsegs mm _ _ SP ltac:(lia)) as W.
      replace (wa X) with (wa (bv_unsigned sp + -128 + (X - (bv_unsigned sp + -128)))) by (f_equal; lia).
      apply (wr_at_store_ok rsegs mm _ _ (X - (bv_unsigned sp + -128)) 8 W); lia.
    - intros x Hx. rewrite (rbe_wr_out [(bv_unsigned sp + -128, bv_unsigned sp)]); [apply I5; exact Hx | lia | exact HL | | exact Hx].
      rewrite length_le8. cbn [inside Z.of_nat]. lia.
    - apply munch_write; [exact I6 | lia | exact HL | rewrite length_le8; cbn [inside Z.of_nat]; lia].
    - apply wmono_write. exact I7.
  Qed.

  Lemma FRs_store : forall mm cs X bs, rw_cells rsegs mm (bv_unsigned sp + -104) cs -> cells_size cs = 104%nat ->
    0 <= X -> X + Z.of_nat (length bs) <= 2^64 ->
    (X + Z.of_nat (length bs) <= bv_unsigned sp + -104 \/ bv_unsigned sp <= X) ->
    rw_cells rsegs (write_to_mem mm (wa X) bs) (bv_unsigned sp + -104) cs.
  Proof.
    intros mm cs X bs H Hs H0 H1 HX. apply rw_cells_frame; [exact H | lia | exact H1 |].
    rewrite Hs. lia.
  Qed.

  Lemma INVB_list : forall mm L L', INVB mm L -> L = L' -> INVB mm L'.
  Proof. intros mm L L' H ->. exact H. Qed.

  Lemma INVB_mu : forall mm L, INVB mm L -> munch [(bv_unsigned sp + -128, bv_unsigned sp); (a, a + 3 * N * ns)] m mm.
  Proof. intros mm L H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.

  Lemma INVB_wr : forall mm L, INVB mm L -> wr_at rsegs mm a (3 * N * ns).
  Proof. intros mm L H. exact (proj1 (proj2 (proj2 H))). Qed.

  Lemma SP_ok : forall mm k, stk rsegs mm (bv_unsigned sp + -128) (bv_unsigned sp + -104) -> 0 <= k -> k + 8 <= 24 ->
    store_ok rsegs mm (wa (bv_unsigned sp + -128 + k)) 8 = true.
  Proof.
    intros mm k H Hk1 Hk2. pose proof (rbe_stk_wr rsegs mm _ _ H ltac:(lia)) as W.
    replace (bv_unsigned sp + -104 - (bv_unsigned sp + -128)) with 24 in W by lia.
    apply (wr_at_store_ok rsegs mm _ 24 k 8 W); cbn [Z.of_nat]; lia.
  Qed.

  (* One byte store into the audio: INVB, the saved-register cells and the spill area. *)
  Lemma B_store : forall mm L X b, INVB mm L ->
    rw_cells rsegs mm (bv_unsigned sp + -104)
      [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mm (bv_unsigned sp + -128) (bv_unsigned sp + -104) -> a <= X < a + 3 * N * ns ->
    INVB (write_to_mem mm (wa X) [b]) (L ++ [(X, b)]) /\
    rw_cells rsegs (write_to_mem mm (wa X) [b]) (bv_unsigned sp + -104)
      [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk rsegs (write_to_mem mm (wa X) [b]) (bv_unsigned sp + -128) (bv_unsigned sp + -104).
  Proof.
    intros mm L X b HI FR SP HX. split; [apply INVB_store; assumption|]. split.
    - apply FRs_store; [exact FR | reflexivity | lia | cbn [length Z.of_nat]; lia |].
      cbn [length Z.of_nat]. destruct HD3; lia.
    - apply stk_write; [exact SP | lia | cbn [length Z.of_nat]; lia].
  Qed.

  (* A spilled word survives a store that misses it. *)
  Lemma RS_keep : forall mm Y v X bs, bytes_at rsegs mm Y (le8 v) -> 0 <= X -> X + Z.of_nat (length bs) <= 2^64 ->
    (Y + 8 <= X \/ X + Z.of_nat (length bs) <= Y) -> bytes_at rsegs (write_to_mem mm (wa X) bs) Y (le8 v).
  Proof.
    intros mm Y v X bs H H0 H1 HD. apply bytes_at_write_other; [exact H | exact H0 | exact H1 |].
    rewrite length_le8. cbn [Z.of_nat]. lia.
  Qed.

  Ltac rs_keep m0 X bs :=
    repeat match goal with
    | H : bytes_at rsegs m0 ?Y (le8 ?v) |- _ =>
        let H' := fresh "RS" in
        pose proof (RS_keep m0 Y v X bs H ltac:(lia) ltac:(cbn [length Z.of_nat]; rewrite ?length_le8; cbn [Z.of_nat]; lia)
                      ltac:(cbn [length Z.of_nat]; rewrite ?length_le8; cbn [Z.of_nat]; destruct HD3; lia)) as H';
        clear H
    end.

  (* A spill store at sp - 128 + k: INVB, the saved-register cells, the spill area and the spilled words. *)
  Ltac bspill k :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?A (le8 ?v)) _) =>
      let X := constr:(bv_unsigned sp + -128 + k) in
      replace A with (wa X) by (apply bv_eq; unfold wa; bzfix; lia);
      lazymatch goal with
      | HI : INVB m0 _, FRs : rw_cells _ m0 _ _, SP : stk _ m0 _ _ |- _ =>
          let HI' := fresh "HI" in let FR' := fresh "FRs" in let SP' := fresh "SP" in
          pose proof (INVB_spill m0 _ X v HI ltac:(lia) ltac:(lia) SP) as HI';
          pose proof (FRs_store m0 _ X (le8 v) FRs eq_refl ltac:(lia) ltac:(rewrite length_le8; cbn [Z.of_nat]; lia)
                        ltac:(rewrite length_le8; cbn [Z.of_nat]; lia)) as FR';
          pose proof (stk_write rsegs m0 _ _ X (le8 v) SP ltac:(lia) ltac:(rewrite length_le8; cbn [Z.of_nat]; lia)) as SP';
          rs_keep m0 X (le8 v);
          let RS' := fresh "RS" in
          pose proof (bytes_at_write_same rsegs m0 X (le8 v) ltac:(lia) ltac:(rewrite length_le8; cbn [Z.of_nat]; lia)) as RS';
          let mn := fresh "mm" in
          set (mn := write_to_mem m0 (wa X) (le8 v)) in *; clearbody mn; clear HI FRs SP
      end
  end.

  (* One byte store into the audio at a + k (the store, then INVB, the saved registers, the spill area and the
     spilled words). *)
  Ltac bbyte k :=
  match goal with
  | HI : INVB ?m0 ?L0, FRs : rw_cells _ ?m0 _ _, SP : stk _ ?m0 _ _ |- _ =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs m0 (wa (a + k)) 1 = true)
        by (apply (wr_at_store_ok rsegs m0 a (3 * N * ns) k 1 (INVB_wr _ _ HI)); cbn [Z.of_nat]; lia);
      step; clear HS;
      rewrite ?rbe_le1; rewrite ?rbe_b0, ?rbe_b1, ?rbe_b2;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m0 ?A [?bb]) _) =>
        replace A with (wa (a + k)) by (apply bv_eq; unfold wa; bzfix; lia);
        let HI' := fresh "HI" in let FR' := fresh "FRs" in let SP' := fresh "SP" in
        destruct (B_store m0 L0 (a + k) bb HI FRs SP ltac:(lia)) as (HI' & FR' & SP');
        rs_keep m0 (a + k) [bb];
        let mn := fresh "mm" in
        set (mn := write_to_mem m0 (wa (a + k)) [bb]) in *; clearbody mn; clear HI FRs SP
      end
  end.

  Definition LOOP (n : nat) : Prop :=
    forall (s ch : Z) (mm : word -> option byte) (G : bvmap 5 word)
      (x2 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    n = Z.to_nat ((ns - s) * N - ch) -> 0 <= s < ns -> 0 <= ch < N ->
    x2 = Z_to_bv 64 (bv_unsigned sp + -128) -> x5 = Z_to_bv 64 off ->
    x6 = Z_to_bv 64 (18446744073709551615 - a) -> x7 = Z_to_bv 64 0 ->
    x8 = Z_to_bv 64 1 -> x9 = Z_to_bv 64 18446744073709551607 ->
    x14 = Z_to_bv 64 ns -> x15 = Z_to_bv 64 (P + 8 * ch) -> x17 = Z_to_bv 64 s ->
    x18 = Z_to_bv 64 ch -> x19 = Z_to_bv 64 (8 * ch) -> x20 = Z_to_bv 64 ch -> x21 = Z_to_bv 64 (4 * s) ->
    x22 = Z_to_bv 64 0 -> x23 = Z_to_bv 64 (s * N) -> x24 = Z_to_bv 64 (P + 8 * ch) ->
    x28 = Z_to_bv 64 (18446744073709551615 - P) -> x29 = Z_to_bv 64 18446744073709551608 ->
    x30 = Z_to_bv 64 (bv_unsigned sp + -128) -> x31 = Z_to_bv 64 18446744073709551599 ->
    INVB mm (rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat ch)) ->
    rw_cells rsegs mm (bv_unsigned sp + -104)
      [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mm (bv_unsigned sp + -128) (bv_unsigned sp + -104) ->
    (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get G k = reg_get F k) ->
    evt rsegs (rbb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K)
      (MS (mkR ra x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 a) (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 N)
               x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (bvmap_set 12 (Z_to_bv 64 18446744072820359168) (bvmap_set 13 (Z_to_bv 64 18446744070672875518)
            (bvmap_set 14 (Z_to_bv 64 18446744070672875520) (bvmap_set 15 (Z_to_bv 64 18446744069414584320) G))))
          (Z_to_bv 64 0x81dc4) fc None mm (seg_rom rsegs)).

  (* +0x1a8 .. +0x2bc: from the join of the parity arms, with lo and mid spilled, the three checked byte stores,
     then the next turn, the next row or the epilogue. *)
  Lemma rbb_tail : forall (n : nat) (s ch w : Z) (mm : word -> option byte) (G : bvmap 5 word)
      (x16 x25 x26 x27 w0 w1 : word),
    LOOP n -> S n = Z.to_nat ((ns - s) * N - ch) -> 0 <= s < ns -> 0 <= ch < N ->
    0 <= w < 2^32 -> fp_to_int fmt_single RNE true 64 w = (K s ch mod 2^64, no_flags) ->
    x16 = Z_to_bv 64 (3 * rb_G N s ch) -> x25 = Z_to_bv 64 (1 + ch mod 2) ->
    w0 = Z_to_bv 64 (rb_lo N s ch) -> w1 = Z_to_bv 64 (rb_mid N s ch) ->
    INVB mm (rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat ch)) ->
    rw_cells rsegs mm (bv_unsigned sp + -104)
      [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mm (bv_unsigned sp + -128) (bv_unsigned sp + -104) ->
    bytes_at rsegs mm (bv_unsigned sp + -128 + 0) (le8 w0) ->
    bytes_at rsegs mm (bv_unsigned sp + -128 + 8) (le8 w1) ->
    (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get G k = reg_get F k) ->
    evt rsegs (rbb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 off)
               (Z_to_bv 64 (18446744073709551615 - a)) (Z_to_bv 64 0) (Z_to_bv 64 1)
               (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 a) (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 N)
               (Z_to_bv 64 ns) (Z_to_bv 64 (P + 8 * ch)) x16 (Z_to_bv 64 s) (Z_to_bv 64 ch) (Z_to_bv 64 (8 * ch))
               (Z_to_bv 64 ch) (Z_to_bv 64 (4 * s)) (Z_to_bv 64 0) (Z_to_bv 64 (s * N)) (Z_to_bv 64 (P + 8 * ch))
               x25 x26 x27 (Z_to_bv 64 (18446744073709551615 - P)) (Z_to_bv 64 18446744073709551608)
               (Z_to_bv 64 (bv_unsigned sp + -128)) (Z_to_bv 64 18446744073709551599))
          (bvmap_set 10 (nan_box (Z_to_bv 32 w)) (bvmap_set 11 (nan_box (Z_to_bv 32 w))
            (bvmap_set 12 (Z_to_bv 64 18446744072820359168) (bvmap_set 13 (Z_to_bv 64 18446744070672875518)
              (bvmap_set 14 (Z_to_bv 64 18446744070672875520) (bvmap_set 15 (Z_to_bv 64 18446744069414584320) G))))))
          (Z_to_bv 64 0x81ea4) fc None mm (seg_rom rsegs)).
  Proof.
    intros n s ch w mm G x16 x25 x26 x27 w0 w1 IH Hn Hs Hch Hw HC -> -> -> -> HI FRs SP RS0 RS1 HG.
    pose proof (rbe_pos_bound N s ch ns Hs Hch HNe) as [HB0 HB1].
    assert (HsN : 0 <= s * N <= 1524) by (clear - Hs Hns HN; nia).
    pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hc2.
    assert (HX1 : a <= a + rb_lo N s ch < a + 3 * N * ns) by (unfold rb_lo; lia).
    assert (HX2 : a <= a + rb_mid N s ch < a + 3 * N * ns) by (unfold rb_mid; lia).
    assert (HX3 : a <= a + rb_hi N s ch < a + 3 * N * ns) by (unfold rb_hi; lia).
    set (L := rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat ch)) in *.
    (* +0x1a8 .. +0x1b4: the reload of lo, a + lo and the spill of hi *)
    pose proof (rbe_rd8 _ _ _ _ RS0) as RD0.
    step. step. step. clear RD0.
    pose proof (SP_ok mm 16 SP ltac:(lia) ltac:(lia)) as HSc.
    step. bspill constr:(16). clear HSc.
    replace (3 * rb_G N s ch + (1 + ch mod 2)) with (rb_hi N s ch) in * by (unfold rb_hi; lia).
    (* +0x1b8 .. +0x1d8: a + lo neither wraps nor is 0, a <> 0, the shadow check of a + lo *)
    bgo.
    rewrite (unsigned_lit (a + rb_lo N s ch)) by lia. rewrite rc_shr3.
    match goal with H : INVB ?m1 _ |- _ =>
      destruct (shA m1 (a + rb_lo N s ch) (INVB_mu _ _ H) HX1) as (k1 & RK1 & OK1) end.
    pose proof (rc_byte_signed k1) as KR1.
    step. clear RK1.
    step.
    rbb_join 26 CONTL.
    { intros y1. map_cbv_set.
      (* +0x1dc .. +0x1fc: the reload of mid, the low byte, the check of a + mid *)
      match goal with H : bytes_at _ _ (bv_unsigned sp + -128 + 8) _ |- _ => pose proof (rbe_rd8 _ _ _ _ H) as RD1 end.
      step. clear RD1.
      step. rbe_fpc. rewrite (rbe_u32 w) by lia. rewrite HC. cbn [fst snd]. rewrite rbe_fc_same.
      bbyte (rb_lo N s ch).
      bgo.
      rewrite (unsigned_lit (a + rb_mid N s ch)) by lia. rewrite rc_shr3.
      match goal with H : INVB ?m1 _ |- _ =>
        destruct (shA m1 (a + rb_mid N s ch) (INVB_mu _ _ H) HX2) as (k2 & RK2 & OK2) end.
      pose proof (rc_byte_signed k2) as KR2.
      step. clear RK2.
      step.
      rbb_join 27 CONTM.
      { intros y2. map_cbv_set.
        (* +0x200 .. +0x220: the reload of hi, the middle byte, the check of a + hi *)
        match goal with H : bytes_at _ _ (bv_unsigned sp + -128 + 16) _ |- _ => pose proof (rbe_rd8 _ _ _ _ H) as RD2 end.
        step. clear RD2.
        step. rewrite (unsigned_lit (K s ch mod 2^64)) by (pose proof (Z.mod_pos_bound (K s ch) (2^64)); lia).
        bbyte (rb_mid N s ch).
        bgo.
        rewrite (unsigned_lit (a + rb_hi N s ch)) by lia. rewrite rc_shr3.
        match goal with H : INVB ?m1 _ |- _ =>
          destruct (shA m1 (a + rb_hi N s ch) (INVB_mu _ _ H) HX3) as (k3 & RK3 & OK3) end.
        pose proof (rc_byte_signed k3) as KR3.
        step. clear RK3.
        step.
        rbb_join 27 CONTH.
        { intros y3. map_cbv_set.
          (* +0x224 .. +0x240: the high byte and the counters *)
          step. rewrite (unsigned_lit (K s ch mod 2^64)) by (pose proof (Z.mod_pos_bound (K s ch) (2^64)); lia).
          do 4 rbe_st.
          bbyte (rb_hi N s ch).
          match goal with HI3 : INVB ?m3 _ |- _ =>
            assert (HI4 : INVB m3 (rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat (ch + 1))))
              by (apply (INVB_list m3 _ _ HI3); subst L; rewrite rb_row_succ by (clear - Hch; lia); unfold rb_turn;
                  rewrite <- !app_assoc; reflexivity);
            clear HI3
          end.
          rbe_st. step.
          destruct (Z.eq_dec (ch + 1) N) as [Hlast|Hmore].
          - bcf.
            (* +0x27c .. +0x280: the next row or the epilogue *)
            step. step. step.
            destruct (Z.eq_dec (s + 1) ns) as [Hend|Hnext].
            + bcf.
              do 14 rbe_st.
              match goal with FR3 : rw_cells _ ?m3 _ _, ST3 : stk _ ?m3 _ _ |- _ =>
                release_frame FR3 ST3 (bv_unsigned sp) end.
              step.
              destruct HI4 as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
              apply evt_done. unfold rbb_post. do 13 eexists. split; [reflexivity|].
              split; [intros k0 Hk; rewrite rbe_fget6 by (first [exact Hk | reflexivity]); apply HG; exact Hk|].
              split; [exact I6|]. split; [exact I7|]. split; [exact I4|]. split; [eassumption|].
              intros x Hx. rewrite (I5 x Hx). rewrite <- Hend, rb_rows_succ by (clear - Hs; lia).
              rewrite <- Hlast. reflexivity.
            + bct.
              step. bcf.
              do 12 rbe_st.
              rewrite rbe_frot by reflexivity.
              unfold LOOP in IH.
              match goal with HI5 : INVB ?m3 _ |- _ => eapply (IH (s + 1) 0 m3) end.
              all: lazymatch goal with
                   | |- INVB _ _ => apply (INVB_list _ _ _ HI4); rewrite rb_rows_succ by (clear - Hs; lia);
                                    rewrite <- Hlast; cbn [Z.to_nat rb_row]; rewrite app_nil_r; reflexivity
                   | |- rw_cells _ _ _ _ => eassumption
                   | |- stk _ _ _ _ => eassumption
                   | |- forall k, _ -> _ => intros k0 Hk; rewrite rbe_fget2 by (first [exact Hk | reflexivity]); apply HG; exact Hk
                   | |- _ = Z_to_bv 64 _ => clear - HN Hns Hs Hch HsN Hsp Hsp2 Hoff Ha HaE HP0 HP8 Hlast Hnext; bweq
                   | |- _ => clear - Hn Hs Hch HN Hns Hlast Hnext; nia
                   end.
          - bct.
            rewrite rbe_frot by reflexivity.
            unfold LOOP in IH.
            match goal with HI5 : INVB ?m3 _ |- _ => eapply (IH s (ch + 1) m3) end.
            all: lazymatch goal with
                 | |- INVB _ _ => exact HI4
                 | |- rw_cells _ _ _ _ => eassumption
                 | |- stk _ _ _ _ => eassumption
                 | |- forall k, _ -> _ => intros k0 Hk; rewrite rbe_fget2 by (first [exact Hk | reflexivity]); apply HG; exact Hk
                 | |- _ = Z_to_bv 64 _ => clear - HN Hns Hs Hch HsN Hsp Hsp2 Hoff Ha HaE HP0 HP8 Hmore; bweq
                 | |- _ => clear - Hn Hs Hch HN Hns Hmore; nia
                 end. }
        unfold sxb. rewrite (rbb_eqb0b k3).
        destruct (Z.eqb_spec (bv_signed k3) 0) as [K3|K3]; cbn [negb].
        - rbb_join_use CONTH.
        - step. rewrite (unsigned_lit (a + rb_hi N s ch)) by lia. rewrite rc_land7.
          step.
          rewrite (rbb_chk0 (a + rb_hi N s ch) k3 K3 OK3).
          cbn [negb]. step. rbb_join_use CONTH. }
      unfold sxb. rewrite (rbb_eqb0b k2).
      destruct (Z.eqb_spec (bv_signed k2) 0) as [K2|K2]; cbn [negb].
      - rbb_join_use CONTM.
      - step. rewrite (unsigned_lit (a + rb_mid N s ch)) by lia. rewrite rc_land7.
        step.
        rewrite (rbb_chk0 (a + rb_mid N s ch) k2 K2 OK2).
        cbn [negb]. step. rbb_join_use CONTM. }
    unfold sxb. rewrite (rbb_eqb0b k1).
    destruct (Z.eqb_spec (bv_signed k1) 0) as [K1|K1]; cbn [negb].
    - rbb_join_use CONTL.
    - step. rewrite (unsigned_lit (a + rb_lo N s ch)) by lia. rewrite rc_land7.
      step.
      rewrite (rbb_chk0 (a + rb_lo N s ch) k1 K1 OK1).
      cbn [negb]. step. rbb_join_use CONTL.
  Qed.

  (* +0xc8 .. +0x1a4: one turn up to the join of the parity arms, with lo and mid spilled. *)
  Lemma rbb_head : forall n, LOOP n -> LOOP (S n).
  Proof.
    intros n IH. red.
    intros s ch mm G x2 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      Hn Hs Hch E2 E5 E6 E7 E8 E9 E14 E15 E17 E18 E19 E20 E21 E22 E23 E24 E28 E29 E30 E31 HI FRs SP HG.
    subst x2 x5 x6 x7 x8 x9 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31.
    destruct (HQ ch Hch) as (HQ0 & HQ4 & HQE).
    destruct (HV s ch Hs Hch) as [_ HVs].
    destruct (rbe_pipe (V s ch) (K s ch) HVs) as (Hv & w & Hw & HM & HL1 & HL2 & HC).
    destruct HVs as [HK _].
    unfold F2P23, FCLAMP_HI, FCLAMP_LO in HM, HL1, HL2.
    pose proof (rbe_pos_bound N s ch ns Hs Hch HNe) as HB.
    assert (HsN : 0 <= s * N <= 1524) by (clear - Hs Hns HN; nia).
    pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hc2.
    assert (RP : ov_read_bytes rsegs mm (wa (P + 8 * ch)) 8 = Some (le8 (Z_to_bv 64 (Q ch))))
      by (apply rbe_rd8; apply (proj1 HI); exact Hch).
    assert (RV : ov_read_bytes rsegs mm (wa (Q ch + 4 * s)) 4 = Some (le4 (Z_to_bv 64 (V s ch))))
      by (apply rbe_rd4; apply (proj1 (proj2 HI)); assumption).
    pose proof (shP mm ch (INVB_mu _ _ HI) Hch) as RKP.
    (* +0xc8 .. +0xe8: P <> 0, ch < N, P + 8 ch neither wraps nor is misaligned, its shadow byte is 0 *)
    bgo.
    rewrite (unsigned_lit (P + 8 * ch)) by lia. rewrite rc_shr3.
    step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    (* +0xf0 .. +0x11c: Q ch <> 0, Q ch + 4 s neither wraps nor is misaligned, its shadow check *)
    bgo.
    rewrite (unsigned_lit (Q ch + 4 * s)) by lia. rewrite rc_shr3.
    destruct (shQ mm s ch (INVB_mu _ _ HI) Hs Hch) as (k & RKQ & OKQ).
    pose proof (rc_byte_signed k) as KR.
    step. clear RKQ.
    step.
    rbb_join 26 CONTQ.
    { intros y. map_cbv_set.
      (* +0x120 .. +0x16c: the sample, its scale and clamps, s N + ch does not overflow, 3 G *)
      bgo. bfp (V s ch) w HM HL1 HL2 HC.
      bgo. bfp (V s ch) w HM HL1 HL2 HC.
      bgo. bfp (V s ch) w HM HL1 HL2 HC.
      bgo.
      (* +0x16c .. +0x1a4: the parity arms spill lo and mid *)
      destruct (Z.eq_dec (ch mod 2) 0) as [Ev|Od].
      - bcf.
        rbe_st.
        pose proof (SP_ok mm 0 SP ltac:(lia) ltac:(lia)) as HSa.
        step. bspill constr:(0). clear HSa.
        step. bcf.
        match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          pose proof (SP_ok mc 8 ltac:(eassumption) ltac:(lia) ltac:(lia)) as HSb end.
        step. bspill constr:(8). clear HSb.
        step. bcf.
        step. step.
        match goal with R0 : bytes_at _ _ (bv_unsigned sp + -128 + 0) (le8 ?v0),
                        R1 : bytes_at _ _ (bv_unsigned sp + -128 + 8) (le8 ?v1) |- _ =>
          eapply (rbb_tail n s ch w _ _ _ _ _ _ v0 v1) end.
        all: lazymatch goal with
             | |- LOOP _ => exact IH
             | |- INVB _ _ => eassumption
             | |- rw_cells _ _ _ _ => eassumption
             | |- stk _ _ _ _ => eassumption
             | |- bytes_at _ _ _ _ => eassumption
             | |- forall k, _ -> _ => exact HG
             | |- fp_to_int _ _ _ _ _ = _ => exact HC
             | |- _ = Z_to_bv 64 _ => clear - HN Hns Hs Hch HsN Hc2 Ev; bjeq
             | |- _ => first [exact Hn | lia]
             end.
      - bct.
        rbe_st.
        pose proof (SP_ok mm 0 SP ltac:(lia) ltac:(lia)) as HSa.
        step. bspill constr:(0). clear HSa.
        step. bcf.
        rbe_st.
        match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          pose proof (SP_ok mc 8 ltac:(eassumption) ltac:(lia) ltac:(lia)) as HSb end.
        step. bspill constr:(8). clear HSb.
        step. bcf.
        step.
        match goal with R0 : bytes_at _ _ (bv_unsigned sp + -128 + 0) (le8 ?v0),
                        R1 : bytes_at _ _ (bv_unsigned sp + -128 + 8) (le8 ?v1) |- _ =>
          eapply (rbb_tail n s ch w _ _ _ _ _ _ v0 v1) end.
        all: lazymatch goal with
             | |- LOOP _ => exact IH
             | |- INVB _ _ => eassumption
             | |- rw_cells _ _ _ _ => eassumption
             | |- stk _ _ _ _ => eassumption
             | |- bytes_at _ _ _ _ => eassumption
             | |- forall k, _ -> _ => exact HG
             | |- fp_to_int _ _ _ _ _ = _ => exact HC
             | |- _ = Z_to_bv 64 _ => clear - HN Hns Hs Hch HsN Hc2 Od; bjeq
             | |- _ => first [exact Hn | lia]
             end. }
    unfold sxb. rewrite (rbb_eqb0b k).
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - rbb_join_use CONTQ.
    - step. rewrite (unsigned_lit (Q ch + 4 * s)) by lia. rewrite rc_land7.
      step. step.
      rewrite (rbb_chk3 (Q ch + 4 * s) k K0 OKQ).
      cbn [negb]. step. rbb_join_use CONTQ.
  Qed.

  Lemma rbb_loop : forall n, LOOP n.
  Proof.
    induction n as [|n IH].
    - red. intros s ch mm G x2 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
        x31 Hn Hs Hch.
      exfalso. clear - Hn Hs Hch HN. assert (s * N <= ns * N - N) by nia. lia.
    - apply rbb_head. exact IH.
  Qed.
End Run.

Theorem reac_braid_encode_exact_holds : reac_braid_encode_exact_contract.
Proof.
  unfold reac_braid_encode_exact_contract, REAC_BRAID_ENCODE, REAC_BRAID_ENCODE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    a N P ns Q V K -> -> -> -> -> HN HNe Hns FRM HI ST Ha HaE HW HP0 HP8m HP8 HPb HQ HV HD1 HD2 HD3 HD4 HD5
    HCE HSW HAa HAP HAQ HWO.
  change (evt rsegs ?Qx ?ms) with
    (evt rsegs (rbb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K) ms).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (Hsp : 128 <= bv_unsigned sp) by lia.
  replace (bv_unsigned sp - 128) with (bv_unsigned sp + -128) in ST, HD3, HD4, HD5, HWO by lia.
  (* the runtime facts on m: the cell of the shadow offset, and the shadow of a, P and each Q ch *)
  pose proof (rt_asan_rt m _ HCE HWO) as HRT.
  assert (HWs : forall x, in_shadow x -> outside [(bv_unsigned sp + -128, bv_unsigned sp); (a, a + 3 * N * ns)] x)
    by (intros x Hx; apply HWO; right; right; exact Hx).
  pose proof (rt_shadow_rd m a (3 * N * ns) _ HAa HWs) as HSRa.
  pose proof (rt_addressable m a (3 * N * ns) HAa) as HADa.
  pose proof (rt_shadow_rd m P (8 * N) _ HAP HWs) as HSRP.
  pose proof (rt_addressable m P (8 * N) HAP) as HADP.
  pose proof (rt_rt3 m P (8 * N) HAP) as HR3P.
  assert (HSRQ : forall ch, 0 <= ch < N -> asan_shadow_rd rsegs m ASAN_K (Q ch) (4 * ns)
                   [(bv_unsigned sp + -128, bv_unsigned sp); (a, a + 3 * N * ns)])
    by (intros ch Hch; apply rt_shadow_rd; [apply HAQ; exact Hch | exact HWs]).
  assert (HADQ : forall ch, 0 <= ch < N -> asan_addressable rsegs m ASAN_K (Q ch) (4 * ns))
    by (intros ch Hch; apply rt_addressable, HAQ, Hch).
  assert (Hoff : 0 <= ASAN_K < 2^63) by (unfold ASAN_K; lia).
  clear HCE HSW HAa HAP HAQ HWs.
  set (off := ASAN_K) in *. clearbody off.
  (* +0x0 .. +0x34: addi sp and the thirteen callee-saved stores *)
  pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 104%nat ST.
  do 14 step.
  (* +0x38: ns > 0 *)
  step. rewrite (rbe_lts 0 ns) by lia. if_false.
  (* +0x3c .. +0x48: the GOT cell of the shadow offset, and min (ns, 12) *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (HRT1 : asan_rt rsegs mc GOT_CELL_K CELL_K off
                     [(bv_unsigned sp + -128, bv_unsigned sp); (a, a + 3 * N * ns)])
      by (apply (asan_rt_munch rsegs m mc _ _ _ _ _ HRT MU); intros x [H1 _]; split; [exact H1 | exact I])
  end.
  pose proof (asan_rt_got_read rsegs _ _ _ _ _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs _ _ _ _ _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  step. step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
  assert (PRO : forall x14 : word, x14 = Z_to_bv 64 ns ->
    evt rsegs (rbb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 N)
               (Z_to_bv 64 P) (Z_to_bv 64 N) x14 (Z_to_bv 64 0xa1338) (Z_to_bv 64 12) a7 s2 s3 s4 s5 s6 s7 s8 s9
               s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d4c) fc None m3 (seg_rom rsegs)))
  end.
  { intros x14 ->.
    (* +0x50 .. +0x90: the shadow offset, the bounds the checks use and the float constants *)
    do 17 rbe_st.
    (* +0x94 .. +0xc4: N > 0, the first row *)
    step. rewrite (rbe_lts 0 N) by lia. if_false.
    do 12 rbe_st.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m4 _) =>
      assert (HI0 : INVB sp m a N P ns Q V m4 (rb_rows a N K (Z.to_nat 0) ++ rb_row a N K 0 (Z.to_nat 0)))
    end.
    { unfold INVB. cbn [rb_rows rb_row Z.to_nat app].
      split.
      { intros ch Hch. eapply bytes_at_transport; [apply HPb; exact Hch | exact MU |].
        cbn [disjoint_from]. split; [|exact I]. rewrite length_le8. destruct HD4; lia. }
      split.
      { intros s' ch Hs' Hch. eapply bytes_at_transport; [apply (proj1 (HV s' ch Hs' Hch)) | exact MU |].
        cbn [disjoint_from]. split; [|exact I]. rewrite length_le4. destruct (HD5 ch Hch); lia. }
      split; [exact HW|].
      split; [exact HI|].
      split; [intros x Hx; exact (MU x Hx)|].
      split; [eapply munch_weaken; [|exact MU]; intros x [H1 [H2 _]]; split; [exact H1|exact I]|].
      exact WM. }
    pose proof rbb_loop as LP. unfold LOOP in LP.
    eapply LP with (n := Z.to_nat ((ns - 0) * N - 0)) (s := 0) (ch := 0).
    all: first
      [ exact HI0
      | match goal with |- forall k, _ -> _ => intros k Hk; reflexivity end
      | eassumption
      | reflexivity
      | lia
      | apply bv_eq; rewrite !unsigned_lit_wrap; reflexivity
      | lazymatch goal with |- _ = Z_to_bv 64 _ =>
          clear - HN Hns Ha HaE HP0 HP8 HP8m Hsp Rsp; bweq end ]. }
  if_cases HC12.
  - apply (PRO (Z_to_bv 64 ns)). reflexivity.
  - rbe_rif. step. apply (PRO (Z_to_bv 64 12)).
    unfold bv_ltu in HC12. rewrite !unsigned_lit in HC12 by lia. apply Z.ltb_ge in HC12.
    f_equal. lia.
Qed.
