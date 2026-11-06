(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the walk of check_clamp (fuzz_uci.c), the plain image's
   0x12f88 (69 instructions, 48-byte frame), against lib/Prog/check_clamp_c.v. It carves the frame, copies *in onto
   it (two `sd` of paired words and one `sw`, shown to be hot_cells by pack_le8), calls rp_hot_clamp through
   lib/Prog/rp_hot_clamp.v's rp_hot_clamp_holds, and walks the five inlined hold() recomputations from *in, each a
   lemma in continuation style. The five `bne` to the `jal abort` at 0x13098 compare a register with itself, once
   lib/Spec/UciModel.v's clamp_prefill, clamp_adapt_min, clamp_adapt_max, clamp_margin (0 <= margin_max) and
   clamp_servo rewrite the clamped copy into the hold_m terms the recomputations reach, so the abort never runs. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require Import rp_hot_clamp_c rp_hot_clamp check_clamp_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the copy of *in onto the frame: two `sd` of paired words and one `sw` are the five int cells ---- *)

Lemma Z_to_le_bytes_add : forall n k z,
  Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros k z.
  - cbn [Nat.add Z_to_le_bytes app Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH. f_equal. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma lor_shift32 : forall a b, 0 <= a < 2^32 -> 0 <= b -> Z.lor (Z.shiftl b 32) a = b * 2^32 + a.
Proof.
  intros a b Ha Hb. rewrite Z.shiftl_mul_pow2 by lia.
  assert (L : Z.land (b * 2^32) a = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec i 32).
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite <- (Z.mod_small a (2^32)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

(* lwu / lwu / slli 32 / or, then sd: the eight bytes are the two words' low four bytes each *)
Lemma pack_le8 : forall u w : word,
  le8 (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zx32 w)) 32))) (bv_unsigned (zx32 u))))
  = le4 u ++ le4 w.
Proof.
  intros u w. unfold le8, word_to_le_bytes, le4, zx32.
  pose proof (Z.mod_pos_bound (bv_unsigned u) (2^32) ltac:(lia)) as Ha.
  pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)) as Hb.
  rewrite (unsigned_lit (bv_unsigned u mod 2^32)), (unsigned_lit (bv_unsigned w mod 2^32)) by lia.
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned w mod 2^32) 32)) by (rewrite Z.shiftl_mul_pow2; lia).
  rewrite lor_shift32 by lia. rewrite unsigned_lit by lia.
  change 8%nat with (4 + 4)%nat. rewrite Z_to_le_bytes_add. f_equal.
  - rewrite <- (Z_to_le_bytes_mod 4 (_ * 2^32 + _) 32) by (cbn; lia).
    rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned u) 32) by (cbn; lia).
    f_equal. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
  - change (8 * Z.of_nat 4) with 32. rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (bv_unsigned u mod 2^32)) by lia. rewrite Z.add_0_r.
    apply Z_to_le_bytes_mod. cbn; lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)].
  apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in Hn, Hw.
  split; (split; [split; assumption|]).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma rw_cells_app_merge : forall segs m A cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[W1 B1] (Ha1 & Hn1 & Hw1)] [[W2 B2] (Ha2 & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

(* the same bytes under another cell layout *)
Lemma rw_cells_bytes : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' E. split; [split; [exact Hwf' | rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma frame_split : forall segs m A c1 c2 c3 c4 c5 c6 c7,
  rw_cells segs m A [c1; c2; c3; c4; c5; c6; c7] ->
  rw_cells segs m A [c1; c2; c3] /\ rw_cells segs m (A + Z.of_nat (cells_size [c1; c2; c3])) [c4; c5; c6; c7].
Proof. intros. apply (rw_cells_app segs m A [c1; c2; c3] [c4; c5; c6; c7]). assumption. Qed.

Lemma frame_merge : forall segs m A c1 c2 c3 c4 c5 d1 d2 d3 d4,
  rw_cells segs m A [c1; c2; c3; c4; c5] ->
  rw_cells segs m (A + Z.of_nat (cells_size [c1; c2; c3; c4; c5])) [d1; d2; d3; d4] ->
  rw_cells segs m A [c1; c2; c3; c4; c5; d1; d2; d3; d4].
Proof. intros. exact (rw_cells_app_merge segs m A [c1; c2; c3; c4; c5] [d1; d2; d3; d4] H H0). Qed.

(* the same local override as rp_hot_clamp.v: both orientations of [wa e = x] *)
Local Ltac addr_eq_tac ::=
  first [ symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
        | first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* sgtz / neg / and at 0x13074-0x1307c: x < 0 ? 0 : x *)
Lemma neg_sgtz_and : forall g, -2^63 <= g < 2^63 ->
  Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 g)))))
         (bv_unsigned (Z_to_bv 64 g)) = (if g <? 0 then 0 else g).
Proof.
  intros g Hg. unfold v_slt, c_lts. rewrite lts_lit by lia.
  destruct (Z.ltb_spec 0 g); destruct (Z.ltb_spec g 0); try lia; cbv beta iota.
  - replace (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) with (Z.ones 64)
      by (vm_compute; reflexivity).
    rewrite unsigned_lit by lia. rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - replace (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 0)))) with 0 by (vm_compute; reflexivity).
    reflexivity.
  - replace (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 0)))) with 0 by (vm_compute; reflexivity).
    replace g with 0 by lia. reflexivity.
Qed.

(* addi -1 / and at 0x13050-0x13054 when x >= 0: the mask is all ones *)
Lemma land_ones64_l : forall v, 0 <= v < 2^64 -> Z.land 18446744073709551615 (bv_unsigned (Z_to_bv 64 v)) = v.
Proof.
  intros v Hv. rewrite unsigned_lit by lia. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* hold_m by cases, innermost comparison first *)
Local Ltac hcase :=
  unfold hold_m;
  repeat (match goal with
          | |- context [Z.ltb ?a ?b] =>
              lazymatch a with context [Z.ltb _ _] => fail | _ =>
              lazymatch b with context [Z.ltb _ _] => fail | _ => destruct (Z.ltb_spec a b) end end
          end; cbv beta iota);
  lia.

(* a join point whose register is stated as [Z_to_bv 64 (hold_m ...)] *)
Local Ltac hjoin K := eapply K; f_equal; hcase.

(* the pc after a conditional branch, with the condition stated over Z and split on [a <? b] (as rp_hot_clamp.v) *)
Local Ltac br a b P :=
  rewrite ?lts_lit, ?ltu_lit by lia; destruct (Z.ltb_spec a b) as [P|P]; cbv beta iota delta [negb].

(* ---- after the call: the five recomputations of hold() from *in, each against the clamped copy ---- *)
Section Post.
Variables (ra sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mm f0 f1 f2 f3 f4 : Z) (j : list byte)
  (v1 v0 vra : word) (Q : machine_state -> Prop).
Hypothesis Rf0 : -2^31 <= f0 <= 2^31 - 1.
Hypothesis Rf1 : -2^31 <= f1 <= 2^31 - 1.
Hypothesis Rf2 : -2^31 <= f2 <= 2^31 - 1.
Hypothesis Rf3 : -2^31 <= f3 <= 2^31 - 1.
Hypothesis Rf4 : -2^31 <= f4 <= 2^31 - 1.
Hypothesis RM : 0 <= mm <= 2^31 - 1.
Hypothesis CI : ro_cells rsegs m (bv_unsigned s0)
  [C4 (Z_to_bv 64 f0); C4 (Z_to_bv 64 f1); C4 (Z_to_bv 64 f2); C4 (Z_to_bv 64 f3); C4 (Z_to_bv 64 f4)].
Hypothesis CF : rw_cells rsegs m (bv_unsigned sp)
  [C4 (Z_to_bv 64 (hold_m f0 1 1000)); C4 (Z_to_bv 64 (hold_m f1 1 1000));
   C4 (Z_to_bv 64 (hold_m f2 (hold_m f1 1 1000) 1000)); C4 (Z_to_bv 64 (hold_m f3 0 mm));
   C4 (Z_to_bv 64 (hold_m f4 0 50000)); CB 4 j; C8 v1; C8 v0; C8 vra].

Local Abbreviation ST pc a0 a1 a2 a3 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 mm) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* 0x12fdc-0x12ff0: a0 = hold (in->adapt_min_ms, 1, 1000) *)
Lemma post_min : forall a0 a1 a2 a3 : word,
  (forall a0' : word, a0' = Z_to_bv 64 (hold_m f1 1 1000) ->
     evt rsegs Q (ST 0x12ff4 a0' (Z_to_bv 64 1000) a2 a3)) ->
  evt rsegs Q (ST 0x12fdc a0 a1 a2 a3).
Proof.
  intros a0 a1 a2 a3 K.
  step. rewrite (sx32_int f1) by lia.
  do 2 step. br f1 1000 P.
  - step. br 0 f1 P2.
    + hjoin K.
    + step. hjoin K.
  - do 2 step. br 0 1000 P2; [| exfalso; lia]. hjoin K.
Qed.

(* 0x12ff4-0x13008: a2 = hold (in->prefill_ms, 1, 1000), a1 = the clamped prefill_ms *)
Lemma post_prefill : forall a0 a2 a3 : word,
  (forall a2' : word, a2' = Z_to_bv 64 (hold_m f0 1 1000) ->
     evt rsegs Q (ST 0x1300c a0 (Z_to_bv 64 (hold_m f0 1 1000)) a2' a3)) ->
  evt rsegs Q (ST 0x12ff4 a0 (Z_to_bv 64 1000) a2 a3).
Proof.
  intros a0 a2 a3 K.
  assert (RC : 1 <= hold_m f0 1 1000 <= 1000) by hcase.
  step. rewrite (sx32_int f0) by lia.
  step. br f0 1000 P.
  - step. rewrite (sx32_int (hold_m f0 1 1000)) by lia.
    step. br 0 f0 P2.
    + hjoin K.
    + step. hjoin K.
  - step. step. rewrite (sx32_int (hold_m f0 1 1000)) by lia.
    step. br 0 1000 P2; [| exfalso; lia]. hjoin K.
Qed.

(* 0x13018-0x13034: a0 = hold (in->adapt_max_ms, lo, 1000), a3 = the clamped adapt_max_ms *)
Lemma post_max : forall a1 a2 a3 : word,
  (forall a0' a2' : word, a0' = Z_to_bv 64 (hold_m f2 (hold_m f1 1 1000) 1000) ->
     evt rsegs Q (ST 0x13038 a0' (Z_to_bv 64 f2) a2' (Z_to_bv 64 (hold_m f2 (hold_m f1 1 1000) 1000)))) ->
  evt rsegs Q (ST 0x13018 (Z_to_bv 64 (hold_m f1 1 1000)) a1 a2 a3).
Proof.
  intros a1 a2 a3 K.
  assert (RL : 1 <= hold_m f1 1 1000 <= 1000) by hcase.
  assert (RC : 1 <= hold_m f2 (hold_m f1 1 1000) 1000 <= 1000) by (unfold hold_m at 1; hcase).
  step. rewrite (sx32_int f2) by lia.
  do 3 step. br f2 1000 P.
  - step. rewrite (sx32_int (hold_m f2 (hold_m f1 1 1000) 1000)) by lia.
    step. br f2 (hold_m f1 1 1000) P2.
    + eapply K. f_equal. revert RL P P2. generalize (hold_m f1 1 1000). intros lo RL P P2. hcase.
    + step. eapply K. f_equal. revert RL P P2. generalize (hold_m f1 1 1000). intros lo RL P P2. hcase.
  - step. step. rewrite (sx32_int (hold_m f2 (hold_m f1 1 1000) 1000)) by lia.
    step. br f2 (hold_m f1 1 1000) P2; [exfalso; lia |].
    step. eapply K. f_equal. revert RL P P2. generalize (hold_m f1 1 1000). intros lo RL P P2. hcase.
Qed.

(* 0x1303c-0x13054: a1 = hold (in->adapt_margin, 0, margin_max), a0 = the clamped adapt_margin *)
Lemma post_margin : forall a0 a1 a2 a3 : word,
  (forall a1' a2' : word, a1' = Z_to_bv 64 (hold_m f3 0 mm) ->
     evt rsegs Q (ST 0x13058 (Z_to_bv 64 (hold_m f3 0 mm)) a1' a2' a3)) ->
  evt rsegs Q (ST 0x1303c a0 a1 a2 a3).
Proof.
  intros a0 a1 a2 a3 K.
  assert (RC : 0 <= hold_m f3 0 mm <= mm) by hcase.
  step. rewrite (sx32_int f3) by lia.
  step. rewrite (sx32_int (hold_m f3 0 mm)) by lia.
  step. unfold v_slti, zsig. rewrite (signed_lit_small f3) by lia.
  destruct (Z.ltb_spec f3 0) as [N|N]; cbv beta iota.
  - step. br f3 mm P; [| exfalso; lia].
    do 2 step. eapply K. f_equal. rewrite Z.land_0_l. hcase.
  - step. br f3 mm P.
    + do 2 step. eapply K. f_equal. rewrite land_ones64_l by lia. hcase.
    + do 3 step. eapply K. f_equal. rewrite land_ones64_l by lia. hcase.
Qed.

(* 0x1305c-0x1307c: a1 = hold (in->servo_clamp_ppm, 0, 50000), a0 = the clamped servo_clamp_ppm *)
Lemma post_servo : forall a0 a1 a2 a3 : word,
  (forall a1' a2' : word, a1' = Z_to_bv 64 (hold_m f4 0 50000) ->
     evt rsegs Q (ST 0x13080 (Z_to_bv 64 (hold_m f4 0 50000)) a1' a2' a3)) ->
  evt rsegs Q (ST 0x1305c a0 a1 a2 a3).
Proof.
  intros a0 a1 a2 a3 K.
  assert (RC : 0 <= hold_m f4 0 50000 <= 50000) by hcase.
  step. rewrite (sx32_int f4) by lia.
  step. rewrite (sx32_int (hold_m f4 0 50000)) by lia.
  do 3 step. br f4 50000 P.
  - do 3 step. rewrite (neg_sgtz_and f4) by lia. hjoin K.
  - (* a1 = 50000: the register is a closed term *)
    do 4 step. eapply K. f_equal.
    match goal with |- ?l = _ => let v := eval vm_compute in l in change l with v end. hcase.
Qed.

End Post.

(* the bne after each recomputation compares a register with itself *)
Local Ltac ne_false :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; cbv beta delta [c_eq bv_eqb]; rewrite Z.eqb_refl; reflexivity]
  end.

(* the premises of a Post lemma: *in's cells and the clamped frame fix the field values, then the ranges *)
Local Ltac post_prem IN CF :=
  first [ exact IN | rewrite unsigned_lit by lia; exact CF | lia | idtac ].

Theorem check_clamp_holds : check_clamp_contract.
Proof.
  unfold check_clamp_contract, CHECK_CLAMP, CHECK_CLAMP_FRAME, RP_HOT_SIZE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p mm lo
    HI HM HA1 IN MI ST HLO HSP DJ.
  assert (E1 : a1 = Z_to_bv 64 mm) by (rewrite <- HA1; symmetry; apply Z_to_bv_lit_self). subst a1.
  pose proof HI as HI0.
  unfold hot_int, INT_MIN, INT_MAX in HI. unfold INT_MAX in HM. destruct HI as (R0 & R1 & R2 & R3 & R4).
  pose proof ST as (Hlo0 & _ & _).
  unfold hot_cells, c4z in IN.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 20 step.
  (* the frame: [*in's five ints as two words and an int; 4 bytes of junk; s1; s0; ra] *)
  rewrite (sx32_int (servo_clamp_ppm p)) in FR by lia.
  destruct (frame_split _ _ _ _ _ _ _ _ _ _ FR) as [HOT0 REST]. clear FR.
  cbn [cells_size csize Nat.add] in REST.
  replace (bv_unsigned sp + -48 + Z.of_nat 20) with (bv_unsigned sp + -28) in REST by lia.
  lazymatch type of HOT0 with rw_cells _ ?mc _ _ =>
    assert (HOT : rw_cells rsegs mc (bv_unsigned sp + -48) (hot_cells p))
  end.
  { eapply rw_cells_bytes; [exact HOT0 | unfold hot_cells; cbn; tauto |].
    unfold hot_cells, c4z. cbn [cells_bytes cbytes]. rewrite !pack_le8, <- !app_assoc. reflexivity. }
  clear HOT0.
  (* jal rp_hot_clamp, with a0 = the frame and a1 = margin_max *)
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    eapply evt_cut;
    [eapply (rp_hot_clamp_holds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p mm) |];
    [ exact HI0 | unfold INT_MAX; lia | exact HA1 | rewrite unsigned_lit by lia; exact HOT | assumption | ];
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
                MUc & WMc & MIc & CHc);
    rewrite unsigned_lit in MUc, CHc by lia; unfold RP_HOT_SIZE in MUc;
    clear HOT; transport_after_call rsegs m1 m2 MUc WMc; clear MUc WMc;
    repeat match goal with H : mem_inv rsegs m1 |- _ => clear H end
  end.
  replace (bv_unsigned sp + -28) with (bv_unsigned sp + -48 + Z.of_nat 20) in REST by lia.
  unfold hot_cells, c4z in CHc.
  pose proof (frame_merge _ _ _ _ _ _ _ _ _ _ _ _ CHc REST) as CF. clear CHc REST.
  rewrite clamp_prefill, clamp_adapt_min, clamp_adapt_max, (clamp_margin p mm ltac:(lia)), clamp_servo in CF.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  (* the five recomputations; each bne compares a register with itself (UciModel's clamp_* theorems, rewritten
     into CF above), so none of the five branches to the `jal abort` at 0x13098 *)
  (eapply post_min; post_prem IN CF); try lia.
  intros a0'' E; subst a0''.
  (eapply post_prefill; post_prem IN CF); try lia.
  intros a2'' E; subst a2''.
  step. ne_false.                                   (* 0x1300c bne: prefill_ms *)
  step. rewrite (sx32_int (hold_m (adapt_min_ms p) 1 1000)) by hcase.
  step. ne_false.                                   (* 0x13014 bne: adapt_min_ms *)
  (eapply post_max; post_prem IN CF); try lia.
  intros a0'' a2'' E; subst a0''.
  step. ne_false.                                   (* 0x13038 bne: adapt_max_ms *)
  (eapply post_margin; post_prem IN CF); try lia.
  intros a1'' a2''' E; subst a1''.
  step. ne_false.                                   (* 0x13058 bne: adapt_margin *)
  (eapply post_servo; post_prem IN CF); try lia.
  intros a1'' a2'''' E; subst a1''.
  step. ne_false.                                   (* 0x13080 bne: servo_clamp_ppm *)
  (* epilogue: reload ra, s0, s1 from the frame, pop it, ret *)
  do 5 step.
  apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split.
  - release_frame CF ST (bv_unsigned sp). exact ST.
  - unfold hot_cells, c4z. exact IN.
Qed.
