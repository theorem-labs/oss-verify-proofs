(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the case SPEC_FN_RING (0x00) of the system exclusive part of the inlined
   spec_event_of (spec.h:438-452) in LLVMFuzzerTestOneInput on the UBSan image, 0x130c4-0x13160 (the entry 0 of the
   jump table at 0x103a4; a0 = pl, a1 = s, a3 = pn):
     0x130c4-0x130c8  pn != 3 -> 0x131cc (the event stays OTHER with the device);
     0x130cc-0x130dc  e.kind = SPEC_EV_RING (7), e.strip = pl[0] & 0x3f;
     0x130e0-0x130fc  e.mask = pl[0] >> 6 & 1 (`slli 57` / `srli 63`), a1 = pl + 1, a2 = pl + 2, led = 2 (a3),
                      a5 = -led;
     0x13100-0x1315c  the loop over the LEDs 2 .. 15 (spec.h:446-451): for led <= 8 the byte pl[1] (UBSan 0x13108:
                      pl + 1 does not wrap) and the bit 8 - led, else pl[2] (UBSan 0x1311c: pl + 2 does not wrap)
                      and the bit 15 - led (`addw a5, 8` or `addw a5, 15`); UBSan 0x1312c: the shift exponent is below
                      32; if the bit is set, e.mask |= 1 << (led - 1) (`sllw s9`, sh); then a5 - 1, led + 1, until
                      a5 = -16;
     0x13160          to 0x131cc.
   ring_inv k is the loop invariant, the state at 0x13100 after k LEDs with the mask ring_mask_k k (DgnSpec.v
   ring_mask folds ring_step over the 14 LEDs, ring_mask_k over the first k); ring_inv_step is one turn and
   ring_loop the induction over the LEDs left. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells
  Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout
  LLVMFuzzerTestOneInput_owed_lib LLVMFuzzerTestOneInput_owed_sysex_lib.
Import ListNotations.
Open Scope Z_scope.

(* ---- the model ---- *)

(* the mask after the first k LEDs of spec.h:446-451 *)
Definition ring_mask_k (p0 p1 p2 : Z) (k : nat) : Z :=
  fold_left (ring_step p1 p2) (map (fun j => j + 2) (zseq k)) (Z.land (Z.shiftr p0 6) 1).

Lemma ring_mask_k_S : forall p0 p1 p2 k,
  ring_mask_k p0 p1 p2 (S k) = ring_step p1 p2 (ring_mask_k p0 p1 p2 k) (Z.of_nat k + 2).
Proof.
  intros p0 p1 p2 k. unfold ring_mask_k, zseq. rewrite seq_S, !map_app, fold_left_app. reflexivity.
Qed.

Lemma ring_step_range : forall p1 p2 mk led, 0 <= mk < 2 ^ 16 -> 0 <= ring_step p1 p2 mk led < 2 ^ 16.
Proof.
  intros p1 p2 mk led H. unfold ring_step. cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c end;
    [unfold u16; apply Z.mod_pos_bound; lia | exact H].
Qed.

Lemma ring_mask_k_range : forall p0 p1 p2 k, 0 <= p0 -> 0 <= ring_mask_k p0 p1 p2 k < 2 ^ 16.
Proof.
  intros p0 p1 p2 k H0. induction k as [|k IH].
  - change (ring_mask_k p0 p1 p2 0) with (Z.land (Z.shiftr p0 6) 1).
    pose proof (land_lt_pow2 1 (Z.shiftr p0 6) 1 ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as R.
    rewrite Z.land_comm in R. change (2 ^ 1) with 2 in R. lia.
  - rewrite ring_mask_k_S. apply ring_step_range. exact IH.
Qed.

(* one LED of pl[1] (led <= 8) and of pl[2] (led >= 9), as the walk tests it *)
Lemma ring_step_lo : forall p1 p2 mk led, 2 <= led <= 8 -> 0 <= mk < 2 ^ 16 -> 0 <= p1 ->
  ring_step p1 p2 mk led =
    (if Z.land (Z.shiftr p1 (8 - led)) 1 =? 0 then mk else Z.lor mk (2 ^ (led - 1))).
Proof.
  intros p1 p2 mk led Hl Hm Hp. unfold ring_step. cbv zeta.
  replace (led <=? 8) with true by (symmetry; apply Z.leb_le; lia). cbv iota.
  pose proof (land_lt_pow2 1 (Z.shiftr p1 (8 - led)) 1 ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as R.
  rewrite Z.land_comm in R. change (2 ^ 1) with 2 in R.
  assert (D : Z.land (Z.shiftr p1 (8 - led)) 1 = 0 \/ Z.land (Z.shiftr p1 (8 - led)) 1 = 1) by lia.
  destruct D as [D|D]; rewrite D; [reflexivity|].
  change (1 =? 1) with true. change (1 =? 0) with false. cbv iota.
  rewrite Z.shiftl_1_l.
  assert (P : 0 < 2 ^ (led - 1) <= 2 ^ 7) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  unfold u16. rewrite (Z.mod_small (2 ^ (led - 1))) by lia.
  pose proof (lor_lt_pow2 mk (2 ^ (led - 1)) 16 ltac:(lia) ltac:(lia)) as L.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma ring_step_hi : forall p1 p2 mk led, 9 <= led <= 15 -> 0 <= mk < 2 ^ 16 -> 0 <= p2 ->
  ring_step p1 p2 mk led =
    (if Z.land (Z.shiftr p2 (15 - led)) 1 =? 0 then mk else Z.lor mk (2 ^ (led - 1))).
Proof.
  intros p1 p2 mk led Hl Hm Hp. unfold ring_step. cbv zeta.
  replace (led <=? 8) with false by (symmetry; apply Z.leb_gt; lia). cbv iota.
  pose proof (land_lt_pow2 1 (Z.shiftr p2 (15 - led)) 1 ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as R.
  rewrite Z.land_comm in R. change (2 ^ 1) with 2 in R.
  assert (D : Z.land (Z.shiftr p2 (15 - led)) 1 = 0 \/ Z.land (Z.shiftr p2 (15 - led)) 1 = 1) by lia.
  destruct D as [D|D]; rewrite D; [reflexivity|].
  change (1 =? 1) with true. change (1 =? 0) with false. cbv iota.
  rewrite Z.shiftl_1_l.
  assert (P : 0 < 2 ^ (led - 1) <= 2 ^ 14) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  unfold u16. rewrite (Z.mod_small (2 ^ (led - 1))) by lia.
  pose proof (lor_lt_pow2 mk (2 ^ (led - 1)) 16 ltac:(lia) ltac:(lia)) as L.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* the ring event of spec.h:443-449 with the mask mk *)
Definition ring_ev (b : list Z) (M : spec_msg) (mk : Z) : spec_event :=
  {| se_kind := 7; se_strip := Z.land (byte_at b (sm_sysex_at M + 3)) 63; se_button := 0; se_zone := 0;
     se_on := 0; se_right := 0; se_addr := 0; se_device := byte_at b (sm_sysex_at M + 1); se_len := 0;
     se_dots := 0; se_value := 0; se_mask := mk; se_delta := 0; se_segments := 0; se_text := repeat 0 8;
     se_seg := repeat 0 8 |}.

(* ---- the values of the loop ---- *)

(* 0x13134: srlw of a byte by a bit index below 32 *)
Lemma srlw_byte : forall x j, 0 <= x < 256 -> 0 <= j < 32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 x) (j mod 32)) = Z.shiftr x j.
Proof.
  intros x j Hx Hj. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
  rewrite (Z.mod_small x) by lia. rewrite (Z.mod_small j) by lia.
  pose proof (shiftr_b x j Hx ltac:(lia)) as R. apply swrap32_small. lia.
Qed.

(* 0x13144: sllw of 1 by led - 1 <= 14 *)
Lemma sllw1 : forall j, 0 <= j <= 14 -> bv_swrap 32 (Z.shiftl 1 (j mod 32)) = 2 ^ j.
Proof.
  intros j Hj. rewrite (Z.mod_small j) by lia. rewrite Z.shiftl_1_l.
  assert (P : 0 < 2 ^ j <= 2 ^ 14) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  apply swrap32_small. lia.
Qed.

(* 0x1315c: a5 = -led against -16 *)
Lemma bne_m16 : forall x, 0 < x < 2 ^ 62 -> bv_eqb (Z_to_bv 64 (- x)) (Z_to_bv 64 (-16)) = (x =? 16).
Proof.
  intros x Hx. unfold bv_eqb. rewrite (unsigned_neg x) by lia.
  change (bv_unsigned (Z_to_bv 64 (-16))) with (2 ^ 64 - 16).
  destruct (Z.eqb_spec (2 ^ 64 - x) (2 ^ 64 - 16)); destruct (Z.eqb_spec x 16); first [reflexivity | lia].
Qed.

(* ---- the loop ---- *)

Section Loop.
Variables (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (Sp lo body : Z)
  (bb : list byte) (M : spec_msg) (Q : machine_state -> Prop)
  (y1 y5 y6 y7 y21 y22 y28 y29 y30 y31 : word) (q1 q2 j56 : list byte).

Local Abbreviation P0 := (byte_at (map bz bb) (sm_sysex_at M + 3)).
Local Abbreviation P1 := (byte_at (map bz bb) (sm_sysex_at M + 4)).
Local Abbreviation P2 := (byte_at (map bz bb) (sm_sysex_at M + 5)).

(* the state at a pc of the loop: led = a3, mask = a4, a5 = -led *)
Local Abbreviation ST pc a3 a4 a5 a6 a7 m :=
  (MS (mkR y1 (Z_to_bv 64 Sp) gp tp y5 y6 y7 (Z_to_bv 64 0x1f) (Z_to_bv 64 (Z.of_nat (length bb)))
         (Z_to_bv 64 (body + sm_sysex_at M + 3)) (Z_to_bv 64 (body + sm_sysex_at M + 4))
         (Z_to_bv 64 (body + sm_sysex_at M + 5)) a3 a4 a5 a6 a7
         (Z_to_bv 64 body) (Z_to_bv 64 (Sp + 0x50)) (Z_to_bv 64 (2 ^ 64 - 1)) y21 y22 x23 (Z_to_bv 64 0xb0)
         (Z_to_bv 64 1) (Z_to_bv 64 13) (Z_to_bv 64 0x90) y28 y29 y30 y31)
       F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* the loop invariant after k LEDs (k <= 13): the state at 0x13100 with led = k + 2, a5 = -led and the mask of the
   first k LEDs in a4 and in e.mask *)
Definition ring_inv (k : nat) : Prop :=
  forall (mk : Z) (a3 a4 a5 a6 a7 : word) (m : word -> option byte),
    mk = ring_mask_k P0 P1 P2 k ->
    a3 = Z_to_bv 64 (Z.of_nat k + 2) -> a4 = Z_to_bv 64 mk -> a5 = Z_to_bv 64 (- (Z.of_nat k + 2)) ->
    sx_env Sp lo body bb M -> sm_sysex_len M - 3 = 3 ->
    sx_mem m0 m Sp lo body bb M (ring_ev (map bz bb) M mk) q1 q2 j56 ->
    owed_k Q gp tp x23 F fc m0 Sp lo body (Z.of_nat (length bb))
      (Owed M (ring_ev (map bz bb) M (ring_mask_k P0 P1 P2 14)) 0 (sm_next M) (sm_status_out M)) ->
    evt rsegs Q (ST 0x13100 a3 a4 a5 a6 a7 m).

(* one turn of the loop: the LED k + 2, then 0x131cc after the last LED (k = 13), else the invariant at k + 1 *)
Lemma ring_inv_step : forall k, (k <= 13)%nat -> ((k < 13)%nat -> ring_inv (S k)) -> ring_inv k.
Proof.
  intros k Hk13 Hnext mk a3 a4 a5 a6 a7 m Hmk -> -> -> SXE Hpn SXM K.
  pose proof SXE as SXE0. sx_env_facts SXE0.
  pose proof (bat_range bb (sm_sysex_at M + 4)) as R1.
  pose proof (bat_range bb (sm_sysex_at M + 5)) as R2.
  pose proof (ring_mask_k_range P0 P1 P2 k ltac:(pose proof (bat_range bb (sm_sysex_at M + 3)); lia)) as HMr.
  rewrite <- Hmk in HMr.
  (* 0x13150-0x1315c: a5 - 1, led + 1, and the loop test *)
  assert (TAIL : forall (m' : word -> option byte) (mk' : Z) (a4' a6' a7' : word),
     mk' = ring_mask_k P0 P1 P2 (S k) -> a4' = Z_to_bv 64 mk' ->
     sx_mem m0 m' Sp lo body bb M (ring_ev (map bz bb) M mk') q1 q2 j56 ->
     evt rsegs Q (ST 0x13150 (Z_to_bv 64 (Z.of_nat k + 2)) a4' (Z_to_bv 64 (- (Z.of_nat k + 2))) a6' a7' m')).
  { intros m' mk' a4' a6' a7' Hmk' -> SXM'.
    step. rewrite (swrap32_neg (Z.of_nat k + 2) (-1)) by lia.
    step. usub. rewrite (swrap32_small (Z.of_nat k + 2 + 1)) by lia.
    do 2 step.
    replace (Z_to_bv 64 (-1 - (Z.of_nat k + 2))) with (Z_to_bv 64 (- (Z.of_nat (S k) + 2))) by (f_equal; lia).
    rewrite (bne_m16 (Z.of_nat (S k) + 2)) by lia.
    destruct (Z.eqb_spec (Z.of_nat (S k) + 2) 16) as [E16|E16]; cbn [negb]; cbv iota.
    - (* the last LED: 0x13160 -> 0x131cc *)
      assert (k = 13)%nat by lia. subst k mk'.
      step.
      eapply sx_close; [exact SXM' | exact K].
    - eapply (Hnext ltac:(lia) mk'); [exact Hmk' | f_equal; lia | reflexivity | reflexivity | exact SXE
                                     | exact Hpn | exact SXM' | exact K]. }
  destruct SXM as (MU & WM & MI & ST & BA & HM & HEv & HLm & HQ1 & HN & HS & HQ2 & H150 & H10).
  unfold spec_msg_cells in HM. rewrite ev_cells_unfold in HEv.
  (* 0x13100-0x13104: led > 8? *)
  do 2 step.
  rewrite (bltu_lit 8 (Z.of_nat k + 2)) by lia.
  destruct (Z.ltb_spec 8 (Z.of_nat k + 2)) as [HI|LO]; cbv iota.
  - (* 0x13118-0x13124: pl[2] (UBSan: pl + 2 does not wrap), bit 15 - led *)
    step. step. take false.
    do 2 step.
    (* 0x13128-0x1312c: the bit index; UBSan: below 32 *)
    step. usub. rewrite (swrap32_neg (Z.of_nat k + 2) 15) by lia.
    step. take false.
    (* 0x13130-0x1313c: the bit *)
    rd_step (sm_sysex_at M + 5). rewrite (zxb_b8 _ R2).
    step. usub. rewrite (srlw_byte P2 (15 - (Z.of_nat k + 2))) by lia.
    pose proof (shiftr_b P2 (15 - (Z.of_nat k + 2)) R2 ltac:(lia)) as RS.
    step. usub.
    pose proof (land_b (Z.shiftr P2 (15 - (Z.of_nat k + 2))) 1 RS ltac:(lia)) as RB.
    step.
    destruct (Z.eqb_spec (Z.land (Z.shiftr P2 (15 - (Z.of_nat k + 2))) 1) 0) as [B0|B1].
    + take true.
      eapply TAIL; [ | reflexivity | sx_mem_solve ].
      rewrite ring_mask_k_S, <- Hmk, (ring_step_hi P1 P2 mk (Z.of_nat k + 2)) by lia.
      rewrite (proj2 (Z.eqb_eq _ _) B0). reflexivity.
    + take false.
      (* 0x13140-0x1314c: mask |= 1 << (led - 1) *)
      step. step. usub. rewrite (sllw1 (Z.of_nat k + 1)) by lia.
      assert (PW : 0 < 2 ^ (Z.of_nat k + 1) <= 2 ^ 14)
        by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
      step. usub.
      step.
      eapply TAIL; [ | reflexivity | sx_mem_solve ].
      rewrite ring_mask_k_S, <- Hmk, (ring_step_hi P1 P2 mk (Z.of_nat k + 2)) by lia.
      rewrite (proj2 (Z.eqb_neq _ _) B1). replace (Z.of_nat k + 2 - 1) with (Z.of_nat k + 1) by lia.
      reflexivity.
  - (* 0x13108-0x13114: pl[1] (UBSan: pl + 1 does not wrap), bit 8 - led *)
    step. take false.
    do 3 step.
    (* 0x13128-0x1312c: the bit index; UBSan: below 32 *)
    step. usub. rewrite (swrap32_neg (Z.of_nat k + 2) 8) by lia.
    step. take false.
    (* 0x13130-0x1313c: the bit *)
    rd_step (sm_sysex_at M + 4). rewrite (zxb_b8 _ R1).
    step. usub. rewrite (srlw_byte P1 (8 - (Z.of_nat k + 2))) by lia.
    pose proof (shiftr_b P1 (8 - (Z.of_nat k + 2)) R1 ltac:(lia)) as RS.
    step. usub.
    pose proof (land_b (Z.shiftr P1 (8 - (Z.of_nat k + 2))) 1 RS ltac:(lia)) as RB.
    step.
    destruct (Z.eqb_spec (Z.land (Z.shiftr P1 (8 - (Z.of_nat k + 2))) 1) 0) as [B0|B1].
    + take true.
      eapply TAIL; [ | reflexivity | sx_mem_solve ].
      rewrite ring_mask_k_S, <- Hmk, (ring_step_lo P1 P2 mk (Z.of_nat k + 2)) by lia.
      rewrite (proj2 (Z.eqb_eq _ _) B0). reflexivity.
    + take false.
      (* 0x13140-0x1314c: mask |= 1 << (led - 1) *)
      step. step. usub. rewrite (sllw1 (Z.of_nat k + 1)) by lia.
      assert (PW : 0 < 2 ^ (Z.of_nat k + 1) <= 2 ^ 14)
        by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
      step. usub.
      step.
      eapply TAIL; [ | reflexivity | sx_mem_solve ].
      rewrite ring_mask_k_S, <- Hmk, (ring_step_lo P1 P2 mk (Z.of_nat k + 2)) by lia.
      rewrite (proj2 (Z.eqb_neq _ _) B1). replace (Z.of_nat k + 2 - 1) with (Z.of_nat k + 1) by lia.
      reflexivity.
Qed.

(* the invariant at every k <= 13, by induction on the LEDs left *)
Lemma ring_loop : forall k, (k <= 13)%nat -> ring_inv k.
Proof.
  intros k. remember (13 - k)%nat as f eqn:Hf. revert k Hf.
  induction f as [|f IH]; intros k Hf Hk; apply ring_inv_step; try assumption; intros Hlt; [lia|].
  apply IH; lia.
Qed.

Lemma ring_start : ring_inv 0.
Proof. apply ring_loop. lia. Qed.

End Loop.

(* ---- the case ---- *)

Lemma sx_ring_evt :
  forall (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
         (Sp lo body : Z) (bb : list byte) (M : spec_msg) (Q : machine_state -> Prop),
    sx_env Sp lo body bb M -> byte_at (map bz bb) (sm_sysex_at M + 2) = 0 ->
    owed_k Q gp tp x23 F fc m0 Sp lo body (Z.of_nat (length bb))
      (Owed M (spec_event_of (map bz bb) M) 0 (sm_next M) (sm_status_out M)) ->
    at_sx Q gp tp x23 F fc m0 Sp lo body bb M 0x130c4.
Proof.
  intros gp tp x23 F fc m0 Sp lo body bb M Q SXE Hfn K.
  pose proof SXE as SXE0. sx_env_facts SXE.
  rewrite (seo_ring _ M E240 Hn3 Hmk Hfn) in K.
  replace (sm_sysex_at M + 3 + 1) with (sm_sysex_at M + 4) in K by lia.
  replace (sm_sysex_at M + 3 + 2) with (sm_sysex_at M + 5) in K by lia.
  pose proof (bat_range bb (sm_sysex_at M + 3)) as R0.
  unfold at_sx. intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 m q1 q2 j56
    -> -> -> -> SXM.
  destruct SXM as (MU & WM & MI & ST & BA & HM & HEv & HLm & HQ1 & HN & HS & HQ2 & H150 & H10).
  unfold spec_msg_cells in HM. rewrite ev_cells_unfold in HEv.
  (* 0x130c4-0x130c8: pn != 3 -> 0x131cc *)
  do 2 step.
  rewrite (beq_lit (sm_sysex_len M - 3) 3) by lia.
  destruct (Z.eqb_spec (sm_sysex_len M - 3) 3) as [P3|P3]; cbn [negb]; cbv iota.
  2: { try rewrite (proj2 (Z.eqb_neq _ _) P3) in K. cbn [negb] in K. sx_fin K. }
  try rewrite (proj2 (Z.eqb_eq _ _) P3) in K. cbn [negb] in K.
  (* 0x130cc-0x130dc: kind, strip *)
  do 2 step.
  rd_step (sm_sysex_at M + 3). rewrite (zxb_b8 _ R0).
  step. usub.
  step. rewrite le1_lit. mem_after_store.
  (* 0x130e0-0x130fc: the first mask bit, pl + 1, pl + 2, led = 2, a5 = -2 *)
  rd_step (sm_sysex_at M + 3). rewrite (zxb_b8 _ R0).
  do 3 step.
  do 2 step. usub.
  rewrite (shl_shr_bit _ 57 6 R0 ltac:(lia) ltac:(lia)).
  do 2 step.
  (* 0x13100: the loop *)
  pose proof ring_start as RS. unfold ring_inv in RS.
  eapply RS; [ reflexivity | reflexivity | reflexivity | reflexivity | exact SXE0 | exact P3 | sx_mem_solve
             | exact K ].
Qed.
