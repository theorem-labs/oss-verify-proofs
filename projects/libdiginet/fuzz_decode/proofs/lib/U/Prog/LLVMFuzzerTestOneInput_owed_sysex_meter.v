(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the case SPEC_FN_METER (0x10) of the system exclusive part of the inlined
   spec_event_of (spec.h:453-464, with spec_segments of spec.h:372-378 inlined) in LLVMFuzzerTestOneInput on the
   UBSan image, 0x13268-0x132ec (the entry 1 of the jump table at 0x103a4; a0 = pl, a1 = s, a3 = pn):
     0x13268-0x1326c  pn != 3 -> 0x131cc (the event stays OTHER with the device);
     0x13270-0x13284  e.kind = SPEC_EV_METER (8), e.strip = pl[0] & 0x1f, e.addr = pl[0];
     0x13288-0x13298  e.right = pl[0] >> 5 & 1 (`slli 58` / `srli 63`), a0 = pl + 2;
     0x1329c-0x132a0  UBSan: pl + 2 does not wrap (bltu pl + 2, 2 -> 0x13460);
     0x132a4-0x132c4  mask = (pl[1] & 0x7f) << 7 | pl[2] & 0x7f, e.mask = mask, n = 0;
     0x132c8-0x132e4  spec_segments: the first n of 0 .. 14 with (-1 << n) ^ mask = -1 (the 32-bit `sllw`,
                      sign-extended), that is mask = 2^n - 1, else -1; the loop sets s4 = -1 again each turn
                      (0x132d4), the value s4 already holds;
     0x132e8-0x132ec  e.segments = n (sb), then 0x131cc.
   seg_loop is the loop, by induction on the turns left; seg_test is its test: x ^ mask = -1 iff mask = x ^ -1,
   and (-1 << n) ^ -1 = 2^n - 1. *)
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

(* the meter event of spec.h:459-462 with the mask mk and the segments seg *)
Definition meter_ev (b : list Z) (M : spec_msg) (mk seg : Z) : spec_event :=
  {| se_kind := 8; se_strip := Z.land (byte_at b (sm_sysex_at M + 3)) 31; se_button := 0; se_zone := 0;
     se_on := 0; se_right := Z.land (Z.shiftr (byte_at b (sm_sysex_at M + 3)) 5) 1;
     se_addr := byte_at b (sm_sysex_at M + 3); se_device := byte_at b (sm_sysex_at M + 1); se_len := 0;
     se_dots := 0; se_value := 0; se_mask := mk; se_delta := 0; se_segments := seg; se_text := repeat 0 8;
     se_seg := repeat 0 8 |}.

Lemma segloop_found : forall mk n f, mk = 2 ^ n - 1 -> segments_loop mk n (S f) = n.
Proof. intros mk n f H. cbn [segments_loop]. rewrite (proj2 (Z.eqb_eq _ _) H). reflexivity. Qed.

Lemma segloop_next : forall mk n f, mk <> 2 ^ n - 1 -> segments_loop mk n (S f) = segments_loop mk (n + 1) f.
Proof. intros mk n f H. cbn [segments_loop]. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma s8_small : forall x, - 128 <= x < 128 -> s8 x = x.
Proof. intros x Hx. unfold s8. rewrite Z.mod_small by lia. lia. Qed.

(* ---- the loop's test: (-1 << n) ^ mask = -1 in 64 bits, -1 << n the sign-extended 32-bit sllw ---- *)

Lemma lxor_ones_iff : forall c z, Z.lxor c z = 18446744073709551615 <-> z = Z.lxor c 18446744073709551615.
Proof.
  intros c z. split; intros H.
  - rewrite <- H, <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity.
  - rewrite H, <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity.
Qed.

Lemma seg_test : forall n mk, 0 <= n <= 14 -> 0 <= mk < 2 ^ 14 ->
  bv_eqb (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl 18446744073709551615 (n mod 32)))))
                             mk))
         (Z_to_bv 64 (-1))
  = (mk =? 2 ^ n - 1).
Proof.
  intros n mk Hn Hm.
  assert (E : bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl 18446744073709551615 (n mod 32)))) = 2 ^ 64 - 2 ^ n /\
              Z.lxor (2 ^ 64 - 2 ^ n) 18446744073709551615 = 2 ^ n - 1).
  { assert (D : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14) by lia.
    destruct D as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]; split; vm_compute; reflexivity. }
  destruct E as [E1 E2].
  assert (P : 0 < 2 ^ n <= 2 ^ 14) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  unfold bv_eqb. rewrite E1.
  change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615.
  rewrite unsigned_lit by (apply Z_lxor_range; lia).
  destruct (Z.eqb_spec (Z.lxor (2 ^ 64 - 2 ^ n) mk) 18446744073709551615) as [H|H];
    destruct (Z.eqb_spec mk (2 ^ n - 1)) as [H'|H']; try reflexivity; exfalso.
  - apply lxor_ones_iff in H. rewrite E2 in H. contradiction.
  - apply H. apply lxor_ones_iff. rewrite E2. exact H'.
Qed.

(* ---- the loop ---- *)

Section Loop.
Variables (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (Sp lo body : Z)
  (bb : list byte) (M : spec_msg) (Q : machine_state -> Prop)
  (y1 y5 y6 y7 y15 y16 y17 y21 y22 y28 y29 y30 y31 : word) (q1 q2 j56 : list byte).

Local Abbreviation P1 := (byte_at (map bz bb) (sm_sysex_at M + 4)).
Local Abbreviation P2 := (byte_at (map bz bb) (sm_sysex_at M + 5)).
Local Abbreviation MK := (Z.lor (Z.shiftl (Z.land P1 127) 7) (Z.land P2 127)).

(* the state at a pc of the loop: n = a0, mask = a1, a4 = 15 *)
Local Abbreviation ST pc a0 a2 a3 s4 m :=
  (MS (mkR y1 (Z_to_bv 64 Sp) gp tp y5 y6 y7 (Z_to_bv 64 0x1f) (Z_to_bv 64 (Z.of_nat (length bb)))
         a0 (Z_to_bv 64 MK) a2 a3 (Z_to_bv 64 15) y15 y16 y17
         (Z_to_bv 64 body) (Z_to_bv 64 (Sp + 0x50)) s4 y21 y22 x23 (Z_to_bv 64 0xb0)
         (Z_to_bv 64 1) (Z_to_bv 64 13) (Z_to_bv 64 0x90) y28 y29 y30 y31)
       F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma meter_mask_range : 0 <= MK < 2 ^ 14.
Proof.
  pose proof (bat_range bb (sm_sysex_at M + 4)) as R1. pose proof (bat_range bb (sm_sysex_at M + 5)) as R2.
  assert (L1 : 0 <= Z.land P1 127 < 2 ^ 7) by (rewrite Z.land_comm; apply land_lt_pow2; lia).
  assert (L2 : 0 <= Z.land P2 127 < 2 ^ 7) by (rewrite Z.land_comm; apply land_lt_pow2; lia).
  assert (S1 : 0 <= Z.shiftl (Z.land P1 127) 7 < 2 ^ 14) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  apply lor_lt_pow2; lia.
Qed.

Lemma seg_loop : forall (f : nat) (n : Z) (a0 a2 a3 s4 : word) (m : word -> option byte),
  n + Z.of_nat f = 15 -> 0 <= n -> (1 <= f)%nat ->
  a0 = Z_to_bv 64 n -> s4 = Z_to_bv 64 (2 ^ 64 - 1) ->
  spec_segments MK = segments_loop MK n f ->
  sx_env Sp lo body bb M -> sm_sysex_len M - 3 = 3 ->
  sx_mem m0 m Sp lo body bb M (meter_ev (map bz bb) M MK 0) q1 q2 j56 ->
  owed_k Q gp tp x23 F fc m0 Sp lo body (Z.of_nat (length bb))
    (Owed M (meter_ev (map bz bb) M MK (s8 (spec_segments MK))) 0 (sm_next M) (sm_status_out M)) ->
  evt rsegs Q (ST 0x132c8 a0 a2 a3 s4 m).
Proof.
  intros f; induction f as [|f IH]; intros n a0 a2 a3 s4 m Hnf Hn0 Hf1 -> -> Hseg SXE Hpn SXM K; [lia|].
  pose proof SXE as SXE0. sx_env_facts SXE0.
  pose proof meter_mask_range as MKR.
  destruct SXM as (MU & WM & MI & ST & BA & HM & HEv & HLm & HQ1 & HN & HS & HQ2 & H150 & H10).
  unfold spec_msg_cells in HM. rewrite ev_cells_unfold in HEv.
  (* 0x132c8-0x132d8: (-1 << n) ^ mask = -1? *)
  step. step. usub. step. usub. do 2 step.
  rewrite (seg_test n MK) by lia.
  destruct (Z.eqb_spec MK (2 ^ n - 1)) as [EQ|NE]; cbv iota.
  - (* 0x132e8-0x132ec: e.segments = n *)
    rewrite Hseg, (segloop_found MK n f EQ), (s8_small n) in K by lia.
    step. rewrite le1_lit. mem_after_store.
    step.
    replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2 ^ 64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
    sx_fin K.
  - (* 0x132dc-0x132e0: n + 1, the loop test *)
    step. usub. rewrite (swrap32_small (n + 1)) by lia.
    step. rewrite (beq_lit (n + 1) 15) by lia.
    destruct (Z.eqb_spec (n + 1) 15) as [E15|N15]; cbn [negb]; cbv iota.
    + (* 0x132e4-0x132ec: e.segments = -1 *)
      assert (f = O) by lia. subst f.
      rewrite Hseg, (segloop_next MK n O NE) in K. cbn [segments_loop] in K. change (s8 (-1)) with (-1) in K.
      step. step. rewrite le1_lit. mem_after_store.
      step.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2 ^ 64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
      sx_fin K.
    + eapply (IH (n + 1)); [ lia | lia | lia | reflexivity | apply bv_eq; vm_compute; reflexivity
                           | rewrite Hseg; apply segloop_next; exact NE | exact SXE | exact Hpn | sx_mem_solve
                           | exact K ].
Qed.

End Loop.

(* ---- the case ---- *)

Lemma sx_meter_evt :
  forall (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
         (Sp lo body : Z) (bb : list byte) (M : spec_msg) (Q : machine_state -> Prop),
    sx_env Sp lo body bb M -> byte_at (map bz bb) (sm_sysex_at M + 2) = 16 ->
    owed_k Q gp tp x23 F fc m0 Sp lo body (Z.of_nat (length bb))
      (Owed M (spec_event_of (map bz bb) M) 0 (sm_next M) (sm_status_out M)) ->
    at_sx Q gp tp x23 F fc m0 Sp lo body bb M 0x13268.
Proof.
  intros gp tp x23 F fc m0 Sp lo body bb M Q SXE Hfn K.
  pose proof SXE as SXE0. sx_env_facts SXE.
  pose proof (bat_range bb (sm_sysex_at M + 3)) as R0.
  pose proof (bat_range bb (sm_sysex_at M + 4)) as R1.
  pose proof (bat_range bb (sm_sysex_at M + 5)) as R2.
  pose proof (meter_mask_range bb M) as MKR.
  assert (L1 : 0 <= Z.land (byte_at (map bz bb) (sm_sysex_at M + 4)) 127 < 2 ^ 7)
    by (rewrite Z.land_comm; apply land_lt_pow2; lia).
  assert (L2 : 0 <= Z.land (byte_at (map bz bb) (sm_sysex_at M + 5)) 127 < 2 ^ 7)
    by (rewrite Z.land_comm; apply land_lt_pow2; lia).
  assert (S1 : 0 <= Z.shiftl (Z.land (byte_at (map bz bb) (sm_sysex_at M + 4)) 127) 7 < 2 ^ 14)
    by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (seo_meter _ M E240 Hn3 Hmk Hfn) in K.
  replace (sm_sysex_at M + 3 + 1) with (sm_sysex_at M + 4) in K by lia.
  replace (sm_sysex_at M + 3 + 2) with (sm_sysex_at M + 5) in K by lia.
  unfold u16 in K. rewrite Z.mod_small in K by lia.
  unfold at_sx. intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 m q1 q2 j56
    -> -> -> -> SXM.
  destruct SXM as (MU & WM & MI & ST & BA & HM & HEv & HLm & HQ1 & HN & HS & HQ2 & H150 & H10).
  unfold spec_msg_cells in HM. rewrite ev_cells_unfold in HEv.
  (* 0x13268-0x1326c: pn != 3 -> 0x131cc *)
  do 2 step.
  rewrite (beq_lit (sm_sysex_len M - 3) 3) by lia.
  destruct (Z.eqb_spec (sm_sysex_len M - 3) 3) as [P3|P3]; cbn [negb]; cbv iota.
  2: { try rewrite (proj2 (Z.eqb_neq _ _) P3) in K. cbn [negb] in K. sx_fin K. }
  try rewrite (proj2 (Z.eqb_eq _ _) P3) in K. cbn [negb] in K.
  (* 0x13270-0x13284: kind, strip, addr *)
  do 2 step.
  rd_step (sm_sysex_at M + 3). rewrite (zxb_b8 _ R0).
  step. usub.
  step. rewrite le1_lit. mem_after_store.
  step. rewrite le1_lit. mem_after_store.
  (* 0x13288-0x13298: right, pl + 2 *)
  rd_step (sm_sysex_at M + 3). rewrite (zxb_b8 _ R0).
  step. usub. step.
  rewrite (shl_shr_bit _ 58 5 R0 ltac:(lia) ltac:(lia)).
  step.
  step. rewrite le1_lit. mem_after_store.
  (* 0x1329c-0x132a0: UBSan pl + 2 does not wrap *)
  step. step. take false.
  (* 0x132a4-0x132c4: n = 0, the mask, a4 = 15 *)
  step.
  rd_step (sm_sysex_at M + 4). rewrite (zxb_b8 _ R1).
  rd_step (sm_sysex_at M + 5). rewrite (zxb_b8 _ R2).
  step. usub. step. usub. step. usub. step. usub.
  do 2 step.
  (* 0x132c8: the loop *)
  eapply seg_loop with (f := 15%nat) (n := 0);
    [ reflexivity | lia | lia | reflexivity | reflexivity | reflexivity | exact SXE0 | exact P3
    | sx_mem_solve | exact K ].
Qed.
