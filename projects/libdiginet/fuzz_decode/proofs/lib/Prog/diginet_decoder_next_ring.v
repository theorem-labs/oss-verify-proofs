(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* diginet_decoder_next in fuzz_decode.plain, the ring case of the sysex switch (fn 0x00, from the jump target 0x13f98): the strip,
   the mask's bit 0 and the LED loop over k = 0..6 (diginet_decode.c:50-62). The loop (0x13fd8 .. 0x14014) is walked one
   half-turn at a time in continuation style (ring_h1: the bit of s[4], ring_h2: the bit of s[5]), and ring_walk chains the
   seven turns by induction on the fuel of ring_loop. The mask register holds Z_to_bv 64 of the model's mask before every
   sh, so the stored cell is ev_head's C2 (Z_to_bv 64 (de_mask e)).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout diginet_cursor_init_c
  diginet_decoder_next_c diginet_decoder_next_bridge diginet_decoder_next_lib.
Import ListNotations.
Open Scope Z_scope.

(* ---- values ---- *)

(* a case split over the seven turns of the LED loop *)
Ltac rg_k7 k :=
  let H := fresh "Hk7" in
  assert (H : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia;
  destruct H as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ].

(* sllw t0, a4, a3 with a4 = 1, a3 = 6 - k *)
Lemma rg_bit_k : forall k, 0 <= k <= 6 ->
  bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 (6 - k)) mod 32)) = Z.shiftl 1 (6 - k).
Proof. intros k Hk. rg_k7 k; vm_compute; reflexivity. Qed.

(* sllw t1, a7, a0 with a7 = 2, a0 = k *)
Lemma rg_lo_k : forall k, 0 <= k <= 6 ->
  bv_swrap 32 (Z.shiftl 2 (bv_unsigned (Z_to_bv 64 k) mod 32)) = Z.shiftl 1 (1 + k).
Proof. intros k Hk. rg_k7 k; vm_compute; reflexivity. Qed.

(* sllw t0, a5, a0 with a5 = 0x100, a0 = k *)
Lemma rg_hi_k : forall k, 0 <= k <= 6 ->
  bv_swrap 32 (Z.shiftl 256 (bv_unsigned (Z_to_bv 64 k) mod 32)) = Z.shiftl 1 (8 + k).
Proof. intros k Hk. rg_k7 k; vm_compute; reflexivity. Qed.

(* addiw a0, a0, 1 *)
Lemma rg_inc : forall k, 0 <= k <= 6 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 k) + 1) = k + 1.
Proof. intros k Hk. rg_k7 k; vm_compute; reflexivity. Qed.

Lemma rg_shl : forall j, 0 <= j <= 14 -> 1 <= Z.shiftl 1 j <= 16384.
Proof.
  intros j Hj. rewrite Z.shiftl_1_l. split.
  - change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia.
  - change 16384 with (2 ^ 14). apply Z.pow_le_mono_r; lia.
Qed.

Lemma rg_shl6 : forall j, 0 <= j <= 6 -> 1 <= Z.shiftl 1 j <= 64.
Proof.
  intros j Hj. rewrite Z.shiftl_1_l. split.
  - change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia.
  - change 64 with (2 ^ 6). apply Z.pow_le_mono_r; lia.
Qed.

Lemma rg_lor_lt : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Hn Ha Hb.
  assert (E : Z.lor a b mod 2 ^ n = Z.lor a b).
  { apply Z.bits_inj'. intros i Hi. destruct (Z.ltb_spec i n) as [L|L].
    - rewrite Z.mod_pow2_bits_low by exact L. reflexivity.
    - rewrite Z.mod_pow2_bits_high by lia. rewrite Z.lor_spec.
      rewrite <- (Z.mod_small a (2 ^ n)) by exact Ha. rewrite <- (Z.mod_small b (2 ^ n)) by exact Hb.
      rewrite !Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- E. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma rg_lor : forall M X, 0 <= M < 32768 -> 0 <= X < 32768 -> 0 <= Z.lor M X < 32768.
Proof.
  intros M X HM HX.
  pose proof (rg_lor_lt M X 15 ltac:(lia) ltac:(change (2 ^ 15) with 32768; lia)
                ltac:(change (2 ^ 15) with 32768; lia)) as H.
  change (2 ^ 15) with 32768 in H. exact H.
Qed.

(* bit 6 of a byte, as slli 57 / srli 63 takes it: the mask's bit 0 (diginet_decode.c:55) *)
Lemma rg_bit6 : forall x, 0 <= x < 256 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 57))) 63 = u16 (if negb (Z.land x 64 =? 0) then 1 else 0).
Proof.
  intros x Hx. apply Z.eqb_eq. revert x Hx.
  apply (byte_forall (fun x => Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 57))) 63 =?
                               u16 (if negb (Z.land x 64 =? 0) then 1 else 0))).
  vm_compute. reflexivity.
Qed.

Lemma rg_mask0 : forall c : bool, 0 <= u16 (if c then 1 else 0) < 32768.
Proof. intros [|]; unfold u16; rewrite Z.mod_small by lia; lia. Qed.

(* ---- the two halves of a turn of ring_loop ---- *)

(* the mask after the bit of b1 = pl[1] (diginet_decode.c:57-58) *)
Definition rh1 (M b k : Z) : Z :=
  if negb (Z.land b (Z.shiftl 1 (6 - k)) =? 0) then u16 (Z.lor M (u16 (Z.shiftl 1 (1 + k)))) else M.

(* the mask after the bit of b2 = pl[2] (diginet_decode.c:59-60) *)
Definition rh2 (M b k : Z) : Z :=
  if negb (Z.land b (Z.shiftl 1 (6 - k)) =? 0) then u16 (Z.lor M (u16 (Z.shiftl 1 (8 + k)))) else M.

Lemma ring_loop_S : forall M b1 b2 k f,
  ring_loop M b1 b2 k (S f) = ring_loop (rh2 (rh1 M b1 k) b2 k) b1 b2 (k + 1) f.
Proof. reflexivity. Qed.

Lemma ring_loop_0 : forall M b1 b2 k, ring_loop M b1 b2 k O = M.
Proof. reflexivity. Qed.

Lemma rh1_range : forall M b k, 0 <= M < 32768 -> 0 <= k <= 6 -> 0 <= rh1 M b k < 32768.
Proof.
  intros M b k HM Hk. unfold rh1. destruct (negb _); [|exact HM].
  pose proof (rg_shl (1 + k) ltac:(lia)) as S.
  rewrite (u16_small (Z.shiftl 1 (1 + k))) by lia.
  pose proof (rg_lor M (Z.shiftl 1 (1 + k)) HM ltac:(lia)) as L.
  rewrite u16_small by lia. exact L.
Qed.

Lemma rh2_range : forall M b k, 0 <= M < 32768 -> 0 <= k <= 6 -> 0 <= rh2 M b k < 32768.
Proof.
  intros M b k HM Hk. unfold rh2. destruct (negb _); [|exact HM].
  pose proof (rg_shl (8 + k) ltac:(lia)) as S.
  rewrite (u16_small (Z.shiftl 1 (8 + k))) by lia.
  pose proof (rg_lor M (Z.shiftl 1 (8 + k)) HM ltac:(lia)) as L.
  rewrite u16_small by lia. exact L.
Qed.

(* ---- tactics ---- *)

(* decode_sysex with the body bytes read as at8 (as diginet_decoder_next_sysex.v has it) *)
Ltac sx_model :=
  unfold decode_sysex, DIGINET_SYSEX_MAKER, DIGINET_FN_RING, DIGINET_FN_METER, DIGINET_FN_LEDS,
    DIGINET_FN_SCRIBBLE, DIGINET_FN_COUNTER, DIGINET_FN_SYSTEM; cbv zeta;
  rewrite !byte_at_map_Z by lia.

(* dn_at's facts as literal cell hypotheses (dn_open's names) for an event de_set_mask M e *)
Ltac rg_open H :=
  destruct H as (HDc & HD2 & HBB & H0 & HL & HP & HM & HS & HE & HEM & MU & WM & MI);
  unfold cursor_cells in HDc; unfold dmsg_cells in HM, HEM;
  unfold ev_head, arr_cells in HE;
  cbn [map seq nth app de_kind de_strip de_button de_zone de_on de_right de_addr de_lsb_missing de_value
       de_delta de_mask de_segments de_len de_text de_seg de_dots de_device de_set_mask] in HE.

(* dn_at back from the literal cell hypotheses *)
Ltac rg_close := unfold dn_at; repeat (split; [eassumption|]); eassumption.

Section RingWalk.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (d ev body lo : Z) (bb ej cpad : list byte) (p : option Z)
  (res : Z * dgn_event * dgn_decoder) (msg : dgn_msg) (pos1 : nat) (st1 : Z) (mpad j0 jl jp : list byte)
  (ra' t2 s3' t3 t4 t5 t6 : word).

(* the machine in the LED loop: a0 = k, a1 = s, a2 = 7, a3 = 6 - k, a4 = 1, a5 = 0x100, a6 = the mask, a7 = 2 *)
Local Abbreviation LS pc a0 a3 a6 t0 t1 m :=
  (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 ev) (Z_to_bv 64 1)
           a0 (Z_to_bv 64 (body + dm_sysex msg)) (Z_to_bv 64 7) a3 (Z_to_bv 64 1) (Z_to_bv 64 256) a6
           (Z_to_bv 64 2) (Z_to_bv 64 (dm_sysex_len msg)) s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Local Abbreviation DA m e := (dn_at sp m0 m d ev body bb cpad p pos1 st1 msg mpad j0 jl jp s3 s2 s1 s0 ra e).
Local Abbreviation B4 := (at8 bb (Z.to_nat (dm_sysex msg + 4))).
Local Abbreviation B5 := (at8 bb (Z.to_nat (dm_sysex msg + 5))).

(* 0x13fd8 .. 0x13ff0: lbu t1 = s[4]; t0 = 1 << (6 - k); if t0 & t1 then mask |= 2 << k and sh *)
Lemma ring_h1 : forall (Q : machine_state -> Prop) (k M : Z) (e : dgn_event) (m : word -> option byte) (t0 t1 : word),
  dn_ctx sp m0 d ev body lo bb p res msg pos1 st1 mpad -> DA m (de_set_mask M e) ->
  0 <= k <= 6 -> 0 <= M < 32768 -> 0 <= dm_sysex msg -> dm_sysex msg + 5 < Z.of_nat (length bb) ->
  (forall (m' : word -> option byte) (t1' : word), DA m' (de_set_mask (rh1 M B4 k) e) ->
     evt rsegs Q (LS 0x13ff4 (Z_to_bv 64 k) (Z_to_bv 64 (6 - k)) (Z_to_bv 64 (rh1 M B4 k))
                    (Z_to_bv 64 (Z.shiftl 1 (6 - k))) t1' m')) ->
  evt rsegs Q (LS 0x13fd8 (Z_to_bv 64 k) (Z_to_bv 64 (6 - k)) (Z_to_bv 64 M) t0 t1 m).
Proof.
  intros Q k M e m t0 t1 HCTX HAT Hk HMr Hs HLen K.
  pose proof HAT as HAT0. dn_ctx_open HCTX. rg_open HAT.
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 4))) as RB.
  pose proof (rg_shl6 (6 - k) ltac:(lia)) as SB.
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 4 HBB ltac:(lia)) as RD.
  (* lbu t1 = s[4]; sllw t0 = 1 << (6 - k); and t1 = t0 & t1 *)
  step. rewrite (dn_zxb_b8 B4) by lia.
  step. rewrite (rg_bit_k k) by lia.
  step. rewrite (unsigned_lit (Z.shiftl 1 (6 - k))), (unsigned_lit B4) by lia.
  pose proof (byte_land_le (Z.shiftl 1 (6 - k)) B4 ltac:(lia) ltac:(lia)) as LB.
  (* beqz t1 *)
  step. rewrite (dn_eqb_u64 (Z.land (Z.shiftl 1 (6 - k)) B4) 0) by lia.
  destruct (Z.eqb_spec (Z.land (Z.shiftl 1 (6 - k)) B4) 0) as [Z0|Z0]; cbv iota.
  - (* the bit is clear: the mask stays *)
    assert (E : rh1 M B4 k = M) by (unfold rh1; rewrite (Z.land_comm B4), Z0; reflexivity).
    rewrite E in K. apply K. exact HAT0.
  - (* the bit is set: sllw t1 = 2 << k; or a6; sh a6 *)
    clear HAT0 RD.
    step. rewrite (rg_lo_k k) by lia.
    pose proof (rg_shl (1 + k) ltac:(lia)) as SL.
    step. rewrite (unsigned_lit M), (unsigned_lit (Z.shiftl 1 (1 + k))) by lia.
    step.
    assert (E : rh1 M B4 k = Z.lor M (Z.shiftl 1 (1 + k))).
    { unfold rh1. rewrite (Z.land_comm B4), (proj2 (Z.eqb_neq _ _) Z0). cbn [negb].
      pose proof (rg_lor M (Z.shiftl 1 (1 + k)) HMr ltac:(lia)) as L.
      rewrite (u16_small (Z.shiftl 1 (1 + k))) by lia. apply u16_small. lia. }
    rewrite E in K. apply K. rg_close.
Qed.

(* 0x13ff4 .. 0x14008: lbu t1 = s[5]; if t0 & t1 then mask |= 0x100 << k and sh *)
Lemma ring_h2 : forall (Q : machine_state -> Prop) (k M : Z) (e : dgn_event) (m : word -> option byte) (t1 : word),
  dn_ctx sp m0 d ev body lo bb p res msg pos1 st1 mpad -> DA m (de_set_mask M e) ->
  0 <= k <= 6 -> 0 <= M < 32768 -> 0 <= dm_sysex msg -> dm_sysex msg + 5 < Z.of_nat (length bb) ->
  (forall (m' : word -> option byte) (t0' t1' : word), DA m' (de_set_mask (rh2 M B5 k) e) ->
     evt rsegs Q (LS 0x1400c (Z_to_bv 64 k) (Z_to_bv 64 (6 - k)) (Z_to_bv 64 (rh2 M B5 k)) t0' t1' m')) ->
  evt rsegs Q (LS 0x13ff4 (Z_to_bv 64 k) (Z_to_bv 64 (6 - k)) (Z_to_bv 64 M) (Z_to_bv 64 (Z.shiftl 1 (6 - k))) t1 m).
Proof.
  intros Q k M e m t1 HCTX HAT Hk HMr Hs HLen K.
  pose proof HAT as HAT0. dn_ctx_open HCTX. rg_open HAT.
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 5))) as RB.
  pose proof (rg_shl6 (6 - k) ltac:(lia)) as SB.
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 5 HBB ltac:(lia)) as RD.
  (* lbu t1 = s[5]; and t0 = t0 & t1 *)
  step. rewrite (dn_zxb_b8 B5) by lia.
  step. rewrite (unsigned_lit (Z.shiftl 1 (6 - k))), (unsigned_lit B5) by lia.
  pose proof (byte_land_le (Z.shiftl 1 (6 - k)) B5 ltac:(lia) ltac:(lia)) as LB.
  (* beqz t0 *)
  step. rewrite (dn_eqb_u64 (Z.land (Z.shiftl 1 (6 - k)) B5) 0) by lia.
  destruct (Z.eqb_spec (Z.land (Z.shiftl 1 (6 - k)) B5) 0) as [Z0|Z0]; cbv iota.
  - (* the bit is clear: the mask stays *)
    assert (E : rh2 M B5 k = M) by (unfold rh2; rewrite (Z.land_comm B5), Z0; reflexivity).
    rewrite E in K. apply K. exact HAT0.
  - (* the bit is set: sllw t0 = 0x100 << k; or a6; sh a6 *)
    clear HAT0 RD.
    step. rewrite (rg_hi_k k) by lia.
    pose proof (rg_shl (8 + k) ltac:(lia)) as SL.
    step. rewrite (unsigned_lit M), (unsigned_lit (Z.shiftl 1 (8 + k))) by lia.
    step.
    assert (E : rh2 M B5 k = Z.lor M (Z.shiftl 1 (8 + k))).
    { unfold rh2. rewrite (Z.land_comm B5), (proj2 (Z.eqb_neq _ _) Z0). cbn [negb].
      pose proof (rg_lor M (Z.shiftl 1 (8 + k)) HMr ltac:(lia)) as L.
      rewrite (u16_small (Z.shiftl 1 (8 + k))) by lia. apply u16_small. lia. }
    rewrite E in K. apply K. rg_close.
Qed.

(* the turns k .. 6 of the loop (n = 7 - k of them), then j 0x140f4, s1 = 1 and the epilogue *)
Lemma ring_walk : forall (n : nat) (k M : Z) (e : dgn_event) (m : word -> option byte) (a0 a3 a6 t0 t1 : word),
  dn_ctx sp m0 d ev body lo bb p res msg pos1 st1 mpad -> DA m (de_set_mask M e) -> de_msg e = msg ->
  res = (1, de_set_mask (ring_loop M B4 B5 k n) e, {| dd_c := cursor_of bb pos1 st1; dd_p := p |}) ->
  (1 <= n)%nat -> k + Z.of_nat n = 7 -> 0 <= k -> 0 <= M < 32768 ->
  0 <= dm_sysex msg -> dm_sysex msg + 5 < Z.of_nat (length bb) ->
  a0 = Z_to_bv 64 k -> a3 = Z_to_bv 64 (6 - k) -> a6 = Z_to_bv 64 M ->
  evt rsegs (dn_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 d ev body lo cpad ej res)
    (LS 0x13fd8 a0 a3 a6 t0 t1 m).
Proof.
  induction n as [|n IH];
    intros k M e m a0 a3 a6 t0 t1 HCTX HAT HMSG HRS Hn Hk Hk0 HMr Hs HLen -> -> ->; [lia|].
  eapply ring_h1; [exact HCTX | exact HAT | lia | lia | lia | lia |].
  intros m' t1' HAT1.
  eapply ring_h2; [exact HCTX | exact HAT1 | lia | apply rh1_range; lia | lia | lia |].
  intros m'' t0' t1'' HAT2.
  rewrite ring_loop_S in HRS.
  (* addiw a0 = k + 1; addi a3 = 6 - k - 1; bne a0, a2 = 7 *)
  step. rewrite (rg_inc k) by lia.
  step. step.
  rewrite (dn_eqb_u64 (k + 1) 7) by lia.
  destruct n as [|n].
  - (* k = 6: the loop ends; j 0x140f4; s1 = 1; the epilogue *)
    if_false.
    step. step.
    rewrite ring_loop_0 in HRS.
    pose proof HCTX as HC. dn_ctx_open HC. rg_open HAT2.
    dn_fin HRS HDc HD2 HE HEM.
    + exact HMSG.
    + reflexivity.
  - (* the next turn *)
    if_true.
    eapply IH; [exact HCTX | exact HAT2 | exact HMSG | exact HRS | lia | lia | lia | | lia | lia
               | reflexivity | f_equal; lia | reflexivity].
    apply rh2_range; [apply rh1_range|]; lia.
Qed.

End RingWalk.

Section Ring.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (d ev body lo : Z) (bb ej cpad : list byte) (p : option Z)
  (res : Z * dgn_event * dgn_decoder) (msg : dgn_msg) (pos1 : nat) (st1 : Z) (mpad j0 jl jp : list byte).

Lemma dn_ring : forall (ra' t0 t1 t2 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 : word) (m1 : word -> option byte),
  dn_ctx sp m0 d ev body lo bb p res msg pos1 st1 mpad ->
  dn_at sp m0 m1 d ev body bb cpad p pos1 st1 msg mpad j0 jl jp s3 s2 s1 s0 ra
    (de_set_device (at8 bb (Z.to_nat (dm_sysex msg + 1))) (dn_e0 msg)) ->
  dm_status msg = 240 -> 1 <= dm_sysex msg -> 3 <= dm_sysex_len msg ->
  dm_sysex msg + dm_sysex_len msg < Z.of_nat (length bb) ->
  at8 bb (Z.to_nat (dm_sysex msg)) = 19 -> at8 bb (Z.to_nat (dm_sysex msg + 2)) = 0 ->
  evt rsegs (dn_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 d ev body lo cpad ej res)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 ev) (Z_to_bv 64 1)
             (Z_to_bv 64 (dm_sysex_len msg + -3)) (Z_to_bv 64 (body + dm_sysex msg)) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (dm_sysex_len msg)) s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f98) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0 t1 t2 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 m1 HCTX HAT HF0 HS1 N3 HSN MK HFN.
  pose proof HCTX as HCTX0. dn_ctx_open HCTX. dn_open HAT.
  assert (HR : res = (1, decode_sysex (map bz bb) msg (dn_e0 msg), {| dd_c := cursor_of bb pos1 st1; dd_p := p |})).
  { rewrite HRES. unfold dn_tail. rewrite HF0. reflexivity. }
  (* addi a2 = 3; bne pn, 3 *)
  step. step.
  rewrite (dn_eqb_u64 (dm_sysex_len msg + -3) 3) by lia.
  destruct (Z.eq_dec (dm_sysex_len msg + -3) 3) as [P3|P3].
  2: {
    (* another length: kind 13 and the device *)
    if_true.
    dn_fin HR HDc HD2 HE HEM; sx_model;
      rewrite MK, HFN, (proj2 (Z.ltb_ge _ _) N3); cbn [Z.eqb Pos.eqb orb negb];
      rewrite (proj2 (Z.eqb_neq (dm_sysex_len msg - 3) 3)) by lia; cbn [negb].
    - dmsg_eq.
    - ev_head_lit. reflexivity. }
  if_false.
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 3))) as RB3.
  pose proof (byte_land_le (at8 bb (Z.to_nat (dm_sysex msg + 3))) 63 ltac:(lia) ltac:(lia)) as LB3.
  (* a0 = 0; a2 = 7; sw kind 7 *)
  step. step. step.
  (* lbu a3 = s[3]; strip = s[3] & 0x3f; sb *)
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 3 HBB ltac:(lia)) as RD3.
  step. rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 3)))) by lia.
  step. rewrite (unsigned_lit (at8 bb (Z.to_nat (dm_sysex msg + 3)))) by lia.
  step. clear RD3.
  (* lbu a6 = s[3]; a3 = 6, a4 = 1, a5 = 0x100; a6 = bit 6 of s[3]; sh; a7 = 2 *)
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 3 HBB ltac:(lia)) as RD3.
  step. rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 3)))) by lia.
  do 5 step.
  rewrite (unsigned_lit (at8 bb (Z.to_nat (dm_sysex msg + 3)))) by lia.
  rewrite (rg_bit6 (at8 bb (Z.to_nat (dm_sysex msg + 3)))) by lia.
  step. step. clear RD3.
  rewrite <- (u8_small (Z.land (at8 bb (Z.to_nat (dm_sysex msg + 3))) 63)) in HE by lia.
  (* the loop *)
  eapply ring_walk with (n := 7%nat) (k := 0)
    (M := u16 (if negb (Z.land (at8 bb (Z.to_nat (dm_sysex msg + 3))) 64 =? 0) then 1 else 0))
    (e := de_set_strip (u8 (Z.land (at8 bb (Z.to_nat (dm_sysex msg + 3))) 63))
            (de_set_kind DIGINET_EV_RING (de_set_device (at8 bb (Z.to_nat (dm_sysex msg + 1)))
              (de_set_kind DIGINET_EV_OTHER (dn_e0 msg))))).
  - exact HCTX0.
  - rg_close.
  - reflexivity.
  - rewrite HR. f_equal. f_equal. sx_model.
    rewrite MK, HFN, (proj2 (Z.ltb_ge _ _) N3). cbn [Z.eqb Pos.eqb orb negb].
    rewrite (proj2 (Z.eqb_eq (dm_sysex_len msg - 3) 3)) by lia. cbn [negb].
    replace (dm_sysex msg + 3 + 1) with (dm_sysex msg + 4) by lia.
    replace (dm_sysex msg + 3 + 2) with (dm_sysex msg + 5) by lia.
    reflexivity.
  - lia.
  - lia.
  - lia.
  - apply rg_mask0.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

End Ring.
