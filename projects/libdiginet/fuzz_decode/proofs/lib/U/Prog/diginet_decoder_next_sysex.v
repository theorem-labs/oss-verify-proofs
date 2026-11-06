(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the system-exclusive segment of the UBSan walk of diginet_decoder_next
   (lib/U/Prog/diginet_decoder_next_seg.v), from DN_DECODE (0x14054) to DN_RET (0x1429c) when the model's message
   is a sysex (dm_status msg = 0xf0): diginet_decode.c:123-126 with decode_sysex (:37-105) inlined, against DgnLib.v's
   decode_sysex. diginet_decoder_next_sysex_seg is the segment; it hands the cut's dn_seg_cont the model's event
   dn_e bb dc = decode_sysex b msg (kind OTHER over the zeroed event with msg) and decoder dn_d bb dc (sx_model).
   - sx_head, 0x14054-0x14068 and 0x140a4-0x14128: kind OTHER (0x14064), the status tests, n = msg.sysex_len < 3
     (0x140b8) and s[0] != 0x13 (0x140cc) to DN_RET, ev->device = s[1] (0x140e0), and the switch on fn = s[2]:
     0x140f4-0x14104 rotate fn right by 4 in 32 bits, which is at most 7 exactly when fn's low nibble is 0 and
     fn < 0x80, and then it is fn / 16 (sx_fn_dec, checked on the 256 bytes); otherwise DN_RET. The jump through the
     table at 0x103e4 (0x14108-0x14128) is taken for each of the 8 indices: ring 0x1412c, meter 0x14348, leds
     0x1430c, counter 0x143ac, scribble 0x14420, 0x50 / 0x60 to DN_RET, system 0x1433c (kind SYSTEM, inline).
   - One lemma per arm, each from its table target to DN_RET, the pn test included: sx_arm_ring (0x1412c-0x141bc and
     0x14298; the LED loop 0x14178-0x141b8 is sx_ring_loop, by induction on ring_loop's fuel), sx_arm_leds
     (0x1430c-0x14338), sx_arm_meter (0x14348-0x143a8, with diginet_meter_segments_holds at 0x143a0 on a mask below
     2^14), sx_arm_counter (0x143ac-0x1441c, the 8 turns of 0x143f8-0x14418 unrolled), sx_arm_scrib (0x14420-0x14474,
     one case per length 1..8, memcpy_holds at 0x14460 on the text's cells cut out of the event).
   - The UBSan check sites of the segment, each a branch to the unimp at 0x14478, are not taken because the payload
     s = body + msg.sysex lies in the body with its n bytes (msg_next_one: 1 <= sysex, sysex + n < len) and
     body + len <= 2^64, and ev + 80 <= 2^64: 0x140c0 (s NULL), 0x140d4 / 0x140e4 / 0x140ec (s + 1, s + 3, s + 2),
     0x1415c / 0x14194 (ring, n = 6), 0x1432c (leds, n = 5), 0x14380 (meter, n = 6), 0x143c8 / 0x143f8 (counter,
     n = 13), 0x143fc (ev + 0x1d + 8), 0x1444c (scribble), 0x14468 (ev + 20 + len).
   - Not reached from DN_DECODE when the status is 0xf0: the note and control-change code, which the other
     segments walk; DN_RET's epilogue is the entry part's. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step
  Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout FrameBytes
  diginet_decoder_next_c diginet_decoder_next_seg diginet_meter_segments_c diginet_meter_segments memcpy_c memcpy.
Import ListNotations.
Open Scope Z_scope.

(* ---- reading the body ---- *)

Lemma sx_rd : forall m body bb j, bytes_at rsegs m body bb -> 0 <= j < Z.of_nat (length bb) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (body + j)) 1 = Some [nth (Z.to_nat j) bb (Z_to_bv 8 0)].
Proof.
  intros m body bb j H Hj. pose proof (rd1 m body bb (Z.to_nat j) H ltac:(lia)) as R.
  rewrite Z2Nat.id in R by lia. exact R.
Qed.

(* the byte the binary loads is the model's byte_at *)
Lemma sx_bat : forall (bb : list byte) j, bv_unsigned (nth (Z.to_nat j) bb (Z_to_bv 8 0)) = byte_at (map bv_unsigned bb) j.
Proof.
  intros bb j. unfold byte_at. change 0 with (bv_unsigned (Z_to_bv 8 0)) at 2. rewrite map_nth. reflexivity.
Qed.

Lemma sx_b8_unsigned : forall x : byte, b8 (bv_unsigned x) = x.
Proof.
  intros x. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma sx_b8_bat : forall (bb : list byte) j, b8 (byte_at (map bv_unsigned bb) j) = nth (Z.to_nat j) bb (Z_to_bv 8 0).
Proof. intros bb j. rewrite <- sx_bat. apply sx_b8_unsigned. Qed.

Lemma sx_zxb_bat : forall (bb : list byte) j,
  bv_unsigned (Z_to_bv 64 (bv_unsigned (nth (Z.to_nat j) bb (Z_to_bv 8 0)))) = byte_at (map bv_unsigned bb) j.
Proof. intros bb j. rewrite zxb_u. apply sx_bat. Qed.

(* ---- the kit, as this segment uses it ---- *)

(* an sb of a computed value: the kit's store step leaves le1 v; as one byte the cell layer takes it *)
Lemma sx_le1 : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

Local Ltac sx_fix_sb :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb _))) _) => rewrite le1_zxb; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 _)) _) => rewrite sx_le1; mem_after_store
  | _ => idtac
  end.
Local Ltac sx_st := step; sx_fix_sb.

(* the concrete register tree back as mkR, so that a lemma about mkR applies syntactically *)
Local Ltac sx_fold_mkR :=
  lazymatch goal with
  | |- evt ?s ?Q (MS (TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
       (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
       (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) ?F ?pc ?fc ?rv ?m ?ro) =>
    change (evt s Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro))
  | _ => idtac
  end.

(* the event's cells after the stores, as event_cells of the model's event *)
Local Ltac sx_ev_close :=
  unfold event_cells, dmsg_cells, arr_cells;
  cbn [map seq app nth de_kind de_strip de_button de_zone de_on de_right de_addr de_lsb_missing de_value de_delta
       de_mask de_segments de_len de_text de_seg de_dots de_device de_msg
       de_set_kind de_set_strip de_set_button de_set_zone de_set_on de_set_right de_set_addr de_set_lsb_missing
       de_set_value de_set_delta de_set_mask de_set_segments de_set_len de_set_text de_set_seg de_set_dots
       de_set_device de_set_msg];
  fold_closed_in_goal;
  rewrite ?sx_b8_bat; rewrite <- ?sx_bat;
  eassumption.

(* ---- the values the binary stores, as the model computes them ---- *)

(* a fact about one byte, checked on its 256 values *)
Lemma sx_enum : forall P : Z -> bool, forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall z, 0 <= z < 256 -> P z = true.
Proof.
  intros P H z Hz. rewrite forallb_forall in H. apply H.
  replace z with (Z.of_nat (Z.to_nat z)) by lia. apply in_map. apply in_seq. lia.
Qed.

Local Ltac sx_enum_tac :=
  let z := fresh "z" in let Rz := fresh "Rz" in
  intros z Rz; apply bv_eq; apply Z.eqb_eq; revert z Rz;
  match goal with |- forall z, _ -> @?P z = true => apply (sx_enum P); vm_compute; reflexivity end.

Local Ltac sx_byte_fact x := unfold zxb, b8; generalize (byte_range x); generalize (bv_unsigned x); sx_enum_tac.

(* 0x1435c andi 0x1f, 0x14360 sb: the meter's strip *)
Lemma sx_v_m_strip : forall x : byte,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (zxb x)) 31))) = b8 (u8 (Z.land (bv_unsigned x) 0x1f)).
Proof. intros x. sx_byte_fact x. Qed.

(* 0x14370 slli 58, 0x14374 srli 63, 0x1437c sb: bit 5, the meter's right *)
Lemma sx_v_m_right : forall x : byte,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb x)) 58))) 63)))
  = b8 (u8 (int_of_bool (negb (Z.land (bv_unsigned x) 0x20 =? 0)))).
Proof. intros x. sx_byte_fact x. Qed.

(* an int stored as a byte is its int8_t *)
Lemma sx_v_s8 : forall v, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 v)) = b8 (s8 v).
Proof.
  intros v. apply bv_eq. unfold b8. rewrite !Z_to_bv_unsigned. unfold bv_wrap, s8, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2 ^ 64). Z.div_mod_to_equations. lia.
Qed.

Lemma sx_lor_low : forall a b k, 0 <= k -> 0 <= b < 2 ^ k -> Z.lor (Z.shiftl a k) b = Z.shiftl a k + b.
Proof.
  intros a b k Hk Hb.
  assert (L : Z.land (Z.shiftl a k) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
    destruct (Z.ltb_spec i k) as [Lt|Ge].
    - rewrite (Z.testbit_neg_r a (i - k)) by lia. reflexivity.
    - rewrite <- (Z.mod_small b (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

Lemma sx_land127 : forall z, Z.land z 127 = z mod 128.
Proof. intros z. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. Qed.

(* 0x1438c-0x14398: (pl[1] & 0x7f) << 7 | (pl[2] & 0x7f), the meter's mask, below 2^14 *)
Lemma sx_v_m_mask : forall x1 x2 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (zxb x1)) 127))) 7)))
                    (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (zxb x2)) 127))))
  = Z_to_bv 64 (u16 (Z.lor (Z.shiftl (Z.land (bv_unsigned x1) 0x7f) 7) (Z.land (bv_unsigned x2) 0x7f))) /\
  0 <= u16 (Z.lor (Z.shiftl (Z.land (bv_unsigned x1) 0x7f) 7) (Z.land (bv_unsigned x2) 0x7f)) < 2 ^ 14.
Proof.
  intros x1 x2. unfold zxb. pose proof (byte_range x1). pose proof (byte_range x2).
  rewrite !zxb_u, !sx_land127.
  pose proof (Z.mod_pos_bound (bv_unsigned x1) 128 ltac:(lia)).
  pose proof (Z.mod_pos_bound (bv_unsigned x2) 128 ltac:(lia)).
  rewrite !(unsigned_lit (_ mod 128)) by lia.
  rewrite (unsigned_lit (Z.shiftl _ 7)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite sx_lor_low by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 7) with 128.
  unfold u16. rewrite (Z.mod_small _ 65536) by lia. split; [reflexivity | lia].
Qed.

(* ---- the model's decode_sysex, arm by arm ---- *)

Definition sx_ring (b : list Z) (s n : Z) (ev : dgn_event) : dgn_event :=
  let pl := s + 3 in
  let pn := n - 3 in
  if negb (pn =? 3) then ev
  else
    let p0 := byte_at b pl in
    let ev := de_set_kind DIGINET_EV_RING ev in
    let ev := de_set_strip (u8 (Z.land p0 0x3f)) ev in
    let mask := u16 (if negb (Z.land p0 0x40 =? 0) then 1 else 0) in
    de_set_mask (ring_loop mask (byte_at b (pl + 1)) (byte_at b (pl + 2)) 0 7) ev.

Definition sx_meter (b : list Z) (s n : Z) (ev : dgn_event) : dgn_event :=
  let pl := s + 3 in
  let pn := n - 3 in
  if negb (pn =? 3) then ev
  else
    let p0 := byte_at b pl in
    let ev := de_set_kind DIGINET_EV_METER ev in
    let ev := de_set_addr p0 ev in
    let ev := de_set_strip (u8 (Z.land p0 0x1f)) ev in
    let ev := de_set_right (u8 (int_of_bool (negb (Z.land p0 0x20 =? 0)))) ev in
    let mask := u16 (Z.lor (Z.shiftl (Z.land (byte_at b (pl + 1)) 0x7f) 7)
                           (Z.land (byte_at b (pl + 2)) 0x7f)) in
    let ev := de_set_mask mask ev in
    de_set_segments (s8 (diginet_meter_segments mask)) ev.

Definition sx_leds (b : list Z) (s n : Z) (ev : dgn_event) : dgn_event :=
  let pl := s + 3 in
  let pn := n - 3 in
  if negb (pn =? 2) then ev
  else
    let ev := de_set_kind DIGINET_EV_STRIP_LEDS ev in
    let ev := de_set_addr (byte_at b pl) ev in
    let ev := de_set_strip (byte_at b pl) ev in
    de_set_mask (byte_at b (pl + 1)) ev.

Definition sx_scrib (b : list Z) (s n : Z) (ev : dgn_event) : dgn_event :=
  let pl := s + 3 in
  let pn := n - 3 in
  if (pn <? 3) || (DIGINET_SCRIBBLE_MAX <? pn - 2) then ev
  else
    let ev := de_set_kind DIGINET_EV_SCRIBBLE ev in
    let ev := de_set_addr (byte_at b pl) ev in
    let len := u8 (pn - 2) in
    let ev := de_set_len len ev in
    let text := copy_text (de_text ev) b (pl + 2) 0 (Z.to_nat len) in
    de_set_text (list_set text (Z.to_nat len) 0) ev.

Definition sx_counter (b : list Z) (s n : Z) (ev : dgn_event) : dgn_event :=
  let pl := s + 3 in
  let pn := n - 3 in
  if negb (pn =? 2 + DIGINET_COUNTER_DIGITS) then ev
  else
    let ev := de_set_kind DIGINET_EV_COUNTER ev in
    let ev := de_set_addr (byte_at b pl) ev in
    let ev := de_set_dots (byte_at b (pl + 1)) ev in
    de_set_seg (counter_loop (de_seg ev) b pl 0 8) ev.

Lemma sx_decode_split : forall b m ev,
  decode_sysex b m ev =
  let s := dm_sysex m in
  let n := dm_sysex_len m in
  let ev := de_set_kind DIGINET_EV_OTHER ev in
  if (n <? 3) || negb (byte_at b s =? DIGINET_SYSEX_MAKER) then ev
  else
    let ev := de_set_device (byte_at b (s + 1)) ev in
    let fn := byte_at b (s + 2) in
    if fn =? DIGINET_FN_RING then sx_ring b s n ev
    else if fn =? DIGINET_FN_METER then sx_meter b s n ev
    else if fn =? DIGINET_FN_LEDS then sx_leds b s n ev
    else if fn =? DIGINET_FN_SCRIBBLE then sx_scrib b s n ev
    else if fn =? DIGINET_FN_COUNTER then sx_counter b s n ev
    else if fn =? DIGINET_FN_SYSTEM then de_set_kind DIGINET_EV_SYSTEM ev
    else ev.
Proof. reflexivity. Qed.

(* ---- the dispatch on s[2] (0x140f4-0x14104): (fn >> 4) | (fn << 28 as a 32-bit int) is at most 7 exactly when
   fn's low nibble is 0 and fn < 0x80, and then it is fn / 16 ---- *)

Definition sx_fnx (z : Z) : word :=
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl z 28))))
                    (bv_unsigned (Z_to_bv 64 (Z.shiftr z 4)))).

Definition sx_fn_ok (z : Z) : bool :=
  let x := bv_unsigned (sx_fnx z) in
  if x <=? 7 then (x =? z / 16) && (z mod 16 =? 0) && (z <? 128)
  else negb ((z mod 16 =? 0) && (z <? 128)).

Lemma sx_fn_ok_all : forallb sx_fn_ok (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sx_fn_ok_z : forall z, 0 <= z < 256 -> sx_fn_ok z = true.
Proof.
  intros z Hz. pose proof sx_fn_ok_all as A. rewrite forallb_forall in A. apply A.
  replace z with (Z.of_nat (Z.to_nat z)) by lia. apply in_map. apply in_seq. lia.
Qed.

Lemma sx_fn_dec : forall z, 0 <= z < 256 ->
  (bv_ltu (Z_to_bv 64 7) (sx_fnx z) = false -> sx_fnx z = Z_to_bv 64 (z / 16) /\ z = 16 * (z / 16) /\ 0 <= z / 16 <= 7)
  /\ (bv_ltu (Z_to_bv 64 7) (sx_fnx z) = true -> ~ (z mod 16 = 0 /\ z < 128)).
Proof.
  intros z Hz. pose proof (sx_fn_ok_z z Hz) as OK. unfold sx_fn_ok in OK. cbv zeta in OK.
  unfold bv_ltu. change (bv_unsigned (Z_to_bv 64 7)) with 7.
  pose proof (bv_unsigned_in_range 64 (sx_fnx z)) as R.
  destruct (Z.leb_spec (bv_unsigned (sx_fnx z)) 7) as [L|L].
  - apply andb_true_iff in OK as [OK O3]. apply andb_true_iff in OK as [O1 O2].
    apply Z.eqb_eq in O1. apply Z.eqb_eq in O2. apply Z.ltb_lt in O3.
    split; intros H; [|apply Z.ltb_lt in H; lia].
    split; [|split; [Z.div_mod_to_equations; lia | split; [apply Z.div_pos; lia | lia]]].
    apply bv_eq. rewrite O1. rewrite unsigned_lit; [reflexivity|]. split; [apply Z.div_pos; lia|].
    apply Z.lt_le_trans with 256; [apply Z.div_lt_upper_bound; lia | lia].
  - apply negb_true_iff, andb_false_iff in OK.
    split; intros H; [apply Z.ltb_ge in H; lia|].
    intros [H1 H2]. destruct OK as [OK|OK]; [apply Z.eqb_neq in OK | apply Z.ltb_ge in OK]; lia.
Qed.

(* ---- what a path of the segment hands on at DN_RET: the event's 80 bytes are the model's event E and memory changed
   only there ---- *)
Definition sx_k (Q : machine_state -> Prop) (spf : Z) (gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (ev body : Z) (mpad : list byte)
    (E : dgn_event) : Prop :=
  forall (ra s0 s2 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (m' : word -> option byte),
    munch [(ev, ev + 80)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' ->
    rw_cells rsegs m' ev (event_cells body mpad E) ->
    evt rsegs Q
      (MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 t2 s0 (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DN_RET) fc None m' (seg_rom rsegs)).

Lemma sx_counter_loop : forall b pl l, length l = 8%nat ->
  counter_loop l b pl 0 8 =
  [byte_at b (pl + 2 + 7); byte_at b (pl + 2 + 6); byte_at b (pl + 2 + 5); byte_at b (pl + 2 + 4);
   byte_at b (pl + 2 + 3); byte_at b (pl + 2 + 2); byte_at b (pl + 2 + 1); byte_at b (pl + 2 + 0)].
Proof.
  intros b pl l H. do 8 (destruct l as [|? l]; [discriminate|]). destruct l; [|discriminate]. reflexivity.
Qed.

(* 0x143e0-0x143f0: (pl < -2 ? -1 : 0) & (pl + 2), the counter's source pointer for the UBSan test *)
Lemma sx_v_cnt_ptr : forall p q, 0 <= p -> p + 2 < 2 ^ 64 -> q = p + 2 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_sltiu (Z_to_bv 64 p) (-2)))))
                     (bv_unsigned (Z_to_bv 64 q)))
  = Z_to_bv 64 q.
Proof.
  intros p q Hp Hq ->. unfold v_sltiu. rewrite (unsigned_lit p) by lia.
  replace (bv_wrap 64 (-2)) with (2 ^ 64 - 2) by (vm_compute; reflexivity).
  rewrite (proj2 (Z.ltb_lt p (2 ^ 64 - 2))) by lia.
  replace (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite (unsigned_lit (p + 2)) by lia. rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Local Ltac sx_if_f := let HC := fresh "HC" in
  if_cases HC; [zify_cond HC; exfalso; Z.div_mod_to_equations; lia | clear HC].

(* one turn of the counter's copy loop 0x143f8-0x14418, reading the payload byte at sx-offset j *)
Local Ltac sx_cnt_iter j :=
  step; sx_if_f; step; sx_if_f;
  lazymatch goal with HB : bytes_at rsegs _ ?body ?bb |- _ =>
    let HR := fresh "HR" in pose proof (sx_rd _ _ _ j HB ltac:(lia)) as HR; sx_st; clear HR
  end;
  sx_st; sx_st; sx_st; sx_st; sx_st; step; first [if_true | if_false].

(* sllw of a small constant by j < 32: the plain shift *)
Lemma sx_sll : forall c j, 0 <= c -> 0 <= j < 32 -> Z.shiftl c j < 2 ^ 31 ->
  bv_swrap 32 (Z.shiftl c (j mod 32)) = Z.shiftl c j.
Proof.
  intros c j Hc Hj Hs. rewrite Z.mod_small by lia.
  pose proof (Z.shiftl_nonneg c j) as N.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma sx_shiftl1_pos : forall j, 0 <= j -> Z.shiftl 1 j = 2 ^ j.
Proof. intros j Hj. rewrite Z.shiftl_1_l. reflexivity. Qed.

(* beqz of byte & (1 << j): the model's test of bit j *)
Lemma sx_bit : forall j (x : byte), 0 <= j <= 7 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftl 1 j))) (bv_unsigned (zxb x)))) (Z_to_bv 64 0)
  = (Z.land (bv_unsigned x) (Z.shiftl 1 j) =? 0).
Proof.
  intros j x Hj. pose proof (byte_range x) as R. unfold bv_eqb, zxb. rewrite zxb_u.
  rewrite sx_shiftl1_pos by lia.
  assert (P : 1 <= 2 ^ j <= 128).
  { split; [apply (Z.pow_le_mono_r 2 0 j); lia | apply (Z.pow_le_mono_r 2 j 7); lia]. }
  rewrite (unsigned_lit (2 ^ j)) by lia.
  rewrite (unsigned_lit (Z.land (2 ^ j) (bv_unsigned x)))
    by (apply Z_land_range; lia).
  change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.land_comm. reflexivity.
Qed.

(* or of the ring's mask with a bit below 2^16 *)
Lemma sx_or : forall mask v, 0 <= mask < 2 ^ 16 -> 0 <= v < 2 ^ 16 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 mask)) (bv_unsigned (Z_to_bv 64 v))) = Z_to_bv 64 (u16 (Z.lor mask (u16 v)))
  /\ 0 <= u16 (Z.lor mask (u16 v)) < 2 ^ 16.
Proof.
  intros mask v Hm Hv. rewrite (unsigned_lit mask), (unsigned_lit v) by lia.
  pose proof (Z_lor_lt_pow2 mask v 16 Hm Hv) as L.
  unfold u16. rewrite (Z.mod_small v) by lia. rewrite (Z.mod_small (Z.lor mask v)) by lia. split; [reflexivity | lia].
Qed.

Lemma sx_ring_shifts : forall k, 0 <= k <= 6 ->
  0 <= Z.shiftl 1 (6 - k) < 2 ^ 7 /\ Z.shiftl 1 (6 - k) < 2 ^ 31 /\
  Z.shiftl 2 k = Z.shiftl 1 (1 + k) /\ Z.shiftl 2 k < 2 ^ 31 /\ 0 <= Z.shiftl 1 (1 + k) < 2 ^ 16 /\
  Z.shiftl 256 k = Z.shiftl 1 (8 + k) /\ Z.shiftl 256 k < 2 ^ 31 /\ 0 <= Z.shiftl 1 (8 + k) < 2 ^ 16.
Proof.
  intros k Hk.
  assert (P : forall j, 0 <= j <= 6 -> 1 <= 2 ^ j <= 64).
  { intros j Hj. split; [apply (Z.pow_le_mono_r 2 0 j); lia | apply (Z.pow_le_mono_r 2 j 6); lia]. }
  pose proof (P k Hk) as Pk. pose proof (P (6 - k) ltac:(lia)) as P6.
  rewrite !Z.shiftl_mul_pow2 by lia. rewrite !Z.pow_add_r by lia.
  change (2 ^ 1) with 2. change (2 ^ 8) with 256. change (2 ^ 7) with 128. change (2 ^ 16) with 65536.
  change (2 ^ 31) with 2147483648. lia.
Qed.

(* 0x14140 andi 0x3f, 0x14144 sb: the ring's strip *)
Lemma sx_v_r_strip : forall x : byte,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (zxb x)) 63))) = b8 (u8 (Z.land (bv_unsigned x) 0x3f)).
Proof. intros x. sx_byte_fact x. Qed.

(* 0x1414c slli 57, 0x14150 srli 63: bit 6, the ring's first mask *)
Lemma sx_v_r_mask0 : forall x : byte,
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb x)) 57))) 63)
  = Z_to_bv 64 (u16 (if negb (Z.land (bv_unsigned x) 0x40 =? 0) then 1 else 0)).
Proof. intros x. unfold zxb. generalize (byte_range x). generalize (bv_unsigned x). sx_enum_tac. Qed.

Lemma sx_bv_swrap_small : forall x, 0 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31). rewrite Z.mod_small by lia. lia.
Qed.

(* ---- the scribble's text: cutting the event around the memcpy's destination ---- *)

(* the n bytes of the body from index j *)
Definition sx_pick (bb : list byte) (j : Z) (n : nat) : list byte :=
  map (fun i => nth (Z.to_nat (j + Z.of_nat i)) bb (Z_to_bv 8 0)) (seq 0 n).

Lemma sx_bytes_pick : forall m body bb j n, bytes_at rsegs m body bb -> 0 <= j ->
  j + Z.of_nat n <= Z.of_nat (length bb) -> bytes_at rsegs m (body + j) (sx_pick bb j n).
Proof.
  intros m body bb j n (H0 & H1 & H2) Hj Hn. unfold bytes_at, sx_pick. rewrite length_map, length_seq.
  split; [lia|]. split; [lia|]. intros i Hi.
  assert (S : nth_error (seq 0 n) i = Some i).
  { rewrite (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; lia). rewrite seq_nth by lia. reflexivity. }
  erewrite map_nth_error by exact S.
  replace (body + j + Z.of_nat i) with (body + Z.of_nat (Z.to_nat (j + Z.of_nat i))) by lia.
  rewrite H2 by lia. apply nth_error_nth'. lia.
Qed.

(* split the rw_cells fact H after its k-th cell; the second part's address as A + its offset *)
Local Ltac sx_split H k H1 H2 :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let c1 := eval cbv [firstn] in (firstn k cs) in
    let c2 := eval cbv [skipn] in (skipn k cs) in
    change (rw_cells segs m A (c1 ++ c2)) in H;
    destruct (rw_cells_split m A c1 c2 H) as [H1 H2]; clear H;
    let z := eval vm_compute in (Z.of_nat (cells_size c1)) in
    change (Z.of_nat (cells_size c1)) with z in H2;
    lazymatch A with
    | Z.add ?X ?c => let v := eval vm_compute in (c + z) in replace (A + z) with (X + v) in H2 by lia
    | _ => idtac
    end
  end.

(* the cells of H as one byte block *)
Local Ltac sx_to_cb H :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let bs := eval cbv [cells_bytes cbytes app] in (cells_bytes cs) in
    let k := eval vm_compute in (cells_size cs) in
    apply (rw_cells_recast m A cs [CB k bs]) in H; [ | split; [reflexivity | exact I] | reflexivity | reflexivity ]
  end.

(* a byte block of picked body bytes as one-byte cells *)
Local Ltac sx_from_cb H :=
  lazymatch type of H with rw_cells ?segs ?m ?A [CB ?k ?bs] =>
    let bs' := eval cbv [sx_pick map seq Z.of_nat Pos.of_succ_nat Pos.succ] in bs in
    let cs := eval cbv [map] in (map C1 bs') in
    apply (rw_cells_recast m A [CB k bs] cs) in H; [ | cbn; repeat split | reflexivity | reflexivity ]
  end.

Local Ltac sx_join H1 H2 H :=
  lazymatch type of H1 with rw_cells ?segs ?m ?A ?c1 =>
  lazymatch type of H2 with rw_cells _ m ?A2 ?c2 =>
    assert (H : rw_cells segs m A (c1 ++ c2));
    [ apply rw_cells_join; [exact H1 | replace (A + Z.of_nat (cells_size c1)) with A2 by (simpl_sizes; lia); exact H2]
    | clear H1 H2; cbn [app] in H ]
  end end.

(* the closed Z.to_nat terms of the goal as nat literals *)
Local Ltac sx_ztn :=
  repeat match goal with |- context [Z.to_nat ?z] =>
    let v := eval vm_compute in (Z.to_nat z) in
    lazymatch v with O => idtac | S _ => idtac end;
    progress change (Z.to_nat z) with v
  end.

Local Ltac sx_finish K := sx_fold_mkR; eapply K; [eassumption | eassumption | eassumption | sx_ev_close].

Section Sysex.
Variables (gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (Q : machine_state -> Prop) (spf ev body : Z) (bb mpad : list byte) (m0 : word -> option byte) (sx n : Z).

Local Abbreviation BB := (map bv_unsigned bb).
Local Abbreviation KK E := (sx_k Q spf gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 ev body mpad E).
Local Abbreviation ST pc ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m :=
  (MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 t2 s0 (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* what every arm knows of the body and the payload s = body + sx of n bytes *)
Definition sx_env (m : word -> option byte) : Prop :=
  bytes_at rsegs m body bb /\ (ev + 80 <= body \/ body + Z.of_nat (length bb) <= ev) /\
  1 <= sx /\ 3 <= n /\ sx + n < Z.of_nat (length bb).

Lemma sx_ring_loop : forall f k mask (ra t2 t3 a4 a5 t4 t5 t6 : word) (m : word -> option byte) (E : dgn_event),
  n = 6 -> k + Z.of_nat f = 7 -> 0 <= k < 7 -> 0 <= mask < 2 ^ 16 ->
  bv_unsigned a4 = k -> bv_unsigned a5 = 6 - k ->
  sx_env m -> munch [(ev, ev + 80)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m ev (event_cells body mpad (de_set_mask mask E)) ->
  KK (de_set_mask (ring_loop mask (byte_at BB (sx + 4)) (byte_at BB (sx + 5)) k f) E) ->
  evt rsegs Q (ST 0x14178 ra (Z_to_bv 64 256) (Z_to_bv 64 2) t2 (Z_to_bv 64 ev) (Z_to_bv 64 (body + sx + 3))
                 (Z_to_bv 64 (body + sx)) (Z_to_bv 64 7) (Z_to_bv 64 mask) a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 (-3))
                 (Z_to_bv 64 n) t3 t4 t5 t6 m).
Proof.
  intros f; induction f as [|f IH];
    intros k mask ra t2 t3 a4 a5 t4 t5 t6 m E Hn6 Hf Hk HM Ha4 Ha5 (HB & HBE & Hs1 & Hn3 & Hsn) MU WM MI HE K;
    [lia|].
  cbn [ring_loop] in K.
  unfold event_cells, dmsg_cells, arr_cells in HE.
  cbn [map seq app de_kind de_strip de_button de_zone de_on de_right de_addr de_lsb_missing de_value de_delta
       de_mask de_segments de_len de_text de_seg de_dots de_device de_msg de_set_mask] in HE.
  pose proof (bytes_at_bound _ _ _ _ HB) as HBB.
  pose proof (rw_cells_bound _ _ _ _ HE) as HEB. cbn in HEB.
  destruct (sx_ring_shifts k ltac:(lia)) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  (* 0x141b0-0x141b8: k + 1, and the loop test *)
  assert (H3 : forall mask2 (m2 : word -> option byte) (t2' t3' a3' : word),
     0 <= mask2 < 2 ^ 16 -> a3' = Z_to_bv 64 mask2 ->
     sx_env m2 -> munch [(ev, ev + 80)] m0 m2 -> wmono rsegs m0 m2 -> mem_inv rsegs m2 ->
     rw_cells rsegs m2 ev (event_cells body mpad (de_set_mask mask2 E)) ->
     KK (de_set_mask (ring_loop mask2 (byte_at BB (sx + 4)) (byte_at BB (sx + 5)) (k + 1) f) E) ->
     evt rsegs Q (ST 0x141b0 ra (Z_to_bv 64 256) (Z_to_bv 64 2) t2' (Z_to_bv 64 ev) (Z_to_bv 64 (body + sx + 3))
                    (Z_to_bv 64 (body + sx)) (Z_to_bv 64 7) a3' a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 (-3))
                    (Z_to_bv 64 n) t3' t4 t5 t6 m2)).
  { intros mask2 m2 t2' t3' a3' HM2 -> HEnv2 MU2 WM2 MI2 HE2 K2.
    sx_st. rewrite Ha4, (sx_bv_swrap_small (k + 1)) by lia.
    sx_st. rewrite Ha5.
    sx_st.
    if_cases HC; zify_cond HC.
    - sx_fold_mkR. eapply (IH (k + 1) mask2); [exact Hn6 | lia | lia | exact HM2 | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; lia | exact HEnv2 | exact MU2 | exact WM2 | exact MI2 | exact HE2 | exact K2].
    - assert (f = O) by lia. subst f. cbn [ring_loop] in K2.
      sx_st. sx_st. sx_finish K2. }
  (* 0x14194-0x141ac: pl + 2 checked, bit 6 - k of pl[2] *)
  assert (H2 : forall mask1 (m1 : word -> option byte) (t3' a3' : word),
     0 <= mask1 < 2 ^ 16 -> a3' = Z_to_bv 64 mask1 ->
     sx_env m1 -> munch [(ev, ev + 80)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
     rw_cells rsegs m1 ev (event_cells body mpad (de_set_mask mask1 E)) ->
     KK (de_set_mask (ring_loop (if negb (Z.land (byte_at BB (sx + 5)) (Z.shiftl 1 (6 - k)) =? 0)
                                 then u16 (Z.lor mask1 (u16 (Z.shiftl 1 (8 + k)))) else mask1)
                                (byte_at BB (sx + 4)) (byte_at BB (sx + 5)) (k + 1) f) E) ->
     evt rsegs Q (ST 0x14194 ra (Z_to_bv 64 256) (Z_to_bv 64 2) (Z_to_bv 64 (Z.shiftl 1 (6 - k))) (Z_to_bv 64 ev)
                    (Z_to_bv 64 (body + sx + 3)) (Z_to_bv 64 (body + sx)) (Z_to_bv 64 7) a3' a4 a5 (Z_to_bv 64 1)
                    (Z_to_bv 64 (-3)) (Z_to_bv 64 n) t3' t4 t5 t6 m1)).
  { intros mask1 m1 t3' a3' HM1 -> (HB1 & HBE1 & _ & _ & _) MU1 WM1 MI1 HE1 K1.
    pose proof (bytes_at_bound _ _ _ _ HB1) as HBB1.
    pose proof (rw_cells_bound _ _ _ _ HE1) as HEB1. cbn in HEB1.
    unfold event_cells, dmsg_cells, arr_cells in HE1.
    cbn [map seq app de_kind de_strip de_button de_zone de_on de_right de_addr de_lsb_missing de_value de_delta
         de_mask de_segments de_len de_text de_seg de_dots de_device de_msg de_set_mask] in HE1.
    sx_st. sx_if_f.
    pose proof (sx_rd _ _ _ (sx + 5) HB1 ltac:(lia)) as HR.
    sx_st. clear HR. sx_st. sx_st.
    if_cases HT; rewrite sx_bit, sx_bat in HT by lia; rewrite HT in K1; cbn [negb] in K1.
    - eapply H3; [exact HM1 | reflexivity | split; [exact HB1 | split; [exact HBE1 | lia]] | exact MU1 | exact WM1
        | exact MI1 | sx_ev_close | exact K1].
    - sx_st. rewrite Ha4, (sx_sll 256 k), S6 by lia.
      sx_st. destruct (sx_or mask1 (Z.shiftl 1 (8 + k)) HM1 S8) as [VO RO]. rewrite VO. clear VO.
      sx_st.
      eapply H3; [exact RO | reflexivity | split; [exact HB1 | split; [exact HBE1 | lia]] | exact MU1 | exact WM1
        | exact MI1 | sx_ev_close | exact K1]. }
  (* 0x14178-0x14190: bit 6 - k of pl[1] *)
  pose proof (sx_rd _ _ _ (sx + 4) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. rewrite Ha5, (sx_sll 1 (6 - k)) by lia.
  sx_st. sx_st.
  if_cases HT; rewrite sx_bit, sx_bat in HT by lia; rewrite HT in K; cbn [negb] in K.
  - eapply H2; [exact HM | reflexivity | split; [exact HB | split; [exact HBE | lia]] | exact MU | exact WM
      | exact MI | sx_ev_close | exact K].
  - sx_st. rewrite Ha4, (sx_sll 2 k), S3 by lia.
    sx_st. destruct (sx_or mask (Z.shiftl 1 (1 + k)) HM S5) as [VO RO]. rewrite VO. clear VO.
    sx_st.
    eapply H2; [exact RO | reflexivity | split; [exact HB | split; [exact HBE | lia]] | exact MU | exact WM
      | exact MI | sx_ev_close | exact K].
Qed.

Lemma sx_arm_ring : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (E : dgn_event),
  a0 = Z_to_bv 64 (body + sx + 3) -> a1 = Z_to_bv 64 (body + sx) -> a2 = Z_to_bv 64 (n - 3) ->
  sx_env m -> munch [(ev, ev + 80)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m ev (event_cells body mpad E) ->
  KK (sx_ring BB sx n E) ->
  evt rsegs Q (ST 0x1412c ra t0 t1 t2 (Z_to_bv 64 ev) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 n) t3 t4 t5 t6 m).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m E -> -> -> (HB & HBE & Hs1 & Hn3 & Hsn) MU WM MI HE K.
  unfold sx_ring in K. cbv zeta in K.
  unfold event_cells, dmsg_cells, arr_cells in HE. cbn [map seq app] in HE.
  pose proof (bytes_at_bound _ _ _ _ HB) as HBB.
  pose proof (rw_cells_bound _ _ _ _ HE) as HEB. cbn in HEB.
  sx_st. sx_st.
  if_cases HC.
  { zify_cond HC.
    rewrite (proj2 (Z.eqb_neq (n - 3) 3)) in K by (Z.div_mod_to_equations; lia). cbn [negb] in K.
    sx_finish K. }
  zify_cond HC. rewrite (proj2 (Z.eqb_eq (n - 3) 3)) in K by (Z.div_mod_to_equations; lia). cbn [negb] in K.
  sx_st. sx_st.
  pose proof (sx_rd _ _ _ (sx + 3) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. sx_st.
  pose proof (sx_rd _ _ _ (sx + 3) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. sx_st. rewrite sx_v_r_mask0.
  sx_st. sx_st.
  sx_st. sx_if_f.
  sx_st. sx_st. sx_st. sx_st. sx_st. sx_st.
  rewrite sx_v_r_strip in HE.
  replace (sx + 3 + 1) with (sx + 4) in K by lia. replace (sx + 3 + 2) with (sx + 5) in K by lia.
  rewrite <- (sx_bat bb (sx + 3)) in K.
  sx_fold_mkR.
  eapply (sx_ring_loop 7 0 (u16 (if negb (Z.land (bv_unsigned (nth (Z.to_nat (sx + 3)) bb (Z_to_bv 8 0))) 0x40 =? 0)
                               then 1 else 0)))
    with (E := de_set_strip (u8 (Z.land (bv_unsigned (nth (Z.to_nat (sx + 3)) bb (Z_to_bv 8 0))) 0x3f))
                 (de_set_kind DIGINET_EV_RING E));
    [lia | reflexivity | lia | unfold u16; apply Z.mod_pos_bound; lia | reflexivity | reflexivity
    | split; [exact HB | split; [exact HBE | lia]] | exact MU | exact WM | exact MI | sx_ev_close | exact K].
Qed.


Lemma sx_arm_meter : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (E : dgn_event),
  a0 = Z_to_bv 64 (body + sx + 3) -> a1 = Z_to_bv 64 (body + sx) -> a2 = Z_to_bv 64 (n - 3) ->
  sx_env m -> munch [(ev, ev + 80)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m ev (event_cells body mpad E) ->
  KK (sx_meter BB sx n E) ->
  evt rsegs Q (ST 0x14348 ra t0 t1 t2 (Z_to_bv 64 ev) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 n) t3 t4 t5 t6 m).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m E -> -> -> (HB & HBE & Hs1 & Hn3 & Hsn) MU WM MI HE K.
  unfold sx_meter in K. cbv zeta in K.
  unfold event_cells, dmsg_cells, arr_cells in HE. cbn [map seq app] in HE.
  pose proof (bytes_at_bound _ _ _ _ HB) as HBB.
  pose proof (rw_cells_bound _ _ _ _ HE) as HEB. cbn in HEB.
  sx_st. sx_st.
  if_cases HC.
  { zify_cond HC.
    rewrite (proj2 (Z.eqb_neq (n - 3) 3)) in K by (Z.div_mod_to_equations; lia). cbn [negb] in K.
    sx_finish K. }
  zify_cond HC. rewrite (proj2 (Z.eqb_eq (n - 3) 3)) in K by (Z.div_mod_to_equations; lia). cbn [negb] in K.
  sx_st. sx_st.
  pose proof (sx_rd _ _ _ (sx + 3) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. sx_st. sx_st.
  pose proof (sx_rd _ _ _ (sx + 3) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. sx_st. sx_st. sx_st. sx_st. sx_st.
  if_cases HC2.
  { zify_cond HC2. Z.div_mod_to_equations; lia. }
  pose proof (sx_rd _ _ _ (sx + 3 + 1) HB ltac:(lia)) as HR.
  sx_st. clear HR.
  pose proof (sx_rd _ _ _ (sx + 3 + 2) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. sx_st. sx_st. sx_st. sx_st.
  destruct (sx_v_m_mask (nth (Z.to_nat (sx + 4)) bb (Z_to_bv 8 0)) (nth (Z.to_nat (sx + 5)) bb (Z_to_bv 8 0)))
    as [VM RM].
  rewrite VM in HE |- *. clear VM.
  remember (u16 (Z.lor (Z.shiftl (Z.land (bv_unsigned (nth (Z.to_nat (sx + 4)) bb (Z_to_bv 8 0))) 0x7f) 7)
                       (Z.land (bv_unsigned (nth (Z.to_nat (sx + 5)) bb (Z_to_bv 8 0))) 0x7f))) as MK eqn:HMK.
  (* 0x143a0: diginet_meter_segments (mask) *)
  sx_st. sx_fold_mkR.
  eapply evt_cut; [eapply diginet_meter_segments_holds; rewrite unsigned_lit by lia; lia |].
  intros ms' (a1' & a2' & ->).
  rewrite (unsigned_lit MK) by lia.
  replace (ret_pc (Z_to_bv 64 0x143a4)) with (Z_to_bv 64 0x143a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  sx_st. sx_st.
  rewrite sx_v_m_strip, sx_v_m_right, sx_v_s8 in HE. subst MK.
  sx_finish K.
Qed.

Lemma sx_arm_leds : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (E : dgn_event),
  a0 = Z_to_bv 64 (body + sx + 3) -> a1 = Z_to_bv 64 (body + sx) -> a2 = Z_to_bv 64 (n - 3) ->
  sx_env m -> munch [(ev, ev + 80)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m ev (event_cells body mpad E) ->
  KK (sx_leds BB sx n E) ->
  evt rsegs Q (ST 0x1430c ra t0 t1 t2 (Z_to_bv 64 ev) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 n) t3 t4 t5 t6 m).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m E -> -> -> (HB & HBE & Hs1 & Hn3 & Hsn) MU WM MI HE K.
  unfold sx_leds in K. cbv zeta in K.
  unfold event_cells, dmsg_cells, arr_cells in HE. cbn [map seq app] in HE.
  pose proof (bytes_at_bound _ _ _ _ HB) as HBB.
  pose proof (rw_cells_bound _ _ _ _ HE) as HEB. cbn in HEB.
  sx_st. sx_st.
  if_cases HC.
  { zify_cond HC.
    rewrite (proj2 (Z.eqb_neq (n - 3) 2)) in K by (Z.div_mod_to_equations; lia). cbn [negb] in K.
    sx_finish K. }
  zify_cond HC. rewrite (proj2 (Z.eqb_eq (n - 3) 2)) in K by (Z.div_mod_to_equations; lia). cbn [negb] in K.
  sx_st. sx_st.
  pose proof (sx_rd _ _ _ (sx + 3) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. sx_st. sx_st. sx_st.
  if_cases HC2.
  { zify_cond HC2. Z.div_mod_to_equations; lia. }
  pose proof (sx_rd _ _ _ (sx + 3 + 1) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. sx_st.
  sx_finish K.
Qed.

Lemma sx_arm_counter : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (E : dgn_event),
  a0 = Z_to_bv 64 (body + sx + 3) -> a1 = Z_to_bv 64 (body + sx) -> a2 = Z_to_bv 64 (n - 3) ->
  sx_env m -> munch [(ev, ev + 80)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m ev (event_cells body mpad E) -> length (de_seg E) = 8%nat ->
  KK (sx_counter BB sx n E) ->
  evt rsegs Q (ST 0x143ac ra t0 t1 t2 (Z_to_bv 64 ev) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 n) t3 t4 t5 t6 m).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m E -> -> -> (HB & HBE & Hs1 & Hn3 & Hsn) MU WM MI HE LS K.
  unfold sx_counter in K. cbv zeta in K. unfold DIGINET_COUNTER_DIGITS in K.
  unfold event_cells, dmsg_cells, arr_cells in HE. cbn [map seq app] in HE.
  pose proof (bytes_at_bound _ _ _ _ HB) as HBB.
  pose proof (rw_cells_bound _ _ _ _ HE) as HEB. cbn in HEB.
  sx_st. sx_st.
  if_cases HC.
  { zify_cond HC.
    rewrite (proj2 (Z.eqb_neq (n - 3) (2 + 8))) in K by (Z.div_mod_to_equations; lia). cbn [negb] in K.
    sx_finish K. }
  zify_cond HC. rewrite (proj2 (Z.eqb_eq (n - 3) (2 + 8))) in K by (Z.div_mod_to_equations; lia). cbn [negb] in K.
  rewrite sx_counter_loop in K by exact LS.
  sx_st. sx_st.
  pose proof (sx_rd _ _ _ (sx + 3) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. sx_st. sx_st.
  sx_if_f.
  pose proof (sx_rd _ _ _ (sx + 4) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. sx_st. sx_st. sx_st. sx_st. sx_st. sx_st. sx_st. sx_st. sx_st.
  rewrite (sx_v_cnt_ptr (body + sx + 3) (body + sx + 5)) by lia.
  sx_cnt_iter (sx + 5). sx_cnt_iter (sx + 6). sx_cnt_iter (sx + 7). sx_cnt_iter (sx + 8).
  sx_cnt_iter (sx + 9). sx_cnt_iter (sx + 10). sx_cnt_iter (sx + 11). sx_cnt_iter (sx + 12).
  sx_st.
  sx_finish K.
Qed.


(* one length L = n - 5 of the scribble's text, 0x14434 to DN_RET *)
Local Ltac sx_scrib_case L K HB HE MI HTX :=
  let Ln := eval vm_compute in (Z.to_nat L) in
  lazymatch goal with
  | |- _ =>
    revert K;
    repeat match goal with |- context [u8 ?e] => let v := eval vm_compute in (u8 e) in change (u8 e) with v end;
    sx_ztn; cbn [copy_text]; sx_ztn; cbn [list_set];
    intro K;
    sx_st; sx_st;
    let HR := fresh "HR" in
    pose proof (sx_rd _ _ _ (sx + 3) HB ltac:(lia)) as HR;
    sx_st; clear HR; sx_st; sx_st; sx_st;
    sx_st; sx_if_f;
    sx_st; sx_st; sx_st; sx_st; sx_st;
    let HP := fresh "HP" in let HR1 := fresh "HR1" in let HT := fresh "HT" in let HR2 := fresh "HR2" in
    sx_split HE 14%nat HP HR1; sx_split HR1 Ln HT HR2; sx_to_cb HT;
    (* 0x14460: memcpy (ev->text, pl + 2, len) *)
    sx_fold_mkR;
    eapply evt_cut;
    [ eapply memcpy_holds with (src := sx_pick bb (sx + 5) Ln);
      [ rewrite unsigned_lit by lia; replace (body + sx + 5) with (body + (sx + 5)) by lia;
        apply sx_bytes_pick; [exact HB | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]
      | reflexivity
      | rewrite (unsigned_lit (ev + 20)) by lia; exact HT
      | rewrite !unsigned_lit by lia; lia
      | exact MI ]
    | ];
    let ms' := fresh "ms'" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIc" in
    let HCB := fresh "HCB" in let HBc := fresh "HBc" in
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?m' & -> & MUc & WMc & MIc & HCB & HBc);
    clear HBc; rewrite (unsigned_lit (ev + 20)) in MUc, HCB by lia;
    replace (bv_unsigned (Z_to_bv 64 L)) with L in MUc, HCB by (vm_compute; reflexivity);
    lazymatch type of MUc with munch _ ?mo ?mn =>
      transport_after_call rsegs mo mn MUc WMc; clear MUc WMc MI; try clear mo end;
    sx_from_cb HCB;
    replace (ret_pc (Z_to_bv 64 0x14464)) with (Z_to_bv 64 0x14464)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]);
    (* 0x14464-0x14474: the text's NUL *)
    sx_st; sx_st;
    let HC3 := fresh "HC3" in
    if_cases HC3; [zify_cond HC3; rewrite zb_lxor_ones in HC3 by lia; exfalso; lia | clear HC3];
    sx_st; sx_st; sx_st;
    let HJ1 := fresh "HJ1" in let HJ := fresh "HJ" in
    sx_join HCB HR2 HJ1; sx_join HP HJ1 HJ;
    try rewrite HTX in HJ; cbn [nth] in HJ;
    revert HJ; fold_closed_in_goal; intro HJ;
    sx_finish K
  end.


Lemma sx_arm_scrib : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (E : dgn_event),
  a0 = Z_to_bv 64 (body + sx + 3) -> a1 = Z_to_bv 64 (body + sx) -> a2 = Z_to_bv 64 (n - 3) ->
  sx_env m -> munch [(ev, ev + 80)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m ev (event_cells body mpad E) -> length (de_text E) = 9%nat ->
  KK (sx_scrib BB sx n E) ->
  evt rsegs Q (ST 0x14420 ra t0 t1 t2 (Z_to_bv 64 ev) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 n) t3 t4 t5 t6 m).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m E -> -> -> (HB & HBE & Hs1 & Hn3 & Hsn) MU WM MI HE LT K.
  unfold sx_scrib in K. cbv zeta in K. unfold DIGINET_SCRIBBLE_MAX in K.
  assert (TXE : exists x0 x1 x2 x3 x4 x5 x6 x7 x8, de_text E = [x0; x1; x2; x3; x4; x5; x6; x7; x8]).
  { destruct (de_text E) as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|x8 [|x9 l]]]]]]]]]]; try discriminate LT.
    do 9 eexists. reflexivity. }
  destruct TXE as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & HTX).
  cbn [de_text de_set_len de_set_addr de_set_kind] in K. rewrite HTX in K.
  unfold event_cells, dmsg_cells, arr_cells in HE. cbn [map seq app] in HE.
  pose proof (bytes_at_bound _ _ _ _ HB) as HBB.
  pose proof (rw_cells_bound _ _ _ _ HE) as HEB. cbn in HEB.
  sx_st. sx_st.
  if_cases HC.
  { zify_cond HC. rewrite (proj2 (Z.ltb_lt (n - 3) 3)) in K by lia. cbn [orb] in K. sx_finish K. }
  zify_cond HC. rewrite (proj2 (Z.ltb_ge (n - 3) 3)) in K by lia. cbn [orb] in K.
  sx_st. sx_st. sx_st.
  if_cases HC2.
  { zify_cond HC2. rewrite (proj2 (Z.ltb_lt 8 (n - 3 - 2))) in K by (Z.div_mod_to_equations; lia). cbn [orb] in K.
    sx_finish K. }
  zify_cond HC2. rewrite (proj2 (Z.ltb_ge 8 (n - 3 - 2))) in K by (Z.div_mod_to_equations; lia). cbn [orb] in K.
  assert (Hn : n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13)
    by (Z.div_mod_to_equations; lia).
  destruct Hn as [Hn|[Hn|[Hn|[Hn|[Hn|[Hn|[Hn|Hn]]]]]]]; rewrite Hn in *.
  - sx_scrib_case 1 K HB HE MI HTX.
  - sx_scrib_case 2 K HB HE MI HTX.
  - sx_scrib_case 3 K HB HE MI HTX.
  - sx_scrib_case 4 K HB HE MI HTX.
  - sx_scrib_case 5 K HB HE MI HTX.
  - sx_scrib_case 6 K HB HE MI HTX.
  - sx_scrib_case 7 K HB HE MI HTX.
  - sx_scrib_case 8 K HB HE MI HTX.
Qed.


(* 0x14054-0x14128: the kind OTHER, the sysex test, decode_sysex's head and the jump through the table *)
Lemma sx_head : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) (m : word -> option byte)
    (E : dgn_event) (msg : dgn_msg),
  dm_status msg = 0xf0 -> dm_sysex msg = sx -> dm_sysex_len msg = n ->
  1 <= sx -> 0 <= n -> sx + n < Z.of_nat (length bb) ->
  bytes_at rsegs m body bb -> (ev + 80 <= body \/ body + Z.of_nat (length bb) <= ev) ->
  rw_cells rsegs m ev (event_cells body mpad E) ->
  rw_cells rsegs m (spf + 72) (dmsg_cells body mpad msg) ->
  (ev + 80 <= spf + 72 \/ spf + 112 <= ev) ->
  munch [(ev, ev + 80)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  length (de_text E) = 9%nat -> length (de_seg E) = 8%nat ->
  KK (decode_sysex BB msg (de_set_kind DIGINET_EV_OTHER E)) ->
  evt rsegs Q (ST 0x14054 ra t0 t1 t2 (Z_to_bv 64 ev) a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m E msg Hst Hs Hn Hs1 Hn0 Hsn HB HBE HE HM HME MU WM MI
    LT LS K.
  rewrite sx_decode_split in K. cbv zeta in K. rewrite Hs, Hn in K.
  unfold DIGINET_SYSEX_MAKER, DIGINET_FN_RING, DIGINET_FN_METER, DIGINET_FN_LEDS, DIGINET_FN_SCRIBBLE,
    DIGINET_FN_COUNTER, DIGINET_FN_SYSTEM in K.
  unfold dmsg_cells, sysex_ptr in HM. rewrite Hst, Hs, Hn in HM.
  rewrite (proj2 (Z.eqb_neq sx 0)) in HM by lia. cbv beta iota in HM.
  unfold event_cells, dmsg_cells, arr_cells in HE. cbn [map seq app] in HE.
  pose proof (bytes_at_bound _ _ _ _ HB) as HBB.
  pose proof (rw_cells_bound _ _ _ _ HE) as HEB. cbn in HEB.
  step.
  replace (zxb (b8 240)) with (Z_to_bv 64 240) by (apply bv_eq; vm_compute; reflexivity).
  step. step. step. step. step.
  if_true.
  step. step. if_false.
  step. step. step. step.
  if_cases HN.
  { (* n < 3: kind OTHER (0x140b8 to DN_RET) *)
    zify_cond HN. rewrite (proj2 (Z.ltb_lt n 3) HN) in K. cbn [orb] in K.
    sx_finish K. }
  zify_cond HN. rewrite (proj2 (Z.ltb_ge n 3) HN) in K. cbn [orb] in K.
  step. step.
  if_cases H0.
  { zify_cond H0. lia. }
  pose proof (sx_rd _ _ _ sx HB ltac:(lia)) as HR.
  step. clear HR. step. step.
  if_cases H13.
  { (* s[0] != DIGINET_SYSEX_MAKER (0x140cc to 0x14298) *)
    zify_cond H13. rewrite sx_zxb_bat in H13.
    rewrite (proj2 (Z.eqb_neq _ _) H13) in K. cbn [negb] in K.
    sx_finish K. }
  zify_cond H13. rewrite sx_zxb_bat in H13.
  rewrite (proj2 (Z.eqb_eq _ _) H13) in K. cbn [negb] in K.
  step. step.
  if_cases H1.
  { zify_cond H1. lia. }
  pose proof (sx_rd _ _ _ (sx + 1) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. sx_st. sx_st.
  if_cases H4.
  { zify_cond H4. lia. }
  sx_st. sx_st.
  if_cases H3.
  { zify_cond H3. lia. }
  pose proof (sx_rd _ _ _ (sx + 2) HB ltac:(lia)) as HR.
  sx_st. clear HR. sx_st. sx_st. sx_st. sx_st. sx_st.
  assert (FR : 0 <= bv_unsigned (zxb (nth (Z.to_nat (sx + 2)) bb (Z_to_bv 8 0))) < 256)
    by (unfold zxb; rewrite zxb_u; apply byte_range).
  destruct (sx_fn_dec _ FR) as [D1 D2]. unfold sx_fnx in D1, D2.
  if_cases H7.
  { (* fn's low nibble is not 0, or fn >= 0x80: the default (0x14104 to DN_RET) *)
    specialize (D2 eq_refl). unfold zxb in D2. rewrite sx_zxb_bat in D2.
    revert K; decide_tests; intro K.
    sx_finish K. }
  destruct (D1 eq_refl) as (X0 & X1 & X2). rewrite X0. clear D1 D2 H7 X0.
  unfold zxb in X1, X2 |- *. rewrite sx_zxb_bat in X1, X2 |- *.
  remember (byte_at BB (sx + 2)) as fn eqn:Hfn.
  assert (I : fn / 16 = 0 \/ fn / 16 = 1 \/ fn / 16 = 2 \/ fn / 16 = 3 \/ fn / 16 = 4 \/ fn / 16 = 5 \/
              fn / 16 = 6 \/ fn / 16 = 7) by lia.
  pose (E1 := de_set_device (byte_at BB (sx + 1)) (de_set_kind DIGINET_EV_OTHER (de_set_kind DIGINET_EV_OTHER E))).
  destruct I as [I|[I|[I|[I|[I|[I|[I|I]]]]]]]; rewrite I in X1 |- *; rewrite X1 in K;
    revert K; decide_tests; intro K; do 9 step.
  - (* 0x00 ring *)
    sx_fold_mkR. eapply sx_arm_ring with (E := E1); [first [reflexivity | f_equal; lia] .. | | | | | | exact K].
    all: try eassumption.
    + unfold sx_env. split; [eassumption | split; [eassumption | lia]].
    + subst E1. sx_ev_close.
  - (* 0x10 meter *)
    sx_fold_mkR. eapply sx_arm_meter with (E := E1); [first [reflexivity | f_equal; lia] .. | | | | | | exact K].
    all: try eassumption.
    + unfold sx_env. split; [eassumption | split; [eassumption | lia]].
    + subst E1. sx_ev_close.
  - (* 0x20 leds *)
    sx_fold_mkR. eapply sx_arm_leds with (E := E1); [first [reflexivity | f_equal; lia] .. | | | | | | exact K].
    all: try eassumption.
    + unfold sx_env. split; [eassumption | split; [eassumption | lia]].
    + subst E1. sx_ev_close.
  - (* 0x30 counter *)
    sx_fold_mkR. eapply sx_arm_counter with (E := E1); [first [reflexivity | f_equal; lia] .. | | | | | | exact LS | exact K].
    all: try eassumption.
    + unfold sx_env. split; [eassumption | split; [eassumption | lia]].
    + subst E1. sx_ev_close.
  - (* 0x40 scribble *)
    sx_fold_mkR. eapply sx_arm_scrib with (E := E1); [first [reflexivity | f_equal; lia] .. | | | | | | exact LT | exact K].
    all: try eassumption.
    + unfold sx_env. split; [eassumption | split; [eassumption | lia]].
    + subst E1. sx_ev_close.
  - (* 0x50: the default *)
    sx_finish K.
  - (* 0x60: the default *)
    sx_finish K.
  - (* 0x70 system: kind SYSTEM (0x1433c-0x14344) *)
    sx_st. sx_st. sx_st. sx_finish K.
Qed.

End Sysex.

(* ---- the model under the path condition, and the segment's continuation from the cut's ---- *)

Lemma sx_model : forall bb dc msg c1,
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (1, msg, c1) -> dm_status msg = 0xf0 ->
  dn_e bb dc = decode_sysex (map bv_unsigned bb) msg (de_set_kind DIGINET_EV_OTHER (de_set_msg msg dgn_event_zero)) /\
  dn_d bb dc = {| dd_c := c1; dd_p := dd_p dc |}.
Proof.
  intros bb dc msg c1 H Hs. unfold dn_e, dn_d, dn_step, diginet_decoder_next. rewrite H. cbv beta iota zeta.
  rewrite Hs. split; reflexivity.
Qed.

Lemma sx_k_of_cont : forall Q spf gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d ev body bb cpad mpad dc,
  dn_seg_cont Q spf gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d ev body bb cpad mpad dc ->
  rw_cells rsegs m d (decoder_cells body cpad (dn_d bb dc)) ->
  (d + 40 <= ev \/ ev + 80 <= d) ->
  sx_k Q spf gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ev body mpad (dn_e bb dc).
Proof.
  intros Q spf gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d ev body bb cpad mpad dc K HD Hde.
  unfold sx_k. intros ra s0 s2 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m' MU WM MI HE.
  apply K; [ | exact WM | exact MI | exact HE | ].
  - eapply munch_weaken; [|exact MU]. unfold sub_fp. intros x. cbn [outside]. tauto.
  - eapply rw_cells_transport; [exact HD | exact MU | exact WM |].
    rewrite decoder_cells_size. cbn [disjoint_from]. lia.
Qed.

(* ---- the segment ---- *)

Lemma diginet_decoder_next_sysex_seg : forall (ra s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
    (spf d ev body : Z) (bb cpad mpad junk : list byte) (dc : dgn_decoder) (msg : dgn_msg) (c1 : dgn_cursor)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  dn_seg_pre m spf d ev body bb cpad mpad junk dc msg c1 ->
  dm_status msg = 0xf0 ->
  dn_seg_cont Q spf gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d ev body bb cpad mpad dc ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 t2 (Z_to_bv 64 ev) (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 DN_DECODE) fc None m (seg_rom rsegs)).
Proof.
  intros ra s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 gp tp F fc m Q spf d ev body bb cpad mpad junk dc msg c1
    t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hpre Hpath K.
  destruct Hpre as (Hmn & Hd0 & Hev0 & Hdal & Heval & Hspal & Hbody & Hlen & Hpos & Hst & Hbb & HD & HE & HM & HJ &
                    Hdev & Hdb & Heb & Hds & Hes & Hbs & HI).
  pose proof (msg_next_one bb (dd_c dc) dgn_msg_zero msg c1 Hlen (proj1 Hpos) Hst Hmn) as MF.
  destruct MF as (_ & _ & _ & Hsx & _ & _ & _ & _).
  destruct (Hsx Hpath) as (Hsx1 & Hsxl & Hsxe). rewrite Hlen in Hsxe.
  destruct (sx_model bb dc msg c1 Hmn Hpath) as [Me Md].
  pose proof (sx_k_of_cont Q spf gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d ev body bb cpad mpad dc K
                ltac:(rewrite Md; exact HD) Hdev) as K'.
  rewrite Me in K'.
  unfold DN_DECODE.
  eapply sx_head with (sx := dm_sysex msg) (n := dm_sysex_len msg) (m0 := m) (msg := msg) (bb := bb)
    (body := body) (mpad := mpad) (E := de_set_msg msg dgn_event_zero);
    [exact Hpath | reflexivity | reflexivity | lia | lia | lia
    | exact Hbb | exact Heb | exact HE | exact HM | lia | apply munch_refl | apply wmono_refl | exact HI
    | reflexivity | reflexivity | exact K'].
Qed.

