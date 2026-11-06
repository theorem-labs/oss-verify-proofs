From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
Import ListNotations.
Open Scope Z_scope.

(** The library's encoders (DgnLib.enc_of_call) agree with what the harness's owe() expects
    (codec_owe.owe_spec) on every call record the reader can make, for each of the 12 kinds run()
    calls: the codes are equal, and on success the library's command is the owed one. These are the
    facts behind check_refusal, check_range and check_bytes (fuzz_codec.c:272-345). *)

(** The personalities a call record can carry: NULL, Control|24, ProControl. *)
Definition od_ok (od : option desk) : Prop := od = None \/ od = Some c24 \/ od = Some pc.

(** check_range's code test (rc = want_rc) and check_bytes's comparison on success. *)
Definition agrees (kind : Z) (od : option desk) (a b c delta : Z) (bytes : list Z) (n : Z) : Prop :=
  let (rc, o) := enc_of_call kind od a b c delta bytes n in
  fst (owe_spec kind od a b c delta bytes n) = rc /\
  (rc = 0 -> o = Some (snd (owe_spec kind od a b c delta bytes n))).

(** ---- tactics ---- *)

Ltac bools :=
  repeat match goal with
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ || _) = true |- _ => apply orb_true_iff in H; destruct H
  | H : (_ || _) = false |- _ => apply orb_false_iff in H; destruct H
  | H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  end.

Ltac split_if :=
  match goal with |- context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E end.

Ltac red_consts := cbn [Z.eqb Z.ltb Z.leb Z.compare Pos.compare Pos.compare_cont Pos.eqb negb orb andb
                        d_dev d_strips d_chars d_counter c24 pc] in *.

Ltac crush_ifs := repeat (split_if; red_consts).

Ltac fin :=
  bools;
  first
    [ exfalso; lia
    | exfalso; congruence
    | split; [ reflexivity
             | let H := fresh "H" in
               intros H; first [ reflexivity | (cbv in H; discriminate H) | exfalso; lia ] ] ].

Ltac rdr H := destruct H as (Ha & Hb & Hc & Hdl & Hlen & Hby & Hn & H5 & H10 & H11).

Ltac len_tac :=
  rewrite ?length_app, ?length_rev; cbn [length];
  repeat match goal with
         | |- context [length (firstn ?k ?l)] =>
           let H := fresh "Hf" in
           pose proof (firstn_le_length k l) as H; revert H; generalize (length (firstn k l)); intros ? H
         end;
  lia.

(** ---- arithmetic and bit facts ---- *)

Lemma s32_eq0 : forall c, 0 <= c < 2 ^ 32 -> (s32 c =? 0) = (c =? 0).
Proof.
  intros c Hc. unfold s32. change (2 ^ 31) with 2147483648. change (2 ^ 32) with 4294967296 in *.
  destruct (c <? 2147483648) eqn:E; [reflexivity|].
  apply Z.ltb_ge in E. destruct (c =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|].
  apply Z.eqb_neq. lia.
Qed.

Lemma tb_small : forall x k, 0 <= k -> 0 <= x < 2 ^ k -> Z.testbit x k = false.
Proof.
  intros x k Hk Hx. replace k with (0 + k) by lia.
  rewrite <- Z.div_pow2_bits by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma tb7_small : forall x, 0 <= x < 128 -> Z.testbit x 7 = false.
Proof. intros x Hx. apply tb_small; [lia|]. change (2 ^ 7) with 128. lia. Qed.

Lemma tb7_u8 : forall x, Z.testbit (u8 x) 7 = Z.testbit x 7.
Proof. intros x. unfold u8. change 256 with (2 ^ 8). apply Z.mod_pow2_bits_low. lia. Qed.

Lemma tb7_bit : forall t v, 0 <= v < 128 -> Z.testbit (bit_or_0 t v) 7 = false.
Proof. intros [|] v Hv; cbn [bit_or_0]; [apply tb7_small; lia | reflexivity]. Qed.

Lemma tb7_byte : forall b, 0 <= b < 256 -> Z.testbit b 7 = (127 <? b).
Proof.
  intros b Hb. destruct (127 <? b) eqn:E.
  - apply Z.ltb_lt in E. replace 7 with (0 + 7) by lia.
    rewrite <- Z.div_pow2_bits by lia. change (2 ^ 7) with 128.
    replace (b / 128) with 1; [reflexivity|].
    apply Z.div_unique with (r := b - 128); lia.
  - apply Z.ltb_ge in E. apply tb7_small. lia.
Qed.

Lemma u8_small : forall x, 0 <= x < 256 -> u8 x = x.
Proof. intros x Hx. unfold u8. apply Z.mod_small. lia. Qed.

Lemma seven_bit_existsb : forall l, seven_bit l = negb (existsb (fun x => Z.testbit x 7) l).
Proof.
  unfold seven_bit. induction l as [|x l IH]; [reflexivity|]. cbn [forallb existsb].
  rewrite IH. destruct (Z.testbit x 7); reflexivity.
Qed.

Lemma existsb_rev : forall (f : Z -> bool) l, existsb f (rev l) = existsb f l.
Proof.
  intros f. induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite existsb_app, IH. simpl. rewrite orb_false_r, orb_comm. reflexivity.
Qed.

Lemma pow_m1 : forall b, 0 <= b <= 14 -> 0 <= 2 ^ b - 1 < 2 ^ 14.
Proof.
  intros b Hb. assert (0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ b <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma meter_mask_le14 : forall b, 0 <= b <= 14 -> meter_mask_spec b = 2 ^ b - 1.
Proof.
  intros b Hb. unfold meter_mask_spec. rewrite Z.min_l by lia.
  pose proof (pow_m1 b Hb). apply Z.mod_small. change (2 ^ 16) with 65536. change (2 ^ 14) with 16384 in H. lia.
Qed.

(** sysex_spec once the device, function and length checks pass. *)
Lemma sysex_pass : forall dev fn pl,
  0 <= dev <= 0x7f -> fn <> 0x70 -> 0 <= fn <= 0x7f -> Z.of_nat (length pl) + 5 <= 24 ->
  sysex_spec dev fn pl =
  if existsb (fun x => Z.testbit x 7) pl then (E_RANGE, None)
  else (0, Some ([0xf0; 0x13; dev; fn] ++ pl ++ [0xf7], 0, bit_or_0 ((fn =? 0x40) || (fn =? 0x30)) 1)).
Proof.
  intros dev fn pl Hd Hf Hf' Hl. unfold sysex_spec.
  replace (0x7f <? dev) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (fn =? 0x70) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (0x7f <? fn) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (24 <? Z.of_nat (length pl) + 5) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(** ---- the ring payload ---- *)

Lemma fold_left_ext_pt : forall {A B : Type} (f g : A -> B -> A) (l : list B) (a : A),
  (forall x y, f x y = g x y) -> fold_left f l a = fold_left g l a.
Proof.
  intros A B f g l. induction l as [|y l IH]; intros a H; cbn; [reflexivity|].
  rewrite H. apply IH. exact H.
Qed.

Lemma fold_left_inv : forall {A B : Type} (P : A -> Prop) (f : A -> B -> A) (l : list B) (a : A),
  P a -> (forall x y, In y l -> P x -> P (f x y)) -> P (fold_left f l a).
Proof.
  intros A B P f l. induction l as [|y l IH]; intros a Ha H; cbn; [exact Ha|].
  apply IH; [apply H; [left; reflexivity | exact Ha]|].
  intros x z Hz Hx. apply H; [right; exact Hz | exact Hx].
Qed.

Definition ring_step (mask : Z) (pr : Z * Z) (k : Z) : Z * Z :=
  (Z.lor (fst pr) (bit_or_0 (Z.testbit mask (1 + k)) (2 ^ (6 - k))),
   Z.lor (snd pr) (bit_or_0 (Z.testbit mask (8 + k)) (2 ^ (6 - k)))).

Definition owe_ring_step (b : Z) (pr : Z * Z) (led : Z) : Z * Z :=
  (if led <=? 8 then Z.lor (fst pr) (bit_or_0 (Z.testbit b (led - 1)) (2 ^ (8 - led))) else fst pr,
   if led <=? 8 then snd pr else Z.lor (snd pr) (bit_or_0 (Z.testbit b (led - 1)) (2 ^ (15 - led)))).

Lemma ring_bits_step : forall mask,
  ring_bits mask = fold_left (ring_step mask) (map Z.of_nat (seq 0 7)) (0, 0).
Proof. intros mask. unfold ring_bits. apply fold_left_ext_pt. intros [x y] k. reflexivity. Qed.

Lemma owe_ring_step_eq : forall b,
  owe_ring b = fold_left (owe_ring_step b) (map Z.of_nat (seq 2 14)) (0, 0).
Proof.
  intros b. unfold owe_ring. apply fold_left_ext_pt. intros [p1 p2] led. unfold owe_ring_step. cbn [fst snd].
  destruct (Z.testbit b (led - 1)), (led <=? 8); cbn; rewrite ?Z.lor_0_r; reflexivity.
Qed.

(** The library's loop and the harness's loop light the same bits of b1 and b2. *)
Lemma ring_bits_owe : forall b, ring_bits b = owe_ring b.
Proof. intros b. rewrite ring_bits_step, owe_ring_step_eq. reflexivity. Qed.

Lemma ring_bits_tb7 : forall b, Z.testbit (fst (ring_bits b)) 7 = false /\ Z.testbit (snd (ring_bits b)) 7 = false.
Proof.
  intros b. rewrite ring_bits_step.
  apply (fold_left_inv (fun pr => Z.testbit (fst pr) 7 = false /\ Z.testbit (snd pr) 7 = false)).
  - split; reflexivity.
  - intros [x y] k Hk [Hx Hy]. apply in_map_iff in Hk. destruct Hk as (k' & <- & Hk'). apply in_seq in Hk'.
    assert (0 <= 2 ^ (6 - Z.of_nat k') < 128).
    { split; [apply Z.pow_nonneg; lia|]. change 128 with (2 ^ 7). apply Z.pow_lt_mono_r; lia. }
    unfold ring_step; cbn [fst snd] in *. rewrite !Z.lor_spec, !tb7_bit by lia. rewrite Hx, Hy. split; reflexivity.
Qed.

(** ---- the per-kind lemmas ---- *)

Lemma agree_0 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 0 a b c delta bytes n -> agrees 0 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod _. unfold agrees, enc_of_call, owe_spec, fader_spec.
  destruct Hod as [-> | [-> | ->]]; red_consts; crush_ifs; fin.
Qed.

Lemma agree_1 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 1 a b c delta bytes n -> agrees 1 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod Hr. rdr Hr. unfold agrees, enc_of_call, owe_spec, button_spec.
  rewrite s32_eq0 by lia.
  destruct Hod as [-> | [-> | ->]]; red_consts; crush_ifs; fin.
Qed.

Lemma agree_2 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 2 a b c delta bytes n -> agrees 2 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod Hr. rdr Hr. unfold agrees, enc_of_call, owe_spec, touch_spec, button_spec.
  rewrite s32_eq0 by lia.
  destruct Hod as [-> | [-> | ->]]; red_consts; crush_ifs; fin.
Qed.

Lemma agree_3 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 3 a b c delta bytes n -> agrees 3 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod _. unfold agrees, enc_of_call, owe_spec, vpot_spec.
  destruct Hod as [-> | [-> | ->]]; red_consts; crush_ifs; fin.
Qed.

Lemma agree_4 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 4 a b c delta bytes n -> agrees 4 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod _. unfold agrees, enc_of_call, owe_spec, jog_spec.
  destruct Hod as [-> | [-> | ->]]; red_consts; crush_ifs; fin.
Qed.

Lemma ring_pl7 : forall a b, 0 <= a < 64 ->
  existsb (fun x => Z.testbit x 7) [u8 (Z.lor a (bit_or_0 (Z.testbit b 0) 0x40)); fst (owe_ring b); snd (owe_ring b)]
  = false.
Proof.
  intros a b Ha. rewrite <- ring_bits_owe. destruct (ring_bits_tb7 b) as [H1 H2].
  cbn [existsb]. rewrite H1, H2, tb7_u8, Z.lor_spec, (tb7_small a), tb7_bit by lia. reflexivity.
Qed.

Lemma agree_5 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 5 a b c delta bytes n -> agrees 5 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod Hr. rdr Hr. specialize (H5 eq_refl).
  unfold agrees, enc_of_call, owe_spec, ring_spec. rewrite (Z.mod_small b (2 ^ 16)) by lia.
  rewrite ring_bits_owe.
  destruct Hod as [-> | [-> | ->]]; red_consts; crush_ifs; try fin.
  all: bools; pose proof (ring_pl7 a b ltac:(lia)) as Hpl; destruct (owe_ring b) as [p1 p2]; cbn [fst snd] in Hpl.
  all: rewrite sysex_pass by first [lia | len_tac]; rewrite Hpl; fin.
Qed.

Lemma meter_pl7 : forall a t b, 0 <= a < 32 -> 0 <= b <= 14 ->
  existsb (fun x => Z.testbit x 7)
    [u8 (Z.lor a (bit_or_0 t 0x20)); u8 (Z.shiftr (2 ^ b - 1) 7); u8 (Z.land (2 ^ b - 1) 0x7f)] = false.
Proof.
  intros a t b Ha Hb. pose proof (pow_m1 b Hb) as Hm. cbn [existsb].
  rewrite !tb7_u8, Z.lor_spec, (tb7_small a), tb7_bit by lia.
  rewrite Z.shiftr_spec by lia. rewrite Z.land_spec. change (7 + 7) with 14.
  rewrite (tb_small (2 ^ b - 1) 14) by lia. replace (Z.testbit 0x7f 7) with false by reflexivity.
  rewrite andb_false_r. reflexivity.
Qed.

Lemma agree_6 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 6 a b c delta bytes n -> agrees 6 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod Hr. rdr Hr. unfold agrees, enc_of_call, owe_spec, meter_spec.
  rewrite s32_eq0 by lia.
  destruct Hod as [-> | [-> | ->]]; red_consts; crush_ifs; try fin.
  all: bools; rewrite meter_mask_le14 by lia; pose proof (pow_m1 b ltac:(lia)) as Hm;
       rewrite (Z.mod_small (2 ^ b - 1) (2 ^ 32)) by (change (2 ^ 32) with 4294967296;
                                                      change (2 ^ 14) with 16384 in Hm; lia).
  all: rewrite sysex_pass by first [lia | len_tac]; rewrite meter_pl7 by lia; fin.
Qed.

Lemma leds_pl7 : forall addr bits, 0 <= addr < 128 -> 0 <= bits < 128 ->
  existsb (fun x => Z.testbit x 7) [u8 addr; u8 bits] = false.
Proof.
  intros addr bits Ha Hb. cbn [existsb]. rewrite !tb7_u8, !tb7_small by lia. reflexivity.
Qed.

Lemma agree_7 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 7 a b c delta bytes n -> agrees 7 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod Hr. rdr Hr. unfold agrees, enc_of_call, owe_spec, strip_leds_spec, leds_spec.
  destruct Hod as [-> | [-> | ->]]; red_consts; [fin | |].
  all: crush_ifs; try fin.
  all: bools; rewrite sysex_pass by first [lia | len_tac]; rewrite leds_pl7 by lia; fin.
Qed.

Lemma agree_8 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 8 a b c delta bytes n -> agrees 8 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod Hr. rdr Hr. unfold agrees, enc_of_call, owe_spec, counter_leds_spec, leds_spec.
  destruct Hod as [-> | [-> | ->]]; red_consts; [fin | |].
  all: crush_ifs; try fin.
  all: bools; rewrite sysex_pass by first [lia | len_tac]; rewrite leds_pl7 by lia; fin.
Qed.

Lemma scribble_pl7 : forall a l, 0 <= a < 128 ->
  existsb (fun x => Z.testbit x 7) ([u8 a; 0] ++ l) = negb (seven_bit l).
Proof.
  intros a l Ha. rewrite seven_bit_existsb, negb_involutive. cbn [app existsb].
  rewrite tb7_u8, (tb7_small a) by lia. reflexivity.
Qed.

Lemma agree_9 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 9 a b c delta bytes n -> agrees 9 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod Hr. rdr Hr. unfold agrees, enc_of_call, owe_spec, scribble_spec.
  destruct Hod as [-> | [-> | ->]]; red_consts; crush_ifs; try fin.
  all: bools; rewrite sysex_pass by first [lia | len_tac]; rewrite scribble_pl7 by lia; crush_ifs; fin.
Qed.

Lemma counter_pl7 : forall ctr b l, 0 <= ctr < 128 -> 0 <= b < 256 ->
  existsb (fun x => Z.testbit x 7) ([ctr; b] ++ rev l) = (127 <? b) || negb (seven_bit l).
Proof.
  intros ctr b l Hc Hb. rewrite seven_bit_existsb, negb_involutive. cbn [app existsb].
  rewrite existsb_rev, (tb7_small ctr), (tb7_byte b) by lia. reflexivity.
Qed.

Lemma agree_10 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 10 a b c delta bytes n -> agrees 10 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod Hr. rdr Hr. specialize (H10 eq_refl).
  unfold agrees, enc_of_call, owe_spec, counter_spec. rewrite (Z.mod_small b 256) by lia.
  rewrite (u8_small b) by lia.
  destruct Hod as [-> | [-> | ->]]; red_consts; [fin | |].
  all: rewrite sysex_pass by first [lia | len_tac]; rewrite counter_pl7 by lia; crush_ifs; fin.
Qed.

Lemma agree_11 : forall od a b c delta bytes n,
  od_ok od -> reader_ok 11 a b c delta bytes n -> agrees 11 od a b c delta bytes n.
Proof.
  intros od a b c delta bytes n Hod Hr. rdr Hr. specialize (H11 eq_refl).
  unfold agrees, enc_of_call, owe_spec, sysex_spec, owe_sx.
  rewrite (Z.mod_small a 256), (Z.mod_small b 256), !(u8_small a), !(u8_small b) by lia.
  rewrite firstn_length_le by lia. rewrite Z2Nat.id by lia.
  rewrite !seven_bit_existsb, !negb_involutive.
  destruct Hod as [-> | [-> | ->]]; red_consts; crush_ifs; fin.
Qed.

(** The 12 kinds run() calls. *)
Theorem agree_all : forall kind od a b c delta bytes n,
  0 <= kind <= 11 -> od_ok od -> reader_ok kind a b c delta bytes n -> agrees kind od a b c delta bytes n.
Proof.
  intros kind od a b c delta bytes n Hk.
  assert (kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/ kind = 5 \/ kind = 6 \/ kind = 7 \/
          kind = 8 \/ kind = 9 \/ kind = 10 \/ kind = 11) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]].
  - apply agree_0.
  - apply agree_1.
  - apply agree_2.
  - apply agree_3.
  - apply agree_4.
  - apply agree_5.
  - apply agree_6.
  - apply agree_7.
  - apply agree_8.
  - apply agree_9.
  - apply agree_10.
  - apply agree_11.
Qed.

(** check_refusal: a SYSEX call with function 0x70 never succeeds. *)
Lemma refusal : forall od a b c delta bytes n,
  b = 0x70 -> fst (enc_of_call 11 od a b c delta bytes n) <> 0.
Proof.
  intros od a b c delta bytes n ->. unfold enc_of_call, sysex_spec.
  replace (0x70 mod 256) with 0x70 by reflexivity. red_consts.
  destruct (0x7f <? a mod 256); cbn; discriminate.
Qed.

(** check_range's "out unchanged": every failure of an encoder is (rc, None). *)
Definition fails_none (r : Z * option cmd) : Prop := fst r <> 0 -> snd r = None.

Lemma with_key_fails_none : forall r k, fails_none r -> fails_none (with_key r k).
Proof.
  intros [rc o] k H. unfold fails_none, with_key in *.
  destruct rc; [destruct o as [[[bs k'] dp]|]|..]; cbn in *;
    first [exact H | intros _; reflexivity | intros H'; exfalso; apply H'; reflexivity].
Qed.

Lemma sysex_fails_none : forall dev fn pl, fails_none (sysex_spec dev fn pl).
Proof. intros dev fn pl. unfold fails_none, sysex_spec. crush_ifs; cbn; congruence. Qed.

Lemma fails_none_None : forall rc, fails_none (rc, None).
Proof. intros rc _. reflexivity. Qed.

Lemma fails_none_0 : forall cm, fails_none (0, Some cm).
Proof. intros cm H. exfalso. apply H. reflexivity. Qed.

Lemma enc_fail_none : forall kind p a b c delta bytes n,
  fst (enc_of_call kind p a b c delta bytes n) <> 0 -> snd (enc_of_call kind p a b c delta bytes n) = None.
Proof.
  intros kind p a b c delta bytes n.
  change (fails_none (enc_of_call kind p a b c delta bytes n)).
  unfold enc_of_call. repeat split_if.
  all: destruct p as [d|];
    unfold fader_spec, touch_spec, button_spec, vpot_spec, jog_spec, ring_spec, meter_spec,
      strip_leds_spec, counter_leds_spec, leds_spec, scribble_spec, counter_spec; cbn beta iota zeta.
  all: repeat match goal with
         | |- fails_none (with_key _ _) => apply with_key_fails_none
         | |- fails_none (sysex_spec _ _ _) => apply sysex_fails_none
         | |- fails_none (let '(_, _) := ?x in _) => destruct x
         | |- fails_none (if ?c then _ else _) => destruct c
         end.
  all: first [apply fails_none_None | apply fails_none_0].
Qed.

(** ---- the owed command on success: check_bytes's widths ---- *)

(** Every byte is a byte, there are at most 24, the key is a u32 and the display flag 0 or 1. *)
Definition cmd_wf (cm : cmd) : Prop :=
  let '(bs, key, dp) := cm in
  (length bs <= 24)%nat /\ Forall (fun x => 0 <= x < 256) bs /\ 0 <= key < 2 ^ 32 /\ (dp = 0 \/ dp = 1).

Lemma u8_range : forall x, 0 <= u8 x < 256.
Proof. intros x. unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma lor_lt_pow2 : forall x y k, 0 <= x < 2 ^ k -> 0 <= y < 2 ^ k -> 0 <= Z.lor x y < 2 ^ k.
Proof.
  intros x y k Hx Hy. assert (0 <= k).
  { destruct (Z.neg_nonneg_cases k) as [Hk|Hk]; [|exact Hk]. rewrite Z.pow_neg_r in Hx by exact Hk. lia. }
  split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec k 0) as [->|Hk0].
  { change (2 ^ 0) with 1 in *. replace x with 0 by lia. replace y with 0 by lia. reflexivity. }
  destruct (Z.eq_dec (Z.lor x y) 0) as [E|E]; [rewrite E; apply Z.pow_pos_nonneg; lia|].
  apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg x y); lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - destruct (Z.eq_dec x 0) as [->|Ex]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec y 0) as [->|Ey]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma KEY_range : forall k addr, 0 <= k < 256 -> 0 <= KEY k addr < 2 ^ 32.
Proof.
  intros k addr Hk. unfold KEY. apply lor_lt_pow2.
  - change (2 ^ 32) with 4294967296. lia.
  - change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound addr (2 ^ 16) ltac:(lia)). change (2 ^ 32) with 4294967296.
    change (2 ^ 16) with 65536 in *. lia.
Qed.

Lemma bit_01 : forall t, bit_or_0 t 1 = 0 \/ bit_or_0 t 1 = 1.
Proof. intros [|]; cbn; auto. Qed.

Lemma Forall_firstn' : forall (P : Z -> Prop) k l, Forall P l -> Forall P (firstn k l).
Proof. intros P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.

Lemma Forall_rev' : forall (P : Z -> Prop) l, Forall P l -> Forall P (rev l).
Proof.
  intros P l H. induction H; cbn; [constructor|].
  apply Forall_app. split; [assumption|]. constructor; [assumption | constructor].
Qed.

Lemma owe_ring_range : forall b, 0 <= fst (owe_ring b) < 256 /\ 0 <= snd (owe_ring b) < 256.
Proof.
  intros b. rewrite <- ring_bits_owe, ring_bits_step.
  enough (H : 0 <= fst (fold_left (ring_step b) (map Z.of_nat (seq 0 7)) (0, 0)) < 2 ^ 7 /\
              0 <= snd (fold_left (ring_step b) (map Z.of_nat (seq 0 7)) (0, 0)) < 2 ^ 7)
    by (change (2 ^ 7) with 128 in H; lia).
  apply (fold_left_inv (fun pr => 0 <= fst pr < 2 ^ 7 /\ 0 <= snd pr < 2 ^ 7)).
  - cbn. lia.
  - intros [x y] k Hk [Hx Hy]. apply in_map_iff in Hk. destruct Hk as (k' & <- & Hk'). apply in_seq in Hk'.
    assert (0 <= 2 ^ (6 - Z.of_nat k') < 2 ^ 7).
    { split; [apply Z.pow_nonneg; lia|]. apply Z.pow_lt_mono_r; lia. }
    unfold ring_step; cbn [fst snd].
    split; apply lor_lt_pow2; auto; unfold bit_or_0;
      match goal with |- context [if ?t then _ else _] => destruct t end; lia.
Qed.

Ltac byte_tac :=
  repeat first
    [ apply Forall_nil
    | apply Forall_app; split
    | apply Forall_cons; [first [apply u8_range | lia] |]
    | apply Forall_rev'
    | apply Forall_firstn'; assumption ].

Lemma owe_ok_wf : forall kind od a b c delta bytes n,
  0 <= kind <= 11 -> od_ok od -> reader_ok kind a b c delta bytes n ->
  fst (owe_spec kind od a b c delta bytes n) = 0 -> cmd_wf (snd (owe_spec kind od a b c delta bytes n)).
Proof.
  intros kind od a b c delta bytes n Hk Hod Hr. rdr Hr.
  pose proof (owe_ring_range b) as Hring. destruct (owe_ring b) as [p1 p2] eqn:Ering. cbn [fst snd] in Hring.
  assert (kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/ kind = 5 \/ kind = 6 \/ kind = 7 \/
          kind = 8 \/ kind = 9 \/ kind = 10 \/ kind = 11) as Hkc by lia.
  unfold owe_spec.
  destruct Hkc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]];
    destruct Hod as [-> | [-> | ->]]; red_consts; rewrite ?Ering; crush_ifs; bools; intros Hok;
    try (cbn [fst] in Hok; unfold E_ARG, E_RANGE, E_SPACE, E_REFUSED in Hok; discriminate Hok).
  all: try unfold owe_sx; cbn [snd cmd_wf]; split; [len_tac|]; split; [byte_tac|].
  all: split; [first [apply KEY_range; lia | change (2 ^ 32) with 4294967296; lia]
              | first [apply bit_01 | left; reflexivity]].
Qed.
