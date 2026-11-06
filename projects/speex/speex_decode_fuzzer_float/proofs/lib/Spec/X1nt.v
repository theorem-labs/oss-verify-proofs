(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import Strings.String.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy.
Import ListNotations.
Import X1bt.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition MAX_CHARS_PER_FRAME : Z := 2000.
Definition BITS_PER_CHAR : Z := 8.

Definition MSG_PACKET_LARGER : list Z := str_bytes "Packet is larger than allocated buffer".
Definition MSG_COULD_NOT_RESIZE : list Z := str_bytes "Could not resize input buffer: truncating input".
Definition MSG_NOT_OWNER : list Z := str_bytes "Do not own input buffer: truncating oversize input".

Section Record.
Variable ptr : Type.
Record bits_st : Type := mkBits {
sb_chars : ptr;
sb_data : list Z;
sb_nbBits : Z;
sb_charPtr : Z;
sb_bitPtr : Z;
sb_owner : Z;
sb_overflow : Z;
sb_buf_size : Z }.
End Record.
Arguments mkBits {ptr}.
Arguments sb_chars {ptr}. Arguments sb_data {ptr}. Arguments sb_nbBits {ptr}. Arguments sb_charPtr {ptr}.
Arguments sb_bitPtr {ptr}. Arguments sb_owner {ptr}. Arguments sb_overflow {ptr}. Arguments sb_buf_size {ptr}.

Definition bit_at (data : list Z) (p : Z) : Z := Z.land (Z.shiftr (znth data (p / 8)) (7 - p mod 8)) 1.

Fixpoint getbits_acc (data : list Z) (p : Z) (n : nat) (d : Z) : Z :=
match n with
| O => d
| S n' => getbits_acc data (p + 1) n' (d * 2 + bit_at data p)
end.
Definition getbits (data : list Z) (p n : Z) : Z := getbits_acc data p (Z.to_nat n) 0.

Lemma bit_at_range : forall data p, 0 <= bit_at data p <= 1.
Proof.
intros. unfold bit_at.
assert (E : forall x, Z.land x 1 = x mod 2).
{ intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. }
rewrite E. pose proof (Z.mod_pos_bound (Z.shiftr (znth data (p / 8)) (7 - p mod 8)) 2 ltac:(lia)). lia.
Qed.

Lemma land_double_1 : forall d, Z.land (d * 2) 1 = 0.
Proof.
intros d. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. apply Z.mod_mul. lia.
Qed.
Lemma lor_double_bit : forall d bit, 0 <= bit <= 1 -> Z.lor (d * 2) bit = d * 2 + bit.
Proof.
intros d bit Hb. assert (bit = 0 \/ bit = 1) as [->| ->] by lia.
- rewrite Z.lor_0_r. lia.
- rewrite <- Z.lxor_lor by apply land_double_1. symmetry. apply Z.add_nocarry_lxor. apply land_double_1.
Qed.

Lemma getbits_acc_bound : forall data n p d, 0 <= d -> 0 <= getbits_acc data p n d < (d + 1) * 2 ^ (Z.of_nat n).
Proof.
induction n as [|n IH]; intros p d Hd; cbn [getbits_acc].
- rewrite Z.pow_0_r. lia.
- pose proof (bit_at_range data p) as Hb.
specialize (IH (p + 1) (d * 2 + bit_at data p) ltac:(lia)).
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
Qed.

Lemma getbits_bound : forall data p n, 0 <= getbits data p n < 2 ^ (Z.max 0 n).
Proof.
intros. unfold getbits. pose proof (getbits_acc_bound data (Z.to_nat n) p 0 ltac:(lia)) as H.
replace (Z.of_nat (Z.to_nat n)) with (Z.max 0 n) in H by lia. lia.
Qed.

Section Pure.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition bits_pos b : Z := sb_charPtr b * 8 + sb_bitPtr b.

Definition set_overflow b : bits_st ptr :=
mkBits (sb_chars b) (sb_data b) (sb_nbBits b) (sb_charPtr b) (sb_bitPtr b) (sb_owner b) 1 (sb_buf_size b).
Definition set_pos b (p : Z) : bits_st ptr :=
mkBits (sb_chars b) (sb_data b) (sb_nbBits b) (p / 8) (p mod 8) (sb_owner b) (sb_overflow b) (sb_buf_size b).

Definition speex_bits_reset b : bits_st ptr :=
mkBits (sb_chars b) (zupd (sb_data b) 0 0) 0 0 0 (sb_owner b) 0 (sb_buf_size b).

Definition speex_bits_unpack_unsigned b (n : Z) : Z * bits_st ptr :=
if (sb_nbBits b <? bits_pos b + n) || negb (sb_overflow b =? 0) then (0, set_overflow b)
else (getbits (sb_data b) (bits_pos b) n, set_pos b (bits_pos b + n)).

Definition speex_bits_unpack_signed b (n : Z) : Z * bits_st ptr :=
let '(d, b') := speex_bits_unpack_unsigned b n in
((if Z.shiftr d (n - 1) =? 0 then d else s32 (Z.lor d (Z.shiftl (2^32 - 1) n))), b').

Definition speex_bits_peek_unsigned b (n : Z) : Z * bits_st ptr :=
if (sb_nbBits b <? bits_pos b + n) || negb (sb_overflow b =? 0) then (0, set_overflow b)
else (getbits (sb_data b) (bits_pos b) n, b).

Definition speex_bits_peek b : Z * bits_st ptr :=
if (sb_nbBits b <? bits_pos b + 1) || negb (sb_overflow b =? 0) then (0, set_overflow b)
else (bit_at (sb_data b) (bits_pos b), b).

Definition speex_bits_advance b (n : Z) : bits_st ptr :=
if (sb_nbBits b <? bits_pos b + n) || negb (sb_overflow b =? 0) then set_overflow b
else set_pos b (bits_pos b + n).

Definition speex_bits_remaining b : Z :=
if negb (sb_overflow b =? 0) then -1 else sb_nbBits b - bits_pos b.

Definition bits_ok b : Prop :=
zlength (sb_data b) = sb_buf_size b /\ 1 <= sb_buf_size b /\
0 <= sb_nbBits b <= sb_buf_size b * 8 /\
0 <= sb_charPtr b /\ 0 <= sb_bitPtr b < 8 /\ bits_pos b <= sb_nbBits b /\
(sb_overflow b = 0 \/ sb_overflow b = 1).

#[using="Type"] Lemma set_pos_fields : forall b p, sb_charPtr (set_pos b p) = p / 8 /\ sb_bitPtr (set_pos b p) = p mod 8 /\
bits_pos (set_pos b p) = p.
Proof. intros. unfold set_pos, bits_pos; cbn. repeat split. pose proof (Z.div_mod p 8 ltac:(lia)). lia. Qed.

#[using="Type"] Lemma advance_C_arith : forall charPtr bitPtr n,
charPtr + (bitPtr + n) / 8 = (charPtr * 8 + bitPtr + n) / 8 /\
(bitPtr + n) mod 8 = (charPtr * 8 + bitPtr + n) mod 8.
Proof.
intros. split.
- replace (charPtr * 8 + bitPtr + n) with ((bitPtr + n) + charPtr * 8) by lia.
rewrite Z.div_add by lia. lia.
- replace (charPtr * 8 + bitPtr + n) with ((bitPtr + n) + charPtr * 8) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

#[using="Type"] Lemma set_overflow_ok : forall b, bits_ok b -> bits_ok (set_overflow b).
Proof. intros b H. unfold bits_ok, set_overflow, bits_pos in *; cbn in *. repeat split; try lia. Qed.

#[using="Type"] Lemma set_pos_ok : forall b p, bits_ok b -> 0 <= p <= sb_nbBits b -> bits_ok (set_pos b p).
Proof.
intros b p H Hp. unfold bits_ok, set_pos, bits_pos in *; cbn in *.
pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)).
pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)).
repeat split; lia.
Qed.

#[using="Type"] Lemma speex_bits_unpack_unsigned_ok : forall b n v b', bits_ok b -> 0 <= n ->
speex_bits_unpack_unsigned b n = (v, b') ->
bits_ok b' /\ 0 <= v < 2 ^ n /\
sb_data b' = sb_data b /\ sb_nbBits b' = sb_nbBits b /\ sb_buf_size b' = sb_buf_size b /\
sb_chars b' = sb_chars b /\ sb_owner b' = sb_owner b /\
((sb_overflow b = 0 /\ bits_pos b + n <= sb_nbBits b /\ v = getbits (sb_data b) (bits_pos b) n /\ b' = set_pos b (bits_pos b + n))
\/ ((sb_overflow b <> 0 \/ sb_nbBits b < bits_pos b + n) /\ v = 0 /\ b' = set_overflow b)).
Proof.
intros b n v b' Hok Hn E. unfold speex_bits_unpack_unsigned in E.
destruct (Z.ltb_spec (sb_nbBits b) (bits_pos b + n)) as [Hlt|Hge]; cbn [orb] in E.
- inversion E; subst. split; [apply set_overflow_ok; exact Hok|]. split; [split; [lia| apply Z.pow_pos_nonneg; lia]|].
unfold set_overflow; cbn. repeat split; auto. all: right; repeat split; auto.
- destruct (Z.eqb_spec (sb_overflow b) 0) as [Ho|Ho]; cbn [negb] in E; inversion E; subst.
+ split; [apply set_pos_ok; [exact Hok|]; unfold bits_ok, bits_pos in *; lia|].
split; [pose proof (getbits_bound (sb_data b) (bits_pos b) n); rewrite Z.max_r in H by lia; exact H|].
unfold set_pos; cbn. repeat split; auto. all: left; repeat split; auto; lia.
+ split; [apply set_overflow_ok; exact Hok|]. split; [split; [lia| apply Z.pow_pos_nonneg; lia]|].
unfold set_overflow; cbn. repeat split; auto. all: right; repeat split; auto.
Qed.

#[using="Type"] Lemma speex_bits_advance_ok : forall b n, bits_ok b -> 0 <= bits_pos b + n ->
bits_ok (speex_bits_advance b n) /\
sb_data (speex_bits_advance b n) = sb_data b /\ sb_nbBits (speex_bits_advance b n) = sb_nbBits b /\
sb_buf_size (speex_bits_advance b n) = sb_buf_size b /\ sb_chars (speex_bits_advance b n) = sb_chars b /\
sb_owner (speex_bits_advance b n) = sb_owner b.
Proof.
intros b n Hok Hpos. unfold speex_bits_advance.
destruct (Z.ltb_spec (sb_nbBits b) (bits_pos b + n)); cbn [orb].
- split; [apply set_overflow_ok; exact Hok|]. unfold set_overflow; cbn; repeat split; reflexivity.
- destruct (Z.eqb_spec (sb_overflow b) 0); cbn [negb].
+ split; [apply set_pos_ok; [exact Hok| lia]|]. unfold set_pos; cbn; repeat split; reflexivity.
+ split; [apply set_overflow_ok; exact Hok|]. unfold set_overflow; cbn; repeat split; reflexivity.
Qed.

#[using="Type"] Lemma speex_bits_peek_ok : forall b v b', bits_ok b -> speex_bits_peek b = (v, b') ->
bits_ok b' /\ 0 <= v <= 1 /\ (b' = b \/ b' = set_overflow b).
Proof.
intros b v b' Hok E. unfold speex_bits_peek in E.
destruct ((sb_nbBits b <? bits_pos b + 1) || negb (sb_overflow b =? 0)); injection E as Ev Eb; subst v b'.
- split; [apply set_overflow_ok; exact Hok|]. split; [lia| right; reflexivity].
- split; [exact Hok|]. split; [apply bit_at_range| left; reflexivity].
Qed.

#[using="Type"] Lemma speex_bits_peek_unsigned_ok : forall b n v b', bits_ok b -> 0 <= n -> speex_bits_peek_unsigned b n = (v, b') ->
bits_ok b' /\ 0 <= v < 2 ^ n /\ (b' = b \/ b' = set_overflow b).
Proof.
intros b n v b' Hok Hn E. unfold speex_bits_peek_unsigned in E.
destruct ((sb_nbBits b <? bits_pos b + n) || negb (sb_overflow b =? 0)); injection E as Ev Eb; subst v b'.
- split; [apply set_overflow_ok; exact Hok|]. split; [split; [lia| apply Z.pow_pos_nonneg; lia]| right; reflexivity].
- split; [exact Hok|]. split; [pose proof (getbits_bound (sb_data b) (bits_pos b) n); rewrite Z.max_r in H by lia; exact H| left; reflexivity].
Qed.

#[using="Type"] Lemma speex_bits_remaining_spec : forall b, bits_ok b ->
(sb_overflow b = 0 -> speex_bits_remaining b = sb_nbBits b - bits_pos b /\ 0 <= speex_bits_remaining b) /\
(sb_overflow b <> 0 -> speex_bits_remaining b = -1).
Proof.
intros b Hok. unfold speex_bits_remaining. unfold bits_ok in Hok.
destruct (Z.eqb_spec (sb_overflow b) 0); cbn [negb]; split; intros; try lia. all: split; [reflexivity| lia].
Qed.
End Pure.

Section Bits.
Context {St ptr : Type}.
Variable lib_calloc : Z -> Z -> M St (option ptr).
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Variable spx_notify : list Z -> M St unit.
Variable spx_warning : list Z -> M St unit.
Implicit Types b : bits_st ptr.

Definition speex_bits_init : M St (option (bits_st ptr)) :=
r <- lib_calloc MAX_CHARS_PER_FRAME 1 ;;
match r with
| None => mret None
| Some p => mret (Some (speex_bits_reset (mkBits p (zrepeat 0 MAX_CHARS_PER_FRAME) 0 0 0 1 0 MAX_CHARS_PER_FRAME)))
end.

Definition speex_bits_destroy b : M St unit :=
if negb (sb_owner b =? 0) then lib_free (sb_chars b) else mret tt.

Definition speex_bits_read_from b (pkt : list Z) (len : Z) : M St (bits_st ptr) :=
let nchars := len in
' (b, nchars) <-
(if sb_buf_size b <? nchars then
spx_notify MSG_PACKET_LARGER ;;;
if negb (sb_owner b =? 0) then
tmp <- lib_realloc (sb_chars b) nchars ;;
match tmp with
| Some q => mret (mkBits q (sb_data b) (sb_nbBits b) (sb_charPtr b) (sb_bitPtr b) (sb_owner b) (sb_overflow b) nchars, nchars)
| None => spx_warning MSG_COULD_NOT_RESIZE ;;; mret (b, sb_buf_size b)
end
else spx_warning MSG_NOT_OWNER ;;; mret (b, sb_buf_size b)
else mret (b, nchars)) ;;
mret (mkBits (sb_chars b) (ztake nchars pkt ++ zdrop nchars (sb_data b)) (nchars * 8) 0 0 (sb_owner b) 0 (sb_buf_size b)).

End Bits.
