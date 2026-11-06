(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlParser.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_pot2 BY_acct_needs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section BUF.
Variables (acharge arefund : Z -> Z) (F : Z).
Hypothesis AC0 : forall n, 0 <= acharge n.
Hypothesis AR0 : forall n, 0 <= arefund n.
Hypothesis HF : 0 <= F <= 1.
Hypothesis BIG : forall t, 2^19 <= t -> acharge (t + 256) - arefund t <= 7.

(* [comment removed for export] *)
Fixpoint Gs (n : nat) (len : Z) : Z :=
  match n with O => 0 | S n' => if len <? 2^28 then acharge (2 * len) + F + Gs n' (2 * len) else 0 end.
Definition G (len : Z) : Z := Gs (Z.to_nat 30) len.

Lemma Gs_nonneg : forall n x, 0 <= Gs n x.
Proof. induction n; intros; cbn [Gs]; [lia|]. destruct (x <? 2^28); [pose proof (AC0 (2*x)); pose proof (IHn (2*x)); lia| lia]. Qed.
Lemma G_nonneg : forall x, 0 <= G x. Proof. intros; unfold G; apply Gs_nonneg. Qed.

Lemma Gs_enough : forall n m x, 1 <= x -> 2^28 <= x * 2 ^ Z.of_nat n -> (n <= m)%nat -> Gs m x = Gs n x.
Proof.
  induction n; intros m x Hx Hp Hnm.
  - cbn [Gs]. destruct m; [reflexivity|]. cbn [Gs]. replace (x <? 2^28) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. rewrite Z.pow_0_r in Hp. lia.
  - destruct m; [lia|]. cbn [Gs]. destruct (x <? 2^28); [| reflexivity]. f_equal. apply IHn; [lia| | lia].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hp by lia. lia.
Qed.

Lemma G_unfold : forall x, 1 <= x -> G x = if x <? 2^28 then acharge (2 * x) + F + G (2 * x) else 0.
Proof.
  intros x Hx. unfold G. replace (Z.to_nat 30) with (S (Z.to_nat 29)) at 1 by (rewrite <- Z2Nat.inj_succ by lia; reflexivity).
  cbn [Gs]. destruct (x <? 2^28); [| reflexivity].
  enough (E : Gs (Z.to_nat 30) (2 * x) = Gs (Z.to_nat 29) (2 * x)) by (rewrite E; reflexivity).
  apply Gs_enough; [lia| | apply Z2Nat.inj_le; lia]. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma G_double : forall x, 1 <= x -> x < 2^28 -> G x = acharge (2 * x) + F + G (2 * x).
Proof. intros x H1 H2. rewrite (G_unfold x H1). replace (x <? 2^28) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

(* [comment removed for export] *)
Lemma ens_G : forall f want len used,
  1 <= len -> used + want < 2^28 -> ens_need_loop f want len used <> len ->
  acharge (ens_need_loop f want len used) + F + G (ens_need_loop f want len used) <= G len.
Proof.
  induction f; intros want len used Hl Huw Hne; [cbn in Hne; congruence|].
  cbn [ens_need_loop] in *.
  destruct (Z.leb_spec (len - used) want); destruct (Z.ltb_spec 0 len); cbn [andb] in *; try congruence.
  rewrite (G_double len) by lia.
  destruct (Z.eq_dec (ens_need_loop f want (len * 2) used) (len * 2)) as [E|NE].
  - rewrite E. replace (len * 2) with (2 * len) by lia. pose proof (G_nonneg (2 * len)). lia.
  - pose proof (IHf want (len * 2) used ltac:(lia) Huw NE). replace (2 * len) with (len * 2) by lia.
    pose proof (AC0 (len * 2)). lia.
Qed.

(* [comment removed for export] *)
Definition phi_buf (b : ybuf) : Z :=
  match yb_state b with
  | BS_ok => match yb_data b with Some _ => G (yb_len b) + 2 * F | None => acharge YAJL_BUF_INIT_SIZE + G YAJL_BUF_INIT_SIZE + 2 * F end
  | _ => 2 * F        (* [comment removed for export] *)
  end.

Lemma phi_buf_nonneg : forall b, 0 <= phi_buf b.
Proof. intros [st len used d bs]; unfold phi_buf; cbn [yb_state yb_data yb_len]. pose proof (G_nonneg len); pose proof (G_nonneg YAJL_BUF_INIT_SIZE); pose proof (AC0 YAJL_BUF_INIT_SIZE). destruct st; try lia; destruct d; lia. Qed.

Lemma phi_buf_shape : forall st len u1 u2 d bs1 bs2, phi_buf (mkBuf st len u1 d bs1) = phi_buf (mkBuf st len u2 d bs2).
Proof. reflexivity. Qed.
Lemma phi_buf_first : forall (d : yptr) used bs,
  acharge YAJL_BUF_INIT_SIZE + phi_buf (mkBuf BS_ok YAJL_BUF_INIT_SIZE used (Some d) bs) <= phi_buf (mkBuf BS_ok 0 used None bs).
Proof. intros. unfold phi_buf. cbn [yb_state yb_data yb_len]. lia. Qed.
Lemma phi_buf_grow : forall len used want (d : yptr) bs,
  0 <= used < len -> len < 2^31 -> 0 < want -> used + want < 2^28 -> ens_need_loop ENS_FUEL want len used <> len ->
  acharge (ens_need_loop ENS_FUEL want len used) + F + phi_buf (mkBuf BS_ok (ens_need_loop ENS_FUEL want len used) used (Some d) bs)
    <= phi_buf (mkBuf BS_ok len used (Some d) bs).
Proof. intros. unfold phi_buf. cbn [yb_state yb_data yb_len]. pose proof (ens_G ENS_FUEL want len used ltac:(lia) ltac:(lia) ltac:(assumption)). lia. Qed.
(* [comment removed for export] *)
Lemma phi_buf_err : forall len u (d : yptr) bs, phi_buf (mkBuf BS_overflow 0 0 None []) <= phi_buf (mkBuf BS_ok len u (Some d) bs).
Proof. intros. unfold phi_buf. cbn [yb_state yb_data yb_len]. pose proof (G_nonneg len). lia. Qed.
(* [comment removed for export] *)
Lemma phi_buf_2F : forall b, F + F <= phi_buf b.
Proof. intros [st len used d bs]; unfold phi_buf; cbn [yb_state yb_data yb_len]. pose proof (G_nonneg len); pose proof (G_nonneg YAJL_BUF_INIT_SIZE); pose proof (AC0 YAJL_BUF_INIT_SIZE). destruct st; try lia; destruct d; lia. Qed.
Lemma phi_buf_zero : phi_buf ybuf_zero = acharge YAJL_BUF_INIT_SIZE + G YAJL_BUF_INIT_SIZE + 2 * F. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition phrc := phr acharge arefund F.
Definition phi_hand (h : yhandle) (L : Z) : Z :=
  phi_buf (lx_buf (h_lexer h)) + phi_buf (h_decbuf h) + phrc (h_bytesConsumed h) (h_used h) (h_stack_size h) L.

Lemma phi_hand_free : forall h L, F + phi_buf (h_decbuf h) + (F + phi_buf (lx_buf (h_lexer h))) + F <= phi_hand h L.
Proof. intros. unfold phi_hand, phrc. pose proof (phr_ge_3F acharge arefund F AC0 HF (h_bytesConsumed h) (h_used h) (h_stack_size h) L). lia. Qed.
Lemma phi_hand_lex1 : forall h L, phi_buf (lx_buf (h_lexer h)) <= phi_hand h L.
Proof. intros. unfold phi_hand, phrc. pose proof (phi_buf_nonneg (h_decbuf h)). pose proof (phr_nonneg acharge arefund F AC0 HF (h_bytesConsumed h) (h_used h) (h_stack_size h) L). lia. Qed.
Lemma phi_hand_shape : forall h1 h2 L, h_lexer h1 = h_lexer h2 -> h_decbuf h1 = h_decbuf h2 -> h_bytesConsumed h1 = h_bytesConsumed h2 ->
  h_used h1 = h_used h2 -> h_stack_size h1 = h_stack_size h2 -> h_stack_blk h1 = h_stack_blk h2 -> phi_hand h1 L = phi_hand h2 L.
Proof. intros. unfold phi_hand. rewrite H, H0, H1, H2, H3. reflexivity. Qed.
Lemma phi_hand_split : forall h L, phi_hand h L = phi_buf (lx_buf (h_lexer h)) + phi_buf (h_decbuf h) + phrc (h_bytesConsumed h) (h_used h) (h_stack_size h) L.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma phr_init1_le : forall L, 0 <= L -> phrc 0 1 128 L <= 3 * F + P acharge arefund F 128 + (L / 16 + 8) + ypc acharge F 128.
Proof.
  intros L HL. unfold phrc, phr.
  assert (PHI 0 1 128 L <= L / 16 + 8) by (unfold PHI, TT; Z.div_mod_to_equations; nia).
  assert (RSV acharge F 0 128 L <= ypc acharge F 128) by (unfold RSV; destruct (0 <? L); [lia| apply ypc_nonneg; assumption]). lia.
Qed.
Definition phi_new (L : Z) : Z :=
  acharge 104 + acharge 48 + 2 * acharge 32 + acharge 128 + 4 * F + 4 * phi_buf ybuf_zero
  + (3 * F + P acharge arefund F 128 + (Z.max 0 L / 16 + 8) + ypc acharge F 128).
Lemma phi_new_alloc : forall L (hb lb db sb : yptr) (bb : nat), 0 <= L ->
  acharge 104 + acharge 48 + 2 * acharge 32 + acharge 128 + 4 * F + 2 * phi_buf ybuf_zero
  + phi_hand (yalloc_hand hb lb db sb bb) L <= phi_new L.
Proof.
  intros L hb lb db sb bb HL. unfold phi_new, phi_hand, yalloc_hand, h_used. cbn [h_lexer h_decbuf lx_buf h_bytesConsumed h_stack h_stack_size].
  change (zlength [ST_start]) with 1. rewrite Z.max_r by lia.
  pose proof (phr_init1_le L HL). lia.
Qed.
Lemma phi_new_nonneg : forall L, 0 <= phi_new L.
Proof.
  intros L. unfold phi_new. pose proof (AC0 104). pose proof (AC0 48). pose proof (AC0 32). pose proof (AC0 128).
  pose proof (phi_buf_nonneg ybuf_zero). pose proof (P_nonneg acharge arefund F 128). pose proof (ypc_nonneg acharge F AC0 HF 128).
  Z.div_mod_to_equations. lia.
Qed.
End BUF.
End RC__1.
