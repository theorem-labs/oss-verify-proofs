(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim CtSizes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition byte (c : list Z) (p : Z) : Z := u8 (znth c p).
Definition u16be (c : list Z) (p : Z) : Z := byte c p * 256 + byte c (p + 1).
Definition u64be (c : list Z) (p : Z) : Z :=
  ((((((byte c p * 256 + byte c (p + 1)) * 256 + byte c (p + 2)) * 256 + byte c (p + 3)) * 256 + byte c (p + 4)) * 256
     + byte c (p + 5)) * 256 + byte c (p + 6)) * 256 + byte c (p + 7).
Lemma byte_range c p : 0 <= byte c p < 256.
Proof. unfold byte, u8. apply Z.mod_pos_bound. lia. Qed.
Lemma u16be_range' c p : 0 <= u16be c p <= 65535.
Proof. unfold u16be. pose proof (byte_range c p). pose proof (byte_range c (p + 1)). lia. Qed.
Lemma u64be_nonneg c p : 0 <= u64be c p.
Proof. unfold u64be. pose proof (byte_range c p). pose proof (byte_range c (p+1)). pose proof (byte_range c (p+2)). pose proof (byte_range c (p+3)).
  pose proof (byte_range c (p+4)). pose proof (byte_range c (p+5)). pose proof (byte_range c (p+6)). pose proof (byte_range c (p+7)). lia. Qed.
(* [comment removed for export] *)
Definition slice (d : list Z) (p n : Z) : list Z := firstn (Z.to_nat n) (skipn (Z.to_nat p) d).

Lemma u16be_range c p : 0 <= u16be c p <= 65535.
Proof. apply u16be_range'. Qed.
Lemma slice_length d p n : 0 <= p -> 0 <= n -> p + n <= zlength d -> length (slice d p n) = Z.to_nat n.
Proof. intros. unfold slice, zlength in *. rewrite length_firstn, length_skipn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record sctr (ptr : Type) : Type := mkSCT {
  sc_blk : ptr;
  sc_version : Z;
  sc_blob : option (ptr * Z);
  sc_logid : option ptr;
  sc_ts : Z;
  sc_ext : option (ptr * Z);
  sc_extlen : Z;
  sc_hash : Z;
  sc_sigalg : Z;
  sc_sig : option (ptr * Z)
}.
Arguments mkSCT {ptr}.
Arguments sc_blk {ptr}. Arguments sc_version {ptr}. Arguments sc_blob {ptr}. Arguments sc_logid {ptr}. Arguments sc_ts {ptr}.
Arguments sc_ext {ptr}. Arguments sc_extlen {ptr}. Arguments sc_hash {ptr}. Arguments sc_sigalg {ptr}. Arguments sc_sig {ptr}.

Section Setters.
Context {ptr : Type}.
Implicit Types s : sctr ptr.
(* [comment removed for export] *)
Definition sct_new (b : ptr) : sctr ptr := mkSCT b (-1) None None 0 None 0 0 0 None.
Definition set_version (v : Z) s := mkSCT (sc_blk s) v (sc_blob s) (sc_logid s) (sc_ts s) (sc_ext s) (sc_extlen s) (sc_hash s) (sc_sigalg s) (sc_sig s).
Definition set_blob (v : option (ptr * Z)) s := mkSCT (sc_blk s) (sc_version s) v (sc_logid s) (sc_ts s) (sc_ext s) (sc_extlen s) (sc_hash s) (sc_sigalg s) (sc_sig s).
Definition set_logid (v : option ptr) s := mkSCT (sc_blk s) (sc_version s) (sc_blob s) v (sc_ts s) (sc_ext s) (sc_extlen s) (sc_hash s) (sc_sigalg s) (sc_sig s).
Definition set_ts (v : Z) s := mkSCT (sc_blk s) (sc_version s) (sc_blob s) (sc_logid s) v (sc_ext s) (sc_extlen s) (sc_hash s) (sc_sigalg s) (sc_sig s).
Definition set_ext (v : option (ptr * Z)) (l : Z) s := mkSCT (sc_blk s) (sc_version s) (sc_blob s) (sc_logid s) (sc_ts s) v l (sc_hash s) (sc_sigalg s) (sc_sig s).
Definition set_algs (h a : Z) s := mkSCT (sc_blk s) (sc_version s) (sc_blob s) (sc_logid s) (sc_ts s) (sc_ext s) (sc_extlen s) h a (sc_sig s).
Definition set_sig (v : option (ptr * Z)) s := mkSCT (sc_blk s) (sc_version s) (sc_blob s) (sc_logid s) (sc_ts s) (sc_ext s) (sc_extlen s) (sc_hash s) (sc_sigalg s) v.
Definition sc_siglen s : Z := match sc_sig s with Some (_, n) => n | None => 0 end.
Definition sc_bloblen s : Z := match sc_blob s with Some (_, n) => n | None => 0 end.

(* [comment removed for export] *)
Definition sct_nid s : Z := sig_nid (sc_version s) (sc_hash s) (sc_sigalg s).
Definition sct_sig_complete s : bool :=
  negb (sct_nid s =? NID_undef) && (match sc_sig s with Some _ => true | None => false end) && (0 <? sc_siglen s).
Definition sct_complete s : bool :=
  if sc_version s =? -1 then false
  else if sc_version s =? 0 then (match sc_logid s with Some _ => true | None => false end) && sct_sig_complete s
  else match sc_blob s with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition i2o_sct_len s : Z := if sc_version s =? 0 then 43 + sc_extlen s + 4 + sc_siglen s else sc_bloblen s.
(* [comment removed for export] *)
Definition sct_blocks s : list ptr :=
  (match sc_logid s with Some p => [p] | None => [] end)
  ++ (match sc_ext s with Some (p, _) => [p] | None => [] end)
  ++ (match sc_sig s with Some (p, _) => [p] | None => [] end)
  ++ (match sc_blob s with Some (p, _) => [p] | None => [] end)
  ++ [sc_blk s].
End Setters.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record skr (ptr : Type) : Type := mkSK { sk_blk : ptr; sk_data : option (ptr * Z); sk_items : list (sctr ptr) }.
Arguments mkSK {ptr}. Arguments sk_blk {ptr}. Arguments sk_data {ptr}. Arguments sk_items {ptr}.
Definition sk_num {ptr} (k : skr ptr) : Z := zlength (sk_items k).

(* [comment removed for export] *)
Fixpoint sk_grow (fuel : nat) (cur target : Z) {struct fuel} : Z :=
  match fuel with
  | O => cur
  | S f => if cur <? target then sk_grow f (cur * 8 / 5) target else cur
  end.
Definition SK_GROW_FUEL : nat := 40%nat.

(* [comment removed for export] *)
Lemma sk_grow_once cur : 4 <= cur -> sk_grow SK_GROW_FUEL cur (cur + 1) = cur * 8 / 5.
Proof.
  intros H. unfold SK_GROW_FUEL. cbn [sk_grow].
  replace (cur <? cur + 1) with true by (symmetry; apply Z.ltb_lt; lia).
  assert (cur + 1 <= cur * 8 / 5) by (apply Z.div_le_lower_bound; lia).
  cbn [sk_grow]. replace (cur * 8 / 5 <? cur + 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint len_octets (fuel : nat) (n : Z) {struct fuel} : Z :=
  match fuel with O => 0 | S f => if 0 <? n then 1 + len_octets f (Z.shiftr n 8) else 0 end.
(* [comment removed for export] *)
Definition der_hl (n : Z) : Z := 1 + (if n <? 128 then 1 else 1 + len_octets 9%nat n).
Lemma der_hl_small n : 0 <= n < 128 -> der_hl n = 2.
Proof. intros. unfold der_hl. replace (n <? 128) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma der_hl_mid n : 128 <= n < 256 -> der_hl n = 3.
Proof.
  intros. unfold der_hl. replace (n <? 128) with false by (symmetry; apply Z.ltb_ge; lia). cbn [len_octets].
  replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Z.shiftr_div_pow2 by lia.
  replace (0 <? n / 2 ^ 8) with false by (symmetry; apply Z.ltb_ge; change (2^8) with 256; apply Z.le_ngt; pose proof (Z.div_lt_upper_bound n 256 1 ltac:(lia) ltac:(lia)); lia).
  reflexivity.
Qed.
Lemma der_hl_big n : 256 <= n < 65536 -> der_hl n = 4.
Proof.
  intros. unfold der_hl. replace (n <? 128) with false by (symmetry; apply Z.ltb_ge; lia). cbn [len_octets].
  replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia). rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  assert (1 <= n / 256 < 256) by (split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia]).
  replace (0 <? n / 256) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (0 <? n / 256 / 256) with false by (symmetry; apply Z.ltb_ge; apply Z.le_ngt; pose proof (Z.div_lt_upper_bound (n / 256) 256 1 ltac:(lia) ltac:(lia)); lia).
  reflexivity.
Qed.
