(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record seqsym : Type := mkSS { ss_next : Z; ss_nbAdd : Z; ss_nbBits : Z; ss_base : Z }.

(* [comment removed for export] *)
Record seq_table : Type := mkST { st_fast : Z; st_log : Z; st_cells : list seqsym }.

Definition ss0 : seqsym := mkSS 0 0 0 0.
(* [comment removed for export] *)
Definition st_cell (t : seq_table) (state : Z) : seqsym := nth (Z.to_nat state) (st_cells t) ss0.

(* [comment removed for export] *)
Definition zle2 (v : Z) : list Z := [v mod 256; (v / 256) mod 256].
Definition zle4 (v : Z) : list Z := [v mod 256; (v / 256) mod 256; (v / 65536) mod 256; (v / 16777216) mod 256].
Definition seqsym_bytes (c : seqsym) : list Z := zle2 (ss_next c) ++ [ss_nbAdd c; ss_nbBits c] ++ zle4 (ss_base c).
Definition seq_table_bytes (t : seq_table) : list Z :=
  zle4 (st_fast t) ++ zle4 (st_log t) ++ flat_map seqsym_bytes (st_cells t).

Lemma seqsym_bytes_length c : length (seqsym_bytes c) = 8%nat.
Proof. reflexivity. Qed.

Lemma seq_table_bytes_length t : Zlength (seq_table_bytes t) = 8 * (1 + Zlength (st_cells t)).
Proof.
  unfold seq_table_bytes, Zlength. rewrite !length_app. cbn [zle4 length].
  assert (E : length (flat_map seqsym_bytes (st_cells t)) = (8 * length (st_cells t))%nat).
  { induction (st_cells t) as [|c l IH]; [reflexivity|]. cbn [flat_map]. rewrite length_app, IH, seqsym_bytes_length. cbn [length]. lia. }
  rewrite E. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LL_base : list Z :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 18; 20; 22; 24; 28; 32; 40; 48; 64; 128; 256; 512; 1024; 2048; 4096; 8192; 16384; 32768; 65536].
Definition LL_bits : list Z :=
  [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 2; 2; 3; 3; 4; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16].
Definition OF_base : list Z :=
  [0; 1; 1; 5; 13; 29; 61; 125; 253; 509; 1021; 2045; 4093; 8189; 16381; 32765; 65533; 131069; 262141; 524285; 1048573; 2097149; 4194301; 8388605; 16777213; 33554429; 67108861; 134217725; 268435453; 536870909; 1073741821; 2147483645].
Definition OF_bits : list Z :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].
Definition ML_base : list Z :=
  [3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 37; 39; 41; 43; 47; 51; 59; 67; 83; 99; 131; 259; 515; 1027; 2051; 4099; 8195; 16387; 32771; 65539].
Definition ML_bits : list Z :=
  [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 2; 2; 3; 3; 4; 4; 5; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16].
Definition LL_defaultDTable : seq_table :=
  mkST 16842753 6
  [mkSS 0 0 4 0; mkSS 16 0 4 0; mkSS 32 0 5 1; mkSS 0 0 5 3
  ; mkSS 0 0 5 4; mkSS 0 0 5 6; mkSS 0 0 5 7; mkSS 0 0 5 9
  ; mkSS 0 0 5 10; mkSS 0 0 5 12; mkSS 0 0 6 14; mkSS 0 1 5 16
  ; mkSS 0 1 5 20; mkSS 0 1 5 22; mkSS 0 2 5 28; mkSS 0 3 5 32
  ; mkSS 0 4 5 48; mkSS 32 6 5 64; mkSS 0 7 5 128; mkSS 0 8 6 256
  ; mkSS 0 10 6 1024; mkSS 0 12 6 4096; mkSS 32 0 4 0; mkSS 0 0 4 1
  ; mkSS 0 0 5 2; mkSS 32 0 5 4; mkSS 0 0 5 5; mkSS 32 0 5 7
  ; mkSS 0 0 5 8; mkSS 32 0 5 10; mkSS 0 0 5 11; mkSS 0 0 6 13
  ; mkSS 32 1 5 16; mkSS 0 1 5 18; mkSS 32 1 5 22; mkSS 0 2 5 24
  ; mkSS 32 3 5 32; mkSS 0 3 5 40; mkSS 0 6 4 64; mkSS 16 6 4 64
  ; mkSS 32 7 5 128; mkSS 0 9 6 512; mkSS 0 11 6 2048; mkSS 48 0 4 0
  ; mkSS 16 0 4 1; mkSS 32 0 5 2; mkSS 32 0 5 3; mkSS 32 0 5 5
  ; mkSS 32 0 5 6; mkSS 32 0 5 8; mkSS 32 0 5 9; mkSS 32 0 5 11
  ; mkSS 32 0 5 12; mkSS 0 0 6 15; mkSS 32 1 5 18; mkSS 32 1 5 20
  ; mkSS 32 2 5 24; mkSS 32 2 5 28; mkSS 32 3 5 40; mkSS 32 4 5 48
  ; mkSS 0 16 6 65536; mkSS 0 15 6 32768; mkSS 0 14 6 16384; mkSS 0 13 6 8192].
Definition OF_defaultDTable : seq_table :=
  mkST 16842753 5
  [mkSS 0 0 5 0; mkSS 0 6 4 61; mkSS 0 9 5 509; mkSS 0 15 5 32765
  ; mkSS 0 21 5 2097149; mkSS 0 3 5 5; mkSS 0 7 4 125; mkSS 0 12 5 4093
  ; mkSS 0 18 5 262141; mkSS 0 23 5 8388605; mkSS 0 5 5 29; mkSS 0 8 4 253
  ; mkSS 0 14 5 16381; mkSS 0 20 5 1048573; mkSS 0 2 5 1; mkSS 16 7 4 125
  ; mkSS 0 11 5 2045; mkSS 0 17 5 131069; mkSS 0 22 5 4194301; mkSS 0 4 5 13
  ; mkSS 16 8 4 253; mkSS 0 13 5 8189; mkSS 0 19 5 524285; mkSS 0 1 5 1
  ; mkSS 16 6 4 61; mkSS 0 10 5 1021; mkSS 0 16 5 65533; mkSS 0 28 5 268435453
  ; mkSS 0 27 5 134217725; mkSS 0 26 5 67108861; mkSS 0 25 5 33554429; mkSS 0 24 5 16777213].
Definition ML_defaultDTable : seq_table :=
  mkST 16842753 6
  [mkSS 0 0 6 3; mkSS 0 0 4 4; mkSS 32 0 5 5; mkSS 0 0 5 6
  ; mkSS 0 0 5 8; mkSS 0 0 5 9; mkSS 0 0 5 11; mkSS 0 0 6 13
  ; mkSS 0 0 6 16; mkSS 0 0 6 19; mkSS 0 0 6 22; mkSS 0 0 6 25
  ; mkSS 0 0 6 28; mkSS 0 0 6 31; mkSS 0 0 6 34; mkSS 0 1 6 37
  ; mkSS 0 1 6 41; mkSS 0 2 6 47; mkSS 0 3 6 59; mkSS 0 4 6 83
  ; mkSS 0 7 6 131; mkSS 0 9 6 515; mkSS 16 0 4 4; mkSS 0 0 4 5
  ; mkSS 32 0 5 6; mkSS 0 0 5 7; mkSS 32 0 5 9; mkSS 0 0 5 10
  ; mkSS 0 0 6 12; mkSS 0 0 6 15; mkSS 0 0 6 18; mkSS 0 0 6 21
  ; mkSS 0 0 6 24; mkSS 0 0 6 27; mkSS 0 0 6 30; mkSS 0 0 6 33
  ; mkSS 0 1 6 35; mkSS 0 1 6 39; mkSS 0 2 6 43; mkSS 0 3 6 51
  ; mkSS 0 4 6 67; mkSS 0 5 6 99; mkSS 0 8 6 259; mkSS 32 0 4 4
  ; mkSS 48 0 4 4; mkSS 16 0 4 5; mkSS 32 0 5 7; mkSS 32 0 5 8
  ; mkSS 32 0 5 10; mkSS 32 0 5 11; mkSS 0 0 6 14; mkSS 0 0 6 17
  ; mkSS 0 0 6 20; mkSS 0 0 6 23; mkSS 0 0 6 26; mkSS 0 0 6 29
  ; mkSS 0 0 6 32; mkSS 0 16 6 65539; mkSS 0 15 6 32771; mkSS 0 14 6 16387
  ; mkSS 0 13 6 8195; mkSS 0 12 6 4099; mkSS 0 11 6 2051; mkSS 0 10 6 1027].

Inductive seq_kind : Type := K_LL | K_OF | K_ML.
Definition kind_base (k : seq_kind) : list Z := match k with K_LL => LL_base | K_OF => OF_base | K_ML => ML_base end.
Definition kind_bits (k : seq_kind) : list Z := match k with K_LL => LL_bits | K_OF => OF_bits | K_ML => ML_bits end.
(* [comment removed for export] *)
Definition kind_max (k : seq_kind) : Z := match k with K_LL => 35 | K_OF => 31 | K_ML => 52 end.
(* [comment removed for export] *)
Definition kind_maxLog (k : seq_kind) : Z := match k with K_LL => 9 | K_OF => 8 | K_ML => 9 end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sym_pairb (k : seq_kind) (c : seqsym) (s : Z) : bool :=
  (ss_base c =? Znth s (kind_base k)) && (ss_nbAdd c =? Znth s (kind_bits k)).

(* [comment removed for export] *)
Definition sym_ok (k : seq_kind) (c : seqsym) : Prop :=
  exists s, 0 <= s <= kind_max k /\ ss_base c = Znth s (kind_base k) /\ ss_nbAdd c = Znth s (kind_bits k).

Definition cell_ok (k : seq_kind) (tl : Z) (c : seqsym) : Prop :=
  0 <= ss_nbBits c <= tl /\ 0 <= ss_next c /\ ss_next c + 2^(ss_nbBits c) <= 2^tl /\ sym_ok k c.

Definition seq_table_ok (k : seq_kind) (t : seq_table) : Prop :=
  0 <= st_log t <= kind_maxLog k /\ Zlength (st_cells t) = 2^(st_log t) /\ Forall (cell_ok k (st_log t)) (st_cells t).

(* [comment removed for export] *)
Fixpoint zseq (n : nat) (from : Z) : list Z := match n with O => [] | S m => from :: zseq m (from + 1) end.

Definition sym_okb (k : seq_kind) (c : seqsym) : bool := existsb (sym_pairb k c) (zseq (Z.to_nat (kind_max k + 1)) 0).
Definition cell_okb (k : seq_kind) (tl : Z) (c : seqsym) : bool :=
  (0 <=? ss_nbBits c) && (ss_nbBits c <=? tl) && (0 <=? ss_next c) && (ss_next c + 2^(ss_nbBits c) <=? 2^tl) && sym_okb k c.
Definition seq_table_okb (k : seq_kind) (t : seq_table) : bool :=
  (0 <=? st_log t) && (st_log t <=? kind_maxLog k) && (Zlength (st_cells t) =? 2^(st_log t))
  && forallb (cell_okb k (st_log t)) (st_cells t).

Lemma zseq_In n : forall from x, In x (zseq n from) -> from <= x < from + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros from x; cbn [zseq In]; [tauto|]. intros [<-|H]; [lia|]. apply IH in H. lia.
Qed.

Lemma sym_okb_ok k c : sym_okb k c = true -> sym_ok k c.
Proof.
  unfold sym_okb. rewrite existsb_exists. intros (s & Hin & Hp). apply zseq_In in Hin.
  unfold sym_pairb in Hp. apply andb_true_iff in Hp. destruct Hp as [H1 H2]. apply Z.eqb_eq in H1, H2.
  exists s. split; [destruct k; cbn [kind_max] in *; lia|]. auto.
Qed.

Lemma cell_okb_ok k tl c : cell_okb k tl c = true -> cell_ok k tl c.
Proof.
  unfold cell_okb. rewrite !andb_true_iff. intros ((((H1 & H2) & H3) & H4) & H5).
  apply Z.leb_le in H1, H2, H3, H4. apply sym_okb_ok in H5. unfold cell_ok. auto.
Qed.

Lemma seq_table_okb_ok k t : seq_table_okb k t = true -> seq_table_ok k t.
Proof.
  unfold seq_table_okb. rewrite !andb_true_iff. intros (((H1 & H2) & H3) & H4).
  apply Z.leb_le in H1, H2. apply Z.eqb_eq in H3. split; [lia|]. split; [exact H3|].
  apply Forall_forall. intros c Hc. apply cell_okb_ok. rewrite forallb_forall in H4. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma LL_default_ok : seq_table_ok K_LL LL_defaultDTable.
Proof. apply seq_table_okb_ok. vm_compute. reflexivity. Qed.
Lemma OF_default_ok : seq_table_ok K_OF OF_defaultDTable.
Proof. apply seq_table_okb_ok. vm_compute. reflexivity. Qed.
Lemma ML_default_ok : seq_table_ok K_ML ML_defaultDTable.
Proof. apply seq_table_okb_ok. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition rle_table (k : seq_kind) (s : Z) : seq_table :=
  mkST 0 0 [mkSS 0 (Znth s (kind_bits k)) 0 (Znth s (kind_base k))].

Lemma rle_table_ok k s : 0 <= s <= kind_max k -> seq_table_ok k (rle_table k s).
Proof.
  intros H. unfold seq_table_ok, rle_table; cbn [st_log st_cells]. split; [destruct k; cbn; lia|]. split; [reflexivity|].
  constructor; [|constructor]. unfold cell_ok; cbn [ss_nbBits ss_next ss_nbAdd ss_base].
  repeat split; try lia. exists s. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma st_cell_ok k t state : seq_table_ok k t -> 0 <= state < 2^(st_log t) -> cell_ok k (st_log t) (st_cell t state).
Proof.
  intros (_ & L & F) Hs. rewrite Forall_forall in F. apply F. unfold st_cell. apply nth_In. unfold Zlength in L. lia.
Qed.

(* [comment removed for export] *)
Lemma next_state_in k tl c lowBits : cell_ok k tl c -> 0 <= lowBits < 2^(ss_nbBits c) ->
  0 <= ss_next c + lowBits < 2^tl.
Proof. intros (_ & H1 & H2 & _) H. lia. Qed.

Lemma sym_ok_kind_bounds k c : sym_ok k c ->
  0 <= ss_nbAdd c <= (match k with K_OF => 31 | _ => 16 end) /\
  0 <= ss_base c /\ ss_base c + 2^(ss_nbAdd c) <= (match k with K_OF => 2^32 - 2 | K_LL => 2^17 | K_ML => 2^17 + 3 end) /\
  (match k with
   | K_OF => (ss_nbAdd c = 0 -> ss_base c = 0) /\ (ss_nbAdd c = 1 -> ss_base c = 1) /\ (2 <= ss_nbAdd c -> ss_base c = 2^(ss_nbAdd c) - 3)
   | K_LL => True
   | K_ML => 3 <= ss_base c
   end).
Proof.
  intros (s & Hs & -> & ->).
  assert (In s (zseq (Z.to_nat (kind_max k + 1)) 0)).
  { assert (G : forall n from x, from <= x < from + Z.of_nat n -> In x (zseq n from)).
    { induction n as [|n IH]; intros from x Hx; cbn [zseq In]; [lia|]. destruct (Z.eq_dec from x); [left; auto|right; apply IH; lia]. }
    apply G. destruct k; cbn [kind_max] in *; lia. }
  revert s Hs H. 
  assert (B : forallb (fun s =>
     let b := Znth s (kind_base k) in let a := Znth s (kind_bits k) in
     (0 <=? a) && (a <=? (match k with K_OF => 31 | _ => 16 end)) && (0 <=? b) &&
     (b + 2^a <=? (match k with K_OF => 2^32 - 2 | K_LL => 2^17 | K_ML => 2^17 + 3 end)) &&
     (match k with
      | K_OF => (negb (a =? 0) || (b =? 0)) && (negb (a =? 1) || (b =? 1)) && (negb (2 <=? a) || (b =? 2^a - 3))
      | K_LL => true
      | K_ML => 3 <=? b
      end)) (zseq (Z.to_nat (kind_max k + 1)) 0) = true) by (destruct k; vm_compute; reflexivity).
  intros s Hs Hin. rewrite forallb_forall in B. specialize (B s Hin). cbv zeta in B.
  rewrite !andb_true_iff in B. destruct B as ((((B1 & B2) & B3) & B4) & B5).
  apply Z.leb_le in B1, B2, B3, B4. repeat split; try lia.
  destruct k; [exact I| |apply Z.leb_le in B5; exact B5].
  rewrite !andb_true_iff, !orb_true_iff, !negb_true_iff in B5. destruct B5 as ((C1 & C2) & C3).
  repeat split.
  - intros E. destruct C1 as [C1|C1]; [apply Z.eqb_neq in C1; lia|apply Z.eqb_eq in C1; exact C1].
  - intros E. destruct C2 as [C2|C2]; [apply Z.eqb_neq in C2; lia|apply Z.eqb_eq in C2; exact C2].
  - intros E. destruct C3 as [C3|C3]; [apply Z.leb_gt in C3; lia|apply Z.eqb_eq in C3; exact C3].
Qed.
