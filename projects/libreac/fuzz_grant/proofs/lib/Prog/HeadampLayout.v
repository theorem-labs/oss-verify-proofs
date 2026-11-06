(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the head-amp table layout and the contract and walk of reac_headamp_tx_effective on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxEffective.v; 4 of its 175 lines of code are new or changed and 391 lines of the source are left out. *)
(* The layout of the head-amp table struct reac_headamp_tx, and the facts about it, address-free, for the walks of
   BOTH images.

   struct reac_headamp_tx (include/reac/reac_headamp_tx.h:121-151), as the compiler lays it out: three 48 x 3 byte
   arrays, then the scalars.
     0..143 value[48][3], 144..287 set[48][3], 288..431 dirty[48][3], 432 active (4), 436 replay_base (1),
     437 replay_width (1), 440 replay_idx (4), 444 replay_wait (4), 448 replay_set_only (1), 449 scene_base (1),
     450 scene_width (1), 452 resweep_period (4), 456 resweep_wait (4);
   460 bytes in all, 438, 439 and 451 being padding.

   The same C struct is laid out the same way in every build of the unit, so nothing here holds an address or an
   image value: `segs` is a Variable and no statement names an image. Ported VERBATIM, with their proofs, from
   image A's walk lib/A/Prog/HeadampTxEffective.v (a working branch d98082bd58b): the layout and its helpers :33-107,
   Section L :109-202, and lay_inside_TX / tx_fbyte_range :263-273, which lie inside that file's walk section but
   name none of its section variables. Image A's file keeps its own copy; this one is what an image-B file uses,
   so that no image-A module enters an image-B Require closure. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition TX_SIZE : Z := 460.
Definition LAY_TX : layout_t :=
  map (fun i => (Z.of_nat i, 1%N)) (seq 0 432) ++
  [ (432, 4%N); (436, 1%N); (437, 1%N); (440, 4%N); (444, 4%N);
    (448, 1%N); (449, 1%N); (450, 1%N); (452, 4%N); (456, 4%N) ].

(* The field value a byte list gives: the little-endian number of its bytes. *)
Fixpoint le_from (T : list byte) (o : Z) (n : nat) : Z :=
  match n with O => 0 | S n' => tb T o + 256 * le_from T (o + 1) n' end.
Definition lay_vals (lay : layout_t) (T : list byte) : list Z :=
  map (fun f => le_from T (fst f) (N.to_nat (snd f))) lay.
Definition tx_vals (T : list byte) : list Z := lay_vals LAY_TX T.

(* The bytes a layout names. *)
Definition lay_byte (lay : layout_t) (i : Z) : bool :=
  existsb (fun f => (fst f <=? i) && (i <? fst f + Z.of_N (snd f))) lay.
Definition tx_fbyte (i : Z) : bool := lay_byte LAY_TX i.

Lemma tb_range : forall T i, 0 <= tb T i < 256.
Proof.
  intros T i. unfold tb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) T (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma tb_nth : forall T i, Z_to_bv 8 (tb T i) = nth (Z.to_nat i) T (Z_to_bv 8 0).
Proof. intros T i. unfold tb. apply Z_to_bv_bv_unsigned. Qed.

Lemma le_from_range : forall n T o, 0 <= le_from T o n < 2 ^ (8 * Z.of_nat n).
Proof.
  induction n as [|n IH]; intros T o; cbn [le_from].
  - cbn. lia.
  - pose proof (tb_range T o) as Hb. specialize (IH T (o + 1)).
    replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
Qed.

Lemma le_byte_le_from : forall n T o k, (k < n)%nat ->
  YO0f.le_byte (le_from T o n) n k = tb T (o + Z.of_nat k).
Proof.
  induction n as [|n IH]; intros T o k Hk; [lia|].
  pose proof (le_from_range (S n) T o) as Hr.
  unfold YO0f.le_byte. rewrite (Z.mod_small _ _ Hr).
  destruct k as [|k].
  - cbn [le_from]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z.add_0_r.
    pose proof (tb_range T o) as Hb. pose proof (le_from_range n T (o + 1)).
    replace (tb T o + 256 * le_from T (o + 1) n) with (tb T o + le_from T (o + 1) n * 256) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - pose proof (IH T (o + 1) k ltac:(lia)) as IHk.
    unfold YO0f.le_byte in IHk. rewrite (Z.mod_small _ _ (le_from_range n T (o + 1))) in IHk.
    replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite <- Z.shiftr_shiftr by lia.
    replace (Z.shiftr (le_from T o (S n)) 8) with (le_from T (o + 1) n).
    2: { cbn [le_from]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
         pose proof (tb_range T o).
         replace (tb T o + 256 * le_from T (o + 1) n) with (le_from T (o + 1) n * 256 + tb T o) by lia.
         rewrite Z_div_plus_full_l by lia.
         rewrite (Z.div_small (tb T o) 256) by lia. lia. }
    rewrite IHk. f_equal. lia.
Qed.

(* A byte a store leaves in the table: the k-th byte of the stored word. *)
Lemma le4_byte_of_word : forall (v : word) (k : nat), (k < 4)%nat ->
  nth k (Mem.le4 v) (Z_to_bv 8 0) = YP09.byte_of_word v (Z.of_nat k).
Proof.
  intros v k Hk. unfold Mem.le4, YP09.byte_of_word.
  destruct k as [|[|[|[|k]]]]; try lia; cbn [Z_to_le_bytes nth Z.of_nat];
    f_equal; rewrite ?Z.shiftr_div_pow2 by lia; try reflexivity.
Qed.

Lemma le1_byte_of_word : forall (v : word),
  nth 0 (Mem.le1 v) (Z_to_bv 8 0) = YP09.byte_of_word v 0.
Proof.
  intros v. unfold Mem.le1, YP09.byte_of_word. cbn [Z_to_le_bytes nth].
  change (8 * 0) with 0. rewrite ?Z.shiftr_0_r. reflexivity.
Qed.

Section L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* The bytes of a layout, read one at a time. *)
Definition fields_at (m : word -> option byte) (a : Z) (lay : layout_t) (T : list byte) : Prop :=
  forall o w, In (o, w) lay -> forall k, (k < N.to_nat w)%nat ->
    mbyte segs m (a + (o + Z.of_nat k)) = Some (nth (Z.to_nat (o + Z.of_nat k)) T (Z_to_bv 8 0)).

Definition bytes_at_lay (m : word -> option byte) (a : Z) (lay : layout_t) (T : list byte) : Prop :=
  forall i, lay_byte lay i = true -> mbyte segs m (a + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0)).

Lemma obj_at_fields : forall lay, lay_widths_ok lay = true ->
  forall m a T, obj_at segs m a lay (lay_vals lay T) <-> fields_at m a lay T.
Proof.
  induction lay as [|[o w] lay IH]; intros Hw m a T.
  - cbn [lay_vals map obj_at]. split; [intros _ o' w' Hin; destruct Hin | intros _; exact I].
  - unfold lay_widths_ok in Hw. cbn [forallb] in Hw. apply andb_prop in Hw as [Hw1 Hw2].
    cbn [fst snd] in Hw1. apply Z.leb_le in Hw1.
    cbn [lay_vals map obj_at fst snd].
    assert (Hfield : field_ok segs m a (o, w) (le_from T o (N.to_nat w)) <->
      (forall k, (k < N.to_nat w)%nat ->
        mbyte segs m (a + (o + Z.of_nat k)) = Some (nth (Z.to_nat (o + Z.of_nat k)) T (Z_to_bv 8 0)))).
    { unfold field_ok. cbn [fst snd]. split.
      - intros [Hv _] k Hk. specialize (Hv k Hk).
        replace (a + (o + Z.of_nat k)) with (a + o + Z.of_nat k) by lia. rewrite Hv.
        rewrite (le_byte_le_from (N.to_nat w) T o k Hk). rewrite tb_nth. reflexivity.
      - intros H. split.
        + intros k Hk. specialize (H k Hk).
          replace (a + o + Z.of_nat k) with (a + (o + Z.of_nat k)) by lia. rewrite H.
          rewrite (le_byte_le_from (N.to_nat w) T o k Hk). rewrite tb_nth. reflexivity.
        + pose proof (le_from_range (N.to_nat w) T o) as Hr.
          rewrite N_nat_Z in Hr. exact Hr. }
    rewrite (IH Hw2 m a T). split.
    + intros [Hf Hr] o' w' Hin k Hk. destruct Hin as [Heq | Hin].
      * injection Heq as <- <-. apply (proj1 Hfield Hf k Hk).
      * exact (Hr o' w' Hin k Hk).
    + intros H. split.
      * apply (proj2 Hfield). intros k Hk. apply (H o w (or_introl eq_refl) k Hk).
      * intros o' w' Hin k Hk. apply (H o' w' (or_intror Hin) k Hk).
Qed.

Lemma fields_bytes_lay : forall lay m a T, fields_at m a lay T <-> bytes_at_lay m a lay T.
Proof.
  intros lay m a T. split.
  - intros H i Hi. unfold lay_byte in Hi. apply existsb_exists in Hi as [[o w] [Hin Hb]].
    cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    specialize (H o w Hin (Z.to_nat (i - o)) ltac:(lia)).
    replace (o + Z.of_nat (Z.to_nat (i - o))) with i in H by lia. exact H.
  - intros H o w Hin k Hk. apply H. unfold lay_byte. apply existsb_exists. exists (o, w).
    split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.

Lemma tx_obj_bytes : forall m a T,
  obj_at segs m a LAY_TX (tx_vals T) <->
  (forall i, tx_fbyte i = true -> mbyte segs m (a + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0))).
Proof.
  intros m a T. unfold tx_vals, tx_fbyte.
  rewrite (obj_at_fields LAY_TX ltac:(vm_compute; reflexivity) m a T).
  exact (fields_bytes_lay LAY_TX m a T).
Qed.

(* One byte of the three arrays, as a one-byte field value. *)
Lemma tx_cell_val : forall m a T i, 0 <= i < 432 ->
  obj_at segs m a LAY_TX (tx_vals T) -> val_mem segs m (a + i) 1 (tb T i).
Proof.
  intros m a T i Hi Ho. apply (proj1 (tx_obj_bytes m a T)) with (i := i) in Ho.
  - intros k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Ho.
    rewrite <- tb_nth. f_equal. f_equal. unfold YO0f.le_byte.
    change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
    change (2 ^ (8 * Z.of_nat 1)) with 256. pose proof (tb_range T i).
    rewrite !Z.mod_small by lia. reflexivity.
  - unfold tx_fbyte, lay_byte. apply existsb_exists. exists (i, 1%N).
    split.
    + apply in_or_app. left. apply in_map_iff. exists (Z.to_nat i).
      split; [f_equal; lia | apply in_seq; lia].
    + cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.

(* The bytes a chunk of a region fixes. *)
Lemma byte_of_region : forall E m n b cs lo hi wlo whi od (w : N) e i,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> 0 <= i < Z.of_N w ->
  mbyte segs m (b + od + i) = Some (YP09.byte_of_word (sv_denot E e) i).
Proof.
  intros E m n b cs lo hi wlo whi od w e i HR Hb Hin Hi.
  unfold region_ok in HR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR.
  destruct HR as (_ & _ & _ & HF). rewrite Hb in HF.
  rewrite Forall_forall in HF. specialize (HF _ Hin).
  unfold chunk_ok in HF. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in HF.
  destruct (HF i Hi) as (bb & Hc & Hm). cbn [cbyte] in Hc. injection Hc as <-. exact Hm.
Qed.

End L.

Lemma lay_inside_TX : lay_inside LAY_TX 460 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tx_fbyte_range : forall i, tx_fbyte i = true -> 0 <= i < 460.
Proof.
  intros i Hi. unfold tx_fbyte, lay_byte in Hi. apply existsb_exists in Hi as [f [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (proj1 (forallb_forall _ LAY_TX) lay_inside_TX f Hin) as Hf. cbn beta in Hf.
  apply andb_prop in Hf as [F1 F2]. apply Z.leb_le in F1. apply Z.leb_le in F2.
  pose proof (N2Z.is_nonneg (snd f)). lia.
Qed.
