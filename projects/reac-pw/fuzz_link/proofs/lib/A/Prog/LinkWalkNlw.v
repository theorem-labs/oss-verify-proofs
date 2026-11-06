(* reac-pw/fuzz_link, image A: the struct nl_w (link_spec.v NW_*: b[4096] at NW_B = 0, the 8-byte n at NW_N = 4096,
   the 4-byte full at NW_FULL = 4104, NW_SIZE = 4112) as the image-A walks of the three functions that write one
   see it: attr_text, nl_error, and kernel's inlined msg_build.

   Their Posts (attr_text_apost, nl_error_apost, the reply clause of kernel's) ask only `anlw_at m' w bs'`,
   `nlw_wf bs'` and `nw_n bs <= nw_n bs'`: no byte of b is named. So a walk's phase invariant can carry just the
   two fields and the presence of the struct (`nlw_fields`): the 8 bytes at w + NW_N hold n, the 4 bytes at
   w + NW_FULL hold f, 0 <= n <= NL_CHUNK_MAX, 0 <= f <= 1, and every byte of [w, w + NW_SIZE) is present and
   writable. This file turns the Pre's byte list into those fields (`fields_of_anlw`), those fields back into a
   byte list (`anlw_of_fields`), and gives the whole nl_w Post from the fields at the end and the n the Pre read
   (`nlw_post_of_fields`). Image-free: only the segments `segs`.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem LinkWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section n.
Variable segs : list Segment.

(* ==========================================================================
   1. A field of a byte list at an address, as a `val_mem`, and back
   ========================================================================== *)

(* The n bytes of bs from off, read as a little-endian value, are a `val_mem` at a + off. *)
Lemma lwn_val_mem_of_abytes : forall m a bs off (n : nat),
  abytes segs m a bs -> 0 <= off -> (Z.to_nat off + n <= length bs)%nat ->
  val_mem segs m (a + off) n (rdn bs off (Z.of_nat n)).
Proof.
  intros m a bs off n Hab Hoff Hn k Hk.
  destruct Hab as (Ha & Hal & Hb).
  assert (Hll : length (slice bs off (Z.of_nat n)) = n) by (rewrite lw_slice_length by lia; lia).
  assert (Hnth : nth_error (slice bs off (Z.of_nat n)) k = nth_error bs (Z.to_nat off + k))
    by (apply lw_slice_nth; lia).
  destruct (nth_error bs (Z.to_nat off + k)) as [b|] eqn:Eb;
    [|exfalso; apply nth_error_None in Eb; lia].
  replace (a + off + Z.of_nat k) with (a + Z.of_nat (Z.to_nat off + k)) by lia.
  rewrite (Hb (Z.to_nat off + k)%nat ltac:(lia)), Eb. f_equal.
  pose proof (nth_error_le_byte (slice bs off (Z.of_nat n)) k b Hnth) as Hbv.
  pose proof (bytes_le_to_Z_bound (slice bs off (Z.of_nat n))) as Hbd. rewrite Hll in Hbd.
  pose proof (bytes_le_to_Z_nonneg (slice bs off (Z.of_nat n))) as Hnn.
  unfold rdn. rewrite (le_byte_small (bytes_le_to_Z (slice bs off (Z.of_nat n))) n k ltac:(lia) Hk).
  apply bv_eq. rewrite Hbv, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* A `val_mem` at a + off of a value in range is the read of the byte list at a. *)
Lemma lwn_rdn_of_val_mem : forall m a bs off (n : nat) v,
  abytes segs m a bs -> 0 <= off -> (Z.to_nat off + n <= length bs)%nat ->
  0 <= v < 2 ^ (8 * Z.of_nat n) -> val_mem segs m (a + off) n v ->
  rdn bs off (Z.of_nat n) = v.
Proof.
  intros m a bs off n v (Ha & Hal & Hb) Hoff Hn Hv HV.
  apply rdn_of_vals; [exact Hoff | lia | exact Hv |].
  intros k Hk. rewrite <- (Hb (Z.to_nat off + k)%nat ltac:(lia)).
  replace (a + Z.of_nat (Z.to_nat off + k)) with (a + off + Z.of_nat k) by lia.
  exact (HV k Hk).
Qed.

(* ==========================================================================
   2. The fields of a struct nl_w
   ========================================================================== *)

(* Every byte of [w, w + NW_SIZE) is present and writable. *)
Definition nlw_present (m : word -> option byte) (w : Z) : Prop :=
  forall i, 0 <= i < NW_SIZE -> (exists b, mbyte segs m (w + i) = Some b) /\ writable_at segs m (w + i).

(* What a phase invariant of an nl_w walk carries: the struct is present and writable, n is the 8 bytes at
   w + NW_N, f the 4 bytes at w + NW_FULL, and both are in nlw_wf's ranges. *)
Definition nlw_fields (m : word -> option byte) (w n f : Z) : Prop :=
  0 <= w /\ w + NW_SIZE <= 2 ^ 64 /\ nlw_present m w /\
  val_mem segs m (w + NW_N) 8 n /\ val_mem segs m (w + NW_FULL) 4 f /\
  0 <= n <= NL_CHUNK_MAX /\ 0 <= f <= 1.

(* THE FIELDS OF THE PRE'S STRUCT: the two val_mem facts, their ranges, and the presence and writability of
   the struct's bytes. *)
Lemma fields_of_anlw : forall m w bs,
  anlw_at segs m w bs -> nlw_wf bs ->
  val_mem segs m (w + NW_N) 8 (nw_n bs) /\ val_mem segs m (w + NW_FULL) 4 (nw_full bs) /\
  0 <= nw_n bs <= NL_CHUNK_MAX /\ 0 <= nw_full bs <= 1 /\
  0 <= w /\ w + NW_SIZE <= 2 ^ 64 /\
  (forall i, 0 <= i < NW_SIZE -> (exists b, mbyte segs m (w + i) = Some b) /\ writable_at segs m (w + i)).
Proof.
  intros m w bs ((Hab & Hwr) & Hlen) (Hn & Hf).
  pose proof Hab as (Hw0 & Hwl & Hb).
  unfold NW_SIZE in Hlen.
  split; [exact (lwn_val_mem_of_abytes m w bs NW_N 8%nat Hab ltac:(unfold NW_N; lia)
                   ltac:(unfold NW_N; lia))|].
  split; [exact (lwn_val_mem_of_abytes m w bs NW_FULL 4%nat Hab ltac:(unfold NW_FULL; lia)
                   ltac:(unfold NW_FULL; lia))|].
  split; [exact Hn|]. split; [exact Hf|]. split; [exact Hw0|].
  split; [unfold NW_SIZE; lia|].
  intros i Hi. unfold NW_SIZE in Hi. split.
  - destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Eb;
      [|exfalso; apply nth_error_None in Eb; lia].
    exists b. rewrite <- Eb. replace (w + i) with (w + Z.of_nat (Z.to_nat i)) by lia. apply Hb. lia.
  - apply Hwr. lia.
Qed.

Lemma nlw_fields_of_anlw : forall m w bs,
  anlw_at segs m w bs -> nlw_wf bs -> nlw_fields m w (nw_n bs) (nw_full bs).
Proof.
  intros m w bs HA HW.
  destruct (fields_of_anlw m w bs HA HW) as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  repeat split; try assumption; try lia; apply H7; assumption.
Qed.

(* THE STRUCT FROM ITS FIELDS: a byte list at w of NW_SIZE bytes (the bytes of memory), well formed, whose n
   and full are the two values. *)
Lemma anlw_of_fields : forall m w n' f',
  (forall i, 0 <= i < NW_SIZE -> (exists b, mbyte segs m (w + i) = Some b) /\ writable_at segs m (w + i)) ->
  val_mem segs m (w + NW_N) 8 n' -> val_mem segs m (w + NW_FULL) 4 f' ->
  0 <= n' <= NL_CHUNK_MAX -> 0 <= f' <= 1 -> 0 <= w -> w + NW_SIZE <= 2 ^ 64 ->
  exists bs', anlw_at segs m w bs' /\ nlw_wf bs' /\ nw_n bs' = n' /\ nw_full bs' = f'.
Proof.
  intros m w n' f' Hp Hn Hf Hnr Hfr Hw0 Hwl.
  set (bs' := abytes_of segs m w (Z.to_nat NW_SIZE)).
  assert (Hlen : length bs' = Z.to_nat NW_SIZE) by apply abytes_of_length.
  assert (Hab : abytes segs m w bs').
  { apply abytes_of_abytes; [exact Hw0 | unfold NW_SIZE in *; lia |].
    intros i Hi. destruct (Hp (Z.of_nat i) ltac:(unfold NW_SIZE in *; lia)) as (Hb & _). exact Hb. }
  assert (HN : nw_n bs' = n').
  { unfold nw_n, fld_u64. change 8 with (Z.of_nat 8).
    apply (lwn_rdn_of_val_mem m w bs' NW_N 8%nat n' Hab ltac:(unfold NW_N; lia));
      [rewrite Hlen; unfold NW_N, NW_SIZE; lia | unfold NL_CHUNK_MAX in Hnr; cbn; lia | exact Hn]. }
  assert (HF : nw_full bs' = f').
  { unfold nw_full, fld_u32. change 4 with (Z.of_nat 4).
    apply (lwn_rdn_of_val_mem m w bs' NW_FULL 4%nat f' Hab ltac:(unfold NW_FULL; lia));
      [rewrite Hlen; unfold NW_FULL, NW_SIZE; lia | cbn; lia | exact Hf]. }
  exists bs'. split; [|split; [unfold nlw_wf; rewrite HN, HF; lia | split; [exact HN | exact HF]]].
  split; [split; [exact Hab|] | rewrite Hlen; unfold NW_SIZE; lia].
  rewrite Hlen. intros i Hi. destruct (Hp i ltac:(unfold NW_SIZE in *; lia)) as (_ & Hw). exact Hw.
Qed.

Lemma anlw_of_nlw_fields : forall m w n f,
  nlw_fields m w n f ->
  exists bs', anlw_at segs m w bs' /\ nlw_wf bs' /\ nw_n bs' = n /\ nw_full bs' = f.
Proof.
  intros m w n f (Hw0 & Hwl & Hp & Hn & Hf & Hnr & Hfr).
  exact (anlw_of_fields m w n f Hp Hn Hf Hnr Hfr Hw0 Hwl).
Qed.

(* The n of the Pre's struct is the value the walk read at w + NW_N. *)
Lemma anlw_nw_n_eq : forall m w bs n,
  anlw_at segs m w bs -> val_mem segs m (w + NW_N) 8 n -> 0 <= n < 2 ^ 64 -> nw_n bs = n.
Proof.
  intros m w bs n ((Hab & _) & Hlen) HV Hr.
  unfold nw_n, fld_u64. change 8 with (Z.of_nat 8).
  apply (lwn_rdn_of_val_mem m w bs NW_N 8%nat n Hab ltac:(unfold NW_N; lia));
    [unfold NW_N, NW_SIZE in *; lia | cbn; lia | exact HV].
Qed.

(* THE nl_w POST (attr_text_apost, nl_error_apost): from the fields at the end memory m' and the n0 the Pre's
   struct holds at m, with n0 <= n'. *)
Lemma nlw_post_of_fields : forall m m' w n0 n' f',
  val_mem segs m (w + NW_N) 8 n0 -> 0 <= n0 -> n0 <= n' ->
  nlw_fields m' w n' f' ->
  forall bs, anlw_at segs m w bs ->
    exists bs', anlw_at segs m' w bs' /\ nlw_wf bs' /\ nw_n bs <= nw_n bs'.
Proof.
  intros m m' w n0 n' f' HV0 Hn0 Hle HF bs HA.
  pose proof HF as (_ & _ & _ & _ & _ & Hnr & _).
  rewrite (anlw_nw_n_eq m w bs n0 HA HV0 ltac:(unfold NL_CHUNK_MAX in Hnr; lia)).
  destruct (anlw_of_nlw_fields m' w n' f' HF) as (bs' & HA' & HW' & HN' & _).
  exists bs'. split; [exact HA'|]. split; [exact HW'|]. rewrite HN'. exact Hle.
Qed.

(* ==========================================================================
   3. Carrying the fields to a later memory
   ========================================================================== *)

(* A later memory that agrees on every byte of the struct, and keeps it writable, keeps the fields. *)
Lemma nlw_fields_agree : forall m m2 w n f,
  nlw_fields m w n f ->
  (forall i, 0 <= i < NW_SIZE -> mbyte segs m2 (w + i) = mbyte segs m (w + i) /\
     (writable_at segs m (w + i) -> writable_at segs m2 (w + i))) ->
  nlw_fields m2 w n f.
Proof.
  intros m m2 w n f (Hw0 & Hwl & Hp & Hn & Hf & Hnr & Hfr) Hag.
  split; [exact Hw0|]. split; [exact Hwl|].
  split; [|split; [|split; [|split; [exact Hnr | exact Hfr]]]].
  - intros i Hi. destruct (Hp i Hi) as ((b & Hb) & Hw). destruct (Hag i Hi) as (Heq & Hwk).
    split; [exists b; rewrite Heq; exact Hb | exact (Hwk Hw)].
  - intros k Hk. destruct (Hag (NW_N + Z.of_nat k) ltac:(unfold NW_N, NW_SIZE; lia)) as (Heq & _).
    replace (w + NW_N + Z.of_nat k) with (w + (NW_N + Z.of_nat k)) by lia. rewrite Heq.
    replace (w + (NW_N + Z.of_nat k)) with (w + NW_N + Z.of_nat k) by lia. exact (Hn k Hk).
  - intros k Hk. destruct (Hag (NW_FULL + Z.of_nat k) ltac:(unfold NW_FULL, NW_SIZE; lia)) as (Heq & _).
    replace (w + NW_FULL + Z.of_nat k) with (w + (NW_FULL + Z.of_nat k)) by lia. rewrite Heq.
    replace (w + (NW_FULL + Z.of_nat k)) with (w + NW_FULL + Z.of_nat k) by lia. exact (Hf k Hk).
Qed.

End n.
