(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatExec StoreOk Frame ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import MState Mem Cells Step Frame Image. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFix.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Lemma u64_lit : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition off_image (x : Z) : Prop := (x + 1 <= 0x10000 \/ 0x66000 <= x)%Z.
Definition rw_data (x : Z) : Prop := (0x32000 <= x < 0x66000)%Z.

Lemma find_segment_skip : forall seg rest a n,
  (0 < n)%Z ->
  (a + n <= Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= a)%Z ->
  find_segment (seg :: rest) a n = find_segment rest a n.
Proof.
  intros seg rest a n Hn H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
    cbn [andb]; try reflexivity; lia.
Qed.

Lemma find_segment_off : forall a n, (0 < n)%Z -> (a + n <= 0x10000 \/ 0x66000 <= a)%Z ->
  find_segment s0segs a n = None.
Proof.
  intros a n Hn H. unfold s0segs, Ubsan.M.loaded_segments, Ubsan_loaded_segments.
  rewrite 4 find_segment_skip; [reflexivity | exact Hn | | exact Hn | | exact Hn | | exact Hn |];
    cbn [seg_base seg_size Ubsan_segment_000 Ubsan_segment_001 Ubsan_segment_002 Ubsan_segment_003]; lia.
Qed.

(* [comment removed for export] *)

Lemma wview_off : forall M (x : word), off_image (bv_unsigned x) -> wview s0segs M x = M x.
Proof.
  intros M x Hx. unfold wview. destruct (M x); [reflexivity|].
  rewrite find_segment_off; [reflexivity | lia | unfold off_image in Hx; lia].
Qed.

(* [comment removed for export] *)
Lemma find_segment_rw2 : forall a, (0x32000 <= a < 0x33000)%Z -> find_segment s0segs a 1 = Some Ubsan_segment_002.
Proof.
  intros a H. unfold s0segs, Ubsan.M.loaded_segments, Ubsan_loaded_segments.
  rewrite 2 find_segment_skip; try (cbn; lia).
  cbn [find_segment seg_base seg_size Ubsan_segment_002 Z.of_N Pos.of_succ_nat Pos.succ].
  change (Z.of_N 204800) with 204800%Z. change (Z.of_N 4096) with 4096%Z.
  destruct (Z.leb_spec 204800 a); destruct (Z.leb_spec (a + 1) (204800 + 4096)); cbn [andb]; try reflexivity; lia.
Qed.
Lemma find_segment_rw3 : forall a, (0x33000 <= a < 0x66000)%Z -> find_segment s0segs a 1 = Some Ubsan_segment_003.
Proof.
  intros a H. unfold s0segs, Ubsan.M.loaded_segments, Ubsan_loaded_segments.
  rewrite 3 find_segment_skip; try (cbn; lia).
  cbn [find_segment seg_base seg_size Ubsan_segment_003].
  change (Z.of_N 208896) with 208896%Z. change (Z.of_N 208896) with 208896%Z.
  destruct (Z.leb_spec 208896 a); destruct (Z.leb_spec (a + 1) (208896 + 208896)); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stk_of_store_ok_off : forall M lo n,
  (0 <= lo)%Z -> (lo + Z.of_nat n <= 2 ^ 64)%Z -> (0x66000 <= lo)%Z ->
  store_ok s0segs M (Z_to_bv 64 lo) n = true ->
  stk s0segs M lo (lo + Z.of_nat n).
Proof.
  intros M lo n Hlo Hhi Himg Hok. split; [lia|]. split; [lia|]. intros a Ha.
  assert (Hw : wview s0segs M (wa a) <> None).
  { apply (store_ok_all s0segs M n (Z_to_bv 64 lo)); [rewrite u64_lit; lia | exact Hok | unfold wa; rewrite !u64_lit; lia]. }
  split; [exact Hw|].
  rewrite wview_off in Hw by (unfold wa, off_image; rewrite u64_lit; lia).
  unfold mrd. destruct (M (wa a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition img_pristine (m : word -> option byte) (lo hi : Z) : Prop :=
  forall a, (lo <= a < hi)%Z -> m (wa a) = None.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma image_bytes_nth : forall n A bs i, image_bytes s0segs A n = Some bs -> (i < n)%nat ->
  seg_rom s0segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs i H Hi; [lia|].
  cbn [image_bytes] in H.
  destruct (seg_rom s0segs (wa A)) as [b|] eqn:E; [|discriminate].
  destruct (image_bytes s0segs (A + 1) n) as [bs'|] eqn:E'; [|discriminate].
  injection H as <-. destruct i as [|i].
  - cbn. rewrite Z.add_0_r. exact E.
  - cbn. replace (A + Z.of_nat (S i))%Z with (A + 1 + Z.of_nat i)%Z by lia. apply IH; [exact E'| lia].
Qed.

(* [comment removed for export] *)
Lemma bytes_at_pristine : forall m A (n : nat) bs,
  img_pristine m A (A + Z.of_nat n) -> image_bytes s0segs A n = Some bs ->
  (0 <= A)%Z -> (A + Z.of_nat n <= 2 ^ 64)%Z ->
  bytes_at s0segs m A bs.
Proof.
  intros m A n bs Hp Himg HA Hn.
  assert (Hlen : length bs = n) by (eapply image_bytes_length; exact Himg).
  split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hp by lia. apply (image_bytes_nth n); [exact Himg| lia].
Qed.

(* [comment removed for export] *)
Lemma segment_read_bytes_1 : forall bytes off,
  segment_read_bytes bytes off 1 = match segment_byte_at bytes off with Some b => Some [b] | None => None end.
Proof. intros. cbn [segment_read_bytes]. destruct (segment_byte_at bytes off); reflexivity. Qed.

Lemma wview_rw_data_pristine : forall m a, rw_data a -> m (wa a) = None ->
  wview s0segs m (wa a) = seg_rom s0segs (wa a).
Proof.
  intros m a Ha Hm. unfold wview. rewrite Hm. unfold wa; rewrite u64_lit by (unfold rw_data in Ha; lia).
  unfold seg_rom, memory_read, wa. rewrite u64_lit by (unfold rw_data in Ha; lia).
  change (Z.of_N 1) with 1%Z. change (N.to_nat 1) with 1%nat.
  destruct (Z.lt_ge_cases a 0x33000) as [Hlt|Hge].
  - rewrite find_segment_rw2 by (unfold rw_data in Ha; lia). cbn [seg_writable seg_readable Ubsan_segment_002 seg_perms seg_bytes seg_base string_has Ascii.eqb].
    cbv beta iota. rewrite segment_read_bytes_1. destruct (segment_byte_at _ _) ; reflexivity.
  - rewrite find_segment_rw3 by (unfold rw_data in Ha; lia). cbn [seg_writable seg_readable Ubsan_segment_003 seg_perms seg_bytes seg_base string_has Ascii.eqb].
    cbv beta iota. rewrite segment_read_bytes_1. destruct (segment_byte_at _ _); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_pristine : forall m A (n : nat) bs,
  img_pristine m A (A + Z.of_nat n) -> (0x32000 <= A)%Z -> (A + Z.of_nat n <= 0x66000)%Z ->
  image_bytes s0segs A n = Some bs ->
  rw_cells s0segs m A [CB n bs].
Proof.
  intros m A n bs Hp H1 H2 Himg.
  assert (Hlen : length bs = n) by (eapply image_bytes_length; exact Himg).
  split.
  - split; [cbn; split; [exact Hlen| exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (bytes_at_pristine m A n bs Hp Himg); lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. rewrite wview_rw_data_pristine; [| unfold rw_data; lia | apply Hp; lia].
    replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite (image_bytes_nth n A bs (Z.to_nat i) Himg) by lia.
    destruct (nth_error bs (Z.to_nat i)) eqn:E; [discriminate|]. apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_at_of_rdn : forall n m (a : Z) bs,
  rdn s0segs m (wa a) n = Some bs -> (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  bytes_at s0segs m a bs.
Proof.
  induction n as [|n IH]; intros m a bs H Ha Hn.
  - cbn in H. injection H as <-. apply bytes_at_nil. lia.
  - rewrite rdn_unfold in H.
    destruct (mrd s0segs m (wa a)) as [b|] eqn:E; [|discriminate].
    rewrite wa_succ in H.
    destruct (rdn s0segs m (wa (a + 1)) n) as [r|] eqn:E'; [|discriminate].
    injection H as <-.
    change (b :: r) with ([b] ++ r). apply (proj2 (bytes_at_app _ _ _ _ _)). split.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn. rewrite Z.add_0_r. exact E.
    + cbn [length]. replace (a + Z.of_nat 1)%Z with (a + 1)%Z by lia. apply IH; [exact E'| lia | lia].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_C8_of_rdn : forall m (a : Z) (v : word),
  rdn s0segs m (wa a) 8 = Some (word_to_le_bytes 8 v) -> wr_at s0segs m a 8 ->
  rw_cells s0segs m a [C8 v].
Proof.
  intros m a v H W. cps_pose W as (Ha & Hn & _). split.
  - split; [cbn; exact (conj I I) |]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    unfold le8. apply (bytes_at_of_rdn 8); [exact H | lia | lia].
  - cbn. exact W.
Qed.

Lemma rw_cells_C4_of_rdn : forall m (a : Z) (v : word),
  rdn s0segs m (wa a) 4 = Some (word_to_le_bytes 4 v) -> wr_at s0segs m a 4 ->
  rw_cells s0segs m a [C4 v].
Proof.
  intros m a v H W. cps_pose W as (Ha & Hn & _). split.
  - split; [cbn; exact (conj I I) |]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    unfold le4. replace (Z_to_le_bytes 4 (bv_unsigned v)) with (word_to_le_bytes 4 v) by reflexivity.
    apply (bytes_at_of_rdn 4); [exact H | lia | lia].
  - cbn. exact W.
Qed.

(* [comment removed for export] *)
Lemma wr_at_of_stk : forall m lo hi A n,
  stk s0segs m lo hi -> (lo <= A)%Z -> (A + n <= hi)%Z -> (0 <= n)%Z -> wr_at s0segs m A n.
Proof.
  (intros m lo hi A n; cps_intros (H0 & H1 & H); intros HA Hn Hnn). split; [lia|]. split; [lia|].
  intros i Hi. apply (proj1 (H (A + i)%Z ltac:(lia))).
Qed.

(* [comment removed for export] *)
Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells s0segs m A cs1 -> rw_cells s0segs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells s0segs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] R1] [[W2 B2] R2].
  assert (L1 : length (cells_bytes cs1) = cells_size cs1) by (apply cells_bytes_length; exact W1).
  split.
  - split.
    + clear -W1 W2. induction cs1 as [|c cs1 IH]; cbn in *; [exact W2| split; [exact (proj1 W1)| apply IH; exact (proj2 W1)]].
    + rewrite cells_bytes_app. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B1|]. rewrite L1. exact B2.
  - rewrite cells_size_app. cps_destruct R1 as (A1 & A2 & H1). cps_destruct R2 as (A3 & A4 & H2).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hl|Hg].
    + apply H1. lia.
    + replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply H2. lia.
Qed.
