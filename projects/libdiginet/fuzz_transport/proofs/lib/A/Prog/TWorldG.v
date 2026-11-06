(* The world relation of the ASan images, over any table of payload rows.

   The plain model's world Bw (TModel/TWorld.v) is the plain .bss region of W_LEN bytes, every harness global at a
   literal offset. On an ASan image the same 18 globals are separate registered globals at other addresses, each
   followed by its redzone. A table T holds one row (o, b, n) per global: o its offset in the world, b its base in
   the image, n its payload length. tw_at T rd Bw: Bw has W_LEN bytes, and every payload byte b + i that the image's
   read view rd shows is the world's byte at o + i. The 7 world bytes that no payload covers (tw_pad: the 3 bytes
   after the one-byte g_fail_next and the 4 bytes between GOT and OW) are left free; no world accessor reads them
   (tw_pad_free).

   rd is a read view, one byte value per address (Z -> option Z). Two views occur: the core's
   aview segs (w_H W) mem = fun a => option_map bv_unsigned (mbyte segs (mrestrict (w_H W) mem) a) (the G-form and
   donor-form statements), and the machine's view fun a => option_map bv_unsigned (mrd segs m (wa a)) (the leaf
   form's evt runs over raw memory m). tw_at and most lemmas take rd abstractly; tw_read_val / tw_garr8 are for
   every view option_map bv_unsigned (mbyte segs mm a) (aview by unfolding, mm := mrestrict ..), tw_bytes_at and
   tw_kept_munch for the machine's view.

   Contents.
   - tw_ok T: every row inside the world and the address space, rows pairwise disjoint in the world AND in the
     image; decided by tw_okb (tw_okb_ok).
   - Loads inside ONE payload: tw_read_bytes (the bytes are sub Bw (o + k) m), tw_read (in the rd32 / rd64 shape:
     byte j is le_byte (u_at Bw (o + k) m) m j), tw_read_val (val_mem of u_at), tw_garr8, and tw_bytes_at (at the
     machine's view: bytes_at segs m (b + k) (sub Bw (o + k) c), the fact the kit's load step reads through
     bytes_at_read).
     Register values: a load step leaves le_bytes_to_word of the loaded bytes, extracted and extended
     (Riscv/Sem.v load_val); ld_world / lw_world / lwu_world / lh_world / lhu_world / lb_world / lbu_world turn that
     form of sub B k n into TWorld's accessor value (u_at, s32_at, the signed wrap of u_at). These are the statements
     of TModel/TWorldMem.v's wm_ld .. wm_lb, which a walk of these images does not Require (TWorldMem redefines the
     kit's load / store tactics). tw_lw / tw_lwu / tw_lh / tw_lhu / tw_lb / tw_lbu: the same values from
     Z_to_bv w (u_at ..).
   - Writes inside ONE payload: tw_upd (any bytes, nat-indexed), tw_write (a store of m bytes of v: put m v),
     tw_fill (any span, Z-indexed: the __asan_memcpy post), tw_fill_set (a memset of c: repeat (Z_to_bv 8 c)),
     tw_fill_zero (a memset of 0: put L 0), tw_fill_z (a span copied from bytes known as a list of Z, garr8's form).
     Each takes the new bytes on the written span and rd unchanged on every other payload byte.
   - tw_kept / tw_kept_rows: rd unchanged on the payloads keeps Bw; tw_kept_munch: at the machine's view, a run
     whose footprint W (munch W m m') misses every payload byte keeps Bw. tw_exists: a view defined on every
     payload byte relates to some world (built byte by byte, padding 0).
   - Build-independent world facts: TW_ROWS (the 18 (offset, payload) pairs; payload = SZ except g_fail_next's one
     byte), TW_ACC (the footprint (address, width) of every reader of TWorld.v and TCb.v's OW_dn_*, indexed readers
     at every index), tw_pad_free, tw_acc_rows (each footprint inside ONE row), tw_cover_rows (every world byte but
     the 7 pad bytes in a row).
   - For a table whose world column is TW_ROWS (map tw_wrow T = TW_ROWS): tw_acc_row, tw_cover; against a list G of
     (base, length) ranges: tw_in_G_of, tw_G_rows_of (both decided), tw_kept_G. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem Bytes Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f YP09 YI04 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TCb.
Import ListNotations.
Open Scope Z_scope.

(* ---- the relation ---- *)

Definition tw_at (T : list (Z * Z * Z)) (rd : Z -> option Z) (Bw : list byte) : Prop :=
  length Bw = Z.to_nat W_LEN /\
  forall o b n i, In (o, b, n) T -> 0 <= i < n ->
    rd (b + i) = Some (bv_unsigned (nth (Z.to_nat (o + i)) Bw (Z_to_bv 8 0))).

Definition tw_row_ok (r : Z * Z * Z) : Prop :=
  let '(o, b, n) := r in 0 <= o /\ 0 < n /\ o + n <= W_LEN /\ 0 <= b /\ b + n <= 2 ^ 64.
Definition tw_disj (r1 r2 : Z * Z * Z) : Prop :=
  let '(o1, b1, n1) := r1 in let '(o2, b2, n2) := r2 in
  (o1 + n1 <= o2 \/ o2 + n2 <= o1) /\ (b1 + n1 <= b2 \/ b2 + n2 <= b1).
Definition tw_ok (T : list (Z * Z * Z)) : Prop := Forall tw_row_ok T /\ ForallOrdPairs tw_disj T.

(* x is a payload byte of the image *)
Definition tw_in (T : list (Z * Z * Z)) (x : Z) : Prop := exists o b n, In (o, b, n) T /\ b <= x < b + n.

Lemma tw_len : forall T rd Bw, tw_at T rd Bw -> length Bw = Z.to_nat W_LEN.
Proof. intros T rd Bw [H _]. exact H. Qed.

(* ---- deciding tw_ok ---- *)

Definition tw_row_okb (r : Z * Z * Z) : bool :=
  let '(o, b, n) := r in (0 <=? o) && (0 <? n) && (o + n <=? W_LEN) && (0 <=? b) && (b + n <=? 2 ^ 64).
Definition tw_disjb (r1 r2 : Z * Z * Z) : bool :=
  let '(o1, b1, n1) := r1 in let '(o2, b2, n2) := r2 in
  ((o1 + n1 <=? o2) || (o2 + n2 <=? o1)) && ((b1 + n1 <=? b2) || (b2 + n2 <=? b1)).
Fixpoint tw_pairsb (T : list (Z * Z * Z)) : bool :=
  match T with [] => true | r :: t => forallb (tw_disjb r) t && tw_pairsb t end.
Definition tw_okb (T : list (Z * Z * Z)) : bool := forallb tw_row_okb T && tw_pairsb T.

Ltac tw_bool H := rewrite ?andb_true_iff, ?orb_true_iff, ?Z.leb_le, ?Z.ltb_lt, ?Z.eqb_eq in H.

Lemma tw_row_okb_ok : forall r, tw_row_okb r = true -> tw_row_ok r.
Proof. intros [[o b] n] H. cbn [tw_row_okb tw_row_ok] in *. tw_bool H. lia. Qed.

Lemma tw_pairsb_ok : forall T, tw_pairsb T = true -> ForallOrdPairs tw_disj T.
Proof.
  induction T as [|r T IH]; cbn [tw_pairsb]; intros H; [constructor|].
  apply andb_true_iff in H as [H1 H2]. constructor; [|exact (IH H2)].
  apply Forall_forall. intros r' Hr'. rewrite forallb_forall in H1. specialize (H1 r' Hr').
  destruct r as [[o1 b1] n1], r' as [[o2 b2] n2]. cbn [tw_disjb tw_disj] in *. tw_bool H1. lia.
Qed.

Lemma tw_okb_ok : forall T, tw_okb T = true -> tw_ok T.
Proof.
  intros T H. unfold tw_okb in H. apply andb_true_iff in H as [H1 H2]. split; [|exact (tw_pairsb_ok T H2)].
  apply Forall_forall. intros r Hr. rewrite forallb_forall in H1. exact (tw_row_okb_ok r (H1 r Hr)).
Qed.

(* ---- rows ---- *)

Lemma tw_fop_in : forall {A : Type} (R : A -> A -> Prop) l x y,
  ForallOrdPairs R l -> In x l -> In y l -> x = y \/ R x y \/ R y x.
Proof.
  intros A R l x y H. induction H as [|a l Ha Hl IH]; intros Hx Hy; [destruct Hx|].
  destruct Hx as [<- | Hx], Hy as [<- | Hy].
  - left. reflexivity.
  - right. left. exact (proj1 (Forall_forall _ _) Ha y Hy).
  - right. right. exact (proj1 (Forall_forall _ _) Ha x Hx).
  - exact (IH Hx Hy).
Qed.

Lemma tw_row : forall T o b n, tw_ok T -> In (o, b, n) T ->
  0 <= o /\ 0 < n /\ o + n <= W_LEN /\ 0 <= b /\ b + n <= 2 ^ 64.
Proof. intros T o b n [HR _] Hin. exact (proj1 (Forall_forall _ _) HR _ Hin). Qed.

(* two rows of a table are the same row, or disjoint in the world and in the image *)
Lemma tw_same : forall T o b n o' b' n', tw_ok T -> In (o, b, n) T -> In (o', b', n') T ->
  (o = o' /\ b = b' /\ n = n') \/ ((o + n <= o' \/ o' + n' <= o) /\ (b + n <= b' \/ b' + n' <= b)).
Proof.
  intros T o b n o' b' n' [_ HD] H1 H2.
  destruct (tw_fop_in tw_disj T _ _ HD H1 H2) as [E | [D | D]].
  - left. injection E as E1 E2 E3. auto.
  - right. cbn [tw_disj] in D. lia.
  - right. cbn [tw_disj] in D. lia.
Qed.

(* ---- byte lists ---- *)

Lemma tw_nth_sub : forall (l : list byte) k m j d, 0 <= k -> (j < m)%nat -> (Z.to_nat k + j < length l)%nat ->
  nth j (sub l k m) d = nth (Z.to_nat k + j) l d.
Proof.
  intros l k m j d Hk Hj Hl. apply nth_error_nth. rewrite ne_sub by exact Hk.
  replace (j <? m)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj).
  apply nth_error_nth'. exact Hl.
Qed.

Lemma tw_nth_upd_in : forall (l v : list byte) k x d, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length l) ->
  k <= x < k + Z.of_nat (length v) -> nth (Z.to_nat x) (upd l k v) d = nth (Z.to_nat (x - k)) v d.
Proof.
  intros l v k x d Hk Hl Hx. apply nth_error_nth. rewrite ne_upd by lia.
  replace ((Z.to_nat k <=? Z.to_nat x) && (Z.to_nat x <? Z.to_nat k + length v))%nat with true
    by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  replace (Z.to_nat x - Z.to_nat k)%nat with (Z.to_nat (x - k)) by lia.
  apply nth_error_nth'. lia.
Qed.

Lemma tw_nth_upd_out : forall (l v : list byte) k x d, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length l) ->
  0 <= x -> ~ (k <= x < k + Z.of_nat (length v)) -> nth (Z.to_nat x) (upd l k v) d = nth (Z.to_nat x) l d.
Proof.
  intros l v k x d Hk Hl Hx Hn.
  destruct (Nat.lt_ge_cases (Z.to_nat x) (length l)) as [Hlt | Hge].
  - apply nth_error_nth. rewrite ne_upd by lia.
    replace ((Z.to_nat k <=? Z.to_nat x) && (Z.to_nat x <? Z.to_nat k + length v))%nat with false.
    + apply nth_error_nth'. exact Hlt.
    + symmetry. apply andb_false_iff.
      destruct (Z_lt_le_dec x k); [left; apply Nat.leb_gt | right; apply Nat.ltb_ge]; lia.
  - assert (LU : length (upd l k v) = length l) by (apply length_upd; lia).
    rewrite (nth_overflow (upd l k v)) by lia. rewrite (nth_overflow l) by lia. reflexivity.
Qed.

(* byte j of a little-endian value *)
Lemma tw_le_val_byte : forall (l : list Z) j, bytes_ok l -> (j < length l)%nat ->
  Z.shiftr (le_val l) (8 * Z.of_nat j) mod 256 = nth j l 0.
Proof.
  induction l as [|x l IH]; intros j Hok Hj; cbn [length] in Hj; [lia|].
  unfold bytes_ok in Hok. inversion Hok as [|? ? Hx Hok']; subst.
  destruct j as [|j]; cbn [le_val nth].
  - replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
    rewrite (Z.mul_comm 256), Z_mod_plus_full. apply Z.mod_small. exact Hx.
  - rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat j)) with (8 + 8 * Z.of_nat j) by lia.
    rewrite <- Z.shiftr_shiftr by lia. rewrite (Z.shiftr_div_pow2 _ 8) by lia. change (2 ^ 8) with 256.
    rewrite (Z.mul_comm 256), Z.div_add by lia. rewrite (Z.div_small x 256) by exact Hx. rewrite Z.add_0_l.
    apply IH; [exact Hok' | lia].
Qed.

Lemma tw_le_byte_ble : forall (l : list byte) j d, (j < length l)%nat ->
  YO0f.le_byte (bytes_le_to_Z l) (length l) j = bv_unsigned (nth j l d).
Proof.
  intros l j d Hj. unfold YO0f.le_byte.
  rewrite (Z.mod_small (bytes_le_to_Z l)) by apply ble_range.
  rewrite bytes_le_to_Z_le_val.
  rewrite tw_le_val_byte by first [apply bytes_ok_map | rewrite length_map; exact Hj].
  rewrite nth_indep with (d' := bv_unsigned d) by (rewrite length_map; exact Hj).
  apply map_nth.
Qed.

Lemma tw_le_byte_put : forall (m : nat) v j d, (j < m)%nat ->
  bv_unsigned (nth j (put m v) d) = YO0f.le_byte v m j.
Proof.
  intros m v j d Hj. rewrite <- tw_le_byte_ble by (rewrite length_put; exact Hj).
  rewrite length_put, bytes_le_to_Z_put. unfold YO0f.le_byte. rewrite Z.mod_mod; [reflexivity|].
  apply Z.pow_nonzero; lia.
Qed.

Lemma tw_le_byte1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* ---- loads inside one payload ---- *)

Lemma tw_read_bytes : forall T rd Bw o b n k m j,
  tw_ok T -> tw_at T rd Bw -> In (o, b, n) T -> 0 <= k -> k + Z.of_nat m <= n -> (j < m)%nat ->
  rd (b + k + Z.of_nat j) = Some (bv_unsigned (nth j (sub Bw (o + k) m) (Z_to_bv 8 0))).
Proof.
  intros T rd Bw o b n k m j Hok [HL HR] Hin Hk Hkm Hj.
  pose proof (tw_row T o b n Hok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  replace (b + k + Z.of_nat j) with (b + (k + Z.of_nat j)) by lia.
  rewrite (HR o b n (k + Z.of_nat j) Hin) by lia.
  rewrite tw_nth_sub by (rewrite ?HL; unfold W_LEN in *; lia).
  replace (Z.to_nat (o + k) + j)%nat with (Z.to_nat (o + (k + Z.of_nat j))) by lia. reflexivity.
Qed.

(* the shape of rd32 / rd64: byte j of a load of m bytes at b + k is byte j of the world's u_at *)
Lemma tw_read : forall T rd Bw o b n k m j,
  tw_ok T -> tw_at T rd Bw -> In (o, b, n) T -> 0 <= k -> k + Z.of_nat m <= n -> (j < m)%nat ->
  rd (b + k + Z.of_nat j) = Some (YO0f.le_byte (u_at Bw (o + k) m) m j).
Proof.
  intros T rd Bw o b n k m j Hok Hat Hin Hk Hkm Hj.
  pose proof (tw_row T o b n Hok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  assert (L : length (sub Bw (o + k) m) = m)
    by (apply length_sub; [lia | rewrite (tw_len T rd Bw Hat); unfold W_LEN in *; lia]).
  rewrite (tw_read_bytes T rd Bw o b n k m j Hok Hat Hin Hk Hkm Hj). f_equal. unfold u_at.
  rewrite <- (tw_le_byte_ble (sub Bw (o + k) m) j (Z_to_bv 8 0)) by (rewrite L; exact Hj).
  rewrite L. reflexivity.
Qed.

Lemma tw_read_val : forall segs (mm : word -> option byte) T Bw o b n k m,
  tw_ok T -> tw_at T (fun a => option_map (fun x => bv_unsigned x) (YP09.mbyte segs mm a)) Bw ->
  In (o, b, n) T -> 0 <= k -> k + Z.of_nat m <= n ->
  YI04.val_mem segs mm (b + k) m (u_at Bw (o + k) m).
Proof.
  intros segs mm T Bw o b n k m Hok Hat Hin Hk Hkm. unfold YI04.val_mem. intros j Hj.
  pose proof (tw_read T _ Bw o b n k m j Hok Hat Hin Hk Hkm Hj) as R. cbv beta in R.
  destruct (YP09.mbyte segs mm (b + k + Z.of_nat j)) as [x|]; [|discriminate R].
  cbn [option_map] in R. injection R as R. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- R.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma tw_garr8 : forall segs (mm : word -> option byte) T Bw o b n k m,
  tw_ok T -> tw_at T (fun a => option_map (fun x => bv_unsigned x) (YP09.mbyte segs mm a)) Bw ->
  In (o, b, n) T -> 0 <= k -> k + Z.of_nat m <= n ->
  YI00.garr8 segs mm (b + k) (zs (sub Bw (o + k) m)).
Proof.
  intros segs mm T Bw o b n k m Hok Hat Hin Hk Hkm.
  pose proof (tw_row T o b n Hok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  assert (L : length (sub Bw (o + k) m) = m)
    by (apply length_sub; [lia | rewrite (tw_len _ _ Bw Hat); unfold W_LEN in *; lia]).
  unfold YI00.garr8, zs. intros j Hj. rewrite length_map, L in Hj.
  pose proof (tw_read_bytes T _ Bw o b n k m j Hok Hat Hin Hk Hkm Hj) as R. cbv beta in R.
  rewrite nth_indep with (d' := bv_unsigned (Z_to_bv 8 0)) by (rewrite length_map, L; exact Hj).
  rewrite map_nth.
  set (y := nth j (sub Bw (o + k) m) (Z_to_bv 8 0)) in *.
  assert (Ry : 0 <= bv_unsigned y < 256)
    by (pose proof (bv_unsigned_in_range 8 y) as Q; unfold bv_modulus in Q; exact Q).
  split; [|exact Ry].
  unfold YI04.val_mem. intros j' Hj'. replace j' with 0%nat by lia.
  rewrite Nat2Z.inj_0, Z.add_0_r, tw_le_byte1 by exact Ry.
  destruct (YP09.mbyte segs mm (b + k + Z.of_nat j)) as [x|]; [|discriminate R].
  cbn [option_map] in R. injection R as R. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- R.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* At the machine's view of raw memory m: the c bytes at b + k inside ONE payload are sub Bw (o + k) c, as the
   bytes_at fact the kit's load step reads through bytes_at_read. *)
Lemma tw_bytes_at : forall segs (m : word -> option byte) T Bw o b n k (c : nat),
  tw_ok T ->
  tw_at T (fun a => option_map (fun x : byte => bv_unsigned x) (mrd segs m (wa a))) Bw ->
  In (o, b, n) T -> 0 <= k -> k + Z.of_nat c <= n ->
  bytes_at segs m (b + k) (sub Bw (o + k) c).
Proof.
  intros segs m T Bw o b n k c Hok Hat Hin Hk Hkc.
  pose proof (tw_row T o b n Hok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  assert (L : length (sub Bw (o + k) c) = c)
    by (apply length_sub; [lia | rewrite (tw_len T _ Bw Hat); unfold W_LEN in *; lia]).
  split; [lia|]. split; [rewrite L; lia|].
  intros i Hi. rewrite L in Hi.
  pose proof (tw_read_bytes T _ Bw o b n k c i Hok Hat Hin Hk Hkc Hi) as R. cbv beta in R.
  assert (E : nth_error (sub Bw (o + k) c) i = Some (nth i (sub Bw (o + k) c) (Z_to_bv 8 0)))
    by (apply nth_error_nth'; rewrite L; exact Hi).
  rewrite E.
  destruct (mrd segs m (wa (b + k + Z.of_nat i))) as [x|]; [|discriminate R].
  cbn [option_map] in R. f_equal. apply bv_eq.
  pose proof (f_equal (fun o : option Z => match o with Some z => z | None => 0 end) R) as R'.
  cbv beta iota in R'. exact R'.
Qed.

(* ---- the extension of a value Z_to_bv w (u_at ..): TWorld's accessor values ---- *)

Lemma tw_zext_u : forall Bw k (n : nat) (w : N), Z.of_N w = 8 * Z.of_nat n ->
  zext 64 (Z_to_bv w (u_at Bw k n)) = Z_to_bv 64 (u_at Bw k n).
Proof.
  intros Bw k n w Hw. rewrite zext_small, Z_to_bv_unsigned. f_equal. apply bv_wrap_small.
  unfold bv_modulus. rewrite Hw. apply u_at_range.
Qed.

Lemma tw_sext_u : forall Bw k (n : nat) (w : N), Z.of_N w = 8 * Z.of_nat n ->
  sext 64 (Z_to_bv w (u_at Bw k n)) = Z_to_bv 64 (bv_swrap w (u_at Bw k n)).
Proof.
  intros Bw k n w Hw. rewrite sext_small. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned. f_equal.
  apply bv_wrap_small. unfold bv_modulus. rewrite Hw. apply u_at_range.
Qed.

Lemma tw_lw : forall Bw k, sext 64 (Z_to_bv 32 (u_at Bw k 4)) = Z_to_bv 64 (s32_at Bw k).
Proof. intros. unfold s32_at. apply tw_sext_u. reflexivity. Qed.
Lemma tw_lwu : forall Bw k, zext 64 (Z_to_bv 32 (u_at Bw k 4)) = Z_to_bv 64 (u_at Bw k 4).
Proof. intros. apply tw_zext_u. reflexivity. Qed.
Lemma tw_lh : forall Bw k, sext 64 (Z_to_bv 16 (u_at Bw k 2)) = Z_to_bv 64 (bv_swrap 16 (u_at Bw k 2)).
Proof. intros. apply tw_sext_u. reflexivity. Qed.
Lemma tw_lhu : forall Bw k, zext 64 (Z_to_bv 16 (u_at Bw k 2)) = Z_to_bv 64 (u_at Bw k 2).
Proof. intros. apply tw_zext_u. reflexivity. Qed.
Lemma tw_lb : forall Bw k, sext 64 (Z_to_bv 8 (u_at Bw k 1)) = Z_to_bv 64 (bv_swrap 8 (u_at Bw k 1)).
Proof. intros. apply tw_sext_u. reflexivity. Qed.
Lemma tw_lbu : forall Bw k, zext 64 (Z_to_bv 8 (u_at Bw k 1)) = Z_to_bv 64 (u_at Bw k 1).
Proof. intros. apply tw_zext_u. reflexivity. Qed.

(* ---- the register value a load step leaves (Riscv/Sem.v load_val) of sub B k n: TWorld's accessor values ---- *)

Lemma tw_wrap_small : forall B k n, (n <= 8)%nat -> bv_wrap 64 (u_at B k n) = u_at B k n.
Proof.
  intros B k n Hn. pose proof (u_at_range B k n) as R. apply bv_wrap_small.
  unfold bv_modulus. change (Z.of_N 64) with 64.
  assert (P : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* ld *)
Lemma ld_world : forall B k, bv_extract 0 64 (le_bytes_to_word (sub B k 8)) = Z_to_bv 64 (u_at B k 8).
Proof.
  intros B k. transitivity (le_bytes_to_word (sub B k 8)); [|reflexivity].
  apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* lwu, lhu, lbu: zero extension, u_at *)
Lemma lwu_world : forall B k, zext 64 (bv_extract 0 32 (le_bytes_to_word (sub B k 4))) = Z_to_bv 64 (u_at B k 4).
Proof.
  intros. rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 4). rewrite tw_wrap_small by lia.
  pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R. change (Z.of_N 32) with 32.
  apply Z.mod_small. exact R.
Qed.
Lemma lhu_world : forall B k, zext 64 (bv_extract 0 16 (le_bytes_to_word (sub B k 2))) = Z_to_bv 64 (u_at B k 2).
Proof.
  intros. rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 2). rewrite tw_wrap_small by lia.
  pose proof (u_at_range B k 2) as R. change (8 * Z.of_nat 2) with 16 in R. change (Z.of_N 16) with 16.
  apply Z.mod_small. exact R.
Qed.
Lemma lbu_world : forall B k, zext 64 (bv_extract 0 8 (le_bytes_to_word (sub B k 1))) = Z_to_bv 64 (u_at B k 1).
Proof.
  intros. rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 1). rewrite tw_wrap_small by lia.
  pose proof (u_at_range B k 1) as R. change (8 * Z.of_nat 1) with 8 in R. change (Z.of_N 8) with 8.
  apply Z.mod_small. exact R.
Qed.

(* lw: s32_at; lh, lb: the signed wrap of u_at *)
Lemma lw_world : forall B k, sext 64 (bv_extract 0 32 (le_bytes_to_word (sub B k 4))) = Z_to_bv 64 (s32_at B k).
Proof.
  intros. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 4). rewrite tw_wrap_small by lia.
  reflexivity.
Qed.
Lemma lh_world : forall B k,
  sext 64 (bv_extract 0 16 (le_bytes_to_word (sub B k 2))) = Z_to_bv 64 (bv_swrap 16 (u_at B k 2)).
Proof.
  intros. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 2). rewrite tw_wrap_small by lia.
  reflexivity.
Qed.
Lemma lb_world : forall B k,
  sext 64 (bv_extract 0 8 (le_bytes_to_word (sub B k 1))) = Z_to_bv 64 (bv_swrap 8 (u_at B k 1)).
Proof.
  intros. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 1). rewrite tw_wrap_small by lia.
  reflexivity.
Qed.

(* ---- writes inside one payload ---- *)

Lemma tw_upd : forall T rd rd' Bw o b n k v,
  tw_ok T -> tw_at T rd Bw -> In (o, b, n) T -> 0 <= k -> k + Z.of_nat (length v) <= n ->
  (forall j, (j < length v)%nat -> rd' (b + k + Z.of_nat j) = Some (bv_unsigned (nth j v (Z_to_bv 8 0)))) ->
  (forall x, tw_in T x -> ~ (b + k <= x < b + k + Z.of_nat (length v)) -> rd' x = rd x) ->
  tw_at T rd' (upd Bw (o + k) v).
Proof.
  intros T rd rd' Bw o b n k v Hok [HL HR] Hin Hk Hkv Hnew Hfr.
  pose proof (tw_row T o b n Hok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  assert (LZ : Z.of_nat (length Bw) = W_LEN) by (rewrite HL; unfold W_LEN; lia).
  split.
  - rewrite length_upd by lia. exact HL.
  - intros o' b' n' i Hin' Hi.
    pose proof (tw_row T o' b' n' Hok Hin') as (Ho' & Hn' & HoW' & Hb' & Hb64').
    assert (Hx : tw_in T (b' + i)) by (exists o', b', n'; split; [exact Hin' | lia]).
    destruct (tw_same T o b n o' b' n' Hok Hin Hin') as [(<- & <- & <-) | (Dw & Db)].
    + destruct (Z_lt_le_dec i k) as [Hlt | Hge];
        [| destruct (Z_lt_le_dec i (k + Z.of_nat (length v))) as [Hin2 | Hge2]].
      * rewrite Hfr by first [exact Hx | lia]. rewrite (HR o b n i Hin Hi).
        rewrite tw_nth_upd_out by lia. reflexivity.
      * replace (b + i) with (b + k + Z.of_nat (Z.to_nat (i - k))) by lia.
        rewrite Hnew by lia. rewrite tw_nth_upd_in by lia.
        replace (Z.to_nat (o + i - (o + k))) with (Z.to_nat (i - k)) by lia. reflexivity.
      * rewrite Hfr by first [exact Hx | lia]. rewrite (HR o b n i Hin Hi).
        rewrite tw_nth_upd_out by lia. reflexivity.
    + rewrite Hfr by first [exact Hx | lia]. rewrite (HR o' b' n' i Hin' Hi).
      rewrite tw_nth_upd_out by lia. reflexivity.
Qed.

(* a store of m bytes of v at b + k (the store writes byte j as le_byte v m j) *)
Lemma tw_write : forall T rd rd' Bw o b n k (m : nat) v,
  tw_ok T -> tw_at T rd Bw -> In (o, b, n) T -> 0 <= k -> k + Z.of_nat m <= n ->
  (forall j, (j < m)%nat -> rd' (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  (forall x, tw_in T x -> ~ (b + k <= x < b + k + Z.of_nat m) -> rd' x = rd x) ->
  tw_at T rd' (upd Bw (o + k) (put m v)).
Proof.
  intros T rd rd' Bw o b n k m v Hok Hat Hin Hk Hkm Hnew Hfr.
  apply (tw_upd T rd rd' Bw o b n k (put m v) Hok Hat Hin Hk); rewrite ?length_put.
  - exact Hkm.
  - intros j Hj. rewrite Hnew by exact Hj. rewrite tw_le_byte_put by exact Hj. reflexivity.
  - exact Hfr.
Qed.

(* a span [b + k, b + k + length src) written with src (the __asan_memcpy post's form, Z-indexed) *)
Lemma tw_fill : forall T rd rd' Bw o b n k (src : list byte),
  tw_ok T -> tw_at T rd Bw -> In (o, b, n) T -> 0 <= k -> k + Z.of_nat (length src) <= n ->
  (forall i, 0 <= i < Z.of_nat (length src) ->
     rd' (b + k + i) = Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0)))) ->
  (forall x, tw_in T x -> ~ (b + k <= x < b + k + Z.of_nat (length src)) -> rd' x = rd x) ->
  tw_at T rd' (upd Bw (o + k) src).
Proof.
  intros T rd rd' Bw o b n k src Hok Hat Hin Hk Hkn Hnew Hfr.
  apply (tw_upd T rd rd' Bw o b n k src Hok Hat Hin Hk Hkn); [|exact Hfr].
  intros j Hj. rewrite Hnew by lia. rewrite Nat2Z.id. reflexivity.
Qed.

(* a memset of [b + k, b + k + L) with c (the __asan_memset post gives c mod 256 per byte) *)
Lemma tw_fill_set : forall T rd rd' Bw o b n k c L,
  tw_ok T -> tw_at T rd Bw -> In (o, b, n) T -> 0 <= k -> 0 <= L -> k + L <= n ->
  (forall i, 0 <= i < L -> rd' (b + k + i) = Some (c mod 256)) ->
  (forall x, tw_in T x -> ~ (b + k <= x < b + k + L) -> rd' x = rd x) ->
  tw_at T rd' (upd Bw (o + k) (repeat (Z_to_bv 8 c) (Z.to_nat L))).
Proof.
  intros T rd rd' Bw o b n k c L Hok Hat Hin Hk HL Hkn Hnew Hfr.
  apply (tw_fill T rd rd' Bw o b n k _ Hok Hat Hin Hk); rewrite ?repeat_length.
  - lia.
  - intros i Hi. rewrite Hnew by lia.
    rewrite nth_indep with (d' := Z_to_bv 8 c) by (rewrite repeat_length; lia).
    rewrite nth_repeat, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity.
  - intros x Hx Hn. apply Hfr; [exact Hx | lia].
Qed.

(* a memset of L bytes with 0, in the model's form put L 0 *)
Lemma tw_fill_zero : forall T rd rd' Bw o b n k (L : nat),
  tw_ok T -> tw_at T rd Bw -> In (o, b, n) T -> 0 <= k -> k + Z.of_nat L <= n ->
  (forall i, 0 <= i < Z.of_nat L -> rd' (b + k + i) = Some 0) ->
  (forall x, tw_in T x -> ~ (b + k <= x < b + k + Z.of_nat L) -> rd' x = rd x) ->
  tw_at T rd' (upd Bw (o + k) (put L 0)).
Proof.
  intros T rd rd' Bw o b n k L Hok Hat Hin Hk Hkn Hnew Hfr.
  apply (tw_fill T rd rd' Bw o b n k _ Hok Hat Hin Hk); rewrite ?length_put.
  - exact Hkn.
  - intros i Hi. rewrite Hnew by lia. rewrite tw_le_byte_put by lia. unfold YO0f.le_byte.
    rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
  - exact Hfr.
Qed.

(* a span copied from bytes known as a list of Z (garr8's form), in the model's form bs l *)
Lemma tw_fill_z : forall T rd rd' Bw o b n k (l : list Z),
  tw_ok T -> tw_at T rd Bw -> In (o, b, n) T -> 0 <= k -> k + Z.of_nat (length l) <= n ->
  Forall (fun z => 0 <= z < 256) l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (b + k + i) = Some (nth (Z.to_nat i) l 0)) ->
  (forall x, tw_in T x -> ~ (b + k <= x < b + k + Z.of_nat (length l)) -> rd' x = rd x) ->
  tw_at T rd' (upd Bw (o + k) (bs l)).
Proof.
  intros T rd rd' Bw o b n k l Hok Hat Hin Hk Hkn Hl Hnew Hfr. unfold bs.
  apply (tw_fill T rd rd' Bw o b n k _ Hok Hat Hin Hk); rewrite ?length_map.
  - exact Hkn.
  - intros i Hi. rewrite Hnew by lia.
    assert (R : 0 <= nth (Z.to_nat i) l 0 < 256) by (rewrite Forall_forall in Hl; apply Hl, nth_In; lia).
    rewrite map_nth, Z_to_bv_unsigned. f_equal. symmetry. apply bv_wrap_small.
    unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. exact R.
  - exact Hfr.
Qed.

(* ---- payload bytes unchanged ---- *)

Lemma tw_kept_rows : forall T rd rd' Bw, tw_at T rd Bw ->
  (forall o b n i, In (o, b, n) T -> 0 <= i < n -> rd' (b + i) = rd (b + i)) -> tw_at T rd' Bw.
Proof.
  intros T rd rd' Bw [HL HR] Hk. split; [exact HL|].
  intros o b n i Hin Hi. rewrite (Hk o b n i Hin Hi). exact (HR o b n i Hin Hi).
Qed.

Lemma tw_kept : forall T rd rd' Bw, tw_at T rd Bw -> (forall x, tw_in T x -> rd' x = rd x) -> tw_at T rd' Bw.
Proof.
  intros T rd rd' Bw H Hk. apply (tw_kept_rows T rd); [exact H|].
  intros o b n i Hin Hi. apply Hk. exists o, b, n. split; [exact Hin | lia].
Qed.

(* At the machine's view: a run whose footprint W (munch W m m') misses every payload byte keeps the world. *)
Lemma tw_kept_munch : forall segs (m m' : word -> option byte) T W Bw, tw_ok T ->
  tw_at T (fun a => option_map (fun x : byte => bv_unsigned x) (mrd segs m (wa a))) Bw ->
  munch W m m' -> (forall x, tw_in T x -> outside W x) ->
  tw_at T (fun a => option_map (fun x : byte => bv_unsigned x) (mrd segs m' (wa a))) Bw.
Proof.
  intros segs m m' T W Bw Hok H MU HW. apply (tw_kept T _ _ Bw H). intros x Hx.
  pose proof (HW x Hx) as Ho. destruct Hx as (o & b & n & Hin & Hx).
  pose proof (tw_row T o b n Hok Hin) as (_ & _ & _ & Hb & Hb64).
  cbv beta. unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* ---- a world exists for every view that shows every payload byte ---- *)

Definition tw_find (T : list (Z * Z * Z)) (x : Z) : option (Z * Z * Z) :=
  find (fun r => let '(o, b, n) := r in (o <=? x) && (x <? o + n)) T.
Definition tw_val (T : list (Z * Z * Z)) (rd : Z -> option Z) (x : Z) : Z :=
  match tw_find T x with
  | Some (o, b, n) => match rd (b + (x - o)) with Some v => v | None => 0 end
  | None => 0
  end.
Definition tw_cell (T : list (Z * Z * Z)) (rd : Z -> option Z) (x : nat) : byte := Z_to_bv 8 (tw_val T rd (Z.of_nat x)).
Definition tw_build (T : list (Z * Z * Z)) (rd : Z -> option Z) : list byte :=
  map (tw_cell T rd) (seq 0 (Z.to_nat W_LEN)).

Lemma tw_exists : forall T rd, tw_ok T ->
  (forall o b n i, In (o, b, n) T -> 0 <= i < n -> exists v, rd (b + i) = Some v /\ 0 <= v < 256) ->
  exists Bw, tw_at T rd Bw.
Proof.
  intros T rd Hok Hv. exists (tw_build T rd). split.
  - unfold tw_build. rewrite length_map, length_seq. reflexivity.
  - intros o b n i Hin Hi.
    pose proof (tw_row T o b n Hok Hin) as (Ho & Hn & HoW & Hb & Hb64).
    destruct (Hv o b n i Hin Hi) as (v & Ev & Rv).
    unfold tw_build.
    rewrite nth_indep with (d' := tw_cell T rd 0) by (rewrite length_map, length_seq; unfold W_LEN in *; lia).
    rewrite map_nth, seq_nth by (unfold W_LEN in *; lia).
    unfold tw_cell. rewrite Nat.add_0_l, Z2Nat.id by lia.
    assert (Hval : tw_val T rd (o + i) = v).
    { unfold tw_val. destruct (tw_find T (o + i)) as [[[o' b'] n']|] eqn:E.
      - unfold tw_find in E. apply find_some in E as [Hin' Hc].
        apply andb_true_iff in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
        destruct (tw_same T o b n o' b' n' Hok Hin Hin') as [(<- & <- & <-) | (Dw & _)].
        + replace (b + (o + i - o)) with (b + i) by lia. rewrite Ev. reflexivity.
        + exfalso. lia.
      - exfalso. unfold tw_find in E. pose proof (find_none _ _ E (o, b, n) Hin) as F. cbv beta iota in F.
        apply andb_false_iff in F as [F | F]; [apply Z.leb_gt in F | apply Z.ltb_ge in F]; lia. }
    rewrite Hval, Ev. f_equal. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. exact Rv.
Qed.

(* ---- build-independent facts of the world ---- *)

(* the world column of a table: (offset in the world, payload) of each of the 18 globals *)
Definition TW_ROWS : list (Z * Z) := [
  (OFF_M, SZ_M); (OFF_g_s, SZ_g_s); (OFF_g_cmd, SZ_g_cmd); (OFF_g_q, SZ_g_q); (OFF_g_fail_next, 1);
  (OFF_g_raw, SZ_g_raw); (OFF_g_last_counter, SZ_g_last_counter); (OFF_g_nq, SZ_g_nq); (OFF_g_ncmd, SZ_g_ncmd);
  (OFF_g_rx_send, SZ_g_rx_send); (OFF_g_rx_fail, SZ_g_rx_fail); (OFF_g_rx_times, SZ_g_rx_times);
  (OFF_g_now, SZ_g_now); (OFF_g_rx, SZ_g_rx); (OFF_g_rx_len, SZ_g_rx_len); (OFF_g_cfg, SZ_g_cfg);
  (OFF_GOT, SZ_GOT); (OFF_OW, SZ_OW)].
Definition tw_wrow (r : Z * Z * Z) : Z * Z := let '(o, _, n) := r in (o, n).
Definition tw_bn (r : Z * Z * Z) : Z * Z := let '(_, b, n) := r in (b, n).

(* the world bytes of no payload *)
Definition tw_pad (x : Z) : Prop := OFF_g_fail_next + 1 <= x < OFF_g_raw \/ OFF_GOT + SZ_GOT <= x < OFF_OW.
Definition tw_padb (x : Z) : bool :=
  ((OFF_g_fail_next + 1 <=? x) && (x <? OFF_g_raw)) || ((OFF_GOT + SZ_GOT <=? x) && (x <? OFF_OW)).

Lemma tw_pad_bytes : forall x, tw_pad x <-> 0xfdc9 <= x < 0xfdcc \/ 0xff1c <= x < 0xff20.
Proof. intros x. unfold tw_pad, OFF_g_fail_next, OFF_g_raw, OFF_GOT, SZ_GOT, OFF_OW. split; intros; lia. Qed.

Fixpoint tw_zs (lo : Z) (fuel : nat) : list Z := match fuel with O => [] | S k => lo :: tw_zs (lo + 1) k end.

Lemma tw_zs_in : forall fuel lo x, In x (tw_zs lo fuel) <-> lo <= x < lo + Z.of_nat fuel.
Proof.
  induction fuel as [|k IH]; intros lo x; cbn [tw_zs In].
  - split; [intros [] | intros; lia].
  - rewrite IH. split; intros; lia.
Qed.

(* the footprint (address, width) of each reader of the world: TWorld.v's, and TCb.v's OW_dn_* *)
Definition TW_ACC0 : list (Z * Z) := [
  (A_M_desk_known, 4);  (* M_desk_known *)
  (A_M_desk, 6);  (* M_desk *)
  (A_M_state, 4);  (* M_state *)
  (A_M_e2_acked, 4);  (* M_e2_acked *)
  (A_M_e1_us, 4);  (* M_e1_us *)
  (A_M_foreign, 4);  (* M_foreign *)
  (A_M_last_rx, 8);  (* M_last_rx *)
  (A_M_wake_sent, 8);  (* M_wake_sent *)
  (A_M_next_ka, 8);  (* M_next_ka *)
  (A_M_backoff_until, 8);  (* M_backoff_until *)
  (A_M_last_display, 8);  (* M_last_display *)
  (A_M_display_sent, 4);  (* M_display_sent *)
  (A_M_desk_counter_valid, 4);  (* M_desk_counter_valid *)
  (A_M_desk_counter, 4);  (* M_desk_counter *)
  (A_M_host_counter, 4);  (* M_host_counter *)
  (A_M_fail, 4);  (* M_fail *)
  (A_M_fly_on, 4);  (* M_fly_on *)
  (A_M_fly_cmd, 1);  (* M_fly_cmd *)
  (A_M_fly_counter, 4);  (* M_fly_counter *)
  (A_M_fly_retries, 4);  (* M_fly_retries *)
  (A_M_fly_sent, 8);  (* M_fly_sent *)
  (A_M_fly_frame, 1514);  (* M_fly_frame *)
  (A_M_fly_len, 8);  (* M_fly_len *)
  (A_OW_n, 4);  (* OW_n *)
  (A_OW_e2, 4);  (* OW_e2 *)
  (A_OW_e3, 4);  (* OW_e3 *)
  (A_OW_acks, 4);  (* OW_acks *)
  (A_OW_desk, 4);  (* OW_desk *)
  (A_OW_foreign, 4);  (* OW_foreign *)
  (A_OW_acked, 4);  (* OW_acked *)
  (A_OW_ndata, 4);  (* OW_ndata *)
  (A_OW_acked_counter, 4);  (* OW_acked_counter *)
  (A_OW_acked_retry, 4);  (* OW_acked_retry *)
  (A_OW_desk_off, 4);  (* OW_desk_off *)
  (A_OW_desk_p, 8);  (* OW_desk_p *)
  (A_OW_desk_body, 8);  (* OW_desk_body *)
  (A_GOT_n, 4);  (* GOT_n *)
  (A_GOT_e2, 4);  (* GOT_e2 *)
  (A_GOT_e3, 4);  (* GOT_e3 *)
  (A_GOT_acks, 4);  (* GOT_acks *)
  (A_GOT_desk, 4);  (* GOT_desk *)
  (A_GOT_foreign, 4);  (* GOT_foreign *)
  (A_GOT_acked, 4);  (* GOT_acked *)
  (A_GOT_ndata, 4);  (* GOT_ndata *)
  (A_S_cfg_host_mac, 6);  (* S_cfg_host_mac *)
  (A_S_cfg_desk_mac, 6);  (* S_cfg_desk_mac *)
  (A_S_cfg_desk_mac_set, 4);  (* S_cfg_desk_mac_set *)
  (A_S_cfg_auto_wake, 4);  (* S_cfg_auto_wake *)
  (A_S_cfg_sum_mode, 4);  (* S_cfg_sum_mode *)
  (A_S_cfg_keepalive_ms, 4);  (* S_cfg_keepalive_ms *)
  (A_S_cfg_ack_timeout_ms, 4);  (* S_cfg_ack_timeout_ms *)
  (A_S_cfg_max_retries, 4);  (* S_cfg_max_retries *)
  (A_S_cfg_backoff_ms, 4);  (* S_cfg_backoff_ms *)
  (A_S_cfg_offline_ms, 4);  (* S_cfg_offline_ms *)
  (A_S_cfg_wake_timeout_ms, 4);  (* S_cfg_wake_timeout_ms *)
  (A_S_cfg_display_gap_us, 4);  (* S_cfg_display_gap_us *)
  (A_S_cfg_max_cmds, 4);  (* S_cfg_max_cmds *)
  (A_S_cfg_max_body, 4);  (* S_cfg_max_body *)
  (A_S_io_ctx, 8);  (* S_io_ctx *)
  (A_S_io_send, 8);  (* S_io_send *)
  (A_S_io_recv, 8);  (* S_io_recv *)
  (A_S_io_now_us, 8);  (* S_io_now_us *)
  (A_S_notify, 8);  (* S_notify *)
  (A_S_notify_ctx, 8);  (* S_notify_ctx *)
  (A_S_state, 4);  (* S_state *)
  (A_S_desk_known, 4);  (* S_desk_known *)
  (A_S_desk_mac, 6);  (* S_desk_mac *)
  (A_S_personality, 8);  (* S_personality *)
  (A_S_foreign, 4);  (* S_foreign *)
  (A_S_e1_named_us, 4);  (* S_e1_named_us *)
  (A_S_wake_acked, 4);  (* S_wake_acked *)
  (A_S_wake_sent_us, 8);  (* S_wake_sent_us *)
  (A_S_host_counter, 4);  (* S_host_counter *)
  (A_S_desk_counter, 4);  (* S_desk_counter *)
  (A_S_desk_counter_valid, 4);  (* S_desk_counter_valid *)
  (A_S_last_rx_us, 8);  (* S_last_rx_us *)
  (A_S_next_keepalive_us, 8);  (* S_next_keepalive_us *)
  (A_S_backoff_until_us, 8);  (* S_backoff_until_us *)
  (A_S_last_display_us, 8);  (* S_last_display_us *)
  (A_S_display_sent, 4);  (* S_display_sent *)
  (A_S_inflight, 4);  (* S_inflight *)
  (A_S_inflight_frame, 1514);  (* S_inflight_frame *)
  (A_S_inflight_len, 8);  (* S_inflight_len *)
  (A_S_inflight_counter, 4);  (* S_inflight_counter *)
  (A_S_inflight_retries, 4);  (* S_inflight_retries *)
  (A_S_inflight_sent_us, 8);  (* S_inflight_sent_us *)
  (A_S_queued, 4);  (* S_queued *)
  (A_S_stats_rx_frames, 8);  (* S_stats_rx_frames *)
  (A_S_stats_rx_data, 8);  (* S_stats_rx_data *)
  (A_S_stats_rx_duplicates, 8);  (* S_stats_rx_duplicates *)
  (A_S_stats_rx_desk_retries, 8);  (* S_stats_rx_desk_retries *)
  (A_S_stats_rx_ignored, 8);  (* S_stats_rx_ignored *)
  (A_S_stats_tx_frames, 8);  (* S_stats_tx_frames *)
  (A_S_stats_tx_data, 8);  (* S_stats_tx_data *)
  (A_S_stats_tx_acks, 8);  (* S_stats_tx_acks *)
  (A_S_stats_tx_keepalives, 8);  (* S_stats_tx_keepalives *)
  (A_S_stats_tx_wakes, 8);  (* S_stats_tx_wakes *)
  (A_S_stats_tx_retransmits, 8);  (* S_stats_tx_retransmits *)
  (A_S_stats_ack_lost, 8);  (* S_stats_ack_lost *)
  (A_S_stats_coalesced, 8);  (* S_stats_coalesced *)
  (A_S_stats_refused, 8);  (* S_stats_refused *)
  (A_Cfg_host_mac, 6);  (* Cfg_host_mac *)
  (A_Cfg_desk_mac, 6);  (* Cfg_desk_mac *)
  (A_Cfg_desk_mac_set, 4);  (* Cfg_desk_mac_set *)
  (A_Cfg_auto_wake, 4);  (* Cfg_auto_wake *)
  (A_Cfg_sum_mode, 4);  (* Cfg_sum_mode *)
  (A_Cfg_keepalive_ms, 4);  (* Cfg_keepalive_ms *)
  (A_Cfg_ack_timeout_ms, 4);  (* Cfg_ack_timeout_ms *)
  (A_Cfg_max_retries, 4);  (* Cfg_max_retries *)
  (A_Cfg_backoff_ms, 4);  (* Cfg_backoff_ms *)
  (A_Cfg_offline_ms, 4);  (* Cfg_offline_ms *)
  (A_Cfg_wake_timeout_ms, 4);  (* Cfg_wake_timeout_ms *)
  (A_Cfg_display_gap_us, 4);  (* Cfg_display_gap_us *)
  (A_Cfg_max_cmds, 4);  (* Cfg_max_cmds *)
  (A_Cfg_max_body, 4);  (* Cfg_max_body *)
  (OFF_g_now, 8);  (* g_now *)
  (OFF_g_raw, 4);  (* g_raw *)
  (OFF_g_last_counter, 4);  (* g_last_counter *)
  (OFF_g_rx_send, 4);  (* g_rx_send *)
  (OFF_g_ncmd, 4);  (* g_ncmd *)
  (OFF_g_nq, 4);  (* g_nq *)
  (OFF_g_rx, 8);  (* g_rx *)
  (OFF_g_rx_len, 8);  (* g_rx_len *)
  (OFF_g_rx_fail, 4);  (* g_rx_fail *)
  (OFF_g_rx_times, 4);  (* g_rx_times *)
  (OFF_g_fail_next, 1)  (* g_fail_next *)
].

Definition TW_ACCI : list ((Z -> Z) * Z * Z) := [
  (A_OW_t_state, 4, OW_t_N);  (* OW_t_state *)
  (A_OW_t_old, 4, OW_t_N);  (* OW_t_old *)
  (A_OW_t_reason, 4, OW_t_N);  (* OW_t_reason *)
  (A_GOT_t_state, 4, GOT_t_N);  (* GOT_t_state *)
  (A_GOT_t_old, 4, GOT_t_N);  (* GOT_t_old *)
  (A_GOT_t_reason, 4, GOT_t_N);  (* GOT_t_reason *)
  (A_S_queue_bytes, 24, S_queue_N);  (* S_queue_bytes *)
  (A_S_queue_len, 1, S_queue_N);  (* S_queue_len *)
  (A_S_queue_display, 1, S_queue_N);  (* S_queue_display *)
  (A_S_queue_key, 4, S_queue_N);  (* S_queue_key *)
  (A_Cmd_st, 4, Cmd_N);  (* Cmd_st *)
  (A_Cmd_key, 4, Cmd_N);  (* Cmd_key *)
  (A_Cmd_display, 4, Cmd_N);  (* Cmd_display *)
  (A_Cmd_bytes, 24, Cmd_N);  (* Cmd_bytes *)
  (A_Cmd_len, 1, Cmd_N);  (* Cmd_len *)
  (fun i => OFF_g_q + 4 * i, 4, SZ_g_q / 4);  (* Q_at *)
  (TCb.A_OW_dn_body, 8, OW_dn_N);  (* OW_dn_body *)
  (TCb.A_OW_dn_len, 8, OW_dn_N);  (* OW_dn_len *)
  (TCb.A_OW_dn_counter, 4, OW_dn_N);  (* OW_dn_counter *)
  (TCb.A_OW_dn_retry, 2, OW_dn_N)  (* OW_dn_retry *)
].

Definition TW_ACC : list (Z * Z) :=
  TW_ACC0 ++ flat_map (fun e => let '(f, w, N) := e in map (fun i => (f i, w)) (tw_zs 0 (Z.to_nat N))) TW_ACCI.

Lemma TW_ACC_ix : forall f w N i, In (f, w, N) TW_ACCI -> 0 <= i < N -> In (f i, w) TW_ACC.
Proof.
  intros f w N i Hin Hi. unfold TW_ACC. apply in_or_app. right. apply in_flat_map.
  exists (f, w, N). split; [exact Hin|]. cbv beta iota. apply in_map_iff.
  exists i. split; [reflexivity | apply tw_zs_in; lia].
Qed.

(* no reader of the world reads a pad byte *)
Definition tw_acc_padb (a w : Z) : bool :=
  ((a + w <=? OFF_g_fail_next + 1) || (OFF_g_raw <=? a)) && ((a + w <=? OFF_GOT + SZ_GOT) || (OFF_OW <=? a)).

Lemma tw_pad_free : forall a w, In (a, w) TW_ACC -> forall x, a <= x < a + w -> ~ tw_pad x.
Proof.
  intros a w Hin x Hx.
  assert (H : forallb (fun aw => tw_acc_padb (fst aw) (snd aw)) TW_ACC = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (a, w) Hin). cbn [fst snd] in H. unfold tw_acc_padb in H.
  tw_bool H. unfold tw_pad. lia.
Qed.

(* every reader's footprint lies inside ONE payload row *)
Definition tw_inrowb (a w : Z) (R : list (Z * Z)) : bool :=
  existsb (fun r => (fst r <=? a) && (a + w <=? fst r + snd r)) R.

Lemma tw_acc_rows : forall a w, In (a, w) TW_ACC -> exists o n, In (o, n) TW_ROWS /\ o <= a /\ a + w <= o + n.
Proof.
  intros a w Hin.
  assert (H : forallb (fun aw => tw_inrowb (fst aw) (snd aw) TW_ROWS) TW_ACC = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (a, w) Hin). cbn [fst snd] in H. unfold tw_inrowb in H.
  apply existsb_exists in H as ([o n] & Hr & Hc). cbn [fst snd] in Hc. tw_bool Hc.
  exists o, n. split; [exact Hr | lia].
Qed.

(* every world byte but the 7 pad bytes lies in a payload row *)
Fixpoint tw_allz (f : Z -> bool) (lo : Z) (fuel : nat) : bool :=
  match fuel with O => true | S k => if f lo then tw_allz f (lo + 1) k else false end.

Lemma tw_allz_ok : forall f fuel lo, tw_allz f lo fuel = true -> forall x, lo <= x < lo + Z.of_nat fuel -> f x = true.
Proof.
  intros f fuel. induction fuel as [|k IH]; intros lo H x Hx; [lia|].
  cbn [tw_allz] in H. destruct (f lo) eqn:E; [|discriminate H].
  destruct (Z.eq_dec x lo) as [-> | Ne]; [exact E|]. apply (IH (lo + 1) H). lia.
Qed.

Lemma tw_cover_rows : forall x, 0 <= x < W_LEN -> ~ tw_pad x -> exists o n, In (o, n) TW_ROWS /\ o <= x < o + n.
Proof.
  intros x Hx Hp.
  assert (H : tw_allz (fun y => tw_padb y || tw_inrowb y 1 TW_ROWS) 0 (Z.to_nat W_LEN) = true)
    by (vm_compute; reflexivity).
  assert (Hx' : 0 <= x < 0 + Z.of_nat (Z.to_nat W_LEN)) by (rewrite Z2Nat.id by (unfold W_LEN; lia); lia).
  pose proof (tw_allz_ok _ _ 0 H x Hx') as Hc. cbv beta in Hc.
  apply orb_true_iff in Hc as [Hc | Hc].
  - exfalso. apply Hp. unfold tw_padb in Hc. tw_bool Hc. unfold tw_pad. lia.
  - unfold tw_inrowb in Hc. apply existsb_exists in Hc as ([o n] & Hr & Hc). cbn [fst snd] in Hc. tw_bool Hc.
    exists o, n. split; [exact Hr | lia].
Qed.

(* ---- a table whose world column is TW_ROWS ---- *)

Lemma tw_acc_row : forall T, map tw_wrow T = TW_ROWS ->
  forall a w, In (a, w) TW_ACC -> exists o b n, In (o, b, n) T /\ o <= a /\ a + w <= o + n.
Proof.
  intros T HT a w Hin. destruct (tw_acc_rows a w Hin) as (o & n & Hr & H1 & H2).
  rewrite <- HT in Hr. apply in_map_iff in Hr as ([[o' b'] n'] & E & Hr'). cbn [tw_wrow] in E.
  injection E as E1 E2. subst o' n'. exists o, b', n. split; [exact Hr' | lia].
Qed.

Lemma tw_cover : forall T, map tw_wrow T = TW_ROWS ->
  forall x, 0 <= x < W_LEN -> ~ tw_pad x -> exists o b n, In (o, b, n) T /\ o <= x < o + n.
Proof.
  intros T HT x Hx Hp. destruct (tw_cover_rows x Hx Hp) as (o & n & Hr & H1).
  rewrite <- HT in Hr. apply in_map_iff in Hr as ([[o' b'] n'] & E & Hr'). cbn [tw_wrow] in E.
  injection E as E1 E2. subst o' n'. exists o, b', n. split; [exact Hr' | lia].
Qed.

(* ---- a table against a list G of (base, length) ranges ---- *)

Definition tw_pair_eqb (p q : Z * Z) : bool := (fst p =? fst q) && (snd p =? snd q).

Lemma tw_pair_eqb_eq : forall p q, tw_pair_eqb p q = true -> p = q.
Proof. intros [a b] [c d] H. unfold tw_pair_eqb in H. cbn [fst snd] in H. tw_bool H. destruct H as [-> ->]. reflexivity. Qed.

(* each row's payload range (b, n) is a range of G *)
Lemma tw_in_G_of : forall T (G : list (Z * Z)),
  forallb (fun r => existsb (tw_pair_eqb (tw_bn r)) G) T = true ->
  forall o b n, In (o, b, n) T -> In (b, n) G.
Proof.
  intros T G H o b n Hin. rewrite forallb_forall in H. specialize (H _ Hin). cbn [tw_bn] in H.
  apply existsb_exists in H as (g & Hg & E). apply tw_pair_eqb_eq in E. rewrite E. exact Hg.
Qed.

(* each range of G is a row's payload range *)
Lemma tw_G_rows_of : forall T (G : list (Z * Z)),
  forallb (fun g => existsb (fun r => tw_pair_eqb (tw_bn r) g) T) G = true ->
  forall b n, In (b, n) G -> exists o, In (o, b, n) T.
Proof.
  intros T G H b n Hin. rewrite forallb_forall in H. specialize (H _ Hin). cbv beta in H.
  apply existsb_exists in H as ([[o b'] n'] & Hr & E). apply tw_pair_eqb_eq in E. cbn [tw_bn] in E.
  injection E as E1 E2. subst b' n'. exists o. exact Hr.
Qed.

(* the bytes of G unchanged keep the world *)
Lemma tw_kept_G : forall T (G : list (Z * Z)) rd rd' Bw,
  (forall o b n, In (o, b, n) T -> In (b, n) G) -> tw_at T rd Bw ->
  (forall b n i, In (b, n) G -> 0 <= i < n -> rd' (b + i) = rd (b + i)) -> tw_at T rd' Bw.
Proof.
  intros T G rd rd' Bw HG H Hk. apply (tw_kept_rows T rd); [exact H|].
  intros o b n i Hin Hi. exact (Hk b n i (HG o b n Hin) Hi).
Qed.
