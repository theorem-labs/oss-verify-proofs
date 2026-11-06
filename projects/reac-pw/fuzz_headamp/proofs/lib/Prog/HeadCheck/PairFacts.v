(** Facts for the pair loop of expect_of (fuzz_headamp.c:119-155) in the plain check segment's walk: the value of
    strncmp(k, "reac.headamp.", 13) as Pod/Headamp.v [ha_prefix] k, one step of pod_next_pair's pairing
    (Pod/Accessors.v [pairs_by]) over the entries left, one step of [ha_fold], the refusal codes [expect_cell]
    gives, and x's bytes past x->rc (struct expect, fuzz_headamp.c:56-62) after the cell write and n++. With them
    the generic memory facts the walk uses: a store into the middle of a run of bytes, and a run of stack cells as
    memset's writable block. No function of a binary is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require strncmp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts Cut.
Import ListNotations.
Open Scope Z_scope.

(** ** strncmp(k, "reac.headamp.", 13) *)
Lemma byte_lt256 : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. exact StrFun.byte_range. Qed.

(** The walk of strncmp on a C string k against a string P without NUL, over |P| bytes: a byte difference, 0
    exactly when k starts with P. *)
Lemma walk_prefix : forall P k, P <> [] -> Forall (fun b : byte => bv_unsigned b <> 0) P -> ~ In NUL k ->
  exists v, StrFun.strncmp_walk (k ++ [NUL]) (P ++ [NUL]) (length P - 1) = Some v /\ -256 < v < 256 /\
            (v = 0 <-> firstn (length P) k = P).
Proof.
  induction P as [|p P IH]; intros k HP HF HK; [congruence|].
  apply Forall_cons_iff in HF as [Hp HF].
  pose proof (byte_lt256 p) as Rp.
  destruct k as [|x k]; cbn [app].
  - exists (bv_unsigned NUL - bv_unsigned p).
    rewrite strncmp.walk_stop by (left; reflexivity).
    change (bv_unsigned NUL) with 0. split; [reflexivity|]. split; [lia|].
    split; [intros E; lia | intros E; cbn in E; discriminate E].
  - assert (Hx : bv_unsigned x <> 0).
    { intros E. apply HK. left. apply bv_eq. rewrite E. reflexivity. }
    assert (HK' : ~ In NUL k) by (intros H; apply HK; right; exact H).
    pose proof (byte_lt256 x) as Rx.
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned p)) as [Exp|Nxp].
    + assert (Exb : x = p) by (apply bv_eq; exact Exp). subst x.
      destruct P as [|p2 P'].
      * exists 0. rewrite strncmp.walk_stop by (right; right; left; reflexivity).
        rewrite Z.sub_diag. split; [reflexivity|]. split; [lia|]. cbn [length firstn].
        split; intros _; reflexivity.
      * assert (Hc : (length (p :: p2 :: P') - 1 = S (length (p2 :: P') - 1))%nat) by (cbn [length]; lia).
        rewrite Hc, strncmp.walk_go by assumption.
        assert (HN : p2 :: P' <> []) by discriminate.
        destruct (IH k HN HF HK') as (v & Hw & Hv & Hiff).
        exists v. split; [exact Hw|]. split; [exact Hv|].
        rewrite Hiff. change (firstn (length (p :: p2 :: P')) (p :: k)) with (p :: firstn (length (p2 :: P')) k).
        split; [intros E; rewrite E; reflexivity | intros E; injection E as E; exact E].
    + exists (bv_unsigned x - bv_unsigned p).
      rewrite strncmp.walk_stop by (right; right; right; exact Nxp).
      split; [reflexivity|]. split; [lia|].
      split; [intros E; lia | intros E; cbn [length firstn] in E; injection E as E _; subst x; exfalso; exact (Nxp eq_refl)].
Qed.

Lemma HA_PREFIX_len : length HA_PREFIX = 13%nat.
Proof. reflexivity. Qed.

Lemma HA_PREFIX_nz : Forall (fun b : byte => bv_unsigned b <> 0) HA_PREFIX.
Proof.
  apply Forall_forall. intros b Hb.
  assert (F : forallb (fun b : byte => negb (bv_unsigned b =? 0)) HA_PREFIX = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. specialize (F b Hb). apply negb_true_iff, Z.eqb_neq in F. exact F.
Qed.

(** strncmp(k, prefix, 13) on the C string k and the NUL-terminated prefix: a byte difference, 0 exactly when k has
    the prefix. *)
Lemma strncmp_prefix : forall k, ~ In NUL k ->
  exists v, StrFun.strncmp_model (k ++ [NUL]) (HA_PREFIX ++ [NUL]) 13 = Some v /\ -256 < v < 256 /\
            (v = 0 <-> ha_prefix k = true).
Proof.
  intros k HK.
  assert (HN : HA_PREFIX <> []) by (intros E; pose proof HA_PREFIX_len as L; rewrite E in L; discriminate L).
  destruct (walk_prefix HA_PREFIX k HN HA_PREFIX_nz HK) as (v & Hw & Hv & Hiff).
  exists v. split; [|split; [exact Hv|]].
  - unfold StrFun.strncmp_model. rewrite HA_PREFIX_len in Hw. exact Hw.
  - unfold ha_prefix. rewrite bytes_eqb_eq. exact Hiff.
Qed.

(** ** pod_next_pair over the entries left (Pod/Accessors.v [pairs_by key_of]) *)
Lemma pairs_skip : forall (es : list ent) i, (i < length es)%nat -> key_of (nth i es (Ent 0 0 [])) = None ->
  pairs_by key_of (skipn i es) None = pairs_by key_of (skipn (S i) es) None.
Proof. intros es i Hi HK. rewrite (skipn_nth_cons es i (Ent 0 0 []) Hi). cbn [pairs_by]. rewrite HK. reflexivity. Qed.

Lemma pairs_key : forall (es : list ent) i k, (i < length es)%nat -> key_of (nth i es (Ent 0 0 [])) = Some k ->
  pairs_by key_of (skipn i es) None = pairs_by key_of (skipn (S i) es) (Some k).
Proof. intros es i k Hi HK. rewrite (skipn_nth_cons es i (Ent 0 0 []) Hi). cbn [pairs_by]. rewrite HK. reflexivity. Qed.

Lemma pairs_value : forall (es : list ent) i k, (S i < length es)%nat ->
  pairs_by key_of (skipn (S i) es) (Some k) =
  (k, nth (S i) es (Ent 0 0 [])) :: pairs_by key_of (skipn (S (S i)) es) None.
Proof. intros es i k Hi. rewrite (skipn_nth_cons es (S i) (Ent 0 0 []) Hi). reflexivity. Qed.

Lemma pairs_end : forall (es : list ent) j ko, (length es <= j)%nat -> pairs_by key_of (skipn j es) ko = [].
Proof. intros es j ko H. rewrite skipn_all2 by lia. reflexivity. Qed.

(** ** One step of [ha_fold] *)
Lemma ha_fold_skip : forall f cap k v ps cells keys rf, ha_prefix k = false ->
  ha_fold f cap ((k, v) :: ps) cells keys rf = ha_fold f cap ps cells keys rf.
Proof. intros f cap k v ps cells keys rf H. cbn [ha_fold]. rewrite H. reflexivity. Qed.

Lemma ha_fold_bad : forall f cap k v ps cells keys rf bad, ha_prefix k = true -> f k v = inl bad ->
  ha_fold f cap ((k, v) :: ps) cells keys rf =
  ha_fold f cap ps cells (keys + 1) (if rf =? REFUSE_NONE then bad else rf).
Proof. intros f cap k v ps cells keys rf bad H1 H2. cbn [ha_fold]. rewrite H1, H2. reflexivity. Qed.

Lemma ha_fold_full : forall f cap k v ps cells keys rf c, ha_prefix k = true -> f k v = inr c ->
  cap <= Z.of_nat (length cells) -> ha_fold f cap ((k, v) :: ps) cells keys rf = (cells, keys + 1, rf).
Proof.
  intros f cap k v ps cells keys rf c H1 H2 H3. cbn [ha_fold]. rewrite H1, H2, (proj2 (Z.leb_le _ _) H3). reflexivity.
Qed.

Lemma ha_fold_add : forall f cap k v ps cells keys rf c, ha_prefix k = true -> f k v = inr c ->
  Z.of_nat (length cells) < cap ->
  ha_fold f cap ((k, v) :: ps) cells keys rf = ha_fold f cap ps (cells ++ [c]) (keys + 1) rf.
Proof.
  intros f cap k v ps cells keys rf c H1 H2 H3. cbn [ha_fold]. rewrite H1, H2, (proj2 (Z.leb_gt _ _) H3). reflexivity.
Qed.

Lemma ha_fold_nil : forall f cap cells keys rf, ha_fold f cap [] cells keys rf = (cells, keys, rf).
Proof. reflexivity. Qed.

(** The refusals of one pair are BAD_KEY and OUT_OF_RANGE. *)
Lemma expect_cell_bad : forall k v bad, expect_cell k v = inl bad ->
  bad = REFUSE_BAD_KEY \/ bad = REFUSE_OUT_OF_RANGE.
Proof.
  intros k v bad H. unfold expect_cell in H.
  destruct (expect_key (skipn (length HA_PREFIX) k)) as [| |ch p]; cbv zeta in H.
  - injection H as <-. left; reflexivity.
  - injection H as <-. right; reflexivity.
  - destruct ((cell_value v <? 0) || ((if p =? HA_SENS then HA_SENS_MAX else 1) <? cell_value v)).
    + injection H as <-. right; reflexivity.
    + discriminate H.
Qed.

(** ** x past x->rc *)
(** The cells part of x: the cells written, then zero cells up to ten. *)
Definition x_cellz (cells : list cell) : list byte :=
  x_cells_bytes cells ++ repeat (Z_to_bv 8 0) (12 * (X_CELLS - length cells)).

Lemma length_x_cellz : forall cells, (length cells <= X_CELLS)%nat -> length (x_cellz cells) = 120%nat.
Proof.
  intros cells H. unfold x_cellz. rewrite length_app, length_x_cells_bytes, repeat_length. unfold X_CELLS in *. lia.
Qed.

Lemma x_tail_res : forall cells keys rf,
  x_tail (ha_result (cells, keys, rf)) =
  x_cellz cells ++ le4 (Z_to_bv 64 (Z.of_nat (length cells))) ++ le4 (Z_to_bv 64 keys) ++ le4 (Z_to_bv 64 rf).
Proof. intros cells keys rf. unfold x_cellz. rewrite <- app_assoc. reflexivity. Qed.

Lemma le4_zero : le4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof. vm_compute. reflexivity. Qed.

(** The answer of the NULL flag, of no props and of no params: x past x->rc is 132 zero bytes. *)
Lemma x_tail_empty : forall rc, x_tail (rc, [], (0, 0, REFUSE_NONE)) = repeat (Z_to_bv 8 0) 132.
Proof. intros rc. vm_compute. reflexivity. Qed.

(** The next cell, while fewer than ten are written: three zero ints. *)
Lemma x_cellz_open : forall cells, (length cells < X_CELLS)%nat ->
  x_cellz cells =
  x_cells_bytes cells ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++
  repeat (Z_to_bv 8 0) (12 * (X_CELLS - S (length cells))).
Proof.
  intros cells H. unfold x_cellz. f_equal.
  replace (12 * (X_CELLS - length cells))%nat with (4 + (4 + (4 + 12 * (X_CELLS - S (length cells)))))%nat
    by (unfold X_CELLS in *; lia).
  rewrite !repeat_app, le4_zero. reflexivity.
Qed.

(** ... and after the cell (ch, p, v) is written there. *)
Lemma x_cellz_add : forall cells ch p v, (length cells < X_CELLS)%nat ->
  x_cellz (cells ++ [(ch, p, v)]) =
  x_cells_bytes cells ++ le4 (Z_to_bv 64 ch) ++ le4 (Z_to_bv 64 p) ++ le4 (Z_to_bv 64 v) ++
  repeat (Z_to_bv 8 0) (12 * (X_CELLS - S (length cells))).
Proof.
  intros cells ch p v H. unfold x_cellz, x_cells_bytes. rewrite flat_map_app, length_app. cbn [flat_map length].
  rewrite app_nil_r, Nat.add_1_r. cbn [x_cell_bytes]. rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Memory *)
Section Gen.
Variable segs : list Segment.

(** A store of as many bytes as Y has over Y in a run X ++ Y ++ Z. *)
Lemma bytes_at_write_mid : forall m A X Y Y' Z,
  bytes_at segs m A (X ++ Y ++ Z) -> length Y' = length Y ->
  bytes_at segs (write_to_mem m (wa (A + Z.of_nat (length X))) Y') A (X ++ Y' ++ Z).
Proof.
  intros m A X Y Y' Z H L.
  pose proof H as (H0 & H1 & _). rewrite !length_app in H1.
  apply bytes_at_app in H as [HX H]. apply bytes_at_app in H as [HY HZ].
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HX | lia | lia | lia].
  - apply bytes_at_app. split.
    + apply bytes_at_write_same; lia.
    + apply bytes_at_write_other; [rewrite L; exact HZ | lia | lia | lia].
Qed.

(** n bytes of the stack region: a writable block holding what it holds (memset's precondition). *)
Lemma stk_rw_cells : forall m lo hi A (n : nat), stk segs m lo hi -> lo <= A -> A + Z.of_nat n <= hi ->
  exists junk, length junk = n /\ rw_cells segs m A [CB n junk].
Proof.
  intros m lo hi A n Hs H1 H2. pose proof Hs as (S1 & S2 & S).
  assert (Hs' : stk segs m A (A + Z.of_nat n)).
  { split; [lia|]. split; [lia|]. intros a Ha. apply S. lia. }
  destruct (stk_bytes segs m A (A + Z.of_nat n) Hs' ltac:(lia)) as (bs & Hlen & Hb).
  replace (Z.to_nat (A + Z.of_nat n - A)) with n in Hlen by lia.
  exists bs. split; [exact Hlen|]. split.
  - split. { cbn. split; [lia | exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply S. lia.
Qed.

End Gen.
