(* Model lemmas for batch b8 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): the frame cursor never passes n and left
   never grows (b8_fc_range, b8_left0), ID_j is stationary once left_j = 0 (b8_left_stay0), the number of turns J
   (b8_fJ_ID), row_of_block (b8_row_hit, b8_row_none), want = want_m (b8_want_eq, C4.12), the classify facts
   C31 C1.8 (b8_cls_k, b8_cls_B, b8_cls_oui, b8_cls_src, b8_cls_TF) and the frame bytes (b8_g_bytes).
   libreac v1.9.0: b8_body_len bounds the body of SlotModel.v's v1.9 fstate (the 35-byte `first` buffer). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcIdentModel RcFrag
  RcMatch RcClassify RcClassifyLib RcMatchLib SlotModel.
Import ListNotations.
Open Scope Z_scope.
(* The kernel compares cl_bsum fr with blocksum (skipn 18 fr) slowly unless cl_bsum is unfolded first. *)
#[local] Strategy expand [cl_bsum].

Lemma b8_bz_range : forall b, 0 <= bz b < 256.
Proof.
  intros b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma b8_nlen_nonneg : forall inp, 0 <= nlen inp.
Proof. intros inp. unfold nlen. lia. Qed.

Lemma b8_fL_nonneg : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb.
  pose proof (b8_bz_range (nthb inp (Z.to_nat c))). pose proof (b8_bz_range (nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma b8_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fc]. unfold c0. pose proof (b8_nlen_nonneg inp). lia.
  - change (fc inp (S j)) with (f_next inp (fc inp j)). pose proof (b8_fL_nonneg inp (fc inp j)).
    unfold f_next, f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma b8_t_facts : forall inp j,
  0 <= t_c inp j <= nlen inp /\ t_left inp j = nlen inp - t_c inp j /\
  0 <= t_h inp j <= t_left inp j /\ t_h inp j = Z.min 2 (t_left inp j) /\
  0 <= t_len inp j <= t_left inp j - t_h inp j /\
  t_body inp j = t_c inp j + t_h inp j /\ t_c inp (S j) = t_body inp j + t_len inp j /\
  t_left inp (S j) = t_left inp j - t_h inp j - t_len inp j.
Proof.
  intros inp j. pose proof (b8_fc_range inp j) as R. pose proof (b8_fL_nonneg inp (fc inp j)) as L.
  unfold t_c, t_left, t_h, t_len, t_body.
  change (fc inp (S j)) with (f_next inp (fc inp j)).
  unfold f_next, f_body, f_len, f_h, f_left in *. lia.
Qed.

(* left_j never grows. *)
Lemma b8_left_mono : forall inp j, t_left inp (S j) <= t_left inp j.
Proof. intros inp j. pose proof (b8_t_facts inp j) as (_ & _ & (Hh & _) & _ & (Hl & _) & _ & _ & E). lia. Qed.

Lemma b8_left_mono_k : forall inp j k, t_left inp (k + j) <= t_left inp j.
Proof.
  intros inp j k. induction k as [|k IH]; [apply Z.le_refl|].
  change (S k + j)%nat with (S (k + j)). pose proof (b8_left_mono inp (k + j)). lia.
Qed.

Lemma b8_left0 : forall inp j, t_left inp j = 0 -> t_len inp j = 0 /\ fc inp (S j) = fc inp j.
Proof.
  intros inp j H. pose proof (b8_fL_nonneg inp (fc inp j)).
  unfold t_left, t_len in *. change (fc inp (S j)) with (f_next inp (fc inp j)).
  unfold f_next, f_body, f_len, f_h in *. rewrite H in *. lia.
Qed.

Lemma b8_turn0_id : forall s g, fs_id (turn s 0 g) = fs_id s.
Proof. intros s g. vm_compute. reflexivity. Qed.

Lemma b8_left0_ID : forall inp j, t_left inp j = 0 -> t_ID inp (S j) = t_ID inp j.
Proof.
  intros inp j H. destruct (b8_left0 inp j H) as [Hl _]. unfold t_ID. rewrite fst_at_S. rewrite Hl.
  apply b8_turn0_id.
Qed.

Lemma b8_left_stay0 : forall inp j k, t_left inp j = 0 -> t_left inp (k + j) = 0 /\ t_ID inp (k + j) = t_ID inp j.
Proof.
  intros inp j k H. induction k as [|k [IH1 IH2]]; [split; [exact H | reflexivity]|].
  change (S k + j)%nat with (S (k + j)).
  destruct (b8_left0 inp (k + j) IH1) as [_ Hc].
  split.
  - unfold t_left in *. rewrite Hc. exact IH1.
  - rewrite (b8_left0_ID inp (k + j) IH1). exact IH2.
Qed.

Lemma b8_fJ_from_spec : forall inp fuel j,
  (j <= fJ_from inp j fuel <= j + fuel)%nat /\
  (forall j', (j <= j' < fJ_from inp j fuel)%nat -> 0 < t_left inp j') /\
  ((fJ_from inp j fuel < j + fuel)%nat -> t_left inp (fJ_from inp j fuel) <= 0).
Proof.
  intros inp fuel. induction fuel as [|f IH]; intros j; cbn [fJ_from].
  - split; [lia|]. split; intros; lia.
  - destruct (Z.ltb_spec 0 (f_left inp (fc inp j))) as [Hp|Hn].
    + destruct (IH (S j)) as (H1 & H2 & H3). split; [lia|]. split.
      * intros j' Hj'. destruct (Nat.eq_dec j' j) as [->|Hne]; [exact Hp|]. apply H2. lia.
      * intros Hlt. apply H3. lia.
    + split; [lia|]. split; [intros; lia|]. intros _. exact Hn.
Qed.

(* K13d80 holds ID_J: at C06's exit (j + 1 = 256 or left_(j+1) = 0), ID_J = ID_(j+1). *)
Lemma b8_fJ_ID : forall inp j, (j <= 255)%nat -> (S j = 256%nat \/ t_left inp (S j) = 0) ->
  t_ID inp (fJ inp) = t_ID inp (S j).
Proof.
  intros inp j Hj Hx. unfold fJ.
  destruct (b8_fJ_from_spec inp 256 0) as (H1 & H2 & H3).
  set (J := fJ_from inp 0 256) in *.
  destruct (Nat.le_gt_cases J (S j)) as [HJ|HJ].
  - destruct (Nat.eq_dec J 256) as [E|E].
    + replace (S j) with J by lia. reflexivity.
    + assert (HL : t_left inp J = 0).
      { pose proof (H3 ltac:(lia)) as X. pose proof (b8_fc_range inp J). unfold t_left, f_left in *. lia. }
      destruct (b8_left_stay0 inp J (S j - J) HL) as [_ E2].
      replace (S j - J + J)%nat with (S j) in E2 by lia. symmetry. exact E2.
  - exfalso. destruct Hx as [Hx|Hx]; [lia|].
    pose proof (H2 (S j) ltac:(lia)). lia.
Qed.

(* row_of_block *)
Lemma b8_rob_hit : forall blk fuel k i, (k <= i < k + fuel)%nat -> decl_i (Z.of_nat i) = blk ->
  (forall i', (k <= i' < i)%nat -> blk <> decl_i (Z.of_nat i')) -> rob blk k fuel = CAT + CAT_ROW * Z.of_nat i.
Proof.
  intros blk fuel. induction fuel as [|f IH]; intros k i Hi E H; [lia|]. cbn [rob].
  destruct (Nat.eq_dec k i) as [->|Hne].
  - rewrite bool_decide_eq_true_2 by exact E. reflexivity.
  - rewrite bool_decide_eq_false_2 by (intros E'; apply (H k); [lia | symmetry; exact E']).
    apply IH; [lia | exact E | intros i' Hi'; apply H; lia].
Qed.

Lemma b8_rob_none : forall blk fuel k, (forall i', (k <= i' < k + fuel)%nat -> blk <> decl_i (Z.of_nat i')) ->
  rob blk k fuel = 0.
Proof.
  intros blk fuel. induction fuel as [|f IH]; intros k H; cbn [rob]; [reflexivity|].
  rewrite bool_decide_eq_false_2 by (intros E; apply (H k); [lia | symmetry; exact E]).
  apply IH. intros i' Hi'. apply H. lia.
Qed.

Lemma b8_row_hit : forall blk i, (i < 11)%nat -> decl_i (Z.of_nat i) = blk ->
  (forall i', (i' < i)%nat -> blk <> decl_i (Z.of_nat i')) -> row_of_block blk = CAT + CAT_ROW * Z.of_nat i.
Proof.
  intros blk i Hi E H. unfold row_of_block. apply b8_rob_hit; [lia | exact E | intros i' Hi'; apply H; lia].
Qed.

Lemma b8_row_none : forall blk, (forall i', (i' < 11)%nat -> blk <> decl_i (Z.of_nat i')) -> row_of_block blk = 0.
Proof. intros blk H. unfold row_of_block. apply b8_rob_none. intros i' Hi'. apply H. lia. Qed.

Lemma b8_bytes_inj : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma b8_lbytes_inj : forall l1 l2 : list (list byte), map (map bv_unsigned) l1 = map (map bv_unsigned) l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply b8_bytes_inj; exact H1 | apply IH; exact H2].
Qed.

Lemma b8_DECLS : DECLS = map (fun i => decl_i (Z.of_nat i)) (seq 0 11).
Proof. apply b8_lbytes_inj. vm_compute. reflexivity. Qed.

Lemma b8_cm_find_rob : forall blk n k,
  match cm_find blk (map (fun i => decl_i (Z.of_nat i)) (seq k n)) with
  | Some j => CAT + 296 * Z.of_nat (k + j) | None => 0 end = rob blk k n.
Proof.
  intros blk n. induction n as [|n IH]; intros k; [reflexivity|].
  cbn [seq map cm_find rob].
  destruct (decide (decl_i (Z.of_nat k) = blk)) as [E|E].
  - rewrite !bool_decide_eq_true_2 by exact E. unfold CAT_ROW. lia.
  - rewrite !bool_decide_eq_false_2 by exact E. rewrite <- (IH (S k)).
    destruct (cm_find blk (map (fun i => decl_i (Z.of_nat i)) (seq (S k) n))) as [j|]; cbn [option_map];
      [lia | reflexivity].
Qed.

(* C4.12 with struct P5.5: the catalogue match equals the harness's row_of_block. *)
Lemma b8_want_eq : forall inp j, t_want inp j = t_want_m inp j.
Proof.
  intros inp j. unfold t_want, t_want_m, want, t_rowsel, t_k.
  set (g := t_g inp j). set (len := t_len inp j).
  destruct (Z.eqb_spec (fst (ctrlparse len g)) 9) as [K|K].
  - assert (Hh : cp_hdr len g = true).
    { destruct (cp_hdr len g) eqn:E; [reflexivity|]. unfold ctrlparse in K. rewrite E in K. cbn in K. discriminate. }
    apply cp_hdr_spec in Hh as (H1 & H2 & H3).
    unfold cm_gate. rewrite K, H2, H3, (proj2 (Z.leb_le 50 len) H1). cbn [Z.eqb Pos.eqb andb].
    destruct (cp_v g 16 =? 205), (cp_v g 17 =? 234); cbn [andb]; try reflexivity.
    rewrite b8_DECLS. change (cm_blk g) with (t_blk inp j).
    exact (b8_cm_find_rob (t_blk inp j) 11 0).
  - unfold cm_gate. rewrite (proj2 (Z.eqb_neq _ _) K). rewrite !andb_false_r. reflexivity.
Qed.

(* classify = Some e (C31 C1.8) *)
Lemma b8_cl_eq6_refl : forall xs, cl_eq6 xs xs = true.
Proof. intros xs. unfold cl_eq6. apply forallb_forall. intros i _. apply Z.eqb_refl. Qed.

Lemma b8_cl_eq6_eq : forall xs ys, length xs = 6%nat -> length ys = 6%nat -> cl_eq6 xs ys = true -> xs = ys.
Proof.
  intros xs ys Hx Hy H.
  assert (E : forall i, (i < 6)%nat -> bv_unsigned (nth i xs cp_z) = bv_unsigned (nth i ys cp_z)).
  { intros i Hi. unfold cl_eq6 in H. rewrite forallb_forall in H. apply Z.eqb_eq. apply H. apply in_seq. lia. }
  apply (nth_ext xs ys cp_z cp_z); [lia|]. intros i Hi. apply bv_eq. apply E. lia.
Qed.
Lemma b8_struct_src : forall fr k,
  firstn 6 (skipn 4 (cp_struct fr k)) = [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11].
Proof. intros fr k. unfold cp_struct. destruct (cp_rec fr), (k =? 6); reflexivity. Qed.

Lemma b8_struct_nth : forall fr k i, (i < 6)%nat -> nth (4 + i) (cp_struct fr k) cp_z = cp_b fr (6 + i).
Proof.
  intros fr k i Hi. unfold cp_struct.
  destruct i as [|[|[|[|[|[|?]]]]]]; try lia; destruct (cp_rec fr), (k =? 6); reflexivity.
Qed.

Lemma b8_cls_k : forall inp j e, t_cls inp j = Some e -> t_k inp j <> 0 /\ 50 <= t_len inp j /\ 0 <= e <= 5.
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (classify_some _ _ _ _ H) as (K & HN & OUI & EQ6 & KB & He).
  split; [exact K|]. split; [exact HN | exact He].
Qed.

Lemma b8_cls_B : forall inp j e, t_cls inp j = Some e -> t_B inp j = cp_struct (t_g inp j) (t_k inp j).
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (classify_some _ _ _ _ H) as (K & HN & OUI & EQ6 & KB & He).
  destruct (cl_hdr _ _ K) as [_ HB]. exact HB.
Qed.

Lemma b8_cls_oui : forall inp j e, t_cls inp j = Some e ->
  cp_v (t_g inp j) 6 = 0 /\ cp_v (t_g inp j) 7 = 64 /\ cp_v (t_g inp j) 8 = 171.
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (classify_some _ _ _ _ H) as (K & HN & OUI & EQ6 & KB & He).
  unfold cl_oui in OUI. apply andb_prop in OUI as [OUI O8]. apply andb_prop in OUI as [O6 O7].
  apply Z.eqb_eq in O6, O7, O8. split; [exact O6|]. split; [exact O7 | exact O8].
Qed.

Lemma b8_cls_eq6 : forall inp j e, t_cls inp j = Some e -> cl_eq6 (skipn 6 (t_g inp j)) (OUR inp) = false.
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (classify_some _ _ _ _ H) as (K & HN & OUI & EQ6 & KB & He). exact EQ6.
Qed.

Lemma b8_src_eq6 : forall inp j, firstn 6 (skipn 4 (cp_struct (t_g inp j) (t_k inp j))) = OUR inp ->
  cl_eq6 (skipn 6 (t_g inp j)) (OUR inp) = true.
Proof.
  intros inp j E. rewrite b8_struct_src in E. rewrite <- cl_eq6_src. rewrite <- E. apply b8_cl_eq6_refl.
Qed.

Lemma b8_cls_src : forall inp j e, t_cls inp j = Some e -> firstn 6 (skipn 4 (t_B inp j)) <> OUR inp.
Proof.
  intros inp j e H E. rewrite (b8_cls_B inp j e H) in E. pose proof (b8_src_eq6 inp j E) as C.
  rewrite (b8_cls_eq6 inp j e H) in C. discriminate C.
Qed.

Lemma b8_TF_eq : forall inp j, 50 <= t_len inp j -> t_TF inp j =
  (blocksum (skipn 18 (t_g inp j)) =? 0) || ((cp_v (t_g inp j) 16 =? 0) && (cp_v (t_g inp j) 17 =? 0)).
Proof.
  intros inp j HN. unfold t_TF, t_sum_ok, t_tfill, t_big. rewrite (proj2 (Z.leb_le 50 (t_len inp j)) HN). reflexivity.
Qed.

Lemma b8_TF_sum : forall inp j, 50 <= t_len inp j -> blocksum (skipn 18 (t_g inp j)) = 0 -> t_TF inp j = true.
Proof. intros inp j HN B0. rewrite (b8_TF_eq inp j HN). rewrite B0. reflexivity. Qed.

Lemma b8_TF_fill : forall inp j, 50 <= t_len inp j -> cp_v (t_g inp j) 16 = 0 -> cp_v (t_g inp j) 17 = 0 ->
  t_TF inp j = true.
Proof. intros inp j HN E16 E17. rewrite (b8_TF_eq inp j HN). rewrite E16, E17. apply orb_true_r. Qed.

Lemma b8_TF_gen : forall n fr us e, classify n fr us = Some e ->
  (blocksum (skipn 18 fr) =? 0) || ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0)) = true.
Proof.
  intros n fr us e H. destruct (classify_some _ _ _ _ H) as (_ & _ & _ & _ & KB & _).
  destruct KB as [K1|B0].
  - apply ctrlparse_filler in K1 as (_ & E16 & E17). rewrite E16, E17. apply orb_true_r.
  - unfold cl_bsum in B0. rewrite B0. reflexivity.
Qed.

Lemma b8_cls_TF : forall inp j e, t_cls inp j = Some e -> t_TF inp j = true.
Proof.
  intros inp j e H. pose proof (b8_cls_k inp j e H) as (_ & HN & _). unfold t_cls in H.
  rewrite (b8_TF_eq inp j HN). exact (b8_TF_gen _ _ _ _ H).
Qed.

Lemma b8_cls_none_r : forall c, RcClassify.cl_r c = 0 -> exists e, c = Some e.
Proof. intros [e|] H; [exists e; reflexivity | unfold RcClassify.cl_r in H; discriminate]. Qed.

Lemma b8_cls_r : forall c, RcClassify.cl_r c = 0 \/ RcClassify.cl_r c = -1.
Proof. intros [e|]; [left | right]; reflexivity. Qed.

(* Lengths *)
Lemma b8_B_length : forall inp j, length (t_B inp j) = 36%nat.
Proof. intros inp j. apply ctrlparse_length. Qed.

Lemma b8_phi_length : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (b8_t_facts inp j) as (R & EL & RH & _ & HL & EB & _).
  unfold t_phi, f_phi. rewrite length_firstn, length_skipn.
  change (f_len inp (fc inp j)) with (t_len inp j). change (f_body inp (fc inp j)) with (t_body inp j).
  unfold nlen in *. lia.
Qed.

Lemma b8_fr50_firstn : forall bs, (50 <= length bs)%nat -> fr50 bs = firstn 50 bs.
Proof. intros bs H. unfold fr50. rewrite firstn_app. replace (50 - length bs)%nat with 0%nat by lia. apply app_nil_r. Qed.

Lemma b8_g_bytes : forall inp j, 50 <= t_len inp j -> t_g inp j = firstn 50 (t_phi inp j).
Proof. intros inp j H. unfold t_g. apply b8_fr50_firstn. rewrite b8_phi_length. lia. Qed.

Lemma b8_g_nth : forall inp j i, 50 <= t_len inp j -> (i < 50)%nat ->
  nth i (t_g inp j) cp_z = nth i (t_phi inp j) cp_z.
Proof.
  intros inp j i H Hi. rewrite b8_g_bytes by exact H. rewrite nth_firstn.
  destruct (Nat.ltb_spec i 50); [reflexivity | lia].
Qed.

Lemma b8_fz_le_len : forall l, (first_zero l <= length l)%nat.
Proof. induction l as [|b l IH]; cbn; [lia|]. destruct (bz b =? 0); lia. Qed.

Lemma b8_fz_mn : forall idb, (first_zero (model_name idb) <= 17)%nat.
Proof.
  intros idb. pose proof (b8_fz_le_len (model_name idb)) as H. unfold model_name, get, NAME_CAP in *.
  rewrite length_firstn in H. lia.
Qed.

(* Lengths of ID_j (38) and FG_j (72). *)
Lemma b8_rp_len : forall idb len g, length idb = 38%nat -> length (rp_id idb len g) = 38%nat.
Proof. intros idb len g H. unfold rp_id. destruct (ir len g); [apply ING_length; exact H | exact H]. Qed.

Lemma b8_fg_id_len : forall idb len st g, length idb = 38%nat -> length (fg_id idb len st g) = 38%nat.
Proof. intros idb len st g H. unfold fg_id. destruct (fg_rf len st g =? 1); [apply ING_length; exact H | exact H]. Qed.

Lemma b8_turn_id : forall s len g, fs_id (turn s len g) = fg_id (rp_id (fs_id s) len g) len (fs_fg s) g.
Proof. intros s len g. unfold turn. destruct (f_opens len g); reflexivity. Qed.

Lemma b8_turn_fg : forall s len g, fs_fg (turn s len g) = fg_st len (fs_fg s) g.
Proof. intros s len g. unfold turn. destruct (f_opens len g); reflexivity. Qed.

Lemma b8_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S, b8_turn_id. apply b8_fg_id_len, b8_rp_len, IH.
Qed.

Lemma b8_bsl_len : forall bs k n, 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) -> length (bsl bs k n) = Z.to_nat n.
Proof. intros bs k n H1 H2 H3. unfold bsl. rewrite length_firstn, length_skipn. lia. Qed.

Lemma b8_bat_range : forall bs i, 0 <= bat bs i < 256.
Proof. intros bs i. unfold bat. exact (b8_bz_range _). Qed.

Lemma b8_fg_n_range : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H H22]. apply andb_prop in H as [_ H1].
  apply Z.leb_le in H22, H1. lia.
Qed.

Lemma b8_fg_keep_T : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof. intros st g H. unfold fg_keep in H. apply andb_prop in H as [_ H]. apply Z.leb_le in H. exact H. Qed.

Lemma b8_fg_clear_len : forall st, length st = 72%nat -> length (fg_clear st) = 72%nat.
Proof. intros st H. unfold fg_clear. rewrite !length_app, length_firstn, length_skipn, H. reflexivity. Qed.

Lemma b8_fg_first_len : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  length (fg_first st g) = 72%nat.
Proof.
  intros st g Hs Hg Hn. unfold fg_first, fg_body. rewrite !length_app, length_skipn, Hs.
  rewrite (b8_bsl_len g 6 6), (b8_bsl_len g 27 (fg_n g)) by (rewrite ?Hg; lia). cbn [length]. lia.
Qed.

Lemma b8_fg_join_len : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  fg_T st g <= 64 -> length (fg_join st g) = 72%nat.
Proof.
  intros st g Hs Hg Hn HT. pose proof (b8_bat_range st 7) as Hl. unfold fg_T, fg_lf in *.
  unfold fg_join, fg_body, fg_T, fg_lf. rewrite !length_app, length_firstn, length_skipn, Hs.
  rewrite (b8_bsl_len g 27 (fg_n g)) by (rewrite ?Hg; lia). lia.
Qed.

Lemma b8_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, fg_class. cbn [Z.eqb orb Pos.eqb].
  destruct (fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  pose proof (b8_fg_n_range len g Efr) as Hn.
  destruct (bat g 19 =? 1); [apply b8_fg_first_len; assumption|].
  destruct (fg_keep st g) eqn:Ek; cbn [negb]; [|apply b8_fg_clear_len; exact Hs].
  pose proof (b8_fg_keep_T st g Ek) as HT.
  destruct (fg_close st g); cbn [negb fg_next]; apply b8_fg_clear_len, b8_fg_join_len; assumption.
Qed.

Lemma b8_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S, b8_turn_fg. apply b8_fg_st_len; [exact IH | apply fr50_length].
Qed.

Lemma b8_FGf_length : forall inp j, length (t_FGf inp j) = 72%nat.
Proof. intros inp j. unfold t_FGf. apply b8_fg_st_len; [apply b8_FG_length | apply fr50_length]. Qed.

(* v1.9.0's `first`: the body is at most the 23 bytes of a 50-byte frame after its byte 27 (fg_body). *)
Lemma b8_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
  unfold fg_body, bsl, t_g. rewrite length_firstn, length_skipn, fr50_length. lia.
Qed.

Lemma b8_mm_spec : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr H.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in H. inversion H. split; [tauto|lia].
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|]. cbn in Hl, Hr, H.
    pose proof (b8_bz_range a) as Ra. pose proof (b8_bz_range b) as Rb. unfold bz in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) H) as [I1 I2]. split; [|exact I2].
      apply bv_eq in E. subst b. split.
      * intros Hv. f_equal. apply I1. exact Hv.
      * intros Hq. apply I1. injection Hq as Hq. exact Hq.
    + inversion H; subst v. split; [|lia]. split; [lia|]. intros Hq. injection Hq as Hab _. subst b. contradiction.
Qed.

Lemma b8_rowsel_big : forall inp j, t_rowsel inp j = true -> 50 <= t_len inp j.
Proof.
  intros inp j H. unfold t_rowsel, t_k in H. apply andb_prop in H as [H _]. apply andb_prop in H as [K _].
  apply Z.eqb_eq in K. destruct (cp_hdr (t_len inp j) (t_g inp j)) eqn:E.
  - apply cp_hdr_spec in E as (E1 & _). exact E1.
  - unfold ctrlparse in K. rewrite E in K. cbn in K. discriminate.
Qed.

Lemma b8_blk : forall inp j, 50 <= t_len inp j -> t_blk inp j = firstn 32 (skipn 18 (t_phi inp j)).
Proof.
  intros inp j H. unfold t_blk, bsl. rewrite b8_g_bytes by exact H.
  change (Z.to_nat 32) with 32%nat. change (Z.to_nat 18) with 18%nat.
  rewrite skipn_firstn_comm, firstn_firstn. reflexivity.
Qed.

