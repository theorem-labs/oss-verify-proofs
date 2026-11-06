(* Model lemmas for batch u8 (C01-C06, W01-W04, X01, X02) of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan), ported from
   the plain batch b8 (a working branch lib/Prog/Seg/Tac_b8m.v) to the U model (CAT = 0x1fcc8): the frame cursor
   (u8_t_facts), the number of turns J (u8_fJ_ID), row_of_block (u8_row_hit, u8_row_none), want = want_m (u8_want_eq,
   C4.12), the classify facts C31 C1.8 (u8_cls_k, u8_cls_B, u8_cls_src, u8_cls_TF), the frame bytes, the id and
   frag lengths (from the u4 helpers) and
   memcmp_model's zero test. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcIdentModel RcFrag
  RcMatch RcClassify RcClassifyLib RcMatchLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel.
Import ListNotations.
Open Scope Z_scope.
(* The kernel compares cl_bsum fr with blocksum (skipn 18 fr) slowly unless cl_bsum is unfolded first. *)
#[local] Strategy expand [cl_bsum].

Lemma u8_bz_range : forall b, 0 <= bz b < 256.
Proof.
  intros b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma u8_nlen_nonneg : forall inp, 0 <= nlen inp.
Proof. intros inp. unfold nlen. lia. Qed.

Lemma u8_fL_nonneg : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb.
  pose proof (u8_bz_range (nthb inp (Z.to_nat c))). pose proof (u8_bz_range (nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma u8_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fc]. unfold c0. pose proof (u8_nlen_nonneg inp). lia.
  - change (fc inp (S j)) with (f_next inp (fc inp j)). pose proof (u8_fL_nonneg inp (fc inp j)).
    unfold f_next, f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma u8_t_facts : forall inp j,
  0 <= t_c inp j <= nlen inp /\ t_left inp j = nlen inp - t_c inp j /\
  0 <= t_h inp j <= t_left inp j /\ t_h inp j = Z.min 2 (t_left inp j) /\
  0 <= t_len inp j <= t_left inp j - t_h inp j /\
  t_body inp j = t_c inp j + t_h inp j /\ t_c inp (S j) = t_body inp j + t_len inp j /\
  t_left inp (S j) = t_left inp j - t_h inp j - t_len inp j.
Proof.
  intros inp j. pose proof (u8_fc_range inp j) as R. pose proof (u8_fL_nonneg inp (fc inp j)) as L.
  unfold t_c, t_left, t_h, t_len, t_body.
  change (fc inp (S j)) with (f_next inp (fc inp j)).
  unfold f_next, f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma u8_left0 : forall inp j, t_left inp j = 0 -> t_len inp j = 0 /\ fc inp (S j) = fc inp j.
Proof.
  intros inp j H. pose proof (u8_fL_nonneg inp (fc inp j)).
  unfold t_left, t_len in *. change (fc inp (S j)) with (f_next inp (fc inp j)).
  unfold f_next, f_body, f_len, f_h in *. rewrite H in *. lia.
Qed.

Lemma u8_turn0_id : forall s g, fs_id (turn s 0 g) = fs_id s.
Proof. intros s g. vm_compute. reflexivity. Qed.

Lemma u8_left0_ID : forall inp j, t_left inp j = 0 -> t_ID inp (S j) = t_ID inp j.
Proof.
  intros inp j H. destruct (u8_left0 inp j H) as [Hl _]. unfold t_ID. rewrite fst_at_S. rewrite Hl.
  apply u8_turn0_id.
Qed.

Lemma u8_left_stay0 : forall inp j k, t_left inp j = 0 -> t_left inp (k + j) = 0 /\ t_ID inp (k + j) = t_ID inp j.
Proof.
  intros inp j k H. induction k as [|k [IH1 IH2]]; [split; [exact H | reflexivity]|].
  change (S k + j)%nat with (S (k + j)).
  destruct (u8_left0 inp (k + j) IH1) as [_ Hc].
  split.
  - unfold t_left in *. rewrite Hc. exact IH1.
  - rewrite (u8_left0_ID inp (k + j) IH1). exact IH2.
Qed.

Lemma u8_fJ_from_spec : forall inp fuel j,
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

(* U14108 holds ID_J: at C06's exit (j + 1 = 256 or left_(j+1) = 0), ID_J = ID_(j+1). *)
Lemma u8_fJ_ID : forall inp j, (j <= 255)%nat -> (S j = 256%nat \/ t_left inp (S j) = 0) ->
  t_ID inp (fJ inp) = t_ID inp (S j).
Proof.
  intros inp j Hj Hx. unfold fJ.
  destruct (u8_fJ_from_spec inp 256 0) as (H1 & H2 & H3).
  set (J := fJ_from inp 0 256) in *.
  destruct (Nat.le_gt_cases J (S j)) as [HJ|HJ].
  - destruct (Nat.eq_dec J 256) as [E|E].
    + replace (S j) with J by lia. reflexivity.
    + assert (HL : t_left inp J = 0).
      { pose proof (H3 ltac:(lia)) as X. pose proof (u8_fc_range inp J). unfold t_left, f_left in *. lia. }
      destruct (u8_left_stay0 inp J (S j - J) HL) as [_ E2].
      replace (S j - J + J)%nat with (S j) in E2 by lia. symmetry. exact E2.
  - exfalso. destruct Hx as [Hx|Hx]; [lia|].
    pose proof (H2 (S j) ltac:(lia)). lia.
Qed.

(* row_of_block *)
Lemma u8_rob_hit : forall blk fuel k i, (k <= i < k + fuel)%nat -> decl_i (Z.of_nat i) = blk ->
  (forall i', (k <= i' < i)%nat -> blk <> decl_i (Z.of_nat i')) -> rob blk k fuel = CAT + CAT_ROW * Z.of_nat i.
Proof.
  intros blk fuel. induction fuel as [|f IH]; intros k i Hi E H; [lia|]. cbn [rob].
  destruct (Nat.eq_dec k i) as [->|Hne].
  - rewrite bool_decide_eq_true_2 by exact E. reflexivity.
  - rewrite bool_decide_eq_false_2 by (intros E'; apply (H k); [lia | symmetry; exact E']).
    apply IH; [lia | exact E | intros i' Hi'; apply H; lia].
Qed.

Lemma u8_rob_none : forall blk fuel k, (forall i', (k <= i' < k + fuel)%nat -> blk <> decl_i (Z.of_nat i')) ->
  rob blk k fuel = 0.
Proof.
  intros blk fuel. induction fuel as [|f IH]; intros k H; cbn [rob]; [reflexivity|].
  rewrite bool_decide_eq_false_2 by (intros E; apply (H k); [lia | symmetry; exact E]).
  apply IH. intros i' Hi'. apply H. lia.
Qed.

Lemma u8_row_hit : forall blk i, (i < 11)%nat -> decl_i (Z.of_nat i) = blk ->
  (forall i', (i' < i)%nat -> blk <> decl_i (Z.of_nat i')) -> row_of_block blk = CAT + CAT_ROW * Z.of_nat i.
Proof.
  intros blk i Hi E H. unfold row_of_block. apply u8_rob_hit; [lia | exact E | intros i' Hi'; apply H; lia].
Qed.

Lemma u8_row_none : forall blk, (forall i', (i' < 11)%nat -> blk <> decl_i (Z.of_nat i')) -> row_of_block blk = 0.
Proof. intros blk H. unfold row_of_block. apply u8_rob_none. intros i' Hi'. apply H. lia. Qed.

Lemma u8_bytes_inj : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma u8_lbytes_inj : forall l1 l2 : list (list byte), map (map bv_unsigned) l1 = map (map bv_unsigned) l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply u8_bytes_inj; exact H1 | apply IH; exact H2].
Qed.

Lemma u8_DECLS : DECLS = map (fun i => decl_i (Z.of_nat i)) (seq 0 11).
Proof. apply u8_lbytes_inj. vm_compute. reflexivity. Qed.

Lemma u8_cm_find_rob : forall blk n k,
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
Lemma u8_want_eq : forall inp j, t_want inp j = t_want_m inp j.
Proof.
  intros inp j. unfold t_want, t_want_m, want, t_rowsel, t_k.
  set (g := t_g inp j). set (len := t_len inp j).
  destruct (Z.eqb_spec (fst (ctrlparse len g)) 9) as [K|K].
  - assert (Hh : cp_hdr len g = true).
    { destruct (cp_hdr len g) eqn:E; [reflexivity|]. unfold ctrlparse in K. rewrite E in K. cbn in K. discriminate. }
    apply cp_hdr_spec in Hh as (H1 & H2 & H3).
    unfold cm_gate. rewrite K, H2, H3, (proj2 (Z.leb_le 50 len) H1). cbn [Z.eqb Pos.eqb andb].
    destruct (cp_v g 16 =? 205), (cp_v g 17 =? 234); cbn [andb]; try reflexivity.
    rewrite u8_DECLS. change (cm_blk g) with (t_blk inp j).
    exact (u8_cm_find_rob (t_blk inp j) 11 0).
  - unfold cm_gate. rewrite (proj2 (Z.eqb_neq _ _) K). rewrite !andb_false_r. reflexivity.
Qed.

(* classify = Some e (C31 C1.8) *)
Lemma u8_cl_eq6_refl : forall xs, cl_eq6 xs xs = true.
Proof. intros xs. unfold cl_eq6. apply forallb_forall. intros i _. apply Z.eqb_refl. Qed.

Lemma u8_struct_src : forall fr k,
  firstn 6 (skipn 4 (cp_struct fr k)) = [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11].
Proof. intros fr k. unfold cp_struct. destruct (cp_rec fr), (k =? 6); reflexivity. Qed.

Lemma u8_cls_k : forall inp j e, t_cls inp j = Some e -> t_k inp j <> 0 /\ 50 <= t_len inp j /\ 0 <= e <= 5.
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (classify_some _ _ _ _ H) as (K & HN & OUI & EQ6 & KB & He).
  split; [exact K|]. split; [exact HN | exact He].
Qed.

Lemma u8_cls_B : forall inp j e, t_cls inp j = Some e -> t_B inp j = cp_struct (t_g inp j) (t_k inp j).
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (classify_some _ _ _ _ H) as (K & HN & OUI & EQ6 & KB & He).
  destruct (cl_hdr _ _ K) as [_ HB]. exact HB.
Qed.

Lemma u8_cls_oui : forall inp j e, t_cls inp j = Some e ->
  cp_v (t_g inp j) 6 = 0 /\ cp_v (t_g inp j) 7 = 64 /\ cp_v (t_g inp j) 8 = 171.
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (classify_some _ _ _ _ H) as (K & HN & OUI & EQ6 & KB & He).
  unfold cl_oui in OUI. apply andb_prop in OUI as [OUI O8]. apply andb_prop in OUI as [O6 O7].
  apply Z.eqb_eq in O6, O7, O8. split; [exact O6|]. split; [exact O7 | exact O8].
Qed.

Lemma u8_cls_eq6 : forall inp j e, t_cls inp j = Some e -> cl_eq6 (skipn 6 (t_g inp j)) (OUR inp) = false.
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (classify_some _ _ _ _ H) as (K & HN & OUI & EQ6 & KB & He). exact EQ6.
Qed.

Lemma u8_src_eq6 : forall inp j, firstn 6 (skipn 4 (cp_struct (t_g inp j) (t_k inp j))) = OUR inp ->
  cl_eq6 (skipn 6 (t_g inp j)) (OUR inp) = true.
Proof.
  intros inp j E. rewrite u8_struct_src in E. rewrite <- cl_eq6_src. rewrite <- E. apply u8_cl_eq6_refl.
Qed.

Lemma u8_cls_src : forall inp j e, t_cls inp j = Some e -> firstn 6 (skipn 4 (t_B inp j)) <> OUR inp.
Proof.
  intros inp j e H E. rewrite (u8_cls_B inp j e H) in E. pose proof (u8_src_eq6 inp j E) as C.
  rewrite (u8_cls_eq6 inp j e H) in C. discriminate C.
Qed.

Lemma u8_TF_eq : forall inp j, 50 <= t_len inp j -> t_TF inp j =
  (blocksum (skipn 18 (t_g inp j)) =? 0) || ((cp_v (t_g inp j) 16 =? 0) && (cp_v (t_g inp j) 17 =? 0)).
Proof.
  intros inp j HN. unfold t_TF, t_sum_ok, t_tfill, t_big. rewrite (proj2 (Z.leb_le 50 (t_len inp j)) HN). reflexivity.
Qed.

Lemma u8_TF_gen : forall n fr us e, classify n fr us = Some e ->
  (blocksum (skipn 18 fr) =? 0) || ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0)) = true.
Proof.
  intros n fr us e H. destruct (classify_some _ _ _ _ H) as (_ & _ & _ & _ & KB & _).
  destruct KB as [K1|B0].
  - apply ctrlparse_filler in K1 as (_ & E16 & E17). rewrite E16, E17. apply orb_true_r.
  - unfold cl_bsum in B0. rewrite B0. reflexivity.
Qed.

Lemma u8_cls_TF : forall inp j e, t_cls inp j = Some e -> t_TF inp j = true.
Proof.
  intros inp j e H. pose proof (u8_cls_k inp j e H) as (_ & HN & _). unfold t_cls in H.
  rewrite (u8_TF_eq inp j HN). exact (u8_TF_gen _ _ _ _ H).
Qed.

Lemma u8_cls_none_r : forall c, RcClassify.cl_r c = 0 -> exists e, c = Some e.
Proof. intros [e|] H; [exists e; reflexivity | unfold RcClassify.cl_r in H; discriminate]. Qed.

(* Lengths and the frame's first 50 bytes. *)
Lemma u8_B_length : forall inp j, length (t_B inp j) = 36%nat.
Proof. intros inp j. apply ctrlparse_length. Qed.

Lemma u8_phi_length : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (u8_t_facts inp j) as (R & EL & RH & _ & HL & EB & _).
  unfold t_phi, f_phi. rewrite length_firstn, length_skipn.
  change (f_len inp (fc inp j)) with (t_len inp j). change (f_body inp (fc inp j)) with (t_body inp j).
  unfold nlen in *. lia.
Qed.

Lemma u8_fr50_firstn : forall bs, (50 <= length bs)%nat -> fr50 bs = firstn 50 bs.
Proof. intros bs H. unfold fr50. rewrite firstn_app. replace (50 - length bs)%nat with 0%nat by lia. apply app_nil_r. Qed.

Lemma u8_g_bytes : forall inp j, 50 <= t_len inp j -> t_g inp j = firstn 50 (t_phi inp j).
Proof. intros inp j H. unfold t_g. apply u8_fr50_firstn. rewrite u8_phi_length. lia. Qed.

Lemma u8_tg_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. apply fr50_length. Qed.

(* A record shorter than 50 bytes has k = 0 (struct P2.1); so k <> 0 gives len >= 50. *)
Lemma u8_k_big : forall inp j, t_k inp j <> 0 -> 50 <= t_len inp j /\ t_big inp j = true.
Proof.
  intros inp j H. destruct (Z_lt_le_dec (t_len inp j) 50) as [Hs|Hb].
  - exfalso. apply H. unfold t_k. apply ctrlparse_none. intros (Hn & _). lia.
  - split; [exact Hb|]. unfold t_big. apply Z.leb_le. exact Hb.
Qed.

Lemma u8_rowsel : forall inp j, t_rowsel inp j = true ->
  t_k inp j = 9 /\ cp_v (t_g inp j) 16 = 0xcd /\ cp_v (t_g inp j) 17 = 0xea /\ 50 <= t_len inp j /\
  t_big inp j = true.
Proof.
  intros inp j H. unfold t_rowsel in H. apply andb_prop in H as [H H17]. apply andb_prop in H as [H9 H16].
  apply Z.eqb_eq in H9, H16, H17.
  destruct (u8_k_big inp j ltac:(lia)) as [Hl Hb]. repeat split; assumption.
Qed.

(* ---- id and frag lengths (from the u4 helpers) ---- *)

Lemma u8_rpid_len : forall idb len g, length idb = 38%nat -> length (rp_id idb len g) = 38%nat.
Proof.
  intros idb len g H. unfold rp_id. destruct (RcReply.ir len g); [|exact H].
  apply RcIdentModel.ING_length. exact H.
Qed.

Lemma u8_fgid_len : forall idb len st g, length idb = 38%nat -> length (fg_id idb len st g) = 38%nat.
Proof.
  intros idb len st g H. unfold fg_id. destruct (fg_rf len st g =? 1); [|exact H].
  apply RcIdentModel.ING_length. exact H.
Qed.

Lemma u8_tID_len : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id];
    apply u8_fgid_len; apply u8_rpid_len; exact IH.
Qed.

Lemma u8_fgfr_n : forall len g, RcFrag.fg_fr len g = true -> 1 <= RcFrag.fg_n g <= 22.
Proof.
  intros len g H. unfold RcFrag.fg_fr in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  repeat match goal with
  | E : (_ <=? _) = true |- _ => apply Z.leb_le in E
  end.
  lia.
Qed.

Lemma u8_byte_nn : forall b : byte, 0 <= bv_unsigned b.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. lia. Qed.

Lemma u8_bat_nn : forall bs i, 0 <= RcFrag.bat bs i.
Proof. intros bs i. unfold RcFrag.bat. apply u8_byte_nn. Qed.

Lemma u8_body_len : forall g, length g = 50%nat -> 1 <= RcFrag.fg_n g <= 22 ->
  length (RcFrag.fg_body g) = Z.to_nat (RcFrag.fg_n g).
Proof.
  intros g Hg Hn. unfold RcFrag.fg_body, RcFrag.bsl. rewrite length_firstn, length_skipn, Hg. lia.
Qed.

(* The body that v1.9.0's `first` keeps is the body of a FIRST fragment: at most 22 bytes, so first's body bytes
   [sp+41, sp+63) lie in the low slots. *)
Lemma u8_tbody_len : forall inp j, (length (fs_body (fst_at inp j)) <= 22)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [apply Nat.leb_le; reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)) eqn:Eo; cbn [fs_body]; [|exact IH].
  unfold f_opens in Eo. apply andb_prop in Eo as [Efr _].
  pose proof (u8_fgfr_n _ _ Efr) as Hn.
  rewrite (u8_body_len _ (u8_tg_len inp j) Hn). lia.
Qed.

Lemma u8_clear_len : forall st, length st = 72%nat -> length (RcFrag.fg_clear st) = 72%nat.
Proof.
  intros st H. unfold RcFrag.fg_clear. rewrite !length_app, length_firstn, length_skipn, H. reflexivity.
Qed.

Lemma u8_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fg_next, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  pose proof (u8_fgfr_n len g Efr) as Hn. pose proof (u8_body_len g Hg Hn) as Hb.
  destruct (RcFrag.bat g 19 =? 1); cbn [negb].
  - unfold RcFrag.fg_first, RcFrag.bsl.
    rewrite !length_app, !length_firstn, !length_skipn, Hb, Hs, Hg. cbn [length]. lia.
  - destruct (RcFrag.fg_keep st g) eqn:Ek; cbn [negb]; [|apply u8_clear_len; exact Hs].
    unfold RcFrag.fg_keep in Ek. apply andb_true_iff in Ek as [_ Ek]. apply Z.leb_le in Ek.
    pose proof (u8_bat_nn st 7) as H7. unfold RcFrag.fg_T, RcFrag.fg_lf in Ek.
    assert (Hj : length (RcFrag.fg_join st g) = 72%nat).
    { unfold RcFrag.fg_join, RcFrag.fg_T, RcFrag.fg_lf.
      rewrite !length_app, length_firstn, Hb, length_skipn, Hs. lia. }
    destruct (RcFrag.fg_close st g); cbn [negb]; apply u8_clear_len; exact Hj.
Qed.

Lemma u8_tFG_len : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg];
    (apply u8_fgst_len; [exact IH | apply u8_tg_len]).
Qed.

(* ---- memcmp_model's zero test ---- *)

Lemma u8_mcmp : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v -> (v = 0 <-> l = r).
Proof.
  induction n as [|n IH]; intros [|a l] [|b r] v Hl Hr H; cbn [length] in Hl, Hr; try lia.
  - cbn in H. injection H as <-. split; intros; reflexivity.
  - cbn [memcmp_model] in H. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + rewrite (IH l r v ltac:(lia) ltac:(lia) H). assert (Eab : a = b) by (apply bv_eq; exact E). subst b.
      split; [intros ->; reflexivity | intros Heq; injection Heq; auto].
    + injection H as <-. split; [intros Hz; lia | intros Heq; injection Heq as -> ->; lia].
Qed.

Lemma u8_mcmp_total : forall l r n, length l = n -> length r = n -> exists v, memcmp_model l r n = Some v.
Proof. intros l r n Hl Hr. apply memcmp_model_total; lia. Qed.

Lemma u8_mcmp_rng : forall n l r v, memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v H.
  - cbn in H. injection H as <-. lia.
  - destruct l as [|a l]; destruct r as [|b r]; cbn [memcmp_model] in H; try discriminate.
    destruct (bv_unsigned a =? bv_unsigned b); [exact (IH l r v H)|].
    injection H as <-. pose proof (bv_unsigned_in_range 8 a) as Ha. pose proof (bv_unsigned_in_range 8 b) as Hb.
    unfold bv_modulus in Ha, Hb. change (2 ^ Z.of_N 8) with 256 in Ha, Hb. lia.
Qed.

(* A word built from a small integer is 0 exactly when the integer is. *)
Lemma u8_bv0 : forall v, -256 < v < 256 -> (Z_to_bv 64 v = Z_to_bv 64 0 <-> v = 0).
Proof.
  intros v Hv. split; [intros E | intros ->; reflexivity].
  apply (f_equal (@bv_unsigned 64)) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in E. Z.div_mod_to_equations. lia.
Qed.

(* Each declaration of the catalogue is 32 bytes. *)
Lemma u8_decl_len : forall i, (i < 11)%nat -> length (decl_i (Z.of_nat i)) = 32%nat.
Proof.
  intros i Hi. do 11 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma u8_blk_len : forall inp j, length (t_blk inp j) = 32%nat.
Proof. intros inp j. unfold t_blk, bsl. rewrite length_firstn, length_skipn, u8_tg_len. reflexivity. Qed.
