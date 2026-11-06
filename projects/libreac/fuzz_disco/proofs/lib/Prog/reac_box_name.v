From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model reac_box_name_c box_name_lemmas
  sb_dec_c memcpy_c strlen_c.
Import ListNotations.
Open Scope Z_scope.

Definition bbuf (m : word -> option byte) (A : Z) (n : nat) (c : list Z) : Prop :=
  exists r, (length c + length r = n)%nat /\ u8arr rsegs m A (bn_bytes c ++ r).

Lemma bn_bytes_length : forall c, length (bn_bytes c) = length c.
Proof. intros c. unfold bn_bytes. apply length_map. Qed.

Lemma bn_bytes_app : forall a b, bn_bytes (a ++ b) = bn_bytes a ++ bn_bytes b.
Proof. intros a b. unfold bn_bytes. apply map_app. Qed.

Lemma bbuf_bytes : forall m A n c, bbuf m A n c -> bytes_at rsegs m A (bn_bytes c).
Proof. intros m A n c (r & _ & B & _). apply bytes_at_app in B. tauto. Qed.

Lemma u8arr_stk : forall m A bs, u8arr rsegs m A bs -> stk rsegs m A (A + Z.of_nat (length bs)).
Proof.
  intros m A bs H. apply rw_cells_of_u8arr in H. apply stk_of_rw_cells in H.
  cbn [cells_size csize] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma bbuf_stk : forall m A n c, bbuf m A n c -> stk rsegs m A (A + Z.of_nat n).
Proof.
  intros m A n c (r & L & H). apply u8arr_stk in H. rewrite length_app, bn_bytes_length, L in H. exact H.
Qed.

Lemma wr_at_prefix : forall m A n k, wr_at rsegs m A n -> 0 <= k <= n -> wr_at rsegs m A k.
Proof. intros m A n k (H1 & H2 & H) Hk. split; [lia|]. split; [lia|]. intros j Hj. apply H. lia. Qed.

Lemma rw_CB_prefix : forall m A n j k, rw_cells rsegs m A [CB n j] -> (k <= n)%nat ->
  rw_cells rsegs m A [CB k (firstn k j)].
Proof.
  intros m A n j k [[Hwf Hb] Hw] Hk. cbn in Hwf. destruct Hwf as [Lj _].
  cbn [cells_bytes cbytes cells_size csize] in Hb, Hw. rewrite app_nil_r in Hb.
  split; [split|].
  - cbn. split; [rewrite length_firstn; lia|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite <- (firstn_skipn k j) in Hb.
    apply bytes_at_app in Hb. tauto.
  - cbn [cells_size csize]. eapply wr_at_prefix; [exact Hw|lia].
Qed.

Lemma stk_cpy : forall m m' lo hi d k bs,
  stk rsegs m lo hi -> munch [(d, d + k)] m m' -> Z.of_nat (length bs) = k -> wmono rsegs m m' ->
  bytes_at rsegs m' d bs -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi d k bs (H1 & H2 & H) MU <- WM (Hd & Hdl & HB). split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (Z.leb_spec d a) as [L1|L1]; [destruct (Z.ltb_spec a (d + Z.of_nat (length bs))) as [L2|L2]|].
  - replace a with (d + Z.of_nat (Z.to_nat (a - d))) by lia. rewrite HB by lia.
    destruct (nth_error bs (Z.to_nat (a - d))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn. split; [lia|exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn. split; [lia|exact I].
Qed.

Lemma bbuf_upd : forall m A n c r x,
  u8arr rsegs m A (upd (bn_bytes c ++ r) (Z.to_nat (Z.of_nat (length c))) (Z_to_bv 8 x)) ->
  (length c + length r = n)%nat -> (length c < n)%nat -> bbuf m A n (c ++ [x]).
Proof.
  intros m A n c r x H L Lt. destruct r as [|y r]; [cbn in L; lia|].
  rewrite Nat2Z.id in H. rewrite <- (bn_bytes_length c) in H at 1. rewrite bl_upd_mid in H.
  exists r. split; [rewrite length_app; cbn in L |- *; lia|].
  rewrite bn_bytes_app, <- app_assoc. exact H.
Qed.

Ltac bst H :=
  try lazymatch goal with |- context [le1 (Z_to_bv 64 ?c)] => rewrite (bl_le1 c) by lia end;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 (Z_to_bv 64 (?A + ?k)) [?b]) _) =>
      let H' := fresh "HW" in
      pose proof (u8arr_write rsegs m1 A _ k b H ltac:(rewrite ?length_app, ?bn_bytes_length; lia)) as H';
      clear H;
      store_done
  end.

Lemma bn_leq_eq : forall a b, bn_leq a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn; try (split; congruence).
  rewrite andb_true_iff, Z.eqb_eq, IH. split; [intros [-> ->]; reflexivity | intros E; inversion E; tauto].
Qed.

Definition dig_b (l : list Z) : bool := forallb (fun c => (48 <=? c) && (c <=? 57)) l.

Definition dec_chk (x : Z) : bool :=
  (0 <=? x) && (x <=? 40) && Nat.eqb (length (bn_dec x 2)) 2 && Nat.leb 1 (length (bn_dec x 1)) &&
  Nat.leb (length (bn_dec x 1)) 2 && bn_leq (sb_dec_D x 2) (bn_dec x 2) && bn_leq (sb_dec_D x 1) (bn_dec x 1) &&
  dig_b (bn_dec x 2) && dig_b (bn_dec x 1).

Lemma dig_b_ok : forall l, dig_b l = true -> Forall (fun c => 48 <= c <= 57) l.
Proof.
  intros l H. unfold dig_b in H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc.
  specialize (H c Hc). apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma bn_ok_dec : forall x, bn_ok x = true ->
  0 <= x <= 40 /\ length (bn_dec x 2) = 2%nat /\ (1 <= length (bn_dec x 1) <= 2)%nat /\
  sb_dec_D x 2 = bn_dec x 2 /\ sb_dec_D x 1 = bn_dec x 1 /\
  Forall (fun c => 48 <= c <= 57) (bn_dec x 2) /\ Forall (fun c => 48 <= c <= 57) (bn_dec x 1).
Proof.
  intros x H. apply bn_ok_in in H.
  assert (A : forallb dec_chk bn_oks = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A x H). unfold dec_chk in A.
  repeat match type of A with andb _ _ = true => apply andb_true_iff in A; destruct A as [A ?] end.
  repeat match goal with
  | E : Z.leb _ _ = true |- _ => apply Z.leb_le in E
  | E : Nat.leb _ _ = true |- _ => apply Nat.leb_le in E
  | E : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in E
  | E : bn_leq _ _ = true |- _ => apply bn_leq_eq in E
  | E : dig_b _ = true |- _ => apply dig_b_ok in E
  end.
  repeat split; first [assumption | lia].
Qed.

Lemma args_ok_split : forall nm nl tk tl dp dl x y, bn_args_ok nm nl tk tl dp dl x y = true ->
  nm <> 0 /\ tk <> 0 /\ dp <> 0 /\ nl <> 0 /\ tl <> 0 /\ dl <> 0 /\ bn_ok x = true /\ bn_ok y = true /\
  (x = 0 /\ y = 0 -> False).
Proof.
  intros nm nl tk tl dp dl x y H. unfold bn_args_ok in H.
  repeat match type of H with andb _ _ = true => apply andb_true_iff in H; destruct H as [H ?] end.
  repeat match goal with
  | E : negb (Z.eqb _ _) = true |- _ => apply negb_true_iff in E; apply Z.eqb_neq in E
  | E : negb (andb (Z.eqb _ _) (Z.eqb _ _)) = true |- _ => apply negb_true_iff in E
  end.
  repeat split; try assumption.
  intros [-> ->]. lazymatch goal with E : (0 =? 0) && (0 =? 0) = false |- _ => discriminate E end.
Qed.

Lemma bn_DP_len : forall l x y, bn_ok x = true -> bn_ok y = true ->
  (length l + 15 <= length (bn_DP l x y) <= length l + 17)%nat.
Proof.
  intros l x y Hx Hy. destruct (bn_ok_dec x Hx) as (_ & _ & Lx & _). destruct (bn_ok_dec y Hy) as (_ & _ & Ly & _).
  unfold bn_DP. rewrite !length_app. cbn [length]. lia.
Qed.

Lemma stk_glue : forall m lo mid A hi, stk rsegs m lo mid -> stk rsegs m A hi -> A = mid -> lo <= mid <= hi ->
  stk rsegs m lo hi.
Proof. intros m lo mid A hi H1 H2 E L. subst A. eapply stk_merge; eassumption. Qed.

Lemma stk_ext : forall m lo hi hi', stk rsegs m lo hi -> hi = hi' -> stk rsegs m lo hi'.
Proof. intros; subst; assumption. Qed.

Lemma outside_app : forall W W' x, outside (W ++ W') x -> outside W x /\ outside W' x.
Proof.
  induction W as [|[a b] W IH]; intros W' x H; cbn [app outside] in *; [split; [exact I|exact H]|].
  destruct H as [H1 H2]. destruct (IH W' x H2) as [A B]. split; [split; assumption|exact B].
Qed.

Lemma munch_snoc : forall W a b m m0 m1, munch W m m0 -> munch [(a, b)] m0 m1 -> munch (W ++ [(a, b)]) m m1.
Proof.
  intros W a b m m0 m1 H0 H1 x Hx. apply outside_app in Hx. destruct Hx as [A B].
  rewrite (H1 x B). apply H0. exact A.
Qed.

Lemma bl_ltu_l : forall a (y : word), 0 <= a < 2^64 -> bv_ltu (Z_to_bv 64 a) y = (a <? bv_unsigned y).
Proof. intros a y Ha. unfold bv_ltu. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma acc_eq : forall f sd i o nm nl tk tl dp dl, bn_args_ok nm nl tk tl dp dl i o = true ->
  bn_accept f sd i o nm nl tk tl dp dl =
  (Z.of_nat (length (bn_NM f sd i o)) <=? 23) && (Z.of_nat (length (bn_NM f sd i o)) <? nl) &&
  (Z.of_nat (length (bn_TK (bn_NM f sd i o))) <? tl) && (Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) <? dl).
Proof.
  intros f sd i o nm nl tk tl dp dl H. pose proof H as H'. unfold bn_args_ok in H'.
  repeat match type of H' with andb _ _ = true => apply andb_true_iff in H'; destruct H' as [H' ?] end.
  unfold bn_accept, bn_ret. rewrite H.
  repeat match goal with E : ?b = true |- context [?b] => rewrite E end.
  cbn [andb]. destruct (Z.of_nat (length (bn_NM f sd i o)) <=? 23); reflexivity.
Qed.

Ltac xport m0 m3 MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : rw_cells rsegs m0 ?A ?cs |- _ =>
      apply (rw_cells_transport rsegs W m0 m3 A cs) in H;
      [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; repeat split; first [exact I | lia]]
  | H : u8arr rsegs m0 ?A ?bs |- _ =>
      apply (u8arr_transport rsegs W m0 m3 A bs) in H;
      [| exact MU | exact WM | cbn [disjoint_from];
         rewrite ?length_app, ?bn_bytes_length, ?upd_length, ?length_app, ?bn_bytes_length; cbn [length];
         repeat split; first [exact I | lia]]
  | H : bytes_at rsegs m0 ?A ?bs |- _ =>
      apply (bytes_at_transport rsegs W m0 m3 A bs) in H;
      [| exact MU | cbn [disjoint_from];
         rewrite ?length_app, ?bn_bytes_length, ?length_app; cbn [length]; repeat split; first [exact I | lia]]
  end.

Lemma rec_bytes : forall p c n ov pad,
  cells_bytes [C8 p; C8 c; C8 n; C4 ov; C4 pad] = sb_rec p c n ov ++ le4 pad.
Proof. intros. unfold sb_rec. cbn [cells_bytes cbytes]. rewrite app_nil_r, <- !app_assoc. reflexivity. Qed.

Lemma sb_rec_length : forall p c n ov, length (sb_rec p c n ov) = 28%nat.
Proof. intros. unfold sb_rec. rewrite !length_app, !length_le8, length_le4. reflexivity. Qed.

Lemma rec_get : forall m A p c n ov pad, rw_cells rsegs m A [C8 p; C8 c; C8 n; C4 ov; C4 pad] ->
  bytes_at rsegs m A (sb_rec p c n ov) /\ bytes_at rsegs m (A + 28) (le4 pad) /\ wr_at rsegs m A 32.
Proof.
  intros m A p c n ov pad [[_ Hb] Hw]. rewrite rec_bytes in Hb. apply bytes_at_app in Hb.
  rewrite sb_rec_length in Hb. destruct Hb as [H1 H2]. split; [exact H1|]. split; [exact H2|exact Hw].
Qed.

Lemma rec_put : forall m A p c n ov pad,
  bytes_at rsegs m A (sb_rec p c n ov) -> bytes_at rsegs m (A + 28) (le4 pad) -> wr_at rsegs m A 32 ->
  rw_cells rsegs m A [C8 p; C8 c; C8 n; C4 ov; C4 pad].
Proof.
  intros m A p c n ov pad H1 H2 Hw. split; [split|].
  - cbn. repeat split.
  - rewrite rec_bytes. apply bytes_at_app. rewrite sb_rec_length. split; assumption.
  - exact Hw.
Qed.

Lemma wr_at_sub : forall m A n k l, wr_at rsegs m A n -> 0 <= k -> 0 <= l -> k + l <= n -> wr_at rsegs m (A + k) l.
Proof.
  intros m A n k l (H1 & H2 & H) Hk Hl Hkl. split; [lia|]. split; [lia|].
  intros j Hj. replace (A + k + j) with (A + (k + j)) by lia. apply H. lia.
Qed.

Lemma dec_big : forall v md cap n, 0 <= n -> n + 1 + Z.of_nat (length (sb_dec_D v md)) <= cap ->
  sb_dec_room cap n = cap - 1 - n /\ sb_dec_acc v md cap n = Z.of_nat (length (sb_dec_D v md)) /\
  (sb_dec_room cap n <? Z.of_nat (length (sb_dec_D v md))) = false.
Proof.
  intros v md cap n Hn H. unfold sb_dec_acc, sb_dec_room.
  replace (n + 1 <=? cap) with true by (symmetry; apply Z.leb_le; lia).
  split; [reflexivity|]. split; [lia|]. apply Z.ltb_ge. lia.
Qed.

Lemma bytes_at_keep : forall W m m' A bs, bytes_at rsegs m A bs -> munch W m m' ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m' A bs.
Proof.
  intros W m m' A bs (Ha & Hl & H) MU Ho. split; [lia|]. split; [lia|].
  intros j Hj. unfold mrd. rewrite MU; [apply H; exact Hj|]. rewrite wa_unsigned by lia. apply Ho. lia.
Qed.

Lemma bbuf_patch : forall W m m' A n c D,
  bbuf m A n c -> munch W m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' (A + Z.of_nat (length c)) (bn_bytes D) -> (length c + length D <= n)%nat ->
  (forall x, A <= x < A + Z.of_nat n -> x < A + Z.of_nat (length c) \/ A + Z.of_nat (length c + length D) <= x ->
             outside W x) ->
  bbuf m' A n (c ++ D).
Proof.
  intros W m m' A n c D (r & L & Hb & Hw) MU WM HD Hn Ho.
  exists (skipn (length D) r). split; [rewrite length_app, length_skipn; lia|].
  pose proof (bytes_at_bound rsegs _ _ _ Hb) as BB. rewrite length_app, bn_bytes_length in BB.
  apply bytes_at_app in Hb. destruct Hb as [Hc Hr]. rewrite bn_bytes_length in Hr.
  rewrite <- (firstn_skipn (length D) r) in Hr. apply bytes_at_app in Hr. destruct Hr as [_ Hr].
  rewrite length_firstn in Hr. replace (Nat.min (length D) (length r)) with (length D) in Hr by lia.
  split.
  - rewrite bn_bytes_app, <- app_assoc. apply bytes_at_app. split.
    + eapply bytes_at_keep; [exact Hc|exact MU|]. intros x Hx. apply Ho; rewrite bn_bytes_length in Hx; lia.
    + rewrite bn_bytes_length. apply bytes_at_app. split; [exact HD|]. rewrite bn_bytes_length.
      eapply bytes_at_keep; [exact Hr|exact MU|]. intros x Hx. rewrite length_skipn in Hx. apply Ho; lia.
  - eapply wr_at_transport; [|exact WM].
    rewrite length_app, bn_bytes_length, length_app, length_skipn.
    replace (Z.of_nat (length c + length D + (length r - length D))) with (Z.of_nat (length (bn_bytes c ++ r)))
      by (rewrite length_app, bn_bytes_length; lia).
    exact Hw.
Qed.

Lemma bbuf_loop : forall m B c r cm s,
  u8arr rsegs m B (sb_b (bn_bytes c ++ r) cm (Z.of_nat (length c)) s) -> 0 <= cm ->
  (length c <= Z.to_nat cm)%nat -> (length c + length r = Z.to_nat cm + 1)%nat ->
  bbuf m B (length c + length r) (firstn (Z.to_nat cm) (c ++ s)).
Proof.
  intros m B c r cm s H Hcm Hc L. unfold sb_b, upd_bytes in H.
  rewrite Nat2Z.id in H. rewrite <- (bn_bytes_length c) in H at 1. rewrite firstn_app_exact in H.
  rewrite skipn_app in H. rewrite skipn_all2 in H by (rewrite bn_bytes_length, bn_bytes_length; lia).
  rewrite bn_bytes_length, length_firstn in H.
  rewrite firstn_app. replace (firstn (Z.to_nat cm) c) with c by (symmetry; apply firstn_all2; lia).
  replace (Z.to_nat cm - length c)%nat with (Z.to_nat (cm - Z.of_nat (length c))) by lia.
  exists (skipn (Init.Nat.min (Z.to_nat (cm - Z.of_nat (length c))) (length s)) r).
  split.
  - rewrite length_app, length_firstn, length_skipn. lia.
  - rewrite bn_bytes_app, <- app_assoc. cbn [app] in H. rewrite bn_bytes_length in H.
    replace (length c + Init.Nat.min (Z.to_nat (cm - Z.of_nat (length c))) (length s) - length c)%nat
      with (Init.Nat.min (Z.to_nat (cm - Z.of_nat (length c))) (length s)) in H by lia.
    exact H.
Qed.

Lemma sb_no_over : forall cm n0 k ov, n0 + k <= cm -> sb_n cm n0 k = n0 + k /\ sb_o cm n0 k ov = ov.
Proof.
  intros cm n0 k ov H. unfold sb_n, sb_o. split; [lia|].
  replace (cm <? n0 + k) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma munch_sub : forall lo hi W m m0 m1, munch [(lo, hi)] m m0 -> munch W m0 m1 ->
  (forall x, outside [(lo, hi)] x -> outside W x) -> munch [(lo, hi)] m m1.
Proof. intros lo hi W m m0 m1 H0 H1 Hs x Hx. rewrite (H1 x (Hs _ Hx)). apply H0. exact Hx. Qed.

Ltac out_tac := intros ?x ?Hx; cbn [outside] in *; repeat split; first [exact I | intro; lia].

Ltac ulit_in H :=
  repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in H by lia end.
Ltac ulit :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

Ltac show := match goal with |- ?G => idtac "GOAL:" G end.

Section BoxName.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo f i o : Z) (display display_len : word)
          (sd : list Z).
Hypothesis DEC : sb_dec_contract.
Hypothesis MC : memcpy_contract.
Hypothesis SL : strlen_contract.

Notation S := (bv_unsigned sp).
Notation SVC := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Notation ACC := (bn_accept f sd i o (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
                   (bv_unsigned display) (bv_unsigned display_len)).
Notation NM := (bn_NM f sd i o).
Hypothesis HIM : bn_image m (S - BN_K) S.

Definition QQ : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo S /\
    (if ACC
     then a0' = Z_to_bv 64 0 /\
          munch [(S - BN_K, S);
                 (bv_unsigned a4, bv_unsigned a4 + Z.of_nat (length NM) + 1);
                 (bv_unsigned a6, bv_unsigned a6 + Z.of_nat (length (bn_TK NM)) + 1);
                 (bv_unsigned display, bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1)] m m' /\
          bytes_at rsegs m' (bv_unsigned a4) (bn_bytes (NM ++ [0])) /\
          bytes_at rsegs m' (bv_unsigned a6) (bn_bytes (bn_TK NM ++ [0])) /\
          bytes_at rsegs m' (bv_unsigned display) (bn_bytes (bn_DP NM i o ++ [0]))
     else a0' = Z_to_bv 64 (-1) /\ munch [(S - BN_K, S)] m m').

Definition bn_res (m2 : word -> option byte) (r : Z) : Prop :=
  if ACC
  then r = 0 /\
       munch [(S - BN_K, S);
              (bv_unsigned a4, bv_unsigned a4 + Z.of_nat (length NM) + 1);
              (bv_unsigned a6, bv_unsigned a6 + Z.of_nat (length (bn_TK NM)) + 1);
              (bv_unsigned display, bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1)] m m2 /\
       bytes_at rsegs m2 (bv_unsigned a4) (bn_bytes (NM ++ [0])) /\
       bytes_at rsegs m2 (bv_unsigned a6) (bn_bytes (bn_TK NM ++ [0])) /\
       bytes_at rsegs m2 (bv_unsigned display) (bn_bytes (bn_DP NM i o ++ [0]))
  else r = -1 /\ munch [(S - BN_K, S)] m m2.

Lemma seg_epi : forall (m2 : word -> option byte) (r : Z)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo + BN_K <= S ->
  stk rsegs m2 lo (S + -104) -> rw_cells rsegs m2 (S + -104) SVC -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  bn_res m2 r ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x15040) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    HLO ST2 SV2 WM2 MI2 RES.
  unfold BN_K in HLO.
  do 13 step.
  release_frame SV2 ST2 (bv_unsigned sp).
  do 2 step.
  apply evt_done. unfold QQ, bn_res in *.
  destruct ACC.
  - destruct RES as (-> & RES). do 15 eexists. exists m2. split; [reflexivity|].
    split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [reflexivity|exact RES].
  - destruct RES as (-> & RES). do 15 eexists. exists m2. split; [reflexivity|].
    split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [reflexivity|exact RES].
Qed.

Notation LN := (firstn 23 NM).
Notation NOV := (if 23 <? Z.of_nat (length NM) then 1 else 0).

Lemma seg_final : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) (jdb jgw jw : list byte) (pw : word),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272) [CB 32 jdb] ->
  bbuf m2 (S + -240) 48 (bn_DP LN i o) ->
  bbuf m2 (S + -192) 24 (bn_tk false LN ++ [0]) ->
  bbuf m2 (S + -168) 24 (LN ++ [0]) ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display (Z_to_bv 64 (S + -240))
                        (Z_to_bv 64 0) (Z_to_bv 64 48) x13 x14 x15 x16 x17 a4 a7 a5
                        (Z_to_bv 64 (Z.of_nat (length (bn_DP LN i o)))) x22
                        (Z_to_bv 64 (Z.of_nat (length (bn_tk false LN)))) display_len
                        (Z_to_bv 64 (Z.of_nat (length LN))) (Z_to_bv 64 NOV) (Z_to_bv 64 0) x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14fd4) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 jdb jgw jw pw
    HLO AOK BUFS ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 GW2.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  destruct DP2 as (rdp & Ldp & UDP). destruct TK2 as (rtk & Ltk & UTK). destruct NM2 as (rnm & Lnm & UNM).
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  pose proof (bn_DP_len LN i o OKI OKO) as LDP.
  assert (LLN : (length LN <= 23)%nat) by (rewrite length_firstn; lia).
  pose proof (bn_tk_len LN false) as LTK.
  step.
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  step. step.
  pose proof (u8arr_store_ok rsegs m2 (S + -240) _ (Z.of_nat (length (bn_DP LN i o))) _ UDP
                ltac:(rewrite length_app, bn_bytes_length; lia) eq_refl) as HST.
  step.
  bst UDP.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  pose proof (bbuf_upd _ _ 48 _ _ _ HW Ldp ltac:(lia)) as DP3. clear HW.
  assert (ST3 : stk rsegs m3 lo (S + -104)).
  { pose proof (stk_of_rw_cells rsegs _ _ _ DB2) as K1. cbn [cells_size csize] in K1.
    pose proof (bbuf_stk _ _ _ _ DP3) as K2.
    pose proof (u8arr_stk _ _ _ UTK) as K3. rewrite length_app, bn_bytes_length, Ltk in K3.
    pose proof (u8arr_stk _ _ _ UNM) as K4. rewrite length_app, bn_bytes_length, Lnm in K4.
    pose proof (stk_of_rw_cells rsegs _ _ _ WB2) as K5. cbn [cells_size csize] in K5.
    pose proof (stk_of_rw_cells rsegs _ _ _ GW2) as K6. cbn [cells_size csize] in K6.
    pose proof (stk_glue _ _ _ _ _ ST2 K1 ltac:(lia) ltac:(lia)) as G.
    pose proof (stk_glue _ _ _ _ _ G K2 ltac:(lia) ltac:(lia)) as G2.
    pose proof (stk_glue _ _ _ _ _ G2 K3 ltac:(lia) ltac:(lia)) as G3.
    pose proof (stk_glue _ _ _ _ _ G3 K4 ltac:(lia) ltac:(lia)) as G4.
    pose proof (stk_glue _ _ _ _ _ G4 K5 ltac:(lia) ltac:(lia)) as G5.
    pose proof (stk_glue _ _ _ _ _ G5 K6 ltac:(lia) ltac:(lia)) as G6.
    eapply stk_ext; [exact G6|lia]. }
  pose proof (acc_eq f sd i o _ _ _ _ _ _ AOK) as ACCE. unfold bn_TK in ACCE.
  assert (REF : forall (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    ACC = false ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp y5 y6 y7 a6 display (Z_to_bv 64 (-1)) y11 y12 y13 y14 y15
                          y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x15040) fc None m3 (seg_rom rsegs))).
  { intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 AF.
    eapply seg_epi; [unfold BN_K; lia | exact ST3 | exact SV2 | exact WM2 | exact MI2 |].
    unfold bn_res. rewrite AF. unfold BN_K. split; [reflexivity|exact MU2]. }
  destruct (Z.ltb_spec 23 (Z.of_nat (length NM))) as [OV|OV].
  - step. step. change (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 1)) with (Z_to_bv 64 1).
    step. step. step. step. if_true.
    apply REF. rewrite ACCE. replace (Z.of_nat (length NM) <=? 23) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
  - assert (EL : LN = NM) by (apply firstn_all2; lia).
    rewrite EL in *.
    step. step. change (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    step. step. step. step. if_false.
    step. if_false.
    step. rewrite bl_ltu_l by lia.
    destruct (Z.ltb_spec (Z.of_nat (length NM)) (bv_unsigned a5)) as [CN|CN]; cbn [negb].
    2: { apply REF. rewrite ACCE. replace (Z.of_nat (length NM) <=? 23) with true by (symmetry; apply Z.leb_le; lia).
         replace (Z.of_nat (length NM) <? bv_unsigned a5) with false by (symmetry; apply Z.ltb_ge; lia).
         reflexivity. }
    step. rewrite bl_ltu_l by lia.
    destruct (Z.ltb_spec (Z.of_nat (length (bn_tk false NM))) (bv_unsigned a7)) as [CT|CT]; cbn [negb].
    2: { apply REF. rewrite ACCE. replace (Z.of_nat (length NM) <=? 23) with true by (symmetry; apply Z.leb_le; lia).
         replace (Z.of_nat (length NM) <? bv_unsigned a5) with true by (symmetry; apply Z.ltb_lt; lia).
         replace (Z.of_nat (length (bn_tk false NM)) <? bv_unsigned a7) with false by (symmetry; apply Z.ltb_ge; lia).
         reflexivity. }
    step. rewrite bl_ltu_l by lia.
    destruct (Z.ltb_spec (Z.of_nat (length (bn_DP NM i o))) (bv_unsigned display_len)) as [CD|CD]; cbn [negb].
    2: { apply REF. rewrite ACCE. replace (Z.of_nat (length NM) <=? 23) with true by (symmetry; apply Z.leb_le; lia).
         replace (Z.of_nat (length NM) <? bv_unsigned a5) with true by (symmetry; apply Z.ltb_lt; lia).
         replace (Z.of_nat (length (bn_tk false NM)) <? bv_unsigned a7) with true by (symmetry; apply Z.ltb_lt; lia).
         replace (Z.of_nat (length (bn_DP NM i o)) <? bv_unsigned display_len) with false
           by (symmetry; apply Z.ltb_ge; lia).
         reflexivity. }
    assert (AT : ACC = true).
    { rewrite ACCE. replace (Z.of_nat (length NM) <=? 23) with true by (symmetry; apply Z.leb_le; lia).
      replace (Z.of_nat (length NM) <? bv_unsigned a5) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z.of_nat (length (bn_tk false NM)) <? bv_unsigned a7) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z.of_nat (length (bn_DP NM i o)) <? bv_unsigned display_len) with true by (symmetry; apply Z.ltb_lt; lia).
      reflexivity. }
    clear REF ACCE.
    destruct BUFS as ((jn & RN) & (jt & RT) & (jd & RD) & DN & DT & DD). cbn [disjoint_from] in DN, DT, DD.
    pose proof (rw_cells_bound rsegs _ _ _ RN) as BN. pose proof (rw_cells_bound rsegs _ _ _ RT) as BT.
    pose proof (rw_cells_bound rsegs _ _ _ RD) as BD. cbn [cells_size csize] in BN, BT, BD.
    pose proof (bv_unsigned_in_range 64 a5) as R5. pose proof (bv_unsigned_in_range 64 a7) as R7.
    pose proof (bv_unsigned_in_range 64 display_len) as R8. unfold bv_modulus in R5, R7, R8.
    assert (M1 : Z.of_nat (length NM) + 1 <= Z.min (bv_unsigned a5) 24) by lia.
    assert (M2 : Z.of_nat (length (bn_tk false NM)) + 1 <= Z.min (bv_unsigned a7) 24) by lia.
    assert (M3 : Z.of_nat (length (bn_DP NM i o)) + 1 <= Z.min (bv_unsigned display_len) 48) by lia.
    destruct DN as (DN1 & DN2 & DN3 & _). destruct DT as (DT1 & DT2 & _). destruct DD as (DD1 & _).
    assert (FN : bv_unsigned a4 + Z.of_nat (length NM) + 1 <= S - 288 \/ S <= bv_unsigned a4)
      by (clear - DN1 M1; lia).
    assert (FT : bv_unsigned a6 + Z.of_nat (length (bn_tk false NM)) + 1 <= S - 288 \/ S <= bv_unsigned a6)
      by (clear - DT1 M2; lia).
    assert (FD : bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1 <= S - 288 \/ S <= bv_unsigned display)
      by (clear - DD1 M3; lia).
    assert (FNT : bv_unsigned a4 + Z.of_nat (length NM) + 1 <= bv_unsigned a6 \/
                  bv_unsigned a6 + Z.of_nat (length (bn_tk false NM)) + 1 <= bv_unsigned a4)
      by (clear - DN2 M1 M2; lia).
    assert (FND : bv_unsigned a4 + Z.of_nat (length NM) + 1 <= bv_unsigned display \/
                  bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1 <= bv_unsigned a4)
      by (clear - DN3 M1 M3; lia).
    assert (FTD : bv_unsigned a6 + Z.of_nat (length (bn_tk false NM)) + 1 <= bv_unsigned display \/
                  bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1 <= bv_unsigned a6)
      by (clear - DT2 M2 M3; lia).
    assert (BN' : 0 <= bv_unsigned a4 /\ bv_unsigned a4 + Z.of_nat (length NM) + 1 <= 2^64) by (clear - BN M1; lia).
    assert (BT' : 0 <= bv_unsigned a6 /\ bv_unsigned a6 + Z.of_nat (length (bn_tk false NM)) + 1 <= 2^64)
      by (clear - BT M2; lia).
    assert (BD' : 0 <= bv_unsigned display /\ bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1 <= 2^64)
      by (clear - BD M3; lia).
    apply (rw_CB_prefix _ _ _ _ (Z.to_nat (Z.of_nat (length NM) + 1))) in RN; [|clear - M1; lia].
    apply (rw_CB_prefix _ _ _ _ (Z.to_nat (Z.of_nat (length (bn_tk false NM)) + 1))) in RT; [|clear - M2; lia].
    apply (rw_CB_prefix _ _ _ _ (Z.to_nat (Z.of_nat (length (bn_DP NM i o)) + 1))) in RD; [|clear - M3; lia].
    clear DN1 DN2 DN3 DT1 DT2 DD1 BN BT BD M1 M2 M3 R5 R7 R8.
    apply (rw_cells_transport rsegs [(S - 288, S)] m m3 _ _) in RN;
      [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; clear - FN; split; [lia|exact I]].
    apply (rw_cells_transport rsegs [(S - 288, S)] m m3 _ _) in RT;
      [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; clear - FT; split; [lia|exact I]].
    apply (rw_cells_transport rsegs [(S - 288, S)] m m3 _ _) in RD;
      [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; clear - FD; split; [lia|exact I]].
    destruct DP3 as (rdp3 & Ldp3 & UDP).
    pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UNM)) as [SRCN _].
    pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UTK)) as [SRCT _].
    pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UDP)) as [SRCD _].
    step. step. step. step.
    eapply evt_cut.
    { eapply MC with (src := bn_bytes (NM ++ [0])).
      - rewrite ?unsigned_lit by lia. exact SRCN.
      - rewrite ?unsigned_lit by lia. rewrite bn_bytes_length, length_app. cbn [length]. lia.
      - rewrite ?unsigned_lit by lia. exact RN.
      - rewrite ?unsigned_lit by lia. lia.
      - exact MI2. }
    intros ms' PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m4 & E & MUc &
                    WMc & MIc & DST & _).
    subst ms'. rewrite ?unsigned_lit in MUc, DST by lia.
    rewrite (ret_pc_even 0x1501c) by (cbn; lia).
    destruct DST as [[_ DSTN] _]. cbn [cells_bytes cbytes] in DSTN. rewrite app_nil_r in DSTN.
    pose proof (stk_cpy _ _ _ _ _ _ (bn_bytes (NM ++ [0])) ST3 MUc
                  ltac:(rewrite bn_bytes_length, length_app; cbn [length]; lia) WMc DSTN)
      as ST4.
    replace (bv_unsigned a4 + (Z.of_nat (length NM) + 1)) with (bv_unsigned a4 + Z.of_nat (length NM) + 1) in MUc by lia.
    pose proof (munch_snoc _ _ _ _ _ _ MU2 MUc) as MU4. cbn [app] in MU4.
    pose proof (wmono_trans rsegs _ _ _ WM2 WMc) as WM4.
    clear RN SRCN ST3 MU2 WM2 MI2.
    xport m3 m4 MUc WMc.
    clear MUc WMc.
    step. step. step. step.
    eapply evt_cut.
    { eapply MC with (src := bn_bytes (bn_tk false NM ++ [0])).
      - rewrite ?unsigned_lit by lia. exact SRCT.
      - rewrite ?unsigned_lit by lia. rewrite bn_bytes_length, length_app. cbn [length]. lia.
      - rewrite ?unsigned_lit by lia. exact RT.
      - rewrite ?unsigned_lit by lia. lia.
      - exact MIc. }
    intros ms' PO.
    destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m5 & E & MUc &
                    WMc & MIc2 & DST & _).
    subst ms'. rewrite ?unsigned_lit in MUc, DST by lia.
    rewrite (ret_pc_even 0x1502c) by (cbn; lia).
    destruct DST as [[_ DSTT] _]. cbn [cells_bytes cbytes] in DSTT. rewrite app_nil_r in DSTT.
    pose proof (stk_cpy _ _ _ _ _ _ (bn_bytes (bn_tk false NM ++ [0])) ST4 MUc
                  ltac:(rewrite bn_bytes_length, length_app; cbn [length]; lia) WMc DSTT)
      as ST5.
    replace (bv_unsigned a6 + (Z.of_nat (length (bn_tk false NM)) + 1))
      with (bv_unsigned a6 + Z.of_nat (length (bn_tk false NM)) + 1) in MUc by lia.
    pose proof (munch_snoc _ _ _ _ _ _ MU4 MUc) as MU5. cbn [app] in MU5.
    pose proof (wmono_trans rsegs _ _ _ WM4 WMc) as WM5.
    clear RT SRCT ST4 MU4 WM4 MIc.
    xport m4 m5 MUc WMc.
    clear MUc WMc.
    step. step. step. step.
    eapply evt_cut.
    { eapply MC with (src := bn_bytes (bn_DP NM i o ++ [0])).
      - rewrite ?unsigned_lit by lia. exact SRCD.
      - rewrite ?unsigned_lit by lia. rewrite bn_bytes_length, length_app. cbn [length]. lia.
      - rewrite ?unsigned_lit by lia. exact RD.
      - rewrite ?unsigned_lit by lia. lia.
      - exact MIc2. }
    intros ms' PO.
    destruct PO as (w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m6 & E & MUc &
                    WMc & MIc3 & DST & _).
    subst ms'. rewrite ?unsigned_lit in MUc, DST by lia.
    rewrite (ret_pc_even 0x1503c) by (cbn; lia).
    destruct DST as [[_ DSTD] _]. cbn [cells_bytes cbytes] in DSTD. rewrite app_nil_r in DSTD.
    pose proof (stk_cpy _ _ _ _ _ _ (bn_bytes (bn_DP NM i o ++ [0])) ST5 MUc
                  ltac:(rewrite bn_bytes_length, length_app; cbn [length]; lia) WMc DSTD)
      as ST6.
    replace (bv_unsigned display + (Z.of_nat (length (bn_DP NM i o)) + 1))
      with (bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1) in MUc by lia.
    pose proof (munch_snoc _ _ _ _ _ _ MU5 MUc) as MU6. cbn [app] in MU6.
    pose proof (wmono_trans rsegs _ _ _ WM5 WMc) as WM6.
    clear RD SRCD ST5 MU5 WM5 MIc2.
    xport m5 m6 MUc WMc.
    clear MUc WMc.
    step.
    eapply seg_epi; [unfold BN_K; lia | exact ST6 | exact SV2 | exact WM6 | exact MIc3 |].
    unfold bn_res. rewrite AT. unfold BN_K, bn_TK. split; [reflexivity|].
    split; [exact MU6|]. split; [exact DSTN|]. split; [exact DSTT|exact DSTD].
Qed.

Notation DP8 := (LN ++ [32; 40] ++ bn_dec i 1 ++ [32; 105; 110; 32; 47; 32]).

Ltac sub_tac := intros ?x ?Hx; cbn [outside] in *; destruct Hx as [?Hx _]; repeat split;
  first [exact I | let H := fresh in intro H; apply Hx; lia].

Lemma seg_out : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x14 x15 x16 x17 x22 x28 x29 x30 x31 nx ox : word) (jgw jw : list byte) (pw : word),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272)
    [C8 (Z_to_bv 64 (S + -240)); C8 (Z_to_bv 64 48); C8 nx; C4 ox; C4 (Z_to_bv 64 0)] ->
  bbuf m2 (S + -240) 48 DP8 ->
  bbuf m2 (S + -192) 24 (bn_tk false LN ++ [0]) ->
  bbuf m2 (S + -168) 24 (LN ++ [0]) ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display (Z_to_bv 64 (S + -240))
                        (Z_to_bv 64 48) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length DP8))) x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) x22 (Z_to_bv 64 (Z.of_nat (length (bn_tk false LN)))) display_len
                        (Z_to_bv 64 (Z.of_nat (length LN))) (Z_to_bv 64 NOV) (Z_to_bv 64 0) x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14f70) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x14 x15 x16 x17 x22 x28 x29 x30 x31 nx ox jgw jw pw
    HLO AOK BUFS ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 GW2.
  pose proof HIM as HIM'. destruct HIM' as (_ & _ & _ & _ & _ & _ & _ & _ & (OUTB & OUTD)).
  unfold BN_K in *. cbn [disjoint_from] in OUTD. destruct OUTD as [OUTD _].
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  destruct (bn_ok_dec i OKI) as (_ & _ & Li1 & _ & _ & _ & _).
  destruct (bn_ok_dec o OKO) as (Ro & _ & Lo1 & _ & Eo1 & _ & Fo1).
  assert (LLN : (length LN <= 23)%nat) by (rewrite length_firstn; lia).
  assert (L8 : (length DP8 <= 33)%nat) by (rewrite !length_app; cbn [length]; lia).
  destruct DP2 as (rdp & Ldp & UDP). destruct TK2 as (rtk & Ltk & UTK). destruct NM2 as (rnm & Lnm & UNM).
  step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  lazymatch goal with H : rw_cells rsegs m3 (S + -272) _ |- _ => rename H into DB3 end.
  destruct (rec_get _ _ _ _ _ _ _ DB3) as (RB & RP & RW).
  pose proof (proj2 UDP) as UW. rewrite length_app, bn_bytes_length in UW.
  destruct (dec_big o 1 48 (Z.of_nat (length DP8)) ltac:(lia) ltac:(rewrite Eo1; lia)) as (Er & Ea & Eo).
  eapply evt_cut.
  { eapply DEC with (lo := lo) (v := o) (md := 1) (p := Z_to_bv 64 (S + -240)) (cap := Z_to_bv 64 48)
                    (n := Z_to_bv 64 (Z.of_nat (length DP8))) (over := Z_to_bv 64 0).
    - lia.
    - reflexivity.
    - left; reflexivity.
    - reflexivity.
    - rewrite unsigned_lit by lia. exact RB.
    - rewrite unsigned_lit by lia. eapply wr_at_prefix; [exact RW|lia].
    - rewrite unsigned_lit by lia. lia.
    - intros _. rewrite !unsigned_lit by lia. rewrite Ea, Eo1. split; [lia|]. split.
      + eapply wr_at_sub; [exact UW|lia|lia|lia].
      + split; lia.
    - exact MI2.
    - rewrite unsigned_lit by lia. exact ST2.
    - unfold SB_DEC_K. rewrite unsigned_lit by lia. lia.
    - unfold SB_DEC_K. rewrite !unsigned_lit by lia. lia. }
  intros ms' PO.
  destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4 & E &
                  MUc & WMc & MIc & STc & RECc & DIGc).
  subst ms'. unfold SB_DEC_K in MUc.
  ulit_in MUc. ulit_in STc. ulit_in RECc. ulit_in DIGc.
  rewrite Er in RECc, DIGc, Eo. rewrite Ea in RECc, DIGc, MUc. rewrite Eo in RECc.
  cbv beta iota in RECc. specialize (DIGc ltac:(lia)).
  rewrite Eo1, Nat2Z.id, firstn_all in DIGc. change (map (Z_to_bv 8) (bn_dec o 1)) with (bn_bytes (bn_dec o 1)) in DIGc.
  rewrite Eo1 in MUc, RECc.
  rewrite (ret_pc_even 0x14f88) by (cbn; lia).
  pose proof (bytes_at_transport rsegs _ _ _ _ _ RP MUc ltac:(cbn [disjoint_from]; rewrite length_le4; repeat split; first [exact I | lia]))
    as RP4.
  pose proof (wr_at_transport rsegs _ _ _ _ RW WMc) as RW4.
  pose proof (rec_put _ _ _ _ _ _ _ RECc RP4 RW4) as DB4.
  assert (DPb : bbuf m3 (S + -240) 48 DP8) by (exists rdp; split; assumption).
  pose proof (bbuf_patch _ _ _ _ _ _ _ DPb MUc WMc DIGc ltac:(lia)
                ltac:(intros xx Hx Hx'; cbn [outside]; repeat split; first [exact I | intro; lia])) as DP4.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MUc ltac:(sub_tac)) as MU4.
  pose proof (wmono_trans rsegs _ _ _ WM2 WMc) as WM4.
  clear DB3 RB RP RW RP4 RW4 RECc DIGc DPb UDP UW ST2 MU2 WM2 MI2.
  xport m3 m4 MUc WMc.
  clear MUc WMc.
  remember (Z.of_nat (length DP8) + Z.of_nat (length (bn_dec o 1))) as n9 eqn:En9 in DB4.
  step. step. step. step.
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  step. step. step. step. step.
  subst n9.
  replace (Z.of_nat (length DP8) + Z.of_nat (length (bn_dec o 1))) with (Z.of_nat (length (DP8 ++ bn_dec o 1)))
    by (rewrite length_app; lia).
  cbn [length] in OUTD.
  pose proof (bytes_at_transport rsegs [(S - 288, S)] m m4 _ _ OUTB MU4
                ltac:(cbn [disjoint_from]; rewrite bn_bytes_length, length_app; cbn [length]; split; [lia|exact I]))
    as OUTB4.
  destruct DP4 as (r4 & L4 & U4).
  eapply evt_cut.
  { eapply box_name_out_loop with (P := BN_OUT) (B := S + -240) (n0 := Z.of_nat (length (DP8 ++ bn_dec o 1)))
                                  (ov0 := Z_to_bv 64 0) (s := [32; 111; 117; 116; 41])
                                  (bs := bn_bytes (DP8 ++ bn_dec o 1) ++ r4).
    - discriminate.
    - repeat constructor; lia.
    - exact OUTB4.
    - unfold BN_OUT. cbn [length]. lia.
    - exact U4.
    - rewrite length_app, bn_bytes_length. lia.
    - rewrite length_app. lia.
    - cbn [length]. lia.
    - exact MIc. }
  intros ms' (x16' & m5 & E & U5 & MUl & WMl & MIl). subst ms'.
  destruct (sb_no_over 47 (Z.of_nat (length (DP8 ++ bn_dec o 1))) (Z.of_nat (length [32; 111; 117; 116; 41]))
              (Z_to_bv 64 0) ltac:(cbn [length]; rewrite length_app; lia)) as (En & Eov).
  rewrite En, Eov.
  pose proof (bbuf_loop _ _ _ _ 47 _ U5 ltac:(lia) ltac:(rewrite length_app; lia) ltac:(lia)) as DP5.
  rewrite L4 in DP5.
  assert (EDP : firstn (Z.to_nat 47) ((DP8 ++ bn_dec o 1) ++ [32; 111; 117; 116; 41]) = bn_DP LN i o).
  { rewrite firstn_all2; [unfold bn_DP; rewrite <- !app_assoc; reflexivity|].
    rewrite !length_app. cbn [length]. lia. }
  rewrite EDP in DP5.
  assert (ELD : Z.of_nat (length (DP8 ++ bn_dec o 1)) + Z.of_nat (length [32; 111; 117; 116; 41]) =
                Z.of_nat (length (bn_DP LN i o))).
  { rewrite <- EDP, length_firstn, !length_app. cbn [length]. lia. }
  rewrite ELD.
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ STc MUl WMl
                ltac:(cbn [disjoint_from]; split; [lia|exact I])) as ST5.
  pose proof (munch_sub _ _ _ _ _ _ MU4 MUl ltac:(sub_tac)) as MU5.
  pose proof (wmono_trans rsegs _ _ _ WM4 WMl) as WM5.
  clear U5 STc MU4 WM4 MIc.
  xport m4 m5 MUl WMl.
  destruct (rw_cells_forget _ _ _ _ DB4) as (jdb & DB5). cbn [cells_size csize Nat.add] in DB5.
  assert (TK5 : bbuf m5 (S + -192) 24 (bn_tk false LN ++ [0])) by (exists rtk; split; assumption).
  assert (NM5 : bbuf m5 (S + -168) 24 (LN ++ [0])) by (exists rnm; split; assumption).
  eapply seg_final; try eassumption.
Qed.

Notation DP6 := (LN ++ [32; 40]).

Lemma seg_in : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 ox : word) (j16 jgw jw : list byte) (pw : word),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272)
    [C8 (Z_to_bv 64 (S + -240)); C8 (Z_to_bv 64 48); CB 8 j16; C4 ox; C4 (Z_to_bv 64 0)] ->
  bbuf m2 (S + -240) 48 DP6 ->
  bbuf m2 (S + -192) 24 (bn_tk false LN ++ [0]) ->
  bbuf m2 (S + -168) 24 (LN ++ [0]) ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display (Z_to_bv 64 (S + -240))
                        (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length DP6))) x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) (Z_to_bv 64 (Z.of_nat (length (bn_tk false LN))))
                        display_len (Z_to_bv 64 (Z.of_nat (length LN))) (Z_to_bv 64 NOV) (Z_to_bv 64 0)
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14f0c) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 ox j16 jgw jw pw
    HLO AOK BUFS ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 GW2.
  pose proof HIM as HIM'. destruct HIM' as (_ & _ & _ & _ & _ & _ & _ & (INB & IND) & _).
  unfold BN_K in *. cbn [disjoint_from length] in IND. destruct IND as [IND _].
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  destruct (bn_ok_dec i OKI) as (Ri & _ & Li1 & _ & Ei1 & _ & Fi1).
  assert (LLN : (length LN <= 23)%nat) by (rewrite length_firstn; lia).
  assert (L6 : (length DP6 <= 25)%nat) by (rewrite !length_app; cbn [length]; lia).
  destruct DP2 as (rdp & Ldp & UDP). destruct TK2 as (rtk & Ltk & UTK). destruct NM2 as (rnm & Lnm & UNM).
  step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  lazymatch goal with H : rw_cells rsegs m3 (S + -272) _ |- _ => rename H into DB3 end.
  destruct (rec_get _ _ _ _ _ _ _ DB3) as (RB & RP & RW).
  pose proof (proj2 UDP) as UW. rewrite length_app, bn_bytes_length in UW.
  destruct (dec_big i 1 48 (Z.of_nat (length DP6)) ltac:(lia) ltac:(rewrite Ei1; lia)) as (Er & Ea & Eo).
  eapply evt_cut.
  { eapply DEC with (lo := lo) (v := i) (md := 1) (p := Z_to_bv 64 (S + -240)) (cap := Z_to_bv 64 48)
                    (n := Z_to_bv 64 (Z.of_nat (length DP6))) (over := Z_to_bv 64 0).
    - lia.
    - reflexivity.
    - left; reflexivity.
    - reflexivity.
    - rewrite unsigned_lit by lia. exact RB.
    - rewrite unsigned_lit by lia. eapply wr_at_prefix; [exact RW|lia].
    - rewrite unsigned_lit by lia. lia.
    - intros _. ulit. rewrite Ea, Ei1. split; [lia|]. split.
      + eapply wr_at_sub; [exact UW|lia|lia|lia].
      + split; lia.
    - exact MI2.
    - rewrite unsigned_lit by lia. exact ST2.
    - unfold SB_DEC_K. rewrite unsigned_lit by lia. lia.
    - unfold SB_DEC_K. ulit. lia. }
  intros ms' PO.
  destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4 & E &
                  MUc & WMc & MIc & STc & RECc & DIGc).
  subst ms'. unfold SB_DEC_K in MUc.
  ulit_in MUc. ulit_in STc. ulit_in RECc. ulit_in DIGc.
  rewrite Er in RECc, DIGc, Eo. rewrite Ea in RECc, DIGc, MUc. rewrite Eo in RECc.
  cbv beta iota in RECc. specialize (DIGc ltac:(lia)).
  rewrite Ei1, Nat2Z.id, firstn_all in DIGc. change (map (Z_to_bv 8) (bn_dec i 1)) with (bn_bytes (bn_dec i 1)) in DIGc.
  rewrite Ei1 in MUc, RECc.
  rewrite (ret_pc_even 0x14f24) by (cbn; lia).
  pose proof (bytes_at_transport rsegs _ _ _ _ _ RP MUc
                ltac:(cbn [disjoint_from]; rewrite length_le4; repeat split; first [exact I | lia])) as RP4.
  pose proof (wr_at_transport rsegs _ _ _ _ RW WMc) as RW4.
  pose proof (rec_put _ _ _ _ _ _ _ RECc RP4 RW4) as DB4.
  assert (DPb : bbuf m3 (S + -240) 48 DP6) by (exists rdp; split; assumption).
  pose proof (bbuf_patch _ _ _ _ _ _ _ DPb MUc WMc DIGc ltac:(lia)
                ltac:(intros xx Hx Hx'; cbn [outside]; repeat split; first [exact I | intro; lia])) as DP4.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MUc ltac:(sub_tac)) as MU4.
  pose proof (wmono_trans rsegs _ _ _ WM2 WMc) as WM4.
  clear DB3 RB RP RW RP4 RW4 RECc DIGc DPb UDP UW ST2 MU2 WM2 MI2.
  xport m3 m4 MUc WMc.
  clear MUc WMc.
  remember (Z.of_nat (length DP6) + Z.of_nat (length (bn_dec i 1))) as n9 eqn:En9 in DB4.
  step. step. step. step.
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  step. step. step. step. step.
  subst n9.
  replace (Z.of_nat (length DP6) + Z.of_nat (length (bn_dec i 1))) with (Z.of_nat (length (DP6 ++ bn_dec i 1)))
    by (rewrite length_app; lia).
  pose proof (bytes_at_transport rsegs [(S - 288, S)] m m4 _ _ INB MU4
                ltac:(cbn [disjoint_from]; rewrite bn_bytes_length, length_app; cbn [length]; split; [lia|exact I]))
    as INB4.
  destruct DP4 as (r4 & L4 & U4).
  eapply evt_cut.
  { eapply box_name_in_loop with (P := BN_IN) (B := S + -240) (n0 := Z.of_nat (length (DP6 ++ bn_dec i 1)))
                                 (ov0 := Z_to_bv 64 0) (s := [32; 105; 110; 32; 47; 32])
                                 (bs := bn_bytes (DP6 ++ bn_dec i 1) ++ r4).
    - discriminate.
    - repeat constructor; lia.
    - exact INB4.
    - unfold BN_IN. cbn [length]. lia.
    - exact U4.
    - rewrite length_app, bn_bytes_length. lia.
    - rewrite length_app. lia.
    - cbn [length]. lia.
    - exact MIc. }
  intros ms' (x17' & m5 & E & U5 & MUl & WMl & MIl). subst ms'.
  destruct (sb_no_over 47 (Z.of_nat (length (DP6 ++ bn_dec i 1))) (Z.of_nat (length [32; 105; 110; 32; 47; 32]))
              (Z_to_bv 64 0) ltac:(cbn [length]; rewrite length_app; lia)) as (En & Eov).
  rewrite En, Eov.
  pose proof (bbuf_loop _ _ _ _ 47 _ U5 ltac:(lia) ltac:(rewrite length_app; lia) ltac:(lia)) as DP5.
  rewrite L4 in DP5.
  assert (EDP : firstn (Z.to_nat 47) ((DP6 ++ bn_dec i 1) ++ [32; 105; 110; 32; 47; 32]) = DP8).
  { rewrite firstn_all2; [rewrite <- !app_assoc; reflexivity|].
    rewrite !length_app. cbn [length]. lia. }
  rewrite EDP in DP5.
  assert (ELD : Z.of_nat (length (DP6 ++ bn_dec i 1)) + Z.of_nat (length [32; 105; 110; 32; 47; 32]) =
                Z.of_nat (length DP8)).
  { rewrite <- EDP, length_firstn, !length_app. cbn [length]. lia. }
  rewrite ELD.
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ STc MUl WMl
                ltac:(cbn [disjoint_from]; split; [lia|exact I])) as ST5.
  pose proof (munch_sub _ _ _ _ _ _ MU4 MUl ltac:(sub_tac)) as MU5.
  pose proof (wmono_trans rsegs _ _ _ WM4 WMl) as WM5.
  clear U5 STc MU4 WM4 MIc.
  xport m4 m5 MUl WMl.
  assert (TK5 : bbuf m5 (S + -192) 24 (bn_tk false LN ++ [0])) by (exists rtk; split; assumption).
  assert (NM5 : bbuf m5 (S + -168) 24 (LN ++ [0])) by (exists rnm; split; assumption).
  eapply seg_out; try eassumption.
Qed.

Lemma seg_paren : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 ox : word) (j16 jgw jw : list byte) (pw : word),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272)
    [C8 (Z_to_bv 64 (S + -240)); C8 (Z_to_bv 64 48); CB 8 j16; C4 ox; C4 (Z_to_bv 64 0)] ->
  bbuf m2 (S + -240) 48 LN ->
  bbuf m2 (S + -192) 24 (bn_tk false LN ++ [0]) ->
  bbuf m2 (S + -168) 24 (LN ++ [0]) ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display (Z_to_bv 64 (S + -240))
                        (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length LN))) x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) (Z_to_bv 64 (Z.of_nat (length (bn_tk false LN))))
                        display_len (Z_to_bv 64 (Z.of_nat (length LN))) (Z_to_bv 64 NOV) (Z_to_bv 64 0)
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14ecc) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 ox j16 jgw jw pw
    HLO AOK BUFS ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 GW2.
  pose proof HIM as HIM'. destruct HIM' as (_ & _ & _ & _ & _ & _ & (PB & PD) & _ & _).
  unfold BN_K in *. cbn [disjoint_from length] in PD. destruct PD as [PD _].
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  assert (LLN : (length LN <= 23)%nat) by (rewrite length_firstn; lia).
  destruct DP2 as (rdp & Ldp & UDP). destruct TK2 as (rtk & Ltk & UTK). destruct NM2 as (rnm & Lnm & UNM).
  step. step. step. step. step. step.
  pose proof (bytes_at_transport rsegs [(S - 288, S)] m m2 _ _ PB MU2
                ltac:(cbn [disjoint_from]; rewrite bn_bytes_length, length_app; cbn [length]; split; [lia|exact I]))
    as PB2.
  eapply evt_cut.
  { eapply box_name_paren_loop with (P := BN_PAREN) (B := S + -240) (n0 := Z.of_nat (length LN))
                                    (ov0 := Z_to_bv 64 0) (s := [32; 40]) (bs := bn_bytes LN ++ rdp).
    - discriminate.
    - repeat constructor; lia.
    - exact PB2.
    - unfold BN_PAREN. cbn [length]. lia.
    - exact UDP.
    - rewrite length_app, bn_bytes_length. lia.
    - lia.
    - cbn [length]. lia.
    - exact MI2. }
  intros ms' (x17' & m5 & E & U5 & MUl & WMl & MIl). subst ms'.
  destruct (sb_no_over 47 (Z.of_nat (length LN)) (Z.of_nat (length [32; 40])) (Z_to_bv 64 0)
              ltac:(cbn [length]; lia)) as (En & Eov).
  rewrite En, Eov.
  pose proof (bbuf_loop _ _ _ _ 47 _ U5 ltac:(lia) ltac:(lia) ltac:(lia)) as DP5.
  rewrite Ldp in DP5. rewrite firstn_all2 in DP5 by (rewrite length_app; cbn [length]; lia).
  replace (Z.of_nat (length LN) + Z.of_nat (length [32; 40])) with (Z.of_nat (length DP6))
    by (rewrite length_app; lia).
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ ST2 MUl WMl
                ltac:(cbn [disjoint_from]; split; [lia|exact I])) as ST5.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MUl ltac:(sub_tac)) as MU5.
  pose proof (wmono_trans rsegs _ _ _ WM2 WMl) as WM5.
  clear U5 ST2 MU2 WM2 MI2.
  xport m2 m5 MUl WMl.
  assert (TK5 : bbuf m5 (S + -192) 24 (bn_tk false LN ++ [0])) by (exists rtk; split; assumption).
  assert (NM5 : bbuf m5 (S + -168) 24 (LN ++ [0])) by (exists rnm; split; assumption).
  eapply seg_in; try eassumption.
Qed.

Lemma rw_cells_conv : forall mm A cs cs', rw_cells rsegs mm A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells rsegs mm A cs'.
Proof.
  intros mm A cs cs' [[Hwf Hb] Hw] Hwf' E. split; [split; [exact Hwf'|rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs') by exact Hwf'. rewrite E, cells_bytes_length by exact Hwf. exact Hw.
Qed.

Lemma conv_z8 : forall mm A pre, rw_cells rsegs mm A (pre ++ [C8 (Z_to_bv 64 0)]) ->
  rw_cells rsegs mm A (pre ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
Proof.
  intros mm A pre H. eapply rw_cells_conv; [exact H| |].
  - pose proof (proj1 (proj1 H)) as W. apply cells_wf_app in W. apply cells_wf_app. split; [tauto|cbn; tauto].
  - rewrite !cells_bytes_app. reflexivity.
Qed.

Lemma seg_tkz : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) (jdb jgw jw : list byte) (pw : word),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  Forall (fun c => 0 < c < 256) NM -> (1 <= length NM)%nat ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272) [CB 32 jdb] ->
  bbuf m2 (S + -240) 48 [] ->
  bbuf m2 (S + -192) 24 (bn_tk false LN) ->
  bbuf m2 (S + -168) 24 (LN ++ [0]) ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display x10
                        (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) (Z_to_bv 64 (Z.of_nat (length (bn_tk false LN))))
                        display_len (Z_to_bv 64 (Z.of_nat (length LN))) (Z_to_bv 64 NOV) x27
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14e68) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 jdb jgw jw pw
    HLO AOK BUFS NMB NM1 ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 GW2.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  assert (LLN : (1 <= length LN <= 23)%nat) by (rewrite length_firstn; lia).
  assert (LNB : Forall (fun c => 0 < c < 256) LN).
  { pose proof NMB as Q. rewrite <- (firstn_skipn 23 NM) in Q. apply Forall_app in Q. tauto. }
  pose proof (bn_tk_len LN false) as LTK.
  assert (R0 : 0 < nth 0 LN 0 < 256) by (rewrite Forall_forall in LNB; apply LNB; apply nth_In; lia).
  destruct DP2 as (rdp & Ldp & UDP). destruct TK2 as (rtk & Ltk & UTK). destruct NM2 as (rnm & Lnm & UNM).
  cbn [bn_bytes map app] in UDP. cbn [length] in Ldp.
  assert (EHD : nth 0 LN 0 = hd 0 LN) by (destruct (firstn 23 NM); reflexivity).
  pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UNM)) as [NMB2 _].
  pose proof (bl_rd0 m2 (S + -168) (LN ++ [0]) 0 NMB2 ltac:(rewrite length_app; cbn [length]; lia)) as RD0.
  rewrite app_nth1 in RD0 by lia. clear NMB2.
  step. change (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  step. step. step.
  clear RD0. rewrite bl_zxb by lia.
  step.
  pose proof (u8arr_store_ok rsegs m2 (S + -192) _ (Z.of_nat (length (bn_tk false LN))) _ UTK
                ltac:(rewrite length_app, bn_bytes_length; lia) eq_refl) as HST.
  step.
  bst UTK.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  pose proof (bbuf_upd _ _ 24 _ _ _ HW Ltk ltac:(lia)) as TK3. clear HW.
  destruct TK3 as (rtk3 & Ltk3 & UTK3).
  step. step. step. step.
  lazymatch goal with
  | H : rw_cells rsegs ?mm (S + -272) [C8 ?p; C8 ?c; CB 8 ?j; C8 (Z_to_bv 64 0)] |- _ =>
      change [C8 p; C8 c; CB 8 j; C8 (Z_to_bv 64 0)] with ([C8 p; C8 c; CB 8 j] ++ [C8 (Z_to_bv 64 0)]) in H;
      apply conv_z8 in H; cbn [app] in H; rename H into DB4
  end.
  step. step. step.
  rewrite bl_eqb by lia. replace (nth 0 LN 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
  pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UNM)) as [NMB4 _].
  replace (S + -167) with (S + -168 + 1) by lia.
  rewrite EHD.
  eapply evt_cut.
  { eapply box_name_nm_dp_loop with (P := S + -168) (B := S + -240) (n0 := 0) (ov0 := Z_to_bv 64 0) (s := LN)
                                    (bs := rdp).
    - intro E. rewrite E in LLN. cbn in LLN. lia.
    - exact LNB.
    - exact NMB4.
    - exact UDP.
    - lia.
    - lia.
    - lia.
    - assumption. }
  intros ms' (x16' & m5 & E & U5 & MUl & WMl & MIl). subst ms'.
  destruct (sb_no_over 47 0 (Z.of_nat (length LN)) (Z_to_bv 64 0) ltac:(lia)) as (En & Eov).
  rewrite En, Eov. replace (0 + Z.of_nat (length LN)) with (Z.of_nat (length LN)) by lia.
  pose proof (bbuf_loop _ _ [] rdp 47 LN U5 ltac:(lia) ltac:(cbn; lia) ltac:(cbn [length]; lia)) as DP5.
  replace (length [] + length rdp)%nat with 48%nat in DP5 by (cbn [length]; lia).
  rewrite app_nil_l, firstn_all2 in DP5 by lia.
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ ST2 MUl WMl
                ltac:(cbn [disjoint_from]; split; [lia|exact I])) as ST5.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MUl ltac:(sub_tac)) as MU5.
  pose proof (wmono_trans rsegs _ _ _ WM2 WMl) as WM5.
  clear U5 ST2 MU2 WM2.
  xport m4 m5 MUl WMl.
  assert (TK5 : bbuf m5 (S + -192) 24 (bn_tk false LN ++ [0])) by (exists rtk3; split; assumption).
  assert (NM5 : bbuf m5 (S + -168) 24 (LN ++ [0])) by (exists rnm; split; assumption).
  eapply seg_paren; try eassumption.
Qed.

Lemma bbuf_upd0 : forall mm A bs xs, u8arr rsegs mm A (upd_bytes bs 0 (bn_bytes xs)) -> (length xs <= length bs)%nat ->
  bbuf mm A (length bs) xs.
Proof.
  intros mm A bs xs U L. exists (skipn (length xs) bs). split; [rewrite length_skipn; lia|].
  unfold upd_bytes in U. cbn [firstn app Nat.add] in U. rewrite bn_bytes_length in U. exact U.
Qed.

Lemma seg_tok : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word) (jdb jgw jw : list byte) (pw : word),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  Forall (fun c => 0 < c < 256) NM -> (1 <= length NM)%nat ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272) [CB 32 jdb] ->
  bbuf m2 (S + -240) 48 [] ->
  bbuf m2 (S + -192) 24 [] ->
  bbuf m2 (S + -168) 24 LN ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display x10
                        x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) x23
                        display_len (Z_to_bv 64 (Z.of_nat (length LN))) (Z_to_bv 64 NOV) x27
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14dd8) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 jdb jgw jw pw
    HLO AOK BUFS NMB NM1 ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 GW2.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  assert (LLN : (1 <= length LN <= 23)%nat) by (rewrite length_firstn; lia).
  assert (LNB : Forall (fun c => 0 < c < 256) LN).
  { pose proof NMB as Q. rewrite <- (firstn_skipn 23 NM) in Q. apply Forall_app in Q. tauto. }
  destruct NM2 as (rnm & Lnm & UNM). destruct DP2 as (rdp & Ldp & UDP). cbn [length] in Ldp.
  unfold bn_bytes in UDP. cbn [map app] in UDP.
  destruct TK2 as (rtk & Ltk & UTK). unfold bn_bytes in UTK. cbn [map app] in UTK. cbn [length] in Ltk.
  step. step.
  pose proof (u8arr_store_ok rsegs m2 (S + -168) _ (Z.of_nat (length LN)) _ UNM
                ltac:(rewrite length_app, bn_bytes_length; lia) eq_refl) as HST.
  step.
  bst UNM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  pose proof (bbuf_upd _ _ 24 _ _ 0 HW Lnm ltac:(lia)) as NM3. clear HW.
  step.
  rewrite bl_eqb by lia. replace (Z.of_nat (length LN) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [negb].
  do 8 step.
  destruct NM3 as (rnm3 & Lnm3 & UNM3).
  pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UNM3)) as [NB _].
  rewrite bn_bytes_app in NB. apply bytes_at_app in NB. destruct NB as [NB _].
  eapply evt_cut.
  { eapply box_name_token_loop with (N := S + -168) (T := S + -192) (l := LN) (bs := rtk).
    - lia.
    - eapply Forall_impl; [|exact LNB]. intros c Hc. cbv beta in Hc |- *. lia.
    - exact NB.
    - lia.
    - exact UTK.
    - exact Ltk.
    - lia.
    - assumption. }
  intros ms' (x5' & x6' & x17' & m4 & E & U4 & MUl & WMl & MIl). subst ms'.
  pose proof (bbuf_upd0 _ _ _ _ U4 ltac:(pose proof (bn_tk_len LN false); lia)) as TK4.
  replace (length rtk) with 24%nat in TK4 by lia. clear U4.
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ ST2 MUl WMl
                ltac:(cbn [disjoint_from]; split; [lia|exact I])) as ST4.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MUl ltac:(sub_tac)) as MU4.
  pose proof (wmono_trans rsegs _ _ _ WM2 WMl) as WM4.
  clear ST2 MU2 WM2 NB.
  xport m3 m4 MUl WMl.
  assert (NM4 : bbuf m4 (S + -168) 24 (LN ++ [0])) by (exists rnm3; split; assumption).
  assert (DP4 : bbuf m4 (S + -240) 48 []) by (exists rdp; split; [cbn [length]; lia | exact UDP]).
  eapply seg_tkz; try eassumption.
Qed.

Lemma firstn_firstn_app : forall {X} n (a b : list X), firstn n (firstn n a ++ b) = firstn n (a ++ b).
Proof.
  intros X n a b. rewrite !firstn_app, firstn_firstn, Nat.min_id, length_firstn.
  destruct (Nat.le_ge_cases n (length a)) as [H|H].
  - rewrite Nat.min_l by lia. replace (n - n)%nat with 0%nat by lia.
    replace (n - length a)%nat with 0%nat by lia. reflexivity.
  - rewrite Nat.min_r by lia. reflexivity.
Qed.

Notation STM := (bn_stem f sd).
Notation W4 := (bn_w4 i o).

Lemma seg_w4 : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word) (jdb jgw jw : list byte) (pw : word)
    (c : list Z) (ov : Z),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  Forall (fun c => 0 < c < 256) NM -> (1 <= length NM)%nat ->
  (length c <= 23)%nat -> firstn 23 (c ++ W4) = LN ->
  (if 23 <? Z.of_nat (length c) + 4 then 1 else ov) = NOV ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272) [CB 32 jdb] ->
  bbuf m2 (S + -240) 48 [] ->
  bbuf m2 (S + -192) 24 [] ->
  bbuf m2 (S + -168) 24 c ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  bytes_at rsegs m2 (S + -109) (bn_bytes (W4 ++ [0])) ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display x10
                        x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) x23
                        display_len (Z_to_bv 64 (Z.of_nat (length c))) (Z_to_bv 64 ov) x27
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14d9c) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 jdb jgw jw pw c ov
    HLO AOK BUFS NMB NM1 LC ELN EOV ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 GW2 W4B.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  pose proof (bn_w4_length i o OKI OKO) as LW.
  assert (W4D : Forall (fun c => 48 <= c <= 57) W4).
  { unfold bn_w4. apply Forall_app. split.
    - destruct (bn_ok_dec i OKI) as (_ & _ & _ & _ & _ & Q & _). exact Q.
    - destruct (bn_ok_dec o OKO) as (_ & _ & _ & _ & _ & Q & _). exact Q. }
  assert (R0 : 48 <= nth 0 W4 0 <= 57) by (rewrite Forall_forall in W4D; apply W4D; apply nth_In; lia).
  assert (EHD : nth 0 W4 0 = hd 0 W4) by (destruct W4; reflexivity).
  assert (LG : length jgw = 8%nat) by (destruct GW2 as [[Hwf _] _]; cbn in Hwf; tauto).
  apply u8arr_of_rw_cells in GW2.
  destruct NM2 as (rnm & Lnm & UNM). destruct DP2 as (rdp & Ldp & UDP). destruct TK2 as (rtk & Ltk & UTK).
  cbn [length] in Ldp, Ltk.
  pose proof (bl_rd0 m2 (S + -109) (W4 ++ [0]) 0 W4B ltac:(rewrite length_app; cbn [length]; lia)) as RD0.
  rewrite app_nth1 in RD0 by lia.
  step. clear RD0. rewrite bl_zxb by lia.
  step.
  rewrite bl_eqb by lia. replace (nth 0 W4 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. step. step.
  replace (S + -108) with (S + -109 + 1) by lia.
  rewrite EHD.
  eapply evt_cut.
  { eapply box_name_w4_loop with (P := S + -109) (B := S + -168) (n0 := Z.of_nat (length c))
                                 (ov0 := Z_to_bv 64 ov) (s := W4) (bs := bn_bytes c ++ rnm).
    - intro E. rewrite E in LW. discriminate.
    - eapply Forall_impl; [|exact W4D]. intros d Hd. cbv beta in Hd |- *. lia.
    - exact W4B.
    - exact UNM.
    - rewrite length_app, bn_bytes_length. lia.
    - lia.
    - rewrite LW. right. lia.
    - exact MI2. }
  intros ms' (x14' & m5 & E & U5 & MUl & WMl & MIl). subst ms'.
  assert (EN : sb_n 23 (Z.of_nat (length c)) (Z.of_nat (length W4)) = Z.of_nat (length LN)).
  { unfold sb_n. rewrite <- ELN, length_firstn, length_app, LW. lia. }
  assert (EO : sb_o 23 (Z.of_nat (length c)) (Z.of_nat (length W4)) (Z_to_bv 64 ov) = Z_to_bv 64 NOV).
  { unfold sb_o. rewrite LW. change (Z.of_nat 4) with 4. rewrite <- EOV.
    destruct (23 <? Z.of_nat (length c) + 4); reflexivity. }
  rewrite EN, EO.
  pose proof (bbuf_loop _ _ _ _ 23 _ U5 ltac:(lia) ltac:(lia) ltac:(lia)) as NM5.
  rewrite Lnm in NM5. change (Z.to_nat 23) with 23%nat in NM5. rewrite ELN in NM5.
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ ST2 MUl WMl
                ltac:(cbn [disjoint_from]; split; [lia|exact I])) as ST5.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MUl ltac:(sub_tac)) as MU5.
  pose proof (wmono_trans rsegs _ _ _ WM2 WMl) as WM5.
  clear U5 ST2 MU2 WM2 MI2 UNM W4B.
  xport m2 m5 MUl WMl.
  apply rw_cells_of_u8arr in GW2. rewrite LG in GW2.
  assert (DP5 : bbuf m5 (S + -240) 48 []) by (exists rdp; split; [cbn [length]; lia | assumption]).
  assert (TK5 : bbuf m5 (S + -192) 24 []) by (exists rtk; split; [cbn [length]; lia | assumption]).
  eapply seg_tok; try eassumption.
Qed.

Lemma seg_dash : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word) (jdb jgw jw : list byte) (pw : word),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  Forall (fun c => 0 < c < 256) NM -> (1 <= length NM)%nat ->
  NM = STM ++ 45 :: W4 ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272) [CB 32 jdb] ->
  bbuf m2 (S + -240) 48 [] ->
  bbuf m2 (S + -192) 24 [] ->
  bbuf m2 (S + -168) 24 (firstn 23 STM) ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  bytes_at rsegs m2 (S + -109) (bn_bytes (W4 ++ [0])) ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display x10
                        x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) x23
                        display_len (Z_to_bv 64 (Z.of_nat (length (firstn 23 STM))))
                        (Z_to_bv 64 (if 23 <? Z.of_nat (length STM) then 1 else 0)) x27
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14d78) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 jdb jgw jw pw
    HLO AOK BUFS NMB NM1 ENM ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 GW2 W4B.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  pose proof (bn_w4_length i o OKI OKO) as LW.
  destruct (Z.leb_spec (Z.of_nat (length STM)) 22) as [Hs|Hs].
  - rewrite firstn_all2 in NM2 |- * by lia.
    replace (23 <? Z.of_nat (length STM)) with false by (symmetry; apply Z.ltb_ge; lia).
    step. step.
    try (rewrite bl_ltu by lia). replace (22 <? Z.of_nat (length STM)) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    step. step. step. step.
    destruct NM2 as (rnm & Lnm & UNM).
    destruct DP2 as (rdp & Ldp & UDP). destruct TK2 as (rtk & Ltk & UTK). cbn [length] in Ldp, Ltk.
    unfold bn_bytes in UDP, UTK. cbn [map app] in UDP, UTK.
    assert (LW5 : length (bn_bytes (W4 ++ [0])) = 5%nat) by (rewrite bn_bytes_length, length_app, LW; reflexivity).
    pose proof (u8arr_store_ok rsegs m2 (S + -168) _ (Z.of_nat (length STM)) _ UNM
                  ltac:(rewrite length_app, bn_bytes_length; lia) eq_refl) as HST.
    step.
    bst UNM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    pose proof (bbuf_upd _ _ 24 _ _ 45 HW Lnm ltac:(lia)) as NM3. clear HW.
    assert (DP3 : bbuf m3 (S + -240) 48 []) by (exists rdp; split; [cbn [length]; lia | exact UDP]).
    assert (TK3 : bbuf m3 (S + -192) 24 []) by (exists rtk; split; [cbn [length]; lia | exact UTK]).
    clear UDP UTK.
    step.
    replace (Z.of_nat (length STM) + 1) with (Z.of_nat (length (STM ++ [45]))) by (rewrite length_app; cbn [length]; lia).
    eapply seg_w4 with (c := STM ++ [45]) (ov := 0); try eassumption.
    + rewrite length_app. cbn [length]. lia.
    + rewrite ENM, <- app_assoc. reflexivity.
    + replace (23 <? Z.of_nat (length (STM ++ [45])) + 4) with (23 <? Z.of_nat (length NM))
        by (f_equal; rewrite ENM, !length_app; cbn [length]; rewrite LW; lia).
      reflexivity.
  - assert (L23 : length (firstn 23 STM) = 23%nat) by (rewrite length_firstn; lia).
    step. step.
    try (rewrite bl_ltu by lia).
    try (replace (22 <? Z.of_nat (length (firstn 23 STM))) with true by (symmetry; apply Z.ltb_lt; lia)).
    cbv iota.
    step.
    eapply seg_w4 with (c := firstn 23 STM) (ov := 1); try eassumption.
    + lia.
    + rewrite ENM, firstn_firstn_app, !firstn_app. replace (23 - length STM)%nat with 0%nat by lia. reflexivity.
    + replace (23 <? Z.of_nat (length NM)) with true
        by (symmetry; apply Z.ltb_lt; rewrite ENM, length_app; cbn [length]; lia).
      destruct (23 <? Z.of_nat (length (firstn 23 STM)) + 4); reflexivity.
Qed.

Lemma bn_lor_add : forall hi lw k, 0 <= k -> 0 <= lw < 2^k -> hi mod 2^k = 0 -> Z.lor hi lw = hi + lw.
Proof.
  intros hi lw k Hk Hlw Hhi.
  assert (HL : Z.land hi lw = 0).
  { rewrite <- (Z.mod_small lw (2^k)) by lia. rewrite <- Z.land_ones by lia.
    rewrite (Z.land_comm lw), Z.land_assoc, Z.land_ones, Hhi by lia. apply Z.land_0_l. }
  pose proof (Z.add_lor_land hi lw). lia.
Qed.

Definition c4v (b0 b1 b2 b3 : Z) : word :=
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (sxb (Z_to_bv 8 b3)) ≪ 24)))
                                                    (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 b2)) ≪ 16))))))
                    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 b1)) ≪ 8)))
                                                    (bv_unsigned (zxb (Z_to_bv 8 b0))))))).

Definition c4z (b0 b1 b2 b3 : Z) : Z :=
  b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + (if b3 <? 128 then 0 else 18446744069414584320).

Lemma c4v_val : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  c4v b0 b1 b2 b3 = Z_to_bv 64 (c4z b0 b1 b2 b3).
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold c4v, c4z, zxb, sxb.
  assert (U : forall b, 0 <= b < 256 -> bv_unsigned (Z_to_bv 8 b) = b).
  { intros b Hb. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. }
  rewrite (U b0), (U b1), (U b2) by assumption.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2^24) with 16777216. change (2^16) with 65536. change (2^8) with 256.
  rewrite (unsigned_lit b2), (unsigned_lit b1), (unsigned_lit b0) by lia.
  rewrite (unsigned_lit (b2 * 65536)), (unsigned_lit (b1 * 256)) by lia.
  assert (LO : Z.lor (b1 * 256) b0 = b1 * 256 + b0).
  { apply (bn_lor_add _ _ 8); [lia | change (2^8) with 256; lia | change (2^8) with 256; apply Z.mod_mul; lia]. }
  rewrite LO, (unsigned_lit (b1 * 256 + b0)) by lia.
  assert (MID : forall h, h mod 16777216 = 0 -> Z.lor h (b2 * 65536) = h + b2 * 65536).
  { intros h Hh. apply (bn_lor_add _ _ 24); [lia | change (2^24) with 16777216; lia | change (2^24) with 16777216; exact Hh]. }
  assert (TOP : forall h, h mod 65536 = 0 -> Z.lor h (b1 * 256 + b0) = h + (b1 * 256 + b0)).
  { intros h Hh. apply (bn_lor_add _ _ 16); [lia | change (2^16) with 65536; lia | change (2^16) with 65536; exact Hh]. }
  assert (SG : bv_signed (Z_to_bv 8 b3) = if b3 <? 128 then b3 else b3 - 256).
  { rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128.
    change (bv_modulus 8) with 256.
    destruct (Z.ltb_spec b3 128).
    - rewrite Z.mod_small by lia. lia.
    - replace (b3 + 128) with ((b3 - 128) + 1 * 256) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  rewrite SG.
  destruct (Z.ltb_spec b3 128) as [Hb|Hb].
  - rewrite (unsigned_lit b3), (unsigned_lit (b3 * 16777216)) by lia.
    rewrite MID by (apply Z.mod_mul; lia).
    rewrite (unsigned_lit (b3 * 16777216 + b2 * 65536)) by lia.
    rewrite TOP by (replace (b3 * 16777216 + b2 * 65536) with ((b3 * 256 + b2) * 65536) by lia; apply Z.mod_mul; lia).
    f_equal. lia.
  - rewrite (unsigned_lit_wrap (b3 - 256)).
    replace ((b3 - 256) mod 2^64) with (b3 - 256 + 2^64)
      by (symmetry; rewrite <- (Z.mod_add _ 1 (2^64)) by lia; rewrite Z.mod_small by lia; lia).
    rewrite (unsigned_lit_wrap ((b3 - 256 + 2^64) * 16777216)).
    replace (((b3 - 256 + 2^64) * 16777216) mod 2^64) with (b3 * 16777216 + 18446744069414584320)
      by (symmetry; rewrite <- (Z.mod_add _ (- 16777215) (2^64)) by lia; rewrite Z.mod_small by lia; lia).
    rewrite MID by (replace (b3 * 16777216 + 18446744069414584320) with ((b3 + 1099511627520) * 16777216) by lia;
                    apply Z.mod_mul; lia).
    rewrite (unsigned_lit (b3 * 16777216 + 18446744069414584320 + b2 * 65536)) by lia.
    rewrite TOP by (replace (b3 * 16777216 + 18446744069414584320 + b2 * 65536)
                      with ((b3 * 256 + 281474976645120 + b2) * 65536) by lia; apply Z.mod_mul; lia).
    f_equal. lia.
Qed.

Lemma c4z_inj : forall b0 b1 b2 b3 c0 c1 c2 c3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  c4z b0 b1 b2 b3 = c4z c0 c1 c2 c3 -> b0 = c0 /\ b1 = c1 /\ b2 = c2 /\ b3 = c3.
Proof.
  intros b0 b1 b2 b3 c0 c1 c2 c3 H0 H1 H2 H3 K0 K1 K2 K3 E. unfold c4z in E.
  destruct (Z.ltb_spec b3 128); destruct (Z.ltb_spec c3 128); lia.
Qed.

Lemma c4z_rng : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  0 <= c4z b0 b1 b2 b3 < 2^64.
Proof. intros. unfold c4z. destruct (Z.ltb_spec b3 128); lia. Qed.

Lemma c4v_eqb : forall b0 b1 b2 b3 c0 c1 c2 c3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  bv_eqb (c4v b0 b1 b2 b3) (c4v c0 c1 c2 c3) = (b0 =? c0) && (b1 =? c1) && (b2 =? c2) && (b3 =? c3).
Proof.
  intros b0 b1 b2 b3 c0 c1 c2 c3 H0 H1 H2 H3 K0 K1 K2 K3.
  rewrite !c4v_val by assumption. unfold bv_eqb.
  rewrite !unsigned_lit by (apply c4z_rng; assumption).
  destruct (Z.eqb_spec (c4z b0 b1 b2 b3) (c4z c0 c1 c2 c3)) as [E|E].
  - destruct (c4z_inj _ _ _ _ _ _ _ _ H0 H1 H2 H3 K0 K1 K2 K3 E) as (-> & -> & -> & ->). rewrite !Z.eqb_refl. reflexivity.
  - symmetry. destruct (Z.eqb_spec b0 c0); destruct (Z.eqb_spec b1 c1); destruct (Z.eqb_spec b2 c2);
      destruct (Z.eqb_spec b3 c3); try reflexivity. subst. contradiction.
Qed.

Lemma c4v_eqb_x : forall b0 b1 b2 b3 c0 c1 c2 c3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  bv_eqb
    (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (sxb (Z_to_bv 8 b3)) ≪ 24)))
                                                      (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 b2)) ≪ 16))))))
                      (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 b1)) ≪ 8)))
                                                      (bv_unsigned (zxb (Z_to_bv 8 b0))))))))
    (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (sxb (Z_to_bv 8 c3)) ≪ 24)))
                                                      (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 c2)) ≪ 16))))))
                      (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 c1)) ≪ 8)))
                                                      (bv_unsigned (zxb (Z_to_bv 8 c0))))))))
  = (b0 =? c0) && (b1 =? c1) && (b2 =? c2) && (b3 =? c3).
Proof. intros. apply (c4v_eqb b0 b1 b2 b3 c0 c1 c2 c3); assumption. Qed.

Lemma bn_leq_nth4 : forall a b, length a = 4%nat -> length b = 4%nat ->
  bn_leq a b = (nth 0 a 0 =? nth 0 b 0) && (nth 1 a 0 =? nth 1 b 0) && (nth 2 a 0 =? nth 2 b 0) &&
               (nth 3 a 0 =? nth 3 b 0).
Proof.
  intros [|u0 [|u1 [|u2 [|u3 [|u4 u]]]]] [|v0 [|v1 [|v2 [|v3 [|v4 v]]]]] Ha Hb; cbn in Ha, Hb; try discriminate.
  cbn [bn_leq nth]. destruct (u0 =? v0), (u1 =? v1), (u2 =? v2), (u3 =? v3); reflexivity.
Qed.

Lemma bytes_skipn : forall mm A (l : list Z) k, bytes_at rsegs mm A (bn_bytes l) -> (k <= length l)%nat ->
  bytes_at rsegs mm (A + Z.of_nat k) (bn_bytes (skipn k l)).
Proof.
  intros mm A l k H Hk. rewrite <- (firstn_skipn k l) in H. rewrite bn_bytes_app in H. apply bytes_at_app in H.
  destruct H as [_ H]. rewrite bn_bytes_length, length_firstn in H. replace (Nat.min k (length l)) with k in H by lia.
  exact H.
Qed.

Lemma bn_nz : forall l, Forall (fun c => 0 < c < 256) l -> ~ In (Z_to_bv 8 0) (bn_bytes l).
Proof.
  intros l H I. unfold bn_bytes in I. apply in_map_iff in I. destruct I as (c & E & Hc).
  rewrite Forall_forall in H. specialize (H c Hc).
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 8) with 256 in E. rewrite (Z.mod_small c) in E by lia. change (0 mod 256) with 0 in E. lia.
Qed.

Lemma seg_cmp : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) (jdb jgw jw : list byte) (pw : word)
    (P : Z) (sl : list byte),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  Forall (fun c => 0 < c < 256) NM -> (1 <= length NM)%nat ->
  Forall (fun c => 0 < c < 256) STM ->
  bytes_at rsegs m2 P (bn_bytes STM ++ Z_to_bv 8 0 :: sl) ->
  (- (P + Z.of_nat (length STM) + 1)) mod 8 <= Z.of_nat (length sl) ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272) [CB 32 jdb] ->
  bbuf m2 (S + -240) 48 [] ->
  bbuf m2 (S + -192) 24 [] ->
  bbuf m2 (S + -168) 24 (firstn 23 STM) ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  bytes_at rsegs m2 (S + -109) (bn_bytes (W4 ++ [0])) ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display (Z_to_bv 64 4)
                        x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) (Z_to_bv 64 P)
                        display_len (Z_to_bv 64 (Z.of_nat (length (firstn 23 STM))))
                        (Z_to_bv 64 (if 23 <? Z.of_nat (length STM) then 1 else 0)) x27
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14d0c) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 jdb jgw jw pw P sl
    HLO AOK BUFS NMB NM1 STC STB SLK ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 GW2 W4B.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  pose proof (bn_w4_length i o OKI OKO) as LW.
  pose proof (bytes_at_bound rsegs m2 P _ STB) as PB.
  rewrite length_app, bn_bytes_length in PB. cbn [length] in PB.
  step.
  step.
  try (rewrite (bl_eqb 4 4) by lia). try (change (4 =? 4) with true). cbn [negb]. cbv iota.
  step. step.
  eapply evt_cut.
  { eapply SL with (str := bn_bytes STM) (slack := sl).
    - rewrite unsigned_lit by lia. exact STB.
    - apply bn_nz. exact STC.
    - rewrite unsigned_lit by lia. rewrite bn_bytes_length. exact SLK.
    - exact MI2. }
  intros ms' (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & E &
              MUc & WMc & MIc & STB3).
  subst ms'. rewrite unsigned_lit in STB3 by lia.
  rewrite (ret_pc_even 0x14d1c) by (cbn; lia).
  rewrite bn_bytes_length.
  assert (MU3 : munch [(S - 288, S)] m m3) by (intros x Hx; rewrite (MUc x I); apply MU2; exact Hx).
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ ST2 MUc WMc ltac:(cbn [disjoint_from]; exact I)) as ST3.
  pose proof (wmono_trans rsegs _ _ _ WM2 WMc) as WM3.
  destruct NM2 as (rnm & Lnm & UNM). destruct DP2 as (rdp & Ldp & UDP). destruct TK2 as (rtk & Ltk & UTK).
  clear STB ST2 MU2 WM2 MI2.
  xport m2 m3 MUc WMc.
  assert (NM3 : bbuf m3 (S + -168) 24 (firstn 23 STM)) by (exists rnm; split; assumption).
  assert (DP3 : bbuf m3 (S + -240) 48 []) by (exists rdp; split; assumption).
  assert (TK3 : bbuf m3 (S + -192) 24 []) by (exists rtk; split; assumption).
  clear UNM UDP UTK MUc WMc.
  step.
  rewrite bl_ltu by lia.
  destruct (Z.ltb_spec (Z.of_nat (length STM)) 4) as [Hl|Hl]; cbv iota.
  - assert (ENM : NM = STM ++ 45 :: W4).
    { unfold bn_NM. cbv zeta. replace (4 <=? Z.of_nat (length STM)) with false by (symmetry; apply Z.leb_gt; lia).
      reflexivity. }
    eapply seg_dash; try eassumption.
  - pose proof (proj1 (proj1 (bytes_at_app rsegs _ _ _ _) STB3)) as STB4.
    pose proof (bytes_skipn _ _ _ (length STM - 4) STB4 ltac:(lia)) as SKB.
    set (SK := skipn (length STM - 4) STM) in *.
    assert (LSK : length SK = 4%nat) by (unfold SK; rewrite length_skipn; lia).
    assert (SKC : Forall (fun c => 0 < c < 256) SK).
    { unfold SK. pose proof STC as Q. rewrite <- (firstn_skipn (length STM - 4) STM) in Q.
      apply Forall_app in Q. tauto. }
    assert (W4D : Forall (fun c => 48 <= c <= 57) W4).
    { unfold bn_w4. apply Forall_app. split.
      - destruct (bn_ok_dec i OKI) as (_ & _ & _ & _ & _ & Q & _). exact Q.
      - destruct (bn_ok_dec o OKO) as (_ & _ & _ & _ & _ & Q & _). exact Q. }
    assert (RS : forall j, (j < 4)%nat -> 0 < nth j SK 0 < 256)
      by (intros j Hj; rewrite Forall_forall in SKC; apply SKC; apply nth_In; lia).
    assert (RW : forall j, (j < 4)%nat -> 48 <= nth j W4 0 <= 57)
      by (intros j Hj; rewrite Forall_forall in W4D; apply W4D; apply nth_In; lia).
    pose proof (RS 0%nat ltac:(lia)) as RS0. pose proof (RS 1%nat ltac:(lia)) as RS1.
    pose proof (RS 2%nat ltac:(lia)) as RS2. pose proof (RS 3%nat ltac:(lia)) as RS3.
    pose proof (RW 0%nat ltac:(lia)) as RW0. pose proof (RW 1%nat ltac:(lia)) as RW1.
    pose proof (RW 2%nat ltac:(lia)) as RW2. pose proof (RW 3%nat ltac:(lia)) as RW3.
    pose proof (bl_rd0 m3 (S + -109) (W4 ++ [0]) 0 W4B ltac:(rewrite length_app; cbn [length]; lia)) as RD0.
    pose proof (bl_rd0 m3 (S + -109) (W4 ++ [0]) 1 W4B ltac:(rewrite length_app; cbn [length]; lia)) as RD1.
    pose proof (bl_rd0 m3 (S + -109) (W4 ++ [0]) 2 W4B ltac:(rewrite length_app; cbn [length]; lia)) as RD2.
    pose proof (bl_rd0 m3 (S + -109) (W4 ++ [0]) 3 W4B ltac:(rewrite length_app; cbn [length]; lia)) as RD3.
    rewrite app_nth1 in RD0, RD1, RD2, RD3 by lia.
    replace (S + -109 + Z.of_nat 0) with (S + -109) in RD0 by lia.
    replace (S + -109 + Z.of_nat 1) with (S + -108) in RD1 by lia.
    replace (S + -109 + Z.of_nat 2) with (S + -107) in RD2 by lia.
    replace (S + -109 + Z.of_nat 3) with (S + -106) in RD3 by lia.
    pose proof (bl_rd0 m3 _ SK 0 SKB ltac:(lia)) as RC0. pose proof (bl_rd0 m3 _ SK 1 SKB ltac:(lia)) as RC1.
    pose proof (bl_rd0 m3 _ SK 2 SKB ltac:(lia)) as RC2. pose proof (bl_rd0 m3 _ SK 3 SKB ltac:(lia)) as RC3.
    replace (P + Z.of_nat (length STM - 4) + Z.of_nat 0) with (P + Z.of_nat (length STM) + -4) in RC0 by lia.
    replace (P + Z.of_nat (length STM - 4) + Z.of_nat 1) with (P + Z.of_nat (length STM) + -3) in RC1 by lia.
    replace (P + Z.of_nat (length STM - 4) + Z.of_nat 2) with (P + Z.of_nat (length STM) + -2) in RC2 by lia.
    replace (P + Z.of_nat (length STM - 4) + Z.of_nat 3) with (P + Z.of_nat (length STM) + -1) in RC3 by lia.
    assert (LG : length jgw = 8%nat) by (destruct GW2 as [[Hwf _] _]; cbn in Hwf; tauto).
    apply u8arr_of_rw_cells in GW2.
    do 21 step.
    step.
    rewrite c4v_eqb_x by lia.
    assert (ENM : NM = if (nth 0 SK 0 =? nth 0 W4 0) && (nth 1 SK 0 =? nth 1 W4 0) && (nth 2 SK 0 =? nth 2 W4 0) &&
                          (nth 3 SK 0 =? nth 3 W4 0) then STM else STM ++ 45 :: W4).
    { unfold bn_NM. cbv zeta. replace (4 <=? Z.of_nat (length STM)) with true by (symmetry; apply Z.leb_le; lia).
      rewrite andb_true_l. change (skipn (length STM - 4) STM) with SK. rewrite (bn_leq_nth4 _ _ LSK LW).
      reflexivity. }
    revert ENM.
    destruct ((nth 0 SK 0 =? nth 0 W4 0) && (nth 1 SK 0 =? nth 1 W4 0) && (nth 2 SK 0 =? nth 2 W4 0) &&
              (nth 3 SK 0 =? nth 3 W4 0)); intros ENM; cbv iota in ENM |- *.
    + rewrite <- ENM in NM3 |- *.
      apply rw_cells_of_u8arr in GW2. rewrite LG in GW2.
      eapply seg_tok; try eassumption.
    + apply rw_cells_of_u8arr in GW2. rewrite LG in GW2.
      eapply seg_dash; try eassumption.
Qed.

Lemma rw_u8_cat : forall mm A n x y, rw_cells rsegs mm A [CB n x] -> u8arr rsegs mm (A + Z.of_nat n) y ->
  rw_cells rsegs mm A [CB (n + length y) (x ++ y)].
Proof.
  intros mm A n x y Hx Hy.
  assert (Lx : length x = n) by (destruct Hx as [[Hwf _] _]; cbn in Hwf; tauto).
  apply u8arr_of_rw_cells in Hx. destruct Hx as [Bx Wx]. destruct Hy as [By Wy].
  rewrite <- Lx, <- length_app. apply rw_cells_of_u8arr. split.
  - apply bytes_at_app. split; [exact Bx|]. rewrite Lx. exact By.
  - destruct Wx as (W1 & W2 & Wx). destruct Wy as (V1 & V2 & Wy). rewrite length_app.
    split; [lia|]. split; [lia|]. intros j Hj.
    destruct (Z.ltb_spec j (Z.of_nat (length x))) as [Hjx|Hjx].
    + apply Wx. lia.
    + replace (A + j) with (A + Z.of_nat n + (j - Z.of_nat n)) by lia. apply Wy. lia.
Qed.

Lemma seg_stem : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word) (jdb g3 : list byte) (pw : word)
    (P : Z) (sl : list byte),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  Forall (fun c => 0 < c < 256) NM -> (1 <= length NM)%nat ->
  Forall (fun c => 0 < c < 256) STM -> STM <> [] ->
  bytes_at rsegs m2 P (bn_bytes STM ++ Z_to_bv 8 0 :: sl) ->
  (- (P + Z.of_nat (length STM) + 1)) mod 8 <= Z.of_nat (length sl) ->
  (P + Z.of_nat (length STM) + 1 + Z.of_nat (length sl) <= S - BN_K \/ S <= P) ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272) [CB 32 jdb] ->
  bbuf m2 (S + -240) 48 [] ->
  bbuf m2 (S + -192) 24 [] ->
  bbuf m2 (S + -168) 24 [] ->
  rw_cells rsegs m2 (S + -144) [C8 (Z_to_bv 64 (S + -109)); C8 (Z_to_bv 64 5); C8 (Z_to_bv 64 (Z.of_nat (length W4)));
                                C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 3 g3] ->
  bbuf m2 (S + -109) 5 W4 ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display x10
                        x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) (Z_to_bv 64 P)
                        display_len (Z_to_bv 64 (S + -109)) x26 x27
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14cb0) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 jdb g3 pw P sl
    HLO AOK BUFS NMB NM1 STC SNE STB SLK PD ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 G32 W4b.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  pose proof (bn_w4_length i o OKI OKO) as LW.
  pose proof (bytes_at_bound rsegs m2 P _ STB) as PB.
  rewrite length_app, bn_bytes_length in PB. cbn [length] in PB.
  pose proof (bn_bytes_length STM) as LBS.
  assert (LS1 : (0 < length STM)%nat)
    by (apply Nat.neq_0_lt_0; intro E; apply length_zero_iff_nil in E; contradiction).
  assert (R0 : 0 < nth 0 STM 0 < 256) by (rewrite Forall_forall in STC; apply STC; apply nth_In; lia).
  assert (EHD : nth 0 STM 0 = hd 0 STM) by (destruct STM; reflexivity).
  destruct W4b as (rw4 & Lw4 & Uw4). destruct DP2 as (rdp & Ldp & UDP). destruct TK2 as (rtk & Ltk & UTK).
  destruct NM2 as (rnm & Lnm & UNM). cbn [length] in Ldp, Ltk, Lnm.
  unfold bn_bytes in UDP, UTK, UNM. cbn [map app] in UDP, UTK, UNM.
  step. step.
  pose proof (u8arr_store_ok rsegs m2 (S + -109) _ (Z.of_nat (length W4)) _ Uw4
                ltac:(rewrite length_app, bn_bytes_length; lia) eq_refl) as HST.
  step.
  bst Uw4.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  pose proof (bbuf_upd _ _ 5 _ _ 0 HW Lw4 ltac:(lia)) as W43. clear HW.
  assert (STB0 : bytes_at rsegs m3 P (bn_bytes (STM ++ [0]))).
  { pose proof STB as Q. rewrite bn_bytes_app. change (bn_bytes [0]) with [Z_to_bv 8 0].
    change (Z_to_bv 8 0 :: sl) with ([Z_to_bv 8 0] ++ sl) in Q. rewrite app_assoc in Q.
    apply bytes_at_app in Q. tauto. }
  pose proof (bl_rd0 m3 P (STM ++ [0]) 0 STB0 ltac:(rewrite length_app; cbn [length]; lia)) as RD0.
  rewrite app_nth1 in RD0 by lia.
  replace (P + Z.of_nat 0) with P in RD0 by lia.
  step. clear RD0. rewrite bl_zxb by lia.
  step.
  rewrite bl_eqb by lia. replace (nth 0 STM 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  do 5 step.
  rewrite EHD.
  eapply evt_cut.
  { eapply box_name_stem_loop with (P := P) (B := S + -168) (n0 := 0) (ov0 := Z_to_bv 64 0) (s := STM) (bs := rnm).
    - exact SNE.
    - exact STC.
    - exact STB0.
    - exact UNM.
    - lia.
    - lia.
    - lia.
    - assumption. }
  intros ms' (x15' & m5 & E & U5 & MUl & WMl & MIl). subst ms'.
  assert (EN : sb_n 23 0 (Z.of_nat (length STM)) = Z.of_nat (length (firstn 23 STM)))
    by (unfold sb_n; rewrite length_firstn; lia).
  assert (EO : sb_o 23 0 (Z.of_nat (length STM)) (Z_to_bv 64 0) =
               Z_to_bv 64 (if 23 <? Z.of_nat (length STM) then 1 else 0)).
  { unfold sb_o. replace (0 + Z.of_nat (length STM)) with (Z.of_nat (length STM)) by lia.
    destruct (23 <? Z.of_nat (length STM)); reflexivity. }
  rewrite EN, EO, LW. change (Z.of_nat 4) with 4.
  pose proof (bbuf_loop _ _ [] rnm 23 STM U5 ltac:(lia) ltac:(cbn; lia) ltac:(cbn [length]; lia)) as NM5.
  replace (length [] + length rnm)%nat with 24%nat in NM5 by (cbn [length]; lia).
  rewrite app_nil_l in NM5. change (Z.to_nat 23) with 23%nat in NM5.
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ ST2 MUl WMl
                ltac:(cbn [disjoint_from]; split; [lia|exact I])) as ST5.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MUl ltac:(sub_tac)) as MU5.
  pose proof (wmono_trans rsegs _ _ _ WM2 WMl) as WM5.
  destruct W43 as (rw5 & Lw5 & Uw5).
  clear U5 ST2 MU2 WM2 MI2 STB0 UNM.
  xport m3 m5 MUl WMl.
  assert (W4B : bytes_at rsegs m5 (S + -109) (bn_bytes (W4 ++ [0]))).
  { eapply bbuf_bytes. exists rw5. split; [exact Lw5 | exact Uw5]. }
  replace (S + -109) with (S + -112 + Z.of_nat 3) in Uw5 by lia.
  pose proof (rw_u8_cat _ _ _ _ _ G32 Uw5) as GW5.
  replace (3 + length (bn_bytes (W4 ++ [0%Z]) ++ rw5))%nat with 8%nat in GW5
    by (rewrite length_app, bn_bytes_length; lia).
  pose proof (rw_cells_merge rsegs m5 (S + -144) []
                [C8 (Z_to_bv 64 (S + -109)); C8 (Z_to_bv 64 5); C8 (Z_to_bv 64 (Z.of_nat (length W4)))]
                [C4 (Z_to_bv 64 0); C4 pw] WB2) as WB5.
  cbn [app cells_size csize Nat.add] in WB5.
  assert (DP5 : bbuf m5 (S + -240) 48 []) by (exists rdp; split; [cbn [length]; lia | exact UDP]).
  assert (TK5 : bbuf m5 (S + -192) 24 []) by (exists rtk; split; [cbn [length]; lia | exact UTK]).
  clear WB2 G32 Uw5.
  eapply seg_cmp; try eassumption.
Qed.

Lemma seg_dec : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 : word) (jdb jw g3 : list byte)
    (P : Z) (sl : list byte),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  Forall (fun c => 0 < c < 256) NM -> (1 <= length NM)%nat ->
  Forall (fun c => 0 < c < 256) STM -> STM <> [] ->
  bytes_at rsegs m2 P (bn_bytes STM ++ Z_to_bv 8 0 :: sl) ->
  (- (P + Z.of_nat (length STM) + 1)) mod 8 <= Z.of_nat (length sl) ->
  (P + Z.of_nat (length STM) + 1 + Z.of_nat (length sl) <= S - BN_K \/ S <= P) ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272) [CB 32 jdb] ->
  bbuf m2 (S + -240) 48 [] ->
  bbuf m2 (S + -192) 24 [] ->
  bbuf m2 (S + -168) 24 [] ->
  rw_cells rsegs m2 (S + -144) [CB 32 jw] ->
  rw_cells rsegs m2 (S + -112) [CB 3 g3] ->
  bbuf m2 (S + -109) 5 [] ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display x10
                        x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) (Z_to_bv 64 P)
                        display_len x25 x26 x27
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14c78) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 jdb jw g3 P sl
    HLO AOK BUFS NMB NM1 STC SNE STB SLK PD ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 G32 W4b.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  destruct (bn_ok_dec i OKI) as (Ri & Li2 & _ & Ei2 & _ & _ & _).
  destruct (bn_ok_dec o OKO) as (Ro & Lo2 & _ & Eo2 & _ & _ & _).
  pose proof (bytes_at_bound rsegs m2 P _ STB) as PB.
  rewrite length_app, bn_bytes_length in PB. cbn [length] in PB.
  pose proof (bn_bytes_length STM) as LBS.
  destruct DP2 as (rdp & Ldp & UDP). destruct TK2 as (rtk & Ltk & UTK).
  destruct NM2 as (rnm & Lnm & UNM). cbn [length] in Ldp, Ltk, Lnm.
  unfold bn_bytes in UDP, UTK, UNM. cbn [map app] in UDP, UTK, UNM.
  destruct W4b as (rw4 & Lw4 & Uw4). cbn [length] in Lw4. unfold bn_bytes in Uw4. cbn [map app] in Uw4.
  do 6 step.
  lazymatch goal with
  | H : rw_cells rsegs ?mm (S + -144) [C8 ?p; C8 ?c; C8 ?n; C8 (Z_to_bv 64 0)] |- _ =>
      change [C8 p; C8 c; C8 n; C8 (Z_to_bv 64 0)] with ([C8 p; C8 c; C8 n] ++ [C8 (Z_to_bv 64 0)]) in H;
      apply conv_z8 in H; cbn [app] in H; rename H into WB3
  end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  do 4 step.
  destruct (rec_get _ _ _ _ _ _ _ WB3) as (RB & RP & RW).
  pose proof (proj2 Uw4) as UW.
  destruct (dec_big i 2 5 0 ltac:(lia) ltac:(rewrite Ei2; lia)) as (Er & Ea & Eo).
  eapply evt_cut.
  { eapply DEC with (lo := lo) (v := i) (md := 2) (p := Z_to_bv 64 (S + -109)) (cap := Z_to_bv 64 5)
                    (n := Z_to_bv 64 0) (over := Z_to_bv 64 0).
    - lia.
    - reflexivity.
    - right; reflexivity.
    - reflexivity.
    - rewrite unsigned_lit by lia. exact RB.
    - rewrite unsigned_lit by lia. eapply wr_at_prefix; [exact RW|lia].
    - rewrite unsigned_lit by lia. lia.
    - intros _. ulit. rewrite Ea, Ei2. split; [lia|]. split.
      + eapply wr_at_sub; [exact UW|lia|lia|lia].
      + split; lia.
    - exact MI2.
    - rewrite unsigned_lit by lia. exact ST2.
    - unfold SB_DEC_K. rewrite unsigned_lit by lia. lia.
    - unfold SB_DEC_K. ulit. lia. }
  intros ms' PO.
  destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4 & E &
                  MUc & WMc & MIc & STc & RECc & DIGc).
  subst ms'. unfold SB_DEC_K in MUc.
  ulit_in MUc. ulit_in STc. ulit_in RECc. ulit_in DIGc.
  rewrite Er in RECc, DIGc, Eo. rewrite Ea in RECc, DIGc, MUc. rewrite Eo in RECc.
  cbv beta iota in RECc. specialize (DIGc ltac:(lia)).
  rewrite Ei2, Nat2Z.id, firstn_all in DIGc. change (map (Z_to_bv 8) (bn_dec i 2)) with (bn_bytes (bn_dec i 2)) in DIGc.
  rewrite Ei2 in MUc, RECc.
  replace (0 + Z.of_nat (length (bn_dec i 2))) with (Z.of_nat (length (bn_dec i 2))) in RECc by lia.
  replace (S + -109 + 0) with (S + -109 + Z.of_nat (length (@nil Z))) in DIGc by (cbn; lia).
  rewrite (ret_pc_even 0x14ca0) by (cbn; lia).
  pose proof (bytes_at_transport rsegs _ _ _ _ _ RP MUc
                ltac:(cbn [disjoint_from]; rewrite length_le4; repeat split; first [exact I | lia])) as RP4.
  pose proof (wr_at_transport rsegs _ _ _ _ RW WMc) as RW4.
  pose proof (rec_put _ _ _ _ _ _ _ RECc RP4 RW4) as WB4.
  assert (W4c : bbuf m3 (S + -109) 5 []) by (exists rw4; split; [cbn [length]; lia | exact Uw4]).
  pose proof (bbuf_patch _ _ _ _ _ _ _ W4c MUc WMc DIGc ltac:(cbn [length]; lia)
                ltac:(intros xx Hx Hx'; cbn [length Nat.add] in Hx'; cbn [outside]; repeat split;
                      first [exact I | intro; lia])) as W44.
  rewrite app_nil_l in W44.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MUc ltac:(sub_tac)) as MU4.
  pose proof (wmono_trans rsegs _ _ _ WM2 WMc) as WM4.
  clear WB3 RB RP RW RP4 RW4 RECc DIGc W4c Uw4 UW ST2 MU2 WM2 MI2.
  xport m3 m4 MUc WMc.
  clear MUc WMc.
  do 4 step.
  destruct (rec_get _ _ _ _ _ _ _ WB4) as (RB & RP & RW).
  destruct W44 as (rw6 & Lw6 & Uw6).
  pose proof (proj2 Uw6) as UW. rewrite length_app, bn_bytes_length, Lw6 in UW.
  clear Er Ea Eo.
  destruct (dec_big o 2 5 (Z.of_nat (length (bn_dec i 2))) ltac:(lia) ltac:(rewrite Eo2; lia)) as (Er & Ea & Eo).
  eapply evt_cut.
  { eapply DEC with (lo := lo) (v := o) (md := 2) (p := Z_to_bv 64 (S + -109)) (cap := Z_to_bv 64 5)
                    (n := Z_to_bv 64 (Z.of_nat (length (bn_dec i 2)))) (over := Z_to_bv 64 0).
    - lia.
    - reflexivity.
    - right; reflexivity.
    - reflexivity.
    - rewrite unsigned_lit by lia. exact RB.
    - rewrite unsigned_lit by lia. eapply wr_at_prefix; [exact RW|lia].
    - rewrite unsigned_lit by lia. lia.
    - intros _. ulit. rewrite Ea, Eo2. split; [lia|]. split.
      + eapply wr_at_sub; [exact UW|lia|lia|lia].
      + split; lia.
    - exact MIc.
    - rewrite unsigned_lit by lia. exact STc.
    - unfold SB_DEC_K. rewrite unsigned_lit by lia. lia.
    - unfold SB_DEC_K. ulit. lia. }
  intros ms' PO.
  destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m5 & E &
                  MUc & WMc & MI5 & ST5 & RECc & DIGc).
  subst ms'. unfold SB_DEC_K in MUc.
  ulit_in MUc. ulit_in ST5. ulit_in RECc. ulit_in DIGc.
  rewrite Er in RECc, DIGc, Eo. rewrite Ea in RECc, DIGc, MUc. rewrite Eo in RECc.
  cbv beta iota in RECc. specialize (DIGc ltac:(lia)).
  rewrite Eo2, Nat2Z.id, firstn_all in DIGc. change (map (Z_to_bv 8) (bn_dec o 2)) with (bn_bytes (bn_dec o 2)) in DIGc.
  rewrite Eo2 in MUc, RECc.
  replace (Z.of_nat (length (bn_dec i 2)) + Z.of_nat (length (bn_dec o 2))) with (Z.of_nat (length W4)) in RECc
    by (unfold bn_w4; rewrite length_app; lia).
  rewrite (ret_pc_even 0x14cb0) by (cbn; lia).
  pose proof (bytes_at_transport rsegs _ _ _ _ _ RP MUc
                ltac:(cbn [disjoint_from]; rewrite length_le4; repeat split; first [exact I | lia])) as RP5.
  pose proof (wr_at_transport rsegs _ _ _ _ RW WMc) as RW5.
  pose proof (rec_put _ _ _ _ _ _ _ RECc RP5 RW5) as WB5.
  assert (W4d : bbuf m4 (S + -109) 5 (bn_dec i 2)) by (exists rw6; split; [exact Lw6 | exact Uw6]).
  pose proof (bbuf_patch _ _ _ _ _ _ _ W4d MUc WMc DIGc ltac:(lia)
                ltac:(intros xx Hx Hx'; cbn [outside]; repeat split; first [exact I | intro; lia])) as W45.
  change (bn_dec i 2 ++ bn_dec o 2) with W4 in W45.
  pose proof (munch_sub _ _ _ _ _ _ MU4 MUc ltac:(sub_tac)) as MU5.
  pose proof (wmono_trans rsegs _ _ _ WM4 WMc) as WM5.
  clear WB4 RB RP RW RP5 RW5 RECc DIGc W4d Uw6 UW STc MU4 WM4 MIc.
  xport m4 m5 MUc WMc.
  clear MUc WMc.
  assert (DP5 : bbuf m5 (S + -240) 48 []) by (exists rdp; split; [cbn [length]; lia | exact UDP]).
  assert (TK5 : bbuf m5 (S + -192) 24 []) by (exists rtk; split; [cbn [length]; lia | exact UTK]).
  assert (NM5 : bbuf m5 (S + -168) 24 []) by (exists rnm; split; [cbn [length]; lia | exact UNM]).
  clear UDP UTK UNM.
  eapply seg_stem; try eassumption.
Qed.

Lemma skipn0 : forall {X} (l : list X), skipn 0 l = l.
Proof. reflexivity. Qed.

Lemma rw_bbuf : forall mm A n j, rw_cells rsegs mm A [CB n j] -> bbuf mm A n [].
Proof.
  intros mm A n j H. assert (L : length j = n) by (destruct H as [[Hwf _] _]; cbn in Hwf; tauto).
  apply u8arr_of_rw_cells in H. exists j. split; [cbn [length]; lia | exact H].
Qed.

Lemma stem_ne : forall ff ss, bn_stem ff ss <> [].
Proof.
  intros ff ss. unfold bn_stem, bn_STEM. destruct ss; [|discriminate].
  destruct (ff =? 1); [discriminate|]. destruct (ff =? 2); [discriminate|]. destruct (ff =? 3); discriminate.
Qed.

Lemma stem_sd : forall ff l, l <> [] -> bn_stem ff l = l.
Proof. intros ff l H. destruct l; [contradiction|reflexivity]. Qed.

Lemma NM_chars : forall ff ss ii oo, Forall (fun c => 0 < c < 256) (bn_stem ff ss) -> bn_ok ii = true -> bn_ok oo = true ->
  Forall (fun c => 0 < c < 256) (bn_NM ff ss ii oo).
Proof.
  intros ff ss ii oo H Hi Ho. unfold bn_NM. cbv zeta.
  match goal with |- context [if ?b then _ else _] => destruct b end; [exact H|].
  apply Forall_app. split; [exact H|]. constructor; [lia|].
  destruct (bn_ok_dec ii Hi) as (_ & _ & _ & _ & _ & Di & _).
  destruct (bn_ok_dec oo Ho) as (_ & _ & _ & _ & _ & Do & _).
  unfold bn_w4. apply Forall_app. split.
  - eapply Forall_impl; [|exact Di]. intros c Hc. cbv beta in Hc |- *. lia.
  - eapply Forall_impl; [|exact Do]. intros c Hc. cbv beta in Hc |- *. lia.
Qed.

Lemma NM_len : forall ff ss ii oo, (length (bn_stem ff ss) <= length (bn_NM ff ss ii oo))%nat.
Proof.
  intros ff ss ii oo. unfold bn_NM. cbv zeta.
  match goal with |- context [if ?b then _ else _] => destruct b end; [lia|]. rewrite length_app. lia.
Qed.

Lemma seg_go : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 : word)
    (jdb jdp jtk jnm jw g3 j4 : list byte) (P : Z),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  bn_cstr m (S - BN_K) S P STM ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272) [CB 32 jdb] -> rw_cells rsegs m2 (S + -240) [CB 48 jdp] ->
  rw_cells rsegs m2 (S + -192) [CB 24 jtk] -> rw_cells rsegs m2 (S + -168) [CB 24 jnm] ->
  rw_cells rsegs m2 (S + -144) [CB 32 jw] -> rw_cells rsegs m2 (S + -112) [CB 3 g3] ->
  rw_cells rsegs m2 (S + -109) [CB 5 j4] ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display x10
                        x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) (Z_to_bv 64 P)
                        display_len x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14c78) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 jdb jdp jtk jnm jw g3 j4 P
    HLO AOK BUFS CS ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 G32 W42.
  unfold BN_K in *.
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  destruct CS as (STC & sl & STB & SLK & PD). cbn [disjoint_from] in PD. destruct PD as [PD _].
  pose proof (bytes_at_transport rsegs _ _ _ _ _ STB MU2
                ltac:(cbn [disjoint_from]; rewrite length_app, bn_bytes_length; cbn [length]; split; [lia|exact I]))
    as STB2.
  pose proof (NM_chars f sd i o STC OKI OKO) as NMB.
  pose proof (NM_len f sd i o) as NML.
  pose proof (stem_ne f sd) as SNE.
  assert (NM1 : (1 <= length NM)%nat).
  { destruct (bn_stem f sd) eqn:E; [contradiction|]. cbn [length] in NML. lia. }
  pose proof (rw_bbuf _ _ _ _ DP2) as DPb. pose proof (rw_bbuf _ _ _ _ TK2) as TKb.
  pose proof (rw_bbuf _ _ _ _ NM2) as NMb. pose proof (rw_bbuf _ _ _ _ W42) as W4b.
  eapply seg_dec; try eassumption. unfold BN_K. lia.
Qed.

Lemma bl_eqb0 : forall w : word, bv_eqb w (Z_to_bv 64 0) = (bv_unsigned w =? 0).
Proof. intros w. unfold bv_eqb. rewrite (unsigned_lit 0) by lia. reflexivity. Qed.

Lemma bl_eqb0s : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.ltb_spec v 0).
  - replace (v mod 2^64) with (v + 2^64)
      by (symmetry; rewrite <- (Z.mod_add v 1 (2^64)) by lia; rewrite Z.mod_small by lia; lia).
    destruct (Z.eqb_spec (v + 2^64) 0); destruct (Z.eqb_spec v 0); first [reflexivity | exfalso; lia].
  - rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma addiw_chk : forall v, -2^31 <= v < 2^31 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + -41))) (Z_to_bv 64 (-39)) =
  negb ((2 <=? v) && (v <=? 40)).
Proof.
  intros v Hv. unfold bv_ltu. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648 in *. change (bv_modulus 32) with 4294967296 in *.
  change (2^64) with 18446744073709551616 in *. change (2^31) with 2147483648 in *.
  destruct (Z.leb_spec 2 v); destruct (Z.leb_spec v 40); cbn [andb negb];
    [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.ltb_lt | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma tbl_chk : forall v, -2^31 <= v < 2^31 ->
  bv_ltu (Z_to_bv 64 2) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + -1))) =
  negb ((1 <=? v) && (v <=? 3)).
Proof.
  intros v Hv. unfold bv_ltu. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648 in *. change (bv_modulus 32) with 4294967296 in *.
  change (2^64) with 18446744073709551616 in *. change (2^31) with 2147483648 in *.
  destruct (Z.leb_spec 1 v); destruct (Z.leb_spec v 3); cbn [andb negb];
    [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.ltb_lt | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma land_chk : forall v, 0 <= v < 2^63 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 v)) 1)) (Z_to_bv 64 0) = Z.even v.
Proof.
  intros v Hv. rewrite (unsigned_lit v) by lia.
  replace (Z.land v 1) with (v mod 2)
    by (symmetry; change 2 with (2^1); rewrite <- Z.land_ones by lia; reflexivity).
  rewrite bl_eqb by (pose proof (Z.mod_pos_bound v 2); lia).
  rewrite Zmod_even. destruct (Z.even v); reflexivity.
Qed.

Lemma args_ok_false : forall nm nl tk tl dp dl x y,
  (nm = 0 \/ tk = 0 \/ dp = 0 \/ nl = 0 \/ tl = 0 \/ dl = 0 \/ bn_ok x = false \/ bn_ok y = false \/
   (x = 0 /\ y = 0)) ->
  bn_args_ok nm nl tk tl dp dl x y = false.
Proof.
  intros nm nl tk tl dp dl x y H. destruct (bn_args_ok nm nl tk tl dp dl x y) eqn:E; [|reflexivity].
  apply args_ok_split in E. exfalso. intuition congruence.
Qed.

Lemma args_ok_true : forall nm nl tk tl dp dl x y, nm <> 0 -> tk <> 0 -> dp <> 0 -> nl <> 0 -> tl <> 0 -> dl <> 0 ->
  bn_ok x = true -> bn_ok y = true -> ~ (x = 0 /\ y = 0) -> bn_args_ok nm nl tk tl dp dl x y = true.
Proof.
  intros nm nl tk tl dp dl x y H1 H2 H3 H4 H5 H6 H7 H8 H9. unfold bn_args_ok. rewrite H7, H8.
  replace (nm =? 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  replace (tk =? 0) with false by (symmetry; apply Z.eqb_neq; exact H2).
  replace (dp =? 0) with false by (symmetry; apply Z.eqb_neq; exact H3).
  replace (nl =? 0) with false by (symmetry; apply Z.eqb_neq; exact H4).
  replace (tl =? 0) with false by (symmetry; apply Z.eqb_neq; exact H5).
  replace (dl =? 0) with false by (symmetry; apply Z.eqb_neq; exact H6).
  destruct (Z.eqb_spec x 0); destruct (Z.eqb_spec y 0); first [reflexivity | exfalso; tauto].
Qed.

Lemma bn_ok_out : forall v, v <> 0 -> (v < 2 \/ 40 < v) -> bn_ok v = false.
Proof.
  intros v H1 H2. unfold bn_ok. destruct (Z.eqb_spec v 0) as [E|E]; [lia|].
  destruct (Z.leb_spec 2 v); destruct (Z.leb_spec v 40); cbn [orb andb]; first [reflexivity | exfalso; lia].
Qed.

Lemma bn_ok_odd : forall v, v <> 0 -> Z.even v = false -> bn_ok v = false.
Proof.
  intros v H1 H2. unfold bn_ok. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  rewrite H2, andb_false_r. reflexivity.
Qed.

Lemma bn_ok_in : forall v, 2 <= v <= 40 -> Z.even v = true -> bn_ok v = true.
Proof.
  intros v H1 H2. unfold bn_ok. replace (2 <=? v) with true by (symmetry; apply Z.leb_le; lia).
  replace (v <=? 40) with true by (symmetry; apply Z.leb_le; lia). rewrite H2, orb_true_r. reflexivity.
Qed.

Lemma bn_ok_0 : forall v, v = 0 -> bn_ok v = true.
Proof. intros v ->. reflexivity. Qed.

Lemma STEM_other : forall ff, (ff < 1 \/ 3 < ff) -> bn_STEM ff = bn_STEM 0.
Proof.
  intros ff H. unfold bn_STEM.
  replace (ff =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (ff =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (ff =? 3) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Ltac fold_tbl :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?e] =>
      lazymatch e with
      | context [bv_swrap] => let v := eval vm_compute in e in change e with v
      end
  end.

Lemma seg_sel : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 : word)
    (jdb jdp jtk jnm jw g3 j4 : list byte),
  lo + BN_K <= S -> -2^31 <= f < 2^31 ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_said m (S - BN_K) S (bv_unsigned a1) sd ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  stk rsegs m2 lo (S + -272) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -272) [CB 32 jdb] -> rw_cells rsegs m2 (S + -240) [CB 48 jdp] ->
  rw_cells rsegs m2 (S + -192) [CB 24 jtk] -> rw_cells rsegs m2 (S + -168) [CB 24 jnm] ->
  rw_cells rsegs m2 (S + -144) [CB 32 jw] -> rw_cells rsegs m2 (S + -112) [CB 3 g3] ->
  rw_cells rsegs m2 (S + -109) [CB 5 j4] ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display x10 (Z_to_bv 64 f)
                        x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) a1
                        display_len x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14c40) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 jdb jdp jtk jnm jw g3 j4
    HLO Hf AOK SAID BUFS ST2 MU2 WM2 MI2 SV2 DB2 DP2 TK2 NM2 WB2 G32 W42.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof HIM as (TB & TD & C1 & C2 & C3 & C0 & _).
  assert (TBL : sd = [] -> forall y10 : word,
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -272)) gp tp x5 x6 x7 a6 display y10 (Z_to_bv 64 f)
                          x12 x13 x14 x15 x16 x17
                          a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) a1
                          display_len x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x14c4c) fc None m2 (seg_rom rsegs))).
  { intros Hsd y10.
    assert (ESTM : bn_stem f sd = bn_STEM f) by (rewrite Hsd; reflexivity).
    pose proof (bytes_at_transport rsegs _ _ _ _ _ TB MU2 TD) as TB2.
    apply bytes_at_app in TB2. destruct TB2 as [T1 T23]. rewrite length_le8 in T23.
    apply bytes_at_app in T23. destruct T23 as [T2 T3]. rewrite length_le8 in T3.
    unfold BN_K in *.
    step. step. step.
    rewrite tbl_chk by lia.
    destruct (Z.leb_spec 1 f) as [F1|F1]; destruct (Z.leb_spec f 3) as [F3|F3]; cbn [andb negb]; cbv iota.
    - assert (EF : f = 1 \/ f = 2 \/ f = 3) by lia.
      destruct EF as [EF|[EF|EF]]; rewrite EF; do 4 step; fold_tbl.
      + pose proof (bytes_at_read rsegs m2 _ _ 0 8 T1 ltac:(lia) ltac:(rewrite length_le8; lia)) as HR.
        change (Z.to_nat 0) with 0%nat in HR. rewrite skipn0 in HR.
        rewrite firstn_all2 in HR by (rewrite length_le8; lia).
        replace (wa (BN_TS + 0)) with (Z_to_bv 64 130624) in HR by reflexivity.
        step. step.
        eapply seg_go with (P := BN_S1); try eassumption. rewrite ESTM, EF. exact C1.
      + pose proof (bytes_at_read rsegs m2 _ _ 0 8 T2 ltac:(lia) ltac:(rewrite length_le8; lia)) as HR.
        change (Z.to_nat 0) with 0%nat in HR. rewrite skipn0 in HR.
        rewrite firstn_all2 in HR by (rewrite length_le8; lia).
        replace (wa (BN_TS + Z.of_nat 8 + 0)) with (Z_to_bv 64 130632) in HR by reflexivity.
        step. step.
        eapply seg_go with (P := BN_S2); try eassumption. rewrite ESTM, EF. exact C2.
      + pose proof (bytes_at_read rsegs m2 _ _ 0 8 T3 ltac:(lia) ltac:(rewrite length_le8; lia)) as HR.
        change (Z.to_nat 0) with 0%nat in HR. rewrite skipn0 in HR.
        rewrite firstn_all2 in HR by (rewrite length_le8; lia).
        replace (wa (BN_TS + Z.of_nat 8 + Z.of_nat 8 + 0)) with (Z_to_bv 64 130640) in HR by reflexivity.
        step. step.
        eapply seg_go with (P := BN_S3); try eassumption. rewrite ESTM, EF. exact C3.
    - step. step.
      eapply seg_go with (P := BN_REAC); try eassumption. rewrite ESTM, (STEM_other f) by lia. exact C0.
    - step. step.
      eapply seg_go with (P := BN_REAC); try eassumption. rewrite ESTM, (STEM_other f) by lia. exact C0.
    - step. step.
      eapply seg_go with (P := BN_REAC); try eassumption. rewrite ESTM, (STEM_other f) by lia. exact C0. }
  step.
  rewrite bl_eqb0.
  destruct (Z.eqb_spec (bv_unsigned a1) 0) as [Hz|Hz]; cbv iota.
  - destruct SAID as [(_ & Hsd)|(Hne & _)]; [|contradiction]. exact (TBL Hsd x10).
  - destruct SAID as [(E & _)|(_ & CS)]; [lia|].
    pose proof CS as (SC & sl & SB & SLK & SPD). cbn [disjoint_from] in SPD. destruct SPD as [SPD _].
    unfold BN_K in *.
    pose proof (bytes_at_transport rsegs _ _ _ _ _ SB MU2
                  ltac:(cbn [disjoint_from]; rewrite length_app, bn_bytes_length; cbn [length]; split; [lia|exact I]))
      as SB2.
    destruct (list_eq_dec Z.eq_dec sd []) as [Hsd|Hsd].
    + pose proof (bytes_at_read rsegs m2 _ _ 0 1 SB2 ltac:(lia)
                    ltac:(rewrite length_app, bn_bytes_length; cbn [length]; lia)) as HR.
      rewrite Hsd in HR. change (Z.to_nat 0) with 0%nat in HR. rewrite skipn0 in HR.
      change (firstn 1 (bn_bytes [] ++ Z_to_bv 8 0 :: sl)) with [Z_to_bv 8 0] in HR.
      replace (wa (bv_unsigned a1 + 0)) with a1 in HR
        by (symmetry; unfold wa; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
      step. step.
      try (rewrite bl_zxb by lia). try (rewrite (bl_eqb 0 0) by lia). cbn [negb Z.eqb]. cbv iota.
      exact (TBL Hsd _).
    + pose proof (proj1 (proj1 (bytes_at_app rsegs _ _ _ _) SB2)) as SB3.
      assert (L1 : (0 < length sd)%nat)
        by (apply Nat.neq_0_lt_0; intro E0; apply length_zero_iff_nil in E0; contradiction).
      assert (R0 : 0 < nth 0 sd 0 < 256) by (rewrite Forall_forall in SC; apply SC; apply nth_In; lia).
      pose proof (bl_rd0 m2 _ sd 0 SB3 L1) as HR.
      replace (Z_to_bv 64 (bv_unsigned a1 + Z.of_nat 0)) with a1 in HR
        by (symmetry; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
      step. rewrite bl_zxb by lia.
      step.
      rewrite bl_eqb by lia. replace (nth 0 sd 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace a1 with (Z_to_bv 64 (bv_unsigned a1)) by (apply Z_to_bv_bv_unsigned).
      eapply seg_go with (P := bv_unsigned a1); try eassumption. rewrite (stem_sd f sd Hsd). exact CS.
Qed.

Lemma bn_main : forall (a0 a2 a3 : word),
  a0 = Z_to_bv 64 f -> -2^31 <= f < 2^31 ->
  a2 = Z_to_bv 64 i -> -2^31 <= i < 2^31 ->
  a3 = Z_to_bv 64 o -> -2^31 <= o < 2^31 ->
  bytes_at rsegs m S (le8 display ++ le8 display_len) ->
  stk rsegs m lo S -> lo + BN_K <= S ->
  (bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
              (bv_unsigned display) (bv_unsigned display_len) i o = true ->
     bn_said m (S - BN_K) S (bv_unsigned a1) sd /\
     bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len)) ->
  mem_inv rsegs m ->
  evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 REAC_BOX_NAME) fc None m (seg_rom rsegs)).
Proof.
  intros a0 a2 a3 -> Hf -> Hi -> Ho DSB ST HLO PRE MI.
  unfold REAC_BOX_NAME. unfold BN_K in HLO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST as (Q & _); exact Q).
  pose proof (bytes_at_bound rsegs m _ _ DSB) as DSR. rewrite length_app, !length_le8 in DSR.
  apply bytes_at_app in DSB. destruct DSB as [DSa DSb]. rewrite length_le8 in DSb.
  assert (DSH : bytes_at rsegs m S (le8 display) /\ bytes_at rsegs m (S + 8) (le8 display_len)).
  { split; [exact DSa|]. replace (S + 8) with (S + Z.of_nat 8) by lia. exact DSb. }
  clear DSa DSb.
  carve_frame 104%nat ST. rename FR into FRS.
  carve_frame 5%nat ST. rename FR into FW4.
  carve_frame 3%nat ST. rename FR into FG3.
  carve_frame 32%nat ST. rename FR into FWB.
  carve_frame 24%nat ST. rename FR into FNM.
  carve_frame 24%nat ST. rename FR into FTK.
  carve_frame 48%nat ST. rename FR into FDP.
  carve_frame 32%nat ST. rename FR into FDB.
  pose proof (munch_refl [(S - 288, S)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  do 13 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => first [is_var mm; rename mm into m1 | set (m1 := mm) in *] end.
  destruct DSH as [DSa0 DSb0].
  pose proof (bytes_at_transport rsegs _ _ _ _ _ DSa0 MU
                ltac:(cbn [disjoint_from]; rewrite length_le8; split; [lia|exact I])) as DSa.
  pose proof (bytes_at_transport rsegs _ _ _ _ _ DSb0 MU
                ltac:(cbn [disjoint_from]; rewrite length_le8; split; [lia|exact I])) as DSb.
  clear DSa0 DSb0.
  pose proof (bytes_at_read rsegs m1 _ _ 0 8 DSa ltac:(lia) ltac:(rewrite length_le8; lia)) as RDa.
  pose proof (bytes_at_read rsegs m1 _ _ 0 8 DSb ltac:(lia) ltac:(rewrite length_le8; lia)) as RDb.
  change (Z.to_nat 0) with 0%nat in RDa, RDb. rewrite skipn0 in RDa, RDb.
  rewrite firstn_all2 in RDa by (rewrite length_le8; lia).
  rewrite firstn_all2 in RDb by (rewrite length_le8; lia).
  replace (wa (S + 0)) with sp in RDa by (symmetry; unfold wa; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
  replace (wa (S + 8 + 0)) with (Z_to_bv 64 (S + 8)) in RDb by (unfold wa; f_equal; lia).
  clear DSa DSb.
  lazymatch goal with H : rw_cells rsegs m1 (S + -104) _ |- _ => rename H into SV1 end.
  assert (SV2 : rw_cells rsegs m1 (S + -104) SVC)
    by (first [exact SV1 | eapply rw_cells_conv; [exact SV1 | cbn; tauto | reflexivity]]).
  clear SV1.
  assert (STF : stk rsegs m1 lo (S + -104)).
  { pose proof (stk_of_rw_cells rsegs _ _ _ FDB) as K1. pose proof (stk_of_rw_cells rsegs _ _ _ FDP) as K2.
    pose proof (stk_of_rw_cells rsegs _ _ _ FTK) as K3. pose proof (stk_of_rw_cells rsegs _ _ _ FNM) as K4.
    pose proof (stk_of_rw_cells rsegs _ _ _ FWB) as K5. pose proof (stk_of_rw_cells rsegs _ _ _ FG3) as K6.
    pose proof (stk_of_rw_cells rsegs _ _ _ FW4) as K7.
    cbn [cells_size csize Nat.add] in K1, K2, K3, K4, K5, K6, K7.
    pose proof (stk_glue _ _ _ _ _ ST K1 ltac:(lia) ltac:(lia)) as G1.
    pose proof (stk_glue _ _ _ _ _ G1 K2 ltac:(lia) ltac:(lia)) as G2.
    pose proof (stk_glue _ _ _ _ _ G2 K3 ltac:(lia) ltac:(lia)) as G3.
    pose proof (stk_glue _ _ _ _ _ G3 K4 ltac:(lia) ltac:(lia)) as G4.
    pose proof (stk_glue _ _ _ _ _ G4 K5 ltac:(lia) ltac:(lia)) as G5.
    pose proof (stk_glue _ _ _ _ _ G5 K6 ltac:(lia) ltac:(lia)) as G6.
    pose proof (stk_glue _ _ _ _ _ G6 K7 ltac:(lia) ltac:(lia)) as G7.
    eapply stk_ext; [exact G7|lia]. }
  assert (REF : forall (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28
                        y29 y30 y31 : word),
    bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
               (bv_unsigned display) (bv_unsigned display_len) i o = false ->
    evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (S + -272)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 (-1)) y11 y12 y13 y14 y15
                          y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x15040) fc None m1 (seg_rom rsegs))).
  { intros y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 AF.
    eapply seg_epi; [unfold BN_K; lia | exact STF | exact SV2 | exact WM | exact MI |].
    unfold bn_res, bn_accept. rewrite AF. cbn [andb]. unfold BN_K. split; [reflexivity|exact MU]. }
  step. step. step. step.
  step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned display_len) 0) as [D0|D0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  step. step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned a7) 0) as [T0|T0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  step. step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned a5) 0) as [N0|N0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  step. step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned a4) 0) as [M0|M0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  step. step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned a6) 0) as [K0|K0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  step. step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned display) 0) as [P0|P0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  assert (SEL : bn_ok i = true -> bn_ok o = true -> ~ (i = 0 /\ o = 0) -> forall y10 y12 y13 : word,
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (S + -272)) gp tp t0 t1 t2 a6 display y10 (Z_to_bv 64 f)
                          y12 y13 a4 a5 a6 a7 a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) a1
                          display_len s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x14c40) fc None m1 (seg_rom rsegs))).
  { intros OKI OKO NZ y10 y12 y13.
    assert (AOK : bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
                             (bv_unsigned display) (bv_unsigned display_len) i o = true)
      by (apply args_ok_true; assumption).
    destruct (PRE AOK) as [SAID BUFS].
    eapply seg_sel; try eassumption; unfold BN_K; lia. }
  assert (OK2 : forall y12 y13 : word, bn_ok i = true -> o <> 0 ->
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (S + -272)) gp tp t0 t1 t2 a6 display (Z_to_bv 64 (-1)) (Z_to_bv 64 f)
                          y12 y13 a4 a5 a6 a7 a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) a1
                          display_len s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x14c2c) fc None m1 (seg_rom rsegs))).
  { intros y12 y13 OKI O0.
    step. step. step.
    rewrite addiw_chk by lia.
    destruct (Z.leb_spec 2 o); destruct (Z.leb_spec o 40); cbn [andb negb]; cbv iota;
      [| apply REF; apply args_ok_false; right; right; right; right; right; right; right; left;
         apply bn_ok_out; lia ..].
    step. step.
    rewrite land_chk by lia.
    destruct (Z.even o) eqn:EV; cbn [negb]; cbv iota.
    - apply SEL; [exact OKI | apply bn_ok_in; [lia | exact EV] | lia].
    - apply REF. apply args_ok_false. right; right; right; right; right; right; right; left.
      apply bn_ok_odd; assumption. }
  step. step. step.
  rewrite bl_eqb0s by lia.
  destruct (Z.eqb_spec i 0) as [I0|I0]; cbv iota.
  - step.
    rewrite bl_eqb0s by lia.
    destruct (Z.eqb_spec o 0) as [O0|O0]; cbv iota.
    + apply REF. apply args_ok_false. tauto.
    + apply OK2; [apply bn_ok_0; exact I0 | exact O0].
  - step. step. step.
    rewrite addiw_chk by lia.
    destruct (Z.leb_spec 2 i); destruct (Z.leb_spec i 40); cbn [andb negb]; cbv iota;
      [| apply REF; apply args_ok_false; right; right; right; right; right; right; left;
         apply bn_ok_out; lia ..].
    step. step.
    rewrite land_chk by lia.
    destruct (Z.even i) eqn:EV; cbn [negb]; cbv iota.
    + assert (OKI : bn_ok i = true) by (apply bn_ok_in; [lia | exact EV]).
      step.
      rewrite bl_eqb0s by lia.
      destruct (Z.eqb_spec o 0) as [O0|O0]; cbn [negb]; cbv iota.
      * step. apply SEL; [exact OKI | apply bn_ok_0; exact O0 | lia].
      * apply OK2; [exact OKI | exact O0].
    + apply REF. apply args_ok_false. right; right; right; right; right; right; left.
      apply bn_ok_odd; assumption.
Qed.

End BoxName.

Theorem reac_box_name_holds : sb_dec_contract -> memcpy_contract -> strlen_contract -> reac_box_name_contract.
Proof.
  intros DEC MC SL. unfold reac_box_name_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo f i o
    display display_len sd E0 Hf E2 Hi E3 Ho DSB ST HLO S16 HIM PRE MI.
  eapply bn_main; eassumption.
Qed.
