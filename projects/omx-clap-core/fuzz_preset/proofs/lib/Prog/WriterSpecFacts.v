From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Lemma list3_ind (P : list Z -> Prop) :
  P [] -> (forall a, P [a]) -> (forall a b, P [a; b]) ->
  (forall a b c l, P l -> P (a :: b :: c :: l)) -> forall l, P l.
Proof.
  intros H0 H1 H2 H3. fix IH 1. intros [|a [|b [|c l]]].
  - exact H0.
  - exact (H1 a).
  - exact (H2 a b).
  - exact (H3 a b c l (IH l)).
Qed.

Lemma list4_ind (P : list Z -> Prop) :
  P [] -> (forall a, P [a]) -> (forall a b, P [a; b]) -> (forall a b c, P [a; b; c]) ->
  (forall a b c d l, P l -> P (a :: b :: c :: d :: l)) -> forall l, P l.
Proof.
  intros H0 H1 H2 H3 H4. fix IH 1. intros [|a [|b [|c [|d l]]]].
  - exact H0.
  - exact (H1 a).
  - exact (H2 a b).
  - exact (H3 a b c).
  - exact (H4 a b c d l (IH l)).
Qed.

Lemma bytes_ok_cons : forall a l, bytes_ok (a :: l) -> 0 <= a < 256 /\ bytes_ok l.
Proof. intros a l H. inversion H; subst. split; assumption. Qed.

Lemma bytes_ok_intro : forall a l, 0 <= a < 256 -> bytes_ok l -> bytes_ok (a :: l).
Proof. intros a l Ha Hl. constructor; assumption. Qed.

Lemma six_cons : forall a l, Forall (fun s => 0 <= s < 64) (a :: l) ->
  0 <= a < 64 /\ Forall (fun s => 0 <= s < 64) l.
Proof. intros a l H. inversion H; subst. split; assumption. Qed.

Lemma chars_ok : forall l, Forall (fun b => 0 < b < 256) l -> no_zero l /\ bytes_ok l.
Proof.
  intros l H. rewrite Forall_forall in H. unfold no_zero, bytes_ok.
  split; rewrite Forall_forall; intros x Hx; specialize (H x Hx); cbv beta in *; lia.
Qed.

Theorem b64_enc_length : forall bs, length (b64_enc bs) = ((length bs + 2) / 3 * 4)%nat.
Proof.
  intros bs. induction bs as [|a|a b|a b c l IH] using list3_ind.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [b64_enc length]. rewrite IH.
    replace (S (S (S (length l))) + 2)%nat with ((length l + 2) + 1 * 3)%nat by lia.
    rewrite Nat.div_add by lia. lia.
Qed.

Definition b64c_chk (v : Z) : bool :=
  (0 <? b64c v) && (b64c v <? 128) && negb (b64_ws (b64c v)) && negb (b64c v =? 61) &&
  match b64v (b64c v) with Some w => w =? v | None => false end.

Theorem b64c_range : forall v, 0 <= v < 64 ->
  0 < b64c v < 128 /\ b64_ws (b64c v) = false /\ b64c v <> 61 /\ b64v (b64c v) = Some v.
Proof.
  intros v Hv.
  assert (A : forallb (fun n => b64c_chk (Z.of_nat n)) (seq 0 64) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A (Z.to_nat v)). cbv beta in A.
  rewrite Z2Nat.id in A by lia.
  assert (H : b64c_chk v = true) by (apply A; apply in_seq; lia).
  unfold b64c_chk in H. revert H.
  destruct (b64v (b64c v)) as [w|] eqn:E; intros H; [|rewrite andb_false_r in H; discriminate].
  rewrite !andb_true_iff in H. destruct H as [[[[H1 H2] H3] H4] H5].
  rewrite Z.ltb_lt in H1, H2. rewrite negb_true_iff in H3, H4. rewrite Z.eqb_neq in H4.
  rewrite Z.eqb_eq in H5. subst w.
  split; [lia|]. split; [exact H3|]. split; [exact H4|]. reflexivity.
Qed.

Lemma enc_cons : forall v l, 0 <= v < 64 -> Forall (fun c => 0 < c < 128) l ->
  Forall (fun c => 0 < c < 128) (b64c v :: l).
Proof. intros v l Hv Hl. constructor; [|exact Hl]. destruct (b64c_range v Hv) as [H _]. exact H. Qed.

Lemma pad_cons : forall l, Forall (fun c => 0 < c < 128) l -> Forall (fun c => 0 < c < 128) (61 :: l).
Proof. intros l Hl. constructor; [|exact Hl]. cbv beta. lia. Qed.

Lemma b64_enc_chars : forall bs, bytes_ok bs -> Forall (fun c => 0 < c < 128) (b64_enc bs).
Proof.
  intros bs. induction bs as [|a|a b|a b c l IH] using list3_ind; intros Hb.
  - constructor.
  - destruct (bytes_ok_cons _ _ Hb) as [Ha _]. cbn [b64_enc].
    apply enc_cons; [Z.div_mod_to_equations; lia|].
    apply enc_cons; [Z.div_mod_to_equations; lia|].
    apply pad_cons. apply pad_cons. constructor.
  - destruct (bytes_ok_cons _ _ Hb) as [Ha Hb1]. destruct (bytes_ok_cons _ _ Hb1) as [Hb2 _].
    cbn [b64_enc].
    apply enc_cons; [Z.div_mod_to_equations; lia|].
    apply enc_cons; [Z.div_mod_to_equations; lia|].
    apply enc_cons; [Z.div_mod_to_equations; lia|].
    apply pad_cons. constructor.
  - destruct (bytes_ok_cons _ _ Hb) as [Ha Hb1]. destruct (bytes_ok_cons _ _ Hb1) as [Hb2 Hb3].
    destruct (bytes_ok_cons _ _ Hb3) as [Hc Hl].
    cbn [b64_enc].
    apply enc_cons; [Z.div_mod_to_equations; lia|].
    apply enc_cons; [Z.div_mod_to_equations; lia|].
    apply enc_cons; [Z.div_mod_to_equations; lia|].
    apply enc_cons; [Z.div_mod_to_equations; lia|].
    exact (IH Hl).
Qed.

Theorem b64_enc_no_zero : forall bs, bytes_ok bs -> no_zero (b64_enc bs).
Proof.
  intros bs Hb. pose proof (b64_enc_chars bs Hb) as H. unfold no_zero.
  rewrite Forall_forall in *. intros x Hx. specialize (H x Hx). cbv beta in *. lia.
Qed.

Theorem b64_enc_ok : forall bs, bytes_ok bs -> bytes_ok (b64_enc bs).
Proof.
  intros bs Hb. pose proof (b64_enc_chars bs Hb) as H. unfold bytes_ok.
  rewrite Forall_forall in *. intros x Hx. specialize (H x Hx). cbv beta in *. lia.
Qed.

Theorem b64_table_nth : forall v, 0 <= v < 64 -> nth (Z.to_nat v) b64_table 0 = b64c v.
Proof.
  intros v Hv.
  assert (H : forallb (fun n => nth n b64_table 0 =? b64c (Z.of_nat n)) (seq 0 64) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat v)). cbv beta in H.
  rewrite Z2Nat.id in H by lia.
  apply Z.eqb_eq. apply H. apply in_seq. lia.
Qed.

Theorem b64_table_last : nth 64%nat b64_table 0 = 0.
Proof. reflexivity. Qed.

Theorem b64_table_length : length b64_table = 65%nat.
Proof. reflexivity. Qed.

Fixpoint b64_six (bs : list Z) : list Z :=
  match bs with
  | b0 :: b1 :: b2 :: rest =>
      b0 / 4 :: (b0 mod 4) * 16 + b1 / 16 :: (b1 mod 16) * 4 + b2 / 64 :: b2 mod 64 :: b64_six rest
  | [b0; b1] => [b0 / 4; (b0 mod 4) * 16 + b1 / 16; (b1 mod 16) * 4]
  | [b0] => [b0 / 4; (b0 mod 4) * 16]
  | [] => []
  end.

Fixpoint b64_pad (bs : list Z) : Z :=
  match bs with
  | _ :: _ :: _ :: rest => b64_pad rest
  | [_; _] => 1
  | [_] => 2
  | [] => 0
  end.

Lemma scan_b64c : forall v six rest, 0 <= v < 64 ->
  b64_scan 0 six (b64c v :: rest) = b64_scan 0 (six ++ [v]) rest.
Proof.
  intros v six rest Hv. destruct (b64c_range v Hv) as [_ [Hw [H61 Hb]]].
  cbn [b64_scan]. rewrite Hw. apply Z.eqb_neq in H61. rewrite H61, Hb. reflexivity.
Qed.

Lemma scan_61 : forall p six rest, b64_scan p six (61 :: rest) = b64_scan (p + 1) six rest.
Proof. reflexivity. Qed.

Lemma scan_enc : forall bs, bytes_ok bs -> forall acc,
  b64_scan 0 acc (b64_enc bs) = Some (acc ++ b64_six bs, b64_pad bs).
Proof.
  intros bs. induction bs as [|a|a b|a b c l IH] using list3_ind; intros Hb acc.
  - cbn [b64_enc b64_six b64_pad]. rewrite app_nil_r. reflexivity.
  - destruct (bytes_ok_cons _ _ Hb) as [Ha _]. cbn [b64_enc b64_six b64_pad].
    rewrite !scan_b64c by (Z.div_mod_to_equations; lia).
    rewrite !scan_61. rewrite <- !app_assoc. reflexivity.
  - destruct (bytes_ok_cons _ _ Hb) as [Ha Hb1]. destruct (bytes_ok_cons _ _ Hb1) as [Hb2 _].
    cbn [b64_enc b64_six b64_pad].
    rewrite !scan_b64c by (Z.div_mod_to_equations; lia).
    rewrite !scan_61. rewrite <- !app_assoc. reflexivity.
  - destruct (bytes_ok_cons _ _ Hb) as [Ha Hb1]. destruct (bytes_ok_cons _ _ Hb1) as [Hb2 Hb3].
    destruct (bytes_ok_cons _ _ Hb3) as [Hc Hl].
    cbn [b64_enc b64_six b64_pad].
    rewrite !scan_b64c by (Z.div_mod_to_equations; lia).
    rewrite (IH Hl). rewrite <- !app_assoc. reflexivity.
Qed.

Lemma b64_pad_le : forall bs, (b64_pad bs <=? 2) = true.
Proof.
  intros bs. induction bs as [|a|a b|a b c l IH] using list3_ind; [reflexivity..|exact IH].
Qed.

Lemma six_tail_ok_cons4 : forall a b c d l, l <> [] ->
  six_tail_ok (a :: b :: c :: d :: l) = six_tail_ok l.
Proof.
  intros a b c d l Hl. unfold six_tail_ok.
  replace (Z.of_nat (length (a :: b :: c :: d :: l))) with (Z.of_nat (length l) + 1 * 4)
    by (cbn [length]; lia).
  rewrite Z.mod_add by lia.
  destruct l as [|e l]; [congruence|]. reflexivity.
Qed.

Lemma b64_six_tail : forall bs, six_tail_ok (b64_six bs) = true.
Proof.
  intros bs. induction bs as [|a|a b|a b c l IH] using list3_ind.
  - reflexivity.
  - unfold six_tail_ok. cbn [b64_six last length]. rewrite Z.mod_mul by lia. reflexivity.
  - unfold six_tail_ok. cbn [b64_six last length]. rewrite Z.mod_mul by lia. reflexivity.
  - cbn [b64_six]. destruct (b64_six l) as [|e r] eqn:E.
    + reflexivity.
    + rewrite six_tail_ok_cons4 by discriminate. exact IH.
Qed.

Lemma bytes1 : forall b0, 0 <= b0 < 256 -> b0 / 4 * 4 + (b0 mod 4 * 16) / 16 = b0.
Proof. intros. Z.div_mod_to_equations; lia. Qed.

Lemma bytes2 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  b0 / 4 * 4 + (b0 mod 4 * 16 + b1 / 16) / 16 = b0 /\
  (b0 mod 4 * 16 + b1 / 16) mod 16 * 16 + (b1 mod 16 * 4) / 4 = b1.
Proof. intros. split; Z.div_mod_to_equations; lia. Qed.

Lemma bytes3 : forall b0 b1 b2, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  b0 / 4 * 4 + (b0 mod 4 * 16 + b1 / 16) / 16 = b0 /\
  (b0 mod 4 * 16 + b1 / 16) mod 16 * 16 + (b1 mod 16 * 4 + b2 / 64) / 4 = b1 /\
  (b1 mod 16 * 4 + b2 / 64) mod 4 * 64 + b2 mod 64 = b2.
Proof. intros. split; [|split]; Z.div_mod_to_equations; lia. Qed.

Lemma six_bytes_b64_six : forall bs, bytes_ok bs -> six_bytes (b64_six bs) = bs.
Proof.
  intros bs. induction bs as [|a|a b|a b c l IH] using list3_ind; intros Hb.
  - reflexivity.
  - destruct (bytes_ok_cons _ _ Hb) as [Ha _]. cbn [b64_six six_bytes].
    rewrite (bytes1 a Ha). reflexivity.
  - destruct (bytes_ok_cons _ _ Hb) as [Ha Hb1]. destruct (bytes_ok_cons _ _ Hb1) as [Hb2 _].
    cbn [b64_six six_bytes]. destruct (bytes2 a b Ha Hb2) as [E1 E2].
    rewrite E1, E2. reflexivity.
  - destruct (bytes_ok_cons _ _ Hb) as [Ha Hb1]. destruct (bytes_ok_cons _ _ Hb1) as [Hb2 Hb3].
    destruct (bytes_ok_cons _ _ Hb3) as [Hc Hl].
    cbn [b64_six six_bytes]. destruct (bytes3 a b c Ha Hb2 Hc) as [E1 [E2 E3]].
    rewrite E1, E2, E3, (IH Hl). reflexivity.
Qed.

Theorem b64_dec_enc : forall bs, bytes_ok bs -> b64_dec (b64_enc bs) = Some bs.
Proof.
  intros bs Hb. unfold b64_dec. rewrite (scan_enc bs Hb []). cbn [app].
  rewrite b64_pad_le, b64_six_tail. rewrite (six_bytes_b64_six bs Hb). reflexivity.
Qed.

Theorem six_bytes_ok : forall six, Forall (fun s => 0 <= s < 64) six -> bytes_ok (six_bytes six).
Proof.
  intros six. induction six as [|a|a b|a b c|a b c d l IH] using list4_ind; intros H;
    cbn [six_bytes].
  - constructor.
  - constructor.
  - destruct (six_cons _ _ H) as [Ha H1]. destruct (six_cons _ _ H1) as [Hb _].
    apply bytes_ok_intro; [Z.div_mod_to_equations; lia|constructor].
  - destruct (six_cons _ _ H) as [Ha H1]. destruct (six_cons _ _ H1) as [Hb H2].
    destruct (six_cons _ _ H2) as [Hc _].
    apply bytes_ok_intro; [Z.div_mod_to_equations; lia|].
    apply bytes_ok_intro; [Z.div_mod_to_equations; lia|constructor].
  - destruct (six_cons _ _ H) as [Ha H1]. destruct (six_cons _ _ H1) as [Hb H2].
    destruct (six_cons _ _ H2) as [Hc H3]. destruct (six_cons _ _ H3) as [Hd Hl].
    apply bytes_ok_intro; [Z.div_mod_to_equations; lia|].
    apply bytes_ok_intro; [Z.div_mod_to_equations; lia|].
    apply bytes_ok_intro; [Z.div_mod_to_equations; lia|].
    exact (IH Hl).
Qed.

Theorem six_bytes_length : forall six,
  Z.of_nat (length (six_bytes six)) = 6 * Z.of_nat (length six) / 8.
Proof.
  intros six. induction six as [|a|a b|a b c|a b c d l IH] using list4_ind.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [six_bytes length]. rewrite !Nat2Z.inj_succ. rewrite IH. Z.div_mod_to_equations. lia.
Qed.

Lemma b64v_range : forall c v, b64v c = Some v -> 0 <= v < 64.
Proof.
  intros c v. unfold b64v.
  destruct (Z.leb_spec 65 c), (Z.leb_spec c 90), (Z.leb_spec 97 c), (Z.leb_spec c 122),
    (Z.leb_spec 48 c), (Z.leb_spec c 57), (Z.eqb_spec c 43), (Z.eqb_spec c 47);
    cbn [andb]; intros Hs; try discriminate; injection Hs as <-; lia.
Qed.

Lemma scan_inv : forall tb p acc six pad, b64_scan p acc tb = Some (six, pad) ->
  (length six <= length acc + length tb)%nat /\
  (Forall (fun s => 0 <= s < 64) acc -> Forall (fun s => 0 <= s < 64) six).
Proof.
  induction tb as [|c rest IH]; intros p acc six pad H.
  - cbn [b64_scan] in H. injection H as <- <-. split; [lia|]. intros F; exact F.
  - cbn [b64_scan length] in *. revert H.
    destruct (b64_ws c).
    + intros H. destruct (IH _ _ _ _ H) as [L F]. split; [lia|exact F].
    + destruct (c =? 61).
      * intros H. destruct (IH _ _ _ _ H) as [L F]. split; [lia|exact F].
      * destruct (b64v c) as [v|] eqn:Ev; [|intros H; discriminate].
        destruct (p =? 0); [|intros H; discriminate].
        intros H. destruct (IH _ _ _ _ H) as [L F]. rewrite length_app in L. cbn [length] in L.
        split; [lia|]. intros Facc. apply F. apply Forall_app. split; [exact Facc|].
        constructor; [|constructor]. exact (b64v_range c v Ev).
Qed.

Theorem b64_dec_bound : forall tb bs, b64_dec tb = Some bs ->
  Z.of_nat (length bs) <= Z.of_nat (length tb) / 4 * 3 + 2.
Proof.
  intros tb bs H. unfold b64_dec in H. revert H.
  destruct (b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|intros H; discriminate].
  destruct ((pad <=? 2) && six_tail_ok six); [|intros H; discriminate].
  intros H. injection H as <-. destruct (scan_inv _ _ _ _ _ E) as [L _]. cbn [length] in L.
  rewrite six_bytes_length. Z.div_mod_to_equations. lia.
Qed.

Theorem b64_dec_ok : forall tb bs, b64_dec tb = Some bs -> bytes_ok bs.
Proof.
  intros tb bs H. unfold b64_dec in H. revert H.
  destruct (b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|intros H; discriminate].
  destruct ((pad <=? 2) && six_tail_ok six); [|intros H; discriminate].
  intros H. injection H as <-. destruct (scan_inv _ _ _ _ _ E) as [_ F].
  apply six_bytes_ok. apply F. constructor.
Qed.

Definition escaped (bs : list Z) : list Z := flat_map (fun c => if special c then esc c else [c]) bs.

Lemma concat_spieces_run : forall bs run, concat (spieces_run run bs) = run ++ escaped bs.
Proof.
  induction bs as [|c rest IH]; intros run.
  - reflexivity.
  - cbn [spieces_run]. unfold escaped. cbn [flat_map]. destruct (special c).
    + cbn [concat]. rewrite IH. reflexivity.
    + rewrite IH. rewrite <- app_assoc. reflexivity.
Qed.

Theorem wstr_spec : forall bs, wstr bs = 34 :: escaped bs ++ [34].
Proof.
  intros bs. unfold wstr, spieces. cbn [concat]. rewrite concat_app, concat_spieces_run.
  reflexivity.
Qed.

Theorem esc_len : forall c, 0 <= c < 32 \/ c = 34 \/ c = 92 ->
  length (esc c) =
  if (c =? 34) || (c =? 92) || (c =? 10) || (c =? 9) || (c =? 13) then 2%nat else 6%nat.
Proof.
  intros c _. unfold esc.
  destruct (c =? 34), (c =? 92), (c =? 10), (c =? 9), (c =? 13); reflexivity.
Qed.

Lemma hexd_range : forall x, 0 <= x < 16 -> 48 <= hexd x < 103.
Proof. intros x Hx. unfold hexd. destruct (Z.ltb_spec x 10); lia. Qed.

Lemma esc_chars : forall c, 0 <= c < 256 -> Forall (fun b => 0 < b < 256) (esc c).
Proof.
  intros c Hc.
  assert (H1 : 0 <= c / 16 < 16) by (Z.div_mod_to_equations; lia).
  assert (H2 : 0 <= c mod 16 < 16) by (Z.div_mod_to_equations; lia).
  apply hexd_range in H1. apply hexd_range in H2.
  unfold esc.
  destruct (c =? 34); [|destruct (c =? 92); [|destruct (c =? 10); [|destruct (c =? 9); [|destruct (c =? 13)]]]];
    rewrite Forall_forall; intros x Hx; cbn [In] in Hx; intuition (subst; cbv beta; lia).
Qed.

Theorem esc_no_zero : forall c, 0 <= c < 256 -> no_zero (esc c) /\ bytes_ok (esc c).
Proof. intros c Hc. exact (chars_ok (esc c) (esc_chars c Hc)). Qed.

Lemma escaped_chars : forall bs, Forall (fun b => 0 < b < 256) bs ->
  Forall (fun b => 0 < b < 256) (escaped bs).
Proof.
  intros bs H. induction H as [|c l Hc Hl IH]; [constructor|].
  cbv beta in Hc. unfold escaped. cbn [flat_map]. apply Forall_app. split; [|exact IH].
  destruct (special c); [apply esc_chars; lia|constructor; [exact Hc|constructor]].
Qed.

Theorem wstr_no_zero : forall bs, bytes_ok bs -> no_zero bs -> no_zero (wstr bs) /\ bytes_ok (wstr bs).
Proof.
  intros bs Hb Hz. apply chars_ok. rewrite wstr_spec.
  assert (H : Forall (fun b => 0 < b < 256) bs).
  { unfold bytes_ok, no_zero in *. rewrite Forall_forall in *. intros x Hx.
    specialize (Hb x Hx). specialize (Hz x Hx). cbv beta in *. lia. }
  constructor; [cbv beta; lia|]. apply Forall_app. split; [exact (escaped_chars bs H)|].
  constructor; [cbv beta; lia|constructor].
Qed.

Theorem concat_spieces : forall bs, concat (spieces bs) = wstr bs.
Proof. reflexivity. Qed.

Definition count_special (bs : list Z) : nat := length (filter special bs).

Lemma spieces_run_length : forall bs run,
  length (spieces_run run bs) = (2 * count_special bs + 1)%nat.
Proof.
  unfold count_special. induction bs as [|c rest IH]; intros run; cbn [spieces_run filter].
  - reflexivity.
  - destruct (special c); cbn [length]; rewrite IH; lia.
Qed.

Theorem spieces_length : forall bs, length (spieces bs) = (2 * count_special bs + 3)%nat.
Proof.
  intros bs. unfold spieces. cbn [length]. rewrite length_app, spieces_run_length. cbn [length]. lia.
Qed.

Theorem dbl_spec : forall k c need, 0 < c -> need <= c * 2 ^ Z.of_nat k ->
  exists j, (j <= k)%nat /\ dbl k c need = c * 2 ^ Z.of_nat j /\ need <= dbl k c need /\
    (j = 0%nat \/ c * 2 ^ (Z.of_nat j - 1) < need).
Proof.
  induction k as [|k IH]; intros c need Hc Hn.
  - exists 0%nat. cbn [dbl]. change (Z.of_nat 0) with 0 in *. rewrite Z.pow_0_r in *.
    split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
  - cbn [dbl]. destruct (Z.leb_spec need c) as [Hle|Hgt]; cbn [dbl].
    + exists 0%nat. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r.
      split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
    + assert (H2 : need <= 2 * c * 2 ^ Z.of_nat k).
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia. nia. }
      destruct (IH (2 * c) need ltac:(lia) H2) as [j [Hj [Hd [Hnd Hmin]]]].
      exists (S j). rewrite Hd in Hnd |- *. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      split; [lia|]. split; [ring|]. split; [nia|]. right.
      destruct j as [|j'].
      * replace (Z.succ (Z.of_nat 0) - 1) with 0 by lia. rewrite Z.pow_0_r. lia.
      * destruct Hmin as [Hm|Hm]; [discriminate|].
        replace (Z.succ (Z.of_nat (S j')) - 1) with (Z.succ (Z.of_nat j')) by lia.
        replace (Z.of_nat (S j') - 1) with (Z.of_nat j') in Hm by lia.
        rewrite Z.pow_succ_r by lia. nia.
Qed.

Theorem newcap_bound : forall c need,
  (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j) -> 0 < need <= 2 ^ 63 ->
  exists j, 0 <= j <= 51 /\ newcap c need = 4096 * 2 ^ j /\ need <= newcap c need /\
    newcap c need <= 2 ^ 63 /\ c <= newcap c need.
Proof.
  intros c need Hc Hn.
  assert (H0 : exists j0, 0 <= j0 <= 51 /\ (if c =? 0 then 4096 else c) = 4096 * 2 ^ j0 /\
    c <= 4096 * 2 ^ j0).
  { destruct Hc as [-> | [j0 [Hj ->]]].
    - exists 0. split; [lia|]. split; [reflexivity|]. rewrite Z.pow_0_r. lia.
    - assert (0 < 2 ^ j0) by (apply Z.pow_pos_nonneg; lia).
      destruct (Z.eqb_spec (4096 * 2 ^ j0) 0); [lia|].
      exists j0. split; [lia|]. split; [reflexivity|lia]. }
  destruct H0 as [j0 [Hj0 [Hc0 Hcle]]].
  unfold newcap. rewrite Hc0.
  assert (Hp : 0 < 2 ^ j0) by (apply Z.pow_pos_nonneg; lia).
  assert (H63 : 2 ^ 63 = 4096 * 2 ^ 51) by reflexivity.
  assert (Hpre : need <= 4096 * 2 ^ j0 * 2 ^ Z.of_nat 64).
  { change (Z.of_nat 64) with 64. rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
    assert (2 ^ 51 <= 2 ^ (j0 + 64)) by (apply Z.pow_le_mono_r; lia). lia. }
  destruct (dbl_spec 64 (4096 * 2 ^ j0) need ltac:(lia) Hpre) as [j [Hj [Hd [Hnd Hmin]]]].
  rewrite Hd in Hnd |- *.
  rewrite <- Z.mul_assoc, <- Z.pow_add_r in Hnd |- * by lia.
  assert (HJ : j0 + Z.of_nat j <= 51).
  { destruct Hmin as [-> | Hmin]; [lia|].
    destruct j as [|j']; [lia|].
    rewrite <- Z.mul_assoc, <- Z.pow_add_r in Hmin by lia.
    destruct (Z.le_gt_cases (j0 + Z.of_nat (S j')) 51) as [Hle | Hgt]; [exact Hle|].
    assert (2 ^ 51 <= 2 ^ (j0 + (Z.of_nat (S j') - 1))) by (apply Z.pow_le_mono_r; lia). lia. }
  exists (j0 + Z.of_nat j).
  assert (Hpj : 2 ^ (j0 + Z.of_nat j) <= 2 ^ 51) by (apply Z.pow_le_mono_r; lia).
  assert (Hpj0 : 2 ^ j0 <= 2 ^ (j0 + Z.of_nat j)) by (apply Z.pow_le_mono_r; lia).
  split; [lia|]. split; [reflexivity|]. split; [exact Hnd|]. split; lia.
Qed.

Lemma pow4096_le : forall j, 0 <= j -> 4096 * 2 ^ j < 2 ^ 29 -> 4096 * 2 ^ j <= 2 ^ 28.
Proof.
  intros j Hj H. destruct (Z_le_gt_dec j 16) as [Hle|Hgt].
  - assert (2 ^ j <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia).
    assert (E : 2 ^ 28 = 4096 * 2 ^ 16) by reflexivity. lia.
  - assert (2 ^ 17 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia).
    assert (E : 2 ^ 29 = 4096 * 2 ^ 17) by reflexivity. lia.
Qed.

Lemma newcap_le28 : forall c need,
  (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j) -> c < need <= 2 ^ 28 -> newcap c need <= 2 ^ 28.
Proof.
  intros c need Hc Hn.
  assert (Hc0 : 0 <= c).
  { destruct Hc as [->|(j & Hj & ->)]; [lia|]. assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia. }
  assert (H63 : 2 ^ 28 <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  destruct (newcap_bound c need Hc ltac:(lia)) as (k & Hk & Ek & _ & _ & _).
  set (c0 := if c =? 0 then 4096 else c).
  assert (Hc1 : 0 < c0 <= 2 ^ 28).
  { assert (E : 2 ^ 28 = 268435456) by reflexivity. unfold c0. destruct (Z.eqb_spec c 0); lia. }
  assert (H64 : 2 ^ 28 <= 2 ^ Z.of_nat 64) by (apply Z.pow_le_mono_r; lia).
  assert (Hpre : need <= c0 * 2 ^ Z.of_nat 64) by nia.
  destruct (dbl_spec 64 c0 need ltac:(lia) Hpre) as (j & Hj & Ed & Hnd & Hmin).
  assert (Enc : newcap c need = dbl 64 c0 need) by reflexivity.
  destruct j as [|j'].
  - rewrite Enc, Ed. cbn [Z.of_nat]. rewrite Z.pow_0_r. lia.
  - destruct Hmin as [Hz|Hlt]; [discriminate|].
    assert (Hlt2 : newcap c need < 2 ^ 29).
    { rewrite Enc, Ed. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite Nat2Z.inj_succ in Hlt. replace (Z.succ (Z.of_nat j') - 1) with (Z.of_nat j') in Hlt by lia.
      assert (E : 2 ^ 29 = 2 * 2 ^ 28) by reflexivity. nia. }
    rewrite Ek in *. apply pow4096_le; lia.
Qed.
