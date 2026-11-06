From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel.
Import ListNotations.
Open Scope Z_scope.

Definition bl (zs : list Z) : list byte := map (Z_to_bv 8) zs.

Definition HEAD_ACK34z : list Z :=
  [0xcd; 0xea; 0x04; 0x03; 0x00; 0x14; 0x00; 0x02; 0x00; 0xfe; 0x0f; 0xf0; 0x41; 0x0a; 0x00; 0x00; 0x12; 0x12;
   0x01; 0x00; 0x06; 0x00; 0x01; 0x00; 0x78; 0xf7; 0; 0; 0; 0; 0; 0; 0; 0].

Definition HEAD_MARK34z : list Z :=
  [0xcd; 0xea; 0x04; 0x03; 0x00; 0x14; 0x00; 0x02; 0x00; 0xfe; 0x0f; 0xf0; 0x41; 0x0a; 0x00; 0x00; 0x12; 0x12;
   0x00; 0x00; 0x03; 0x00; 0x00; 0x00; 0x7d; 0xf7; 0; 0; 0; 0; 0; 0; 0; 0].

Definition gb_tail (i : Z) : list Z :=
  if i =? 0 then [0x00; 0x00; 0x04; 0x77]
  else if i =? 1 then [0x06; 0x00; 0x08; 0x6d]
  else if i =? 2 then [0x10; 0x00; 0x11; 0x5a]
  else if i =? 3 then [0x10; 0x11; 0x09; 0x51]
  else if i =? 4 then [0x11; 0x00; 0x11; 0x59]
  else [0x11; 0x11; 0x09; 0x50].

Definition GBz (i : Z) : list Z :=
  [0xcd; 0xea; 0x04; 0x03; 0x00; 0x13; 0x00; 0x02; 0x00; 0xfe; 0x0e; 0xf0; 0x41; 0x0a; 0x00; 0x00; 0x12; 0x11;
   0x05; 0x00] ++ gb_tail i ++ [0xf7; 0; 0; 0; 0; 0; 0; 0; 0; 0x03].

Definition GBallz : list Z := GBz 0 ++ GBz 1 ++ GBz 2 ++ GBz 3 ++ GBz 4 ++ GBz 5.

Definition T32z : list Z :=
  [0x04; 0x03; 0x00; 0x13; 0x00; 0x02; 0x00; 0xfe; 0x0e; 0xf0; 0x41; 0x0a; 0x00; 0x00; 0x12; 0x12;
   0x01; 0x01; 0x00; 0x00; 0x00; 0x00; 0xf7; 0; 0; 0; 0; 0; 0; 0; 0; 0].

Definition ga_r (ch p v : Z) : Z := (128 - ((2 + ch + p + v) mod 128)) mod 128.
Definition ga_c (ch p v : Z) : Z := (256 - ((128 + ch + p + v + ga_r ch p v) mod 256)) mod 256.

Definition GAz (ch p v : Z) : list Z :=
  [0xcd; 0xea; 0x04; 0x03; 0x00; 0x13; 0x00; 0x02; 0x00; 0xfe; 0x0e; 0xf0; 0x41; 0x0a; 0x00; 0x00; 0x12; 0x12;
   0x01; 0x01; ch; p; v; ga_r ch p v; 0xf7; 0; 0; 0; 0; 0; 0; 0; 0; ga_c ch p v].

Definition HEAD_ACK34 : list byte := bl HEAD_ACK34z.
Definition HEAD_MARK34 : list byte := bl HEAD_MARK34z.
Definition GB (i : Z) : list byte := bl (GBz i).
Definition GBall : list byte := bl GBallz.
Definition T32 : list byte := bl T32z.
Definition GA (ch p v : Z) : list byte := bl (GAz ch p v).

Definition CTRL_ROW : Z := 0x1ee20.
Definition CTRL_ROWz : list Z :=
  [0xcd; 0xea; 0x02; 0; 0; 0; 0; 0; 0x94; 0x05; 0x01; 0; 0; 0; 0; 0; 0x12; 0x03; 0x10; 0x06; 0x02; 0x02; 0; 0].
Definition CTRL_ROW_BYTES : list byte := bl CTRL_ROWz.

Definition vz (vals : list byte) (j : nat) : Z := bv_unsigned (nth j vals (Z_to_bv 8 0)).

Definition ga_row (base : Z) (vals : list byte) (c p : nat) : list byte :=
  GA ((base + Z.of_nat c) mod 256) (Z.of_nat p) (vz vals (3 * c + p)).

Definition ga_chan (base : Z) (vals : list byte) (c : nat) : list byte :=
  ga_row base vals c 0 ++ ga_row base vals c 1 ++ ga_row base vals c 2.

Definition SWEEP (base : Z) (w : nat) (vals : list byte) : list byte :=
  HEAD_ACK34 ++ ga_chan base vals 0 ++ HEAD_MARK34 ++ GBall ++
  concat (map (ga_chan base vals) (seq 1 (w - 1))).

Definition vals_legal (w : nat) (vals : list byte) : Prop :=
  forall j, (j < 3 * w)%nat -> legal (Z.of_nat (j mod 3)) (vz vals j).

Lemma length_bl : forall zs, length (bl zs) = length zs.
Proof. intros. apply map_length. Qed.

Lemma length_GB : forall i, length (GB i) = 34%nat.
Proof.
  intros. unfold GB, GBz, gb_tail. rewrite length_bl.
  destruct (i =? 0), (i =? 1), (i =? 2), (i =? 3), (i =? 4); reflexivity.
Qed.

Lemma length_GA : forall ch p v, length (GA ch p v) = 34%nat.
Proof. reflexivity. Qed.

Lemma GBall_split : GBall = GB 0 ++ GB 1 ++ GB 2 ++ GB 3 ++ GB 4 ++ GB 5.
Proof. reflexivity. Qed.

Definition sum_from (k : nat) (zs : list Z) : Z := fold_right Z.add 0 (skipn k zs).
Definition rf1z (zs : list Z) : bool :=
  match zs with
  | a :: b :: c :: d :: _ => (a =? 0xcd) && (b =? 0xea) && (c =? 4) && (d =? 3) && (sum_from 2 zs mod 256 =? 0)
  | _ => false
  end.

Lemma GA_bytes_range : forall ch p v, 0 <= ch < 256 -> 0 <= p < 256 -> 0 <= v < 256 ->
  Forall (fun z => 0 <= z < 256) (GAz ch p v).
Proof.
  intros ch p v Hc Hp Hv. unfold GAz.
  assert (0 <= ga_r ch p v < 128) by (unfold ga_r; apply Z.mod_pos_bound; lia).
  assert (0 <= ga_c ch p v < 256) by (unfold ga_c; apply Z.mod_pos_bound; lia).
  repeat constructor; lia.
Qed.

Lemma GA_sum_block : forall ch p v,
  (sum_from 2 (GAz ch p v)) mod 256 = 0.
Proof.
  intros.
  assert (E : sum_from 2 (GAz ch p v) = 768 + (128 + ch + p + v + ga_r ch p v) + ga_c ch p v)
    by (unfold sum_from, GAz; cbn [skipn fold_right]; lia).
  rewrite E. unfold ga_c. generalize (128 + ch + p + v + ga_r ch p v). intros s.
  Z.div_mod_to_equations. lia.
Qed.

Lemma GA_record_sum : forall ch p v,
  (1 + 1 + ch + p + v + ga_r ch p v) mod 128 = 0.
Proof.
  intros. unfold ga_r. replace (1 + 1 + ch + p + v) with (2 + ch + p + v) by lia.
  generalize (2 + ch + p + v). intros t.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ga_small : forall ch p v, 0 <= ch -> 0 <= p -> 0 <= v -> ch + p + v <= 126 ->
  ga_r ch p v = 126 - ch - p - v /\ ga_c ch p v = 2.
Proof.
  intros ch p v H1 H2 H3 H4.
  assert (Er : ga_r ch p v = 126 - ch - p - v)
    by (unfold ga_r; Z.div_mod_to_equations; lia).
  split; [exact Er|]. unfold ga_c. rewrite Er.
  replace (128 + ch + p + v + (126 - ch - p - v)) with 254 by lia. reflexivity.
Qed.

Lemma rf1_fixed :
  rf1z HEAD_ACK34z = true /\ rf1z HEAD_MARK34z = true /\
  rf1z (GBz 0) = true /\ rf1z (GBz 1) = true /\ rf1z (GBz 2) = true /\
  rf1z (GBz 3) = true /\ rf1z (GBz 4) = true /\ rf1z (GBz 5) = true.
Proof. vm_compute. repeat split. Qed.

Lemma rf3_poll :
  firstn 7 (skipn 16 (GBz 0)) = [0x12; 0x11; 5; 0; 0x00; 0x00; 4] /\
  firstn 7 (skipn 16 (GBz 1)) = [0x12; 0x11; 5; 0; 0x06; 0x00; 8] /\
  firstn 7 (skipn 16 (GBz 2)) = [0x12; 0x11; 5; 0; 0x10; 0x00; 17] /\
  firstn 7 (skipn 16 (GBz 3)) = [0x12; 0x11; 5; 0; 0x10; 0x11; 9] /\
  firstn 7 (skipn 16 (GBz 4)) = [0x12; 0x11; 5; 0; 0x11; 0x00; 17] /\
  firstn 7 (skipn 16 (GBz 5)) = [0x12; 0x11; 5; 0; 0x11; 0x11; 9].
Proof. vm_compute. repeat split. Qed.

Lemma GA_from_T32 : forall ch p v,
  skipn 2 (GAz ch p v) =
  firstn 18 T32z ++ [ch; p; v] ++ [ga_r ch p v] ++ firstn 9 (skipn 22 T32z) ++ [ga_c ch p v].
Proof. reflexivity. Qed.

Definition zsum (zs : list Z) : Z := fold_right Z.add 0 zs.

Definition lay_z (ch p v : Z) : list Z := firstn 18 T32z ++ [ch; p; v] ++ skipn 21 T32z.

Definition finish_z (zs : list Z) : list Z :=
  let r := (128 - zsum (firstn 5 (skipn 16 zs)) mod 128) mod 128 in
  let zs1 := firstn 21 zs ++ [r] ++ skipn 22 zs in
  let c := (256 - zsum (firstn 31 zs1) mod 256) mod 256 in
  firstn 31 zs1 ++ [c] ++ skipn 32 zs1.

Definition finish_bytes (bs : list byte) : list byte := bl (finish_z (map bv_unsigned bs)).

Lemma bv8_small : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. exact Hz.
Qed.

Lemma map_unsigned_bl : forall zs, Forall (fun z => 0 <= z < 256) zs -> map bv_unsigned (bl zs) = zs.
Proof.
  induction zs as [|z zs IH]; intros H; [reflexivity|].
  inversion H; subst. cbn [bl map]. rewrite bv8_small by assumption. f_equal. apply IH. assumption.
Qed.

Lemma stamp_bytes : forall ch p v, 0 <= ch < 256 -> 0 <= p < 256 -> 0 <= v < 256 ->
  bl [0xcd; 0xea] ++ finish_bytes (bl (lay_z ch p v)) = GA ch p v.
Proof.
  intros ch p v Hc Hp Hv. unfold finish_bytes.
  rewrite map_unsigned_bl by (unfold lay_z, T32z; cbn [firstn skipn app]; repeat constructor; lia).
  unfold GA, bl. rewrite <- map_app. f_equal.
  unfold lay_z, finish_z, GAz, T32z, zsum. cbn [firstn skipn app fold_right].
  unfold ga_c, ga_r.
  repeat (match goal with |- cons _ _ = cons _ _ => apply f_equal2 end).
  all: try reflexivity.
  all: Z.div_mod_to_equations; lia.
Qed.
