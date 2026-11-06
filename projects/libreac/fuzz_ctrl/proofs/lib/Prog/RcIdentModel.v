From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

Definition ID_SIZE : nat := 38.
Definition ADDR_FIRMWARE : Z := 0x0000.
Definition ADDR_REAC_VERSION : Z := 0x0600.
Definition ADDR_MODEL_NAME : Z := 0x1000.
Definition NAME_CAP : nat := 17.
Definition REAC_VER_LEN : nat := 8.

Definition OFF_FW : nat := 0.
Definition OFF_HAS_FW : nat := 2.
Definition OFF_NAME : nat := 3.
Definition OFF_HAS_NAME : nat := 20.
Definition OFF_MAJOR : nat := 22.
Definition OFF_MINOR : nat := 24.
Definition OFF_PATCH : nat := 26.
Definition OFF_RAW : nat := 28.
Definition OFF_HAS_VER : nat := 36.

Definition bz (b : byte) : Z := bv_unsigned b.
Definition zb (z : Z) : byte := Z_to_bv 8 z.

Definition le16 (v : Z) : list byte := [zb (v mod 256); zb ((v / 256) mod 256)].
Definition be16 (hi lo : byte) : Z := bz hi * 256 + bz lo.

Definition upd (l : list byte) (off : nat) (bs : list byte) : list byte :=
  firstn off l ++ bs ++ skipn (off + length bs) l.

Definition get (l : list byte) (off len : nat) : list byte := firstn len (skipn off l).

Definition nthb (l : list byte) (i : nat) : byte := nth i l (zb 0).

Fixpoint first_zero (l : list byte) : nat :=
  match l with
  | [] => O
  | b :: r => if Z.eqb (bz b) 0 then O else S (first_zero r)
  end.

Definition all_digits (l : list byte) : bool := forallb (fun b => Z.leb (bz b) 9) l.

Definition fw_value (p : list byte) : Z :=
  bz (nthb p 0) * 1000 + bz (nthb p 1) * 100 + bz (nthb p 2) * 10 + bz (nthb p 3).

Definition ing_firmware (idb p : list byte) : Z * list byte :=
  if (4 <=? length p)%nat && all_digits (firstn 4 p)
  then (1, upd (upd idb OFF_FW (le16 (fw_value p))) OFF_HAS_FW [zb 1])
  else (0, idb).

Definition name_len (p : list byte) : nat :=
  let n' := Nat.min (length p - 1) (NAME_CAP - 1) in
  Nat.min (first_zero (firstn n' (skipn 1 p))) n'.

Definition ing_name (idb p : list byte) : Z * list byte :=
  let w := name_len p in
  if (2 <=? length p)%nat && (1 <=? w)%nat
  then (1, upd (upd idb OFF_NAME (firstn w (skipn 1 p) ++ [zb 0])) OFF_HAS_NAME [zb 1])
  else (0, idb).

Definition ing_version (idb p : list byte) : Z * list byte :=
  if (REAC_VER_LEN <=? length p)%nat
  then (1,
        upd (upd (upd (upd (upd idb OFF_RAW (firstn REAC_VER_LEN p))
                            OFF_MAJOR (le16 (be16 (nthb p 2) (nthb p 3))))
                       OFF_MINOR (le16 (be16 (nthb p 4) (nthb p 5))))
                  OFF_PATCH (le16 (be16 (nthb p 6) (nthb p 7))))
            OFF_HAS_VER [zb 1])
  else (0, idb).

Definition ING (idb : list byte) (addr : Z) (p : list byte) : Z * list byte :=
  if Z.eqb addr ADDR_FIRMWARE then ing_firmware idb p
  else if Z.eqb addr ADDR_MODEL_NAME then ing_name idb p
  else if Z.eqb addr ADDR_REAC_VERSION then ing_version idb p
  else (0, idb).

Definition ID0 : list byte := repeat (zb 0) ID_SIZE.

Definition fw_milli (idb : list byte) : Z := bz (nthb idb 0) + 256 * bz (nthb idb 1).
Definition has_fw (idb : list byte) : Z := bz (nthb idb OFF_HAS_FW).
Definition model_name (idb : list byte) : list byte := get idb OFF_NAME NAME_CAP.
Definition has_model_name (idb : list byte) : Z := bz (nthb idb OFF_HAS_NAME).
Definition major (idb : list byte) : Z := bz (nthb idb 22) + 256 * bz (nthb idb 23).
Definition minor (idb : list byte) : Z := bz (nthb idb 24) + 256 * bz (nthb idb 25).
Definition patch (idb : list byte) : Z := bz (nthb idb 26) + 256 * bz (nthb idb 27).
Definition raw (idb : list byte) : list byte := get idb OFF_RAW REAC_VER_LEN.
Definition has_reac_version (idb : list byte) : Z := bz (nthb idb OFF_HAS_VER).

Definition id_ok (idb : list byte) : Prop :=
  (has_fw idb = 0 \/ has_fw idb = 1) /\
  (has_model_name idb = 0 \/ has_model_name idb = 1) /\
  (has_reac_version idb = 0 \/ has_reac_version idb = 1) /\
  bz (nthb idb 19) = 0 /\
  (has_model_name idb = 0 -> forall j, (3 <= j < 20)%nat -> bz (nthb idb j) = 0) /\
  (has_model_name idb = 1 -> bz (nthb idb 3) <> 0) /\
  (has_fw idb = 0 -> fw_milli idb = 0) /\
  (has_fw idb = 1 -> fw_milli idb <= 9999) /\
  (has_reac_version idb = 0 -> forall j, (22 <= j < 36)%nat -> bz (nthb idb j) = 0) /\
  (has_reac_version idb = 1 ->
     major idb = be16 (nthb idb 30) (nthb idb 31) /\ minor idb = be16 (nthb idb 32) (nthb idb 33) /\
     patch idb = be16 (nthb idb 34) (nthb idb 35)) /\
  bz (nthb idb 21) = 0 /\ bz (nthb idb 37) = 0.

Lemma upd_length : forall l off bs, (off + length bs <= length l)%nat -> length (upd l off bs) = length l.
Proof.
  intros l off bs H. unfold upd. rewrite !length_app, length_firstn, length_skipn. lia.
Qed.

Lemma ING_length : forall idb addr p, length idb = ID_SIZE -> length (snd (ING idb addr p)) = ID_SIZE.
Proof.
  intros idb addr p H. unfold ING, ing_firmware, ing_name, ing_version.
  assert (Hw : (name_len p <= NAME_CAP - 1)%nat) by (unfold name_len; lia).
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [snd]; try exact H;
  repeat rewrite upd_length; rewrite ?length_app, ?length_firstn, ?H; cbn [length le16];
  unfold ID_SIZE, OFF_FW, OFF_HAS_FW, OFF_NAME, OFF_HAS_NAME, OFF_MAJOR, OFF_MINOR, OFF_PATCH, OFF_RAW,
    OFF_HAS_VER, REAC_VER_LEN, NAME_CAP in *; try lia;
  repeat (rewrite upd_length; rewrite ?length_app, ?length_firstn, ?H; cbn [length le16]; try lia).
Qed.

Lemma ING_ret : forall idb addr p, fst (ING idb addr p) = 0 \/ fst (ING idb addr p) = 1.
Proof.
  intros idb addr p. unfold ING, ing_firmware, ing_name, ing_version.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst]; auto.
Qed.

Lemma ING_ignored : forall idb addr p, fst (ING idb addr p) = 0 -> snd (ING idb addr p) = idb.
Proof.
  intros idb addr p. unfold ING, ing_firmware, ing_name, ing_version.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst snd];
  intro H; try discriminate H; reflexivity.
Qed.
