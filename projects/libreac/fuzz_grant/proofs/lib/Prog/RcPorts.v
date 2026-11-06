From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

Definition rc_u8 (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition pu_decl (bs : list byte) : bool :=
  (rc_u8 bs 0 =? 1) && (rc_u8 bs 1 =? 3) &&
  ((rc_u8 bs 4 =? 128) || (rc_u8 bs 4 =? 130) || (rc_u8 bs 4 =? 132)).

Definition pu_ok (p : Z) (bs : list byte) : bool := negb (p =? 0) && pu_decl bs.

Fixpoint pu_nunk (bs : list byte) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => pu_nunk bs k' + (if 4 <=? rc_u8 bs (8 + k')%nat then 1 else 0)
  end.

Fixpoint pu_first (bs : list byte) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' =>
      if (pu_nunk bs k' =? 0) && (4 <=? rc_u8 bs (8 + k')%nat) then rc_u8 bs (8 + k')%nat
      else pu_first bs k'
  end.

Definition rc_s32of (u0 u1 u2 u3 : Z) : Z :=
  let u := u0 + 256 * u1 + 65536 * u2 + 16777216 * u3 in
  if u <? 2147483648 then u else u - 4294967296.

Definition bm_in_ch (bs : list byte) : Z := rc_s32of (rc_u8 bs 0) (rc_u8 bs 1) (rc_u8 bs 2) (rc_u8 bs 3).

Definition bm_out_ch (bs : list byte) : Z := rc_s32of (rc_u8 bs 4) (rc_u8 bs 5) (rc_u8 bs 6) (rc_u8 bs 7).

Definition bm_wok (w : Z) : bool := (2 <=? w) && (w <=? 40) && (w mod 2 =? 0).

Definition bm_uw (mp : Z) (bs : list byte) : Z :=
  if mp =? 0 then 0
  else if (bm_in_ch bs <? 0) || (bm_out_ch bs <? 0) then 0
  else if negb (bm_in_ch bs =? 0) && negb (bm_wok (bm_in_ch bs)) then 0
  else if negb (bm_out_ch bs =? 0) && negb (bm_wok (bm_out_ch bs)) then 0
  else Z.max (bm_in_ch bs) 2.
