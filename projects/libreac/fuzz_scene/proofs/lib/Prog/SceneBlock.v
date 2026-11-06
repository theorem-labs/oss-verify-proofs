From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

Definition scene_seg (k : Z) : Z := if k =? 0 then 1 else if k =? 342 then 2 else 0.
Definition scene_len (k : Z) : Z := if k =? 0 then 24 else if k =? 342 then 14 else 26.
Definition scene_off (k : Z) : Z := if k =? 0 then 0 else if k =? 342 then 8890 else 24 + 26 * (k - 1).

Definition scene_trailer : list byte := map (Z_to_bv 8) [0; 0; 3; 0; 0; 0; 1; 0; 0; 0; 0; 0].

Definition scene_payload (b : list byte) (k : Z) : list byte :=
  if k =? 0 then [Z_to_bv 8 0x22; Z_to_bv 8 0xc8] ++ firstn 24 b
  else if k =? 342 then firstn 14 (skipn (Z.to_nat (scene_off k)) b) ++ scene_trailer
  else firstn 26 (skipn (Z.to_nat (scene_off k)) b).

Definition byte_sum (l : list byte) : Z := fold_right (fun x s => bv_unsigned x + s) 0 l.

Definition scene_fields (b : list byte) (k : Z) : list byte :=
  [Z_to_bv 8 0x01; Z_to_bv 8 (scene_seg k); Z_to_bv 8 0; Z_to_bv 8 (scene_len k); Z_to_bv 8 0]
  ++ scene_payload b k.

Definition scene_block (b : list byte) (k : Z) : list byte :=
  [Z_to_bv 8 0xcd; Z_to_bv 8 0xea] ++ scene_fields b k
  ++ [Z_to_bv 8 ((256 - byte_sum (scene_fields b k) mod 256) mod 256)].
