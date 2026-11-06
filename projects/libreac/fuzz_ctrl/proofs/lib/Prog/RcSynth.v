From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox.
Import ListNotations.
Open Scope Z_scope.

Definition bz (x : Z) : byte := Z_to_bv 8 x.

Definition zeros (n : nat) : list byte := repeat (bz 0) n.

Definition rb (row : list byte) (i : nat) : Z := bv_unsigned (nth i row (bz 0)).

Definition rw16 (row : list byte) (i : nat) : Z := rb row i + 256 * rb row (S i).

Definition rw32 (row : list byte) (i : nat) : Z := rw16 row i + 65536 * rw16 row (S (S i)).

Definition rw64 (row : list byte) (i : nat) : Z := rw32 row i + 4294967296 * rw32 row (4 + i).

Definition ic (row : list byte) : Z := bv_swrap 32 (rw32 row 16).

Definition oc (row : list byte) : Z := bv_swrap 32 (rw32 row 20).

Definition has (row : list byte) : Z := rw32 row 56.

Definition sel (row : list byte) : byte := nth 252 row (bz 0).

Definition strap (row : list byte) : byte := nth 253 row (bz 0).

Definition tail (row : list byte) : list byte := firstn 11 (skipn 254 row).

Definition fwm (row : list byte) : Z := rw16 row 266.

Definition rname (row : list byte) : Z := rw64 row 280.

Definition org (row : list byte) : Z := rb row 288.

Definition lay (row : list byte) : Z := rb row 290.

Definition cfg (row : list byte) : list byte := firstn 32 (skipn 24 row).

Definition synok (row : list byte) : bool :=
  (0 <=? ic row) && (0 <=? oc row) && (ic row mod 4 =? 0) && (oc row mod 4 =? 0) && (ic row / 4 + oc row / 4 <=? 12).

Definition ok (row : list byte) : bool := (org row =? 0) || synok row.

Definition slots (row : list byte) : list byte :=
  let si := Z.to_nat (ic row / 4) in
  let so := Z.to_nat (oc row / 4) in
  if lay row =? 1 then repeat (bz 1) so ++ repeat (bz 0) si ++ repeat (bz 3) (12 - si - so)
  else repeat (bz 2) si ++ repeat (bz 1) so ++ repeat (bz 3) (12 - si - so).

Definition gram31 (row : list byte) : list byte :=
  [bz 1; bz 3; bz 0; bz 16; sel row; bz 0; bz 0; strap row] ++ slots row ++ tail row.

Definition gram (row : list byte) : list byte :=
  gram31 row ++ [bz ((256 - (psum (gram31 row) 31 mod 256)) mod 256)].

Definition decl (row : list byte) : list byte := if org row =? 0 then cfg row else gram row.

Definition chk (x : list byte) : byte := bz ((- psum x 31) mod 256).

Definition withchk (x : list byte) : list byte := x ++ [chk x].

Definition J14 : list byte :=
  map bz [4; 3; 0; 20; 0; 2; 0; 254; 15; 240; 65; 10; 0; 0; 18; 18; 1; 0; 6; 0; 1; 0; 120; 247;
          0; 0; 0; 0; 0; 0; 0; 0].

Definition J13 : list byte :=
  map bz [4; 3; 0; 19; 0; 2; 0; 254; 14; 240; 65; 10; 0; 0; 18; 18; 3; 2; 0; 1; 0; 122; 247; 0;
          0; 0; 0; 0; 0; 0; 0; 2].

Definition digits (v : Z) : list byte := map bz [v / 1000; (v / 100) mod 10; (v / 10) mod 10; v mod 10].

Definition whi (w : Z) : byte := bz (Z.shiftr w 8 mod 256).

Definition wlo (w : Z) : byte := bz (w mod 256).

Definition rvb (row : list byte) : list byte :=
  [bz 0; bz 0; whi (rw16 row 268); wlo (rw16 row 268); whi (rw16 row 270); wlo (rw16 row 270);
   whi (rw16 row 272); wlo (rw16 row 272)].

Definition dt1s (a : Z) (D : list byte) : list byte := dt1_out (length D) a D (zeros 32).

Definition nmr (row nb : list byte) : list byte := if rname row =? 0 then zeros 16 else nmf nb.

Definition idf31 (nm : list byte) : list byte :=
  map bz [4; 1; 0; 27; 0; 2; 0; 254; 22; 240; 65; 10; 0; 0; 18; 18; 5; 0; 16; 0; 1] ++ firstn 10 nm.

Definition idf (nm : list byte) : list byte := withchk (idf31 nm).

Definition idlc (nm : list byte) : byte := bz ((- (22 + psum nm 16)) mod 128).

Definition idl31 (nm : list byte) : list byte :=
  map bz [4; 2; 0; 13; 0; 2; 0; 254; 8] ++ firstn 6 (skipn 10 nm) ++ [idlc nm; bz 247] ++ zeros 14.

Definition idl (nm : list byte) : list byte := withchk (idl31 nm).

Definition rc (row : list byte) (b : Z) : Z :=
  if 6 <? b then -1
  else if b =? 0 then (if synok row then 1 else -1)
  else if b =? 3 then (if fwm row <=? 9999 then 1 else -1)
  else if (b =? 5) || (b =? 6) then (if has row =? 0 then 0 else 1)
  else 1.

Definition synth (row : list byte) (b : Z) (nb : list byte) : list byte :=
  if 6 <? b then zeros 32
  else if b =? 0 then (if synok row then gram row else zeros 32)
  else if b =? 1 then J14
  else if b =? 2 then J13
  else if b =? 3 then (if fwm row <=? 9999 then dt1s 0 (digits (fwm row)) else zeros 32)
  else if b =? 4 then dt1s 1536 (rvb row)
  else if has row =? 0 then zeros 32
  else if b =? 5 then idf (nmr row nb)
  else idl (nmr row nb).
