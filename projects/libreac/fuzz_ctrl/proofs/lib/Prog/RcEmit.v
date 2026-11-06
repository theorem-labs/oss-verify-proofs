From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcFin RcPorts.
Import ListNotations.
Open Scope Z_scope.

Definition em_wok (n : Z) : bool := (2 <=? n) && (n <=? 40) && Z.even n.

Definition em_hid (mb : list byte) : Z := rc_s32of (rc_u8 mb 56) (rc_u8 mb 57) (rc_u8 mb 58) (rc_u8 mb 59).

Definition em_E (L G n h : Z) : bool := ((L =? 2) || em_wok n) && (negb (G =? 1) || negb (h =? 0)).

Definition em_len (L n : Z) : Z := if L =? 2 then 1492 else 52 + 36 * n.

Definition em_hdr (d6 s6 : list byte) (c16 : Z) (t0 t1 : byte) : list byte :=
  d6 ++ s6 ++ [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 (c16 mod 256); Z_to_bv 8 (c16 / 256); t0; t1].

Definition em_fr (d6 s6 : list byte) (c16 : Z) (t0 t1 : byte) (blk : list byte) (len : Z) : list byte :=
  em_hdr d6 s6 c16 t0 t1 ++ blk ++ repeat (Z_to_bv 8 0) (Z.to_nat (len - 52)) ++ [Z_to_bv 8 194; Z_to_bv 8 234].
