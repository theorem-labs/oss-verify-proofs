From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcPorts RcBox RcSynth.
Import ListNotations.
Open Scope Z_scope.

Fixpoint ly_le (bs : list byte) : Z :=
  match bs with
  | [] => 0
  | b :: r => bv_unsigned b + 256 * ly_le r
  end.

Definition ly_k (fr : list byte) : Z := rc_u8 fr 2.

Definition ly_tm (fr : list byte) : Z := ly_le (firstn 8 (skipn 8 fr)).

Definition ly_ao (fr : list byte) : Z := rc_u8 fr 16.

Definition ly_al (fr : list byte) : Z := rc_u8 fr 17.

Definition ly_zero : list byte := repeat (Z_to_bv 8 0) 32.

Definition ly_desc : list byte := concat (repeat [Z_to_bv 8 0; Z_to_bv 8 122] 16).

Definition ly_bb (k : Z) : Z :=
  if k =? 3 then 0 else if k =? 4 then 5 else if k =? 5 then 1 else if k =? 6 then 2
  else if k =? 7 then 3 else if k =? 8 then 4 else 6.

Definition ly_base (k : Z) (tb zb : list byte) : list byte :=
  if k =? 0 then ly_zero else if k =? 1 then ly_desc else if k =? 2 then tb else zb.

Definition ly_put (bs : list byte) (ao : Z) (gb : list byte) : list byte :=
  firstn (Z.to_nat ao) bs ++ gb ++ skipn (Z.to_nat ao + length gb) bs.

Definition ly_lay (k : Z) (tb zb : list byte) (g ao al : Z) (gb : list byte) : list byte :=
  if (g =? 0) || (al =? 0) then ly_base k tb zb else ly_put (ly_base k tb zb) ao gb.

Definition ly_dj (a b c d : Z) : Prop := b <= c \/ d <= a.

Definition ly_Z (md : Z) (mb nb : list byte) (b : Z) : list byte :=
  if md =? 0 then ly_zero else if rc mb b =? 1 then synth mb b nb else ly_zero.
