(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.

Module RefDeflateEnd1.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition dstatus_ok (st : Z) : Prop :=
  st = 42 \/ st = 57 \/ st = 69 \/ st = 73 \/ st = 91 \/ st = 103 \/ st = 113 \/ st = 666.

Lemma deflateStateCheck_ok : forall s, deflateStateCheck s = false <-> dstatus_ok (ds_status s).
Proof.
  intros s. unfold deflateStateCheck, dstatus_ok, INIT_STATE, GZIP_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, BUSY_STATE, FINISH_STATE.
  rewrite Bool.negb_false_iff, !Bool.orb_true_iff, !Z.eqb_eq. tauto.
Qed.

Definition pcT (k : nat) : Z := nth k [0x17d50; 0x17d68; 0x17d80; 0x17d98; 0x17db0] 0.
Definition offT (k : nat) : Z := nth k [16; 120; 112; 96] 0.
Definition raT (k : nat) : Z := nth k [0x17d60; 0x17d78; 0x17d90; 0x17da8] 0.


Section Entry.

Local Ltac stcase :=
  lazymatch goal with
  | |- _ mod _ = 0 => subst; vm_compute; reflexivity
  | |- _ mod _ <> 0 => subst; vm_compute; discriminate
  | |- ~ (_ mod _ = 0) => subst; vm_compute; discriminate
  | |- 113 < _ => lia
  | |- ~ (113 < _) => lia
  | |- 68 >= _ => lia
  | |- ~ (68 >= _) => lia
  end.
End Entry.


Section Tests.
End Tests.


Section Fin.

Definition dend_rc (st : Z) : Z := if st =? BUSY_STATE then Z_DATA_ERROR else Z_OK.
End Fin.
End RefDeflateEnd1.

Module RefDeflateBound1.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateKZ.RefDeflateEnd1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition db_fixed (n : Z) : Z := n / 2 ^ 3 + n + n / 2 ^ 8 + n / 2 ^ 9 + 4.
Definition db_stored (n : Z) : Z := n / 2 ^ 5 + n + n / 2 ^ 7 + n / 2 ^ 11 + 7.
Definition db_wraplen (wrap strstart : Z) : Z :=
  if wrap =? 0 then 0
  else if wrap =? 1 then 6 + (if negb (strstart =? 0) then 4 else 0)
  else if wrap =? 2 then 18 else 6.
Definition db_result (n wl wbits hbits level : Z) : Z :=
  if negb (wbits =? 15) || negb (hbits =? 15)
  then (if (wbits <=? hbits) && negb (level =? 0) then db_fixed n else db_stored n) + wl
  else n / 2 ^ 12 + n + n / 2 ^ 14 + n / 2 ^ 25 + wl + 7.


Section Entry.

Local Ltac stcase :=
  lazymatch goal with
  | |- _ mod _ = 0 => subst; vm_compute; reflexivity
  | |- _ mod _ <> 0 => subst; vm_compute; discriminate
  | |- ~ (_ mod _ = 0) => subst; vm_compute; discriminate
  | |- 113 < _ => lia
  | |- ~ (113 < _) => lia
  | |- 68 >= _ => lia
  | |- ~ (68 >= _) => lia
  end.
End Entry.


Section Wrap.

Lemma sx32_of_int : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> szwrap 32 (x mod 2 ^ 32) = x.
Proof. intros x Hx. rewrite szwrap_mod by lia. apply szwrap_small; [lia|]. change (2 ^ (32 - 1)) with 2147483648. lia. Qed.

Lemma mod64_of_int : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> x mod 2 ^ 64 = (if x <? 0 then x + 2 ^ 64 else x).
Proof.
  intros x Hx. destruct (Z.ltb_spec x 0).
  - rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
  - apply Z.mod_small. lia.
Qed.

Lemma sx32_u_mod64 : forall x, 0 <= x < 2 ^ 32 ->
  szwrap 32 x mod 2 ^ 64 = (if x <? 2 ^ 31 then x else x - 2 ^ 32 + 2 ^ 64).
Proof.
  intros x Hx. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 32) with 4294967296 in *. change (2 ^ 31) with 2147483648.
  destruct (Z.ltb_spec x 2147483648).
  - rewrite (Z.mod_small (x + _)) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((x + 2147483648) mod 4294967296) with (x + 2147483648 - 4294967296)
      by (rewrite <- (Z.mod_add _ (-1)) by lia; symmetry; apply Z.mod_small; lia).
    rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
End Wrap.


Section Tail.
End Tail.
End RefDeflateBound1.

Module RefDeflateDict1.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateKZ.RefDeflateEnd1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateKZ.RefDeflateBound1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section Entry.

Definition sd_pc1 (st : Z) : Z := if (st =? 42) || (st =? 57) then 0x1528c else 0x1526c.

Local Ltac stcase :=
  lazymatch goal with
  | |- _ mod _ = 0 => subst; vm_compute; reflexivity
  | |- _ mod _ <> 0 => subst; vm_compute; discriminate
  | |- ~ (_ mod _ = 0) => subst; vm_compute; discriminate
  | |- 113 < _ => lia
  | |- ~ (113 < _) => lia
  | |- 68 >= _ => lia
  | |- ~ (68 >= _) => lia
  end.
End Entry.


Section Disp.
End Disp.


Section Disp2.
End Disp2.


Section Epi.
End Epi.
End RefDeflateDict1.

Module RefDeflateDict2.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateKZ.RefDeflateEnd1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateKZ.RefDeflateBound1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateKZ.RefDeflateDict1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition sd_pc2 (wrap st look : Z) : Z :=
  if wrap =? 2 then 0x153d8
  else if wrap =? 1 then (if (st =? 42) && (look =? 0) then 0x1540c else 0x153d8)
  else 0x152a4.

Section W2.
End W2.


Section Adl.
End Adl.


Definition sd_n (ws dl : Z) : Z := if dl <? ws then dl else ws.
Definition sd_pd (ws dl pd : Z) : Z := if dl <? ws then pd else pd + (dl - ws).

Section PostAdl.
End PostAdl.


Definition sd_pc3 (ws dl wrap : Z) : Z :=
  if dl <? ws then 0x152cc else if wrap =? 0 then 0x15448 else 0x152cc.

Section B152ac.
End B152ac.


Lemma sll32_srl31 : forall x, 0 <= x < 2 ^ 31 -> (x * 2 ^ 32) mod 2 ^ 64 / 2 ^ 31 = 2 * x.
Proof.
  intros x Hx. rewrite Z.mod_small by lia.
  replace (x * 2 ^ 32) with (2 * x * 2 ^ 31) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Section Clear1.
End Clear1.


Section Clear2.
End Clear2.


Section Call1.
End Call1.


Section Head.

Definition sd_head_pc (second : bool) : Z := if second then 0x15388 else 0x152f0.
End Head.


Section Body.
End Body.


Section Call2.
End Call2.


Section Final.
End Final.
End RefDeflateDict2.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KZF.

  Lemma bytes_sep : forall a n b m, 0 < n -> 0 < m ->
    (forall z, b <= z < b + m -> ~ (a <= z < a + n)) -> sep a n b m.
  Proof.
    intros a n b m Hn Hm H. unfold sep.
    destruct (Z_lt_le_dec b a) as [Hba|Hab].
    - destruct (Z_lt_le_dec a (b + m)) as [Ham|Ham]; [| right; lia]. exfalso. apply (H a); lia.
    - left. specialize (H b ltac:(lia)). lia.
  Qed.
End KZF.
