(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk SendModel BitsModel BitsModel2 TrSmallModel FillWinModel
     RefDeflFast1 RefDeflFastM RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 ZChkAdl ZChecksum AdlerModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.


Definition olen (s : deflate_state) : nat := length (cs_out_rev (ds_strm s)).

Lemma length_rev_append : forall {A} (l acc : list A), length (rev_append l acc) = (length l + length acc)%nat.
Proof. intros A l. induction l as [|x l IH]; intros acc; cbn; [reflexivity|]. rewrite IH. cbn. lia. Qed.

Lemma olen_cs_emit : forall st l, length (cs_out_rev (cs_emit st l)) = (length (cs_out_rev st) + length l)%nat.
Proof.
  intros st l. unfold cs_emit. destruct st as [ci cn ca o cao cti cto cm cd cad]. cbn [DeflateState.cs_out_rev cset_out_rev].
  rewrite length_rev_append. lia.
Qed.


Lemma bv8_unsigned_small : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  apply Z.mod_small. lia.
Qed.

Lemma bZ_zb8 : forall l, Forall (fun b => 0 <= b < 256) l -> bZ (map (Z_to_bv 8) l) = l.
Proof.
  intros l H. induction H as [|c l Hc H IH]; [reflexivity|]. cbn [map]. unfold bZ in *. cbn [map]. rewrite bv8_unsigned_small by exact Hc.
  f_equal. exact IH.
Qed.

Lemma adler32_upd_spec : forall a P l, 0 <= a -> P <> 0 -> Forall (fun b => 0 <= b < 256) l ->
  adler32_z_spec a P (map (Z_to_bv 8) l) = adler32_upd a l.
Proof.
  intros a P l Ha HP Hl.
  destruct l as [|c [|c' l']].
  - cbn [map]. rewrite (adler32_z_spec_model a P [] Ha ltac:(cbn; lia) HP). reflexivity.
  - inversion Hl as [|c0 l0 Hc _]; subst.
    unfold adler32_z_spec, adler32_upd, adler32_len1, lo16, hi16, csub, adler_csub, bnth. cbn [map length Z.of_nat Pos.of_succ_nat Z.eqb Pos.eqb nth].
    rewrite bv8_unsigned_small by exact Hc. reflexivity.
  - rewrite (adler32_z_spec_model a P _ Ha) ; [| cbn; lia| exact HP]. rewrite bZ_zb8 by exact Hl. reflexivity.
Qed.


