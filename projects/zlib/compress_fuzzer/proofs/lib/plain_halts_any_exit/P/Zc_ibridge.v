(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZInst ZApiL ZHarnessL ZApiC ZHarnessC ZInstC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ZIface ZApiInst ZApiInstC ZApiOk ZApiOkC ZLoopFactsC HarnessSmall.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Zc_kit Zc_u2facts.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Zg_zlib_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Transparent the_zapi the_zapiC.
Notation za := the_zapi.
Notation zc := the_zapiC.

Lemma firstn_skipn_swap : forall (A : Type) (a b : nat) (l : list A), firstn a (skipn b l) = skipn b (firstn (b + a) l).
Proof. intros A a b l. rewrite firstn_skipn_comm. reflexivity. Qed.

Lemma bridge_input : forall (comprc : list Z) (slen tin : Z),
  0 <= tin <= slen -> slen <= zlength comprc ->
  ZIface.zfirstn (slen - tin) (ZIface.zskipn tin comprc) = zdrop tin (ztake slen comprc).
Proof.
  intros comprc slen tin HT HS.
  change (@ZIface.zfirstn Z) with (@Prelim.ztake). change (@ZIface.zskipn Z) with (@Prelim.zdrop).
  unfold ztake, zdrop. rewrite firstn_skipn_swap. f_equal. f_equal. lia.
Qed.

Lemma bridge_zcall : forall (comprc : list Z) (slen : Z) (x : u2L zc) (aout : Z),
  0 <= u2_tin x <= slen -> slen <= zlength comprc ->
  ZApiInst.zi_zcall comprc (u2_is zc x) (slen - u2_tin x) aout
  = ZIface.mkZCall (zdrop (u2_tin x) (ztake slen comprc)) aout (ZApiInst.iz_z (u2_is zc x)).
Proof.
  intros comprc slen x aout HT HS. unfold ZApiInst.zi_zcall. unfold u2_tin in *.
  rewrite (bridge_input comprc slen _ HT HS). reflexivity.
Qed.

Lemma bridge_wants : forall (comprc : list Z) (slen : Z) (x : u2L zc) (aout : Z),
  0 <= u2_tin x <= slen -> slen <= zlength comprc ->
  Zg_zlib_iface.zi_wantsG comprc (u2_is zc x) (slen - u2_tin x) aout
  = ic_wants_window zc (zdrop (u2_tin x) (ztake slen comprc)) (u2_is zc x) aout.
Proof.
  intros comprc slen x aout HT HS. unfold Zg_zlib_iface.zi_wantsG. cbn [ic_wants_window the_zapiC ZApiInstC.zinstC].
  unfold ZApiInstC.zic_wants_window. rewrite (bridge_zcall comprc slen x aout HT HS). reflexivity.
Qed.

Lemma bridge_inflate : forall (comprc : list Z) (slen : Z) (x : u2L zc) (aout : Z) (ok : bool),
  0 <= u2_tin x <= slen -> slen <= zlength comprc ->
  i_inflate za comprc (u2_is zc x) (slen - u2_tin x) aout ok
  = (let '(is', consumed, bs, rc) := ic_inflate zc (zdrop (u2_tin x) (ztake slen comprc)) (u2_is zc x) aout ok in
     (is', (slen - u2_tin x) - consumed, aout - zlength bs, bs, rc)).
Proof.
  intros comprc slen x aout ok HT HS.
  cbn [i_inflate the_zapi ZApiInst.zinst ic_inflate the_zapiC ZApiInstC.zinstC].
  unfold ZApiInst.zi_inflate, ZApiInstC.zic_inflate. cbv zeta.
  rewrite (bridge_zcall comprc slen x aout HT HS).
  lazymatch goal with |- context [HarnessSmall.inflate_p ?a ?b ?c ?d] => destruct (HarnessSmall.inflate_p a b c d) as [[s' zr] asked] end.
  cbn [ZIface.zc_input]. change (@ZIface.zlength) with (@Prelim.zlength).
  replace (zlength (zdrop (u2_tin x) (ztake slen comprc))) with (slen - u2_tin x); [reflexivity|].
  unfold zdrop, ztake, zlength. rewrite length_skipn, length_firstn. unfold zlength in HS. lia.
Qed.

Lemma bridge_tin : forall x : u2L zc, i_total_in za (u2_is zc x) = u2_tin x.
Proof. intros x. reflexivity. Qed.
Lemma bridge_tout : forall x : u2L zc, i_total_out za (u2_is zc x) = u2_tout x.
Proof. intros x. reflexivity. Qed.
Lemma bridge_ictout : forall x : u2L zc, ic_total_out zc (u2_is zc x) = u2_tout x.
Proof. intros x. reflexivity. Qed.
Lemma bridge_wsize : z_wsize za = zc_wsize zc.
Proof. reflexivity. Qed.
Lemma bridge_isize : z_isize za = zc_isize zc.
Proof. reflexivity. Qed.
Lemma bridge_iinit : i_init za = ic_init zc.
Proof. reflexivity. Qed.
Lemma u2_x0_totals : forall dlen src, u2_tin (u2_x0 zc dlen src) = 0 /\ u2_tout (u2_x0 zc dlen src) = 0.
Proof.
  intros dlen src. unfold u2_tin, u2_tout, u2_x0. cbn [u2_is ic_init the_zapiC ZApiInstC.zinstC]. unfold ZApiInst.zi_init. cbn [ZApiInst.iz_z].
  pose proof ZApiOk.iz0_totals as [T1 T2]. split; [exact T1| exact T2].
Qed.

Lemma u2_refused : forall dlen src x, 0 < dlen <= ZBC_MAX -> zlength src <= ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
  U2I dlen src x -> u2_wants zc x = true -> exists x', u2_stepP zc false x = inr (Some (x', Z_MEM_ERROR)).
Proof.
  intros dlen src x HD HS HB (R & _) HW. cbv delta [the_zapiC] in *.
  exact (ZApiOkC.u2_nomem dlen src x HD HS HB R HW).
Qed.

Lemma u2_wants_bridge : forall dlen src (x : u2L zc) comprc slen (w : option Prog.bptr),
  0 < dlen <= ZBC_MAX -> zlength src <= ZBC_MAX -> U2I dlen src x ->
  ztake slen comprc = src -> zlength src = slen -> slen <= zlength comprc ->
  u2_wants zc x && match w with None => true | Some _ => false end
  = Zg_zlib_iface.i_wantsG comprc (u2_is zc x) (zlength (u2_rest zc x)) (dlen - u2_tout x) w.
Proof.
  intros dlen src x comprc slen w HD HS UX ES EL HC.
  pose proof (U2I_shape dlen src x UX) as SH. cbv zeta in SH. destruct SH as (TIN0 & TINS & _).
  pose proof (u2_trip dlen src x true HD HS UX) as TR. cbv zeta in TR.
  destruct (ic_inflate zc (zdrop (u2_tin x) src) (u2_is zc x) (dlen - u2_tout x) true) as [[[is' consumed] bs] rc].
  destruct TR as (_ & _ & _ & _ & _ & TRW).
  assert (RL0 : 0 <= zlength (u2_rest zc x)) by (unfold zlength; lia).
  unfold Zg_zlib_iface.i_wantsG. f_equal. rewrite TRW.
  replace (zlength (u2_rest zc x)) with (slen - u2_tin x) by lia.
  rewrite (bridge_wants comprc slen x (dlen - u2_tout x)) by lia. rewrite ES. reflexivity.
Qed.
