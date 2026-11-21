(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import InfPure U2AIfaceS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma uw_next_win : forall wsize wn wh copy, 0 <= copy ->
  (wsize = 0 \/ (0 <= wn < 32768 /\ 0 <= wh <= 32768 /\ (wh < 32768 -> wn = wh))) ->
  0 <= snd (uw_next wsize wn wh copy) <= 32768 /\ 0 <= fst (uw_next wsize wn wh copy) < 32768
  /\ (snd (uw_next wsize wn wh copy) < 32768 -> fst (uw_next wsize wn wh copy) = snd (uw_next wsize wn wh copy)).
Proof.
  intros wsize wn wh copy HC HW. unfold uw_next.
  set (wn0 := if wsize =? 0 then 0 else wn). set (wh0 := if wsize =? 0 then 0 else wh).
  assert (INV : 0 <= wn0 < 32768 /\ 0 <= wh0 <= 32768 /\ (wh0 < 32768 -> wn0 = wh0)).
  { subst wn0 wh0. destruct (Z.eqb_spec wsize 0) as [E|E]; [lia|]. destruct HW as [X|X]; [contradiction| exact X]. }
  clearbody wn0 wh0. clear HW.
  destruct (Z.leb_spec 32768 copy) as [F|F]; [cbn [fst snd]; lia|].
  destruct (Z.eqb_spec (copy - Z.min (32768 - wn0) copy) 0) as [E|E]; cbn [fst snd].
  - destruct (Z.eqb_spec (wn0 + Z.min (32768 - wn0) copy) 32768); destruct (Z.ltb_spec wh0 32768); lia.
  - lia.
Qed.

Definition set_win (st : ist) (wh wn : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) wh wn.

Lemma sinv_with_win : forall cx st lf cf W' wh wn,
  sinv cx st lf cf -> W' <> 0 ->
  0 <= wh <= 32768 -> 0 <= wn < 32768 -> (wh < 32768 -> wn = wh) ->
  sinv (with_win cx W') (set_win st wh wn) lf cf.
Proof.
  intros cx st lf cf W' wh wn (R & W & P & Mo) Hw H1 H2 H3.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold with_win, set_win. icx_cbn.
  split; [| split; [| split; [exact P | exact Mo]]].
  - unfold IDefs.RNG in *. cbv zeta in *. icx_cbn. destr_conj R. split_conj; try assumption; lia.
  - unfold WIN, WIN_SIZE. icx_cbn. split; [intros E; exfalso; exact (Hw E) | intros _; split_conj; lia].
Qed.

Lemma set_win_fields : forall st wh wn, t_mode (set_win st wh wn) = t_mode st /\ t_cin (set_win st wh wn) = t_cin st /\ t_cout (set_win st wh wn) = t_cout st
  /\ t_out (set_win st wh wn) = t_out st.
Proof. intros. cbn. tauto. Qed.

Lemma rng_win : forall cx st lf cf, IDefs.RNG cx st lf cf -> 0 <= t_whave st /\ 0 <= t_wnext st.
Proof.
  intros cx st lf cf H. unfold IDefs.RNG in H. cbv zeta in H.
  repeat match type of H with _ /\ _ => let X := fresh "X" in destruct H as [X H] end.
  split; assumption.
Qed.
