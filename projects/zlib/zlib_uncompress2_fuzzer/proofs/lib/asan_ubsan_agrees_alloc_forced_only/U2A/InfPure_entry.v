(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import InfPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition mode_load (m : Z) : Z := if m =? TYPE then TYPEDO else m.
Definition st_load (cx : ictx) (st : ist) : ist :=
  IST (mode_load (t_mode st)) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st)
      (c_osz cx - t_cout st) 0
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma mode_load_reach : forall m, reach m -> reach (mode_load m) /\ 16180 <= mode_load m <= 16210.
Proof.
  intros m H. unfold mode_load, reach in *. cbv [HEAD DICTID MEM TYPE TYPEDO] in *.
  destruct (Z.eqb_spec m 16191); lia_std.
Qed.
Lemma mode_load_eq : forall m v, mode_load m = v -> v <> TYPEDO -> m = v.
Proof. intros m v E Hv. revert E. unfold mode_load. destruct (Z.eqb_spec m TYPE); intros E; [congruence | exact E]. Qed.
Lemma mode_load_ne : forall m v, m <> TYPE -> m <> v -> mode_load m <> v.
Proof. intros m v H1 H2. unfold mode_load. destruct (Z.eqb_spec m TYPE); [contradiction | exact H2]. Qed.
Lemma mode_load_live : forall m, codes_liveP (mode_load m) -> codes_liveP m.
Proof. intros m. unfold codes_liveP, mode_load. cbv [TYPE TYPEDO LEN_ LIT]. destruct (Z.eqb_spec m 16191); lia_std. Qed.

Lemma sinv_load : forall cx st lf cf,
  0 <= c_n cx < 67108864 -> 1 <= c_osz cx <= 262144 -> ainv cx st lf cf ->
  c_cin0 cx = t_cin st -> c_cout0 cx = t_cout st -> c_W0 cx = Wm cx st ->
  sinv cx (st_load cx st) lf cf.
Proof.
  intros cx st lf cf CXN CXO (R & W & Mo) H1 H2 H3.
  split; [| split; [exact W | split]].
  - clear W Mo.
    destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
    destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
    unfold RNG, st_load in *. icx_cbn.
    destr_conj R.
    split_conj; try assumption; lia_std.
  - clear W Mo R. destruct cx, st. unfold PROG, Wm, st_load in *. icx_cbn. split; [lia_std | split; [lia_std | left; lia_std]].
  - clear W R H1 H2 H3. destruct Mo as (Mr & Mf & Mll & Mcl & Mlive & Mle & Mdi & Mde & Mma & Mco).
    destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
    destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
    unfold MODE, st_load in *. icx_cbn. split_conj.
    + exact (proj1 (mode_load_reach mode Mr)).
    + intros Hf. destruct (Mf Hf) as [Hm Hc]. split; [|exact Hc].
      assert (Hm' : mode <> TYPE) by (clear - Hm; cbv [TYPE HEAD BAD] in *; lia_std).
      unfold mode_load. destruct (Z.eqb_spec mode TYPE); [contradiction | exact Hm].
    + intros E. apply Mll. apply (mode_load_eq _ _ E). cbv; discriminate.
    + intros E. assert (E' : mode = CODELENS) by (apply (mode_load_eq _ _ E); cbv; discriminate).
      destruct (Mcl E') as (A1 & A2 & A3 & A4 & A5 & A6 & A7). split_conj; assumption.
    + intros Hl. exact (Mlive (mode_load_live _ Hl)).
    + intros E. apply Mle. apply (mode_load_eq _ _ E). cbv; discriminate.
    + intros E. apply Mdi. apply (mode_load_eq _ _ E). cbv; discriminate.
    + intros E. apply Mde. apply (mode_load_eq _ _ E). cbv; discriminate.
    + intros E. apply Mma. apply (mode_load_eq _ _ E). cbv; discriminate.
    + intros [E|E]; apply Mco; [left | right]; apply (mode_load_eq _ _ E); cbv; discriminate.
Qed.

