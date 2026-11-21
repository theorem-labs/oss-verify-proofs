(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  ZChecksum AdlerModel DeflateInv DeflateInvKeep DeflInvTally DeflInvCore RefDeflateRel RefDeflatePost DeflInitLib DeflInvInit
  HarnessKit HarnessSmall HarnessSmallStages HarnessSmallFacts BoundArith BoundInv BoundCore BoundCall.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma dsyms_zin : forall sy s, dsyms sy (zin s) <-> dsyms sy s.
Proof. intros sy s. apply dsyms_iff; destruct s; reflexivity. Qed.

Lemma dsyms_nil_DI : forall s, DI s -> ds_sym_next s = 0 -> dsyms [] s.
Proof.
  intros s [C I] SN. destruct (di_syms _ _ _ _ I) as (sy & Dy & _).
  apply dsyms_zin. apply (dsyms_nil_of _ sy Dy). destruct s; exact SN.
Qed.

Lemma adler_canon_1 : adler_canon 1.
Proof. unfold adler_canon, lo16, hi16, ZChecksum.ABASE. rewrite (Z.mod_small 1 (2 ^ 32)), Z.mod_1_l, Z.div_1_l by lia. lia. Qed.

Theorem DB_ds0 : DB 0 0 ds0 (zr_strm zr0).
Proof.
  unfold zr0. rewrite ds0_sLM.
  match goal with |- DB 0 0 ?S _ =>
    pose proof (scalars_LM (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 2%N 3%N 4%N 5%N 6%N
                  (cs_init (mkZCall [] 0 zstrm0)) 1 15 8 6 0 8) as SC;
    pose proof (sizes_LM (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 2%N 3%N 4%N 5%N 6%N
                  (cs_init (mkZCall [] 0 zstrm0)) 1 15 8 6 0 8) as SZ;
    pose proof (zret_LM (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 2%N 3%N 4%N 5%N 6%N
                  (cs_init (mkZCall [] 0 zstrm0)) 1 15 8 6 0 8 Z_OK eq_refl eq_refl) as ZR;
    pose proof (DI_LM (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 2%N 3%N 4%N 5%N 6%N
                  (cs_init (mkZCall [] 0 zstrm0)) 1 15 8 6 0 8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)) as D0;
    remember S as s0 eqn:Es0
  end.
  destruct SC as (Str & Lk & _ & Bs & _ & _ & _ & _ & Ml & _ & Ma & _ & Sn & Bv & _ & Pd & _).
  destruct SZ as (Ws & _ & Lbs & _ & _ & Lv & Sg & _ & Wr & St & _).
  destruct ZR as (_ & _ & _ & Ti & To & Ad & Dt).
  unfold rk_status' in St. unfold rk_adler' in Ad. change (1 =? 2) with false in St, Ad. cbv iota in St, Ad.
  apply DB_intro; try assumption.
  - unfold zs_ok. rewrite Ti, To, Ad, Dt. unfold Z_UNKNOWN. lia.
  - rewrite Ad. lia.
  - rewrite Ad. exact adler_canon_1.
  - unfold SZX. rewrite Ws, Lbs. split; reflexivity.
  - rewrite Lv. lia.
  - apply dsyms_nil_DI; [exact D0 | exact Sn].
Qed.


Section DATA.
  Variable d : list Z.
  Hypothesis Hd : Forall (fun b => 0 <= b < 256) d.
  Hypothesis Hn : 1 <= zlength d <= 2 ^ 20.

  Record LI (s : deflate_state) (c : czs) (compr : arr) : Prop := MkLI {
    li_db : DB (cz_next_in c) (cz_next_out c) s (cz_z c);
    li_ain : 0 <= cz_avail_in c <= 1;
    li_in : cz_next_in c + cz_avail_in c <= zlength d;
    li_len : arr_len compr = cb (zlength d) }.








  Lemma LI_start : LI ds0 (mkCZS 0 0 0 0 (zr_strm zr0)) (zero_buf (cb (zlength d))).
  Proof.
    constructor; cbn [cz_next_in cz_next_out cz_z cz_avail_in]; [exact DB_ds0 | lia | lia |].
    unfold zero_buf. rewrite arr_len_make. unfold cb. pose proof (cb_budget_le (zlength d) ltac:(lia)). unfold cb_budget in H. lia.
  Qed.


End DATA.
