(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCompressBlk1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4.RefSendTree3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeE3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeE3.RefDeflSafeE2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma static_ltree_dl_hi : forall c, 256 <= c -> 0 <= arr_get static_ltree_dl c <= 8.
Proof.
  intros c Hc. destruct (Z_lt_le_dec c 288) as [Hc'|Hc'].
  - assert (R : forallb (fun k => (0 <=? arr_get static_ltree_dl (256 + Z.of_nat k)) && (arr_get static_ltree_dl (256 + Z.of_nat k) <=? 8)) (seq 0 32) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in R. specialize (R (Z.to_nat (c - 256)) ltac:(apply in_seq; lia)).
    replace (256 + Z.of_nat (Z.to_nat (c - 256))) with c in R by lia.
    apply andb_prop in R. destruct R as [R1 R2]. apply Z.leb_le in R1. apply Z.leb_le in R2. lia.
  - pose proof (static_ltree_dl_bound c). rewrite arr_get_oob in * by (change (arr_len static_ltree_dl) with 288; lia).
    change (arr_dflt static_ltree_dl c) with 0 in *. lia.
Qed.

Lemma stree_Len_TL_END : stree_Len TL END_BLOCK = 7.
Proof. reflexivity. Qed.
Lemma xbits_TL_lit : forall c, c <= 256 -> xbits TL c = 0.
Proof. intros c Hc. unfold xbits. cbn [sd_extra_base]. unfold LITERALS. replace (256 + 1 <=? c) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.
Lemma xbits_TL_END : xbits TL END_BLOCK = 0.
Proof. apply xbits_TL_lit. unfold END_BLOCK. lia. Qed.
Lemma xbits_TL_len : forall lc, xbits TL (arr_get length_code_a lc + LITERALS + 1) = arr_get extra_lbits_a (arr_get length_code_a lc).
Proof.
  intros lc. unfold xbits. cbn [sd_extra_base sd_extra_bits]. pose proof (length_code_bound lc).
  replace (LITERALS + 1 <=? arr_get length_code_a lc + LITERALS + 1) with true by (symmetry; apply Z.leb_le; lia).
  f_equal. lia.
Qed.
Lemma xbits_TD : forall d, 0 <= d -> xbits TD d = arr_get extra_dbits_a d.
Proof. intros d Hd. unfold xbits. cbn [sd_extra_base sd_extra_bits]. replace (0 <=? d) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.sub_0_r. reflexivity. Qed.

Section Syms.
Variable s : deflate_state.
Hypothesis OP : overlay_pre s.
Let N := nsym s.
Let FL := ds_dyn_ltree_fc s.
Let FD := ds_dyn_dtree_fc s.

Lemma N_range : 0 <= N <= ds_lit_bufsize s - 1.
Proof. exact (op_nsym _ OP). Qed.

Lemma sym_codes : forall j, 0 <= j < N ->
  0 <= sym_lcode s j < L_CODES /\ 0 <= sym_lc s (3 * j) < 256 /\ 0 <= sym_dist s (3 * j) <= 32768
  /\ (sym_isdist s j = false -> sym_lcode s j < 256)
  /\ (sym_isdist s j = true -> 256 < sym_lcode s j /\ 0 <= sym_dcode s j < D_CODES /\ 1 <= sym_dist s (3 * j)).
Proof.
  intros j Hj. pose proof (op_syms _ OP j Hj) as [A B]. unfold sym_lcode, sym_isdist, sym_dcode, L_CODES, D_CODES, LITERALS.
  pose proof (length_code_bound (sym_lc s (3 * j))). pose proof (dist_code_bound (sym_dist s (3 * j) - 1)). pose proof (dist_code_bound (256 + Z.shiftr (sym_dist s (3 * j) - 1) 7)).
  destruct (Z.eqb_spec (sym_dist s (3 * j)) 0); cbn [negb].
  - split; [lia|]. split; [lia|]. split; [lia|]. split; [intros _; lia | intros X; discriminate X].
  - split; [lia|]. split; [lia|]. split; [lia|]. split; [intros X; discriminate X|]. intros _. split; [lia|]. split; [|lia].
    unfold d_code. destruct (_ <? 256); lia.
Qed.

Lemma fubini_L : forall g : Z -> Z,
  zsum (fun c => arr_get FL c * g c) 0 (Z.to_nat L_CODES) = zsum (fun j => g (sym_lcode s j)) 0 (Z.to_nat N) + g END_BLOCK.
Proof.
  intros g. destruct (op_hist _ OP) as (HL & _ & _). pose proof N_range as RN.
  transitivity (zsum (fun c => zsum (fun j => zind (sym_lcode s j =? c) * g c) 0 (Z.to_nat N) + zind (c =? END_BLOCK) * g c) 0 (Z.to_nat L_CODES)).
  - apply zsum_ext. intros c Hc. subst FL. rewrite (HL c ltac:(lia)). fold N. rewrite Z.mul_add_distr_r. f_equal. rewrite Z.mul_comm, <- zsum_scale. apply zsum_ext. intros; lia.
  - rewrite zsum_add. rewrite (zsum_swap (fun c j => zind (sym_lcode s j =? c) * g c)). f_equal.
    + apply zsum_ext. intros j Hj. pose proof (sym_codes j ltac:(lia)) as (A & _).
      rewrite (zsum_single (fun c => zind (sym_lcode s j =? c) * g c) 0 (Z.to_nat L_CODES) (sym_lcode s j)); [| lia |].
      * rewrite Z.eqb_refl. cbn [zind]. lia.
      * intros i Hi Ni. replace (sym_lcode s j =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    + rewrite (zsum_single (fun c => zind (c =? END_BLOCK) * g c) 0 (Z.to_nat L_CODES) END_BLOCK); [| unfold END_BLOCK, L_CODES; lia |].
      * rewrite Z.eqb_refl. cbn [zind]. lia.
      * intros i Hi Ni. replace (i =? END_BLOCK) with false by (symmetry; apply Z.eqb_neq; exact Ni). reflexivity.
Qed.

Lemma fubini_D : forall h : Z -> Z,
  zsum (fun d => arr_get FD d * h d) 0 (Z.to_nat D_CODES) = zsum (fun j => zind (sym_isdist s j) * h (sym_dcode s j)) 0 (Z.to_nat N).
Proof.
  intros h. destruct (op_hist _ OP) as (_ & HD & _). pose proof N_range as RN.
  transitivity (zsum (fun d => zsum (fun j => zind (sym_isdist s j && (sym_dcode s j =? d)) * h d) 0 (Z.to_nat N)) 0 (Z.to_nat D_CODES)).
  - apply zsum_ext. intros d Hd. subst FD. rewrite (HD d ltac:(lia)). fold N. rewrite Z.mul_comm, <- zsum_scale. apply zsum_ext. intros; lia.
  - rewrite (zsum_swap (fun d j => zind (sym_isdist s j && (sym_dcode s j =? d)) * h d)).
    apply zsum_ext. intros j Hj. pose proof (sym_codes j ltac:(lia)) as (_ & _ & _ & _ & M).
    destruct (sym_isdist s j); cbn [andb zind].
    + destruct (M eq_refl) as (_ & Rd & _).
      rewrite (zsum_single (fun d => zind (sym_dcode s j =? d) * h d) 0 (Z.to_nat D_CODES) (sym_dcode s j)); [| lia |].
      * rewrite Z.eqb_refl. cbn [zind]. lia.
      * intros i Hi Ni. replace (sym_dcode s j =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    + rewrite zsum_0 by (intros; lia). lia.
Qed.

Lemma data_by_syms : forall (LD DD : Z -> Z),
  zsum (fun c => arr_get FL c * (LD c + xbits TL c)) 0 (Z.to_nat L_CODES)
  + zsum (fun d => arr_get FD d * (DD d + xbits TD d)) 0 (Z.to_nat D_CODES)
  = zsum (fun j => if sym_isdist s j then LD (sym_lcode s j) + sym_xl s j + DD (sym_dcode s j) + sym_xd s j else LD (sym_lcode s j)) 0 (Z.to_nat N)
    + LD END_BLOCK.
Proof.
  intros LD DD. rewrite (fubini_L (fun c => LD c + xbits TL c)), (fubini_D (fun d => DD d + xbits TD d)), xbits_TL_END.
  rewrite Z.add_0_r. rewrite <- Z.add_assoc, (Z.add_comm (LD END_BLOCK)), Z.add_assoc. f_equal.
  rewrite <- zsum_add. apply zsum_ext. intros j Hj. pose proof (sym_codes j ltac:(pose proof N_range; lia)) as (A & B & C & Lit & M).
  destruct (sym_isdist s j) eqn:ISD; cbn [zind].
  - destruct (M eq_refl) as (Rl & Rd & Rdist). unfold sym_xl, sym_xd. rewrite xbits_TD by lia.
    unfold sym_lcode in *. unfold sym_isdist in ISD. destruct (sym_dist s (3 * j) =? 0); [discriminate|]. rewrite xbits_TL_len. lia.
  - rewrite xbits_TL_lit by (pose proof (Lit eq_refl); lia). lia.
Qed.

Corollary data_dyn : forall (LDa DDa : arr),
  zsum (fun c => arr_get FL c * (arr_get LDa c + xbits TL c)) 0 (Z.to_nat L_CODES)
  + zsum (fun d => arr_get FD d * (arr_get DDa d + xbits TD d)) 0 (Z.to_nat D_CODES)
  = zsum (dcost LDa DDa s) 0 (Z.to_nat N) + arr_get LDa END_BLOCK.
Proof. intros. rewrite (data_by_syms (arr_get LDa) (arr_get DDa)). reflexivity. Qed.

Lemma scost_bound : forall j, 0 <= j < N -> 0 <= scost s j <= 31.
Proof.
  intros j Hj. pose proof (sym_codes j Hj) as (A & B & C & Lit & M). unfold scost, dcost, sym_xl, sym_xd.
  destruct (sym_isdist s j) eqn:ISD.
  - destruct (M eq_refl) as (Rl & Rd & Rdist). pose proof (static_ltree_dl_hi (sym_lcode s j) ltac:(lia)).
    pose proof (static_dtree_dl_bound (sym_dcode s j)). pose proof (extra_lbits_bound (arr_get length_code_a (sym_lc s (3 * j)))).
    pose proof (extra_dbits_bound (sym_dcode s j)). lia.
  - pose proof (static_ltree_dl_bound (sym_lcode s j)). lia.
Qed.

Lemma scost_sum_bound : 0 <= zsum (scost s) 0 (Z.to_nat N) <= 31 * N.
Proof.
  pose proof N_range. pose proof (zsum_bound (scost s) 0 (Z.to_nat N) 31 ltac:(lia) ltac:(intros; apply scost_bound; lia)). lia.
Qed.

Lemma static_by_syms :
  zsum (fun c => arr_get FL c * (stree_Len TL c + xbits TL c)) 0 (Z.to_nat L_CODES)
  + zsum (fun d => arr_get FD d * (stree_Len TD d + xbits TD d)) 0 (Z.to_nat D_CODES)
  = zsum (scost s) 0 (Z.to_nat N) + 7.
Proof.
  rewrite (data_by_syms (stree_Len TL) (stree_Len TD)), stree_Len_TL_END. f_equal.
Qed.
End Syms.


Lemma ov_mb_eq : forall s, ov_mb s = tfb_mb (ov_X5 s).
Proof. reflexivity. Qed.

Lemma branch1_lt : forall X6 buf len,
  0 <= ds_opt_len X6 < 2 ^ 40 -> 0 <= ds_static_len X6 < 2 ^ 40 ->
  tfb_branch X6 buf len = 1 -> ds_opt_len X6 < ds_static_len X6.
Proof.
  intros X6 buf len HO HS. unfold tfb_branch. rewrite (wrap64_id (ds_opt_len X6 + 3 + 7)), (wrap64_id (ds_static_len X6 + 3 + 7)) by lia.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Z.leb_spec ((ds_static_len X6 + 3 + 7) / 8) ((ds_opt_len X6 + 3 + 7) / 8)); cbn [orb].
  - destruct (_ && _); [discriminate|]. rewrite Z.eqb_refl. discriminate.
  - destruct (ds_strategy X6 =? Z_FIXED); [destruct (_ && _); [discriminate|]; rewrite Z.eqb_refl; discriminate|].
    destruct (_ && _); [discriminate|]. intros _. Z.to_euclidean_division_equations; lia.
Qed.

Lemma branch2_le : forall X6 buf len,
  0 <= ds_opt_len X6 < 2 ^ 40 -> 0 <= ds_static_len X6 < 2 ^ 40 -> 0 <= len < 2 ^ 40 ->
  tfb_branch X6 buf len = 2 -> len + 4 <= (ds_static_len X6 + 10) / 8 /\ buf <> None.
Proof.
  intros X6 buf len HO HS HL. unfold tfb_branch. rewrite (wrap64_id (ds_opt_len X6 + 3 + 7)), (wrap64_id (ds_static_len X6 + 3 + 7)), (wrap64_id (len + 4)) by lia.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  replace (ds_static_len X6 + 3 + 7) with (ds_static_len X6 + 10) by lia. replace (ds_opt_len X6 + 3 + 7) with (ds_opt_len X6 + 10) by lia.
  set (ol' := if ((ds_static_len X6 + 10) / 8 <=? (ds_opt_len X6 + 10) / 8) || (ds_strategy X6 =? Z_FIXED) then (ds_static_len X6 + 10) / 8 else (ds_opt_len X6 + 10) / 8).
  assert (ol' <= (ds_static_len X6 + 10) / 8).
  { subst ol'. destruct (Z.leb_spec ((ds_static_len X6 + 10) / 8) ((ds_opt_len X6 + 10) / 8)); cbn [orb]; [lia|]. destruct (_ =? _); lia. }
  destruct (Z.leb_spec (len + 4) ol'); cbn [andb].
  - destruct buf as [bz|]; cbn [is_some].
    + intros _. split; [lia|]. intros X. discriminate X.
    + destruct ((ds_static_len X6 + 10) / 8 =? ol'); intros X; discriminate X.
  - destruct ((ds_static_len X6 + 10) / 8 =? ol'); intros X; discriminate X.
Qed.

Lemma branch_cases : forall X6 buf len, tfb_branch X6 buf len = 0 \/ tfb_branch X6 buf len = 1 \/ tfb_branch X6 buf len = 2.
Proof. intros. unfold tfb_branch. cbv zeta. destruct (_ && _); [lia|]. match goal with |- context [if ?c then 0 else 1] => destruct c end; lia. Qed.

Lemma hi_ok_ov : forall P s buf len last,
  hi_ok P s buf len last <->
  (bt_safe (ov_X0 s) TL /\ bt_safe (ov_X1 s) TD
   /\ (0 <= ds_l_max_code (ov_X2 s) /\ ds_l_max_code (ov_X2 s) + 1 < 573) /\ (forall i, 0 <= i <= ds_l_max_code (ov_X2 s) -> 0 <= Len (ov_X2 s) TL i <= 15)
   /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl (ov_X2 s) TL) i < 65536)
   /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc (ov_X2 s)) i < 65536)
   /\ (0 <= ds_d_max_code (ov_X3 s) /\ ds_d_max_code (ov_X3 s) + 1 < 61) /\ (forall i, 0 <= i <= ds_d_max_code (ov_X3 s) -> 0 <= Len (ov_X3 s) TD i <= 15)
   /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl (ov_X3 s) TD) i < 65536)
   /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc (ov_X3 s)) i < 65536)
   /\ bt_safe (ov_X4 s) TB
   /\ ((forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_dl (ov_X5 s)) i < 16)
       /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl (ov_X5 s)) i < 65536))
   /\ 0 <= ds_opt_len (ov_X5 s) < 2 ^ 63 /\ 0 <= ds_static_len (ov_X5 s) < 2 ^ 63 /\ 0 <= ds_strategy (ov_X5 s) <= 4
   /\ match tfb_branch (ov_X6 s) buf len with
      | 0 => stat_ok P last (ov_X6 s)
      | 1 => OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok P last (ov_X6 s) (ov_mb s)
      | _ => sto_ok P (ov_X6 s) buf len last
      end).
Proof.
  intros P s buf len last. unfold hi_ok, ov_X6, ov_mb, ov_X5, ov_X4, ov_X3, ov_X2, ov_X1, ov_X0. cbv zeta.
  split; intros H; exact H.
Qed.

Lemma tfb_pre_ov : forall s buf len last, 0 < ds_level s ->
  tfb_pre s buf len last = tfb_emit (tfb_branch (ov_X6 s) buf len) (ov_X6 s) (ov_mb s) buf len last.
Proof.
  intros s buf len last HL. unfold tfb_pre. replace (0 <? ds_level s) with true by (symmetry; apply Z.ltb_lt; exact HL).
  cbv zeta. rewrite <- ov_X6_tfb, <- ov_X5_tfb, <- ov_mb_eq. reflexivity.
Qed.

Lemma clen_bl_calls : forall X r n, clen (bl_calls X r n) = 3 * Z.of_nat n.
Proof. intros X r n. revert r. induction n as [|n IH]; intros r; cbn [bl_calls clen]; [lia|]. rewrite IH. lia. Qed.
Lemma bl_calls_lens : forall X r n, Forall (fun c => 0 <= snd c <= 16) (bl_calls X r n).
Proof. intros X r n. revert r. induction n as [|n IH]; intros r; cbn [bl_calls]; constructor; [cbn; lia | apply IH]. Qed.


Section Header.
Variable X6 : deflate_state.
Variable last : Z.
Variable mb : Z.
Variable PBL : Z.
Let lmax := ds_l_max_code X6.
Let dmax := ds_d_max_code X6.
Hypothesis Hmb : 0 <= mb <= 18.
Hypothesis Hlast : 0 <= last <= 1.
Hypothesis Hp0 : ds_pending X6 = 0.
Hypothesis Hbv : 0 <= ds_bi_valid X6 <= 16.
Hypothesis Hbb : 0 <= ds_bi_buf X6 < 2 ^ 16.
Hypothesis Hpbl : arr_len (ds_pending_buf X6) = PBL.
Hypothesis Hpbb : PBB X6.
Hypothesis HLD : forall i, 0 <= i <= lmax -> 0 <= Len X6 TL i <= 15.
Hypothesis HDD : forall i, 0 <= i <= dmax -> 0 <= Len X6 TD i <= 15.
Hypothesis HBD : forall x, 0 <= x < 19 -> 0 <= Len X6 TB x <= 7.
Hypothesis Hlmax : 0 <= lmax.
Hypothesis Hdmax : 0 <= dmax.

Definition hX11 : deflate_state := sbs_run X6 (hd_calls last X6 mb).
Definition hX12 : deflate_state := send_tree hX11 TL lmax.
Definition hX13 : deflate_state := send_tree hX12 TD dmax.
Definition hcost : Z := 17 + 3 * (mb + 1) + TDcost (fun x => Len X6 TB x) (fun i => Len X6 TL i) lmax + TDcost (fun x => Len X6 TB x) (fun i => Len X6 TD i) dmax.

Lemma hd_calls_clen : clen (hd_calls last X6 mb) = 17 + 3 * (mb + 1) /\ Forall (fun c => 0 <= snd c <= 16) (hd_calls last X6 mb).
Proof.
  unfold hd_calls. cbn [clen]. rewrite clen_bl_calls. split; [lia|].
  repeat (constructor; [cbn; lia|]). apply bl_calls_lens.
Qed.

Record HDR (y : deflate_state) (w : Z) : Prop := {
  hd_nb : nb_view y = nb_view X6;
  hd_W : ov_W y = ds_bi_valid X6 + w;
  hd_bv : 0 <= ds_bi_valid y <= 16;
  hd_bb : 0 <= ds_bi_buf y < 2 ^ 16;
  hd_pbl : arr_len (ds_pending_buf y) = PBL;
  hd_pend : 0 <= ds_pending y;
  hd_pbb : PBB y;
  hd_prist : forall i, ds_pending y <= i -> arr_get (ds_pending_buf y) i = arr_get (ds_pending_buf X6) i }.

Lemma HDR_X6 : HDR X6 0.
Proof.
  constructor.
  - reflexivity.
  - unfold ov_W. rewrite Hp0. lia.
  - exact Hbv.
  - exact Hbb.
  - exact Hpbl.
  - rewrite Hp0. lia.
  - exact Hpbb.
  - intros; reflexivity.
Qed.

Lemma TDcost_nonneg_L : 0 <= TDcost (fun x => Len X6 TB x) (fun i => Len X6 TL i) lmax.
Proof.
  rewrite TDcost_cnt by apply HLD. apply zsum_nonneg. intros x Hx.
  pose proof (TDcnt_nonneg (fun i => Len X6 TL i) lmax x). pose proof (HBD x Hx). pose proof (extra_blbits_bound x). nia.
Qed.
Lemma TDcost_nonneg_D : 0 <= TDcost (fun x => Len X6 TB x) (fun i => Len X6 TD i) dmax.
Proof.
  rewrite TDcost_cnt by apply HDD. apply zsum_nonneg. intros x Hx.
  pose proof (TDcnt_nonneg (fun i => Len X6 TD i) dmax x). pose proof (HBD x Hx). pose proof (extra_blbits_bound x). nia.
Qed.

Lemma HDR_X11 : HDR hX11 (17 + 3 * (mb + 1)) /\ (ds_bi_valid X6 + hcost <= 8 * PBL -> sbs_ok PBL X6 (hd_calls last X6 mb)).
Proof.
  destruct HDR_X6 as [NB W BV BB PL PE PB PR]. destruct hd_calls_clen as [CL LL]. pose proof TDcost_nonneg_L. pose proof TDcost_nonneg_D.
  unfold hX11. split.
  - constructor.
    + rewrite sbs_nb_view. exact NB.
    + rewrite sbs_W, W, CL. lia.
    + apply sbs_biv; assumption.
    + apply sbs_bib; assumption.
    + rewrite sbs_pbl. exact PL.
    + pose proof (sbs_pending_mono (hd_calls last X6 mb) X6). lia.
    + apply sbs_PBB. exact PB.
    + intros i Hi. rewrite sbs_frame by lia. apply PR. pose proof (sbs_pending_mono (hd_calls last X6 mb) X6). lia.
  - intros HW. apply sbs_ok_of_bound; [exact BV | exact LL |]. rewrite W, CL. unfold hcost in HW. lia.
Qed.

Lemma HDR_X13 : HDR hX13 hcost /\ HDR hX12 (17 + 3 * (mb + 1) + TDcost (fun x => Len X6 TB x) (fun i => Len X6 TL i) lmax)
  /\ (ds_bi_valid X6 + hcost <= 8 * PBL -> send_tree_safe PBL hX11 TL lmax /\ send_tree_safe PBL hX12 TD dmax).
Proof.
  destruct HDR_X11 as [[NB W BV BB PL PE PB PR] _]. pose proof TDcost_nonneg_L. pose proof TDcost_nonneg_D.
  pose proof (nb_view_facts _ _ NB) as (_ & _ & _ & _ & _ & _ & Vfc & Vdl & _).
  assert (EL11 : forall t i, Len hX11 t i = Len X6 t i) by (intros; unfold Len; rewrite Vdl; reflexivity).
  pose proof (send_tree_facts (fun i => Len X6 TL i) (fun x => Len X6 TB x) hX11 TL lmax
                (fun i => EL11 TL i) (fun x => EL11 TB x) HLD ltac:(intros x Hx; pose proof (HBD x Hx); lia) BV) as F12.
  cbv zeta in F12. fold hX12 in F12. destruct F12 as (W12 & NB12 & BV12 & PL12 & PM12 & FR12 & PB12 & BB12 & OK12).
  pose proof (nb_view_facts _ _ NB12) as (_ & _ & _ & _ & _ & _ & Vfc12 & Vdl12 & _).
  assert (EL12 : forall t i, Len hX12 t i = Len X6 t i) by (intros; unfold Len; rewrite Vdl12, Vdl; reflexivity).
  pose proof (send_tree_facts (fun i => Len X6 TD i) (fun x => Len X6 TB x) hX12 TD dmax
                (fun i => EL12 TD i) (fun x => EL12 TB x) HDD ltac:(intros x Hx; pose proof (HBD x Hx); lia) BV12) as F13.
  cbv zeta in F13. fold hX13 in F13. destruct F13 as (W13 & NB13 & BV13 & PL13 & PM13 & FR13 & PB13 & BB13 & OK13).
  split; [| split].
  - constructor.
    + rewrite NB13, NB12. exact NB.
    + rewrite W13, W12, W. unfold hcost. lia.
    + exact BV13.
    + apply BB13. apply BB12. exact BB.
    + rewrite PL13, PL12. exact PL.
    + lia.
    + apply PB13. apply PB12. exact PB.
    + intros i Hi. rewrite FR13 by lia. rewrite FR12 by lia. apply PR. lia.
  - constructor.
    + rewrite NB12. exact NB.
    + rewrite W12, W. lia.
    + exact BV12.
    + apply BB12. exact BB.
    + rewrite PL12. exact PL.
    + lia.
    + apply PB12. exact PB.
    + intros i Hi. rewrite FR12 by lia. apply PR. lia.
  - intros HW. unfold hcost in HW. split.
    + unfold send_tree_safe, RefSendTree4.OK, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4.RefSendTree3.cnts0. replace (lmax + 1 - 0) with (lmax + 1) by lia.
      pose proof (OK12 PBL ltac:(lia)) as OK. unfold cnts0 in OK. exact OK.
    + unfold send_tree_safe, RefSendTree4.OK, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4.RefSendTree3.cnts0. replace (dmax + 1 - 0) with (dmax + 1) by lia.
      pose proof (OK13 PBL ltac:(lia)) as OK. unfold cnts0 in OK. exact OK.
Qed.

Lemma emit1_eq : forall bf ln, tfb_emit 1 X6 mb bf ln last
  = compress_block hX13 (ds_dyn_ltree_fc hX13) (ds_dyn_ltree_dl hX13) (ds_dyn_dtree_fc hX13) (ds_dyn_dtree_dl hX13).
Proof.
  intros bf ln. unfold tfb_emit. cbn [Z.eqb Pos.eqb]. cbv zeta.
  rewrite send_all_trees_eq by lia. unfold hX13, hX12, hX11, hd_calls, sat_calls.
  set (s7 := send_bits X6 (Z.shiftl DYN_TREES 1 + last) 3).
  pose proof (nb_view_facts _ _ (send_bits_nb_view X6 (Z.shiftl DYN_TREES 1 + last) 3)) as (_ & _ & _ & _ & _ & _ & Vfc & Vdl & VL & VD & _).
  fold s7 in Vfc, Vdl, VL, VD. rewrite VL, VD. subst lmax dmax.
  replace (ds_l_max_code X6 + 1 - 257) with (ds_l_max_code X6 - 256) by lia.
  replace (ds_d_max_code X6 + 1 - 1) with (ds_d_max_code X6) by lia.
  replace (ds_l_max_code X6 + 1 - 1) with (ds_l_max_code X6) by lia.
  replace (mb + 1 - 4) with (mb - 3) by lia.
  rewrite (bl_calls_ext X6 s7) by (intros; unfold Len; rewrite Vdl; reflexivity).
  change (Z.shiftl DYN_TREES 1 + last) with (4 + last) in s7. subst s7. cbn [sbs_run app]. reflexivity.
Qed.

Lemma dyn_ok_intro :
  BINV PBL X6 -> sbs_ok PBL X6 (hd_calls last X6 mb) ->
  (0 <= lmax /\ lmax + 1 < 573) -> (0 <= dmax /\ dmax + 1 < 61) ->
  ((forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_dl X6) i < 16) /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X6) i < 65536)) ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X6) i < 65536) ->
  (forall i, 0 <= i <= lmax -> 0 <= Len X6 TL i <= 15) ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_dl X6) i < 65536) ->
  (forall i, 0 <= i <= dmax -> 0 <= Len X6 TD i <= 15) ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_dl X6) i < 65536) ->
  send_tree_safe PBL hX11 TL lmax -> send_tree_safe PBL hX12 TD dmax ->
  compress_block_ok PBL hX13 (ds_dyn_ltree_fc X6) (ds_dyn_ltree_dl X6) (ds_dyn_dtree_fc X6) (ds_dyn_dtree_dl X6) ->
  (forall i, 0 <= i < 286 -> 0 <= arr_get (ds_dyn_ltree_fc X6) i < 65536) ->
  (forall i, 0 <= i < 30 -> 0 <= arr_get (ds_dyn_dtree_fc X6) i < 65536) ->
  compress_lens_ok hX13 (ds_dyn_ltree_fc X6) (ds_dyn_ltree_dl X6) (ds_dyn_dtree_fc X6) (ds_dyn_dtree_dl X6) ->
  (0 <= ds_sym_next X6 /\ ds_sym_next X6 + 3 < 2 ^ 31) -> 0 <= ds_lit_bufsize X6 < 2 ^ 32 ->
  OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok PBL last X6 mb.
Proof.
  intros. unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok, hX13, hX12, hX11 in *. subst lmax dmax. cbv zeta.
  repeat (split; [assumption|]). assumption.
Qed.
End Header.


Lemma init_block_eq : forall y,
  init_block y =
  set_matches (set_sym_next (set_static_len (set_opt_len
    (set_tree_fc (set_bl_tree_fc (set_dyn_dtree_fc (set_dyn_ltree_fc y (arr_fill (ds_dyn_ltree_fc y) 0 L_CODES 0))
                                                    (arr_fill (ds_dyn_dtree_fc y) 0 D_CODES 0))
                                  (arr_fill (ds_bl_tree_fc y) 0 BL_CODES 0))
       TL (arr_set (arr_fill (ds_dyn_ltree_fc y) 0 L_CODES 0) END_BLOCK (wrap16 1))) 0) 0) 0) 0.
Proof. intros y. unfold init_block, set_Freq, Freq. destruct y; reflexivity. Qed.

Record IB (y y' : deflate_state) : Prop := {
  ib_pb : ds_pending_buf y' = ds_pending_buf y;
  ib_pend : ds_pending y' = ds_pending y;
  ib_bb : ds_bi_buf y' = ds_bi_buf y;
  ib_bv : ds_bi_valid y' = ds_bi_valid y;
  ib_lbs : ds_lit_bufsize y' = ds_lit_bufsize y;
  ib_po : ds_pending_out y' = ds_pending_out y;
  ib_strm : ds_strm y' = ds_strm y;
  ib_nt : nt_view y' = nt_view (set_matches (set_sym_next y 0) 0);
  ib_sn : ds_sym_next y' = 0;
  ib_matches : ds_matches y' = 0;
  ib_ol : ds_opt_len y' = 0;
  ib_sl : ds_static_len y' = 0;
  ib_L : tree_lens y -> forall c, 0 <= c < L_CODES -> arr_get (ds_dyn_ltree_fc y') c = zind (c =? END_BLOCK);
  ib_D : tree_lens y -> forall d, 0 <= d < D_CODES -> arr_get (ds_dyn_dtree_fc y') d = 0;
  ib_B : tree_lens y -> forall b, 0 <= b < BL_CODES -> arr_get (ds_bl_tree_fc y') b = 0;
  ib_fcT : (forall t i, 0 <= arr_get (tree_fc y t) i < 65536) -> forall t i, 0 <= arr_get (tree_fc y' t) i < 65536;
  ib_dl : forall t, tree_dl y' t = tree_dl y t;
  ib_depth : ds_depth y' = ds_depth y;
  ib_blc : ds_bl_count y' = ds_bl_count y;
  ib_tl : tree_lens y -> tree_lens y' }.

Lemma fill0_get : forall (a : arr) n i, 0 <= i < n -> n <= arr_len a -> arr_get (arr_fill a 0 n 0) i = 0.
Proof.
  intros a n i Hi Hn. rewrite arr_get_fill. unfold arr_inb.
  replace ((0 <=? i) && (i <? 0 + Z.max 0 n) && ((0 <=? i) && (i <? arr_len a))) with true; [reflexivity|].
  symmetry. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
Qed.
Lemma fill0_typed : forall (a : arr) n i, (forall j, 0 <= arr_get a j < 65536) -> 0 <= arr_get (arr_fill a 0 n 0) i < 65536.
Proof. intros a n i H. rewrite arr_get_fill. destruct (_ && _); [lia | apply H]. Qed.

Lemma init_block_facts : forall y, IB y (init_block y).
Proof.
  intros y. rewrite init_block_eq. unfold set_tree_fc.
  constructor; unfold nt_view, tree_lens; dsred.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros (L1 & _) c Hc.
    rewrite arr_get_set. unfold arr_inb. rewrite arr_len_fill, L1.
    destruct (Z.eqb_spec END_BLOCK c) as [<-|N]; cbn [andb].
    + rewrite Z.eqb_refl. reflexivity.
    + replace (c =? END_BLOCK) with false by (symmetry; apply Z.eqb_neq; congruence). cbn [zind].
      apply fill0_get; [exact Hc | rewrite L1; unfold L_CODES; lia].
  - intros (_ & _ & L3 & _) d Hd. apply fill0_get; [exact Hd | rewrite L3; unfold D_CODES; lia].
  - intros (_ & _ & _ & _ & L5 & _) b Hb. apply fill0_get; [exact Hb | rewrite L5; unfold BL_CODES; lia].
  - intros T t i. destruct t; cbn [tree_fc]; dsred; [| apply fill0_typed; exact (T TD) | apply fill0_typed; exact (T TB)].
    rewrite arr_get_set. destruct (_ && _); [rewrite wrap16_id by lia; lia | apply fill0_typed; exact (T TL)].
  - intros t; destruct t; cbn [tree_dl]; dsred; reflexivity.
  - reflexivity.
  - reflexivity.
  - intros TLn. rewrite arr_len_set, !arr_len_fill. exact TLn.
Qed.

Section Flush.
Variable s : deflate_state.
Variable last : Z.
Hypothesis FE : fb_entry s last.
Hypothesis HOV : OVERLAY_CORE.

Let lbs := ds_lit_bufsize s.
Let N := nsym s.
Let PBL := ds_lit_bufsize s * 4.

Lemma OP : overlay_pre s.
Proof. destruct FE. constructor; assumption. Qed.

Let TP : TPF s := tree_phase s OP.

Lemma FEn : 2048 <= lbs <= 32768 /\ arr_len (ds_pending_buf s) = PBL /\ ds_pending s = 0 /\ 0 <= ds_bi_valid s <= 7
  /\ 0 <= ds_bi_buf s < 2 ^ 16 /\ ds_sym_next s = 3 * N /\ 0 <= N <= lbs - 1 /\ ds_pending_out s = 0 /\ 1 <= ds_level s <= 9
  /\ 0 <= ds_strategy s <= 4 /\ 0 <= last <= 1 /\ PBB s.
Proof.
  pose proof FE as F. destruct F. subst lbs N PBL.
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold PBB. assumption.
Qed.

Lemma X6n : ds_pending_buf (ov_X6 s) = ds_pending_buf s /\ ds_pending (ov_X6 s) = 0 /\ ds_bi_buf (ov_X6 s) = ds_bi_buf s
  /\ ds_bi_valid (ov_X6 s) = ds_bi_valid s /\ ds_lit_bufsize (ov_X6 s) = lbs /\ ds_sym_next (ov_X6 s) = 3 * N
  /\ ds_pending_out (ov_X6 s) = 0 /\ ds_level (ov_X6 s) = ds_level s /\ ds_strategy (ov_X6 s) = ds_strategy s
  /\ ds_block_start (ov_X6 s) = ds_block_start s /\ ds_strstart (ov_X6 s) = ds_strstart s
  /\ ds_window (ov_X6 s) = ds_window s /\ ds_w_size (ov_X6 s) = ds_w_size s.
Proof.
  pose proof (nt_view_facts _ _ (tp_nt6 _ TP)) as V. pose proof FEn as (_ & _ & F3 & _ & _ & F6 & _ & F8 & _).
  destruct V as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16).
  rewrite V2, V6, V7. subst lbs N. repeat split; try assumption.
Qed.

Lemma used_L : forall j, 0 <= j < N -> 1 <= Len (ov_X6 s) TL (sym_lcode s j) <= 15.
Proof.
  intros j Hj. pose proof (sym_codes s OP j Hj) as (A & _). destruct (op_hist _ OP) as (HL & _ & _). pose proof (N_range s OP).
  assert (NZ : arr_get (ds_dyn_ltree_fc s) (sym_lcode s j) <> 0).
  { rewrite (HL _ A). pose proof (zsum_ind_ge1 (fun i => sym_lcode s i =? sym_lcode s j) 0 (Z.to_nat (nsym s)) j ltac:(subst N; lia) (Z.eqb_refl _)).
    pose proof (zind_le1 (sym_lcode s j =? END_BLOCK)). lia. }
  exact (proj1 (tp_LDu _ TP _ A NZ)).
Qed.
Lemma used_E : 1 <= Len (ov_X6 s) TL END_BLOCK <= 15.
Proof.
  destruct (op_hist _ OP) as (HL & _ & _).
  assert (NZ : arr_get (ds_dyn_ltree_fc s) END_BLOCK <> 0).
  { rewrite (HL END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia)). rewrite Z.eqb_refl. cbn [zind].
    pose proof (zsum_nonneg (fun i => zind (sym_lcode s i =? END_BLOCK)) 0 (Z.to_nat (nsym s)) ltac:(intros; apply zind_le1)). lia. }
  exact (proj1 (tp_LDu _ TP END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia) NZ)).
Qed.
Lemma used_D : forall j, 0 <= j < N -> sym_isdist s j = true -> 1 <= Len (ov_X6 s) TD (sym_dcode s j) <= 15.
Proof.
  intros j Hj Hd. pose proof (sym_codes s OP j Hj) as (_ & _ & _ & _ & M). destruct (M Hd) as (_ & Rd & _).
  destruct (op_hist _ OP) as (_ & HD & _). pose proof (N_range s OP).
  assert (NZ : arr_get (ds_dyn_dtree_fc s) (sym_dcode s j) <> 0).
  { rewrite (HD _ Rd). pose proof (zsum_ind_ge1 (fun i => sym_isdist s i && (sym_dcode s i =? sym_dcode s j)) 0 (Z.to_nat (nsym s)) j ltac:(subst N; lia) ltac:(cbv beta; rewrite Hd, Z.eqb_refl; reflexivity)). lia. }
  exact (proj1 (tp_DDu _ TP _ Rd NZ)).
Qed.

Let X11 := hX11 (ov_X6 s) last (ov_mb s).
Let X12 := hX12 (ov_X6 s) last (ov_mb s).
Let X13 := hX13 (ov_X6 s) last (ov_mb s).

Lemma hcost_eq : hcost (ov_X6 s) (ov_mb s) = ov_hdr s.
Proof.
  unfold hcost, ov_hdr. rewrite !TDcost_cnt by (first [apply (tp_LD _ TP) | apply (tp_DD _ TP)]).
  rewrite <- Z.add_assoc, <- zsum_add. replace (3 + (5 + 5 + 4) + 3 * (ov_mb s + 1)) with (17 + 3 * (ov_mb s + 1)) by lia. f_equal.
  apply zsum_ext. intros x Hx. rewrite (tp_BC _ TP x) by lia. unfold ov_BD. rewrite <- (tree_dl_TB (ov_X6 s)), <- Len_eq. lia.
Qed.

Lemma stat_val : ds_static_len (ov_X6 s) = zsum (scost s) 0 (Z.to_nat N) + 7 /\ 0 <= zsum (scost s) 0 (Z.to_nat N) <= 31 * N.
Proof. split; [rewrite (tp_stat _ TP); apply (static_by_syms s OP) | apply (scost_sum_bound s OP)]. Qed.

Lemma dyn_total : ov_hdr s + zsum (dcost (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s)) s) 0 (Z.to_nat N)
                  + arr_get (ds_dyn_ltree_dl (ov_X6 s)) END_BLOCK <= 3 + ds_opt_len (ov_X6 s).
Proof.
  pose proof (tp_opt_ge _ TP) as G. pose proof (data_dyn s OP (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s))) as D. fold N in D.
  rewrite (zsum_ext (fun c => arr_get (ds_dyn_ltree_fc s) c * (Len (ov_X6 s) TL c + xbits TL c))
                    (fun c => arr_get (ds_dyn_ltree_fc s) c * (arr_get (ds_dyn_ltree_dl (ov_X6 s)) c + xbits TL c))) in G
    by (intros; rewrite Len_eq, tree_dl_TL; reflexivity).
  rewrite (zsum_ext (fun d => arr_get (ds_dyn_dtree_fc s) d * (Len (ov_X6 s) TD d + xbits TD d))
                    (fun d => arr_get (ds_dyn_dtree_fc s) d * (arr_get (ds_dyn_dtree_dl (ov_X6 s)) d + xbits TD d))) in G
    by (intros; rewrite Len_eq, tree_dl_TD; reflexivity).
  rewrite (zsum_ext (fun x => arr_get (ov_BC s) x * (Len (ov_X6 s) TB x + arr_get extra_blbits_a x))
                    (fun x => arr_get (ov_BC s) x * (arr_get (ds_bl_tree_dl (ov_X6 s)) x + arr_get extra_blbits_a x))) in G
    by (intros; rewrite Len_eq, tree_dl_TB; reflexivity).
  unfold ov_hdr, ov_BD.
  match goal with |- context [zsum ?f 0 19] => set (A := zsum f 0 19) in * end.
  match type of D with context [zsum ?f 0 (Z.to_nat L_CODES)] => set (B := zsum f 0 (Z.to_nat L_CODES)) in * end.
  match type of D with context [zsum ?f 0 (Z.to_nat D_CODES)] => set (C := zsum f 0 (Z.to_nat D_CODES)) in * end.
  match goal with |- context [zsum ?f 0 (Z.to_nat N)] => set (Dd := zsum f 0 (Z.to_nat N)) in * end.
  clearbody A B C Dd. lia.
Qed.
Record EMIT (y : deflate_state) : Prop := {
  em_nb : nb_view y = nb_view (ov_X6 s);
  em_W : ov_W y <= 32 * lbs - 16;
  em_bv : 0 <= ds_bi_valid y <= 16;
  em_bb : 0 <= ds_bi_buf y < 2 ^ 16;
  em_pbb : PBB y;
  em_pbl : arr_len (ds_pending_buf y) = PBL;
  em_pend : 0 <= ds_pending y;
  em_pendW : 8 * ds_pending y <= ov_W y + 7 }.

Lemma HDRs : HDR (ov_X6 s) PBL X13 (ov_hdr s)
  /\ (ds_bi_valid s + ov_hdr s <= 8 * PBL ->
      sbs_ok PBL (ov_X6 s) (hd_calls last (ov_X6 s) (ov_mb s))
      /\ send_tree_safe PBL X11 TL (ds_l_max_code (ov_X6 s)) /\ send_tree_safe PBL X12 TD (ds_d_max_code (ov_X6 s))).
Proof.
  pose proof X6n as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _). pose proof FEn as (F1 & F2 & F3 & F4 & F5 & _).
  pose proof (tp_mb _ TP) as Rmb. pose proof (tp_lmax _ TP) as RL. pose proof (tp_dmax _ TP) as RD.
  assert (Hbv : 0 <= ds_bi_valid (ov_X6 s) <= 16) by (rewrite P4; lia).
  assert (Hbb : 0 <= ds_bi_buf (ov_X6 s) < 2 ^ 16) by (rewrite P3; exact F5).
  assert (Hpbl : arr_len (ds_pending_buf (ov_X6 s)) = PBL) by (rewrite P1; exact F2).
  assert (Hpbb : PBB (ov_X6 s)) by (unfold PBB; rewrite P1; apply FEn).
  pose proof (HDR_X13 (ov_X6 s) last (ov_mb s) PBL ltac:(lia) P2 Hbv Hbb Hpbl Hpbb (tp_LD _ TP) (tp_DD _ TP) (tp_BD _ TP)) as (H13 & _ & OKs).
  pose proof (HDR_X11 (ov_X6 s) last (ov_mb s) PBL ltac:(lia) P2 Hbv Hbb Hpbl Hpbb (tp_LD _ TP) (tp_DD _ TP) (tp_BD _ TP)) as (_ & OK11).
  rewrite hcost_eq in H13, OKs, OK11. fold X13 in H13. fold X11 X12 in OKs.
  split; [exact H13|]. intros HW. rewrite P4 in OKs, OK11.
  specialize (OKs HW). split; [apply OK11; exact HW | exact OKs].
Qed.

Lemma dyn_branch : tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) = 1 ->
  OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok PBL last (ov_X6 s) (ov_mb s)
  /\ EMIT (tfb_emit 1 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last).
Proof.
  intros HB.
  pose proof X6n as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _). pose proof FEn as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  pose proof (tp_mb _ TP) as Rmb. pose proof (tp_lmax _ TP) as RL. pose proof (tp_dmax _ TP) as RD.
  pose proof (branch1_lt _ _ _ (tp_opt _ TP) (tp_stat_range _ TP) HB) as LT.
  destruct stat_val as [SV SB]. pose proof dyn_total as DT.
  destruct HDRs as [[NB13 W13 BV13 BB13 PL13 PE13 PB13 PR13] OKs].
  set (W0 := ds_bi_valid s + ov_hdr s).
  set (cost := dcost (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s)) s).
  assert (TOTALE : W0 + zsum cost 0 (Z.to_nat N) + arr_get (ds_dyn_ltree_dl (ov_X6 s)) END_BLOCK <= 8 * arr_len (ds_pending_buf s)).
  { rewrite F2. subst PBL lbs W0 cost. lia. }
  assert (HE : 0 <= arr_get (ds_dyn_ltree_dl (ov_X6 s)) END_BLOCK <= 15).
  { pose proof used_E as X. rewrite Len_eq, tree_dl_TL in X. lia. }
  assert (TOTAL : W0 + zsum cost 0 (Z.to_nat N) <= 8 * arr_len (ds_pending_buf s)) by lia.
  assert (PREFIX : forall k, 0 <= k < N -> W0 + zsum cost 0 (Z.to_nat k) <= 8 * (ds_lit_bufsize s + 3 * k)).
  { intros k Hk. pose proof (HOV s OP HB k ltac:(subst N; exact Hk)) as X. unfold ov_wpos, ov_rpos, ov_LD, ov_DD in X. subst W0 cost. lia. }
  assert (HlenL : forall j, 0 <= j < N -> 0 <= arr_get (ds_dyn_ltree_dl (ov_X6 s)) (sym_lcode s j) <= 15).
  { intros j Hj. pose proof (used_L j Hj) as X. rewrite Len_eq, tree_dl_TL in X. lia. }
  assert (HlenD : forall j, 0 <= j < N -> sym_isdist s j = true -> 0 <= arr_get (ds_dyn_dtree_dl (ov_X6 s)) (sym_dcode s j) <= 15).
  { intros j Hj Hd. pose proof (used_D j Hj Hd) as X. rewrite Len_eq, tree_dl_TD in X. lia. }
  assert (Hroom : ds_lit_bufsize s + 3 * N + 3 <= arr_len (ds_pending_buf s)) by (rewrite F2; subst PBL lbs; lia).
  pose proof (nb_view_facts _ _ NB13) as (V1 & V2 & V3 & V4 & V5 & V6 & Vfc & Vdl & _).
  assert (CB0 : CBI s (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s)) N W0 0 X13).
  { constructor.
    - pose proof (N_range s OP). subst N. lia.
    - rewrite V1. exact P5.
    - rewrite PL13. subst PBL. symmetry. exact F2.
    - rewrite V2. exact P6.
    - rewrite W13. change (zsum _ 0 (Z.to_nat 0)) with 0. subst W0. lia.
    - exact BV13.
    - exact PB13.
    - exact PE13.
    - intros i Hi. rewrite (PR13 i Hi). rewrite P1. reflexivity. }
  pose proof (compress_block_facts s (ds_dyn_ltree_fc (ov_X6 s)) (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_fc (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s)) N W0
                (proj1 (N_range s OP)) F2 Hroom (op_syms _ OP) HlenL HlenD PREFIX TOTAL HE TOTALE X13 CB0 BB13) as CBF.
  cbv zeta in CBF. destruct CBF as (WF & CBOK & CLOK & NBF & BVF & BBF & PBF & PLF & PMF & PWF & FRF).
  assert (EM : tfb_emit 1 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last
               = compress_block X13 (ds_dyn_ltree_fc (ov_X6 s)) (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_fc (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s))).
  { rewrite (emit1_eq (ov_X6 s) last (ov_mb s) ltac:(lia)). fold X13.
    rewrite <- !tree_fc_TL, <- !tree_fc_TD, <- !tree_dl_TL, <- !tree_dl_TD, !Vfc, !Vdl. reflexivity. }
  split.
  -
    assert (HW : ds_bi_valid s + ov_hdr s <= 8 * PBL).
    { subst W0. pose proof (zsum_nonneg cost 0 (Z.to_nat N) ltac:(intros j Hj; subst cost; pose proof (cost_nonneg s (ds_dyn_ltree_fc (ov_X6 s)) (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_fc (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s)) N HlenL HlenD j ltac:(lia)); exact H)).
      rewrite F2 in TOTAL. lia. }
    destruct (OKs HW) as (OK11 & OK12 & OK13').
    apply dyn_ok_intro.
    + unfold BINV. rewrite P4, P3, P2. subst PBL lbs. lia.
    + exact OK11.
    + unfold L_CODES in RL. lia.
    + unfold D_CODES in RD. lia.
    + split; intros i Hi; rewrite <- tree_dl_TB; [pose proof (tp_BD _ TP i Hi) as X; rewrite Len_eq in X; lia | apply (tp_dl6 _ TP)].
    + intros i Hi. rewrite <- tree_fc_TB. apply (tp_fc6 _ TP).
    + exact (tp_LD _ TP).
    + intros i Hi. rewrite <- tree_dl_TL. apply (tp_dl6 _ TP).
    + exact (tp_DD _ TP).
    + intros i Hi. rewrite <- tree_dl_TD. apply (tp_dl6 _ TP).
    + exact OK12.
    + exact OK13'.
    + rewrite F2 in CBOK. exact CBOK.
    + intros i Hi. rewrite <- tree_fc_TL. apply (tp_fc6 _ TP).
    + intros i Hi. rewrite <- tree_fc_TD. apply (tp_fc6 _ TP).
    + exact CLOK.
    + rewrite P6. pose proof (N_range s OP). subst N lbs. lia.
    + rewrite P5. subst lbs. lia.
  -
    rewrite EM. constructor.
    + rewrite NBF. exact NB13.
    + rewrite WF. rewrite F2 in TOTALE. subst PBL lbs W0. lia.
    + exact BVF.
    + exact BBF.
    + exact PBF.
    + rewrite PLF. subst PBL. exact F2.
    + lia.
    + lia.
Qed.
Lemma stat_branch : tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) = 0 ->
  stat_ok PBL last (ov_X6 s)
  /\ EMIT (tfb_emit 0 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last).
Proof.
  intros HB.
  pose proof X6n as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _). pose proof FEn as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  destruct stat_val as [SV SB]. pose proof (N_range s OP) as RN. fold N in RN.
  set (y0 := send_bits (ov_X6 s) (Z.shiftl STATIC_TREES 1 + last) 3).
  set (W0 := ds_bi_valid s + 3).
  set (cost := dcost static_ltree_dl static_dtree_dl s).
  assert (Ecost : forall j, cost j = scost s j) by (intros; reflexivity).
  assert (Esum : forall n, zsum cost 0 n = zsum (scost s) 0 n) by (intros; apply zsum_ext; intros; apply Ecost).
  assert (HE : 0 <= arr_get static_ltree_dl END_BLOCK <= 15) by (pose proof (static_ltree_dl_bound END_BLOCK); lia).
  assert (EEND : arr_get static_ltree_dl END_BLOCK = 7) by reflexivity.
  assert (TOTALE : W0 + zsum cost 0 (Z.to_nat N) + arr_get static_ltree_dl END_BLOCK <= 8 * arr_len (ds_pending_buf s)).
  { rewrite F2, Esum, EEND. subst PBL lbs W0. lia. }
  assert (TOTAL : W0 + zsum cost 0 (Z.to_nat N) <= 8 * arr_len (ds_pending_buf s)) by lia.
  assert (PREFIX : forall k, 0 <= k < N -> W0 + zsum cost 0 (Z.to_nat k) <= 8 * (ds_lit_bufsize s + 3 * k)).
  { intros k Hk. rewrite Esum. pose proof (zsum_bound (scost s) 0 (Z.to_nat k) 31 ltac:(lia) ltac:(intros; apply (scost_bound s OP); fold N; lia)). subst W0 lbs. lia. }
  assert (HlenL : forall j, 0 <= j < N -> 0 <= arr_get static_ltree_dl (sym_lcode s j) <= 15).
  { intros j Hj. pose proof (static_ltree_dl_bound (sym_lcode s j)). lia. }
  assert (HlenD : forall j, 0 <= j < N -> sym_isdist s j = true -> 0 <= arr_get static_dtree_dl (sym_dcode s j) <= 15).
  { intros j Hj _. pose proof (static_dtree_dl_bound (sym_dcode s j)). lia. }
  assert (Hroom : ds_lit_bufsize s + 3 * N + 3 <= arr_len (ds_pending_buf s)) by (rewrite F2; subst PBL lbs; lia).
  assert (Hbv6 : 0 <= ds_bi_valid (ov_X6 s) <= 16) by (rewrite P4; lia).
  assert (CL3 : Forall (fun c => 0 <= snd c <= 16) [(Z.shiftl STATIC_TREES 1 + last, 3)]) by (repeat constructor; cbn; lia).
  pose proof (nb_view_facts _ _ (send_bits_nb_view (ov_X6 s) (Z.shiftl STATIC_TREES 1 + last) 3)) as (V1 & V2 & V3 & V4 & V5 & V6 & Vfc & Vdl & _). fold y0 in V1, V2, V3, V4, V5, V6, Vfc, Vdl.
  assert (CB0 : CBI s static_ltree_dl static_dtree_dl N W0 0 y0).
  { constructor.
    - lia.
    - rewrite V1. exact P5.
    - subst y0. rewrite sb_pbl, P1. reflexivity.
    - rewrite V2. exact P6.
    - subst y0 W0. rewrite send_bits_W. change (zsum _ 0 (Z.to_nat 0)) with 0. unfold ov_W. rewrite P2, P4. lia.
    - subst y0. apply send_bits_biv; [exact Hbv6 | lia].
    - subst y0. apply send_bits_PBB. unfold PBB. rewrite P1. exact F12.
    - subst y0. pose proof (send_bits_pending_mono (ov_X6 s) (Z.shiftl STATIC_TREES 1 + last) 3). rewrite P2 in *. lia.
    - intros i Hi. subst y0. rewrite send_bits_frame by lia. rewrite P1. reflexivity. }
  assert (BB0 : 0 <= ds_bi_buf y0 < 2 ^ 16) by (subst y0; apply send_bits_bib; lia).
  pose proof (compress_block_facts s static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl N W0
                (proj1 RN) F2 Hroom (op_syms _ OP) HlenL HlenD PREFIX TOTAL HE TOTALE y0 CB0 BB0) as CBF.
  cbv zeta in CBF. destruct CBF as (WF & CBOK & CLOK & NBF & BVF & BBF & PBF & PLF & PMF & PWF & FRF).
  assert (EM : tfb_emit 0 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last = compress_block y0 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl) by reflexivity.
  split.
  - unfold stat_ok. split; [unfold sb_room; rewrite P2; subst PBL lbs; lia|]. split; [rewrite F2 in CBOK; exact CBOK|].
    split; [rewrite P6; subst N lbs; lia | rewrite P5; subst lbs; lia].
  - rewrite EM. constructor.
    + rewrite NBF. apply send_bits_nb_view.
    + rewrite WF, Esum, EEND. subst W0 lbs. lia.
    + exact BVF.
    + exact BBF.
    + exact PBF.
    + rewrite PLF. subst PBL. exact F2.
    + pose proof (ci_pend _ _ _ _ _ _ _ CB0). lia.
    + lia.
Qed.

Lemma sto_branch : tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) = 2 ->
  sto_ok PBL (ov_X6 s) (fb_buf s) (fb_len s) last
  /\ EMIT (tfb_emit 2 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last).
Proof.
  intros HB.
  pose proof X6n as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13). pose proof FEn as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  destruct stat_val as [SV SB]. pose proof (N_range s OP) as RN. fold N in RN.
  pose proof (fe_diff _ _ FE) as Fd. pose proof (fe_str _ _ FE) as Fs. pose proof (fe_ws _ _ FE) as Fw. pose proof (fe_wb _ _ FE) as Fwb.
  assert (Elen : fb_len s = ds_strstart s - ds_block_start s) by (unfold fb_len; apply wrap64_id; lia).
  pose proof (branch2_le (ov_X6 s) (fb_buf s) (fb_len s) (tp_opt _ TP) (tp_stat_range _ TP) ltac:(rewrite Elen; lia) HB) as [LE NB].
  assert (Hbs : 0 <= ds_block_start s).
  { unfold fb_buf in NB. destruct (Z.leb_spec 0 (ds_block_start s)); [lia | exfalso; apply NB; reflexivity]. }
  assert (Ebuf : fb_buf s = Some (ds_block_start s)).
  { unfold fb_buf. replace (0 <=? ds_block_start s) with true by (symmetry; apply Z.leb_le; lia). rewrite wrap32_id by lia. reflexivity. }
  assert (Hbv6 : 0 <= ds_bi_valid (ov_X6 s) <= 16) by (rewrite P4; lia).
  assert (Hbb6 : 0 <= ds_bi_buf (ov_X6 s) < 2 ^ 16) by (rewrite P3; exact F5).
  assert (LENB : 8 * (fb_len s + 4) <= 31 * N + 17).
  { rewrite SV in LE. clear - LE SB RN. Z.to_euclidean_division_equations. lia. }
  assert (EM : tfb_emit 2 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last = tr_stored_block (ov_X6 s) (fb_buf s) (fb_len s) last) by reflexivity.
  rewrite EM. rewrite (tr_stored_block_eq (ov_X6 s) (fb_buf s) (fb_len s) last Hbv6 Hbb6).
  pose proof (tsb_hP_range (ov_X6 s)) as HPR. rewrite P2 in HPR.
  split.
  - unfold sto_ok. split; [| intros _; exact NB].
    rewrite (tr_stored_block_eq (ov_X6 s) (fb_buf s) (fb_len s) last Hbv6 Hbb6), tsb_tail_pending. subst PBL lbs. lia.
  - unfold tsb_tail. cbv zeta. constructor; rewrite ?upd4_nb_view, ?upd4_pending, ?upd4_bi_buf, ?upd4_bi_valid, ?upd4_pending_buf.
    + reflexivity.
    + unfold ov_W. rewrite upd4_pending, upd4_bi_valid. subst lbs. lia.
    + lia.
    + lia.
    + unfold PBB. rewrite upd4_pending_buf. rewrite Ebuf, Elen.
      assert (LA : arr_len (tsb_lenA (tsb_hA (ov_X6 s) last) (tsb_hP (ov_X6 s)) (ds_strstart s - ds_block_start s)) = PBL).
      { unfold tsb_lenA. rewrite !arr_len_set, tsb_hA_len, P1. exact F2. }
      assert (BA : forall i, 0 <= i < PBL -> 0 <= arr_get (tsb_lenA (tsb_hA (ov_X6 s) last) (tsb_hP (ov_X6 s)) (ds_strstart s - ds_block_start s)) i < 256).
      { intros i Hi. unfold tsb_lenA, tsb_hA. rewrite !arr_get_set.
        repeat (destruct (_ && _); [apply wrap8_range|]).
        destruct (ds_bi_valid (ov_X6 s) <=? 5); [| destruct (ds_bi_valid (ov_X6 s) <=? 13)]; rewrite !arr_get_set;
          repeat (destruct (_ && _); [apply wrap8_range|]); rewrite P1; apply F12; rewrite F2; exact Hi. }
      destruct (negb (ds_strstart s - ds_block_start s =? 0)).
      * intros i. rewrite arr_len_blit, LA. intros Hi. rewrite arr_get_blit.
        destruct ((tsb_hP (ov_X6 s) + 1 + 1 + 1 + 1 <=? i) && (i <? tsb_hP (ov_X6 s) + 1 + 1 + 1 + 1 + Z.max 0 (ds_strstart s - ds_block_start s))) eqn:EC; cbn [andb]; [| apply BA; exact Hi].
        apply andb_prop in EC. destruct EC as [EC1 EC2]. apply Z.leb_le in EC1. apply Z.ltb_lt in EC2.
        destruct (arr_inb _ i); [| apply BA; exact Hi].
        rewrite P12. apply Fwb. clear - Hi Hbs Fs Fd Fw EC1 EC2. lia.
      * intros i. rewrite LA. apply BA.
    + destruct (negb _); [destruct (fb_buf s); rewrite ?arr_len_blit|]; unfold tsb_lenA; rewrite !arr_len_set, tsb_hA_len, P1; exact F2.
    + lia.
    + unfold ov_W. rewrite upd4_pending, upd4_bi_valid. lia.
Qed.
Lemma emit_facts :
  let d := tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) in
  EMIT (tfb_emit d (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last)
  /\ match d with
     | 0 => stat_ok PBL last (ov_X6 s)
     | 1 => OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok PBL last (ov_X6 s) (ov_mb s)
     | _ => sto_ok PBL (ov_X6 s) (fb_buf s) (fb_len s) last
     end.
Proof.
  cbv zeta. destruct (branch_cases (ov_X6 s) (fb_buf s) (fb_len s)) as [E|[E|E]]; rewrite E.
  - destruct (stat_branch E) as [A B]. split; [exact B | exact A].
  - destruct (dyn_branch E) as [A B]. split; [exact B | exact A].
  - destruct (sto_branch E) as [A B]. split; [exact B | exact A].
Qed.

Record FIN (y s8 : deflate_state) : Prop := {
  fi_nb : nb_view s8 = nb_view (init_block y);
  fi_pend : 0 <= ds_pending s8 /\ 8 * ds_pending s8 <= ov_W y + 7;
  fi_W : ov_W s8 <= ov_W y + 7;
  fi_bv : 0 <= ds_bi_valid s8 <= 16;
  fi_bv_last : last <> 0 -> ds_bi_valid s8 = 0;
  fi_bb : 0 <= ds_bi_buf s8 < 2 ^ 16;
  fi_pbl : arr_len (ds_pending_buf s8) = arr_len (ds_pending_buf y);
  fi_pbb : PBB s8 }.

Lemma fin_facts : forall y, EMIT y -> FIN y (tfb_fin last y).
Proof.
  intros y [NB WY BV BB PB PL PE PW]. unfold tfb_fin. cbv zeta.
  pose proof (init_block_facts y) as IBy. pose proof (ib_strm _ _ IBy) as Estrm. pose proof (ib_po _ _ IBy) as Epo. pose proof (ib_lbs _ _ IBy) as Elbs.
  pose proof (ib_bv _ _ IBy) as Ebv. pose proof (ib_bb _ _ IBy) as Ebb. pose proof (ib_pend _ _ IBy) as Epend. pose proof (ib_pb _ _ IBy) as Epb.
  assert (WI : ov_W (init_block y) = ov_W y) by (unfold ov_W; rewrite Epend, Ebv; reflexivity).
  assert (PBI : PBB (init_block y)) by (unfold PBB; rewrite Epb; exact PB).
  destruct (Z.eqb_spec last 0) as [L0|L0]; cbn [negb].
  - constructor.
    + reflexivity.
    + rewrite Epend. unfold ov_W in *. lia.
    + rewrite WI. lia.
    + rewrite Ebv. exact BV.
    + intros X. exfalso. exact (X L0).
    + rewrite Ebb. exact BB.
    + rewrite Epb. reflexivity.
    + exact PBI.
  - pose proof (bi_windup_facts (init_block y) ltac:(rewrite Ebv; exact BV)) as (Wnb & Wbv & Wbb & Wp1 & Wp2 & Wlen & Wfr & Wpbb).
    constructor.
    + exact Wnb.
    + rewrite WI in Wp2. rewrite Epend in Wp1. lia.
    + unfold ov_W at 1. rewrite Wbv. rewrite WI in Wp2. lia.
    + rewrite Wbv. lia.
    + intros _. exact Wbv.
    + rewrite Wbb. lia.
    + rewrite Wlen, Epb. reflexivity.
    + apply Wpbb. exact PBI.
Qed.

Lemma total_out_cset_data_type : forall c dt, cs_total_out (cset_data_type c dt) = cs_total_out c.
Proof. intros c dt; destruct c; reflexivity. Qed.
Lemma data_type_cset_data_type : forall c dt, cs_data_type (cset_data_type c dt) = dt.
Proof. intros c dt; destruct c; reflexivity. Qed.
Lemma avail_out_cset_data_type : forall c dt, cs_avail_out (cset_data_type c dt) = cs_avail_out c.
Proof. intros c dt; destruct c; reflexivity. Qed.

Lemma tree_lens_nb : forall a b, nb_view b = nb_view a -> tree_lens a -> tree_lens b.
Proof.
  intros a b E T. pose proof (nb_view_facts _ _ E) as (_ & _ & _ & _ & _ & _ & Vfc & Vdl & _ & _ & _ & _ & _ & _ & Vbc & Vhp & Vdp & _).
  unfold tree_lens in *. rewrite <- !tree_fc_TL, <- !tree_fc_TD, <- !tree_fc_TB, <- !tree_dl_TL, <- !tree_dl_TD, <- !tree_dl_TB in *.
  rewrite !Vfc, !Vdl, Vbc, Vhp, Vdp. exact T.
Qed.

Lemma set_block_start_facts : forall x v,
  ds_bi_valid (set_block_start x v) = ds_bi_valid x /\ ds_bi_buf (set_block_start x v) = ds_bi_buf x /\ ds_pending (set_block_start x v) = ds_pending x
  /\ ds_pending_out (set_block_start x v) = ds_pending_out x /\ ds_strm (set_block_start x v) = ds_strm x /\ ov_W (set_block_start x v) = ov_W x.
Proof. intros x v. unfold ov_W. destruct x; repeat split; reflexivity. Qed.

Theorem flush_facts : flush_ok s last /\ fb_post s last (tr_flush_block s (fb_buf s) (fb_len s) last).
Proof.
  pose proof X6n as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13). pose proof FEn as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  assert (EPBL : PBL = ds_lit_bufsize s * 4) by reflexivity. assert (Elbs : lbs = ds_lit_bufsize s) by reflexivity.
  pose proof emit_facts as EF. cbv zeta in EF. destruct EF as [EMy BRANCH].
  assert (EPRE : tfb_pre s (fb_buf s) (fb_len s) last = tfb_emit (tfb_branch (ov_X6 s) (fb_buf s) (fb_len s)) (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last) by (apply tfb_pre_ov; lia).
  remember (tfb_branch (ov_X6 s) (fb_buf s) (fb_len s)) as d eqn:Ed.
  remember (tfb_emit d (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last) as y eqn:Ey.
  assert (E8 : tr_flush_block s (fb_buf s) (fb_len s) last = tfb_fin last y) by (rewrite tr_flush_block_eq, EPRE; reflexivity).
  pose proof (fin_facts y EMy) as FI8.
  set (s8 := tfb_fin last y) in *.
  pose proof EMy as [NBy Wy BVy BBy PBy PLy PEy PWy]. destruct FI8 as [NB8 PE8 W8 BV8 BVL8 BB8 PL8 PB8].
  pose proof (init_block_facts y) as IBy.
  pose proof (nb_view_facts _ _ NBy) as (Vlbs & Vsn & Vpo & Vstrm & Vlev & Vstr & Vfc & Vdl & Vlm & Vdm & Vol & Vsl & Vbs & Vss & Vbc & Vhp & Vdp & Vmat & _).
  pose proof (nb_view_facts _ _ NB8) as (Wlbs & Wsn & Wpo & Wstrm & Wlev & Wstr & Wfc & Wdl & Wlm & Wdm & Wol & Wsl & Wbs & Wss & Wbc & Whp & Wdp & Wmat & _).
  pose proof (ib_strm _ _ IBy) as Istrm. pose proof (ib_po _ _ IBy) as Ipo. pose proof (ib_lbs _ _ IBy) as Ilbs.
  pose proof (ib_bv _ _ IBy) as Ibv. pose proof (ib_bb _ _ IBy) as Ibb. pose proof (ib_pend _ _ IBy) as Ipend. pose proof (ib_pb _ _ IBy) as Ipb.
  assert (TLy : tree_lens y) by (apply (tree_lens_nb (ov_X6 s)); [exact NBy | exact (tp_tl6 _ TP)]).
  assert (PP8 : 0 <= ds_pending s8 /\ ds_pending s8 + 2 <= PBL) by (lia).
  assert (SAFE : fb_safe s (fb_buf s) (fb_len s) last).
  { unfold fb_safe. cbv zeta. rewrite F2.
    split; [lia|]. split; [exact (fe_dt _ _ FE)|]. split; [lia|].
    split; [intros i Hi; rewrite <- tree_fc_TL; apply (fe_fc _ _ FE)|].
    split.
    - rewrite EPRE. unfold post_ok. split.
      + unfold BINV. lia.
      + intros HL. pose proof (bi_windup_facts (init_block y) ltac:(rewrite Ibv; exact BVy)) as (_ & _ & _ & _ & Wp2 & _).
        unfold ov_W in Wp2, Wy. rewrite Ipend, Ibv in Wp2. lia.
    - replace (0 <? ds_level s) with true by (symmetry; apply Z.ltb_lt; lia).
      apply (proj2 (hi_ok_ov _ _ _ _ _)).
      split; [exact (tp_h1 _ TP)|]. split; [exact (tp_h2 _ TP)|].
      split; [rewrite (tp_h3 _ TP); pose proof (tp_lmax _ TP); unfold L_CODES in *; lia|]. split; [exact (tp_h4 _ TP)|].
      split; [intros i _; apply (tp_h5 _ TP)|]. split; [intros i _; apply (tp_h6 _ TP)|].
      split; [rewrite (tp_h7 _ TP); pose proof (tp_dmax _ TP); unfold D_CODES in *; lia|]. split; [exact (tp_h8 _ TP)|].
      split; [intros i _; apply (tp_h9 _ TP)|]. split; [intros i _; apply (tp_h10 _ TP)|].
      split; [exact (tp_h11 _ TP)|]. split; [split; [exact (tp_h12 _ TP) | intros i _; apply (tp_h12' _ TP)]|].
      split; [exact (proj1 (tp_h13 _ TP))|]. split; [exact (proj2 (tp_h13 _ TP))|]. split; [rewrite (tp_h14 _ TP); lia|].
      rewrite <- Ed. exact BRANCH. }
  split.
  -
    unfold flush_ok. cbv zeta.
    change (if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None) with (fb_buf s).
    change (wrap64 (ds_strstart s - ds_block_start s)) with (fb_len s). rewrite E8. fold s8.
    split; [exact SAFE|]. split; [unfold BINV; lia|].
    split; [exact (fe_diff _ _ FE)|]. split; [exact (fe_bs _ _ FE)|]. split; [exact (fe_str _ _ FE)|]. split; [exact (fe_look _ _ FE)|]. split; [exact (fe_wb _ _ FE)|].
    destruct (set_block_start_facts s8 (ds_strstart s8)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (bi_flush_facts (set_block_start s8 (ds_strstart s8)) ltac:(rewrite B1; exact BV8) ltac:(rewrite B2; exact BB8)) as (Fnb & Fbv & Fbb & Fp1 & Fp2 & FW & Flen & Ffr & Fpbb).
    pose proof (nb_view_facts _ _ Fnb) as (_ & _ & Fpo & Fstrm & _).
    unfold tr_flush_bits.
    split; [unfold BINV; rewrite B1, B2, B3; lia|].
    split; [rewrite B6 in Fp2; lia|].
    split; [rewrite B6 in Fp2; rewrite B3 in Fp1; lia|].
    split; [rewrite Fpo, B4, Wpo, Ipo, Vpo, P7; lia|].
    split.
    + unfold fp_len. rewrite Fpo, B4, Wpo, Ipo, Vpo, P7. rewrite wrap32_id by (rewrite B6 in Fp2; lia).
      rewrite B6 in Fp2. destruct (Z.ltb_spec (cs_avail_out (ds_strm (bi_flush (set_block_start s8 (ds_strstart s8))))) (ds_pending (bi_flush (set_block_start s8 (ds_strstart s8))))); lia.
    + rewrite Fstrm, B5, Wstrm, Istrm, Vstrm, (tp_strm6 _ TP). destruct (tp_X0 _ TP) as (dt & EX0 & _). rewrite EX0, strm_set_strm, total_out_cset_data_type. exact (fe_tout _ _ FE).
  -
    rewrite E8. fold s8.
    constructor.
    + subst s8. rewrite <- E8. apply tfb_lz_view.
    + intros A g K. subst s8. rewrite <- E8. apply (k_tr_flush_block g K).
    + destruct (tp_X0 _ TP) as (dt & EX0 & Rdt). exists dt. rewrite Wstrm, Istrm, Vstrm, (tp_strm6 _ TP), EX0, strm_set_strm. split; [reflexivity|].
      destruct Rdt as [->|R]; [exact (fe_dt _ _ FE) | lia].
    + rewrite Wsn. apply (ib_sn _ _ IBy).
    + rewrite Wmat. apply (ib_matches _ _ IBy).
    + rewrite Wol. apply (ib_ol _ _ IBy).
    + rewrite Wsl. apply (ib_sl _ _ IBy).
    + intros c Hc. rewrite <- tree_fc_TL, Wfc, tree_fc_TL. apply (ib_L _ _ IBy TLy c Hc).
    + intros dd Hd. rewrite <- tree_fc_TD, Wfc, tree_fc_TD. apply (ib_D _ _ IBy TLy dd Hd).
    + intros bb Hb. rewrite <- tree_fc_TB, Wfc, tree_fc_TB. apply (ib_B _ _ IBy TLy bb Hb).
    + apply (tree_lens_nb (init_block y)); [exact NB8 | apply (ib_tl _ _ IBy); exact TLy].
    + intros t i. rewrite Wfc. apply (ib_fcT _ _ IBy). intros t' i'. rewrite Vfc. apply (tp_fc6 _ TP).
    + intros t i. rewrite Wdl, (ib_dl _ _ IBy), Vdl. apply (tp_dl6 _ TP).
    + intros i. rewrite Wdp, (ib_depth _ _ IBy), Vdp. apply (tp_depth6 _ TP).
    + intros i Hi. rewrite Wbc, (ib_blc _ _ IBy), Vbc. apply (tp_blc6 _ TP). exact Hi.
    + lia.
    + rewrite Wpo, Ipo, Vpo. exact P7.
    + exact BV8.
    + intros HL. rewrite (BVL8 HL). lia.
    + exact BB8.
    + rewrite PL8, PLy. reflexivity.
    + exact PB8.
Qed.

Lemma stat_W : tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) = 0 ->
  ov_W (tfb_emit 0 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last) = ds_bi_valid s + 3 + ds_static_len (ov_X6 s).
Proof.
  intros HB.
  pose proof X6n as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _). pose proof FEn as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  destruct stat_val as [SV SB]. pose proof (N_range s OP) as RN. fold N in RN.
  set (y0 := send_bits (ov_X6 s) (Z.shiftl STATIC_TREES 1 + last) 3).
  set (W0 := ds_bi_valid s + 3).
  set (cost := dcost static_ltree_dl static_dtree_dl s).
  assert (Ecost : forall j, cost j = scost s j) by (intros; reflexivity).
  assert (Esum : forall n, zsum cost 0 n = zsum (scost s) 0 n) by (intros; apply zsum_ext; intros; apply Ecost).
  assert (HE : 0 <= arr_get static_ltree_dl END_BLOCK <= 15) by (pose proof (static_ltree_dl_bound END_BLOCK); lia).
  assert (EEND : arr_get static_ltree_dl END_BLOCK = 7) by reflexivity.
  assert (TOTALE : W0 + zsum cost 0 (Z.to_nat N) + arr_get static_ltree_dl END_BLOCK <= 8 * arr_len (ds_pending_buf s)).
  { rewrite F2, Esum, EEND. subst PBL lbs W0. lia. }
  assert (TOTAL : W0 + zsum cost 0 (Z.to_nat N) <= 8 * arr_len (ds_pending_buf s)) by lia.
  assert (PREFIX : forall k, 0 <= k < N -> W0 + zsum cost 0 (Z.to_nat k) <= 8 * (ds_lit_bufsize s + 3 * k)).
  { intros k Hk. rewrite Esum. pose proof (zsum_bound (scost s) 0 (Z.to_nat k) 31 ltac:(lia) ltac:(intros; apply (scost_bound s OP); fold N; lia)). subst W0 lbs. lia. }
  assert (HlenL : forall j, 0 <= j < N -> 0 <= arr_get static_ltree_dl (sym_lcode s j) <= 15).
  { intros j Hj. pose proof (static_ltree_dl_bound (sym_lcode s j)). lia. }
  assert (HlenD : forall j, 0 <= j < N -> sym_isdist s j = true -> 0 <= arr_get static_dtree_dl (sym_dcode s j) <= 15).
  { intros j Hj _. pose proof (static_dtree_dl_bound (sym_dcode s j)). lia. }
  assert (Hroom : ds_lit_bufsize s + 3 * N + 3 <= arr_len (ds_pending_buf s)) by (rewrite F2; subst PBL lbs; lia).
  assert (Hbv6 : 0 <= ds_bi_valid (ov_X6 s) <= 16) by (rewrite P4; lia).
  pose proof (nb_view_facts _ _ (send_bits_nb_view (ov_X6 s) (Z.shiftl STATIC_TREES 1 + last) 3)) as (V1 & V2 & V3 & V4 & V5 & V6 & Vfc & Vdl & _). fold y0 in V1, V2, V3, V4, V5, V6, Vfc, Vdl.
  assert (CB0 : CBI s static_ltree_dl static_dtree_dl N W0 0 y0).
  { constructor.
    - lia.
    - rewrite V1. exact P5.
    - subst y0. rewrite sb_pbl, P1. reflexivity.
    - rewrite V2. exact P6.
    - subst y0 W0. rewrite send_bits_W. change (zsum _ 0 (Z.to_nat 0)) with 0. unfold ov_W. rewrite P2, P4. lia.
    - subst y0. apply send_bits_biv; [exact Hbv6 | lia].
    - subst y0. apply send_bits_PBB. unfold PBB. rewrite P1. exact F12.
    - subst y0. pose proof (send_bits_pending_mono (ov_X6 s) (Z.shiftl STATIC_TREES 1 + last) 3). rewrite P2 in *. lia.
    - intros i Hi. subst y0. rewrite send_bits_frame by lia. rewrite P1. reflexivity. }
  assert (BB0 : 0 <= ds_bi_buf y0 < 2 ^ 16) by (subst y0; apply send_bits_bib; lia).
  pose proof (compress_block_facts s static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl N W0
                (proj1 RN) F2 Hroom (op_syms _ OP) HlenL HlenD PREFIX TOTAL HE TOTALE y0 CB0 BB0) as CBF.
  cbv zeta in CBF. destruct CBF as (WF & _).
  assert (EM : tfb_emit 0 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last = compress_block y0 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl) by reflexivity.
  rewrite EM, WF, Esum, EEND, SV. subst W0. lia.
Qed.

Lemma dyn_W : tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) = 1 ->
  ov_W (tfb_emit 1 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last) <= ds_bi_valid s + 3 + ds_opt_len (ov_X6 s)
  /\ ds_opt_len (ov_X6 s) < ds_static_len (ov_X6 s).
Proof.
  intros HB.
  pose proof X6n as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _). pose proof FEn as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  pose proof (tp_mb _ TP) as Rmb. pose proof (tp_lmax _ TP) as RL. pose proof (tp_dmax _ TP) as RD.
  pose proof (branch1_lt _ _ _ (tp_opt _ TP) (tp_stat_range _ TP) HB) as LT.
  destruct stat_val as [SV SB]. pose proof dyn_total as DT.
  destruct HDRs as [[NB13 W13 BV13 BB13 PL13 PE13 PB13 PR13] OKs].
  set (W0 := ds_bi_valid s + ov_hdr s).
  set (cost := dcost (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s)) s).
  assert (TOTALE : W0 + zsum cost 0 (Z.to_nat N) + arr_get (ds_dyn_ltree_dl (ov_X6 s)) END_BLOCK <= 8 * arr_len (ds_pending_buf s)).
  { rewrite F2. subst PBL lbs W0 cost. lia. }
  assert (HE : 0 <= arr_get (ds_dyn_ltree_dl (ov_X6 s)) END_BLOCK <= 15).
  { pose proof used_E as X. rewrite Len_eq, tree_dl_TL in X. lia. }
  assert (TOTAL : W0 + zsum cost 0 (Z.to_nat N) <= 8 * arr_len (ds_pending_buf s)) by lia.
  assert (PREFIX : forall k, 0 <= k < N -> W0 + zsum cost 0 (Z.to_nat k) <= 8 * (ds_lit_bufsize s + 3 * k)).
  { intros k Hk. pose proof (HOV s OP HB k ltac:(subst N; exact Hk)) as X. unfold ov_wpos, ov_rpos, ov_LD, ov_DD in X. subst W0 cost. lia. }
  assert (HlenL : forall j, 0 <= j < N -> 0 <= arr_get (ds_dyn_ltree_dl (ov_X6 s)) (sym_lcode s j) <= 15).
  { intros j Hj. pose proof (used_L j Hj) as X. rewrite Len_eq, tree_dl_TL in X. lia. }
  assert (HlenD : forall j, 0 <= j < N -> sym_isdist s j = true -> 0 <= arr_get (ds_dyn_dtree_dl (ov_X6 s)) (sym_dcode s j) <= 15).
  { intros j Hj Hd. pose proof (used_D j Hj Hd) as X. rewrite Len_eq, tree_dl_TD in X. lia. }
  assert (Hroom : ds_lit_bufsize s + 3 * N + 3 <= arr_len (ds_pending_buf s)) by (rewrite F2; subst PBL lbs; lia).
  pose proof (nb_view_facts _ _ NB13) as (V1 & V2 & V3 & V4 & V5 & V6 & Vfc & Vdl & _).
  assert (CB0 : CBI s (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s)) N W0 0 X13).
  { constructor.
    - pose proof (N_range s OP). subst N. lia.
    - rewrite V1. exact P5.
    - rewrite PL13. subst PBL. symmetry. exact F2.
    - rewrite V2. exact P6.
    - rewrite W13. change (zsum _ 0 (Z.to_nat 0)) with 0. subst W0. lia.
    - exact BV13.
    - exact PB13.
    - exact PE13.
    - intros i Hi. rewrite (PR13 i Hi). rewrite P1. reflexivity. }
  pose proof (compress_block_facts s (ds_dyn_ltree_fc (ov_X6 s)) (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_fc (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s)) N W0
                (proj1 (N_range s OP)) F2 Hroom (op_syms _ OP) HlenL HlenD PREFIX TOTAL HE TOTALE X13 CB0 BB13) as CBF.
  cbv zeta in CBF. destruct CBF as (WF & _).
  assert (EM : tfb_emit 1 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last
               = compress_block X13 (ds_dyn_ltree_fc (ov_X6 s)) (ds_dyn_ltree_dl (ov_X6 s)) (ds_dyn_dtree_fc (ov_X6 s)) (ds_dyn_dtree_dl (ov_X6 s))).
  { rewrite (emit1_eq (ov_X6 s) last (ov_mb s) ltac:(lia)). fold X13.
    rewrite <- !tree_fc_TL, <- !tree_fc_TD, <- !tree_dl_TL, <- !tree_dl_TD, !Vfc, !Vdl. reflexivity. }
  split; [| exact LT]. rewrite EM, WF. subst W0 cost. lia.
Qed.

Lemma sto_W : tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) = 2 ->
  ov_W (tfb_emit 2 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last) = 8 * (tsb_hP (ov_X6 s) + 4 + fb_len s)
  /\ fb_buf s <> None.
Proof.
  intros HB.
  pose proof X6n as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13). pose proof FEn as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  pose proof (fe_diff _ _ FE) as Fd.
  assert (Elen : fb_len s = ds_strstart s - ds_block_start s) by (unfold fb_len; apply wrap64_id; lia).
  pose proof (branch2_le (ov_X6 s) (fb_buf s) (fb_len s) (tp_opt _ TP) (tp_stat_range _ TP) ltac:(rewrite Elen; lia) HB) as [LE NB].
  assert (Hbv6 : 0 <= ds_bi_valid (ov_X6 s) <= 16) by (rewrite P4; lia).
  assert (Hbb6 : 0 <= ds_bi_buf (ov_X6 s) < 2 ^ 16) by (rewrite P3; exact F5).
  assert (EM : tfb_emit 2 (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last = tr_stored_block (ov_X6 s) (fb_buf s) (fb_len s) last) by reflexivity.
  split; [| exact NB].
  rewrite EM. rewrite (tr_stored_block_eq (ov_X6 s) (fb_buf s) (fb_len s) last Hbv6 Hbb6).
  unfold tsb_tail. cbv zeta. unfold ov_W. rewrite upd4_pending, upd4_bi_valid. lia.
Qed.


End Flush.

Theorem FB_CALL_intro : OVERLAY_CORE -> FB_CALL.
Proof. intros HOV s last FE. exact (flush_facts s last FE HOV). Qed.
