(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BgPlace.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BnCall.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation ST := (bstate bptr).

Definition hpl_only (PL : placement) : Prop := pl_frames PL = [].

Lemma nil_of_no_In : forall {A} (l : list A), (forall x, ~ In x l) -> l = [].
Proof. intros A l H. destruct l as [|x l]; [reflexivity|]. exfalso. apply (H x). left. reflexivity. Qed.

Lemma hpl_only_empty : hpl_only pl_empty.
Proof. unfold hpl_only. apply pl_frames_empty. Qed.

Lemma hpl_only_set_heap : forall PL r a q off, hpl_only PL -> hpl_only (pl_set PL r (Some (PHeap a q off))).
Proof.
  intros PL r a q off H. unfold hpl_only in *. apply nil_of_no_In. intros iv Hiv. apply pl_frames_set_In in Hiv.
  destruct Hiv as [[]|Hiv]. rewrite H in Hiv. destruct Hiv.
Qed.

Lemma hpl_only_set_none : forall PL r, hpl_only PL -> hpl_only (pl_set PL r None).
Proof.
  intros PL r H. unfold hpl_only in *. apply nil_of_no_In. intros iv Hiv. apply pl_frames_set_In in Hiv.
  destruct Hiv as [[]|Hiv]. rewrite H in Hiv. destruct Hiv.
Qed.

Lemma hpl_only_set_ctx : forall PL c, hpl_only PL -> hpl_only (pl_set_ctx PL c).
Proof. intros PL c H. exact H. Qed.

Lemma xw_hpl_only : forall PL PL', hpl_only PL -> hpl_only PL' -> XW PL' = XW PL.
Proof. intros PL PL' H H'. unfold XW. rewrite H, H'. reflexivity. Qed.

Lemma refs_stable_noitems : forall (st : ST) OW st' OW', gx_items (st_ctx st) = [] -> refs_stable st OW st' OW'.
Proof.
  intros st OW st' OW' E PL i a H. apply ref_at_pool in H. destruct H as (q & H0 & Eq & _). rewrite E in Eq.
  destruct ((i / BN_CTX_POOL_SIZE)%nat); discriminate Eq.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma lib_state_err_cleared : forall s LB SPX BX (st : ST) m m' OW PL EA W,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> frames_ok PL SPX BX ->
  munch ((BnRep.ea_ES EA, BnRep.ea_ES EA + 904) :: W) m m' -> wmono bgusegs m m' -> Forall (w_okc OW LB st PL EA SPX false []) W ->
  rw_cells bgusegs m' (BnRep.ea_ES EA) [CB 904 BnRep.ES_CLEARED] -> lib_state st m' OW PL EA.
Proof.
  intros s LB SPX BX st m m' OW PL EA W HEAP LS FROK MU WM HW NEW.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (_ & _ & _ & _ & ERRB).
  pose proof ERRB as (_ & _ & _ & HinE). pose proof (RH_range _ _ _ _ _ _ _ HEAP HinE) as (EA0 & _ & _ & EAC & EAI).
  pose proof LS as (_ & (_ & (_ & _ & _ & _ & _ & _ & _ & _ & OLD)) & _).
  unfold lib_state. eapply lib_state_hc_agree; [exact LS|]. intros x Hx HO. split; [|apply WM].
  destruct (Z_lt_ge_dec x (BnRep.ea_ES EA)) as [L|G]; [|destruct (Z_lt_ge_dec x (BnRep.ea_ES EA + 904)) as [L2|G2]].
  - apply MU. unfold wa. rewrite unsigned_lit by lia. cbn [outside]. split; [lia|].
    eapply (own_fp_outside s OW LB m HEAP st PL EA SPX BX PARTS FROK); eauto.
  -
    destruct OLD as [[_ (_ & _ & BO)] _]. destruct NEW as [[_ (_ & _ & BN)] _]. cbn [cells_bytes cbytes] in BO, BN. rewrite app_nil_r in BO, BN.
    assert (LES : length BnRep.ES_CLEARED = 904%nat) by reflexivity.
    specialize (BO (Z.to_nat (x - BnRep.ea_ES EA)) ltac:(lia)). specialize (BN (Z.to_nat (x - BnRep.ea_ES EA)) ltac:(lia)).
    replace (BnRep.ea_ES EA + Z.of_nat (Z.to_nat (x - BnRep.ea_ES EA))) with x in BO, BN by lia.
    rewrite ref_mrd_overlay in BO, BN by (unfold wa; rewrite unsigned_lit by lia; lia). congruence.
  - apply MU. unfold wa. rewrite unsigned_lit by lia. cbn [outside]. split; [lia|].
    eapply (own_fp_outside s OW LB m HEAP st PL EA SPX BX PARTS FROK); eauto.
Qed.

Lemma cenv_call_raw : forall LB PL PL' lo B SPv FB s0 (bs0 : ST) OW0 m0 fr st bs m OW st' (bs' : ST) m' OW' (errv' : word),
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= FB -> FB <= SPv -> frames_ok PL SPv B ->
  XW PL' = XW PL ->
  cenv LB PL lo B SPv FB s0 bs0 OW0 m0 fr st bs m OW ->
  RHEAP st' (OW' ++ LB) m' -> rauxv_ok m' B -> stk bgusegs m' lo FB -> rw_cells bgusegs m' LX_ERRNO [C4 errv'] -> mem_inv bgusegs m' ->
  lx_pres LB FB (XW PL) m m' -> ps_fa st' = ps_fa st -> ps_so st' = ps_so st -> refs_stable bs0 OW0 bs' OW' ->
  cenv LB PL' lo B SPv FB s0 bs0 OW0 m0 fr st' bs' m' OW'.
Proof.
  intros LB PL PL' lo B SPv FB s0 bs0 OW0 m0 fr st bs m OW st' bs' m' OW' errv' CEIL GLO LOFB FBSP FROK EXW
         (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ) HEAP' AUX' ST' ERR' MI' LXP' FA' SO' RS'.
  unfold cenv. rewrite EXW. split; [exact HEAP'|]. split; [exact AUX'|]. split; [exact ST'|]. split; [exists errv'; exact ERR'|]. split; [exact MI'|].
  split. { eapply lx_pres_trans; [exact LXP|]. eapply lx_pres_weaken; [exact LXP'| exact FBSP| auto| auto]. }
  split; [congruence|]. split; [congruence|]. split; [exact RS'|]. split; [|exact FSZ].
  eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP' | exact FR |].
  intros a Ha. eapply (xw_client PL LB FB SPv B); [exact (proj1 FROK)| lia|].
  unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. unfold GLOBALS_TOP in GLO. lia.
Qed.

End WithCeiling0.

Lemma div255_magic : forall x, 0 <= x < 2^40 -> Z.shiftr (Z.shiftr (x * 9259542123273814145) 64) 7 = x / 255.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia. change (2^64 * 2^7) with (2^71).
  pose proof (Z.div_mod x 255 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 255 ltac:(lia)) as R.
  pose proof (Z.div_pos x 255 ltac:(lia) ltac:(lia)) as Q0. pose proof (Z.div_lt_upper_bound x 255 (2^40) ltac:(lia) ltac:(lia)) as Q1.
  set (q := x / 255) in *. set (r := x mod 255) in *. clearbody q r. subst x.
  symmetry. apply (Z.div_unique_pos _ _ _ (127 * q + r * 9259542123273814145)).
  - change (2^71) with 2361183241434822606848. change (2^40) with 1099511627776 in Q1. lia.
  - change (2^71) with 2361183241434822606848. lia.
Qed.

Lemma land_ones64_id : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma mulhu255_small : forall x, 0 <= x < 2^40 -> 0 <= (x * 9259542123273814145) ≫ 64 < 2^40.
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. change (2^64) with 18446744073709551616. change (2^40) with 1099511627776 in *. lia.
Qed.

Lemma split_l1_m : forall x, 0 <= x < 2^40 ->
  Z.land (Z.land ((Z.land x 18446744073709551615 * 9259542123273814145) ≫ 64) 18446744073709551615 ≪ 48) 18446744073709551615 ≫ 55
  = (x / 255) mod 512.
Proof.
  intros x Hx. rewrite (land_ones64_id x) by (change (2^64) with 18446744073709551616; change (2^40) with 1099511627776 in Hx; lia).
  pose proof (mulhu255_small x Hx) as HR. pose proof (div255_magic x Hx) as HD.
  set (h := (x * 9259542123273814145) ≫ 64) in *.
  rewrite (land_ones64_id h) by (change (2^64) with 18446744073709551616; change (2^40) with 1099511627776 in HR; lia).
  rewrite <- HD. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change (2^48) with 281474976710656. change (2^64) with 18446744073709551616. change (2^55) with 36028797018963968. change (2^7) with 128.
  clear HD. destruct HR as [H0 _]. clearbody h. Z.div_mod_to_equations. lia.
Qed.

Lemma split_q2_m : forall y k, 0 <= y < 2^30 -> 0 <= k < 256 ->
  Z.land ((Z.land (Z.land y 18446744073709551615 * k) 18446744073709551615 * 9259542123273814145) ≫ 64) 18446744073709551615 ≫ 7
  = (y * k) / 255.
Proof.
  intros y k Hy Hk.
  assert (HX : 0 <= y * k < 2^40) by (change (2^40) with 1099511627776; change (2^30) with 1073741824 in Hy; nia).
  rewrite (land_ones64_id y) by (change (2^64) with 18446744073709551616; change (2^30) with 1073741824 in Hy; lia).
  rewrite (land_ones64_id (y * k)) by (change (2^64) with 18446744073709551616; change (2^40) with 1099511627776 in HX; lia).
  pose proof (mulhu255_small (y * k) HX) as HR.
  rewrite (land_ones64_id ((y * k * 9259542123273814145) ≫ 64)) by (change (2^64) with 18446744073709551616; change (2^40) with 1099511627776 in HR; lia).
  apply div255_magic. exact HX.
Qed.

Lemma div255_le : forall y k, 0 <= y -> 0 <= k < 256 -> 0 <= (y * k) / 255 <= y.
Proof.
  intros y k Hy Hk. split; [apply Z.div_pos; nia|]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma split_l3_m : forall v, 0 <= v < 2^31 ->
  Z.land (Z.land (bv_swrap 32 v) 18446744073709551615) 511 = v mod 512.
Proof.
  intros v Hv. rewrite BnMem.bn_swrap32_small by (change (2^31) with 2147483648 in Hv; lia).
  rewrite land_ones64_id by (change (2^64) with 18446744073709551616; change (2^31) with 2147483648 in Hv; lia).
  change 511 with (Z.ones 9). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma land511_mod : forall v, 0 <= v -> Z.land v 511 = v mod 512.
Proof. intros v Hv. change 511 with (Z.ones 9). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma byte_bits : forall k, 0 <= k < 256 ->
  negb (Z.land k 1 =? 0) = Z.testbit k 0 /\ negb (Z.land k 4 =? 0) = Z.testbit k 2.
Proof.
  intros k Hk.
  assert (H : forallb (fun n => Bool.eqb (negb (Z.land (Z.of_nat n) 1 =? 0)) (Z.testbit (Z.of_nat n) 0)
                               && Bool.eqb (negb (Z.land (Z.of_nat n) 4 =? 0)) (Z.testbit (Z.of_nat n) 2)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat k) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Bool.eqb_prop in H1. apply Bool.eqb_prop in H2. split; assumption.
Qed.

Lemma byte_masks : forall k, 0 <= k < 256 -> 0 <= Z.land k 1 <= 1 /\ 0 <= Z.land k 4 <= 4.
Proof.
  intros k Hk.
  assert (H : forallb (fun n => (0 <=? Z.land (Z.of_nat n) 1) && (Z.land (Z.of_nat n) 1 <=? 1) && (0 <=? Z.land (Z.of_nat n) 4) && (Z.land (Z.of_nat n) 4 <=? 4)) (seq 0 256) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat k) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4]. lia.
Qed.

Lemma split_l1_m' : forall x, 0 <= x < 2^40 ->
  Z.land (Z.land ((x * 9259542123273814145) ≫ 64) 18446744073709551615 ≪ 48) 18446744073709551615 ≫ 55 = (x / 255) mod 512.
Proof.
  intros x Hx. rewrite <- (split_l1_m x Hx).
  rewrite (land_ones64_id x) by (change (2^64) with 18446744073709551616; change (2^40) with 1099511627776 in Hx; lia). reflexivity.
Qed.

Lemma split_q2_m' : forall y k, 0 <= y < 2^30 -> 0 <= k < 256 ->
  Z.land ((y * k * 9259542123273814145) ≫ 64) 18446744073709551615 ≫ 7 = (y * k) / 255.
Proof.
  intros y k Hy Hk. rewrite <- (split_q2_m y k Hy Hk).
  assert (HX : 0 <= y * k < 2^40) by (change (2^40) with 1099511627776; change (2^30) with 1073741824 in Hy; nia).
  rewrite (land_ones64_id y) by (change (2^64) with 18446744073709551616; change (2^30) with 1073741824 in Hy; lia).
  rewrite (land_ones64_id (y * k)) by (change (2^64) with 18446744073709551616; change (2^40) with 1099511627776 in HX; lia). reflexivity.
Qed.
