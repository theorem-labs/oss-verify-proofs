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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves BnAssoc W_rshift W_small2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_expand.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Local Ltac rs1_eq := f_equal; try unfold MallocRep.wz; repeat (rewrite unsigned_lit by lia); rewrite ?Z.shiftl_mul_pow2 by lia; lia.
Local Ltac rs1_not := f_equal; try unfold MallocRep.wz; repeat (rewrite unsigned_lit by lia); rewrite zb_lxor_ones by lia; lia.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_RSHIFT1 : Z := 0x10a044.
Definition BN_IS_ZERO : Z := 0xfde2c.
Definition BN_ZERO_EX : Z := 0xff920.
Definition BN_RSHIFT1_STACK : Z := 64.

Definition rs1_res (buf : list Z) (top : nat) : list Z := splice buf 0 (rshift_limbs (firstn top buf) 1).
Definition rs1_top (buf : list Z) (top : nat) : nat := if nth (top - 1) buf 0 =? 1 then (top - 1)%nat else top.
Definition rs1_bn (b : bignum bptr) : bignum bptr :=
  mkBN (bn_d b) (rs1_res (bn_buf b) (bn_top b)) (rs1_top (bn_buf b) (bn_top b))
       (if (rs1_top (bn_buf b) (bn_top b) =? 0)%nat then false else bn_neg b) (bn_flags b).

Definition rs1_mix (buf : list Z) (top k : nat) : list Z := firstn k buf ++ skipn k (rs1_res buf top).

Lemma wlimbs_upd : forall l (i : nat) v, (i < length l)%nat -> Arr.upd (wlimbs l) i (Z_to_bv 64 v) = wlimbs (upd l i v).
Proof.
  induction l as [|y l IH]; intros i v H; cbn [length] in H; [lia|].
  destruct i as [|i']; [reflexivity|].
  unfold wlimbs in *. cbn [map Arr.upd]. rewrite (IH i' v) by lia.
  unfold upd, splice. cbn [firstn length Nat.add skipn app map]. reflexivity.
Qed.

Lemma wlimbs_nth : forall buf (i : nat), (i < length buf)%nat -> nth_error (wlimbs buf) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i buf 0)).
Proof. intros buf i H. rewrite Nat2Z.id. unfold wlimbs. rewrite nth_error_map. rewrite (nth_error_nth' buf 0) by lia. reflexivity. Qed.

Lemma rshift_limbs_length1 : forall f rb, length (rshift_limbs f rb) = length f.
Proof. intros f rb. rewrite rshift_limbs_seq, length_map, length_seq. reflexivity. Qed.

Lemma rshift_limbs_nth : forall f rb k, (k < length f)%nat -> nth k (rshift_limbs f rb) 0 = rsh_at f rb k.
Proof.
  intros f rb k Hk. rewrite rshift_limbs_seq.
  rewrite (nth_indep _ 0 (rsh_at f rb 0%nat)) by (rewrite length_map, length_seq; exact Hk).
  rewrite (map_nth (rsh_at f rb) (seq 0 (length f)) 0%nat k). rewrite seq_nth by exact Hk. reflexivity.
Qed.

Lemma rs1_res_length : forall buf top, (top <= length buf)%nat -> length (rs1_res buf top) = length buf.
Proof. intros buf top H. unfold rs1_res. apply splice_length. rewrite rshift_limbs_length1, firstn_length_le by exact H. lia. Qed.

Lemma rs1_res_limbs : forall buf top, limbs buf -> limbs (rs1_res buf top).
Proof.
  intros buf top H. unfold rs1_res. apply splice_limbs; [exact H|].
  exact (proj1 (rshift_limbs_spec (firstn top buf) 1 (limbs_firstn _ _ H) ltac:(lia))).
Qed.

Lemma rs1_res_nth_lo : forall buf top k, (top <= length buf)%nat -> (k < top)%nat -> nth k (rs1_res buf top) 0 = rsh_at (firstn top buf) 1 k.
Proof.
  intros buf top k HT Hk. unfold rs1_res, splice. rewrite firstn_O. cbn [app Nat.add].
  rewrite app_nth1 by (rewrite rshift_limbs_length1, firstn_length_le; lia). apply rshift_limbs_nth. rewrite firstn_length_le; lia.
Qed.

Lemma rs1_res_mid : forall buf top k, (top <= length buf)%nat -> (S k < top)%nat ->
  nth k (rs1_res buf top) 0 = Z.lor (shlw (nth (S k) buf 0) 63) (shrw (nth k buf 0) 1).
Proof.
  intros buf top k HT Hk. rewrite rs1_res_nth_lo by lia. rewrite rsh_at_mid by (rewrite firstn_length_le; lia).
  cbn [Z.eqb]. change (64 - 1) with 63. rewrite !nth_firstn. rewrite !(proj2 (Nat.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma rs1_res_last : forall buf top, (top <= length buf)%nat -> (0 < top)%nat ->
  nth (top - 1) (rs1_res buf top) 0 = shrw (nth (top - 1) buf 0) 1.
Proof.
  intros buf top HT Hk. rewrite rs1_res_nth_lo by lia. rewrite rsh_at_last by (rewrite firstn_length_le; lia).
  rewrite nth_firstn. rewrite (proj2 (Nat.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma rs1_mix_length : forall buf top k, (top <= length buf)%nat -> (k <= length buf)%nat -> length (rs1_mix buf top k) = length buf.
Proof. intros buf top k HT Hk. unfold rs1_mix. rewrite length_app, firstn_length_le, length_skipn, rs1_res_length by lia. lia. Qed.

Lemma rs1_mix_nth_lo : forall buf top k i, (top <= length buf)%nat -> (k <= length buf)%nat -> (i < k)%nat -> nth i (rs1_mix buf top k) 0 = nth i buf 0.
Proof. intros buf top k i HT Hk Hi. unfold rs1_mix. rewrite app_nth1 by (rewrite firstn_length_le; lia). rewrite nth_firstn. rewrite (proj2 (Nat.ltb_lt _ _)) by lia. reflexivity. Qed.

Lemma skipn_nth_cons : forall (l : list Z) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k d H; cbn [length] in H; [lia|].
  destruct k as [|k']; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma rs1_mix_step : forall buf top k, (top <= length buf)%nat -> (k < length buf)%nat ->
  upd (rs1_mix buf top (S k)) k (nth k (rs1_res buf top) 0) = rs1_mix buf top k.
Proof.
  intros buf top k HT Hk. unfold rs1_mix, upd, splice. cbn [length Nat.add].
  assert (L1 : length (firstn (S k) buf) = S k) by (apply firstn_length_le; lia).
  rewrite firstn_app, L1. replace (k - S k)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
  rewrite firstn_firstn, Nat.min_l by lia.
  rewrite skipn_app, L1. replace (k + 1 - S k)%nat with 0%nat by lia. rewrite skipn_O.
  rewrite (skipn_all2 (firstn (S k) buf)) by (rewrite L1; lia). cbn [app].
  rewrite (skipn_nth_cons (rs1_res buf top) k 0) by (rewrite rs1_res_length; lia). reflexivity.
Qed.

Lemma rs1_mix_init : forall buf top, (top <= length buf)%nat -> (0 < top)%nat ->
  upd buf (top - 1) (shrw (nth (top - 1) buf 0) 1) = rs1_mix buf top (top - 1).
Proof.
  intros buf top HT H0. rewrite <- rs1_res_last by lia.
  replace buf with (rs1_mix buf top top) at 1.
  - replace top with (S (top - 1)) at 2 by lia. apply rs1_mix_step; lia.
  - unfold rs1_mix. unfold rs1_res, splice. rewrite firstn_O. cbn [app Nat.add].
    rewrite rshift_limbs_length1, firstn_length_le by lia.
    rewrite skipn_app, rshift_limbs_length1, firstn_length_le, Nat.sub_diag, skipn_O by lia.
    rewrite (skipn_all2 (rshift_limbs _ _)) by (rewrite rshift_limbs_length1, firstn_length_le; lia). cbn [app]. apply firstn_skipn.
Qed.

Lemma rs1_mix_0 : forall buf top, rs1_mix buf top 0 = rs1_res buf top.
Proof. intros. unfold rs1_mix. rewrite firstn_O, skipn_O. reflexivity. Qed.

Lemma rs1_or_machine : forall t t', 0 <= t < 18446744073709551616 -> 0 <= t' < 18446744073709551616 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 t)) 63))) (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 t')) 1))))
  = Z_to_bv 64 (Z.lor (shlw t 63) (shrw t' 1)).
Proof.
  intros t t' Ht Ht'. rewrite (unsigned_lit t), (unsigned_lit t') by lia. f_equal. f_equal.
  - rewrite unsigned_lit_wrap. unfold shlw. rewrite Z.shiftl_mul_pow2, BW_lit by lia. reflexivity.
  - unfold shrw. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. apply unsigned_lit. lia.
Qed.

Lemma rs1_shr_machine : forall t, 0 <= t < 18446744073709551616 -> Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 t)) 1) = Z_to_bv 64 (shrw t 1).
Proof. intros t Ht. rewrite (unsigned_lit t) by lia. unfold shrw. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma rs1_top_machine : forall t top, 0 <= t < 18446744073709551616 -> 1 <= top < 2147483648 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 top) - bv_unsigned (v_sltiu (Z_to_bv 64 (t + -1)) 1)))
  = Z_to_bv 64 (if t =? 1 then top - 1 else top).
Proof.
  intros t top Ht Htop. rewrite v_sltiu_b2z. rewrite (unsigned_lit top) by lia. change (bv_wrap 64 1) with 1.
  rewrite (unsigned_lit_wrap (t + -1)).
  replace (bv_unsigned (Z_to_bv 64 (Z.b2z ((t + -1) mod 2 ^ 64 <? 1)))) with (if t =? 1 then 1 else 0).
  - destruct (Z.eqb_spec t 1); rewrite bn_swrap32_small by lia; f_equal; lia.
  - destruct (Z.eqb_spec t 1) as [->|Nt].
    + change ((1 + -1) mod 2 ^ 64 <? 1) with true. cbn [Z.b2z]. rewrite unsigned_lit by lia. reflexivity.
    + destruct (Z.ltb_spec ((t + -1) mod 2 ^ 64) 1) as [Hl|Hl]; [exfalso; Z.div_mod_to_equations; lia|]. cbn [Z.b2z]. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma rs1_top_Z : forall buf top, (0 < top)%nat ->
  Z.of_nat (rs1_top buf top) = if nth (top - 1) buf 0 =? 1 then Z.of_nat top - 1 else Z.of_nat top.
Proof. intros buf top H. unfold rs1_top. destruct (nth (top - 1) buf 0 =? 1); lia. Qed.

Lemma rs1_top_le : forall buf top, (rs1_top buf top <= top)%nat.
Proof. intros buf top. unfold rs1_top. destruct (nth (top - 1) buf 0 =? 1); lia. Qed.

Lemma rs1_body : forall (Q : machine_state -> Prop) (buf : list Z) (top : nat) (D : Z) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x13 x18 x19 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (k : nat) (m1 : mem),
  limbs buf -> (top <= length buf)%nat -> (k + 2 <= top)%nat -> Z.of_nat (length buf) < 2 ^ 31 -> 8 <= D ->
  D + 8 * Z.of_nat (length buf) < 2 ^ 64 ->
  u64arr bgusegs m1 D (wlimbs (rs1_mix buf top (S k))) -> mem_inv bgusegs m1 ->
  (forall (m' : mem) (y6 : word),
      u64arr bgusegs m' D (wlimbs (rs1_mix buf top k)) -> munch [(D + 8 * Z.of_nat k, D + 8 * Z.of_nat k + 8)] m1 m' -> wmono bgusegs m1 m' -> mem_inv bgusegs m' ->
      evt bgusegs Q (MS (mkR x1 x2 gp tp (Z_to_bv 64 (nth k buf 0)) y6 x7 x8 x9 (Z_to_bv 64 (D + 8 * (Z.of_nat k - 1))) (Z_to_bv 64 (Z.of_nat k + 1))
                              (Z_to_bv 64 (8 * (Z.of_nat k - 1))) x13 (Z_to_bv 64 (2 ^ 64 - 1 - D)) (Z_to_bv 64 (2 ^ 64 - 1 - D)) (Z_to_bv 64 (nth k buf 0)) (Z_to_bv 64 1)
                              x18 x19 (Z_to_bv 64 (D + 8 * (Z.of_nat k - 1))) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x10a1b8) fc None m' (seg_rom bgusegs))) ->
  evt bgusegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (D + 8 * Z.of_nat k)) (Z_to_bv 64 (Z.of_nat k + 2))
                          (Z_to_bv 64 (8 * Z.of_nat k)) x13 (Z_to_bv 64 (2 ^ 64 - 1 - D)) (Z_to_bv 64 (2 ^ 64 - 1 - D)) (Z_to_bv 64 (nth (S k) buf 0)) (Z_to_bv 64 1)
                          x18 x19 (Z_to_bv 64 (D + 8 * Z.of_nat k)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x10a188) fc None m1 (seg_rom bgusegs)).
Proof.
  intros Q buf top D F fc x1 x2 gp tp x5 x6 x7 x8 x9 x13 x18 x19 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 k m1 LB HT HK L31 D8 DC U MI K.
  pose proof (u64arr_bound bgusegs _ _ _ U) as UB. rewrite wlimbs_len, rs1_mix_length in UB by lia.
  assert (LM : Z.of_nat (length (wlimbs (rs1_mix buf top (S k)))) = Z.of_nat (length buf)) by (rewrite wlimbs_len, rs1_mix_length by lia; reflexivity).
  pose proof (limbs_nth buf k LB) as Lk. pose proof (limbs_nth buf (S k) LB) as LSk. unfold limb in Lk, LSk. rewrite BW_lit in Lk, LSk.
  assert (NTH : nth_error (wlimbs (rs1_mix buf top (S k))) (Z.to_nat (Z.of_nat k)) = Some (Z_to_bv 64 (nth k buf 0))).
  { rewrite <- (rs1_mix_nth_lo buf top (S k) k) by lia. apply wlimbs_nth. rewrite rs1_mix_length; lia. }
  pose proof (u64arr_read bgusegs m1 D _ (Z.of_nat k) _ (wa (D + 8 * Z.of_nat k)) U NTH ltac:(lia) eq_refl) as RD.
  pose proof (munch_refl [(D + 8 * Z.of_nat k, D + 8 * Z.of_nat k + 8)] m1) as MU. pose proof (wmono_refl bgusegs m1) as WM.
  ub_chk. ub_chk.
  step. clear RD. do 5 step. rewrite rs1_or_machine by lia. rewrite <- (rs1_res_mid buf top k) by lia.
  assert (IDX : 0 <= Z.of_nat k < Z.of_nat (length (wlimbs (rs1_mix buf top (S k))))) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u64arr_store_ok bgusegs mx D _ (Z.of_nat k) (wa (D + 8 * Z.of_nat k)) U IDX eq_refl) as SOKW;
    pose proof (u64arr_write bgusegs mx D _ (Z.of_nat k) (Z_to_bv 64 (nth k (rs1_res buf top) 0)) U IDX) as U2 end.
  rewrite Nat2Z.id, wlimbs_upd, rs1_mix_step in U2 by (rewrite ?rs1_mix_length; lia).
  clear U. step. store_done.
  step. step. step.
  setreg 10%Z (Z_to_bv 64 (D + 8 * (Z.of_nat k - 1))) ltac:(f_equal; lia).
  setreg 11%Z (Z_to_bv 64 (Z.of_nat k + 1)) ltac:(f_equal; lia).
  setreg 12%Z (Z_to_bv 64 (8 * (Z.of_nat k - 1))) ltac:(f_equal; lia).
  setreg 20%Z (Z_to_bv 64 (D + 8 * (Z.of_nat k - 1))) ltac:(f_equal; lia).
  eapply K; [exact U2 | exact MU | assumption | assumption].
Qed.

Lemma rs1_loop : forall (Q : machine_state -> Prop) (buf : list Z) (top : nat) (D : Z) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 gp tp x7 x8 x9 x13 x18 x19 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (k : nat) (m1 : mem) (x5 x6 : word),
  limbs buf -> (top <= length buf)%nat -> (k + 2 <= top)%nat -> Z.of_nat (length buf) < 2 ^ 31 -> 8 <= D ->
  D + 8 * Z.of_nat (length buf) < 2 ^ 64 ->
  u64arr bgusegs m1 D (wlimbs (rs1_mix buf top (S k))) -> mem_inv bgusegs m1 ->
  (forall (m' : mem) (y6 : word),
      u64arr bgusegs m' D (wlimbs (rs1_res buf top)) -> munch [(D, D + 8 * (Z.of_nat k + 1))] m1 m' -> wmono bgusegs m1 m' -> mem_inv bgusegs m' ->
      evt bgusegs Q (MS (mkR x1 x2 gp tp (Z_to_bv 64 (nth 0 buf 0)) y6 x7 x8 x9 (Z_to_bv 64 (D - 8)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) x13
                              (Z_to_bv 64 (2 ^ 64 - 1 - D)) (Z_to_bv 64 (2 ^ 64 - 1 - D)) (Z_to_bv 64 (nth 0 buf 0)) (Z_to_bv 64 1) x18 x19 (Z_to_bv 64 (D - 8))
                              s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x10a1bc) fc None m' (seg_rom bgusegs))) ->
  evt bgusegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (D + 8 * Z.of_nat k)) (Z_to_bv 64 (Z.of_nat k + 2))
                          (Z_to_bv 64 (8 * Z.of_nat k)) x13 (Z_to_bv 64 (2 ^ 64 - 1 - D)) (Z_to_bv 64 (2 ^ 64 - 1 - D)) (Z_to_bv 64 (nth (S k) buf 0)) (Z_to_bv 64 1)
                          x18 x19 (Z_to_bv 64 (D + 8 * Z.of_nat k)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x10a188) fc None m1 (seg_rom bgusegs)).
Proof.
  intros Q buf top D F fc x1 x2 gp tp x7 x8 x9 x13 x18 x19 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 k.
  induction k as [|k IH]; intros m1 x5 x6 LB HT HK L31 D8 DC U MI K.
  - eapply rs1_body; [exact LB| exact HT| exact HK| exact L31| exact D8| exact DC| exact U| exact MI|].
    intros m' y6 U' MU' WM' MI'.
    pose proof (u64arr_bound bgusegs _ _ _ U') as UB. rewrite wlimbs_len, rs1_mix_length in UB by lia.
    step. if_cases KE; zify_cond KE; [exfalso; rewrite ?unsigned_lit in KE by lia; lia|]. clear KE.
    setreg 10%Z (Z_to_bv 64 (D - 8)) ltac:(f_equal; lia). setreg 11%Z (Z_to_bv 64 1) ltac:(f_equal; lia).
    setreg 12%Z (Z_to_bv 64 (-8)) ltac:(f_equal; lia). setreg 20%Z (Z_to_bv 64 (D - 8)) ltac:(f_equal; lia).
    rewrite rs1_mix_0 in U'. eapply K; [exact U'| | exact WM'| exact MI'].
    eapply munch_weaken; [| exact MU']. unfold sub_fp. cbn [outside]. intros x Hx. lia.
  - eapply rs1_body; [exact LB| exact HT| exact HK| exact L31| exact D8| exact DC| exact U| exact MI|].
    intros m' y6 U' MU' WM' MI'.
    pose proof (u64arr_bound bgusegs _ _ _ U') as UB. rewrite wlimbs_len, rs1_mix_length in UB by lia.
    step. if_cases KE; zify_cond KE; [| exfalso; rewrite ?unsigned_lit in KE by lia; lia]. clear KE.
    setreg 10%Z (Z_to_bv 64 (D + 8 * Z.of_nat k)) ltac:(f_equal; lia). setreg 11%Z (Z_to_bv 64 (Z.of_nat k + 2)) ltac:(f_equal; lia).
    setreg 12%Z (Z_to_bv 64 (8 * Z.of_nat k)) ltac:(f_equal; lia). setreg 20%Z (Z_to_bv 64 (D + 8 * Z.of_nat k)) ltac:(f_equal; lia).
    eapply (IH m'); [exact LB| exact HT| lia| exact L31| exact D8| exact DC| exact U'| exact MI'|].
    intros m'' z6 U'' MU'' WM'' MI''. eapply K; [exact U''| | eapply wmono_trans; [exact WM'| exact WM'']| exact MI''].
    eapply munch_trans; [eapply munch_weaken; [| exact MU']| eapply munch_weaken; [| exact MU'']]; unfold sub_fp; cbn [outside]; intros x Hx; lia.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_rshift1_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx : bnref) (ax : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_RSHIFT1_STACK -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz ax ->
    implM bgusegs (interp (embed (BN_rshift1 (tree_ops bptr) rx rx bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RSHIFT1) fc None m (seg_rom bgusegs)).
  Proof.
    intros until ax. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAx WRx -> ->. pose proof (proj1 WRx) as NROx.
    unfold BN_RSHIFT1_STACK, BN_RSHIFT1, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (lib_state_open [] bs m OW PL EA rx ax LS ND HAx ltac:(intros []) NROx) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & LSH).
    destruct (bn_arr_facts s OW LB m HEAP bs PL EA _ _ PARTS FROK rx Dx ltac:(eapply ref_at_valid; [exact LS| exact HAx]) NROx ARRx) as (Ux & LENx & Dx0 & DxC & DxI & DSEPx).
    set (bx := getbn rx bs) in *.
    pose proof (DSEPx rx ax HAx) as SEPxx.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAx NROx) as (XA0 & XAC & XAI).
    assert (ALX : 0 < ax /\ ax mod 8 = 0) by (eapply ref_at_ualign; [exact HEAP| exact PARTS| exact HAx| exact NROx]). destruct ALX as (AX0 & AX8).
    pose proof alloc_ceiling_range as ACR.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
    unfold bn_cells in BNx. unfold BG_DMAX in OKx3.
    assert (LBX : length (bn_buf bx) = bn_dmax bx) by reflexivity.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    unfold BN_rshift1, BN_zero, bbind, bget, bset, bret. rewrite Nat.eqb_refl. cbn [bind ret tree_ops tbind fst snd]. fold bx.
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 7 step. step.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOKh : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).

    assert (EPI : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word)
                         (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
      RHEAP st1 (OW2 ++ LB) m2 -> lib_state bs1 m2 OW2 PL EA -> rauxv_ok m2 B -> stk bgusegs m2 lo (bv_unsigned sp + -48) ->
      rw_cells bgusegs m2 3346164 [C4 errv2] -> mem_inv bgusegs m2 -> lx_pres LB (bv_unsigned sp) (XW PL) m m2 ->
      ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW2 ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW2) ->
      rw_cells bgusegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      implM bgusegs (interp (embed (TRet (tt, bs1)))) st1
        (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                 (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x10a1c8) fc None m2 (seg_rom bgusegs))).
    { intros st1 bs1 m2 OW2 errv2 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31
             HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RST2 BST FR2.
      clear BNx ARRx Ux MU WM ST ERR MI FR HWL WOKh LSH.
      cbn [embed interp]. apply implM_ret.
      do 6 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
      apply evt_done.
      unfold bn_post. do 15 eexists. exists m2, OW2, PL, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact HEAP2|]. split; [exact LS2|]. split; [exact AUX2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|].
      split; [exact LXP2|]. split; [exact FA2|]. split; [exact SO2|]. split; [exact RST2|].
      split; [reflexivity|]. split; [reflexivity| exact BST]. }

    step. step. step. step.
    eapply evt_cut.
    { eapply BgBnU.W_small2.BN_is_zero_spec with (lo := lo) (A := ax) (D := Dx) (b := bx);
        [exact BNx | exact (conj AX0 AX8) | lia | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; lia | reflexivity]. }
    intros ms' PO. unfold BgBnU.W_small.bn_small_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc & ->).
    subst ms'. rewrite ESP in *.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    eapply (rw_cells_transport bgusegs _ _ m2) in FR; [| exact MUc | exact WMc | cbn; lia].
    eapply (rw_cells_transport bgusegs _ _ m2) in ERR; [| exact MUc | exact WMc | cbn; lia].
    eapply (rw_cells_transport bgusegs _ _ m2) in BNx; [| exact MUc | exact WMc | cbn; lia].
    eapply (u64arr_transport bgusegs _ _ m2) in Ux; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite wlimbs_len; fold (bn_dmax bx); lia].
    assert (MU2 : munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m2).
    { eapply munch_trans; [eapply munch_weaken; [|exact MU]| eapply munch_weaken; [|exact MUc]]; unfold sub_fp; intros x Hx; cbn [outside] in *; lia. }
    assert (WM2 : wmono bgusegs m m2) by (eapply wmono_trans; [exact WM| exact WMc]).
    clear ST MI MU WM MUc WMc.
    destruct (bn_top bx =? 0)%nat eqn:ET; step; if_cases KT; zify_cond KT; try (exfalso; rewrite ?unsigned_lit in KT by lia; cbn in KT; lia).
    -
      apply Nat.eqb_eq in ET. clear KT.
      step. step.
      eapply evt_cut.
      { eapply BgBnU.W_rshift.BN_zero_ex_spec with (lo := lo) (A := ax) (D := Dx) (b := bx);
          [exact BNx | exact (conj AX0 AX8) | rewrite ESP; exact STc | rewrite ESP; lia | exact MIc | rewrite ESP; lia | reflexivity]. }
      intros ms' PO. unfold BgBnU.W_small.bn_small_post in PO.
      destruct PO as (u0' & u1' & u2' & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3' & u4' & u5' & u6' & m3 & E & MUc & WMc & MI3 & ST3 & BNz).
      subst ms'. rewrite ESP in *.
      lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
      eapply (rw_cells_transport bgusegs _ _ m3) in FR; [| exact MUc | exact WMc | cbn; lia].
      eapply (rw_cells_transport bgusegs _ _ m3) in ERR; [| exact MUc | exact WMc | cbn; lia].
      eapply (u64arr_transport bgusegs _ _ m3) in Ux; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite wlimbs_len; fold (bn_dmax bx); lia].
      clear STc MIc BNx.
      step. step.
      assert (MUT : munch [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24)]%Z m m3).
      { eapply munch_trans; [eapply munch_weaken; [|exact MU2]| eapply munch_weaken; [|exact MUc]]; unfold sub_fp; intros x Hx; cbn [outside] in *; lia. }
      assert (WMT : wmono bgusegs m m3) by (eapply wmono_trans; [exact WM2| exact WMc]).
      assert (HWLT : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24)]).
      { constructor; [left; cbn; lia|]. constructor; [right; right; exists rx, ax; split; [exact HAx|]; split; [exact NROx|]; cbn; lia| constructor]. }
      assert (WOKc : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24)]).
      { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW LB bs PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx| exact NROx| cbn; lia| cbn; lia]| constructor]. }
      ihere. to_implM. fold bx.
      eapply (EPI s (setbn rx (bn_zero_pure bx) bs) m3 OW errv);
        [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUT WMT HWLT CEIL)
        | | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MUT WMT HWLT SPB ltac:(lia)); unfold GLOBALS_TOP; lia
        | exact ST3 | exact ERR | exact MI3
        | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUT WMT HWLT CEIL); unfold GLOBALS_TOP; lia
        | reflexivity | reflexivity | apply refs_stable_setbn
        | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR ].
      unfold lib_state. eapply (lib_state_close [] bs m3 OW PL EA rx ax); [| exact ND| exact HAx| exact NROx| | |].
      + exact (lib_state_frame s LB _ _ [rx] bs m m3 OW PL EA _ HEAP LSH MUT WMT FROK WOKc).
      + exists Dx. split; [exact BNz|]. unfold bn_zero_pure. eapply bn_arr_of_u64arr; [exact ARRx|]. cbn [bn_buf]. exact Ux.
      + unfold bg_ok, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKx1|]. split; [lia|]. split; [unfold BG_DMAX; exact OKx3| exact OKx4].
      + apply ids_ok_setbn_same; [exact IDS| exact HVx| reflexivity].
    -
      apply Nat.eqb_neq in ET. clear KT.

      assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx, 8 * Z.of_nat (bn_dmax bx)) OW).
      { pose proof ARRx as ARRx'. unfold bn_arr in ARRx'. destruct (bn_d bx) as [px|] eqn:Edx0; [exists px; split; [reflexivity| exact (proj1 ARRx')]|].
        exfalso. destruct (bn_arr_null PL rx m OW Dx bx PWF WRx Edx0 ARRx) as [_ E0]. unfold bn_dmax in OKx2. rewrite E0 in OKx2. cbn in OKx2. lia. }
      destruct HDx as (px & Edx & Hinpx).

      assert (MU3 : munch [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m m2).
      { eapply munch_weaken; [| exact MU2]. unfold sub_fp; intros x Hx; cbn [outside] in *; lia. }
      clear MU2. rename WM2 into WM3.
      pose proof (limbs_nth (bn_buf bx) (bn_top bx - 1) OKx1) as LT. unfold limb in LT. rewrite BW_lit in LT.
      set (t := nth (bn_top bx - 1) (bn_buf bx) 0) in *.

      assert (ALD : 0 < Dx /\ Dx mod 8 = 0) by (eapply block_ualign; [exact HEAP| exact Hinpx]). destruct ALD as (DX0 & DX8).
      pose proof (RH_range _ _ _ _ _ _ _ HEAP Hinpx) as (BA0 & BA16 & _ & BAC & BAI).
      ub_chk. step. ub_chk.
      step. step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
      step. if_cases KE; zify_cond KE; [| exfalso; rewrite ?unsigned_lit in KE by lia; lia]. clear KE.

      step. step. ub_chk. ub_chk.
      step. step. setreg 11%Z (Z_to_bv 64 (Z.of_nat (bn_top bx) - 1)) ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat (bn_top bx))) by lia; rewrite bn_swrap32_small by lia; lia).
      step. ub_chk.
      step. setreg 12%Z (Z_to_bv 64 (8 * (Z.of_nat (bn_top bx) - 1))) ltac:(rs1_eq).
      step. setreg 13%Z (Z_to_bv 64 (Dx + 8 * (Z.of_nat (bn_top bx) - 1))) ltac:(rs1_eq).
      step. step. ub_chk. do 4 step. ub_chk. ub_chk. step. ub_chk.
      step. setreg 14%Z (Z_to_bv 64 (Dx + 8 * (Z.of_nat (bn_top bx) - 1))) ltac:(rs1_eq).
      step. step. ub_chk. do 3 step. ub_chk. ub_chk. step. ub_chk.
      assert (NTH : nth_error (wlimbs (bn_buf bx)) (Z.to_nat (Z.of_nat (bn_top bx) - 1)) = Some (Z_to_bv 64 t)).
      { replace (Z.of_nat (bn_top bx) - 1) with (Z.of_nat (bn_top bx - 1)) by lia. apply wlimbs_nth. unfold bn_dmax in OKx2. lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (u64arr_read bgusegs mx Dx (wlimbs (bn_buf bx)) (Z.of_nat (bn_top bx) - 1) (Z_to_bv 64 t) (wa (Dx + 8 * (Z.of_nat (bn_top bx) - 1))) Ux NTH ltac:(lia) eq_refl) as RD end.
      step. clear RD.
      step. rewrite rs1_shr_machine by lia.
      assert (IDX : 0 <= Z.of_nat (bn_top bx) - 1 < Z.of_nat (length (wlimbs (bn_buf bx)))) by (rewrite LENx; unfold bn_dmax in OKx2; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (u64arr_store_ok bgusegs mx Dx _ (Z.of_nat (bn_top bx) - 1) (wa (Dx + 8 * (Z.of_nat (bn_top bx) - 1))) Ux IDX eq_refl) as SOKW;
        pose proof (u64arr_write bgusegs mx Dx _ (Z.of_nat (bn_top bx) - 1) (Z_to_bv 64 (shrw t 1)) Ux IDX) as U2 end.
      replace (Z.to_nat (Z.of_nat (bn_top bx) - 1)) with (bn_top bx - 1)%nat in U2 by lia.
      rewrite wlimbs_upd in U2 by (rewrite LBX; unfold bn_dmax in OKx2; lia).
      replace (upd (bn_buf bx) (bn_top bx - 1) (shrw t 1)) with (rs1_mix (bn_buf bx) (bn_top bx) (bn_top bx - 1)) in U2
        by (unfold t; symmetry; apply rs1_mix_init; unfold bn_dmax in OKx2; lia).
      assert (LM1 : Z.of_nat (length (wlimbs (rs1_mix (bn_buf bx) (bn_top bx) (bn_top bx - 1)))) = Z.of_nat (bn_dmax bx)).
      { rewrite wlimbs_len, rs1_mix_length, LBX by (rewrite ?LBX; unfold bn_dmax in OKx2; lia). reflexivity. }
      clear Ux. step. store_done.

      step. step. step. rewrite rs1_top_machine, <- (rs1_top_Z (bn_buf bx) (bn_top bx)) by lia.
      pose proof (rs1_top_le (bn_buf bx) (bn_top bx)) as TLE.
      step.

      lazymatch goal with |- evt _ ?Q _ =>
      assert (TAIL : forall (m3 : mem) (y5 y6 y10 y11 y12 y14 y15 y16 y17 y20 : word),
        u64arr bgusegs m3 Dx (wlimbs (rs1_res (bn_buf bx) (bn_top bx))) ->
        rw_cells bgusegs m3 ax [C8 (wz Dx); C4 (Z_to_bv 64 (Z.of_nat (rs1_top (bn_buf bx) (bn_top bx)))); C4 (wz (Z.of_nat (bn_dmax bx)));
                                C4 (wz (Z.b2z (bn_neg bx))); C4 (wz (bn_flags bx))] ->
        rw_cells bgusegs m3 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells bgusegs m3 3346164 [C4 errv] -> stk bgusegs m3 lo (bv_unsigned sp + -48) -> mem_inv bgusegs m3 ->
        munch [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m m3 -> wmono bgusegs m m3 ->
        evt bgusegs Q (MS (mkR (Z_to_bv 64 0x10a074) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) y5 y6 u2 sp (Z_to_bv 64 ax) y10
                            y11 y12 (Z_to_bv 64 (Z.of_nat (rs1_top (bn_buf bx) (bn_top bx)))) y14 y15 y16 y17 (Z_to_bv 64 (Z.of_nat (bn_top bx))) (Z_to_bv 64 ax) y20
                            s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x10a1bc) fc None m3 (seg_rom bgusegs)))
      end.
      { intros m3 y5 y6 y10 y11 y12 y14 y15 y16 y17 y20 UR BNr FR3 ERR3 ST3 MI3 MU4 WM4.
        clear U2 BNx FR ERR STc MIc MU3 WM3.
        assert (LRES : length (rs1_res (bn_buf bx) (bn_top bx)) = bn_dmax bx) by (rewrite rs1_res_length; [exact LBX| unfold bn_dmax in OKx2; lia]).
        assert (LMR : Z.of_nat (length (wlimbs (rs1_res (bn_buf bx) (bn_top bx)))) = Z.of_nat (bn_dmax bx)) by (rewrite wlimbs_len, LRES; reflexivity).
        assert (HWL3 : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
        { constructor; [left; cbn; lia|]. constructor; [right; right; exists rx, ax; split; [exact HAx|]; split; [exact NROx|]; cbn; lia|].
          constructor; [| constructor]. right; left; exists (px, Dx, 8 * Z.of_nat (bn_dmax bx)); cbn; split; [exact Hinpx| clear; lia]. }
        assert (WOK3 : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
        { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW LB bs PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx| exact NROx| cbn; lia| cbn; lia]|].
          constructor; [| constructor].
          eapply (w_limbs OW LB bs PL EA (bv_unsigned sp) false [rx] _ rx px Dx); [left; reflexivity| exact HVx| exact Edx| exact Hinpx| cbn [fst snd]; fold bx; clear; lia| cbn [fst snd]; fold bx; clear; lia]. }

        assert (CLOSE : forall m5, rw_cells bgusegs m5 ax (bn_cells Dx (rs1_bn bx)) -> u64arr bgusegs m5 Dx (wlimbs (rs1_res (bn_buf bx) (bn_top bx))) ->
                         munch [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m m5 -> wmono bgusegs m m5 ->
                         lib_state (setbn rx (rs1_bn bx) bs) m5 OW PL EA).
        { intros m5 BN5 U5 MU5 WM5. unfold lib_state. eapply (lib_state_close [] bs m5 OW PL EA rx ax); [| exact ND| exact HAx| exact NROx| | |].
          - exact (lib_state_frame s LB _ _ [rx] bs m m5 OW PL EA _ HEAP LSH MU5 WM5 FROK WOK3).
          - exists Dx. split; [exact BN5|]. unfold bn_arr, rs1_bn, bn_dmax. cbn [bn_d bn_buf]. rewrite Edx, LRES. split; [exact Hinpx| exact U5].
          - unfold bg_ok, rs1_bn, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. rewrite LRES. split; [apply rs1_res_limbs; exact OKx1|]. split; [lia|]. split; [unfold BG_DMAX; exact OKx3| exact OKx4].
          - apply ids_ok_setbn_same; [exact IDS| exact HVx|]. unfold bn_blocks, rs1_bn, bn_dmax. cbn [bn_d bn_buf]. rewrite LRES. reflexivity. }
        step. step. if_cases KN; zify_cond KN.
        -
          ihere. to_implM. fold bx.
          eapply (EPI s (setbn rx (rs1_bn bx) bs) m3 OW errv);
            [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU4 WM4 HWL3 CEIL)
            | apply CLOSE; [| exact UR| exact MU4| exact WM4]
            | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU4 WM4 HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia
            | exact ST3 | exact ERR3 | exact MI3
            | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU4 WM4 HWL3 CEIL); unfold GLOBALS_TOP; lia
            | reflexivity | reflexivity | apply refs_stable_setbn
            | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR3 ].
          unfold bn_cells, rs1_bn, bn_dmax. cbn [bn_d bn_buf bn_top bn_neg bn_flags]. rewrite LRES.
          replace (rs1_top (bn_buf bx) (bn_top bx) =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; rewrite ?unsigned_lit in KN by lia; lia). exact BNr.
        -
          step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
          ihere. to_implM. fold bx.
          eapply (EPI s (setbn rx (rs1_bn bx) bs) m5 OW errv);
            [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU4 WM4 HWL3 CEIL)
            | apply CLOSE; [| assumption| exact MU4| exact WM4]
            | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU4 WM4 HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia
            | assumption | exact ERR3 | assumption
            | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU4 WM4 HWL3 CEIL); unfold GLOBALS_TOP; lia
            | reflexivity | reflexivity | apply refs_stable_setbn
            | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR3 ].
          unfold bn_cells, rs1_bn, bn_dmax. cbn [bn_d bn_buf bn_top bn_neg bn_flags]. rewrite LRES.
          replace (rs1_top (bn_buf bx) (bn_top bx) =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; rewrite ?unsigned_lit in KN by lia; lia). cbn [Z.b2z]. exact BNr. }
      step. if_cases K2; zify_cond K2.
      +
        assert (T1 : (bn_top bx - 1 = 0)%nat)
          by (repeat match type of K2 with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in K2; first [discriminate K2 | lia]).
        replace (bn_top bx - 1)%nat with 0%nat in U2 by lia. rewrite rs1_mix_0 in U2.
        eapply TAIL; [exact U2 | exact BNx | exact FR | exact ERR | exact STc | exact MIc | exact MU3 | exact WM3].
      +
        step. step. unfold MallocRep.wz.
        setreg 14%Z (Z_to_bv 64 (2 ^ 64 - 1 - Dx)) ltac:(rs1_not).
        setreg 15%Z (Z_to_bv 64 (2 ^ 64 - 1 - Dx)) ltac:(rs1_not).
        step. setreg 11%Z (Z_to_bv 64 (Z.of_nat (bn_top bx - 2) + 2)) ltac:(rs1_eq).
        step. setreg 12%Z (Z_to_bv 64 (8 * Z.of_nat (bn_top bx - 2))) ltac:(rs1_eq).
        step. setreg 10%Z (Z_to_bv 64 (Dx + 8 * Z.of_nat (bn_top bx - 2))) ltac:(rs1_eq).
        step. setreg 20%Z (Z_to_bv 64 (Dx + 8 * Z.of_nat (bn_top bx - 2))) ltac:(rs1_eq).
        step. setreg 17%Z (Z_to_bv 64 1) ltac:(rs1_eq).
        setreg 16%Z (Z_to_bv 64 (nth (S (bn_top bx - 2)) (bn_buf bx) 0)) ltac:(unfold t; f_equal; f_equal; lia).
        replace (bn_top bx - 1)%nat with (S (bn_top bx - 2)) in U2 by lia.
        eapply (rs1_loop _ (bn_buf bx) (bn_top bx) Dx) with (k := (bn_top bx - 2)%nat);
          [exact OKx1 | unfold bn_dmax in OKx2; lia | lia | rewrite LBX; lia | lia | rewrite LBX; lia | exact U2 | exact MIc |].
        intros m4 y15 U4 MU4 WM4 MI4.
        eapply (rw_cells_transport bgusegs _ _ m4) in FR; [| exact MU4 | exact WM4 | cbn; lia].
        eapply (rw_cells_transport bgusegs _ _ m4) in ERR; [| exact MU4 | exact WM4 | cbn; lia].
        eapply (rw_cells_transport bgusegs _ _ m4) in BNx; [| exact MU4 | exact WM4 | cbn; lia].
        eapply TAIL; [exact U4 | exact BNx | exact FR | exact ERR | | exact MI4 | | eapply wmono_trans; [exact WM3| exact WM4]].
        * eapply (stk_transport_disjoint bgusegs _ _ m4); [exact STc | exact MU4 | exact WM4 |]. cbn [disjoint_from]. unfold bn_dmax in OKx2. lia.
        * eapply munch_trans; [exact MU3|]. eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]; intros x Hx. unfold bn_dmax in OKx2. lia.
  Qed.
End Proofs.

End WithCeiling0.
