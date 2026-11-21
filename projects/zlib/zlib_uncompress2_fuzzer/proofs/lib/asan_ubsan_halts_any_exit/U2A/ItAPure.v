(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import
  ZIface InflateState Inftrees ModelRel InftreesCoverage ItableModel ItCovIface ItCovMain.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition it_ret   (r : Z * arr * Z * Z * arr) : Z   := fst (fst (fst (fst r))).
Definition it_tbl   (r : Z * arr * Z * Z * arr) : arr := snd (fst (fst (fst r))).
Definition it_table (r : Z * arr * Z * Z * arr) : Z   := snd (fst (fst r)).
Definition it_bits  (r : Z * arr * Z * Z * arr) : Z   := snd (fst r).
Definition it_work  (r : Z * arr * Z * Z * arr) : arr := snd r.
Definition cty (ty : codetype) : Z := match ty with CODES => 0 | LENS => 1 | DISTS => 2 end.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition lensA (lf : Z -> Z) : arr := arr_init N_LENS lf.
Definition tblA (cf : Z -> Z) : arr := arr_init N_CODES cf.
Definition workA (wf : Z -> Z) : arr := arr_init N_WORK wf.

Section Model.
  Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z).

  Definition cntK (k : Z) : arr := itm_count_k (lensA lf) lens_ofs k.
  Definition cntA : arr := itm_count (lensA lf) lens_ofs codes.
  Definition mxA : Z := itm_max cntA.
  Definition mnA : Z := itm_min cntA mxA.
  Definition rootA : Z := itm_root bits mxA mnA.
  Definition offsA : arr := itm_offs cntA.
  Definition work1A : arr := itm_work (lensA lf) lens_ofs codes offsA (workA wf).
  Definition resA : Z * arr * Z * Z * arr :=
    inflate_table ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf).
End Model.


Record itc (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) : Prop := ITC {
  C_lf    : forall i, 0 <= i < N_LENS -> 0 <= lf i < 65536;
  C_cf    : forall i, 0 <= i < N_CODES -> 0 <= cf i < two32;
  C_wf    : forall i, 0 <= i < N_WORK -> 0 <= wf i < 65536;
  C_ofs   : 0 <= lens_ofs;
  C_ofs2  : lens_ofs + codes <= N_LENS;
  C_codes : 0 <= codes;
  C_codes2 : codes <= 288;
  C_lens15 : forall s, 0 <= s < codes -> lf (lens_ofs + s) <= 15;
  C_tyC   : ty = CODES -> codes <= 19 /\ bits = 7 /\ (forall s, 0 <= s < codes -> lf (lens_ofs + s) <= 7);
  C_tyD   : ty = DISTS -> codes <= 32;
  C_bits  : 1 <= bits;
  C_bits2 : bits <= 15;
  C_nx    : 0 <= nx;
  C_room  : nx + it_room ty <= N_CODES }.

Ltac open_itc C :=
  destruct C as [Hlf Hcf Hwf Hofs Hofs2 Hcodes Hcodes2 Hlens15 HtyC HtyD Hbits Hbits2 Hnx Hroom];
  cbv [N_LENS N_CODES N_WORK] in Hlf, Hcf, Hwf, Hofs2, Hcodes2, Hroom.


Section Safe.
  Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z).
  Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf.

  Lemma lensA_get : forall i, arr_get (lensA lf) i = lf i.
  Proof. intros. apply arr_get_init. Qed.
  Lemma workA_get : forall i, arr_get (workA wf) i = wf i.
  Proof. intros. apply arr_get_init. Qed.
  Lemma tblA_get : forall i, arr_get (tblA cf) i = cf i.
  Proof. intros. apply arr_get_init. Qed.

  Lemma it_safe_ok : it_safe ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf) = true.
  Proof.
    destruct C.
    apply it_safe_true; unfold lensA, tblA, workA; rewrite ?arr_len_init.
    all: cbv [N_WORK N_LENS N_CODES] in *; try lia.
    - intros s Hs. rewrite arr_get_init. pose proof (C_lf0 (lens_ofs + s) ltac:(lia)).
      pose proof (C_lens16 s Hs). lia.
    - intros H. destruct (C_tyC0 H) as (A & B & D). split; [exact A|]. split; [exact B|].
      intros s Hs. rewrite arr_get_init. apply D. exact Hs.
    - exact C_tyD0.
  Qed.
End Safe.


Lemma wrap16_small : forall z, 0 <= z < 65536 -> wrap16 z = z.
Proof. intros z Hz. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. exact Hz. Qed.

Lemma cntK_le : forall lf lens_ofs k i, 0 <= k -> k < 65536 -> 0 <= arr_get (cntK lf lens_ofs k) i <= k.
Proof.
  intros lf lens_ofs k i Hk Hk2. unfold cntK.
  remember (Z.to_nat k) as n eqn:Hn. replace k with (Z.of_nat n) in * by lia. clear Hk Hn. revert i.
  induction n as [|n IH]; intros i.
  - rewrite itm_count_k_0 by lia. rewrite it_zero_count_spec. lia.
  - assert (Hn : Z.of_nat n < 65536) by lia.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. rewrite itm_count_k_step by lia. cbv zeta.
    rewrite arr_get_set. destruct (_ && _).
    + specialize (IH Hn (arr_get (lensA lf) (lens_ofs + Z.of_nat n))). rewrite wrap16_small by lia. lia.
    + specialize (IH Hn i). lia.
Qed.

Lemma cntK_len : forall lf lens_ofs k, arr_len (cntK lf lens_ofs k) = 16.
Proof. intros. unfold cntK. apply itm_count_k_len. Qed.

Lemma cntA_eq : forall lf lens_ofs codes, cntA lf lens_ofs codes = cntK lf lens_ofs codes.
Proof. intros. unfold cntA, cntK. apply itm_count_eq. Qed.

Lemma cntK_step : forall lf lens_ofs k, 0 <= k -> k < 65535 ->
  cntK lf lens_ofs (k + 1) = arr_set (cntK lf lens_ofs k) (lf (lens_ofs + k)) (arr_get (cntK lf lens_ofs k) (lf (lens_ofs + k)) + 1).
Proof.
  intros lf lens_ofs k Hk Hk2. unfold cntK at 1. rewrite itm_count_k_step by lia. cbv zeta. fold (cntK lf lens_ofs k).
  unfold lensA at 1 2. rewrite !arr_get_init.
  pose proof (cntK_le lf lens_ofs k (lf (lens_ofs + k)) Hk ltac:(lia)).
  rewrite wrap16_small by lia. reflexivity.
Qed.

Lemma mx_range : forall c, 0 <= itm_max c <= 15.
Proof. intros c. rewrite itm_max_rec. pose proof (find_max_rec_spec c 16 15 ltac:(lia) ltac:(cbn; lia)) as (A & _). exact A. Qed.

Lemma mx_found : forall c k, 1 <= k <= 15 ->
  (forall j, k < j <= 15 -> arr_get c j = 0) -> arr_get c k <> 0 -> itm_max c = k.
Proof.
  intros c k Hk Hz Hnz. rewrite itm_max_rec.
  pose proof (find_max_rec_spec c 16 15 ltac:(lia) ltac:(cbn; lia)) as (A & B & C). cbv zeta in *.
  set (r := find_max_rec c 16 15) in *.
  destruct (Z.lt_trichotomy r k) as [L | [E | G]]; [| exact E |].
  - exfalso. apply Hnz. apply C. lia.
  - exfalso. destruct B as [B | B]; [lia|]. apply B. apply Hz. lia.
Qed.

Lemma mx_zero : forall c, (forall j, 1 <= j <= 15 -> arr_get c j = 0) -> itm_max c = 0.
Proof.
  intros c Hz. rewrite itm_max_rec.
  pose proof (find_max_rec_spec c 16 15 ltac:(lia) ltac:(cbn; lia)) as (A & B & C). cbv zeta in *.
  set (r := find_max_rec c 16 15) in *. destruct (Z.eq_dec r 0) as [E|NE]; [exact E|].
  destruct B as [B | B]; [exact B|]. exfalso. apply B. apply Hz. lia.
Qed.

Lemma mn_range : forall c mx, 1 <= mx <= 15 -> 1 <= itm_min c mx <= mx.
Proof.
  intros c mx Hmx. rewrite itm_min_rec by lia.
  pose proof (find_min_rec_spec c mx 16 1 ltac:(lia) ltac:(cbn; lia)) as (A & _). exact A.
Qed.

Lemma mn_found : forall c mx m, 1 <= mx <= 15 -> 1 <= m < mx ->
  (forall j, 1 <= j < m -> arr_get c j = 0) -> arr_get c m <> 0 -> itm_min c mx = m.
Proof.
  intros c mx m Hmx Hm Hz Hnz. rewrite itm_min_rec by lia.
  pose proof (find_min_rec_spec c mx 16 1 ltac:(lia) ltac:(cbn; lia)) as (A & B & C). cbv zeta in *.
  set (r := find_min_rec c mx 16 1) in *.
  destruct (Z.lt_trichotomy r m) as [L | [E | G]]; [| exact E |].
  - exfalso. destruct B as [B | B]; [lia|]. apply B. apply Hz. lia.
  - exfalso. apply Hnz. apply C. lia.
Qed.

Lemma mn_all : forall c mx, 1 <= mx <= 15 ->
  (forall j, 1 <= j < mx -> arr_get c j = 0) -> itm_min c mx = mx.
Proof.
  intros c mx Hmx Hz. rewrite itm_min_rec by lia.
  pose proof (find_min_rec_spec c mx 16 1 ltac:(lia) ltac:(cbn; lia)) as (A & B & C). cbv zeta in *.
  set (r := find_min_rec c mx 16 1) in *. destruct (Z.eq_dec r mx) as [E|NE]; [exact E|].
  destruct B as [B | B]; [exact B|]. exfalso. apply B. apply Hz. lia.
Qed.

Lemma cntK_pos : forall lf lens_ofs k i, 0 <= k -> k < 65535 ->
  (forall s, 0 <= s < k -> 0 <= lf (lens_ofs + s) <= 15) ->
  0 <= i < k -> 1 <= arr_get (cntK lf lens_ofs k) (lf (lens_ofs + i)).
Proof.
  intros lf lens_ofs k i Hk Hk2 Hl Hi.
  remember (Z.to_nat k) as n eqn:Hn. replace k with (Z.of_nat n) in * by lia. clear Hk Hn. revert i Hi Hl.
  induction n as [|n IH]; intros i Hi Hl; [lia|].
  assert (Hn : Z.of_nat n < 65535) by lia.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. rewrite cntK_step by lia.
  pose proof (cntK_le lf lens_ofs (Z.of_nat n) (lf (lens_ofs + i)) ltac:(lia) ltac:(lia)).
  pose proof (Hl (Z.of_nat n) ltac:(lia)). pose proof (Hl i ltac:(lia)).
  destruct (Z.eq_dec (lf (lens_ofs + Z.of_nat n)) (lf (lens_ofs + i))) as [E|NE].
  - rewrite E. rewrite arr_get_set_same by (rewrite cntK_len; lia). lia.
  - rewrite arr_get_set_other by exact NE.
    destruct (Z.eq_dec i (Z.of_nat n)) as [->|Hne]; [congruence|].
    apply IH; try lia. intros s Hs. apply Hl. lia.
Qed.

Fixpoint lzk (c : arr) (k : nat) : Z :=
  match k with O => 1 | S k' => 2 * lzk c k' - arr_get c (Z.of_nat k) end.
Definition LZ (c : arr) (k : Z) : Z := lzk c (Z.to_nat k).

Lemma LZ_S : forall c k, 0 <= k -> LZ c (k + 1) = 2 * LZ c k - arr_get c (k + 1).
Proof.
  intros c k Hk. unfold LZ. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  cbn [lzk]. f_equal. f_equal. lia.
Qed.

Lemma left_rec_adv : forall c (m : nat) (n : nat) k,
  0 <= k -> k + Z.of_nat m <= 15 -> (m <= n)%nat ->
  (forall j, k < j <= k + Z.of_nat m -> 0 <= LZ c j) ->
  left_rec c n (k + 1) (LZ c k) = left_rec c (n - m) (k + Z.of_nat m + 1) (LZ c (k + Z.of_nat m)).
Proof.
  intros c m. induction m as [|m IH]; intros n k Hk Hm Hn Hpos.
  - cbn [Z.of_nat]. rewrite !Z.add_0_r. replace (n - 0)%nat with n by lia. reflexivity.
  - destruct n as [|n]; [lia|]. rewrite left_rec_S.
    destruct (Z.leb_spec (k + 1) MAXBITS); [|unfold MAXBITS in *; lia].
    rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
    replace (LZ c k * 2 - arr_get c (k + 1)) with (LZ c (k + 1)) by (rewrite LZ_S by lia; lia).
    pose proof (Hpos (k + 1) ltac:(lia)) as P1.
    destruct (Z.ltb_spec (LZ c (k + 1)) 0); [lia|].
    cbn [Nat.sub]. replace (k + Z.of_nat (S m)) with (k + 1 + Z.of_nat m) by lia.
    apply IH; try lia. intros j Hj. apply Hpos. lia.
Qed.

Lemma left_check_some : forall c, (forall j, 1 <= j <= 15 -> 0 <= LZ c j) -> it_left_check c = Some (LZ c 15).
Proof.
  intros c Hpos. rewrite it_left_check_rec.
  change (left_rec c 16 1 1) with (left_rec c 16 (0 + 1) (LZ c 0)).
  rewrite (left_rec_adv c 15 16 0); try lia; [| intros; apply Hpos; lia].
  cbn [Nat.sub Z.of_nat]. reflexivity.
Qed.

Lemma left_check_none : forall c k, 1 <= k <= 15 ->
  (forall j, 1 <= j < k -> 0 <= LZ c j) -> LZ c k < 0 -> it_left_check c = None.
Proof.
  intros c k Hk Hpos Hneg. rewrite it_left_check_rec.
  change (left_rec c 16 1 1) with (left_rec c 16 (0 + 1) (LZ c 0)).
  rewrite (left_rec_adv c (Z.to_nat (k - 1)) 16 0); try lia; [| intros; apply Hpos; lia].
  replace (0 + Z.of_nat (Z.to_nat (k - 1))) with (k - 1) by lia.
  replace (16 - Z.to_nat (k - 1))%nat with (S (16 - Z.to_nat k))%nat by lia.
  rewrite left_rec_S. destruct (Z.leb_spec (k - 1 + 1) MAXBITS); [|unfold MAXBITS in *; lia].
  rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
  replace (LZ c (k - 1) * 2 - arr_get c (k - 1 + 1)) with (LZ c k).
  2:{ replace k with (k - 1 + 1) at 1 by lia. rewrite LZ_S by lia. lia. }
  destruct (Z.ltb_spec (LZ c k) 0); [reflexivity | lia].
Qed.

Lemma LZ_bound : forall c k N, 0 <= N -> (forall j, 0 <= arr_get c j <= N) -> 0 <= k <= 15 ->
  - 65536 * N <= LZ c k <= 32768.
Proof.
  intros c k N HN Hc Hk. unfold LZ. remember (Z.to_nat k) as n eqn:Hn.
  assert (Hn15 : (n <= 15)%nat) by lia. clear Hn Hk k.
  assert (G : - (2 ^ Z.of_nat n - 1) * N <= lzk c n <= 2 ^ Z.of_nat n).
  { induction n as [|n IH].
    - cbn. lia.
    - cbn [lzk]. specialize (IH ltac:(lia)). pose proof (Hc (Z.of_nat (S n))).
      replace (2 ^ Z.of_nat (S n)) with (2 * 2 ^ Z.of_nat n) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
      pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n) ltac:(lia) ltac:(lia)). nia. }
  assert (2 ^ Z.of_nat n <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). change (2 ^ 15) with 32768 in *.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n) ltac:(lia) ltac:(lia)). nia.
Qed.

Lemma zext32_x2 : forall c, 0 <= c < 2147483648 ->
  Z.shiftr ((Z.shiftl c 32) mod 18446744073709551616) 31 = 2 * c.
Proof.
  intros c Hc. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma zext32_id : forall c, 0 <= c < 4294967296 ->
  Z.shiftr ((Z.shiftl c 32) mod 18446744073709551616) 32 = c.
Proof.
  intros c Hc. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia). apply Z.div_mul. lia.
Qed.
Lemma zext32_x4 : forall c, 0 <= c < 1073741824 ->
  Z.shiftr ((Z.shiftl c 32) mod 18446744073709551616) 30 = 4 * c.
Proof.
  intros c Hc. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (4 * 2 ^ 30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Lemma zext16_id : forall c, 0 <= c < 65536 ->
  Z.shiftr ((Z.shiftl c 48) mod 18446744073709551616) 48 = c.
Proof.
  intros c Hc. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 48) with 281474976710656; lia). apply Z.div_mul. lia.
Qed.

Lemma LZ_0 : forall c, LZ c 0 = 1.
Proof. reflexivity. Qed.
Lemma LZ_1 : forall c, LZ c 1 = 2 - arr_get c 1.
Proof. intros c. change 1 with (0 + 1) at 1. rewrite LZ_S by lia. rewrite LZ_0. reflexivity. Qed.

Lemma LZ_S' : forall c k, 1 <= k -> LZ c k = 2 * LZ c (k - 1) - arr_get c k.
Proof.
  intros c k Hk. replace k with (k - 1 + 1) at 1 by lia. rewrite LZ_S by lia. f_equal. f_equal. lia.
Qed.

Fixpoint osk (c : arr) (n : nat) : Z :=
  match n with O => 0 | S n' => osk c n' + arr_get c (Z.of_nat n) end.
Definition OZ (c : arr) (k : Z) : Z := osk c (Z.to_nat (k - 1)).

Lemma OZ_1 : forall c, OZ c 1 = 0.
Proof. reflexivity. Qed.
Lemma OZ_S : forall c k, 1 <= k -> OZ c (k + 1) = OZ c k + arr_get c k.
Proof.
  intros c k Hk. unfold OZ. replace (Z.to_nat (k + 1 - 1)) with (S (Z.to_nat (k - 1))) by lia.
  cbn [osk]. f_equal. f_equal. lia.
Qed.
Lemma OZ_S' : forall c k, 2 <= k -> OZ c k = OZ c (k - 1) + arr_get c (k - 1).
Proof. intros c k Hk. replace k with (k - 1 + 1) at 1 by lia. apply OZ_S. lia. Qed.

Lemma OZ_range : forall c N k, 0 <= N -> (forall j, 0 <= arr_get c j <= N) -> 1 <= k ->
  0 <= OZ c k <= (k - 1) * N.
Proof.
  intros c N k HN Hc Hk. unfold OZ. remember (Z.to_nat (k - 1)) as n eqn:Hn.
  replace (k - 1) with (Z.of_nat n) by lia. clear Hn Hk k.
  induction n as [|n IH]; [cbn; lia|]. cbn [osk]. pose proof (Hc (Z.of_nat (S n))). lia.
Qed.

Lemma offs_spec : forall c, (forall j, 0 <= arr_get c j <= 288) ->
  forall k, 1 <= k <= 15 -> arr_get (itm_offs c) k = OZ c k.
Proof.
  intros c Hc. rewrite itm_offs_eq. unfold MAXBITS.
  assert (G : forall n : nat, (n <= 14)%nat -> forall k, 1 <= k <= 1 + Z.of_nat n ->
             arr_get (itm_offs_k c (1 + Z.of_nat n)) k = OZ c k).
  { induction n as [|n IH]; intros Hn k Hk.
    - cbn [Z.of_nat Z.add] in *. replace k with 1 by lia. rewrite itm_offs_k_1.
      rewrite arr_get_set_same by (rewrite arr_len_make; lia). rewrite OZ_1. reflexivity.
    - replace (1 + Z.of_nat (S n)) with (1 + Z.of_nat n + 1) in * by lia.
      rewrite itm_offs_k_step by lia. cbv zeta.
      destruct (Z.eq_dec k (1 + Z.of_nat n + 1)) as [->|Hne].
      + rewrite arr_get_set_same by (rewrite itm_offs_k_len; lia).
        rewrite IH by lia. rewrite OZ_S by lia.
        pose proof (OZ_range c 288 (1 + Z.of_nat n) ltac:(lia) Hc ltac:(lia)). pose proof (Hc (1 + Z.of_nat n)).
        apply wrap16_small. lia.
      + rewrite arr_get_set_other by lia. apply IH; lia. }
  intros k Hk. change 15 with (1 + Z.of_nat 14). apply G; lia.
Qed.

Lemma sort_ok_at : forall lens lens_ofs codes offs work WN i,
  it_sort_ok lens lens_ofs codes offs WN = true -> 0 <= i < codes ->
  arr_get lens (lens_ofs + i) <> 0 ->
  0 <= arr_get (fst (itm_sort_k lens lens_ofs i offs work)) (arr_get lens (lens_ofs + i)) < WN.
Proof.
  intros lens lens_ofs codes offs work WN i Hok Hi Hnz. rewrite it_sort_ok_eq in Hok.
  pose proof (itm_sort_ok_k_le lens lens_ofs offs WN codes (i + 1) ltac:(lia) Hok) as H1.
  exact (proj2 (itm_sort_ok_k_inv lens lens_ofs offs work WN i ltac:(lia) H1) Hnz).
Qed.

Lemma sort_k_skip : forall lens lens_ofs i offs work, 0 <= i -> arr_get lens (lens_ofs + i) = 0 ->
  itm_sort_k lens lens_ofs (i + 1) offs work = itm_sort_k lens lens_ofs i offs work.
Proof.
  intros lens lens_ofs i offs work Hi Hz. rewrite itm_sort_k_step by lia.
  destruct (itm_sort_k lens lens_ofs i offs work) as [o w]. cbn [sort_body]. rewrite Hz. reflexivity.
Qed.
Lemma sort_k_take : forall lens lens_ofs i offs work, 0 <= i -> arr_get lens (lens_ofs + i) <> 0 ->
  itm_sort_k lens lens_ofs (i + 1) offs work =
  (let ow := itm_sort_k lens lens_ofs i offs work in
   let l := arr_get lens (lens_ofs + i) in
   let o := arr_get (fst ow) l in
   (arr_set (fst ow) l (wrap16 (o + 1)), arr_set (snd ow) o (wrap16 i))).
Proof.
  intros lens lens_ofs i offs work Hi Hnz. rewrite itm_sort_k_step by lia.
  destruct (itm_sort_k lens lens_ofs i offs work) as [o w]. cbn [sort_body fst snd].
  destruct (Z.eqb_spec (arr_get lens (lens_ofs + i)) 0); [lia|]. reflexivity.
Qed.

Lemma sort_k_work_range : forall lens lens_ofs k offs work n,
  (forall i, 0 <= i < n -> 0 <= arr_get work i < 65536) ->
  forall i, 0 <= i < n -> 0 <= arr_get (snd (itm_sort_k lens lens_ofs k offs work)) i < 65536.
Proof.
  intros lens lens_ofs k offs work n B. unfold itm_sort_k.
  destruct (Z_lt_le_dec k 0).
  - rewrite forZ_nil by lia. exact B.
  - apply (forZ_ind (fun _ ow => forall i, 0 <= i < n -> 0 <= arr_get (snd ow) i < 65536)); [| exact B | lia].
    intros j [o w] _ H i Hi. cbn [sort_body snd] in *.
    destruct (negb _); cbn [snd]; [|apply H; exact Hi]. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply H; exact Hi].
Qed.

Lemma sort_k_len : forall lens lens_ofs k offs work,
  arr_len (fst (itm_sort_k lens lens_ofs k offs work)) = arr_len offs /\
  arr_len (snd (itm_sort_k lens lens_ofs k offs work)) = arr_len work.
Proof. intros. apply itm_sort_k_len. Qed.

Lemma offsA_len : forall lf lens_ofs codes, arr_len (offsA lf lens_ofs codes) = 16.
Proof. intros. unfold offsA. rewrite itm_offs_eq. apply itm_offs_k_len. Qed.
Lemma workA_len : forall wf, arr_len (workA wf) = 288.
Proof. intros. unfold workA. apply arr_len_init. Qed.
Lemma lensA_len : forall lf, arr_len (lensA lf) = 320.
Proof. intros. unfold lensA. apply arr_len_init. Qed.

Fixpoint allr (f : Z -> Z) (lo hi : Z) (n : nat) : bool :=
  match n with O => true | S n' => (lo <=? f (Z.of_nat n')) && (f (Z.of_nat n') <? hi) && allr f lo hi n' end.
Lemma allr_spec : forall f lo hi n, allr f lo hi n = true -> forall j, 0 <= j < Z.of_nat n -> lo <= f j < hi.
Proof.
  intros f lo hi n. induction n as [|n IH]; intros H j Hj; [lia|].
  cbn [allr] in H. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  destruct (Z.eq_dec j (Z.of_nat n)) as [->|]; [lia|]. apply IH; [exact H2 | lia].
Qed.
Lemma lbase_range : forall j, 0 <= j < 31 -> 0 <= arr_get lbase_a j < 65536.
Proof. apply (allr_spec (arr_get lbase_a) 0 65536 31). vm_compute. reflexivity. Qed.
Lemma lext_range : forall j, 0 <= j < 31 -> 0 <= arr_get lext_a j < 65536.
Proof. apply (allr_spec (arr_get lext_a) 0 65536 31). vm_compute. reflexivity. Qed.
Lemma dbase_range : forall j, 0 <= j < 32 -> 0 <= arr_get dbase_a j < 65536.
Proof. apply (allr_spec (arr_get dbase_a) 0 65536 32). vm_compute. reflexivity. Qed.
Lemma dext_range : forall j, 0 <= j < 32 -> 0 <= arr_get dext_a j < 65536.
Proof. apply (allr_spec (arr_get dext_a) 0 65536 32). vm_compute. reflexivity. Qed.

Section Trip.
  Variables (x : ItCtx) (st : ItSt).
  Definition tr_hb : Z := t_len st - t_drop st.
  Definition tr_w : Z := arr_get (t_work st) (t_sym st).
  Definition tr_ov : Z * Z :=
    let ty := x_ty x in let w := tr_w in
    if w + 1 <? it_match ty then (0, w)
    else if it_match ty <=? w then (wrap8 (it_extra ty (t_work st) (w - it_match ty)), it_base ty (t_work st) (w - it_match ty))
    else (96, 0).
  Definition tr_op : Z := fst tr_ov.
  Definition tr_val : Z := snd tr_ov.
  Definition tr_here : Z := code_pack tr_op (wrap8 tr_hb) tr_val.
  Definition tr_incr : Z := shl32 1 tr_hb.
  Definition tr_fill : Z := shl32 1 (t_curr st).
  Definition tr_tbl1 : arr := it_fill tr_here tr_incr (t_huff st) (t_drop st) (t_next st) tr_fill (t_tbl st).
  Definition tr_incr2 : Z := it_incr_back (t_huff st) (t_len st).
  Definition tr_huff : Z := if negb (tr_incr2 =? 0) then Z.land (t_huff st) (tr_incr2 - 1) + tr_incr2 else 0.
  Definition tr_sym : Z := wrap32 (t_sym st + 1).
  Definition tr_c : Z := wrap16 (arr_get (t_count st) (t_len st) - 1).
  Definition tr_count : arr := arr_set (t_count st) (t_len st) tr_c.
  Definition tr_brk : bool := (tr_c =? 0) && (t_len st =? x_max x).
  Definition tr_len : Z := if (tr_c =? 0) && negb (t_len st =? x_max x)
                           then arr_get (x_lens x) (x_lens_ofs x + arr_get (t_work st) tr_sym) else t_len st.
  Definition tr_st1 : ItSt := mkItSt tr_huff tr_sym tr_len (t_next st) (t_curr st) (t_drop st) (t_low st) (t_used st)
                                     tr_fill tr_count tr_tbl1 (t_work st).
  Definition tr_sub : bool := (x_root x <? tr_len) && negb (Z.land tr_huff (x_mask x) =? t_low st).
  Definition tr_drop : Z := if t_drop st =? 0 then x_root x else t_drop st.
  Definition tr_next : Z := t_next st + tr_fill.
  Definition tr_curr : Z := it_subtable_curr tr_count tr_len tr_drop (x_max x).
  Definition tr_used : Z := wrap32 (t_used st + Z.shiftl 1 tr_curr).
  Definition tr_st2 : ItSt := mkItSt tr_huff tr_sym tr_len tr_next tr_curr tr_drop (t_low st) tr_used
                                     tr_fill tr_count tr_tbl1 (t_work st).
  Definition tr_low : Z := Z.land tr_huff (x_mask x).
  Definition tr_tbl2 : arr := arr_set tr_tbl1 (x_table x + tr_low) (code_pack tr_curr (x_root x) (tr_next - x_table x)).
  Definition tr_st3 : ItSt := mkItSt tr_huff tr_sym tr_len tr_next tr_curr tr_drop tr_low tr_used
                                     tr_fill tr_count tr_tbl2 (t_work st).

  Lemma it_step_eq : it_step x st =
    if tr_brk then ItBreak tr_st1
    else if tr_sub then (if it_not_enough (x_ty x) tr_used then ItFail tr_st2 else ItCont tr_st3)
    else ItCont tr_st1.
  Proof.
    unfold it_step, tr_st1, tr_st2, tr_st3, tr_brk, tr_sub, tr_used, tr_curr, tr_next, tr_drop, tr_low, tr_tbl2,
      tr_len, tr_count, tr_c, tr_sym, tr_huff, tr_incr2, tr_tbl1, tr_fill, tr_incr, tr_here, tr_op, tr_val, tr_ov, tr_w, tr_hb.
    cbv zeta.
    destruct (arr_get (t_work st) (t_sym st) + 1 <? it_match (x_ty x));
      [| destruct (it_match (x_ty x) <=? arr_get (t_work st) (t_sym st))]; cbn [fst snd]; reflexivity.
  Qed.
End Trip.

Ltac split_all := repeat match goal with |- _ /\ _ => split end.

Definition BOX (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?P => change (BOX P) in H end.
Ltac unbox H := unfold BOX in H.

Definition tr_hd (st : ItSt) : Z := Z.shiftr (t_huff st) (t_drop st).
Definition fill_body (here incr hd next : Z) (ft : Z * arr) : bool * (Z * arr) :=
  let '(fill, tbl) := ft in
  let fill' := wrap32 (fill - incr) in
  let tbl' := arr_set tbl (next + (hd + fill')) here in
  if negb (fill' =? 0) then (true, (fill', tbl')) else (false, (fill', tbl')).
Lemma it_fill_eq : forall here incr huff drop next fill tbl,
  it_fill here incr huff drop next fill tbl = snd (loopZ fill (fill_body here incr (Z.shiftr huff drop) next) (fill, tbl)).
Proof. reflexivity. Qed.
Lemma fill_last : forall here incr hd next n f t, 0 < n -> wrap32 (f - incr) = 0 ->
  loopZ n (fill_body here incr hd next) (f, t) = (0, arr_set t (next + (hd + 0)) here).
Proof.
  intros here incr hd next n f t Hn H0. rewrite loopZ_step by lia. cbn [fill_body]. rewrite H0. cbn [Z.eqb negb]. reflexivity.
Qed.
Lemma fill_more : forall here incr hd next n f t, 0 < n -> wrap32 (f - incr) <> 0 ->
  loopZ n (fill_body here incr hd next) (f, t) =
  loopZ (n - 1) (fill_body here incr hd next) (wrap32 (f - incr), arr_set t (next + (hd + wrap32 (f - incr))) here).
Proof.
  intros here incr hd next n f t Hn H0. rewrite loopZ_step at 1 by lia. cbn [fill_body].
  destruct (Z.eqb_spec (wrap32 (f - incr)) 0); [lia|]. cbn [negb]. reflexivity.
Qed.
Lemma shl32_1 : forall k, 0 <= k <= 15 -> shl32 1 k = 2 ^ k.
Proof. intros k Hk. exact (itm_used_pow2 k Hk). Qed.
Lemma wrap32_small : forall z, 0 <= z < 4294967296 -> wrap32 z = z.
Proof. intros z Hz. unfold wrap32. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma loopZ_fuel_arr_len : forall here incr hd next n f t,
  arr_len (snd (loopZ n (fill_body here incr hd next) (f, t))) = arr_len t.
Proof.
  intros here incr hd next n. destruct (Z_lt_le_dec 0 n) as [Hn|Hn].
  2:{ intros. rewrite loopZ_le0 by lia. reflexivity. }
  remember (Z.to_nat n) as m eqn:Hm. replace n with (Z.of_nat m) by lia. clear n Hn Hm.
  induction m as [|m IH]; intros f t.
  - rewrite loopZ_le0 by lia. reflexivity.
  - rewrite loopZ_step by lia. cbn [fill_body]. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
    destruct (negb _); [rewrite IH|]; cbn [snd]; apply arr_len_set.
Qed.

Lemma land_le_l : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros a b Ha Hb.
  pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as Hal.
  rewrite Z.lor_ldiff_and in Hal.
  assert (Hand : Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  rewrite Hand in Hal.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia). lia.
Qed.
Lemma land_le_r : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= b.
Proof. intros. rewrite Z.land_comm. apply land_le_l; assumption. Qed.
Lemma shiftr1_half : forall c m, 0 <= c < 2 ^ Z.of_nat (S m) -> 0 <= Z.shiftr c 1 < 2 ^ Z.of_nat m.
Proof.
  intros c m Hc. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hc by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma wrap16_mod : forall z, wrap16 z = z mod 65536.
Proof. intros z. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma swrap16_cases : forall c, 0 <= c < 65536 ->
  (c < 32768 /\ bv_swrap 16 c = c) \/ (32768 <= c /\ bv_swrap 16 c = c - 65536).
Proof.
  intros c Hc. unfold bv_swrap, bv_wrap. change (bv_half_modulus 16) with 32768. change (bv_modulus 16) with 65536.
  destruct (Z_lt_le_dec c 32768).
  - left. rewrite Z.mod_small by lia. lia.
  - right. replace (c + 32768) with ((c - 32768) + 1 * 65536) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
Lemma negshift48_mod : forall n, -32769 <= n <= -1 ->
  (n * 281474976710656) mod 18446744073709551616 = (n + 65536) * 281474976710656.
Proof.
  intros n Hn. replace (n * 281474976710656) with ((n + 65536) * 281474976710656 + (-1) * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Definition incr_body (huff : Z) (incr : Z) : bool * Z :=
  if negb (Z.land huff incr =? 0) then (true, Z.shiftr incr 1) else (false, incr).
Lemma it_incr_back_eq : forall huff len, it_incr_back huff len = loopZ 32 (incr_body huff) (shl32 1 (len - 1)).
Proof. reflexivity. Qed.
Lemma incr_last : forall huff n c, 0 < n -> Z.land huff c = 0 -> loopZ n (incr_body huff) c = c.
Proof. intros huff n c Hn H0. rewrite loopZ_step by lia. unfold incr_body. rewrite H0. cbv beta iota. reflexivity. Qed.
Lemma incr_more : forall huff n c, 0 < n -> Z.land huff c <> 0 ->
  loopZ n (incr_body huff) c = loopZ (n - 1) (incr_body huff) (Z.shiftr c 1).
Proof.
  intros huff n c Hn H0. rewrite loopZ_step at 1 by lia. unfold incr_body at 1.
  destruct (Z.eqb_spec (Z.land huff c) 0); [lia|]. cbv beta iota. reflexivity.
Qed.
Lemma incr_range : forall huff n c, 0 <= c -> 0 <= loopZ n (incr_body huff) c <= c.
Proof.
  intros huff n. destruct (Z_lt_le_dec 0 n) as [Hn|Hn].
  2:{ intros. rewrite loopZ_le0 by lia. lia. }
  remember (Z.to_nat n) as m eqn:Hm. replace n with (Z.of_nat m) by lia. clear n Hn Hm.
  induction m as [|m IH]; intros c Hc.
  - rewrite loopZ_le0 by lia. lia.
  - destruct (Z.eq_dec (Z.land huff c) 0) as [E|E].
    + rewrite incr_last by lia. lia.
    + rewrite incr_more by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
      assert (0 <= Z.shiftr c 1 <= c) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      specialize (IH (Z.shiftr c 1) ltac:(lia)). lia.
Qed.

Definition curr_body (count : arr) (drop max : Z) (cl : Z * Z) : bool * (Z * Z) :=
  let '(curr, lft) := cl in
  if wrap32 (curr + drop) <? max then
    let lft' := lft - arr_get count (wrap32 (curr + drop)) in
    if lft' <=? 0 then (false, (curr, lft')) else (true, (wrap32 (curr + 1), Z.shiftl lft' 1))
  else (false, (curr, lft)).
Lemma it_subtable_curr_eq : forall count len drop max,
  it_subtable_curr count len drop max =
  fst (loopZ 16 (curr_body count drop max) (wrap32 (len - drop), swrap32 (Z.shiftl 1 (wrap32 (len - drop))))).
Proof. reflexivity. Qed.
Lemma curr_stop_ge : forall count drop max n curr lft, 0 < n -> 0 <= curr + drop < 4294967296 -> max <= curr + drop ->
  loopZ n (curr_body count drop max) (curr, lft) = (curr, lft).
Proof.
  intros count drop max n curr lft Hn Hr Hge. rewrite loopZ_step by lia. unfold curr_body at 1.
  rewrite wrap32_small by lia. destruct (Z.ltb_spec (curr + drop) max); [lia|]. reflexivity.
Qed.
Lemma curr_stop_le : forall count drop max n curr lft, 0 < n -> 0 <= curr + drop < 4294967296 -> curr + drop < max ->
  lft - arr_get count (curr + drop) <= 0 ->
  loopZ n (curr_body count drop max) (curr, lft) = (curr, lft - arr_get count (curr + drop)).
Proof.
  intros count drop max n curr lft Hn Hr Hlt Hle. rewrite loopZ_step by lia. unfold curr_body at 1.
  rewrite wrap32_small by lia. destruct (Z.ltb_spec (curr + drop) max); [|lia].
  destruct (Z.leb_spec (lft - arr_get count (curr + drop)) 0); [|lia]. reflexivity.
Qed.
Lemma curr_more : forall count drop max n curr lft, 0 < n -> 0 <= curr + drop < 4294967295 -> 0 <= curr -> curr + drop < max ->
  0 <= drop -> max <= 65536 ->
  0 < lft - arr_get count (curr + drop) ->
  loopZ n (curr_body count drop max) (curr, lft) =
  loopZ (n - 1) (curr_body count drop max) (curr + 1, Z.shiftl (lft - arr_get count (curr + drop)) 1).
Proof.
  intros count drop max n curr lft Hn Hr Hc Hlt Hd Hm Hgt. rewrite loopZ_step at 1 by lia. unfold curr_body at 1.
  rewrite wrap32_small by lia. destruct (Z.ltb_spec (curr + drop) max); [|lia].
  destruct (Z.leb_spec (lft - arr_get count (curr + drop)) 0); [lia|]. rewrite wrap32_small by lia. reflexivity.
Qed.

Lemma curr_result_range : forall count drop max n curr lft,
  0 <= curr -> 0 <= drop -> max <= 65536 -> 0 < n -> curr + drop < 4294967296 ->
  curr <= fst (loopZ n (curr_body count drop max) (curr, lft)) /\
  (curr + drop <= max -> fst (loopZ n (curr_body count drop max) (curr, lft)) <= max - drop) /\
  (max <= curr + drop -> fst (loopZ n (curr_body count drop max) (curr, lft)) = curr).
Proof.
  intros count drop max n. intros curr lft Hc Hd Hmx Hn Hcd.
  remember (Z.to_nat n) as m eqn:Hm. replace n with (Z.of_nat m) by lia. assert (Hm1 : (1 <= m)%nat) by lia. clear n Hn Hm.
  revert curr lft Hc Hcd. induction m as [|m IH]; intros curr lft Hc Hcd; [lia|].
  destruct (Z_lt_le_dec (curr + drop) max).
  - destruct (Z_lt_le_dec 0 (lft - arr_get count (curr + drop))).
    + rewrite curr_more by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
      destruct m as [|m'].
      * rewrite loopZ_le0 by lia. cbn [fst]. lia.
      * specialize (IH ltac:(lia) (curr + 1) (Z.shiftl (lft - arr_get count (curr + drop)) 1) ltac:(lia) ltac:(lia)). lia.
    + rewrite curr_stop_le by lia. cbn [fst]. lia.
  - rewrite curr_stop_ge by lia. cbn [fst]. lia.
Qed.

Lemma it_fill_len_tr : forall x st, arr_len (tr_tbl1 x st) = arr_len (t_tbl st).
Proof. intros. unfold tr_tbl1. apply it_fill_len. Qed.

Lemma code_pack_range : forall op bits val, 0 <= code_pack op bits val < 4294967296.
Proof.
  intros. unfold code_pack.
  pose proof (wrap16_range val) as A. change (2 ^ 16) with 65536 in A.
  assert (W8 : forall z, 0 <= wrap8 z < 256).
  { intros z. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  pose proof (W8 op). pose proof (W8 bits). lia.
Qed.
Lemma fill_get_cases : forall here incr hd next n f t j,
  arr_get (snd (loopZ n (fill_body here incr hd next) (f, t))) j = here \/
  arr_get (snd (loopZ n (fill_body here incr hd next) (f, t))) j = arr_get t j.
Proof.
  intros here incr hd next n. destruct (Z_lt_le_dec 0 n) as [Hn|Hn].
  2:{ intros. rewrite loopZ_le0 by lia. cbn [snd]. right. reflexivity. }
  remember (Z.to_nat n) as m eqn:Hm. replace n with (Z.of_nat m) by lia. clear n Hn Hm.
  induction m as [|m IH]; intros f t j.
  - rewrite loopZ_le0 by lia. right. reflexivity.
  - destruct (Z.eq_dec (wrap32 (f - incr)) 0) as [E|E].
    + rewrite fill_last by first [lia | exact E]. cbn [snd]. rewrite arr_get_set. destruct (_ && _); [left | right]; reflexivity.
    + rewrite fill_more by first [lia | exact E]. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
      destruct (IH (wrap32 (f - incr)) (arr_set t (next + (hd + wrap32 (f - incr))) here) j) as [A|A]; [left; exact A|].
      rewrite arr_get_set in A. destruct (_ && _); [left | right]; exact A.
Qed.
Lemma tr_tbl1_range : forall x st, (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) ->
  forall j, 0 <= j < 1444 -> 0 <= arr_get (tr_tbl1 x st) j < 4294967296.
Proof.
  intros x st H j Hj. unfold tr_tbl1. rewrite it_fill_eq.
  destruct (fill_get_cases (tr_here x st) (tr_incr st) (Z.shiftr (t_huff st) (t_drop st)) (t_next st) (tr_fill st) (tr_fill st) (t_tbl st) j) as [A|A]; rewrite A.
  - unfold tr_here. apply code_pack_range.
  - apply H. exact Hj.
Qed.
Lemma tr_tbl2_range : forall x st, (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) ->
  forall j, 0 <= j < 1444 -> 0 <= arr_get (tr_tbl2 x st) j < 4294967296.
Proof.
  intros x st H j Hj. unfold tr_tbl2. rewrite arr_get_set. destruct (_ && _); [apply code_pack_range | apply tr_tbl1_range; assumption].
Qed.
Lemma tr_count_range0 : forall st, (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) ->
  forall j, 0 <= j < 16 -> 0 <= arr_get (tr_count st) j < 65536.
Proof.
  intros st H j Hj. unfold tr_count. rewrite arr_get_set. destruct (_ && _); [|apply H; exact Hj].
  pose proof (wrap16_range (arr_get (t_count st) (t_len st) - 1)) as W. change (2 ^ 16) with 65536 in W. unfold tr_c. lia.
Qed.

Lemma trip_ok_facts : forall x WN LN TN st, it_trip_ok x WN LN TN st = true ->
  0 <= t_sym st < WN /\ 1 <= t_len st <= 15 /\ 0 <= t_drop st <= t_len st /\
  t_len st - t_drop st <= t_curr st <= 15 /\ 0 <= t_huff st < 65536 /\ 0 <= t_next st /\
  0 <= t_used st < 65536 /\ 0 <= t_min st < 65536 /\
  0 <= tr_w st < 65536 /\
  (it_match (x_ty x) <= tr_w st -> tr_w st - it_match (x_ty x) < it_ext_len (x_ty x) WN) /\
  t_next st + Z.shiftr (t_huff st) (t_drop st) + Z.shiftl 1 (t_curr st) - Z.shiftl 1 (t_len st - t_drop st) < TN /\
  (tr_c st = 0 -> t_len st <> x_max x ->
     t_sym st + 1 < WN /\ 0 <= arr_get (t_work st) (t_sym st + 1) /\
     0 <= x_lens_ofs x + arr_get (t_work st) (t_sym st + 1) < LN /\
     1 <= arr_get (x_lens x) (x_lens_ofs x + arr_get (t_work st) (t_sym st + 1)) <= 15) /\
  (forall st', it_step x st = ItCont st' -> (t_low st' <> t_low st \/ t_next st' <> t_next st) ->
     0 <= x_table x + t_low st' < TN /\ 1 <= t_curr st' <= 15 /\ t_next st <= t_next st').
Proof.
  intros x WN LN TN st H. unfold it_trip_ok in H. cbv zeta in H. fold (tr_w st) in H. fold (tr_c st) in H.
  repeat match goal with G : (_ && _) = true |- _ => apply andb_prop in G as [? ?] end.
  repeat match goal with
  | G : (_ <=? _) = true |- _ => apply Z.leb_le in G
  | G : (_ <? _) = true |- _ => apply Z.ltb_lt in G
  end.
  split_all; try lia.
  - intros Hm. match goal with G : (if tr_w st + 1 <? _ then _ else _) = true |- _ =>
      destruct (Z.ltb_spec (tr_w st + 1) (it_match (x_ty x))); [lia|];
      destruct (Z.leb_spec (it_match (x_ty x)) (tr_w st)); [|lia]; apply Z.ltb_lt in G; exact G end.
  - intros Hc Hne. match goal with G : (if (tr_c st =? 0) && _ then _ else _) = true |- _ =>
      rewrite Hc in G; cbn [Z.eqb] in G;
      destruct (Z.eqb_spec (t_len st) (x_max x)); [lia|]; cbn [negb andb] in G; cbv zeta in G;
      repeat (apply andb_prop in G as [G ?Y]) end.
    repeat match goal with
    | G : (_ <=? _) = true |- _ => apply Z.leb_le in G
    | G : (_ <? _) = true |- _ => apply Z.ltb_lt in G
    end. lia.
  - intros st' Hs Hch. match goal with G : match it_step x st with _ => _ end = true |- _ =>
      rewrite Hs in G;
      destruct (Z.eqb_spec (t_low st') (t_low st)); destruct (Z.eqb_spec (t_next st') (t_next st)); cbn [negb orb] in G; try lia;
      repeat (apply andb_prop in G as [G ?W]) end.
    all: repeat match goal with
      | G : (_ <=? _) = true |- _ => apply Z.leb_le in G
      | G : (_ <? _) = true |- _ => apply Z.ltb_lt in G
      end; lia.
Qed.

Section Res.
  Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z).
  Let cnt := cntA lf lens_ofs codes.
  Let mx := mxA lf lens_ofs codes.
  Let mn := mnA lf lens_ofs codes.
  Let rt := rootA lf lens_ofs codes bits.
  Let w1 := work1A lf lens_ofs codes wf.
  Let X := itm_ctx ty (lensA lf) lens_ofs nx rt mx.
  Let st0 := itm_st0 mn nx rt cnt (tblA cf) w1.
  Let R := resA ty lf lens_ofs codes nx bits cf wf.

  Lemma res_phases : R =
    (if mx =? 0 then (0, arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0), nx + 2, 1, workA wf)
     else if itm_reject ty mx (it_left_check cnt) then (-1, tblA cf, nx, bits, workA wf)
     else if it_not_enough ty (itm_used rt) then (1, tblA cf, nx, bits, w1)
     else match it_loop X codes st0 with
          | inr st => (1, t_tbl st, nx, bits, t_work st)
          | inl st => (0, (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0) else t_tbl st),
                       nx + t_used st, rt, t_work st)
          end).
  Proof.
    unfold R, resA. rewrite inflate_table_phases. cbv zeta.
    fold cnt. unfold mxA in mx. fold mx. unfold mnA in mn. fold mn. unfold rootA in rt. fold rt.
    unfold work1A, offsA in w1. fold w1. fold X. fold st0. reflexivity.
  Qed.
End Res.


Ltac destr_conj H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "F" in destruct H as [H1 H]; destr_conj H1; destr_conj H
  | _ => idtac
  end.
Ltac split_conj := repeat match goal with |- _ /\ _ => split end.
