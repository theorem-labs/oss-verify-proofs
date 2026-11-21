(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZTac ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ModelRel ItCovIface ItCovMain.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.

Module S_It0.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ModelRel OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ItableModel OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ItCovIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ItCovMain.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZStep OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ISpecs.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


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


Record itc (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z)
           (p pb sp ret FR zc : Z) : Prop := ITC {
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
  C_room  : nx + it_room ty <= N_CODES;
  C_pb    : pb = p + o_lenbits \/ pb = p + o_distbits;
  C_pal   : p mod 16 = 0;
  C_p0    : 0 < p;
  C_pceil : p + STATE_SIZE <= zc;
  C_sp    : zc + FR <= sp;
  C_zrom  : DEXT_ADDR + 64 <= zc;
  C_sp2   : sp <= 140737488355328;
  C_spal  : sp mod 16 = 0;
  C_prom  : p + STATE_SIZE <= ROM_LO_ALL \/ DEXT_ADDR + 64 <= p;
  C_ret   : Z.land ret (-2) = ret;
  C_ret2  : 0 <= ret < two64 }.

Ltac open_itc C :=
  destruct C as [Hlf Hcf Hwf Hofs Hofs2 Hcodes Hcodes2 Hlens15 HtyC HtyD Hbits Hbits2 Hnx Hroom
                 Hpb Hpal Hp0 Hpceil Hsp Hzrom Hsp2 Hspal Hprom Hret Hret2];
  cbv [N_LENS N_CODES N_WORK STATE_SIZE o_lenbits o_distbits ROM_LO_ALL DEXT_ADDR] in
    Hlf, Hcf, Hwf, Hofs2, Hcodes2, Hroom, Hpb, Hpceil, Hsp, Hzrom, Hprom;
  lazymatch type of Hpb with ?P => change (ZSEP P) in Hpb end;
  lazymatch type of Hprom with ?P => change (ZSEP P) in Hprom end.


Section Safe.
  Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret FR zc : Z).
  Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret FR zc.

  Lemma lensA_get : forall i, arr_get (lensA lf) i = lf i.
  Proof using. intros. apply arr_get_init. Qed.
  Lemma workA_get : forall i, arr_get (workA wf) i = wf i.
  Proof using. intros. apply arr_get_init. Qed.
  Lemma tblA_get : forall i, arr_get (tblA cf) i = cf i.
  Proof using. intros. apply arr_get_init. Qed.

  Lemma it_safe_ok : it_safe ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf) = true.
  Proof using C zc FR ret sp pb p.
    destruct C.
    apply it_safe_true; unfold lensA, tblA, workA; rewrite ?arr_len_init.
    all: cbv [N_WORK N_LENS N_CODES] in *; try lia.
    - intros s Hs. rewrite arr_get_init. pose proof (C_lf0 (lens_ofs + s) ltac:(lia)).
      pose proof (C_lens16 s Hs). lia.
    - intros H. dand (C_tyC0 H) as (A & B & D). split; [exact A|]. split; [exact B|].
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
  Proof using.
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

Lemma land_le_l : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros a b Ha Hb.
  pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as Hal.
  rewrite Z.lor_ldiff_and in Hal.
  assert (Hand : Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  rewrite Hand in Hal.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia_std). lia_std.
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
  remember (Z.to_nat n) as m eqn:Hm. replace n with (Z.of_nat m) by lia_std. assert (Hm1 : (1 <= m)%nat) by lia_std. clear n Hn Hm.
  revert curr lft Hc Hcd. induction m as [|m IH]; intros curr lft Hc Hcd; [lia_std|].
  destruct (Z_lt_le_dec (curr + drop) max).
  - destruct (Z_lt_le_dec 0 (lft - arr_get count (curr + drop))).
    + rewrite curr_more by lia_std. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia_std.
      destruct m as [|m'].
      * rewrite loopZ_le0 by lia_std. cbn [fst]. lia_std.
      * specialize (IH ltac:(lia_std) (curr + 1) (Z.shiftl (lft - arr_get count (curr + drop)) 1) ltac:(lia_std) ltac:(lia_std)). lia_std.
    + rewrite curr_stop_le by lia_std. cbn [fst]. lia_std.
  - rewrite curr_stop_ge by lia_std. cbn [fst]. lia_std.
Qed.

Lemma it_fill_len_tr : forall x st, arr_len (tr_tbl1 x st) = arr_len (t_tbl st).
Proof. intros. unfold tr_tbl1. apply it_fill_len. Qed.

Lemma code_pack_range : forall op bits val, 0 <= code_pack op bits val < 4294967296.
Proof.
  intros. unfold code_pack.
  pose proof (wrap16_range val) as A. change (2 ^ 16) with 65536 in A.
  assert (W8 : forall z, 0 <= wrap8 z < 256).
  { intros z. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia_std. apply Z.mod_pos_bound. lia_std. }
  pose proof (W8 op). pose proof (W8 bits). lia_std.
Qed.
Lemma fill_get_cases : forall here incr hd next n f t j,
  arr_get (snd (loopZ n (fill_body here incr hd next) (f, t))) j = here \/
  arr_get (snd (loopZ n (fill_body here incr hd next) (f, t))) j = arr_get t j.
Proof.
  intros here incr hd next n. destruct (Z_lt_le_dec 0 n) as [Hn|Hn].
  2:{ intros. rewrite loopZ_le0 by lia_std. cbn [snd]. right. reflexivity. }
  remember (Z.to_nat n) as m eqn:Hm. replace n with (Z.of_nat m) by lia_std. clear n Hn Hm.
  induction m as [|m IH]; intros f t j.
  - rewrite loopZ_le0 by lia_std. right. reflexivity.
  - destruct (Z.eq_dec (wrap32 (f - incr)) 0) as [E|E].
    + rewrite fill_last by first [lia_std | exact E]. cbn [snd]. rewrite arr_get_set. destruct (_ && _); [left | right]; reflexivity.
    + rewrite fill_more by first [lia_std | exact E]. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia_std.
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
  pose proof (wrap16_range (arr_get (t_count st) (t_len st) - 1)) as W. change (2 ^ 16) with 65536 in W. unfold tr_c. lia_std.
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
  Proof using.
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

Ltac zkeys := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6
                   o_strm o_mode o_last o_wrap o_havedict o_flags o_dmax o_check o_total o_head o_wbits
                   o_wsize o_whave o_wnext o_window o_hold o_bits o_length o_offset o_extra o_lencode
                   o_distcode o_lenbits o_distbits o_ncode o_nlen o_ndist o_shave o_next o_lens o_work
                   o_codes o_sane o_back o_was STATE_SIZE N_LENS N_WORK N_CODES WIN_SIZE
                   ORDER_ADDR LENFIX_ADDR DISTFIX_ADDR LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR JTAB_ADDR MOD31_ADDR
                   FRA ROM_LO_ALL] in *.

Ltac zregv := cbv [zget_l kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                  kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6];
             cbn [alookup Pos.eqb]; rewrite ?zget_zupd; cbv [zget_l]; cbn [alookup Pos.eqb];
             zrefold_getl; zbase.
Ltac zreg := zregv; first [ reflexivity | assumption | OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ITac.zarith_goal; lia ].
Ltac hyp := lazymatch goal with |- ?G => match goal with Hh : G |- _ => exact Hh end end.
End S_It0.

Module S_It1.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ITac.
Import S_It0.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

(* THE LIST FORM's WORD OF THIS TEXT is the quantities text's: a layout's register list (a list of
   registers) is read with the list of values that a statement binds, place by place. *)

(* an opener: the layout's fields that this text reads are unfolded, everywhere *)
Ltac lay_it3 :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ITABLE
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_COUNT OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_CLOOP OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAXE
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX14 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX13 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX12
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX11 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX10 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX9
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX8 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX7 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX6
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX5 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX4 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX3
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_ROOT OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_ROOT1
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MINLOOP OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MINDONE OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_LEFT
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZBIB_LOOP OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_FILL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_FLOOP
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_INCR OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_ILOOP OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_IDONE
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_ST1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZBIB_BRK OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_LOW
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZBIB_MAX0
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SP OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV8 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV9
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV18 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV19 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV20
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV21 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV22 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV23
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV24 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV25 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV26
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV27
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_entry OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_p OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_cloop
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_kmax OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_mloop
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_mdone OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_left] in *.
(* an opener: every list-form hypothesis: the meaning word unfolded, the conjunction split *)
Ltac open_rvals :=
  lay_it3; repeat match goal with
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv _ _ _ _ |- _ => progress (cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv] in H); destr_conj H
         end.
(* the same for a goal *)
Ltac split_rvals := lazymatch goal with |- OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv _ _ _ _ => lay_it3; cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv]; split_conj end.

Ltac zmem_transport_loop_S_It3 M a bs :=
  repeat match goal with
  | H : mem_arr ?k ?segs M ?base ?n ?f |- _ =>
      first [ apply (mem_arr_frame segs k M base n f a bs) in H; [|unfold zdisj; zlen_norm; zlia]
            | let kn := eval cbv in (Z.to_nat k) in
              lazymatch bs with
              | Z_to_le_bytes kn ?v =>
                  let e := zstrip_base a base in
                  let x := zdivk e k in
                  apply (mem_arr_upd segs k M base n f a x v) in H; [| zlia | zlia];
                  change (Z.to_nat k) with kn in H
              end
            | clear H ]
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 8;
      first [ apply (mem_u64_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 4;
      first [ apply (mem_u32_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 2;
      first [ apply (mem_u16_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 1;
      first [ apply (mem_u8_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      zrng_ensure a' (Z.of_nat (length bs'));
      first [ apply (mem_is_frame segs M a bs a' bs') in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      apply (mem_wr_frame segs M a bs a' len) in H
  | H : rom_ok M |- _ =>
      first [ apply (rom_ok_frame M a bs) in H; [| zlia | zlen_norm; zlia | unfold ROM_LO, ROM_HI; zdisj_tac]
            | clear H ]
  | H : framed ?Fr M, HS : wb_stable ?Fr ?lo ?hi |- _ =>
      first [ apply (HS M a bs) in H; [|zlia|zlen_norm; zlia]
            | clear H ]
  | H : framed ?Fr M, HS : wb_stable2 ?Fr _ _ _ _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; zlia]
            | clear H ]
  | H : framed ?Fr M, HS : wb_stableL ?Fr _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; in_some_tac]
            | clear H ]
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.
Ltac zmem_transport M a bs ::=
  zxfer_pre a bs;
  zmem_transport_loop_S_It3 M a bs;
  zxfer_post a.


Lemma mem_arr2_zero16 {RCa1 : RunCtx}  : forall M a,
  0 <= a -> a + 32 <= two64 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (a + 8) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (a + 16) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (a + 24) 0 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M a 16 (fun _ => 0).
Proof.
  intros M a Ha Ha2 H0 H1 H2 H3.
  apply mem_arr_of_elems; [lia | lia | lia | lia |].
  intros i Hi. change (Z.to_nat 2) with 2%nat.
  assert (E : forall b j, mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M b 0 -> 0 <= j < 4 -> mem_is (run_segments R_segs rc_inp rc_sp rc_mb) M (b + 2 * j) (Z_to_le_bytes 2 0)).
  { intros b j Hb Hj. unfold mem_u64 in Hb.
    pose proof (mem_is_sub (run_segments R_segs rc_inp rc_sp rc_mb) M b (Z_to_le_bytes 8 0) (2 * j) 2 Hb ltac:(lia) ltac:(cbn; lia)) as X.
    unfold mem_is. cbn [length Z_to_le_bytes]. rewrite X.
    assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
    destruct J as [-> | [-> | [-> | ->]]]; reflexivity. }
  assert (C : i < 4 \/ (4 <= i < 8) \/ (8 <= i < 12) \/ 12 <= i) by lia.
  destruct C as [C | [C | [C | C]]].
  - apply (E a i H0). lia.
  - replace (a + 2 * i) with (a + 8 + 2 * (i - 4)) by lia. apply (E (a + 8) (i - 4) H1). lia.
  - replace (a + 2 * i) with (a + 16 + 2 * (i - 8)) by lia. apply (E (a + 16) (i - 8) H2). lia.
  - replace (a + 2 * i) with (a + 24 + 2 * (i - 12)) by lia. apply (E (a + 24) (i - 12) H3). lia.
Qed.


Lemma shl1_x2 : forall c, Z.shiftl c 1 = 2 * c.
Proof. intros c. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma snez_pos : forall c, 0 < c < 18446744073709551616 -> Z.b2z (0 <? c mod 18446744073709551616) = 1.
Proof.
  intros c Hc. rewrite Z.mod_small by lia.
  replace (0 <? c) with true; [reflexivity | symmetry; apply Z.ltb_lt; lia].
Qed.
Section Prologue.
Context {RCa1 : RunCtx}.

(* THE LIST FORM: the entry's registers hold the values that the statement binds; the continuation's registers,
   the frame's distances and the two labels are the layout's fields *)
Lemma it_prologue_L : forall Rb l M MD T (sp v1 v4 v5 v8 v9 v10 v11 v12 v13 v14 v15 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : Z),
  m_halted MD = None ->
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_entry
    [sp; v1; v4; v5; v8; v9; v10; v11; v12; v13; v14; v15; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27] ->
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT <= sp -> sp <= 140737488355328 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT ->
  (forall R' M',
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_p [sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SP; v4; v5; v10; v11; v12; v13; v14; v15] ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SP) sp 0 0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV1) v1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV8) v8 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV9) v9 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV18) v18 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV19) v19 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV20) v20 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV21) v21 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV22) v22 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV23) v23 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV24) v24 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV25) v25 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV26) v26 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SV27) v27 ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 (fun _ => 0) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_COUNT (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ITABLE (zupd Rb l) M MD) T.
Proof using.
  intros Rb l M MD T sp v1 v4 v5 v8 v9 v10 v11 v12 v13 v14 v15 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
         Hh HR Hsp Hsp2 Wf K.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SP) sp 0 0 ltac:(lay_it3; lia) ltac:(lay_it3; rewrite two64_eq; lia) ltac:(lay_it3; lia) ltac:(lay_it3; rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SP) sp 0 0) M) by (apply mpost_refl).
  lay_it3. open_rvals.
  zkeys. idtac.
  zrebase.
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?MX _) _ => eapply (K RR MX) end).
  all: try split_rvals.
  all: try zreg.
  all: try assumption.
  apply mem_arr2_zero16; [lia | rewrite two64_eq; lia | assumption | | | ].
  all: match goal with |- mem_u64 _ _ ?a 0 => zfold; assumption end.
Qed.
End Prologue.

Ltac clear_regs := repeat match goal with H : zget _ _ = _ |- _ => clear H | H : zget_l _ _ _ = _ |- _ => clear H end.

(* the registers that hold the function's arguments, in the list form: the layout's register list with
   the values in its order *)
Definition pregsL (p lens_ofs codes pb sp vgp vtp tyv : Z) (R : tree Z) (l : list (positive * Z)) : Prop :=
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv R l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_p
    [sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SP; vgp; vtp; tyv; p + 168 + 2 * lens_ofs; codes; p + 160; pb; p + 808].

Ltac open_pregsL H := unfold pregsL in H;
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_p OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SP] in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let f := fresh "LA2" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in dand H as (a & b & c & d & e & f & g & h & i).
Ltac close_pregsL := unfold pregsL;
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_p OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_SP]; split_conj; zreg.

Section S7IT.
Context {RCa1 : RunCtx}.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT zc.

#[local] Abbreviation PRL := (pregsL p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cnt i := (arr_get (cntK lf lens_ofs i)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).


Lemma cA_range : forall j, 0 <= cA j <= codes.
Proof using C zc ret sp pb p wf cf bits nx ty. intros j. destruct C. rewrite cntA_eq. pose proof (cntK_le lf lens_ofs codes j ltac:(lia) ltac:(lia)). lia. Qed.

Lemma count_loop_s : forall fuel i Rb l M MD T,
  (Z.to_nat (codes - i) <= fuel)%nat -> 0 <= i < codes ->
  m_halted MD = None -> PRL Rb l ->
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_cloop
    [p + 168 + 2 * lens_ofs + 2 * i; p + 168 + 2 * lens_ofs + 2 * codes; sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT] ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 (cnt i) ->
  (forall R' M',
     PRL R' [] -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT] ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END) 0 0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 (cnt codes) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAXE (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_CLOOP (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  induction fuel as [|fuel IH]; intros i Rb l M MD T Hfuel Hi Hh HP HR Wf Hlens Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END) 0 0 ltac:(lay_it3; lia) ltac:(lay_it3; rewrite two64_eq; lia) ltac:(lay_it3; lia) ltac:(lay_it3; rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END) 0 0) M) by (apply mpost_refl).
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  pose proof (Hlens15 i ltac:(lia)) as Hl15. pose proof (Hlf (lens_ofs + i) ltac:(lia)) as Hl16.
  assert (HCr1 : forall j, 0 <= j < 16 -> -32768 <= cnt i j < 32768).
  { intros j _. pose proof (cntK_le lf lens_ofs i j ltac:(lia) ltac:(lia)). lia. }
  zrebase.
  zto_branch_h Rfd (first [ zhint shl1_x2 ]).
  apply mem_arr_arr_set in Hcnt; [|rewrite cntK_len; lia].
  rewrite <- (cntK_step lf lens_ofs i) in Hcnt by lia.
  destruct (Z.eq_dec (i + 1) codes) as [Hend|Hmore].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?MX _) _ => eapply (K RR MX) end).
    all: try split_rvals.
    all: try first [close_pregsL | zreg | assumption].
    rewrite <- Hend. exact Hcnt.
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?MX _) _ =>
      eapply (IH (i + 1) RR [] MX MD T) end).
    all: try split_rvals.
    all: try first [lia | assumption | close_pregsL | zreg].
    intros R' M'. intros. eapply K; try eassumption.
    eapply mpost_trans; [exact HAG | assumption].
Qed.

Lemma count_phase_L : forall Rb l M MD T,
  0 < codes -> m_halted MD = None -> PRL Rb l ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 (fun _ => 0) ->
  (forall R' M',
     PRL R' [] -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT] ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END) 0 0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAXE (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_COUNT (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T Hc0 Hh HP Wf Hlens Hcnt K.
  pose proof C as C'. open_itc C'.
  pose proof (count_loop_s (Z.to_nat codes) 0) as CL.
  assert (Hcnt0 : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 (cnt 0)).
  { eapply mem_arr_ext; [exact Hcnt|]. intros j Hj. cbn beta. unfold cntK. rewrite itm_count_k_0 by lia.
    rewrite it_zero_count_spec. reflexivity. }
  clear Hcnt.
  lay_it3. open_pregsL HP. zkeys. zrebase.
  pose proof (zext32_x2 codes ltac:(lia)) as EX. zuntil Rfd
    (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?MX _) _ =>
      eapply (CL RR [] MX MD T) end).
  all: try split_rvals.
  all: try first [lia | assumption | close_pregsL | zreg].
  all: intros; rewrite cntA_eq in K; eapply K; eassumption.
Qed.


(* two continuations, in the list form *)
Definition KmaxL (bitsv : Z) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PRL R' [] -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_kmax [bitsv; mx; cA 15] ->
    2 <= mx -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_ROOT (zupd R' []) M MD) T.
Definition KlowL (bitsv : Z) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PRL R' [] -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] -> (forall j, 2 <= j <= 15 -> cA j = 0) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_LOW (zupd R' []) M MD) T.

Lemma max_stage_2 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 2 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX2 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 2) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 2) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KL RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 2) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 2); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 2); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_3 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 3 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX3 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_2 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 3) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 3) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 3) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 3); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 3); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_4 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 4 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX4 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_3 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 4) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 4) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 4) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 4); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 4); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_5 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 5 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX5 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_4 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 5) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 5) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 5) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 5); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 5); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_6 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 6 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX6 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_5 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 6) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 6) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 6) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 6); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 6); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_7 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 7 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX7 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_6 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 7) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 7) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 7) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 7); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 7); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_8 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 8 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX8 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_7 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 8) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 8) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 8) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 8); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 8); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_9 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 9 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX9 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_8 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 9) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 9) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 9) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 9); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 9); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_10 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 10 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX10 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_9 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 10) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 10) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 10) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 10); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 10); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_11 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 11 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX11 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_10 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 11) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 11) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 11) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 11); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 11); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_12 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 12 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX12 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_11 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 12) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 12) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 12) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 12); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 12); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_13 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 13 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX13 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_12 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 13) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 13) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 13) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 13); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 13); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_14 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bitsv] ->
  (forall j, 14 < j <= 15 -> cA j = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KmaxL bitsv M MD T -> KlowL bitsv M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAX14 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP HR Hz Hcnt KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. pose proof KL0 as KL. unfold KmaxL in KF. unfold KlowL in KL.
  pose proof max_stage_13 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 14) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 14) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bitsv) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 14) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 14); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 14); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_entry_L : forall Rb l M MD T av,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [av] ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M pb bits ->
  KmaxL bits M MD T -> KlowL bits M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MAXE (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T av Hh HP HR Hcnt HB32 KF0 KL0.
  pose proof C as C'. open_itc C'.
  pose proof KF0 as KF. unfold KmaxL in KF.
  pose proof max_stage_14 as NX.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 15) as HRk.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 15) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bits) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    intros jj Hjj. replace jj with 15 by lia. exact Z0.
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KF RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 15); [lia | intros; lia | exact NZ].
    + unfold mxA. rewrite (mx_found _ 15); [lia | lia | intros; lia | exact NZ].
Qed.

#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).


(* two continuations, in the list form *)
Definition KleftL (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PRL R' [] ->
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_left [mx; mn; rt; (if mx =? 1 then 0 else 1); cA 15] -> 1 <= mx ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_LEFT (zupd R' []) M MD) T.
Definition Kmax0L (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PRL R' [] -> mx = 0 -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZBIB_MAX0 (zupd R' []) M MD) T.

Lemma mxmn_facts : 1 <= mx -> 1 <= mn <= mx /\ mx <= 15 /\ 1 <= rt <= 15 /\ mn <= rt /\
  rt = (let r := (if bits <? mx then bits else mx) in if mn <? r then r else mn).
Proof using C zc ret sp pb p wf cf nx ty.
  intros H1. pose proof C as C'. open_itc C'. pose proof (mx_range (cntA lf lens_ofs codes)) as MR.
  pose proof (mn_range (cntA lf lens_ofs codes) mx ltac:(unfold mxA in *; lia)) as NR.
  unfold rootA, itm_root. unfold mnA in *. unfold mxA in *.
  set (mxv := itm_max (cntA lf lens_ofs codes)) in *. set (mnv := itm_min (cntA lf lens_ofs codes) mxv) in *.
  destruct (Z.ltb_spec mxv bits); destruct (Z.ltb_spec bits mxv); try lia_std;
    destruct (Z.ltb_spec mxv mnv); destruct (Z.ltb_spec bits mnv); destruct (Z.ltb_spec mnv mxv); destruct (Z.ltb_spec mnv bits); cbv zeta; lia_std.
Qed.

Lemma min_loop_s : forall fuel m Rb l M MD T r7,
  (Z.to_nat (mx - m) <= fuel)%nat -> 1 <= m < mx -> 2 <= mx <= 15 ->
  (forall jj, 1 <= jj < m -> cA jj = 0) ->
  m_halted MD = None -> PRL Rb l ->
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_mloop
    [m; sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT + 2 * m; mx - m; mx; r7; 1; cA 15] ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  (forall R', PRL R' [] -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_mdone [mn; mx; r7; 1; cA 15] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MINDONE (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_MINLOOP (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  induction fuel as [|fuel IH]; intros m Rb l M MD T r7 Hfuel Hm Hmx2 Hz Hh HP HR Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range m) as HRm.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA m) 0) as [Z0|NZ].
  - zto_branch Rfd.
    destruct (Z.eq_dec (m + 1) mx) as [Hlast|Hmore].
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (K RR) end).
      all: try split_rvals.
      all: try first [assumption | close_pregsL | zreg].
      zregv. symmetry. unfold mnA. apply mn_all; [lia|].
      intros jj Hjj. destruct (Z.eq_dec jj m) as [->|]; [exact Z0 | apply Hz; lia].
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (IH (m + 1) RR [] M MD T r7) end).
      all: try split_rvals.
      all: try first [lia | assumption | close_pregsL | zreg].
      intros jj Hjj. destruct (Z.eq_dec jj m) as [->|]; [exact Z0 | apply Hz; lia].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (K RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    zregv. symmetry. unfold mnA. apply mn_found; [lia | lia | exact Hz | exact NZ].
Qed.

Lemma rootmin_L : forall Rb l M MD T,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_kmax [bits; mx; cA 15] ->
  2 <= mx ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KleftL M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_ROOT (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T Hh HP HR Hmx2 Hcnt KL0.
  pose proof C as C'. open_itc C'.
  pose proof (mxmn_facts ltac:(lia)) as (MN1 & MX15 & RT & MNRT & RTEQ).
  pose proof KL0 as KL. unfold KleftL in KL.
  pose proof (min_loop_s (Z.to_nat mx) 1) as ML.
  assert (STEP : forall r7, r7 = (if bits <? mx then bits else mx) -> 1 <= r7 <= 15 ->
    forall Rx lx, m_halted MD = None -> PRL Rx lx -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rx lx OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_kmax [r7; mx; cA 15] ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_ROOT1 (zupd Rx lx) M MD) T).
  { intros r7 Hr7 Hr7b Rx lx Hh' HP' HR'. lay_it3. open_rvals. open_pregsL HP'. zkeys. zrebase.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (ML RR [] M MD T r7) end).
    all: try split_rvals.
    all: try first [lia | assumption | close_pregsL | zreg].
    intros R' HP2 HR2. open_rvals. open_pregsL HP2. zkeys. zrebase.
    destruct (Z.ltb_spec mn r7).
    - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KL RR) end).
      all: try split_rvals.
      all: try first [assumption | close_pregsL | zreg].
      + zregv. rewrite RTEQ. cbv zeta. subst r7. destruct (Z.ltb_spec mn (if bits <? mx then bits else mx)); lia.
      + zregv. destruct (Z.eqb_spec mx 1); lia.
    - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KL RR) end).
      all: try split_rvals.
      all: try first [assumption | close_pregsL | zreg].
      + zregv. rewrite RTEQ. cbv zeta. subst r7. destruct (Z.ltb_spec mn (if bits <? mx then bits else mx)); lia.
      + zregv. destruct (Z.eqb_spec mx 1); lia. }
  lay_it3. open_rvals. open_pregsL HP. zkeys. zrebase.
  destruct (Z.ltb_spec bits mx).
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (STEP bits _ _ RR []) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    all: destruct (Z.ltb_spec bits mx); lia.
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (STEP mx _ _ RR []) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    all: destruct (Z.ltb_spec bits mx); lia.
  Unshelve. all: lia.
Qed.

Lemma maxlow_L : forall Rb l M MD T,
  m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [bits] ->
  (forall jj, 2 <= jj <= 15 -> cA jj = 0) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA ->
  KleftL M MD T -> Kmax0L M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_LOW (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T Hh HP HV Hz Hcnt KL0 K00.
  pose proof C as C'. open_itc C'.
  pose proof KL0 as KL. unfold KleftL in KL. pose proof K00 as K0. unfold Kmax0L in K0.
  lay_it3. open_rvals. open_pregsL HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 1) as HR1. pose proof (Hz 15 ltac:(lia)) as Z15.
  zrebase.
  zto_branch Rfd.
  destruct (Z.eq_dec (cA 1) 0) as [Z0|NZ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (K0 RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    unfold mxA. apply mx_zero. intros jj Hjj. destruct (Z.eq_dec jj 1) as [->|]; [exact Z0 | apply Hz; lia].
  - assert (MX1 : mx = 1) by (unfold mxA; apply (mx_found _ 1); [lia | intros jj Hjj; apply Hz; lia | exact NZ]).
    pose proof (mxmn_facts ltac:(lia)) as (MN1 & MX15 & RT & MNRT & RTEQ).
    zuntil_h Rfd (first [ zhint snez_pos ])
      (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (KL RR) end).
    all: try split_rvals.
    all: try first [assumption | close_pregsL | zreg].
    + zregv. rewrite RTEQ, MX1. cbv zeta. destruct (Z.ltb_spec bits 1); destruct (Z.ltb_spec mn 1); destruct (Z.ltb_spec mn bits); lia.
    + zregv. rewrite MX1. reflexivity.
Qed.

Lemma count_phase0_L : forall Rb l M MD T av,
  codes = 0 -> m_halted MD = None -> PRL Rb l -> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keys_it3_a7 [av] ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 (fun _ => 0) -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M pb bits ->
  Kmax0L M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_COUNT (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T av Hc0 Hh HP HV Hcnt HB32 K0.
  pose proof C as C'. open_itc C'.
  assert (ZALL : forall jj, cA jj = 0).
  { intros jj. rewrite cntA_eq, Hc0. unfold cntK. rewrite itm_count_k_0 by lia. apply it_zero_count_spec. }
  assert (MX0 : mx = 0) by (unfold mxA; apply mx_zero; intros; apply ZALL).
  assert (Hcnt' : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 cA).
  { eapply mem_arr_ext; [exact Hcnt|]. intros jj Hjj. cbn beta. symmetry. apply ZALL. }
  pose proof max_stage_14 as NX. pose proof maxlow_L as MLW.
  lay_it3. open_rvals. open_pregsL HP. zkeys. zrebase.
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => eapply (NX RR [] M MD T bits) end).
  all: try split_rvals.
  all: try first [assumption | close_pregsL | zreg].
  - intros; apply ZALL.
  - intros R'; intros; exfalso; lia.
  - intros R' HP' HV' HZ'. eapply MLW; try eassumption.
    all: try (intros; apply ZALL).
    all: try (lay_it3; open_rvals; split_rvals; zkeys; assumption).
    all: intros R''; intros; exfalso; lia.
Qed.
End S7IT.
End S_It1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import Base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require Import ZTac ZArr ZArr4 IDefs ISpecs ITac.
Import S_It0. Import S_It1.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

Definition lowS (z : Z) : Z := if z =? 4294967295 then -1 else z.

Definition NE (ty : codetype) : Z := match ty with CODES => 288 | LENS => 31 | DISTS => 32 end.
Definition isL (ty : codetype) : Z := match ty with LENS => 1 | _ => 0 end.
Definition isD (ty : codetype) : Z := match ty with DISTS => 1 | _ => 0 end.

Lemma NE_ext_len : forall ty, NE ty = it_ext_len ty 288.
Proof. destruct ty; reflexivity. Qed.


Lemma pow2_le15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof.
  intros k Hk. split. - change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia. - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.
Lemma sllw_1 : forall k, 0 <= k <= 15 -> bv_swrap 32 (Z.shiftl 1 (k mod 32)) = 2 ^ k.
Proof.
  intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. pose proof (pow2_le15 k Hk). apply swrap32_small. lia.
Qed.
Lemma sllw_m1 : forall k, 0 <= k <= 15 -> bv_swrap 32 (Z.shiftl (-1) (k mod 32)) = - 2 ^ k.
Proof.
  intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. pose proof (pow2_le15 k Hk).
  rewrite swrap32_small by lia. lia.
Qed.
Lemma srlw_small : forall a b, 0 <= a < 2147483648 -> 0 <= b < 32 ->
  bv_swrap 32 (Z.shiftr (a mod 4294967296) (b mod 32)) = Z.shiftr a b.
Proof.
  intros a b Ha Hb. rewrite !Z.mod_small by lia.
  assert (0 <= Z.shiftr a b <= a).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  apply swrap32_small. lia.
Qed.
Lemma mul_S_sub : forall a m, a * Z.of_nat (S m) - a = a * Z.of_nat m.
Proof. intros. rewrite Nat2Z.inj_succ. ring. Qed.
Lemma mul_S_ge : forall a m, 0 <= a -> a <= a * Z.of_nat (S m).
Proof. intros. rewrite Nat2Z.inj_succ. nia. Qed.

Lemma wrap8_mod : forall z, wrap8 z = z mod 256.
Proof. intros z. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

(* HINT LEMMAS (new in the run form: each is the equation that a value replacement of the hand text proved in
   place: machine form = nicer form; a run's hint names the lemma) *)
Lemma srliw_shiftr : forall x k, 0 <= x < 4294967296 -> 0 < k < 32 ->
  bv_swrap 32 (Z.shiftr (x mod 4294967296) k) = Z.shiftr x k.
Proof.
  intros x k Hx Hk. rewrite (srliw_small x k Hx Hk). rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma seqz_b2z : forall x m, 0 <= x < m -> Z.b2z (x mod m <? 1) = Z.b2z (x =? 0).
Proof.
  intros x m Hx. rewrite (Z.mod_small x m) by lia.
  destruct (Z.eqb_spec x 0); destruct (Z.ltb_spec x 1); cbn [Z.b2z]; lia.
Qed.
Lemma shl1_x2 : forall x, Z.shiftl x 1 = 2 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma shl48_dec : forall x, Z.shiftl x 48 + -281474976710656 = (x + -1) * 281474976710656.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 48) with 281474976710656. lia. Qed.
Lemma sym_next : forall st, 0 <= t_sym st + 1 < 4294967296 -> t_sym st + 1 = tr_sym st.
Proof. intros st Hs. unfold tr_sym. symmetry. apply wrap32_small. exact Hs. Qed.
Lemma huff_next : forall st a b, a = tr_incr2 st - 1 -> b = Z.b2z (tr_incr2 st =? 0) + -1 ->
  Z.land b (Z.land a (t_huff st) + tr_incr2 st) = tr_huff st.
Proof.
  intros st a b -> ->. symmetry.
  unfold tr_huff. destruct (Z.eqb_spec (tr_incr2 st) 0) as [E0|NE0]; cbn [Z.b2z negb Z.add].
  - symmetry. apply Z.land_0_l.
  - rewrite Z.land_m1_l. rewrite Z.land_comm. reflexivity.
Qed.

(* THE TWO TABLES' ADDRESSES BY THE KIND OF CODE: the layout's fields hold the addresses *)
Definition EXA_l (ty : codetype) (p : Z) : Z :=
  match ty with CODES => p + 808 | LENS => OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_it3b_lext | DISTS => OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_it3b_dext end.
Definition BSA_l (ty : codetype) (p : Z) : Z :=
  match ty with CODES => p + 808 | LENS => OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_it3b_lbase | DISTS => OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_it3b_dbase end.
Definition EXAn_l (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | _ => EXA_l ty p end.
Definition BSAn_l (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | _ => BSA_l ty p end.
Lemma EXAn_l_ne : forall ty p, ty <> CODES -> EXAn_l ty p = EXA_l ty p. Proof. intros [] p H; [congruence|reflexivity|reflexivity]. Qed.
Lemma BSAn_l_ne : forall ty p, ty <> CODES -> BSAn_l ty p = BSA_l ty p. Proof. intros [] p H; [congruence|reflexivity|reflexivity]. Qed.

Section S7IT3.
Context {RCa1 : RunCtx}.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT zc.

#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).

Definition spure_l (st : ItSt) : Prop :=
  t_work st = work1Ar /\ ZSEP (t_low st = 4294967295 \/ 0 <= t_low st < 32768) /\ ZSEP (t_drop st = 0 \/ t_drop st = rt) /\
  0 <= t_next st /\ nx <= t_next st /\
  (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) /\
  (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) /\
  arr_len (t_count st) = 16 /\ arr_len (t_tbl st) = 1444.

(* THE LIST FORM OF THIS SECTION's STATEMENTS. A register list of the layout says which value of a VALUE LIST each
   register holds; the statement writes the value list. `it3b_cvals`: the values that every place of the table's
   main loop keeps (the frame's base, the two thread registers, the lengths' address, the address of the table
   pointer's field, the bits pointer, the work array's address, the root, the longest length, the match value, the
   two tables' addresses, the root's mask). `it3b_svals st`: the model state's values (the symbol's index, the
   length, the dropped bits, the used count, the code, the next entry's address, the sub-table's size, the low
   bits). *)
Definition it3b_cvals : list Z :=
  [sp; vgp; vtp; p + 168 + 2 * lens_ofs; p + 160; pb; p + 808; rt; mx; it_match ty; EXAn_l ty p; BSAn_l ty p; 2 ^ rt - 1].
Definition it3b_svals (st : ItSt) : list Z :=
  [t_sym st; t_len st; t_drop st; t_used st; t_huff st; p + 1384 + 4 * t_next st; 2 ^ t_curr st; lowS (t_low st)].
Definition cregsN_l (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  rholds (qargs it3b_cvals) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_c.
Definition sregs_l (st : ItSt) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  rholds (qargs (it3b_svals st)) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_s.
Definition cmem_l (M : mem) : Prop :=
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT /\
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 (arr_get work1Ar) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 160) (p + 1384 + 4 * nx) /\
  fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs [isD ty; isL ty]) M sp OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.fr_it3b_sl /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (EXA_l ty p) (NE ty) (it_extra ty work1Ar) /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (BSA_l ty p) (NE ty) (it_base ty work1Ar).
Definition smem_l (st : ItSt) (M : mem) : Prop :=
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 (arr_get (t_count st)) /\
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (t_tbl st)).
Ltac open_spure H :=
  unfold spure_l in H;
  let a := fresh "WK" in let b := fresh "LOWR" in let b2 := fresh "DROPR" in let c := fresh "NX0" in let d := fresh "NX1" in
  let e := fresh "HCr" in let f := fresh "HTr" in let g := fresh "CL" in let h := fresh "TL" in
  dand H as (a & b & b2 & c & d & e & f & g & h).

(* OPENERS AND CLOSERS OF THE LIST FORM (an opener only unfolds, splits and names). `open_lists`: every
   list-form hypothesis: the meaning over the layout's list is unfolded and the conjunction split.
   `split_lists`: the same for a goal. `it3b_fields`: the layout's labels and frame integers of this section
   are unfolded everywhere (the runs need numerals); `it3b_g`: in the goal only. *)
Ltac open_lists :=
  repeat match goal with
         | H : cregsN_l _ _ |- _ =>
             cbv [cregsN_l rholds qargs nth fst snd it3b_cvals OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_c] in H; destr_conj H
         | H : sregs_l _ _ _ |- _ =>
             cbv [sregs_l rholds qargs nth fst snd it3b_svals OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_s] in H; destr_conj H
         | H : rholds _ _ _ _ |- _ =>
             cbv [rholds qargs nth fst snd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_ov OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_hb
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_floop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_incr
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_incrk] in H; destr_conj H
         end.
Ltac split_lists :=
  cbv [cregsN_l sregs_l rholds qargs nth fst snd it3b_cvals it3b_svals
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_c OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_s
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_ov OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_hb
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_floop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_incr
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_incrk];
  split_conj.
Ltac open_cmem_l H :=
  cbv [cmem_l fholds fhold1 fs_off fs_width fs_quant qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.fr_it3b_sl] in H;
  destr_conj H;
  repeat match goal with H' : mem_u64 _ _ _ _ /\ _ |- _ => destr_conj H' end.
Ltac it3b_fields :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZBIB_LOOP OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_FILL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_FLOOP
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_INCR OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_ILOOP OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_IDONE
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_ST1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZBIB_BRK] in *.
Ltac it3b_g :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_IT OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END].
Ltac close_cmem_l :=
  cbv [cmem_l fholds fhold1 fs_off fs_width fs_quant qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.fr_it3b_sl];
  split_conj; assumption.
Ltac close_sregs1_l EL :=
  cbv [sregs_l rholds qargs nth fst snd it3b_svals OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_s];
  cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]; rewrite ?EL; split_conj; zreg.
(* the closing word of the runs' continuations *)
Ltac kauto := first
  [ assumption
  | lazymatch goal with
    | |- cregsN_l _ _ => split_lists; zreg
    | |- sregs_l (tr_st1 _ _) _ _ => fail
    | |- sregs_l _ _ _ => split_lists; zreg
    | |- rholds _ _ _ _ => split_lists; zreg
    | |- zget_l _ _ _ = _ => zreg
    | |- zget _ _ = _ => zreg
    | |- m_halted _ = _ => assumption
    end ].

Lemma work1_range : forall j, 0 <= j < 288 -> 0 <= arr_get work1Ar j < 65536.
Proof using C zc ret sp pb p cf bits nx ty.
  intros j Hj. pose proof C as C'. open_itc C'. unfold work1A. rewrite itm_work_eq.
  apply (sort_k_work_range _ _ _ _ _ 288); [|exact Hj]. intros i Hi. rewrite workA_get. apply Hwf. exact Hi.
Qed.

Lemma rt_facts : 1 <= mx -> 1 <= rt <= 15 /\ mn <= rt <= mx /\ 1 <= mn.
Proof using C zc ret sp pb p wf cf nx ty.
  intros H. pose proof (mxmn_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C H) as (A & B & D & E & F). cbv zeta in F.
  destruct (Z.ltb_spec bits mx); [destruct (Z.ltb_spec mn bits) | destruct (Z.ltb_spec mn mx)]; lia_std.
Qed.

Lemma mx15 : 0 <= mx <= 15.
Proof using. unfold mxA. apply mx_range. Qed.


Lemma base_range : forall j, 0 <= j < NE ty -> 0 <= it_base ty work1Ar j < 65536.
Proof using C zc ret sp pb p cf bits nx.
  intros j Hj. pose proof (work1_range j) as W.
  destruct ty; cbn [it_base NE] in *; [apply W; lia_std | apply lbase_range; lia_std | apply dbase_range; lia_std].
Qed.
Lemma ext_range : forall j, 0 <= j < NE ty -> 0 <= it_extra ty work1Ar j < 65536.
Proof using C zc ret sp pb p cf bits nx.
  intros j Hj. pose proof (work1_range j) as W.
  destruct ty; cbn [it_extra NE] in *; [apply W; lia_std | apply lext_range; lia_std | apply dext_range; lia_std].
Qed.

(* the facts on the two tables' addresses (the layout's fields) *)
Lemma xaddr_facts_l :
  ZSEP (p + 7160 <= EXA_l ty p \/ EXA_l ty p + 2 * NE ty <= p + 1384) /\
  ZSEP (p + 7160 <= BSA_l ty p \/ BSA_l ty p + 2 * NE ty <= p + 1384) /\
  0 <= EXA_l ty p /\ EXA_l ty p + 2 * NE ty <= zc /\
  0 <= BSA_l ty p /\ BSA_l ty p + 2 * NE ty <= zc /\ 0 < NE ty <= 288.
Proof using C ret sp pb wf cf bits nx codes lens_ofs lf.
  pose proof C as C'. open_itc C'. unfold ZSEP in *. destruct ty; cbn [EXA_l BSA_l NE];
    cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_it3b_lext OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_it3b_dext
         OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_it3b_lbase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_it3b_dbase]; lia_std.
Qed.
Ltac xaddr_l := pose proof xaddr_facts_l as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

(* THE FIRST WALK LEMMA OF THE SECTION, IN THE LIST FORM: the entry's and the continuation's registers are the
   layout's lists over the section's value lists; the continuation's two own values are the entry's operation
   byte and its value; the two places are layout labels *)
Lemma here_l : forall st Rb l M MD T,
  m_halted MD = None -> cregsN_l Rb l -> sregs_l st Rb l -> cmem_l M -> spure_l st ->
  0 <= t_sym st < 288 -> 0 <= tr_w st < 65536 ->
  (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
  (ty = CODES -> tr_w st < it_match ty) ->
  (forall R', cregsN_l R' [] -> sregs_l st R' [] ->
     rholds (qargs [tr_op X st; tr_val X st]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_ov ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_FILL (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZBIB_LOOP (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS HM HU Hsym Hw Hwm HcB K.
  pose proof C as C'. open_itc C'. open_lists. open_cmem_l HM. open_spure HU. it3b_fields. zkeys. xaddr_l.
  pose proof work1_range as HWr. pose proof base_range as HBr. pose proof ext_range as HEr.
  assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia).
  unfold tr_w in Hw, Hwm. rewrite WK in Hw, Hwm. box Hwm. clear HtyC HtyD LOWR DROPR.
  zrebase.
  (* ONE RUN to the first test, with ONE VALUE HINT (the symbol's index doubled) *)
  zto_branch_h Rfd (first [ zhint zext32_x2 ]).
  destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)) as [Cw1|Cw1'].
  - (* ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end).
    all: try kauto. split_lists.
    + zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK. destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [reflexivity | lia].
    + zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK. destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [reflexivity | lia].
  - (* ONE RUN to the second test *)
    zto_branch Rfd.
    destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))) as [Cw2|Cw2'].
    + unbox Hwm. specialize (Hwm Cw2).
      assert (Hty : ty <> CODES) by (intro HH; specialize (HcB HH); unfold tr_w in HcB; rewrite WK in HcB; lia).
      (* the two tables' registers: their facts are found by the value they name *)
      match goal with H : _ = EXAn_l ty p |- _ => rewrite (EXAn_l_ne _ _ Hty) in H end.
      match goal with H : _ = BSAn_l ty p |- _ => rewrite (BSAn_l_ne _ _ Hty) in H end.
      (* ONE RUN to the continuation, with ONE VALUE HINT (the index into the two tables, doubled) *)
      zuntil_h Rfd (first [ zhint zext32_x2 ])
        (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end).
      all: match goal with H : _ = EXA_l ty p |- _ => rewrite <- (EXAn_l_ne _ _ Hty) in H end.
      all: match goal with H : _ = BSA_l ty p |- _ => rewrite <- (BSAn_l_ne _ _ Hty) in H end.
      all: try kauto. split_lists.
      * zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [|lia]. cbn [fst]. symmetry. apply wrap8_mod.
      * zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [|lia]. reflexivity.
    + (* ONE RUN to the continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end).
      all: try kauto. split_lists.
      * zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [lia|]. reflexivity.
      * zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [lia|]. reflexivity.
Qed.
Lemma entry_write : forall M base n f i op hbits val a0 a1 a2,
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M base i f ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => f (i + 1 + j)) ->
  mem_u8 (run_segments R_segs rc_inp rc_sp rc_mb) M a0 op -> mem_u8 (run_segments R_segs rc_inp rc_sp rc_mb) M a1 hbits -> mem_u16 (run_segments R_segs rc_inp rc_sp rc_mb) M a2 val ->
  a0 = base + 4 * i -> a1 = a0 + 1 -> a2 = a0 + 2 ->
  0 <= i < n -> base + 4 * n <= two64 -> 0 <= base ->
  0 <= op < 256 -> 0 <= hbits < 256 -> 0 <= val < 65536 ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M base n (zfupd f i (code_pack op hbits val)).
Proof using.
  intros M base n f i op hbits val a0 a1 a2 H1 H2 Ho Hb Hv -> -> -> Hi Hn Hb0 Ro Rb Rv.
  eapply mem_arr4_fill; [exact H1 | | exact H2 | lia | lia].
  apply mem_arr4_pack; try assumption; rewrite ?two64_eq in *; lia.
Qed.

(* THE FILL LOOP, IN THE LIST FORM (no other text names it: its statement is changed in place): the loop's own
   three registers (the fill index, the step negated, the code's upper bits less the step), the entry's operation
   byte and value, and the entry's bit count are small layout lists over the values the statement writes *)
Lemma fill_loop_s : forall trips f t n st Rb l M MD T,
  f = 2 ^ tr_hb st * Z.of_nat trips -> (1 <= trips)%nat -> Z.of_nat trips <= n ->
  m_halted MD = None -> cregsN_l Rb l -> sregs_l st Rb l ->
  rholds (qargs [f; - 2 ^ tr_hb st; tr_hd st - 2 ^ tr_hb st]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_floop ->
  rholds (qargs [tr_op X st; tr_val X st]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_ov ->
  rholds (qargs [tr_hb st]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_hb ->
  0 <= tr_hb st <= 15 -> 0 <= t_next st -> 0 <= tr_hd st -> t_next st + tr_hd st + f - 2 ^ tr_hb st < 1444 ->
  0 <= tr_op X st < 256 -> 0 <= tr_val X st < 65536 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get t) -> arr_len t = 1444 ->
  (forall R' M', cregsN_l R' [] -> sregs_l st R' [] ->
     rholds (qargs [tr_hb st]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_hb ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (p + 1384) (p + 7160) 0 0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 ->
     mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 (arr_get (snd (loopZ n (fill_body (tr_here X st) (2 ^ tr_hb st) (tr_hd st) (t_next st)) (f, t)))) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_INCR (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_FLOOP (zupd Rb l) M MD) T.
Proof using C zc ret wf cf.
  induction trips as [|trips IH]; intros f t n st Rb l M MD T Hf Htr Hn Hh HC HS RF ROV RHB Hhb Hnx0 Hhd Hfit Rop Rval Wp Htbl TL K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_lists. it3b_fields. zkeys.
  pose proof (pow2_le15 (tr_hb st) Hhb) as PI.
  set (I := 2 ^ tr_hb st) in *.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  assert (Hf1 : I <= f) by (rewrite Hf; apply mul_S_ge; lia).
  assert (W1 : wrap32 (f - I) = f - I) by (apply wrap32_small; lia).
  destruct (arr4_hole (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get t) (t_next st + tr_hd st + (f - I)) Htbl ltac:(lia)) as [HT1 HT2].
  clear Htbl. zrebase.
  (* ONE RUN through the entry's stores to the loop's test, with ONE VALUE HINT (the entry's index times the
     entry's width) *)
  zto_branch_h Rfd (first [ zhint zext32_x4 ]).
  match goal with
  | Ho : mem_u8 _ ?Mc _ (tr_op X st), Hb : mem_u8 _ _ _ (tr_hb st), Hv : mem_u16 _ _ _ (tr_val X st) |- _ =>
    pose proof (entry_write Mc (p + 1384) 1444 (arr_get t) (t_next st + tr_hd st + (f - I)) _ _ _ _ _ _ HT1 HT2 Ho Hb Hv
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) Rop ltac:(lia) Rval) as Htbl;
    clear Ho Hb Hv HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| rewrite TL; lia].
  assert (EH : code_pack (tr_op X st) (tr_hb st) (tr_val X st) = tr_here X st).
  { unfold tr_here. rewrite (wrap8_mod (tr_hb st)). rewrite Z.mod_small by lia. reflexivity. }
  rewrite EH in Htbl. clear EH.
  replace (t_next st + tr_hd st + (f - I)) with (t_next st + (tr_hd st + wrap32 (f - I))) in Htbl by lia.
  destruct (Z.eq_dec (f - I) 0) as [Hz|Hnz].
  - (* the last round: ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end).
    all: try kauto.
    rewrite fill_last by first [lia | rewrite W1; exact Hz]. cbn [snd]. rewrite W1, Hz in Htbl. exact Htbl.
  - (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH (f - I) (arr_set t (t_next st + (tr_hd st + wrap32 (f - I))) (tr_here X st)) (n - 1) st Rx [] Mx MD T) end).
    all: try kauto.
    all: try (rewrite Hf; apply mul_S_sub).
    all: try (rewrite arr_len_set; exact TL).
    all: try (destruct trips; [cbn in Hf; exfalso; lia | lia]).
    intros R' M'. intros. eapply K; try eassumption.
    * eapply mpost_trans; [exact HAG | assumption].
    * rewrite fill_more by first [lia | rewrite W1; exact Hnz]. subst I. rewrite W1 in *. assumption.
Qed.

Lemma op_val_range : forall st, t_work st = work1Ar -> 0 <= tr_w st < 65536 ->
  (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
  0 <= tr_op X st < 256 /\ 0 <= tr_val X st < 65536.
Proof using C zc ret sp pb p cf.
  intros st WK Fw Fwm. assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia_std).
  unfold tr_op, tr_val, tr_ov. cbn [x_ty itm_ctx]. unfold tr_w in *. rewrite WK in Fw, Fwm. rewrite WK.
  destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [cbn [fst snd]; lia_std|].
  destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); cbn [fst snd]; [|lia_std].
  split; [rewrite wrap8_mod; apply Z.mod_pos_bound; lia_std | apply base_range; lia_std].
Qed.

Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.

(* THE FILL OF ONE CODE's ENTRIES, IN THE LIST FORM *)
Lemma fill_l : forall st Rb l M MD T,
  m_halted MD = None -> cregsN_l Rb l -> sregs_l st Rb l ->
  rholds (qargs [tr_op X st; tr_val X st]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_ov ->
  spure_l st -> it_trip_ok X 288 320 1444 st = true ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (t_tbl st)) ->
  (forall R' M', cregsN_l R' [] -> sregs_l st R' [] ->
     rholds (qargs [tr_hb st]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_hb ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (p + 1384) (p + 7160) 0 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 ->
     mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 (arr_get (tr_tbl1 X st)) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_INCR (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_FILL (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS ROV HU TOK Wp Htbl K.
  pose proof C as C'. open_itc C'. open_lists. open_spure HU. it3b_fields. zkeys.
  trip_facts TOK.
  unbox Fwm. pose proof (op_val_range st WK Fw Fwm) as [Rop Rval].
  clear Fwm Flook Fcont LOWR DROPR Hprom HtyC HtyD Hlf Hcf Hwf HCr HTr.
  assert (Ehb : tr_hb st = t_len st - t_drop st) by reflexivity.
  assert (Hhb : 0 <= tr_hb st <= 15) by lia.
  assert (Hhd : 0 <= tr_hd st <= t_huff st).
  { unfold tr_hd. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (t_drop st) ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  pose proof (pow2_le15 (tr_hb st) Hhb) as PI. pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PF.
  pose proof (pow2_le15 (t_curr st - tr_hb st) ltac:(lia)) as PQ.
  assert (EQ : 2 ^ t_curr st = 2 ^ tr_hb st * 2 ^ (t_curr st - tr_hb st)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  zrebase.
  (* ONE RUN to the fill loop's head, with TWO VALUE HINTS (the step of the fill, negated; the code's bits
     above the dropped ones) *)
  zuntil_h Rfd (first [ zhint sllw_m1 | zhint srlw_small ])
    (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
      eapply (fill_loop_s (Z.to_nat (2 ^ (t_curr st - tr_hb st))) (2 ^ t_curr st) (t_tbl st) (2 ^ t_curr st) st Rx [] M MD T) end).
  all: try kauto.
  - rewrite Z2Nat.id by lia. exact EQ.
  - lia.
  - rewrite Z2Nat.id by lia. apply Z.pow_le_mono_r; lia.
  - lia.
  - intros R' M'. intros. eapply K; try eassumption.
    unfold tr_tbl1. rewrite it_fill_eq. unfold tr_incr, tr_fill. rewrite !shl32_1 by lia. assumption.
Qed.

(* THE INCREMENT LOOP, IN THE LIST FORM (no other text names it: its statement is changed in place): the bit that
   walks down and the loop's result are one-register layout lists over the value the statement writes *)
Lemma incr_loop_s : forall m c n st Rb l M MD T,
  0 <= c < 2 ^ Z.of_nat m -> Z.of_nat m < n -> c < 65536 ->
  m_halted MD = None -> cregsN_l Rb l -> sregs_l st Rb l ->
  rholds (qargs [tr_hb st]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_hb ->
  rholds (qargs [c]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_incr -> 0 <= t_huff st < 65536 ->
  (forall R', cregsN_l R' [] -> sregs_l st R' [] ->
     rholds (qargs [tr_hb st]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_hb ->
     rholds (qargs [loopZ n (incr_body (t_huff st)) c]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_incrk ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_IDONE (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_ILOOP (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  induction m as [|m IH]; intros c n st Rb l M MD T Hc Hn Hc2 Hh HC HS R8 R6 Hhuff K.
  - cbn [Z.of_nat Z.pow Z.pow_pos Pos.iter Z.mul] in Hc. assert (E : c = 0) by lia. rewrite E in *. clear E Hc Hc2.
    pose proof C as C'. open_itc C'. open_lists. it3b_fields. zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf.
    zrebase.
    (* ONE RUN to the continuation, with ONE VALUE HINT (no bit is left) *)
    zuntil_h Rfd (first [ zhint Z.land_0_l ])
      (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end).
    all: try kauto. split_lists. zregv. symmetry. apply incr_last; [lia | apply Z.land_0_r].
  - pose proof C as C'. open_itc C'. open_lists. it3b_fields. zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf.
    assert (HA : 0 <= Z.land c (t_huff st) <= c) by (split; [apply Z.land_nonneg; lia | apply land_le_l; lia]).
    pose proof (shiftr1_half c m Hc) as HH.
    assert (HH2 : Z.shiftr c 1 <= c) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; apply Z.div_le_upper_bound; lia).
    zrebase.
    (* ONE RUN to the loop's test, with ONE VALUE HINT (the bit moved down by one place) *)
    zto_branch_h Rfd (first [ zhint srliw_shiftr ]).
    destruct (Z.eq_dec (Z.land c (t_huff st)) 0) as [Z0|NZ].
    + (* the bit is clear: ONE RUN to the continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end).
      all: try kauto. split_lists. zregv. symmetry. apply incr_last; [lia | rewrite Z.land_comm; exact Z0].
    + (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (IH (Z.shiftr c 1) (n - 1) st Rx [] M MD T) end).
      all: try kauto. all: try lia.
      intros R' HC' HS' L8 L9. eapply K; try eassumption. rewrite incr_more; [exact L9 | lia | rewrite Z.land_comm; exact NZ].
Qed.

(* THE CONTINUATION FORM OF THE LAST WALK LEMMA AND THAT LEMMA, IN THE LIST FORM: the continuation's registers are
   the layout's lists; the count array's place in the frame is the layout's two frame integers *)
Definition Kst1_l (pc : Z) (brk : bool) (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', cregsN_l R' [] -> sregs_l (tr_st1 X st) R' [] ->
    rholds (qargs [tr_hb st]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_hb ->
    mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END) 0 0 -> cmem_l M' -> smem_l (tr_st1 X st) M' ->
    tr_brk X st = brk ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd R' []) M' MD) T.

Lemma count_l : forall st Rb l M MD T,
  m_halted MD = None -> cregsN_l Rb l -> sregs_l st Rb l ->
  rholds (qargs [tr_hb st]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_it3b_hb ->
  cmem_l M -> spure_l st -> it_trip_ok X 288 320 1444 st = true ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 (arr_get (t_count st)) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (tr_tbl1 X st)) ->
  Kst1_l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_ST1 false st M MD T -> Kst1_l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZBIB_BRK true st M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_IT3_INCR (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS R8 HM HU TOK Hcnt Htbl KS KB.
  pose proof C as C'. open_itc C'. open_lists. open_cmem_l HM. open_spure HU. it3b_fields. zkeys. xaddr_l.
  trip_facts TOK. clear Fcont Fwm Hprom HtyC HtyD Hcf Hwf DROPR.
  pose proof work1_range as HWr.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END) 0 0 ltac:(it3b_g; lia) ltac:(it3b_g; rewrite two64_eq; lia) ltac:(it3b_g; lia) ltac:(it3b_g; rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END) 0 0) M) by (apply mpost_refl).
  it3b_fields.
  pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL.
  zrebase.
  (* ONE RUN to the increment loop's head, with ONE VALUE HINT (the top bit of a code of this length) *)
  zuntil_h Rfd (first [ zhint sllw_1 ])
    (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
      eapply (incr_loop_s (Z.to_nat (t_len st)) (2 ^ (t_len st - 1)) 32 st Rx [] M MD T) end).
  all: try kauto.
  { rewrite Z2Nat.id by lia. split; [lia|]. apply Z.pow_lt_mono_r; lia. }
  { lia. }
  { assert (2 ^ (t_len st - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *. lia. }
  clear HST HAG. clear_regs. intros R1 HC HS L8 L9.
  assert (EI : loopZ 32 (incr_body (t_huff st)) (2 ^ (t_len st - 1)) = tr_incr2 st).
  { unfold tr_incr2. rewrite it_incr_back_eq, shl32_1 by lia. reflexivity. }
  pose proof (incr_range (t_huff st) 32 (2 ^ (t_len st - 1)) ltac:(lia)) as IR.
  rewrite EI in L9, IR. clear EI.
  assert (I14 : 2 ^ (t_len st - 1) <= 16384) by (change 16384 with (2 ^ 14); apply Z.pow_le_mono_r; lia).
  set (v1 := Z.land (tr_incr2 st - 1) (t_huff st) + tr_incr2 st).
  assert (HL : 0 <= Z.land (tr_incr2 st - 1) (t_huff st) <= t_huff st).
  { destruct (Z.eq_dec (tr_incr2 st) 0) as [E0|NE0].
    - rewrite E0. change (0 - 1) with (-1). rewrite Z.land_m1_l. lia.
    - split; [apply Z.land_nonneg; lia | apply land_le_r; lia]. }
  assert (EH : tr_huff st = Z.land (Z.b2z (tr_incr2 st =? 0) + -1) v1).
  { unfold tr_huff, v1. destruct (Z.eqb_spec (tr_incr2 st) 0) as [E0|NE0]; cbn [Z.b2z negb Z.add].
    - symmetry. apply Z.land_0_l.
    - rewrite Z.land_m1_l. rewrite Z.land_comm. reflexivity. }
  pose proof (HCr (t_len st) ltac:(lia)) as HC0.
  assert (ESY : tr_sym st = t_sym st + 1) by (unfold tr_sym; apply wrap32_small; lia).
  pose proof mx15 as MXR.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END) 0 0 ltac:(it3b_g; lia) ltac:(it3b_g; rewrite two64_eq; lia) ltac:(it3b_g; lia) ltac:(it3b_g; rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT_END) 0 0) M) by (apply mpost_refl).
  it3b_fields.
  (* the facts on the count that the run loads, stated before the run on the count as the array holds it (the
     hand text states them between the load and the next step) *)
  pose proof (swrap16_cases _ HC0) as HS16.
  assert (HSR : -32768 <= bv_swrap 16 (arr_get (t_count st) (t_len st)) <= arr_get (t_count st) (t_len st)) by (destruct HS16; lia).
  box HS16.
  assert (HLm : 0 <= Z.land (tr_incr2 st + -1) (t_huff st) <= t_huff st) by exact HL.
  open_lists. zkeys. zrebase.
  (* ONE RUN to the count's store, which the kit's array-store word takes, with FIVE VALUE HINTS (the test of the
     reversed increment; the length doubled; the next code; the count less one, moved up; the next symbol) *)
  zuntil_h Rfd (first [ zhint seqz_b2z | zhint zext32_x2 | zhint_by huff_next ltac:(reflexivity)
                      | zhint shl48_dec | zhint sym_next ])
    (idtac; tstore_arr Rfd Hcnt (t_len st)).
  set (c0 := arr_get (t_count st) (t_len st)). fold c0 in HC0, HSR, HS16.
  set (c0s := bv_swrap 16 c0) in *.
  assert (Hcnt' : forall Mq, mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 (zfupd (arr_get (t_count st)) (t_len st) (c0s + -1)) ->
                             mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (sp + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.F_IT3_COUNT) 16 (arr_get (tr_count st))).
  { intros Mq Hq. eapply mem_arr_ext_mod; [exact Hq|]. intros j Hj. unfold tr_count, zfupd, tr_c. fold c0.
    change (cell_mod 2) with 65536. rewrite arr_get_set. unfold arr_inb. rewrite CL.
    destruct (Z.eqb_spec j (t_len st)) as [Ej|NEj].
    - subst j. rewrite Z.eqb_refl. destruct (Z.leb_spec 0 (t_len st)); destruct (Z.ltb_spec (t_len st) 16); cbn [andb]; try lia.
      rewrite wrap16_mod. rewrite Z.mod_mod by lia. unbox HS16. destruct HS16 as [[A B]|[A B]]; rewrite B; [f_equal; lia|].
      replace (c0 - 65536 + -1) with ((c0 - 1) + (-1) * 65536) by lia. rewrite Z_mod_plus_full. reflexivity.
    - destruct (Z.eqb_spec (t_len st) j); [lia|]. cbn [andb]. reflexivity. }
  apply Hcnt' in Hcnt. clear Hcnt'.
  assert (EC : tr_c st = (c0 - 1) mod 65536) by (unfold tr_c; fold c0; apply wrap16_mod).
  destruct (Z.eq_dec c0 1) as [C1|NC1].
  - assert (C1s : c0s = 1) by (unbox HS16; destruct HS16; lia).
    assert (EC0 : tr_c st = 0) by (rewrite EC, C1; reflexivity).
    destruct (Z.eq_dec (t_len st) mx) as [LM|NLM].
    + assert (EL : tr_len X st = t_len st).
      { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [reflexivity | lia]. }
      (* ONE RUN through the two tests to the continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KB Rx Mx) end).
      all: try kauto.
      * close_sregs1_l EL.
      * close_cmem_l.
      * unfold smem_l. cbn [t_count t_tbl tr_st1]. split; assumption.
      * unfold tr_brk. cbn [x_max itm_ctx]. rewrite EC0. cbn [Z.eqb andb]. apply Z.eqb_eq. exact LM.
    + unbox Flook. dand (Flook EC0 NLM) as (W1 & W2 & W3 & W4). rewrite WK in W2, W3, W4. rewrite lensA_get in W4. rewrite <- ESY in W1, W2, W3, W4.
      assert (EL : tr_len X st = lf (lens_ofs + arr_get work1Ar (tr_sym st))).
      { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [lia|].
        cbn [andb negb]. rewrite WK. apply lensA_get. }
      (* ONE RUN through the two tests and the next length's load to the continuation, with TWO VALUE HINTS
         (the next symbol's index doubled; that symbol's index doubled) *)
      zuntil_h Rfd (first [ zhint zext32_x2 | zhint shl1_x2 ])
        (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KS Rx Mx) end).
      all: try kauto.
      * close_sregs1_l EL.
      * close_cmem_l.
      * unfold smem_l. cbn [t_count t_tbl tr_st1]. split; assumption.
      * unfold tr_brk. cbn [x_max itm_ctx]. rewrite EC0. cbn [Z.eqb andb]. apply Z.eqb_neq. exact NLM.
  - assert (HNZ : ((c0s + -1) * 281474976710656) mod 18446744073709551616 <> 0).
    { unbox HS16. destruct HS16 as [[A B]|[A B]]; rewrite B.
      - destruct (Z.eq_dec c0 0) as [E0|NE0]; [rewrite E0; cbv; discriminate | rewrite Z.mod_small by lia; lia].
      - rewrite negshift48_mod by lia. lia. }
    assert (ECN : tr_c st <> 0).
    { rewrite EC. destruct (Z.eq_dec c0 0) as [E0|NE0]; [rewrite E0; cbv; discriminate | rewrite Z.mod_small by lia; lia]. }
    assert (EL : tr_len X st = t_len st).
    { unfold tr_len. destruct (Z.eqb_spec (tr_c st) 0); [lia | reflexivity]. }
    (* ONE RUN through the test to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KS Rx Mx) end).
    all: try kauto.
    * close_sregs1_l EL.
    * close_cmem_l.
    * unfold smem_l. cbn [t_count t_tbl tr_st1]. split; assumption.
    * unfold tr_brk. destruct (Z.eqb_spec (tr_c st) 0); [lia | reflexivity].
Qed.
End S7IT3.

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ItCovBits ItCovPre ItCovMath ItCovStep ItCovLoop ItCovMain.

Module PIc_mod.
Definition PIc (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (st : ItSt) : Prop :=
  ty = CODES -> exists j, 0 <= j < N (lensA lf) lens_ofs codes /\
    IS ty (lensA lf) lens_ofs codes (rootA lf lens_ofs codes bits) nx j st.

Section PI.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z).
Hypothesis Hc : 0 <= codes <= 288.
Hypothesis Hl : forall s, 0 <= s < codes -> 0 <= arr_get (lensA lf) (lens_ofs + s) <= 15.
Hypothesis HtyC' : ty = CODES -> codes <= 19 /\ bits = 7 /\ forall s, 0 <= s < codes -> arr_get (lensA lf) (lens_ofs + s) <= 7.
Hypothesis Hb : 1 <= bits <= 15.
Hypothesis Hmx : 1 <= mxA lf lens_ofs codes.
Hypothesis Hrj : itm_reject ty (mxA lf lens_ofs codes) (it_left_check (cntA lf lens_ofs codes)) = false.

Lemma Hmx' : max (lensA lf) lens_ofs codes <> 0.
Proof. intro H. change (mxA lf lens_ofs codes = 0) in H. lia. Qed.

Lemma pic_complete : ty = CODES -> kraft (lensA lf) lens_ofs codes 15 = 2 ^ 15.
Proof.
  intros Ety. pose proof (left_eq (lensA lf) lens_ofs codes Hc Hl) as LE.
  change (it_left_check (cntA lf lens_ofs codes)) with (it_left_check (count (lensA lf) lens_ofs codes)) in Hrj.
  rewrite LE in Hrj. unfold itm_reject in Hrj.
  destruct (Z.ltb_spec (2 ^ 15) (kraft (lensA lf) lens_ofs codes 15)); [discriminate|].
  rewrite Ety in Hrj. cbn [codetype_eqb orb andb] in Hrj.
  destruct (Z.ltb_spec 0 (2 ^ 15 - kraft (lensA lf) lens_ofs codes 15)); [discriminate | lia].
Qed.

Lemma pic_init : it_not_enough ty (itm_used (rootA lf lens_ofs codes bits)) = false ->
  PIc ty lf lens_ofs codes nx bits
    (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).
Proof using Hc Hl HtyC' Hb Hmx Hrj.
  intros Hne Ety. pose proof (N_range (lensA lf) lens_ofs codes Hc Hl) as NR.
  pose proof (HtyC19 ty (lensA lf) lens_ofs codes bits HtyC' Ety) as C19.
  pose proof (CN (lensA lf) lens_ofs codes Hc Hl Hmx) as N1.
  exists 0. split; [lia|].
  assert (HU : itm_used (rootA lf lens_ofs codes bits) = 2 ^ rootA lf lens_ofs codes bits).
  { exact (used_eq (lensA lf) lens_ofs codes bits Hc Hl Hb Hmx'). }
  rewrite HU in Hne.
  exact (IS0' ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf) Hc Hl Hb ltac:(rewrite workA_len; lia) Hmx' Hne).
Qed.

Lemma pic_step : forall st st', PIc ty lf lens_ofs codes nx bits st ->
  it_step (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)) st = ItCont st' ->
  PIc ty lf lens_ofs codes nx bits st'.
Proof using Hc Hl HtyC' Hb Hmx Hrj.
  intros st st' HP Hs Ety. destruct (HP Ety) as (j & Hj & HIS).
  pose proof (HtyC19 ty (lensA lf) lens_ofs codes bits HtyC' Ety) as C19.
  change (it_step (itm_ctx ty (lensA lf) lens_ofs nx (itm_root bits (max (lensA lf) lens_ofs codes) (min (lensA lf) lens_ofs codes)) (max (lensA lf) lens_ofs codes)) st = ItCont st') in Hs.
  rewrite (ctx_eq ty (lensA lf) lens_ofs codes nx bits Hc Hl Hb Hmx') in Hs.
  pose proof (trip ty (lensA lf) lens_ofs codes Hc Hl Hmx (pic_complete Ety) (rootA lf lens_ofs codes bits)
                (Hroot (lensA lf) lens_ofs codes bits Hc Hl Hb Hmx') nx (fun _ => C19) j st Hj HIS) as TP.
  unfold trip_post in TP. match type of TP with context [it_step ?c st] => assert (Hs2 : it_step c st = ItCont st') by exact Hs; rewrite Hs2 in TP end. destruct TP as (HjN & _ & HIS' & _).
  exists (j + 1). split; [lia | exact HIS'].
Qed.

Lemma pic_w : forall st, PIc ty lf lens_ofs codes nx bits st -> ty = CODES ->
  arr_get (t_work st) (t_sym st) < 20.
Proof using Hc Hl HtyC' Hb Hmx Hrj.
  intros st HP Ety. destruct (HP Ety) as (j & Hj & HIS).
  pose proof (HtyC19 ty (lensA lf) lens_ofs codes bits HtyC' Ety) as C19.
  destruct HIS as (Hsym & _ & _ & _ & _ & Hw & _).
  rewrite Hsym, (Hw j Hj). pose proof (LWr (lensA lf) lens_ofs codes Hc j Hj). lia.
Qed.
End PI.
End PIc_mod.
