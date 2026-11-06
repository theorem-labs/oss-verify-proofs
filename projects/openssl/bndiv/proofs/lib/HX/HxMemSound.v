(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie AxFetchFast.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import MState Mem.
From OSSVerify.Proofs.openssl.bndiv.lib.HX Require Import HxVal HxBytes HxMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive kb : Type :=
| KB (z : Z)
| KP (t : int) (o : w64) (j : Z)
| KU.

Definition cell_kb (c : cell) (j : Z) : kb :=
  match c with
  | CW w km => if Z.testbit (to_Z km) j then KB (byteZ (wZ w) j) else KU
  | CP t o => KP t o j
  end.

Definition kb_ok (rho : valuation) (k : kb) (b : byte) : Prop :=
  match k with
  | KB z => bv_unsigned b = z
  | KP t o j => bv_unsigned b = byteZ (bv_unsigned (pword rho t o)) j
  | KU => True
  end.

(* [comment removed for export] *)
Definition kb_le (k' k : kb) : Prop := k' = KU \/ k' = k.

Lemma kb_ok_le (rho : valuation) (k' k : kb) (b : byte) : kb_le k' k -> kb_ok rho k b -> kb_ok rho k' b.
Proof. intros [->| ->] H; [exact I | exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MemSound.
Variable segs : list Segment.

Definition rbase (rho : valuation) (t : int) (rg : region) : Z :=
  match rg_abs rg with Some lo => to_Z lo | None => rho t end.

(* [comment removed for export] *)
Definition rg_kb (rg : region) (i : Z) : kb := cell_kb (rd_cell segs rg (of_Z (i / 8))) (i mod 8).

Definition region_ok (rho : valuation) (t : int) (rg : region) (m : word -> option byte) : Prop :=
  let B := rbase rho t rg in
  (0 <= B /\ (0 < B \/ to_Z (rg_al rg) = 0)) /\ B + to_Z (rg_size rg) < two63 /\ to_Z (rg_size rg) < 2 ^ 62
  /\ to_Z (rg_size rg) <= 8 * 2 ^ Z.of_nat (rg_d rg) /\ Z.of_nat (rg_d rg) <= 59
  /\ to_Z (rg_al rg) < 63 /\ B mod 2 ^ to_Z (rg_al rg) = 0
  /\ forall i, 0 <= i < to_Z (rg_size rg) ->
       exists b, mrd segs m (wa (B + i)) = Some b /\ kb_ok rho (rg_kb rg i) b
                 /\ (rg_wr rg = true -> wview segs m (wa (B + i)) <> None).

(* [comment removed for export] *)
Definition regions_sep (rho : valuation) (M : mem) : Prop :=
  forall t1 t2 rg1 rg2, mget M t1 = Some rg1 -> mget M t2 = Some rg2 -> t1 <> t2 -> rg_wr rg1 = true \/ rg_wr rg2 = true ->
    rbase rho t1 rg1 + to_Z (rg_size rg1) <= rbase rho t2 rg2 \/ rbase rho t2 rg2 + to_Z (rg_size rg2) <= rbase rho t1 rg1.

Definition Rmem (rho : valuation) (M : mem) (m : word -> option byte) : Prop :=
  (forall t rg, mget M t = Some rg -> region_ok rho t rg m) /\ regions_sep rho M.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma TAGLIM_Z : to_Z TAGLIM = 2 ^ Z.of_nat TAGD.
Proof. reflexivity. Qed.

Lemma mget_mset (M : mem) (t t' : int) (rg : region) : to_Z t < to_Z TAGLIM ->
  mget (mset M t rg) t' = if (to_Z t =? to_Z t') then Some rg else mget M t'.
Proof.
  intros Ht. unfold mget, mset. destruct (ltbP t' TAGLIM) as [H'|H'].
  - rewrite iget_iset. rewrite <- TAGLIM_Z. pose proof (to_Z_bounded t) as B1. pose proof (to_Z_bounded t') as B2.
    rewrite !Z.mod_small by lia. reflexivity.
  - destruct (Z.eqb_spec (to_Z t) (to_Z t')) as [E|E]; [lia | reflexivity].
Qed.

Lemma mget_lt (M : mem) (t : int) (rg : region) : mget M t = Some rg -> to_Z t < to_Z TAGLIM.
Proof. unfold mget. destruct (ltbP t TAGLIM) as [H|H]; [intros _; exact H | discriminate]. Qed.

(* [comment removed for export] *)
Lemma ctx_of_ok (rho : valuation) (M : mem) (m : word -> option byte) : Rmem rho M m -> ctx_ok rho (ctx_of M).
Proof.
  intros [HR _] t al sz H. unfold ctx_of in H. destruct (mget M t) as [rg|] eqn:E; [|discriminate].
  destruct (rg_abs rg) eqn:Ea; [discriminate|]. destruct (eqbP (rg_al rg) 0) as [E0|E0]; [discriminate|]. injection H as <- <-.
  destruct (HR t rg E) as ((H0 & H0') & H1 & _ & _ & _ & H5 & H6 & _). unfold rbase in *. rewrite Ea in *.
  change (to_Z 0%uint63) with 0 in E0. repeat split; try assumption. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_rg_spec (off n size : int) : to_Z size < 2 ^ 62 -> to_Z n <= 8 -> in_rg off n size = true ->
  to_Z off + to_Z n <= to_Z size /\ to_Z (off + n)%uint63 = to_Z off + to_Z n.
Proof.
  intros Hs Hn H. unfold in_rg in H. apply andb_prop in H as [H1 H2]. apply leb_spec in H1. apply leb_spec in H2.
  pose proof (to_Z_bounded off) as Bo. pose proof (to_Z_bounded n) as Bn.
  assert (E : to_Z (off + n)%uint63 = to_Z off + to_Z n) by (rewrite add_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
  lia.
Qed.

Lemma wa_of_unsigned (x : word) (A : Z) : bv_unsigned x = A -> x = wa A.
Proof. intros <-. unfold wa. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma resolve_spec (rho : valuation) (M : mem) (abs : abstab) (m : word -> option byte) (a : hval) (n : int) (x : word)
    (t : int) (rg : region) (off : int) :
  Rmem rho M m -> to_Z n <= 8 -> resolve M abs a n = Some (t, rg, off) -> den rho a x ->
  mget M t = Some rg /\ x = wa (rbase rho t rg + to_Z off) /\ to_Z off + to_Z n <= to_Z (rg_size rg).
Proof.
  intros [HR _] Hn H Hd. unfold resolve in H. destruct a as [w|t' o| |]; [| |discriminate|discriminate].
  - destruct (wh w) eqn:Eh; [discriminate|]. destruct (abs_find abs (wl w) n) as [[t' off']|]; [|discriminate].
    destruct (mget M t') as [rg'|] eqn:Eg; [|discriminate]. destruct (rg_abs rg') as [lo|] eqn:Ea; [|discriminate].
    destruct (in_rg off' n (rg_size rg')) eqn:Ei; [|discriminate]. cbn [andb] in H.
    destruct (eqbP (lo + off')%uint63 (wl w)) as [E|E]; [|discriminate]. injection H as <- <- <-.
    destruct (HR t' rg' Eg) as (H0 & H1 & H2 & _). destruct (in_rg_spec off' n (rg_size rg') H2 Hn Ei) as [Hin _].
    split; [exact Eg|]. split; [|exact Hin]. apply wa_of_unsigned. cbn [den] in Hd. subst x. rewrite wbv_unsigned.
    unfold rbase in *. rewrite Ea in *. rewrite wZ_split, Eh. cbn [Z.b2z]. rewrite <- E, add_spec.
    pose proof (to_Z_bounded off') as Bo. pose proof (to_Z_bounded n) as Bn. rewrite wB_eq in *.
    rewrite Z.mod_small by lia. lia.
  - destruct (wh o) eqn:Eh; [discriminate|]. destruct (mget M t') as [rg'|] eqn:Eg; [|discriminate].
    destruct (rg_abs rg') eqn:Ea; [discriminate|]. destruct (in_rg (wl o) n (rg_size rg')) eqn:Ei; [|discriminate].
    injection H as <- <- <-. destruct (HR t' rg' Eg) as (H0 & H1 & H2 & _). destruct (in_rg_spec (wl o) n (rg_size rg') H2 Hn Ei) as [Hin _].
    split; [exact Eg|]. split; [|exact Hin]. apply wa_of_unsigned. cbn [den] in Hd. subst x. unfold pword.
    unfold rbase in *. rewrite Ea in *. rewrite wZ_split, Eh. cbn [Z.b2z]. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64). unfold two63 in *. pose proof (to_Z_bounded (wl o)) as Bo. pose proof (to_Z_bounded n) as Bn.
    split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma collect_bytes (m : word -> option byte) : forall (n : nat) (A : Z) (P : Z -> byte -> Prop),
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> exists b, mrd segs m (wa (A + i)) = Some b /\ P i b) ->
  exists bs, length bs = n /\ bytes_at segs m A bs /\ forall i b, nth_error bs i = Some b -> P (Z.of_nat i) b.
Proof.
  induction n as [|n IH]; intros A P HA Hn H.
  - exists []. split; [reflexivity|]. split; [|intros i b Hb; destruct i; discriminate].
    split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0 ltac:(lia)) as (b0 & Hb0 & HP0). rewrite Z.add_0_r in Hb0.
    destruct (IH (A + 1) (fun i b => P (i + 1) b) ltac:(lia) ltac:(lia)) as (bs & Hl & Hb & HP).
    { intros i Hi. destruct (H (i + 1) ltac:(lia)) as (b & E & HPb). exists b. split; [|exact HPb].
      replace (A + 1 + i) with (A + (i + 1)) by ring. exact E. }
    exists (b0 :: bs). split; [cbn; lia|]. split.
    + destruct Hb as (_ & _ & Hb). split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i].
      * cbn [nth_error]. rewrite Z.add_0_r. exact Hb0.
      * cbn [nth_error]. rewrite <- (Hb i) by (cbn in Hi; lia). f_equal. f_equal. lia.
    + intros i b Hi. destruct i as [|i]; cbn [nth_error] in Hi.
      * injection Hi as <-. exact HP0.
      * replace (Z.of_nat (Datatypes.S i)) with (Z.of_nat i + 1) by lia. exact (HP i b Hi).
Qed.

Lemma phi_shr3 (off : int) : to_Z (off >> 3)%uint63 = to_Z off / 8.
Proof. rewrite lsr_spec. reflexivity. Qed.

Lemma phi_land7 (off : int) : to_Z (off land 7)%uint63 = to_Z off mod 8.
Proof. rewrite land_spec'. change (to_Z 7%uint63) with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cell_of_byte (off : int) (i n : Z) : to_Z off mod 8 + n <= 8 -> 0 <= i < n ->
  of_Z ((to_Z off + i) / 8) = (off >> 3)%uint63 /\ (to_Z off + i) mod 8 = to_Z off mod 8 + i.
Proof.
  intros Hj Hi. pose proof (to_Z_bounded off) as Bo. pose proof (Z.mod_pos_bound (to_Z off) 8 ltac:(lia)) as Hm.
  pose proof (Z.div_mod (to_Z off) 8 ltac:(lia)) as E.
  assert (Eq : (to_Z off + i) / 8 = to_Z off / 8).
  { symmetry. apply Z.div_unique with (r := to_Z off mod 8 + i); lia. }
  split.
  - rewrite Eq. apply to_Z_inj. rewrite phi_shr3, of_Z_spec. apply Z.mod_small.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
  - symmetry. apply Z.mod_unique with (q := to_Z off / 8); lia.
Qed.

Lemma byte_mask_Z (n : int) : to_Z n <= 8 -> to_Z (byte_mask n) = 2 ^ to_Z n - 1.
Proof.
  intros Hn. pose proof (to_Z_bounded n) as Bn. unfold byte_mask. rewrite sub_spec, lsl_spec. change (to_Z 1%uint63) with 1.
  assert (P : 0 < 2 ^ to_Z n <= 2 ^ 8) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  rewrite wB_eq in *. unfold two63 in *. rewrite Z.mul_1_l, (Z.mod_small (2 ^ to_Z n)) by lia. apply Z.mod_small. lia.
Qed.

Lemma known_spec (km j n : int) (i : Z) : to_Z n <= 8 -> known km j n = true -> 0 <= i < to_Z n ->
  Z.testbit (to_Z km) (to_Z j + i) = true.
Proof.
  intros Hn H Hi. unfold known in H. destruct (eqbP ((km >> j) land byte_mask n)%uint63 (byte_mask n)) as [E|E]; [|discriminate].
  rewrite land_spec', lsr_spec, byte_mask_Z in E by exact Hn. pose proof (to_Z_bounded j) as Bj. pose proof (to_Z_bounded n) as Bn.
  change (2 ^ to_Z n - 1) with (Z.pred (2 ^ to_Z n)) in E. rewrite <- Z.ones_equiv in E. rewrite Z.land_ones in E by lia.
  assert (T : Z.testbit ((to_Z km / 2 ^ to_Z j) mod 2 ^ to_Z n) i = true) by (rewrite E; apply Z.ones_spec_low; lia).
  rewrite Z.mod_pow2_bits_low in T by lia. rewrite Z.div_pow2_bits in T by lia. rewrite Z.add_comm. exact T.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition msz_nat (sz : msize) : nat := match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

Lemma nbytes_Z (sz : msize) : to_Z (nbytes sz) = Z.of_nat (msz_nat sz).
Proof. destruct sz; reflexivity. Qed.

(* [comment removed for export] *)
Definition load_word (sz : msize) (sg : bool) (bs : list byte) : word :=
  match sz with
  | SZ1 => if sg then sext 64 (bv_extract 0 8 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
  | SZ2 => if sg then sext 64 (bv_extract 0 16 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
  | SZ4 => if sg then sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
  | SZ8 => bv_extract 0 64 (le_bytes_to_word bs)
  end.

Lemma extract_small (k : N) (F : Z) : (0 < k <= 64)%N -> 0 <= F < 2 ^ Z.of_N k ->
  bv_unsigned (bv_extract 0 k (Z_to_bv 64 F)) = F.
Proof.
  intros Hk HF. rewrite bv_extract_unsigned, Z_to_bv_unsigned. rewrite Z.shiftr_0_r.
  assert (P : 2 ^ Z.of_N k <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (bv_wrap_small 64 F) by (change (bv_modulus 64) with (2 ^ 64); lia).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

Lemma load_word_conc (sz : msize) (sg : bool) (bs : list byte) (Fw : w64) :
  bytes_le_to_Z bs = wZ Fw -> wZ Fw < 2 ^ (8 * Z.of_nat (msz_nat sz)) ->
  load_word sz sg bs = wbv (ext_val sz sg Fw).
Proof.
  intros HF Hr. pose proof (wZ_range Fw) as HFr.
  assert (E0 : le_bytes_to_word bs = Z_to_bv 64 (wZ Fw)) by (unfold le_bytes_to_word; rewrite HF; reflexivity).
  unfold load_word. rewrite E0. clear E0 HF.
  assert (Hz : forall k : N, (0 < k <= 64)%N -> wZ Fw < 2 ^ Z.of_N k -> zext 64 (bv_extract 0 k (Z_to_bv 64 (wZ Fw))) = wbv Fw).
  { intros k Hk Hlt. apply bv_eq. unfold zext. rewrite bv_zero_extend_unsigned by lia. rewrite extract_small by lia. symmetry. apply wbv_unsigned. }
  assert (Hs : forall (k : N) (n : int), (0 < k <= 32)%N -> Z.of_N k = 8 * to_Z n -> 1 <= to_Z n <= 4 -> wZ Fw < 2 ^ Z.of_N k ->
            sext 64 (bv_extract 0 k (Z_to_bv 64 (wZ Fw))) = wbv (w_sextn n Fw)).
  { intros k n Hk Ek Hn Hlt. apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned by lia. rewrite wbv_unsigned.
    rewrite wZ_sextn by (try lia; rewrite <- Ek; lia). rewrite <- Ek.
    unfold bv_signed, bv_swrap. rewrite extract_small by lia. unfold bv_wrap, bv_half_modulus, bv_modulus.
    assert (E2 : 2 ^ Z.of_N k = 2 * 2 ^ (Z.of_N k - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (P1 : 0 < 2 ^ (Z.of_N k - 1)) by (apply Z.pow_pos_nonneg; lia).
    assert (P2 : 2 ^ Z.of_N k <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
    replace (2 ^ Z.of_N k / 2) with (2 ^ (Z.of_N k - 1)) by (rewrite E2 at 1; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    change (2 ^ Z.of_N 64) with two64.
    destruct (Z.ltb_spec (wZ Fw) (2 ^ (Z.of_N k - 1))).
    - rewrite (Z.mod_small (wZ Fw + 2 ^ (Z.of_N k - 1))) by lia.
      replace (wZ Fw + 2 ^ (Z.of_N k - 1) - 2 ^ (Z.of_N k - 1)) with (wZ Fw) by ring. apply Z.mod_small. lia.
    - replace (wZ Fw + 2 ^ (Z.of_N k - 1)) with ((wZ Fw - 2 ^ (Z.of_N k - 1)) + 1 * 2 ^ Z.of_N k) by lia.
      rewrite Z.mod_add by lia. rewrite (Z.mod_small (wZ Fw - 2 ^ (Z.of_N k - 1))) by lia.
      replace (wZ Fw - 2 ^ (Z.of_N k - 1) - 2 ^ (Z.of_N k - 1)) with ((wZ Fw + two64 - 2 ^ Z.of_N k) + (-1) * two64) by lia.
      rewrite Z.mod_add by (unfold two64; lia). apply Z.mod_small. unfold two64 in *. lia. }
  destruct sz; cbn [msz_nat ext_val nbytes] in *.
  - destruct sg; [apply (Hs 8%N 1%uint63); [lia | reflexivity | change (to_Z 1%uint63) with 1; lia | exact Hr] | apply Hz; [lia | exact Hr]].
  - destruct sg; [apply (Hs 16%N 2%uint63); [lia | reflexivity | change (to_Z 2%uint63) with 2; lia | exact Hr] | apply Hz; [lia | exact Hr]].
  - destruct sg; [apply (Hs 32%N 4%uint63); [lia | reflexivity | change (to_Z 4%uint63) with 4; lia | exact Hr] | apply Hz; [lia | exact Hr]].
  - apply bv_eq. rewrite extract_small by (unfold two64 in *; lia). symmetry. apply wbv_unsigned.
Qed.

Lemma load_word_ptr (bs : list byte) (x : word) : bytes_le_to_Z bs = bv_unsigned x -> load_word SZ8 false bs = x /\ load_word SZ8 true bs = x.
Proof.
  intros H. unfold load_word, le_bytes_to_word. rewrite H. rewrite Z_to_bv_bv_unsigned.
  assert (E : bv_extract 0 64 x = x).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. }
  rewrite E. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma byte_of_eq (b : byte) (z j : Z) : bv_unsigned b = byteZ z j -> b = byte_of z j.
Proof. intros H. apply bv_eq. rewrite byte_of_unsigned. exact H. Qed.

Lemma nth_known (bs : list byte) (n : nat) (f : Z -> byte) (Q : Z -> byte -> Prop) :
  length bs = n -> (forall i b, nth_error bs i = Some b -> Q (Z.of_nat i) b) ->
  (forall i b, (i < n)%nat -> Q (Z.of_nat i) b -> b = f (Z.of_nat i)) ->
  forall i, (i < n)%nat -> nth_error bs i = Some (f (Z.of_nat i)).
Proof.
  intros Hl HQ Hf i Hi. destruct (nth_error bs i) as [b|] eqn:E.
  - f_equal. apply Hf; [exact Hi | apply HQ; exact E].
  - apply nth_error_None in E. lia.
Qed.

Lemma fieldZ_full (z : Z) : 0 <= z < 2 ^ 64 -> fieldZ z 0 8 = z.
Proof. intros H. unfold fieldZ. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r. apply Z.mod_small. exact H. Qed.

Theorem hx_load_sound (rho : valuation) (M : mem) (abs : abstab) (m : word -> option byte) (a : hval) (sz : msize) (sg : bool)
    (v : hval) (x : word) :
  Rmem rho M m -> den rho a x -> hx_load segs M abs a sz sg = Some v ->
  exists bs, ov_read_bytes segs m x (msz_nat sz) = Some bs /\ den rho v (load_word sz sg bs).
Proof.
  intros HR Ha H. unfold hx_load in H.
  destruct (resolve M abs a (nbytes sz)) as [[[t rg] off]|] eqn:Er; [|discriminate].
  assert (Hn8 : to_Z (nbytes sz) <= 8) by (destruct sz; cbn; change (to_Z 1%uint63) with 1; change (to_Z 2%uint63) with 2; change (to_Z 4%uint63) with 4; change (to_Z 8%uint63) with 8; lia).
  destruct (resolve_spec rho M abs m a (nbytes sz) x t rg off HR Hn8 Er Ha) as (Eg & -> & Hin).
  destruct HR as [HRr _]. destruct (HRr t rg Eg) as (HB0 & HB1 & Hs62 & Hd & Hd59 & _ & _ & Hbytes).
  set (B := rbase rho t rg) in *. pose proof (to_Z_bounded off) as Bo. rewrite nbytes_Z in Hin, Hn8.
  destruct (collect_bytes m (msz_nat sz) (B + to_Z off) (fun i b => kb_ok rho (rg_kb rg (to_Z off + i)) b)
              ltac:(lia) ltac:(unfold two63 in *; lia)) as (bs & Hl & Hb & HP).
  { intros i Hi. destruct (Hbytes (to_Z off + i) ltac:(lia)) as (b & E1 & E2 & _). exists b.
    split; [rewrite <- Z.add_assoc; exact E1 | exact E2]. }
  exists bs. split.
  { pose proof (bytes_at_ov_read segs m (B + to_Z off) bs 0 (msz_nat sz) Hb ltac:(lia)) as E.
    cbn [Z.of_nat skipn] in E. rewrite Z.add_0_r in E. rewrite E. f_equal. rewrite <- Hl. apply firstn_all. }
  set (j := (off land 7)%uint63) in *. set (k := (off >> 3)%uint63) in *.
  destruct (j + nbytes sz <=? 8)%uint63 eqn:Ejn; [|injection H as <-; exact I].
  apply leb_spec in Ejn. assert (Ej : to_Z j = to_Z off mod 8) by apply phi_land7.
  pose proof (Z.mod_pos_bound (to_Z off) 8 ltac:(lia)) as Hjr.
  assert (Ejn' : to_Z off mod 8 + Z.of_nat (msz_nat sz) <= 8).
  { rewrite add_spec, nbytes_Z, Ej in Ejn. change (to_Z 8%uint63) with 8 in Ejn. rewrite wB_eq in *. unfold two63 in *.
    rewrite Z.mod_small in Ejn by lia. exact Ejn. }
  assert (Hkb : forall i, 0 <= i < Z.of_nat (msz_nat sz) -> rg_kb rg (to_Z off + i) = cell_kb (rd_cell segs rg k) (to_Z j + i)).
  { intros i Hi. unfold rg_kb. destruct (cell_of_byte off i (Z.of_nat (msz_nat sz)) Ejn' Hi) as [-> ->]. rewrite Ej. reflexivity. }
  destruct (rd_cell segs rg k) as [w km|t' o'] eqn:Ec.
  - destruct (known km j (nbytes sz)) eqn:Ek; [|injection H as <-; exact I]. injection H as <-.
    assert (Hnth : forall i, (i < msz_nat sz)%nat -> nth_error bs i = Some (byte_of (wZ w) (to_Z j + Z.of_nat i))).
    { apply (nth_known bs (msz_nat sz) (fun i => byte_of (wZ w) (to_Z j + i)) (fun i b => kb_ok rho (rg_kb rg (to_Z off + i)) b) Hl HP).
      intros i b Hi Hk. rewrite Hkb in Hk by lia. cbn [cell_kb] in Hk.
      rewrite (known_spec km j (nbytes sz) (Z.of_nat i)) in Hk by (rewrite ?nbytes_Z; try exact Ek; lia).
      cbn [kb_ok] in Hk. apply byte_of_eq. exact Hk. }
    pose proof (bytes_le_to_Z_field (msz_nat sz) bs (wZ w) (to_Z j) ltac:(lia) Hl Hnth) as EF.
    cbn [den]. assert (Hfr := fieldZ_range (wZ w) (to_Z j) (Z.of_nat (msz_nat sz)) ltac:(lia)).
    destruct sz; cbn [msz_nat] in *.
    + apply load_word_conc; rewrite wZ_ext by (change (to_Z (nbytes SZ1)) with 1; lia); [exact EF | exact (proj2 Hfr)].
    + apply load_word_conc; rewrite wZ_ext by (change (to_Z (nbytes SZ2)) with 2; lia); [exact EF | exact (proj2 Hfr)].
    + apply load_word_conc; rewrite wZ_ext by (change (to_Z (nbytes SZ4)) with 4; lia); [exact EF | exact (proj2 Hfr)].
    + assert (Ej0 : to_Z j = 0) by lia. rewrite Ej0 in EF. change (Z.of_nat 8) with 8 in EF.
      pose proof (wZ_range w) as Hw. unfold two64 in Hw. rewrite fieldZ_full in EF by lia.
      apply (load_word_conc SZ8 sg bs w EF). cbn. unfold two64 in *. lia.
  - destruct sz; try (injection H as <-; exact I). injection H as <-. cbn [den msz_nat] in *.
    assert (Ej0 : to_Z j = 0) by lia.
    set (U := bv_unsigned (pword rho t' o')).
    assert (Hnth : forall i, (i < 8)%nat -> nth_error bs i = Some (byte_of U (0 + Z.of_nat i))).
    { apply (nth_known bs 8 (fun i => byte_of U (0 + i)) (fun i b => kb_ok rho (rg_kb rg (to_Z off + i)) b) Hl HP).
      intros i b Hi Hk. rewrite Hkb in Hk by lia. cbn [cell_kb kb_ok] in Hk. rewrite Ej0 in Hk. apply byte_of_eq. exact Hk. }
    pose proof (bytes_le_to_Z_field 8 bs U 0 ltac:(lia) Hl Hnth) as EF. change (Z.of_nat 8) with 8 in EF.
    pose proof (bv_unsigned_in_range 64 (pword rho t' o')) as HU. change (bv_modulus 64) with (2 ^ 64) in HU. fold U in HU.
    rewrite fieldZ_full in EF by exact HU. destruct (load_word_ptr bs (pword rho t' o') EF) as [E1 E2].
    destruct sg; [exact E2 | exact E1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma testbit_ones_shift (n j b : Z) : 0 <= n -> 0 <= j -> 0 <= b ->
  Z.testbit ((2 ^ n - 1) * 2 ^ j) b = (j <=? b) && (b <? j + n).
Proof.
  intros Hn Hj Hb. change (2 ^ n - 1) with (Z.pred (2 ^ n)). rewrite <- Z.ones_equiv. rewrite Z.mul_pow2_bits by lia.
  destruct (Z.leb_spec j b) as [L|L]; cbn [andb].
  - destruct (Z.ltb_spec b (j + n)) as [L2|L2]; [apply Z.ones_spec_low; lia | apply Z.ones_spec_high; lia].
  - apply Z.testbit_neg_r. lia.
Qed.

Lemma phi_mask_shift (n j : int) : to_Z j + to_Z n <= 8 -> to_Z (byte_mask n << j)%uint63 = (2 ^ to_Z n - 1) * 2 ^ to_Z j.
Proof.
  intros H. pose proof (to_Z_bounded j) as Bj. pose proof (to_Z_bounded n) as Bn. rewrite lsl_spec, byte_mask_Z by lia.
  assert (P1 : 0 < 2 ^ to_Z n <= 2 ^ 8) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  assert (P2 : 0 < 2 ^ to_Z j <= 2 ^ 8) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  apply Z.mod_small. rewrite wB_eq. unfold two63. nia.
Qed.

Lemma testbit_mask_shift (n j : int) (b : Z) : to_Z j + to_Z n <= 8 -> 0 <= b ->
  Z.testbit (to_Z (byte_mask n << j)%uint63) b = (to_Z j <=? b) && (b <? to_Z j + to_Z n).
Proof.
  intros H Hb. pose proof (to_Z_bounded j) as Bj. pose proof (to_Z_bounded n) as Bn.
  rewrite phi_mask_shift by exact H. apply testbit_ones_shift; lia.
Qed.

Lemma testbit_255 (b : Z) : 0 <= b < 8 -> Z.testbit 255 b = true.
Proof. intros H. change 255 with (Z.ones 8). apply Z.ones_spec_low. lia. Qed.

Lemma forget_kb (c : cell) (j n : int) (jj : Z) : to_Z j + to_Z n <= 8 -> 0 <= jj < 8 ->
  kb_le (cell_kb (forget c j n) jj) (cell_kb c jj)
  /\ ((to_Z j <=? jj) && (jj <? to_Z j + to_Z n) = true -> cell_kb (forget c j n) jj = KU).
Proof.
  intros H Hjj. destruct c as [w km|t o]; cbn [forget cell_kb].
  - rewrite land_spec', lxor_spec', Z.land_spec, Z.lxor_spec. change (to_Z 255%uint63) with 255.
    rewrite testbit_255 by exact Hjj. rewrite testbit_mask_shift by lia.
    destruct ((to_Z j <=? jj) && (jj <? to_Z j + to_Z n)); cbn [xorb negb].
    + rewrite andb_false_r. split; [left; reflexivity | reflexivity].
    + rewrite andb_true_r. split; [right; reflexivity | discriminate].
  - change (to_Z 0%uint63) with 0. rewrite Z.bits_0. split; [left; reflexivity | reflexivity].
Qed.

Lemma store_cell_kb (rho : valuation) (c : cell) (j : int) (sz : msize) (v : hval) (y : word) (jj : Z) :
  to_Z j + to_Z (nbytes sz) <= 8 -> den rho v y -> 0 <= jj < 8 ->
  let c' := store_cell c j (nbytes sz) sz v in
  if (to_Z j <=? jj) && (jj <? to_Z j + to_Z (nbytes sz))
  then forall b : byte, bv_unsigned b = byteZ (bv_unsigned y) (jj - to_Z j) -> kb_ok rho (cell_kb c' jj) b
  else kb_le (cell_kb c' jj) (cell_kb c jj).
Proof.
  intros H Hv Hjj c'. pose proof (to_Z_bounded j) as Bj.
  assert (Hn1 : 1 <= to_Z (nbytes sz)) by (destruct sz; cbn; change (to_Z 1%uint63) with 1; change (to_Z 2%uint63) with 2; change (to_Z 4%uint63) with 4; change (to_Z 8%uint63) with 8; lia).
  (* [comment removed for export] *)
  assert (Hforget : c' = forget c j (nbytes sz) ->
            if (to_Z j <=? jj) && (jj <? to_Z j + to_Z (nbytes sz))
            then forall b : byte, bv_unsigned b = byteZ (bv_unsigned y) (jj - to_Z j) -> kb_ok rho (cell_kb c' jj) b
            else kb_le (cell_kb c' jj) (cell_kb c jj)).
  { intros ->. destruct (forget_kb c j (nbytes sz) jj H Hjj) as [Hle Hin].
    destruct ((to_Z j <=? jj) && (jj <? to_Z j + to_Z (nbytes sz))); [intros b _; rewrite Hin by reflexivity; exact I | exact Hle]. }
  (* [comment removed for export] *)
  assert (Hins : forall (w0 : w64) (km0 : int) (xw : w64), y = wbv xw ->
            (forall q, 0 <= q < 8 -> (to_Z j <=? q) && (q <? to_Z j + to_Z (nbytes sz)) = false ->
                       kb_le (if Z.testbit (to_Z km0) q then KB (byteZ (wZ w0) q) else KU) (cell_kb c q)) ->
            c' = CW (w_ins w0 j (nbytes sz) xw) (km0 lor (byte_mask (nbytes sz) << j))%uint63 ->
            if (to_Z j <=? jj) && (jj <? to_Z j + to_Z (nbytes sz))
            then forall b : byte, bv_unsigned b = byteZ (bv_unsigned y) (jj - to_Z j) -> kb_ok rho (cell_kb c' jj) b
            else kb_le (cell_kb c' jj) (cell_kb c jj)).
  { intros w0 km0 xw -> Hold ->. cbn [cell_kb]. rewrite lor_spec', Z.lor_spec, testbit_mask_shift by lia.
    rewrite wZ_ins by lia. pose proof (wZ_range w0) as Hw0. rewrite byteZ_insZ by lia.
    destruct ((to_Z j <=? jj) && (jj <? to_Z j + to_Z (nbytes sz))) eqn:Ein.
    - rewrite orb_true_r. intros b Hb. cbn [kb_ok]. rewrite wbv_unsigned in Hb. exact Hb.
    - rewrite orb_false_r. exact (Hold jj Hjj Ein). }
  destruct v as [xw|t o| |tn on].
  - cbn [den] in Hv. destruct sz; cbn [store_cell] in c'.
    1-3: (destruct c as [w km|t o];
          [ apply (Hins w km xw Hv); [intros q _ _; right; reflexivity | reflexivity]
          | apply (Hins w_zero 0%uint63 xw Hv); [intros q _ _; change (to_Z 0%uint63) with 0; rewrite Z.bits_0; left; reflexivity|];
            unfold c'; f_equal; apply to_Z_inj; rewrite lor_spec'; reflexivity ]).
    (* [comment removed for export] *)
    change (to_Z (nbytes SZ8)) with 8 in *. assert (Ej0 : to_Z j = 0) by lia. rewrite Ej0.
    replace ((0 <=? jj) && (jj <? 0 + 8)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    intros b Hb. unfold c'. cbn [cell_kb]. change (to_Z 255%uint63) with 255. rewrite testbit_255 by exact Hjj.
    cbn [kb_ok]. subst y. rewrite wbv_unsigned, Z.sub_0_r in Hb. exact Hb.
  - cbn [den] in Hv. destruct sz; cbn [store_cell] in c'; try (apply Hforget; reflexivity).
    change (to_Z (nbytes SZ8)) with 8 in *. assert (Ej0 : to_Z j = 0) by lia. rewrite Ej0.
    replace ((0 <=? jj) && (jj <? 0 + 8)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    intros b Hb. unfold c'. cbn [cell_kb kb_ok]. subst y. rewrite Z.sub_0_r in Hb. exact Hb.
  - apply Hforget. destruct sz; reflexivity.
  - apply Hforget. destruct sz; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wa_u (z : Z) : 0 <= z < 2 ^ 64 -> bv_unsigned (wa z) = z.
Proof. intros H. apply wa_unsigned. exact H. Qed.

(* [comment removed for export] *)
Lemma mrd_write (m : word -> option byte) (A : Z) (bs : list byte) (z : Z) :
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  mrd segs (write_to_mem m (wa A) bs) (wa z) =
  if (A <=? z) && (z <? A + Z.of_nat (length bs)) then nth_error bs (Z.to_nat (z - A)) else mrd segs m (wa z).
Proof.
  intros HA Hl Hz. unfold mrd. rewrite write_to_mem_spec by lia. rewrite wa_u by exact Hz.
  destruct ((A <=? z) && (z <? A + Z.of_nat (length bs))) eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  destruct (nth_error bs (Z.to_nat (z - A))) as [b|] eqn:En; [reflexivity|]. apply nth_error_None in En. lia.
Qed.

Lemma rd_cell_wr_cell (rg : region) (k k2 : int) (c : cell) :
  to_Z k < 2 ^ Z.of_nat (rg_d rg) -> to_Z k2 < 2 ^ Z.of_nat (rg_d rg) ->
  rd_cell segs (wr_cell rg k c) k2 = if (to_Z k =? to_Z k2) then c else rd_cell segs rg k2.
Proof.
  intros Hk Hk2. unfold rd_cell, wr_cell. cbn [rg_d rg_cells rg_dflt]. rewrite iget_iset.
  pose proof (to_Z_bounded k). pose proof (to_Z_bounded k2). rewrite !Z.mod_small by lia.
  destruct (to_Z k =? to_Z k2); reflexivity.
Qed.

(* [comment removed for export] *)
Definition same_dir (rg rg' : region) : Prop :=
  rg_abs rg' = rg_abs rg /\ rg_size rg' = rg_size rg /\ rg_al rg' = rg_al rg /\ rg_wr rg' = rg_wr rg
  /\ rg_dflt rg' = rg_dflt rg /\ rg_d rg' = rg_d rg.

Lemma same_dir_wr_cell (rg : region) (k : int) (c : cell) : same_dir rg (wr_cell rg k c).
Proof. repeat split. Qed.

Theorem hx_store_sound (rho : valuation) (M M' : mem) (abs : abstab) (m : word -> option byte) (a v : hval) (sz : msize) (x y : word) :
  Rmem rho M m -> den rho a x -> den rho v y -> hx_store segs M abs a sz v = Some M' ->
  store_ok segs m x (msz_nat sz) = true
  /\ Rmem rho M' (write_to_mem m x (Z_to_le_bytes (msz_nat sz) (bv_unsigned y)))
  /\ (exists t rg off, mget M t = Some rg /\ rg_wr rg = true /\ x = wa (rbase rho t rg + to_Z off)
                       /\ to_Z off + Z.of_nat (msz_nat sz) <= to_Z (rg_size rg)
                       /\ exists rg', same_dir rg rg' /\ M' = mset M t rg').
Proof.
  intros HR Ha Hv H. unfold hx_store in H.
  destruct (resolve M abs a (nbytes sz)) as [[[t rg] off]|] eqn:Er; [|discriminate].
  destruct (rg_wr rg) eqn:Ewr; [|discriminate].
  set (j := (off land 7)%uint63) in *. set (k := (off >> 3)%uint63) in *.
  destruct (j + nbytes sz <=? 8)%uint63 eqn:Ejn; [|discriminate]. injection H as <-.
  assert (Hn8 : to_Z (nbytes sz) <= 8) by (destruct sz; cbn; change (to_Z 1%uint63) with 1; change (to_Z 2%uint63) with 2; change (to_Z 4%uint63) with 4; change (to_Z 8%uint63) with 8; lia).
  destruct (resolve_spec rho M abs m a (nbytes sz) x t rg off HR Hn8 Er Ha) as (Eg & -> & Hin).
  pose proof HR as [HRr Hsep]. destruct (HRr t rg Eg) as (HB0 & HB1 & Hs62 & Hd & Hd59 & Hal & Halm & Hbytes).
  set (B := rbase rho t rg) in *. pose proof (to_Z_bounded off) as Bo. rewrite nbytes_Z in Hin, Hn8.
  set (n := msz_nat sz) in *. set (Y := bv_unsigned y). set (bytes := Z_to_le_bytes n Y).
  assert (HY : 0 <= Y) by (pose proof (bv_unsigned_in_range 64 y); unfold Y; lia).
  assert (Hlen : length bytes = n) by apply length_Z_to_le_bytes.
  set (A := B + to_Z off) in *.
  apply leb_spec in Ejn. assert (Ej : to_Z j = to_Z off mod 8) by apply phi_land7.
  pose proof (Z.mod_pos_bound (to_Z off) 8 ltac:(lia)) as Hjr.
  assert (Ejn' : to_Z off mod 8 + Z.of_nat n <= 8).
  { rewrite add_spec, nbytes_Z, Ej in Ejn. change (to_Z 8%uint63) with 8 in Ejn. rewrite wB_eq in *. unfold two63 in *.
    rewrite Z.mod_small in Ejn by lia. exact Ejn. }
  assert (Hk : to_Z k = to_Z off / 8) by apply phi_shr3.
  assert (Hoff : to_Z off = 8 * to_Z k + to_Z j) by (rewrite Hk, Ej; apply Z.div_mod; lia).
  assert (P2d : 0 < 2 ^ Z.of_nat (rg_d rg)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hkd : to_Z k < 2 ^ Z.of_nat (rg_d rg)) by (assert (0 < Z.of_nat n) by (unfold n; destruct sz; cbn; lia); nia).
  split; [|split].
  - (* [comment removed for export] *)
    assert (Hw : wr_at segs m A (Z.of_nat n)).
    { split; [unfold A; lia|]. split; [unfold A, two63 in *; lia|]. intros i Hi.
      destruct (Hbytes (to_Z off + i) ltac:(lia)) as (b & _ & _ & W). unfold A. rewrite <- Z.add_assoc. apply W. exact Ewr. }
    pose proof (wr_at_store_ok segs m A (Z.of_nat n) 0 n Hw ltac:(lia) ltac:(lia)) as E. rewrite Z.add_0_r in E. exact E.
  - (* [comment removed for export] *)
    set (c' := store_cell (rd_cell segs rg k) j (nbytes sz) sz v).
    set (rg' := wr_cell rg k c'). set (m' := write_to_mem m (wa A) bytes).
    assert (HA0 : 0 <= A) by (unfold A; lia). assert (HA1 : A + Z.of_nat (length bytes) <= 2 ^ 64) by (rewrite Hlen; unfold A, two63 in *; lia).
    assert (Hget : forall t2 rg2, mget (mset M t rg') t2 = Some rg2 -> (t2 = t /\ rg2 = rg') \/ (t2 <> t /\ mget M t2 = Some rg2)).
    { intros t2 rg2 G. rewrite (mget_mset M t t2 rg' (mget_lt M t rg Eg)) in G.
      destruct (Z.eqb_spec (to_Z t) (to_Z t2)) as [E|E].
      - left. split; [symmetry; apply to_Z_inj; exact E | congruence].
      - right. split; [intros ->; apply E; reflexivity | exact G]. }
    split.
    + intros t2 rg2 G. destruct (Hget t2 rg2 G) as [[-> ->]|[Hne G2]].
      * (* [comment removed for export] *)
        unfold region_ok. change (rbase rho t rg') with B. cbn [rg' wr_cell rg_size rg_d rg_al rg_wr].
        repeat (split; [assumption|]). intros i Hi.
        assert (Hi64 : 0 <= B + i < 2 ^ 64) by (unfold two63 in *; lia).
        destruct (Hbytes i Hi) as (b & Eb & Kb & Wb).
        assert (Hkb' : rg_kb rg' i = cell_kb (rd_cell segs rg' (of_Z (i / 8))) (i mod 8)) by reflexivity.
        assert (Hi8 : 0 <= i / 8 < 2 ^ Z.of_nat (rg_d rg)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
        assert (Ei8 : to_Z (of_Z (i / 8)) = i / 8) by (rewrite of_Z_spec; apply Z.mod_small; rewrite wB_eq; unfold two63; assert (2 ^ Z.of_nat (rg_d rg) <= 2 ^ 59) by (apply Z.pow_le_mono_r; lia); lia).
        pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Him. pose proof (Z.div_mod i 8 ltac:(lia)) as Edm.
        unfold m'. rewrite (mrd_write m A bytes (B + i) HA0 HA1 Hi64). rewrite Hlen.
        destruct ((A <=? B + i) && (B + i <? A + Z.of_nat n)) eqn:Ein.
        -- apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
           assert (Hq : 0 <= i - to_Z off < Z.of_nat n) by (unfold A in *; lia).
           exists (byte_of Y (i - to_Z off)). split; [|split].
           ++ unfold bytes. replace (B + i - A) with (i - to_Z off) by (unfold A; ring).
              rewrite (nth_Z_to_le_bytes n Y (Z.to_nat (i - to_Z off)) HY ltac:(lia)). rewrite Z2Nat.id by lia. reflexivity.
           ++ rewrite Hkb'. destruct (cell_of_byte off (i - to_Z off) (Z.of_nat n) Ejn' Hq) as [Ec Em].
              replace (to_Z off + (i - to_Z off)) with i in Ec, Em by ring. rewrite Ec, Em. fold k.
              unfold rg'. rewrite rd_cell_wr_cell by assumption. rewrite Z.eqb_refl.
              pose proof (store_cell_kb rho (rd_cell segs rg k) j sz v y (to_Z off mod 8 + (i - to_Z off))
                            ltac:(rewrite nbytes_Z; lia) Hv ltac:(lia)) as SK. cbv zeta in SK. fold c' in SK.
              rewrite nbytes_Z, Ej in SK. fold n in SK.
              replace ((to_Z off mod 8 <=? to_Z off mod 8 + (i - to_Z off)) && (to_Z off mod 8 + (i - to_Z off) <? to_Z off mod 8 + Z.of_nat n)) with true in SK
                by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
              apply SK. rewrite byte_of_unsigned. f_equal. ring.
           ++ intros _. apply wview_write_mono. apply Wb. exact Ewr.
        -- exists b. split; [exact Eb|]. split; [|intros _; apply wview_write_mono; apply Wb; exact Ewr].
           rewrite Hkb'. unfold rg'. rewrite rd_cell_wr_cell by (rewrite ?Ei8; lia). rewrite Ei8.
           destruct (Z.eqb_spec (to_Z k) (i / 8)) as [Ek|Ek].
           ++ (* [comment removed for export] *)
              pose proof (store_cell_kb rho (rd_cell segs rg k) j sz v y (i mod 8) ltac:(rewrite nbytes_Z; lia) Hv ltac:(lia)) as SK.
              cbv zeta in SK. fold c' in SK. rewrite nbytes_Z, Ej in SK. fold n in SK.
              assert (Eout : (to_Z off mod 8 <=? i mod 8) && (i mod 8 <? to_Z off mod 8 + Z.of_nat n) = false).
              { apply andb_false_iff. apply andb_false_iff in Ein. rewrite Z.leb_gt, Z.ltb_ge in *. unfold A in Ein. lia. }
              rewrite Eout in SK. apply (kb_ok_le rho _ _ b SK). unfold rg_kb in Kb.
              replace (of_Z (i / 8)) with k in Kb by (apply to_Z_inj; rewrite Ei8; exact Ek). exact Kb.
           ++ exact Kb.
      * (* [comment removed for export] *)
        destruct (HRr t2 rg2 G2) as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & Cb).
        unfold region_ok. repeat (split; [assumption|]). intros i Hi. destruct (Cb i Hi) as (b & Eb & Kb & Wb).
        exists b. split; [|split; [exact Kb | intros W; apply wview_write_mono; apply Wb; exact W]].
        unfold m'. rewrite (mrd_write m A bytes (rbase rho t2 rg2 + i) HA0 HA1 ltac:(unfold two63 in *; lia)). rewrite Hlen.
        destruct (Hsep t2 t rg2 rg G2 Eg Hne (or_intror Ewr)) as [D|D]; fold B in D.
        -- replace ((A <=? rbase rho t2 rg2 + i) && (rbase rho t2 rg2 + i <? A + Z.of_nat n)) with false; [exact Eb|].
           symmetry. apply andb_false_iff. left. apply Z.leb_gt. unfold A. lia.
        -- replace ((A <=? rbase rho t2 rg2 + i) && (rbase rho t2 rg2 + i <? A + Z.of_nat n)) with false; [exact Eb|].
           symmetry. apply andb_false_iff. right. apply Z.ltb_ge. unfold A. lia.
    + (* [comment removed for export] *)
      intros t1 t2 r1 r2 G1 G2 Hne Hw.
      destruct (Hget t1 r1 G1) as [[-> ->]|[N1 G1']]; destruct (Hget t2 r2 G2) as [[-> ->]|[N2 G2']].
      * exfalso. apply Hne. reflexivity.
      * change (rbase rho t rg') with B. change (rg_size rg') with (rg_size rg). exact (Hsep t t2 rg r2 Eg G2' Hne (or_introl Ewr)).
      * change (rbase rho t rg') with B. change (rg_size rg') with (rg_size rg). exact (Hsep t1 t r1 rg G1' Eg Hne (or_intror Ewr)).
      * exact (Hsep t1 t2 r1 r2 G1' G2' Hne Hw).
  - exists t, rg, off. split; [exact Eg|]. split; [exact Ewr|]. split; [reflexivity|]. split; [exact Hin|].
    eexists. split; [apply same_dir_wr_cell | reflexivity].
Qed.

End MemSound.
