(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim MemSplit ZStores StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs PortLib.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv64_mod : forall a : Z, Z_to_bv 64 (a mod 2^64) = Z_to_bv 64 a.
Proof.
  intros a. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Z.mod_mod. lia.
Qed.

Lemma Z_to_bv64_eqm : forall a b : Z, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
  intros a b H. rewrite <- (Z_to_bv64_mod a), <- (Z_to_bv64_mod b), H. reflexivity.
Qed.

Lemma u_Z2bv_mod : forall a : Z, bv_unsigned (Z_to_bv 64 a) = a mod 2^64.
Proof. intros a. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. Qed.

Lemma zbv_addi : forall a i : Z, v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof.
  intros a i. unfold v_addi. rewrite u_Z2bv_mod. apply Z_to_bv64_eqm.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma zbv_add : forall a b : Z, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold v_add. rewrite !u_Z2bv_mod. apply Z_to_bv64_eqm.
  rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma zbv_sub : forall a b : Z, v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. unfold v_sub. rewrite !u_Z2bv_mod. apply Z_to_bv64_eqm.
  rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma zbv_mul : forall a b : Z, v_mul (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b. unfold v_mul. rewrite !u_Z2bv_mod. apply Z_to_bv64_eqm.
  rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma zbv_slli : forall a k : Z, 0 <= k -> v_slli (Z_to_bv 64 a) k = Z_to_bv 64 (a * 2^k).
Proof.
  intros a k Hk. unfold v_slli. rewrite u_Z2bv_mod, Z.shiftl_mul_pow2 by lia. apply Z_to_bv64_eqm.
  rewrite Zmult_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zbv_srai_small : forall a k : Z, 0 <= a < 2^63 -> 0 <= k ->
  v_srai (Z_to_bv 64 a) k = Z_to_bv 64 (a / 2^k).
Proof.
  intros a k Ha Hk. unfold v_srai. rewrite bv_signed_small by (rewrite u_Z2bv by lia; lia).
  rewrite u_Z2bv, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zbv_addiw_small : forall a i : Z, 0 <= a < 2^64 -> - 2^31 <= a + i < 2^31 ->
  v_addiw (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof.
  intros a i Ha Hai. unfold v_addiw. rewrite u_Z2bv by lia. f_equal.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31)%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma zbv_self : forall x : word, Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply Z_to_bv_bv_unsigned. Qed.

Lemma zbv_addi_w : forall (x : word) i, v_addi x i = Z_to_bv 64 (bv_unsigned x + i).
Proof. intros x i. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint inzr (i : Z) (l : list (Z * Z)) : bool :=
  match l with
  | [] => false
  | (lo, hi) :: r => ((lo <=? i) && (i <? hi)) || inzr i r
  end.

Definition zf (m : word -> option byte) (d : Z) (l : list (Z * Z)) : word -> option byte :=
  fun x => if inzr (bv_unsigned x - d) l then Some (Z_to_bv 8 0) else m x.

Lemma zf_nil : forall m d, zf m d [] = m.
Proof. intros m d. apply functional_extensionality. intros x. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zf_ext : forall m d l1 l2,
  (forall i, inzr i l1 = inzr i l2) -> zf m d l1 = zf m d l2.
Proof.
  intros m d l1 l2 H. apply functional_extensionality. intros x. unfold zf. rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint inzrP (i : Z) (l : list (Z * Z)) : Prop :=
  match l with
  | [] => False
  | (lo, hi) :: r => (lo <= i < hi) \/ inzrP i r
  end.

Lemma inzr_iff : forall i l, inzr i l = true <-> inzrP i l.
Proof.
  intros i l. induction l as [|[lo hi] r IH]; cbn [inzr inzrP].
  - split; [discriminate | tauto].
  - rewrite orb_true_iff, andb_true_iff, Z.leb_le, Z.ltb_lt, IH. tauto.
Qed.

Lemma inzr_eqP : forall i l1 l2, (inzrP i l1 <-> inzrP i l2) -> inzr i l1 = inzr i l2.
Proof.
  intros i l1 l2 H. apply eq_true_iff_eq. rewrite !inzr_iff. exact H.
Qed.

Lemma inzr_trueP : forall i l, inzrP i l -> inzr i l = true.
Proof. intros i l H. apply inzr_iff. exact H. Qed.

Lemma inzr_falseP : forall i l, ~ inzrP i l -> inzr i l = false.
Proof.
  intros i l H. destruct (inzr i l) eqn:E; [|reflexivity]. exfalso. apply H, inzr_iff, E.
Qed.

Lemma zf_extP : forall m d l1 l2,
  (forall i, inzrP i l1 <-> inzrP i l2) -> zf m d l1 = zf m d l2.
Proof. intros m d l1 l2 H. apply zf_ext. intros i. apply inzr_eqP, H. Qed.

(* [comment removed for export] *)
Ltac zf_eqP := apply zf_extP; intros ?i; cbn [inzrP]; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac bool_lia :=
  apply eq_true_iff_eq;
  rewrite ?orb_true_iff, ?andb_true_iff, ?orb_true_iff, ?andb_true_iff, ?Z.leb_le, ?Z.ltb_lt, ?Z.eqb_eq;
  lia.
Ltac inzr_tac :=
  cbn [inzr];
  repeat match goal with |- context [inzr ?i ?L] => destruct (inzr i L) end;
  first [ bool_lia | lia ].

Lemma zf_drop_empty : forall m d lo l, zf m d ((lo, lo) :: l) = zf m d l.
Proof. intros. apply zf_ext. intros i. inzr_tac. Qed.

(* [comment removed for export] *)
Lemma wbytes_zf : forall m d l o (w : nat),
  0 <= d -> 0 <= o -> d + o + Z.of_nat w <= 2^64 ->
  wbytes (zf m d l) (Z_to_bv 64 (d + o)) (zeros w) = zf m d ((o, o + Z.of_nat w) :: l).
Proof.
  intros m d l o w Hd Ho Hnw.
  destruct w as [|w'].
  { cbn [wbytes zeros repeat Z.of_nat]. rewrite Z.add_0_r. symmetry. apply zf_drop_empty. }
  set (w := S w') in *.
  assert (Hw : 1 <= Z.of_nat w) by (subst w; lia).
  apply functional_extensionality. intros x.
  pose proof (u64_range x) as Hx.
  destruct (Z.lt_ge_cases (bv_unsigned x) (d + o)) as [Hlt|Hge].
  - rewrite wbytes_outside by (rewrite length_zeros, u_Z2bv by lia; lia).
    unfold zf. cbn [inzr]. replace ((o <=? bv_unsigned x - d) && (bv_unsigned x - d <? o + Z.of_nat w)) with false by lia.
    reflexivity.
  - destruct (Z.lt_ge_cases (bv_unsigned x) (d + o + Z.of_nat w)) as [Hin|Hout].
    + rewrite wbytes_inside by (rewrite length_zeros, u_Z2bv by lia; lia). rewrite nth_zeros.
      unfold zf. cbn [inzr]. replace ((o <=? bv_unsigned x - d) && (bv_unsigned x - d <? o + Z.of_nat w)) with true by lia.
      reflexivity.
    + rewrite wbytes_outside by (rewrite length_zeros, u_Z2bv by lia; lia).
      unfold zf. cbn [inzr]. replace ((o <=? bv_unsigned x - d) && (bv_unsigned x - d <? o + Z.of_nat w)) with false by lia.
      reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zf_outside : forall m d l (x : word),
  inzr (bv_unsigned x - d) l = false -> zf m d l x = m x.
Proof. intros m d l x H. unfold zf. rewrite H. reflexivity. Qed.

Lemma zf_inside : forall m d l (x : word),
  inzr (bv_unsigned x - d) l = true -> zf m d l x = Some (Z_to_bv 8 0).
Proof. intros m d l x H. unfold zf. rewrite H. reflexivity. Qed.

Lemma zf_grows : forall m d l, mem_grows m (zf m d l).
Proof.
  intros m d l x Hx. unfold zf. destruct (inzr (bv_unsigned x - d) l); [discriminate | exact Hx].
Qed.

Lemma store_ok_zf : forall segs m d l (a : word) n,
  store_ok segs m a n = true -> store_ok segs (zf m d l) a n = true.
Proof. intros. eapply store_ok_mono; [apply zf_grows | eassumption]. Qed.

(* [comment removed for export] *)
Lemma rdn_zf_zeros : forall segs m d l (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall i, a <= i < a + Z.of_nat n -> inzr (i - d) l = true) ->
  rdn segs (zf m d l) (Z_to_bv 64 a) n = Some (zeros n).
Proof.
  intros segs m d l a n Ha Hnw Hall. destruct n as [|n']; [reflexivity|].
  unfold zeros. apply rdn_const; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. apply zf_inside. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma word_to_le_bytes_zero : forall w : nat, word_to_le_bytes w (Z_to_bv 64 0) = zeros w.
Proof.
  induction w as [|w IH]; [reflexivity|].
  unfold word_to_le_bytes in *. cbn [Z_to_le_bytes]. fold (zeros w).
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in *. rewrite Z.shiftr_0_l. rewrite IH. reflexivity.
Qed.

Lemma Z_to_bv8_u0 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0)) = Z_to_bv 8 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_rom_any : forall segs m n (a : word) bs,
  rdn segs (fun _ => None) a n = Some bs ->
  exists bs', rdn segs m a n = Some bs' /\ length bs' = n.
Proof.
  intros segs m n; induction n as [|n IH]; intros a bs H.
  - exists []. split; reflexivity.
  - cbn [rdn] in H |- *.
    destruct (seg_rom segs a) as [b|] eqn:Hr; [|discriminate].
    destruct (rdn segs (fun _ => None) (a + 1) n) as [rest|] eqn:Hrest; [|discriminate].
    destruct (IH (a + 1)%bv rest Hrest) as (bs' & H' & L').
    rewrite H'. destruct (m a) as [b0|]; eexists; (split; [reflexivity | cbn; rewrite L'; reflexivity]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint natseq (i : nat) (k : nat) : list nat :=
  match k with O => [] | S k' => i :: natseq (S i) k' end.

Lemma natseq_In : forall k i j, (i <= j < i + k)%nat -> In j (natseq i k).
Proof.
  induction k as [|k IH]; intros i j Hj; [lia|]. cbn.
  destruct (Nat.eq_dec i j); [left; assumption | right]. apply IH. lia.
Qed.

(* [comment removed for export] *)
Definition rostr_chk (segs : list Segment) (a k : Z) : bool :=
  forallb (fun j => match seg_rom segs (Z_to_bv 64 (a + Z.of_nat j)) with
                    | Some b => negb (Z.eqb (bv_unsigned b) 0) | None => false end)
          (natseq 0 (Z.to_nat k))
  && match seg_rom segs (Z_to_bv 64 (a + k)) with Some b => Z.eqb (bv_unsigned b) 0 | None => false end
  && match rdn segs (fun _ => None) (Z_to_bv 64 a) (Z.to_nat (SSP.rostr_win a k)) with Some _ => true | None => false end.

Lemma rostr_intro : forall segs M a k,
  0 <= k -> SSP.flatZ a (SSP.rostr_win a k) ->
  rostr_chk segs a k = true ->
  (forall i, 0 <= i < SSP.rostr_win a k -> M (Z_to_bv 64 (a + i)) = None) ->
  SSP.rostr segs M a k.
Proof.
  intros segs M a k Hk Hfl Hc HM. unfold rostr_chk in Hc.
  apply andb_true_iff in Hc as [Hc Hrd]. apply andb_true_iff in Hc as [Hall Hnul].
  assert (Hwin : k + 1 <= SSP.rostr_win a k).
  { unfold SSP.rostr_win. pose proof (Z.div_mod (a + k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a + k) 8 ltac:(lia)). lia. }
  split; [exact Hk|]. split; [exact Hfl|]. split.
  { intros i Hi. apply HM. lia. }
  split.
  { intros i Hi. pose proof (forallb_In _ _ (Z.to_nat i) Hall (natseq_In (Z.to_nat k) 0 (Z.to_nat i) ltac:(lia))) as Hb.
    cbn beta in Hb. rewrite Z2Nat.id in Hb by lia.
    destruct (seg_rom segs (Z_to_bv 64 (a + i))) as [b|]; [|discriminate].
    exists b. split; [reflexivity|]. intros E. rewrite E in Hb. discriminate Hb. }
  split.
  { destruct (seg_rom segs (Z_to_bv 64 (a + k))) as [b|]; [|discriminate]. f_equal.
    apply Z.eqb_eq in Hnul. apply bv_eq. rewrite Hnul. reflexivity. }
  destruct (rdn segs (fun _ => None) (Z_to_bv 64 a) (Z.to_nat (SSP.rostr_win a k))) as [bs|] eqn:E; [|discriminate].
  exists bs. rewrite <- E. destruct Hfl as (Ha & Hw0 & Haw). apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
  replace (bv_unsigned x) with (a + (bv_unsigned x - a)) by lia. apply HM. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wr_readable (segs : list Segment) : Prop :=
  forall seg, In seg segs -> seg_writable seg = true -> seg_readable seg = true.

Lemma find_segment_In : forall segs addr n seg,
  find_segment segs addr n = Some seg -> In seg segs.
Proof.
  induction segs as [|s0 rest IH]; intros addr n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (_ && _)%bool; [injection H as <-; left; reflexivity | right; eapply IH; exact H].
Qed.

Lemma wview_readable : forall segs m (a : word) b,
  wr_readable segs ->
  wview segs m a = Some b ->
  (match m a with Some b' => Some b' | None => seg_rom segs a end) = Some b.
Proof.
  intros segs m a b WR H. unfold wview in H.
  destruct (m a) as [b'|]; [exact H|].
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1%Z.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate].
  destruct (seg_writable seg) eqn:Hw; [|discriminate].
  rewrite (WR seg (find_segment_In _ _ _ _ Hf) Hw).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  rewrite H. reflexivity.
Qed.

Lemma store_ok_rdn : forall segs m n (a : word),
  wr_readable segs ->
  store_ok segs m a n = true -> exists bs, rdn segs m a n = Some bs /\ length bs = n.
Proof.
  intros segs m n; induction n as [|n IH]; intros a WR H.
  - exists []. split; reflexivity.
  - cbn [store_ok] in H. cbn [rdn].
    destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
    rewrite (wview_readable segs m a b WR Hv).
    destruct (IH (a + 1)%bv WR H) as (bs & Hbs & Hlen). rewrite Hbs.
    exists (b :: bs). split; [reflexivity | cbn; rewrite Hlen; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma mod4_mod_pow2' : forall t k, 2 <= k -> (t mod 2^k) mod 4 = t mod 4.
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2^(k-2)). change 4 with (2^2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3 : forall x : word,
  v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 ((- bv_unsigned x) mod 4).
Proof.
  intros x. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2^31).
  unfold bv_wrap. change (bv_modulus 32) with (2^32). change (2^2) with 4.
  rewrite mod4_mod_pow2' by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2' by lia.
  rewrite <- Zminus_mod_idemp_r with (b := 2^31).
  change (2^31 mod 4) with 0. rewrite Z.sub_0_r, Z.mod_mod by lia.
  rewrite <- Zplus_mod_idemp_r. change (2^31 mod 4) with 0. rewrite Z.add_0_r. f_equal.
Qed.

(* [comment removed for export] *)
Lemma andi_mpow2 : forall (x : word) (k : Z), 0 < k < 64 ->
  v_andi x (- 2^k) = Z_to_bv 64 (bv_unsigned x - bv_unsigned x mod 2^k).
Proof.
  intros x k Hk. unfold v_andi. f_equal. pose proof (u64_range x) as Hx.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as Hp.
  pose proof (Z.pow_lt_mono_r 2 k 64 ltac:(lia) ltac:(lia)) as Hp64.
  replace (bv_wrap 64 (- 2^k)) with (Z.shiftl (Z.ones (64 - k)) k).
  2:{ rewrite Z.shiftl_mul_pow2, Z.ones_equiv, bv_wrap64_mod by lia.
      rewrite Z.mul_pred_l, <- Z.pow_add_r by lia. replace (64 - k + k) with 64 by lia.
      rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
  replace (bv_unsigned x - bv_unsigned x mod 2^k) with (Z.shiftl (Z.shiftr (bv_unsigned x) k) k).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
      rewrite (Z.div_mod (bv_unsigned x) (2^k)) at 2 by lia. lia. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite (Z.testbit_neg_r (Z.ones _)) by lia. rewrite (Z.testbit_neg_r (Z.shiftr _ _)) by lia. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - k + k) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite (Z_testbit_high 64 (bv_unsigned x)) by lia. reflexivity.
Qed.

Lemma andi_m4 : forall x : word,
  v_andi x (-4) = Z_to_bv 64 (bv_unsigned x - bv_unsigned x mod 4).
Proof. intros x. change (-4)%Z with (- 2^2)%Z. change 4 with (2^2). apply andi_mpow2. lia. Qed.

Lemma andi_m32 : forall x : word,
  v_andi x (-32) = Z_to_bv 64 (bv_unsigned x - bv_unsigned x mod 32).
Proof. intros x. change (-32)%Z with (- 2^5)%Z. change 32 with (2^5). apply andi_mpow2. lia. Qed.

(* [comment removed for export] *)
Lemma andi_4_al4 : forall x : word,
  bv_unsigned x mod 4 = 0 -> v_andi x 4 = Z_to_bv 64 (bv_unsigned x mod 8).
Proof.
  intros x H4. unfold v_andi. f_equal. pose proof (u64_range x) as Hx.
  change (bv_wrap 64 4) with (2^2).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  change 8 with (2^3).
  destruct (Z.eq_dec 2 i) as [<-|Hne].
  - rewrite Z.eqb_refl, andb_true_r. rewrite <- (Z.mod_pow2_bits_low _ 3 2) by lia. reflexivity.
  - replace (2 =? i) with false by (symmetry; apply Z.eqb_neq; lia). rewrite andb_false_r.
    destruct (Z.lt_ge_cases i 3) as [Hl|Hh].
    + (* [comment removed for export] *)
      rewrite Z.mod_pow2_bits_low by lia.
      assert (E : Z.testbit (bv_unsigned x mod 2^2) i = false).
      { change (2^2) with 4. rewrite H4. apply Z.bits_0. }
      rewrite Z.mod_pow2_bits_low in E by lia. rewrite E. reflexivity.
    + rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma andi_lowmask : forall (x : word) (k : Z), 0 <= k < 64 ->
  v_andi x (2^k - 1) = Z_to_bv 64 (bv_unsigned x mod 2^k).
Proof.
  intros x k Hk. unfold v_andi. f_equal. pose proof (u64_range x) as Hx.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as Hp.
  pose proof (Z.pow_lt_mono_r 2 k 64 ltac:(lia) ltac:(lia)) as Hp64.
  rewrite bv_wrap64_mod, Z.mod_small by lia.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. lia.
Qed.

Lemma andi_1 : forall x : word, v_andi x 1 = Z_to_bv 64 (bv_unsigned x mod 2).
Proof. intros x. change 1%Z with (2^1 - 1)%Z at 1. change 2 with (2^1) at 2. apply andi_lowmask. lia. Qed.
Lemma andi_3 : forall x : word, v_andi x 3 = Z_to_bv 64 (bv_unsigned x mod 4).
Proof. intros x. change 3%Z with (2^2 - 1)%Z. change 4 with (2^2). apply andi_lowmask. lia. Qed.
Lemma andi_7 : forall x : word, v_andi x 7 = Z_to_bv 64 (bv_unsigned x mod 8).
Proof. intros x. change 7%Z with (2^3 - 1)%Z. change 8 with (2^3). apply andi_lowmask. lia. Qed.
Lemma andi_15 : forall x : word, v_andi x 15 = Z_to_bv 64 (bv_unsigned x mod 16).
Proof. intros x. change 15%Z with (2^4 - 1)%Z. change 16 with (2^4). apply andi_lowmask. lia. Qed.
Lemma andi_31 : forall x : word, v_andi x 31 = Z_to_bv 64 (bv_unsigned x mod 32).
Proof. intros x. change 31%Z with (2^5 - 1)%Z. change 32 with (2^5). apply andi_lowmask. lia. Qed.

(* [comment removed for export] *)
Lemma zbv_mulw_small : forall a b : Z, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= a * b < 2^31 ->
  v_mulw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b Ha Hb Hab. unfold v_mulw. rewrite !u_Z2bv by lia. f_equal.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31)%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma mod0_sub : forall a k m : Z, 0 < m -> a mod m = 0 -> k mod m = 0 -> (a - k) mod m = 0.
Proof.
  intros a k m Hm Ha Hk. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hk; [|lia].
  destruct Ha as [x Hx], Hk as [y Hy]. apply Z.mod_divide; [lia|]. exists (x - y). lia.
Qed.
Lemma mod0_add : forall a k m : Z, 0 < m -> a mod m = 0 -> k mod m = 0 -> (a + k) mod m = 0.
Proof.
  intros a k m Hm Ha Hk. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hk; [|lia].
  destruct Ha as [x Hx], Hk as [y Hy]. apply Z.mod_divide; [lia|]. exists (x + y). lia.
Qed.
Lemma mod0_mul_l : forall c a m : Z, 0 < m -> c mod m = 0 -> (c * a) mod m = 0.
Proof.
  intros c a m Hm Hc. apply Z.mod_divide in Hc; [|lia]. destruct Hc as [x Hx].
  apply Z.mod_divide; [lia|]. exists (x * a). lia.
Qed.
Lemma mod0_weaken : forall a m n : Z, 0 < n -> a mod (n * m) = 0 -> 0 < m -> a mod n = 0.
Proof.
  intros a m n Hn Ha Hm. apply Z.mod_divide in Ha; [|lia]. destruct Ha as [x Hx].
  apply Z.mod_divide; [lia|]. exists (x * m). lia.
Qed.
Lemma mod16_mod8 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof. intros a H. apply (mod0_weaken a 2 8); [lia | exact H | lia]. Qed.
Lemma mod16_mod4 : forall a, a mod 16 = 0 -> a mod 4 = 0.
Proof. intros a H. apply (mod0_weaken a 4 4); [lia | exact H | lia]. Qed.
Lemma mod8_mod4 : forall a, a mod 8 = 0 -> a mod 4 = 0.
Proof. intros a H. apply (mod0_weaken a 2 4); [lia | exact H | lia]. Qed.

(* [comment removed for export] *)
Lemma Zltb_t : forall a b : Z, a < b -> (a <? b) = true.
Proof. intros. apply Z.ltb_lt. assumption. Qed.
Lemma Zltb_f : forall a b : Z, b <= a -> (a <? b) = false.
Proof. intros. apply Z.ltb_ge. assumption. Qed.

(* [comment removed for export] *)
Lemma v_mulhu_0_l : forall y : word, v_mulhu (Z_to_bv 64 0) y = Z_to_bv 64 0.
Proof. intros y. unfold v_mulhu. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.mul_0_l. reflexivity. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma c_ltu_Z : forall a b : Z, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma c_lts_Z : forall a b : Z, 0 <= a < 2^63 -> 0 <= b < 2^63 ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. rewrite c_lts_small by (rewrite u_Z2bv by lia; lia).
  unfold bv_ltu. rewrite !u_Z2bv by lia. reflexivity.
Qed.

Lemma c_eq_Zm : forall a b : Z,
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a mod 2^64 =? b mod 2^64).
Proof. intros a b. unfold c_eq, bv_eqb. rewrite !u_Z2bv_mod. reflexivity. Qed.

(* [comment removed for export] *)
Lemma v_sltu_Z : forall a b : Z, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof. intros a b Ha Hb. unfold v_sltu. rewrite c_ltu_Z by lia. destruct (a <? b); reflexivity. Qed.

Lemma v_slt_Z : forall a b : Z, 0 <= a < 2^63 -> 0 <= b < 2^63 ->
  v_slt (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof. intros a b Ha Hb. unfold v_slt. rewrite c_lts_Z by lia. destruct (a <? b); reflexivity. Qed.

Lemma v_sltiu_Z : forall a i : Z, 0 <= a < 2^64 -> 0 <= i < 2^64 ->
  v_sltiu (Z_to_bv 64 a) i = Z_to_bv 64 (if a <? i then 1 else 0).
Proof.
  intros a i Ha Hi. unfold v_sltiu. rewrite u_Z2bv, bv_wrap64_mod, Z.mod_small by lia.
  destruct (a <? i); reflexivity.
Qed.

Lemma v_slti_Z : forall a i : Z, 0 <= a < 2^63 ->
  v_slti (Z_to_bv 64 a) i = Z_to_bv 64 (if a <? i then 1 else 0).
Proof.
  intros a i Ha. unfold v_slti, zsig. rewrite bv_signed_small by (rewrite u_Z2bv by lia; lia).
  rewrite u_Z2bv by lia. destruct (a <? i); reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_wbytes_hit4 : forall segs m (a v : word),
  (bv_unsigned a + 4 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

(* [comment removed for export] *)
Ltac rdn_addr e' :=
  match goal with
  | |- rdn _ _ ?a _ = _ =>
      first [ constr_eq a (Z_to_bv 64 e')
            | replace a with (Z_to_bv 64 e') by (rewrite ?zbv_addi; unfold v_addi; unorm; f_equal; lia) ]
  end.

(* [comment removed for export] *)
Ltac rdn_chain :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b ?n = _ =>
      tryif constr_eq a b
      then lazymatch n with
           | 8%nat => apply rdn_wbytes_hit8; unorm; lia
           | 4%nat => apply rdn_wbytes_hit4; unorm; lia
           end
      else (rdn_peel1; rdn_chain)
  | |- _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition disj_apart (a la b lb : Z) : Prop := a + la <= b \/ b + lb <= a.

Ltac use_apart H := unfold disj_apart in H.

(* [comment removed for export] *)
Definition is_aligned (a m : Z) : Prop := a mod m = 0.

Ltac use_aligned H := unfold is_aligned in H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition all_regs32 : list reg :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma reg_in_all : forall r : reg, In r all_regs32.
Proof.
  intros r. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32%Z in Hr.
  rewrite <- (Z_to_bv_bv_unsigned 5 r). set (z := bv_unsigned r) in *. clearbody z.
  assert (H : forall k : nat, (k < 32)%nat -> z = Z.of_nat k -> In (Z_to_bv 5 z) all_regs32).
  { intros k Hk ->. do 32 (destruct k as [|k]; [apply PortLib.in_regs_dec; vm_compute; reflexivity|]). lia. }
  apply (H (Z.to_nat z)); lia.
Qed.

(* [comment removed for export] *)
Ltac regs_agree_enum tac :=
  intros x__ Hx__; pose proof (reg_in_all x__) as HIN__; cbn [all_regs32 In] in HIN__;
  repeat (destruct HIN__ as [EQ__|HIN__];
          [ rewrite <- EQ__ in Hx__ |- *; clear EQ__; first [ solve [exfalso; apply Hx__; in_list] | tac ] | ]);
  try destruct HIN__.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithFP.
Context {fx : FPState}.

Lemma step_sltu_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLTU rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_sltu (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_sltu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_slt_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLT rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_slt (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_slt segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_slti_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_SLT rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_slti (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_slti segs regs pc mem rom w rd rs imm Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_mulw_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 M_MUL rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_mulw (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mulw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_and_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_and (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_xor_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_XOR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_xor (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_xor segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
End WithFP.


(* [comment removed for export] *)
Ltac stepat F D vv tac :=
  lazymatch type of D with
  | decode_any _ = Some (Op ALU_SLTU _ _ _, _) =>
      chain_step; [ reflexivity | eapply step_sltu_at with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl ]
  | decode_any _ = Some (Op ALU_SLT _ _ _, _) =>
      chain_step; [ reflexivity | eapply step_slt_at with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl ]
  | decode_any _ = Some (OpImm ALU_SLT _ _ _, _) =>
      chain_step; [ reflexivity | eapply step_slti_at with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl ]
  | decode_any _ = Some (Mul32 M_MUL _ _ _, _) =>
      chain_step; [ reflexivity | eapply step_mulw_at with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl ]
  | decode_any _ = Some (Op ALU_AND _ _ _, _) =>
      chain_step; [ reflexivity | eapply step_and_at with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl ]
  | decode_any _ = Some (Op ALU_OR _ _ _, _) =>
      chain_step; [ reflexivity | eapply step_or_at with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl ]
  | decode_any _ = Some (Op ALU_XOR _ _ _, _) =>
      chain_step; [ reflexivity | eapply step_xor_at with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl ]
  | _ => stepiv F D vv tac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zval := gres; pin; imm_norm; rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia].
Ltac zv F D v := stepat F D v zval.

(* [comment removed for export] *)
Ltac condZ :=
  pin; rewrite ?c_ltu_Z by lia; rewrite ?c_lts_Z by lia; rewrite ?c_eq_Zm;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq | reflexivity ];
  rewrite ?Z.mod_small by lia; lia.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
