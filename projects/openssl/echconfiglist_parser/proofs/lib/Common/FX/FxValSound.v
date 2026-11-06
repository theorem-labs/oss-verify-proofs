(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector bitvector.tactics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kind_lits :=
  change (to_Z 0%uint63) with 0 in *; change (to_Z 1%uint63) with 1 in *;
  change (to_Z 2%uint63) with 2 in *; change (to_Z 3%uint63) with 3 in *;
  change (to_Z 4%uint63) with 4 in *; change (to_Z 5%uint63) with 5 in *;
  change (to_Z 6%uint63) with 6 in *; change (to_Z 7%uint63) with 7 in *.

Lemma some_inj : forall (A : Type) (x y : A), Some x = Some y -> y = x.
Proof. intros A x y H. injection H as ->. reflexivity. Qed.

Lemma eqb_0_eq : forall t : int, (t =? 0)%uint63 = true -> t = 0%uint63.
Proof. intros t H. apply Uint63.eqb_spec. exact H. Qed.

(* [comment removed for export] *)
Lemma vkind_range (t : int) (k : Z) :
  0 <= k <= 4 -> k * 2 ^ 60 <= to_Z t < (k + 1) * 2 ^ 60 ->
  to_Z (vkind t) = k /\ to_Z (vbase t) = to_Z t - k * 2 ^ 60.
Proof.
  intros Hk B. destruct (fk_tag_decomp t) as [E _].
  destruct (fk_vkind_cases t) as [[B' K]|[[B' K]|[[B' K]|[[B' K]|[[B' K]|[[B' K]|[[B' K]|[B' K]]]]]]]];
    rewrite K in E |- *; kind_lits; lia.
Qed.

Lemma vkind_bounds (t : int) :
  to_Z (vkind t) * 2 ^ 60 <= to_Z t
  /\ (to_Z (vkind t) <= 4 -> to_Z t < (to_Z (vkind t) + 1) * 2 ^ 60).
Proof.
  pose proof (i63_range t) as Ht.
  destruct (fk_vkind_cases t) as [[B' K]|[[B' K]|[[B' K]|[[B' K]|[[B' K]|[[B' K]|[[B' K]|[B' K]]]]]]]];
    rewrite K; kind_lits; lia.
Qed.

Lemma is_linear_spec t : is_linear t = true <-> to_Z t < 2 * 2 ^ 60.
Proof. unfold is_linear. rewrite Uint63.ltb_spec. reflexivity. Qed.

Lemma is_linear_kind t : is_linear t = true -> vkind t = 0%uint63 \/ vkind t = 1%uint63.
Proof.
  intros H. apply is_linear_spec in H.
  destruct (fk_vkind_cases t) as [[B K]|[[B K]|[[B K]|[[B K]|[[B K]|[[B K]|[[B K]|[B K]]]]]]]]; auto; lia.
Qed.

Lemma w_high_spec w : w_high w = true -> 2 ^ 63 <= wZ w.
Proof.
  unfold w_high. rewrite w_fits63_spec. destruct (Z.ltb_spec (wZ w) (2 ^ 63)); [discriminate | auto].
Qed.

Lemma w_is0_wbv w : w_is0 w = true -> wbv w = w0.
Proof. unfold w_is0. intros H. apply w_eqb_true_bv in H. rewrite H. apply wbv_w_zero. Qed.

Lemma w_ones_wbv w : w_eqb w FxExec.w_ones = true -> wbv w = Z_to_bv 64 (-1).
Proof. intros H. apply w_eqb_true_bv in H. rewrite H. exact wbv_w_ones. Qed.

(* [comment removed for export] *)
Lemma lxor_ones64 a : 0 <= a < 2 ^ 64 -> Z.lxor a (Z.ones 64) = Z.ones 64 - a.
Proof.
  intros Ha.
  assert (Hd : Z.land a (Z.lxor a (Z.ones 64)) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.ltb_spec n 64) as [Hlt | Hge].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a n); reflexivity.
    - assert (E : Z.testbit a n = false).
      { rewrite <- (Z.mod_small a (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
      rewrite E. reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ Hd) as E.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in E. lia.
Qed.

Lemma bv_xor_ones (z : word) : bv_xor z (Z_to_bv 64 (-1)) = bv_sub (bv_opp z) (Z_to_bv 64 1).
Proof.
  apply bv_eq. rewrite bv_xor_unsigned, bv_sub_unsigned, bv_opp_unsigned.
  change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64). change (bv_unsigned (Z_to_bv 64 1)) with 1.
  pose proof (bv_unsigned_in_range _ z) as Hz. unfold bv_modulus in Hz. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hz.
  rewrite (lxor_ones64 _ Hz). rewrite !bv_wrap64. change (Z.ones 64) with (2 ^ 64 - 1).
  rewrite Zminus_mod_idemp_l.
  replace (- bv_unsigned z - 1) with (2 ^ 64 - 1 - bv_unsigned z + (-1) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma land_low u m e : 0 <= e -> 0 <= m < 2 ^ e -> Z.land u m = Z.land (u mod 2 ^ e) m.
Proof.
  intros He Hm.
  assert (E : m = Z.land m (Z.ones e)) by (rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  rewrite E at 1. rewrite (Z.land_comm m), Z.land_assoc, Z.land_ones by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_ones_fix m e : 0 <= e -> 0 <= m -> Z.land m (2 ^ e - 1) = m -> m < 2 ^ e.
Proof.
  intros He Hm H. change (2 ^ e - 1) with (Z.pred (2 ^ e)) in H. rewrite <- Z.ones_equiv, Z.land_ones in H by lia.
  rewrite <- H. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

(* [comment removed for export] *)
Lemma land_round z m nm e :
  0 <= e <= 64 -> 0 <= z < 2 ^ 64 -> 0 <= m < 2 ^ 64 -> nm = Z.ones 64 - m -> 0 <= nm < 2 ^ e ->
  Z.land z m = z - Z.land (z mod 2 ^ e) nm.
Proof.
  intros He Hz Hm Hnm Hnme.
  assert (Enm : nm = Z.lxor m (Z.ones 64)) by (rewrite lxor_ones64 by lia; exact Hnm).
  assert (Hdis : Z.land (Z.land z m) (Z.land z nm) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.bits_0, Enm, Z.lxor_spec.
    destruct (Z.ltb_spec n 64) as [Hlt | Hge].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit z n), (Z.testbit m n); reflexivity.
    - assert (E : Z.testbit z n = false).
      { rewrite <- (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
      rewrite E. reflexivity. }
  assert (Hsum : Z.land z m + Z.land z nm = z).
  { rewrite (Z.add_nocarry_lxor _ _ Hdis). apply Z.bits_inj'. intros n Hn.
    rewrite Z.lxor_spec, !Z.land_spec, Enm, Z.lxor_spec.
    destruct (Z.ltb_spec n 64) as [Hlt | Hge].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit z n), (Z.testbit m n); reflexivity.
    - assert (E : Z.testbit z n = false).
      { rewrite <- (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
      rewrite E. reflexivity. }
  rewrite (land_low z nm e) in Hsum by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sx32_low32 (z : word) : low32 (sx32 z) = low32 z.
Proof. apply bv_eq. rewrite !bv_low32_unsigned. apply fk_sx32_unsigned_mod. Qed.

Lemma pow32_div64 : (2 ^ 32 | 2 ^ 64).
Proof. exists (2 ^ 32). reflexivity. Qed.

Lemma alu32_add_sx (p q : word) : sext 64 (alu32 ALU_ADD (low32 p) (low32 q)) = sx32 (bv_add p q).
Proof.
  unfold sx32. change (bv_extract 0 32 (bv_add p q)) with (low32 (bv_add p q)). f_equal.
  unfold alu32, alu. apply bv_eq.
  rewrite bv_add_unsigned, !bv_low32_unsigned, bv_add_unsigned, bv_wrap32, bv_wrap64.
  rewrite <- Zplus_mod. rewrite (Z.mod_mod_divide _ _ _ pow32_div64). reflexivity.
Qed.

Lemma alu32_sub_sx (p q : word) : sext 64 (alu32 ALU_SUB (low32 p) (low32 q)) = sx32 (bv_sub p q).
Proof.
  unfold sx32. change (bv_extract 0 32 (bv_sub p q)) with (low32 (bv_sub p q)). f_equal.
  unfold alu32, alu. apply bv_eq.
  rewrite bv_sub_unsigned, !bv_low32_unsigned, bv_sub_unsigned, bv_wrap32, bv_wrap64.
  rewrite <- Zminus_mod. rewrite (Z.mod_mod_divide _ _ _ pow32_div64). reflexivity.
Qed.

Lemma sx32_add_l (p q : word) : sx32 (bv_add (sx32 p) q) = sx32 (bv_add p q).
Proof. rewrite <- !alu32_add_sx, sx32_low32. reflexivity. Qed.

Lemma sx32_sub_l (p q : word) : sx32 (bv_sub (sx32 p) q) = sx32 (bv_sub p q).
Proof. rewrite <- !alu32_sub_sx, sx32_low32. reflexivity. Qed.

Lemma sx32_sub_r (p q : word) : sx32 (bv_sub p (sx32 q)) = sx32 (bv_sub p q).
Proof. rewrite <- !alu32_sub_sx, sx32_low32. reflexivity. Qed.

(* [comment removed for export] *)
Lemma branch_taken_refl c (x y : word) : branch_taken c x x = branch_taken c y y.
Proof.
  destruct c; cbn [branch_taken]; unfold bv_eqb, bv_lts, bv_ltu;
    rewrite ?Z.eqb_refl, ?Z.ltb_irrefl; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma low32_and31 (y : word) :
  bv_unsigned (bv_and (low32 y) (Z_to_bv 32 31)) = bv_unsigned y mod 32.
Proof.
  rewrite bv_and_unsigned. unfold low32. rewrite bv_extract_unsigned.
  change (bv_unsigned (Z_to_bv 32 31)) with (Z.ones 5). rewrite Z.land_ones by lia.
  rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 5) with 32.
  apply Z.mod_mod_divide. exists (2 ^ 27). reflexivity.
Qed.

Definition is_shift_op (op : aluop) : Prop := match op with ALU_SLL | ALU_SRL | ALU_SRA => True | _ => False end.

Lemma sh32_amount_ext op (x : bv 32) (y y' : word) :
  bv_unsigned y mod 32 = bv_unsigned y' mod 32 -> is_shift_op op ->
  alu32 op x (low32 y) = alu32 op x (low32 y').
Proof.
  intros E Hop.
  assert (Ea : bv_and (low32 y) (Z_to_bv 32 31) = bv_and (low32 y') (Z_to_bv 32 31)).
  { apply bv_eq. rewrite !low32_and31. exact E. }
  unfold alu32, alu. destruct op; try contradiction; rewrite Ea; reflexivity.
Qed.

Lemma sll3_mod32 (x : word) :
  bv_unsigned (alu64 ALU_SLL x (Z_to_bv 64 3)) mod 32 = (bv_unsigned x mod 4) * 8.
Proof.
  unfold alu64, alu. rewrite bv_shiftl_unsigned.
  change (bv_unsigned (bv_and (Z_to_bv 64 3) (Z_to_bv 64 63))) with 3.
  rewrite Z.shiftl_mul_pow2 by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 3) with 8.
  rewrite Z.mod_mod_divide by (exists (2 ^ 59); reflexivity).
  pose proof (bv_unsigned_in_range _ x). Z.div_mod_to_equations. lia.
Qed.

Section ValSound.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.

Definition regs_ok (M : itrie region) : Prop :=
  forall t rg, iget t M = Some rg -> region_ok rho t rg.

Lemma dv_conc : forall w, dv rho (FV 0 w) = wbv w.
Proof. intros w. apply fk_dv_conc. exact Hrho0. Qed.

Lemma dv_tag0 : forall v, (vtag v =? 0)%uint63 = true -> dv rho v = wbv (vw v).
Proof. intros [t w] H. cbn in H. apply eqb_0_eq in H. subst t. apply dv_conc. Qed.

Lemma dv_fv0 : dv rho fv0 = w0.
Proof. unfold fv0. rewrite dv_conc. apply wbv_w_zero. Qed.

(* [comment removed for export] *)
Definition lb (t : int) : word :=
  if ((vkind t =? 1) || (vkind t =? 4))%uint63 then bv_opp (rho (vbase t)) else rho (vbase t).

Lemma dv_lin t w : is_linear t = true -> dv rho (FV t w) = bv_add (lb t) (wbv w).
Proof.
  intros H. unfold dv, lb. cbn [vtag vw]. destruct (is_linear_kind t H) as [-> | ->]; reflexivity.
Qed.

Lemma dv_k24 t w :
  ((vkind t =? 2) || (vkind t =? 4))%uint63 = true -> dv rho (FV t w) = sx32 (bv_add (lb t) (wbv w)).
Proof.
  intros H. unfold dv, lb. cbn [vtag vw].
  apply orb_true_iff in H as [H | H]; apply Uint63.eqb_spec in H; rewrite H; reflexivity.
Qed.

Lemma lb_plain t : to_Z t < 2 ^ 60 -> lb t = rho t.
Proof. intros H. unfold lb. rewrite (fk_vkind_plain t H), (fk_vbase_plain t H). reflexivity. Qed.

Lemma neg_tag_lin t :
  is_linear t = true -> is_linear (neg_tag t) = true /\ lb (neg_tag t) = bv_opp (lb t).
Proof.
  intros H. apply is_linear_spec in H. pose proof (i63_range t) as Ht. unfold neg_tag.
  destruct (ltbP t kind_lim) as [Hlt | Hge]; rewrite fk_kind_lim in *.
  - assert (E : to_Z (t + kind_lim)%uint63 = to_Z t + 2 ^ 60).
    { rewrite add_spec, fk_kind_lim, i63_wB. apply Z.mod_small. lia. }
    destruct (vkind_range (t + kind_lim)%uint63 1 ltac:(lia) ltac:(lia)) as [K B].
    assert (K' : vkind (t + kind_lim)%uint63 = 1%uint63) by (apply to_Z_inj; exact K).
    assert (B' : vbase (t + kind_lim)%uint63 = t) by (apply to_Z_inj; lia).
    split; [apply is_linear_spec; lia |].
    unfold lb at 1. rewrite K', B'. rewrite (lb_plain t Hlt). reflexivity.
  - assert (E : to_Z (t - kind_lim)%uint63 = to_Z t - 2 ^ 60).
    { rewrite sub_spec, fk_kind_lim, i63_wB. apply Z.mod_small. lia. }
    destruct (vkind_range t 1 ltac:(lia) ltac:(lia)) as [K B].
    assert (K' : vkind t = 1%uint63) by (apply to_Z_inj; exact K).
    assert (B' : vbase t = (t - kind_lim)%uint63) by (apply to_Z_inj; lia).
    split; [apply is_linear_spec; lia |].
    rewrite (lb_plain (t - kind_lim)%uint63) by lia.
    unfold lb. rewrite K', B'. cbn [orb]. change ((1 =? 1)%uint63) with true. cbn [orb].
    apply bv_eq. rewrite !bv_opp_unsigned, !bv_wrap64.
    pose proof (bv_unsigned_in_range _ (rho (t - kind_lim)%uint63)) as Hr. unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr.
    rewrite <- (Z.sub_0_l (- bv_unsigned (rho (t - kind_lim)%uint63) mod 2 ^ 64)).
    rewrite Zminus_mod_idemp_r, Z.sub_0_l, Z.opp_involutive. symmetry. apply Z.mod_small. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma k32_form t t' : k32 t = Some t' ->
  (forall w, dv rho (FV t' w) = sx32 (bv_add (lb t) (wbv w)))
  /\ (forall w, sx32 (dv rho (FV t w)) = sx32 (bv_add (lb t) (wbv w))).
Proof.
  unfold k32. intros H. destruct (vkind_bounds t) as [B1 B2].
  destruct (vkind t =? 0)%uint63 eqn:E0.
  { apply Uint63.eqb_spec in E0. rewrite E0 in B1, B2. kind_lits.
    assert (Hpl : to_Z t < 2 ^ 60) by lia.
    apply some_inj in H. subst t'. rewrite (lb_plain t Hpl). split; intros w.
    - rewrite (fk_dv_ktag rho K_LO t w) by (try exact Hpl; cbn; lia). reflexivity.
    - rewrite (fk_dv_plain rho (FV t w)) by exact Hpl. reflexivity. }
  destruct (vkind t =? 1)%uint63 eqn:E1.
  { apply Uint63.eqb_spec in E1. rewrite E1 in B1, B2. kind_lits.
    assert (Hb : to_Z (vbase t) < 2 ^ 60) by (apply fk_vbase_lt; lia).
    apply some_inj in H. subst t'.
    assert (El : lb t = bv_opp (rho (vbase t))) by (unfold lb; rewrite E1; reflexivity).
    rewrite El. split; intros w.
    - rewrite (fk_dv_ktag rho K_NLO (vbase t) w) by (try exact Hb; cbn; lia). reflexivity.
    - unfold dv. cbn [vtag vw]. rewrite E1. reflexivity. }
  destruct ((vkind t =? 2) || (vkind t =? 4))%uint63 eqn:E24; [| discriminate H].
  apply some_inj in H. subst t'. split; intros w.
  - exact (dv_k24 t w E24).
  - rewrite (dv_k24 t w E24). apply fk_sx32_sx32.
Qed.

(* [comment removed for export] *)
Lemma lb_align M t : regs_ok M ->
  bv_unsigned (lb t) mod 2 ^ to_Z (base_align M t) = 0.
Proof.
  intros HM. unfold base_align.
  destruct (iget (vbase t) M) as [rg |] eqn:Hg; [| change (to_Z 0%uint63) with 0; apply Z.mod_1_r].
  destruct (HM _ _ Hg) as (_ & _ & _ & _ & Hal & _).
  pose proof (i63_range (rg_align rg)) as Ha.
  unfold lb. destruct ((vkind t =? 1) || (vkind t =? 4))%uint63; [| exact Hal].
  rewrite bv_opp_unsigned, bv_wrap64.
  destruct (Z.le_gt_cases (to_Z (rg_align rg)) 64) as [Hle | Hgt].
  - rewrite Z.mod_mod_divide
      by (exists (2 ^ (64 - to_Z (rg_align rg))); rewrite <- Z.pow_add_r by lia; f_equal; lia).
    apply Z.mod_opp_l_z; [apply Z.pow_nonzero; lia | exact Hal].
  - (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range _ (rho (vbase t))) as Hr. unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr.
    assert (Hbig : 2 ^ 64 < 2 ^ to_Z (rg_align rg)) by (apply Z.pow_lt_mono_r; lia).
    rewrite Z.mod_small in Hal by lia. rewrite Hal. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma inb_unsigned : forall M t top off rg,
  regs_ok M -> iget t M = Some rg ->
  ((top land 1) =? 0)%uint63 = true -> (rg_lo rg <=? off)%uint63 = true -> (off <=? rg_len rg)%uint63 = true ->
  bv_unsigned (dv rho (FV t (W64 top off))) = bv_unsigned (rho t) + to_Z off
  /\ bv_unsigned (rho t) + to_Z off < 2 ^ 63
  /\ wZ (W64 top off) = to_Z off
  /\ (t <> 0%uint63 -> 0 < bv_unsigned (rho t) + to_Z off).
Proof.
  intros M t top off rg HM Ht Htop Hlo Hoff.
  destruct (HM t rg Ht) as (Hpl & Hl & Hw & Hpos & Hal). clear Hal.
  apply Uint63.leb_spec in Hoff. apply Uint63.leb_spec in Hlo.
  assert (HwZ : wZ (W64 top off) = to_Z off).
  { rewrite wZ_W64. apply Uint63.eqb_spec in Htop.
    assert (to_Z top mod 2 = 0).
    { rewrite <- i63_land1. rewrite Htop. reflexivity. }
    lia. }
  pose proof (Uint63.to_Z_bounded off) as Hb.
  rewrite (fk_dv_plain rho (FV t (W64 top off)) Hpl). cbn [vtag vw].
  rewrite bv_add_unsigned, wbv_unsigned, HwZ.
  pose proof (bv_unsigned_in_range _ (rho t)) as Hr.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. intros Hne. specialize (Hpos Hne). lia.
Qed.

Lemma fv_inb_unsigned : forall M v,
  regs_ok M -> fv_inb M v = true ->
  bv_unsigned (dv rho v) = bv_unsigned (rho (vtag v)) + wZ (vw v)
  /\ bv_unsigned (rho (vtag v)) + wZ (vw v) < 2 ^ 63
  /\ wZ (vw v) < 2 ^ 63.
Proof.
  intros M [t [top off]] HM H. unfold fv_inb in H.
  destruct (iget t M) as [rg|] eqn:Ht; [|discriminate].
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H Hoff]. apply andb_true_iff in H as [Htop Hlo].
  destruct (inb_unsigned M t top off rg HM Ht Htop Hlo Hoff) as (E1 & E2 & E3 & _).
  cbn [vtag vw]. rewrite E3. pose proof (Uint63.to_Z_bounded off).
  pose proof (bv_unsigned_in_range _ (rho t)). split; [exact E1 | split; lia].
Qed.

(* [comment removed for export] *)
Lemma fv_inb_pos : forall M v,
  regs_ok M -> fv_inb M v = true -> vtag v <> 0%uint63 -> 0 < bv_unsigned (dv rho v).
Proof.
  intros M [t [top off]] HM H Hne. unfold fv_inb in H.
  destruct (iget t M) as [rg|] eqn:Ht; [|discriminate].
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H Hoff]. apply andb_true_iff in H as [Htop Hlo].
  destruct (inb_unsigned M t top off rg HM Ht Htop Hlo Hoff) as (E1 & E2 & E3 & E4).
  rewrite E1. exact (E4 Hne).
Qed.

Lemma fv_nonzero_sound : forall M v,
  regs_ok M -> fv_nonzero M v = Some true -> bv_unsigned (dv rho v) <> 0.
Proof.
  intros M [t w] HM H. unfold fv_nonzero in H.
  destruct (t =? 0)%uint63 eqn:Et.
  - apply eqb_0_eq in Et. subst t. rewrite dv_conc, wbv_unsigned.
    injection H as H. destruct (w_eqb w w_zero) eqn:Ew; [discriminate|].
    apply w_eqb_false_iff in Ew. rewrite wZ_w_zero in Ew. exact Ew.
  - assert (Hne : t <> 0%uint63) by (intros ->; rewrite Uint63.eqb_refl in Et; discriminate).
    destruct (fv_inb M (FV t w)) eqn:Hin.
    { pose proof (fv_inb_pos M _ HM Hin Hne). lia. }
    destruct ((vkind t =? 1)%uint63 && w_high w) eqn:EN.
    2:{ (* [comment removed for export] *)
        destruct ((vkind t =? 5)%uint63 && b5_nonzero M (vbase t) w) eqn:E5; [| discriminate H].
        apply andb_true_iff in E5 as [Ek Hb]. apply Uint63.eqb_spec in Ek.
        unfold dv. cbn [vtag vw]. rewrite Ek. change (dvk 5 ?x ?y) with (b5 (bv_add x y)).
        exact (fk_b5_nonzero rho M _ _ HM Hb). }
    apply andb_true_iff in EN as [Ek Hw]. apply Uint63.eqb_spec in Ek. apply w_high_spec in Hw.
    destruct (iget (vbase t) M) as [rg |] eqn:Hg; [| discriminate H].
    destruct (HM _ _ Hg) as (_ & _ & Hlen & _ & _).
    pose proof (i63_range (rg_len rg)) as Hl. pose proof (wZ_range w) as Hwr.
    pose proof (bv_unsigned_in_range _ (rho (vbase t))) as Hr. unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr.
    unfold dv. cbn [vtag vw]. rewrite Ek. change (dvk 1 ?x ?y) with (bv_add (bv_opp x) y).
    rewrite bv_add_unsigned, bv_opp_unsigned, wbv_unsigned, !bv_wrap64.
    rewrite Zplus_mod_idemp_l.
    replace (- bv_unsigned (rho (vbase t)) + wZ w) with (wZ w - bv_unsigned (rho (vbase t))) by lia.
    rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma dv_same_tag_eq : forall t a b, is_linear t = true ->
  (dv rho (FV t a) = dv rho (FV t b) <-> wbv a = wbv b).
Proof.
  intros t a b Hl. rewrite !(dv_lin t _ Hl). split; intros H; [|rewrite H; reflexivity].
  apply bv_eq. apply (f_equal bv_unsigned) in H. rewrite !bv_add_unsigned in H.
  pose proof (bv_unsigned_in_range _ (lb t)). pose proof (bv_unsigned_in_range _ (wbv a)).
  pose proof (bv_unsigned_in_range _ (wbv b)).
  unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
  set (r := bv_unsigned (lb t)) in *. set (x := bv_unsigned (wbv a)) in *. set (y := bv_unsigned (wbv b)) in *.
  assert (E : (r + x - (r + y)) mod 2 ^ 64 = 0) by (rewrite Zminus_mod, H, Z.sub_diag; reflexivity).
  replace (r + x - (r + y)) with (x - y) in E by lia.
  apply Z.mod_divide in E; [|lia]. destruct E as [k Hk]. assert (k = 0) by nia. lia.
Qed.

(* [comment removed for export] *)
Lemma dv_same_word : forall t a b, w_eqb a b = true -> dv rho (FV t a) = dv rho (FV t b).
Proof. intros t a b H. apply w_eqb_true_bv in H. unfold dv. cbn [vtag vw]. rewrite H. reflexivity. Qed.

Lemma inb_ord : forall M t wa wb,
  regs_ok M -> fv_inb M (FV t wa) = true -> fv_inb M (FV t wb) = true ->
  bv_ltu (dv rho (FV t wa)) (dv rho (FV t wb)) = w_ltu wa wb
  /\ bv_lts (dv rho (FV t wa)) (dv rho (FV t wb)) = w_lts wa wb.
Proof.
  intros M ta wa wb HM Ha Hb.
  destruct (fv_inb_unsigned M _ HM Ha) as (A1 & A2 & A3).
  destruct (fv_inb_unsigned M _ HM Hb) as (B1 & B2 & B3). cbn [vtag vw] in *.
  pose proof (bv_unsigned_in_range _ (rho ta)) as Hr. pose proof (wZ_range wa). pose proof (wZ_range wb).
  split.
  - unfold bv_ltu. rewrite A1, B1, w_ltu_spec.
    destruct (Z.ltb_spec (wZ wa) (wZ wb)); destruct (Z.ltb_spec (bv_unsigned (rho ta) + wZ wa) (bv_unsigned (rho ta) + wZ wb)); try reflexivity; lia.
  - unfold bv_lts, bv_signed. rewrite A1, B1, w_lts_spec, !wS_swrap.
    rewrite !bv_swrap_small by (unfold bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
    destruct (Z.ltb_spec (wZ wa) (wZ wb)); destruct (Z.ltb_spec (bv_unsigned (rho ta) + wZ wa) (bv_unsigned (rho ta) + wZ wb)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma ptr_vs_high_sound : forall M p k,
  regs_ok M -> (vtag k =? 0)%uint63 && w_high (vw k) && fv_inb M p = true ->
  bv_unsigned (dv rho p) < 2 ^ 63 <= bv_unsigned (dv rho k).
Proof.
  intros M p k HM H. apply andb_true_iff in H as [H Hin]. apply andb_true_iff in H as [Hk Hh].
  rewrite (dv_tag0 _ Hk), wbv_unsigned. apply w_high_spec in Hh.
  destruct (fv_inb_unsigned M _ HM Hin) as (E1 & E2 & _). rewrite E1. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fv_branch0_sound : forall M c a b bb,
  regs_ok M -> fv_branch0 M c a b = Some bb -> branch_taken c (dv rho a) (dv rho b) = bb.
Proof.
  intros M c a b bb HM H. unfold fv_branch0 in H.
  destruct ((vtag a =? 0)%uint63 && (vtag b =? 0)%uint63) eqn:E0.
  { apply andb_true_iff in E0 as [Ea Eb]. rewrite (dv_tag0 _ Ea), (dv_tag0 _ Eb).
    injection H as <-. symmetry. apply w_branch_spec. }
  destruct (vtag a =? vtag b)%uint63 eqn:Eab.
  - apply Uint63.eqb_spec in Eab. destruct a as [ta wa], b as [tb wb]. cbn [vtag vw] in *. subst tb.
    destruct (w_eqb wa wb) eqn:Ew.
    { (* [comment removed for export] *)
      injection H as <-. rewrite (dv_same_word ta wa wb Ew), w_branch_spec.
      apply w_eqb_true_bv in Ew. rewrite Ew. apply branch_taken_refl. }
    assert (Heq : is_linear ta = true -> bv_eqb (dv rho (FV ta wa)) (dv rho (FV ta wb)) = w_eqb wa wb).
    { intros Hl. rewrite w_eqb_bv. unfold bv_eqb.
      destruct (Z.eqb_spec (bv_unsigned (wbv wa)) (bv_unsigned (wbv wb))) as [E|E].
      - apply bv_eq in E. apply (dv_same_tag_eq ta _ _ Hl) in E. rewrite E. apply Z.eqb_refl.
      - apply Z.eqb_neq. intros E'. apply E. apply bv_eq in E'. apply (dv_same_tag_eq ta _ _ Hl) in E'.
        rewrite E'. reflexivity. }
    destruct c; cbn [branch_taken w_branch] in *.
    1: { destruct (is_linear ta) eqn:Hl; [| discriminate H]. injection H as <-. exact (Heq eq_refl). }
    1: { destruct (is_linear ta) eqn:Hl; [| discriminate H]. injection H as <-. rewrite (Heq eq_refl). reflexivity. }
    all: destruct (fv_inb M (FV ta wa) && fv_inb M (FV ta wb)) eqn:Hin; [|discriminate];
         injection H as <-; apply andb_true_iff in Hin as [Ha Hb];
         destruct (inb_ord M ta wa wb HM Ha Hb) as [Hu Hs]; rewrite ?Hu, ?Hs; reflexivity.
  - (* [comment removed for export] *)
    cbv zeta in H.
    remember ((vtag b =? 0)%uint63 && w_high (vw b) && fv_inb M a) as p1 eqn:Ep1.
    remember ((vtag a =? 0)%uint63 && w_high (vw a) && fv_inb M b) as p2 eqn:Ep2.
    remember (if (vtag a =? 0)%uint63
              then (if (vtag a =? 0)%uint63 && w_eqb (vw a) w_zero then fv_nonzero M b else None)
              else (if (vtag b =? 0)%uint63 && w_eqb (vw b) w_zero then fv_nonzero M a else None)) as q eqn:Eq.
    assert (HP1 : p1 = true -> bv_unsigned (dv rho a) < 2 ^ 63 <= bv_unsigned (dv rho b)).
    { intros E. subst p1. exact (ptr_vs_high_sound M a b HM E). }
    assert (HP2 : p2 = true -> bv_unsigned (dv rho b) < 2 ^ 63 <= bv_unsigned (dv rho a)).
    { intros E. subst p2. exact (ptr_vs_high_sound M b a HM E). }
    assert (NZ : forall x y, (vtag y =? 0)%uint63 = true -> w_eqb (vw y) w_zero = true -> fv_nonzero M x = Some true ->
                 bv_eqb (dv rho x) (dv rho y) = false /\ bv_eqb (dv rho y) (dv rho x) = false).
    { intros x y Ey1 Ey2 Hxy. apply w_eqb_true_iff in Ey2. rewrite wZ_w_zero in Ey2.
      pose proof (fv_nonzero_sound M x HM Hxy) as Hnz.
      rewrite (dv_tag0 _ Ey1). unfold bv_eqb. rewrite wbv_unsigned, Ey2.
      split; apply Z.eqb_neq; lia. }
    assert (Hq : q = Some true -> bv_eqb (dv rho a) (dv rho b) = false).
    { intros Hx. subst q. destruct (vtag a =? 0)%uint63 eqn:Ea.
      - cbn [andb] in Hx. destruct (w_eqb (vw a) w_zero) eqn:Ew; [|discriminate].
        exact (proj2 (NZ b a Ea Ew Hx)).
      - destruct ((vtag b =? 0)%uint63 && w_eqb (vw b) w_zero) eqn:Ey; [|discriminate].
        apply andb_true_iff in Ey as [Ey1 Ey2]. exact (proj1 (NZ a b Ey1 Ey2 Hx)). }
    assert (Hne : p1 || p2 = true -> bv_eqb (dv rho a) (dv rho b) = false).
    { intros EP. unfold bv_eqb. apply Z.eqb_neq.
      apply orb_true_iff in EP as [EP | EP]; [destruct (HP1 EP) | destruct (HP2 EP)]; lia. }
    clear Ep1 Ep2 Eq.
    destruct c; try discriminate H; cbn [branch_taken].
    + (* [comment removed for export] *)
      destruct q as [[|]|].
      * injection H as <-. exact (Hq eq_refl).
      * destruct (p1 || p2) eqn:EP; [| discriminate H]. injection H as <-. exact (Hne eq_refl).
      * destruct (p1 || p2) eqn:EP; [| discriminate H]. injection H as <-. exact (Hne eq_refl).
    + (* [comment removed for export] *)
      destruct q as [[|]|].
      * injection H as <-. rewrite (Hq eq_refl). reflexivity.
      * destruct (p1 || p2) eqn:EP; [| discriminate H]. injection H as <-. rewrite (Hne eq_refl). reflexivity.
      * destruct (p1 || p2) eqn:EP; [| discriminate H]. injection H as <-. rewrite (Hne eq_refl). reflexivity.
    + (* [comment removed for export] *)
      unfold bv_ltu. destruct p1.
      * injection H as <-. destruct (HP1 eq_refl). apply Z.ltb_lt. lia.
      * destruct p2; [| discriminate H]. injection H as <-. destruct (HP2 eq_refl). apply Z.ltb_ge. lia.
    + (* [comment removed for export] *)
      unfold bv_ltu. destruct p1.
      * injection H as <-. destruct (HP1 eq_refl). apply negb_false_iff. apply Z.ltb_lt. lia.
      * destruct p2; [| discriminate H]. injection H as <-. destruct (HP2 eq_refl).
        apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pow2_div64 e : 0 <= e <= 64 -> (2 ^ e | 2 ^ 64).
Proof. intros He. exists (2 ^ (64 - e)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma low_bits_add Y W e : 0 <= e <= 64 -> Y mod 2 ^ e = 0 -> ((Y + W) mod 2 ^ 64) mod 2 ^ e = W mod 2 ^ e.
Proof.
  intros He HY. rewrite (Z.mod_mod_divide _ _ _ (pow2_div64 e He)).
  rewrite Zplus_mod, HY, Z.add_0_l. apply Z.mod_mod. apply Z.pow_nonzero; lia.
Qed.

Lemma and_low_core Y W m e :
  0 <= e <= 64 -> Y mod 2 ^ e = 0 -> 0 <= m < 2 ^ e -> Z.land ((Y + W) mod 2 ^ 64) m = Z.land W m.
Proof.
  intros He HY Hm. rewrite (land_low _ m e), (land_low W m e) by lia.
  rewrite (low_bits_add Y W e He HY). reflexivity.
Qed.

Lemma and_round_core Y W m nm e :
  0 <= e <= 64 -> 0 <= W < 2 ^ 64 -> Y mod 2 ^ e = 0 -> 0 <= m < 2 ^ 64 ->
  nm = Z.ones 64 - m -> 0 <= nm < 2 ^ e ->
  Z.land ((Y + W) mod 2 ^ 64) m = (Y + Z.land W m) mod 2 ^ 64.
Proof.
  intros He HW HY Hm Hnm Hnme.
  assert (Hz : 0 <= (Y + W) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  pose proof (land_round _ m nm e He Hz Hm Hnm Hnme) as E1.
  pose proof (land_round W m nm e He HW Hm Hnm Hnme) as E2.
  rewrite (low_bits_add Y W e He HY) in E1.
  assert (N1 : 0 <= Z.land ((Y + W) mod 2 ^ 64) m) by (apply Z.land_nonneg; left; lia).
  assert (N2 : 0 <= Z.land (W mod 2 ^ e) nm) by (apply Z.land_nonneg; right; lia).
  rewrite E2. set (d := Z.land (W mod 2 ^ e) nm) in *.
  replace (Y + (W - d)) with (Y + W - d) by lia.
  rewrite <- Zminus_mod_idemp_l. rewrite E1. symmetry. apply Z.mod_small. lia.
Qed.

Theorem fv_and_sound : forall M a m v,
  regs_ok M -> fv_and M a m = Some v -> dv rho v = bv_and (dv rho a) (wbv m).
Proof.
  intros M [t w] m v HM H. unfold fv_and in H. cbn [vtag vw] in H. cbv zeta in H.
  pose proof (lb_align M t HM) as Hlb.
  set (al := base_align M t) in *.
  destruct (al <=? 62)%uint63 eqn:Eal; cbn [negb] in H; [| discriminate H].
  apply Uint63.leb_spec in Eal. change (to_Z 62) with 62 in Eal.
  pose proof (i63_range al) as Hal0.
  set (A := W64 0 ((1 << al) - 1)%uint63) in *.
  assert (Hp : 0 < 2 ^ to_Z al < 2 ^ 63).
  { split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
  assert (HA : wZ A = 2 ^ to_Z al - 1).
  { unfold A. rewrite wZ_even_top by reflexivity. rewrite sub_spec, lsl_spec.
    change (to_Z 1) with 1. rewrite Z.mul_1_l, i63_wB.
    rewrite (Z.mod_small (2 ^ to_Z al)) by lia. apply Z.mod_small. lia. }
  assert (MK : forall x, w_eqb (w_alu ALU_AND x A) x = true -> wZ x < 2 ^ to_Z al).
  { intros x Hx. apply w_eqb_true_iff in Hx. cbn [w_alu] in Hx. rewrite wZ_w_and, HA in Hx.
    apply (land_ones_fix _ (to_Z al)); [lia | apply wZ_range | exact Hx]. }
  pose proof (wZ_range w) as Hw. pose proof (wZ_range m) as Hm.
  destruct (is_linear t) eqn:Hl.
  - destruct (w_eqb (w_alu ALU_AND m A) m) eqn:E1.
    + (* [comment removed for export] *)
      apply some_inj in H. subst v. pose proof (MK m E1) as Hmlt.
      rewrite dv_conc, (dv_lin t w Hl). cbn [w_alu]. rewrite wbv_w_and.
      apply bv_eq. rewrite !bv_and_unsigned, bv_add_unsigned, bv_wrap64, !wbv_unsigned.
      symmetry. apply (and_low_core _ _ _ (to_Z al)); [lia | exact Hlb | lia].
    + (* [comment removed for export] *)
      set (nm := w_alu ALU_XOR m FxExec.w_ones) in *.
      destruct (w_eqb (w_alu ALU_AND nm A) nm) eqn:E2; [| discriminate H].
      apply some_inj in H. subst v. pose proof (MK nm E2) as Hnlt.
      assert (Enm : wZ nm = Z.ones 64 - wZ m).
      { unfold nm. cbn [w_alu]. rewrite wZ_w_xor. change (wZ FxExec.w_ones) with (Z.ones 64).
        apply lxor_ones64. exact Hm. }
      rewrite !(dv_lin t _ Hl). cbn [w_alu]. rewrite wbv_w_and.
      apply bv_eq. rewrite bv_and_unsigned, !bv_add_unsigned, bv_and_unsigned, !bv_wrap64, !wbv_unsigned.
      symmetry. apply (and_round_core _ _ _ (wZ nm) (to_Z al)); [lia | exact Hw | exact Hlb | exact Hm | exact Enm |].
      pose proof (wZ_range nm). lia.
  - (* [comment removed for export] *)
    destruct (((vkind t =? 2) || (vkind t =? 4))%uint63 && w_eqb (w_alu ALU_AND m A) m
              && w_ltu m (W64 0 2147483648)) eqn:E; [| discriminate H].
    apply some_inj in H. subst v.
    apply andb_true_iff in E as [E E31]. apply andb_true_iff in E as [Ek E1].
    pose proof (MK m E1) as Hmlt.
    rewrite w_ltu_spec in E31. apply Z.ltb_lt in E31.
    change (wZ (W64 0 2147483648)) with (2 ^ 31) in E31.
    rewrite dv_conc, (dv_k24 t w Ek). cbn [w_alu]. rewrite wbv_w_and.
    apply bv_eq. rewrite !bv_and_unsigned, !wbv_unsigned.
    rewrite (land_low (bv_unsigned (sx32 _)) (wZ m) 32) by lia.
    rewrite fk_sx32_unsigned_mod. rewrite <- (land_low _ (wZ m) 32) by lia.
    rewrite bv_add_unsigned, bv_wrap64, wbv_unsigned.
    symmetry. apply (and_low_core _ _ _ (to_Z al)); [lia | exact Hlb | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bv_xor_comm64 (x y : word) : bv_xor x y = bv_xor y x.
Proof. apply bv_eq. rewrite !bv_xor_unsigned. apply Z.lxor_comm. Qed.
Lemma bv_or_comm64 (x y : word) : bv_or x y = bv_or y x.
Proof. apply bv_eq. rewrite !bv_or_unsigned. apply Z.lor_comm. Qed.
Lemma bv_and_comm64 (x y : word) : bv_and x y = bv_and y x.
Proof. apply bv_eq. rewrite !bv_and_unsigned. apply Z.land_comm. Qed.
Lemma bv_xor_0_r64 (x : word) : bv_xor x w0 = x.
Proof. apply bv_eq. rewrite bv_xor_unsigned. change (bv_unsigned w0) with 0. apply Z.lxor_0_r. Qed.
Lemma bv_or_0_r64 (x : word) : bv_or x w0 = x.
Proof. apply bv_eq. rewrite bv_or_unsigned. change (bv_unsigned w0) with 0. apply Z.lor_0_r. Qed.
Lemma bv_xor_diag64 (x : word) : bv_xor x x = w0.
Proof. apply bv_eq. rewrite bv_xor_unsigned, Z.lxor_nilpotent. reflexivity. Qed.

Theorem fv_alu0_sound : forall M op a b v,
  regs_ok M -> fv_alu0 M op a b = Some v -> dv rho v = alu64 op (dv rho a) (dv rho b).
Proof.
  intros M op [ta wa] [tb wb] v HM H.
  assert (CONC : (ta =? 0)%uint63 && (tb =? 0)%uint63 = true -> forall op',
            dv rho (FV 0 (w_alu op' wa wb)) = alu64 op' (dv rho (FV ta wa)) (dv rho (FV tb wb))).
  { intros E op'. apply andb_true_iff in E as [Ea Eb]. apply eqb_0_eq in Ea, Eb. subst ta tb.
    rewrite !dv_conc. apply w_alu_spec. }
  assert (GEN : forall op', (if (ta =? 0)%uint63 && (tb =? 0)%uint63 then Some (FV 0 (w_alu op' wa wb)) else None) = Some v ->
            dv rho v = alu64 op' (dv rho (FV ta wa)) (dv rho (FV tb wb))).
  { intros op' H'. destruct ((ta =? 0)%uint63 && (tb =? 0)%uint63) eqn:E0; [|discriminate].
    (apply some_inj in H'; subst v). exact (CONC eq_refl _). }
  destruct op; cbn [fv_alu0 vtag vw] in H; cbv zeta in H;
    [ | | exact (GEN _ H) | exact (GEN _ H) | | | exact (GEN _ H) | exact (GEN _ H) | | ].
  - (* [comment removed for export] *)
    destruct (tb =? 0)%uint63 eqn:Eb.
    { apply eqb_0_eq in Eb. subst tb. rewrite (dv_conc wb). destruct (is_linear ta) eqn:La.
      - apply some_inj in H; subst v. rewrite !(dv_lin ta _ La), wbv_w_add. unfold alu64, alu. bv_solve.
      - destruct (w_is0 wb) eqn:Z0; [| discriminate H]. apply some_inj in H; subst v.
        rewrite (w_is0_wbv _ Z0). unfold alu64, alu, w0. bv_solve. }
    destruct (ta =? 0)%uint63 eqn:Ea.
    { apply eqb_0_eq in Ea. subst ta. rewrite (dv_conc wa). destruct (is_linear tb) eqn:Lb.
      - apply some_inj in H; subst v. rewrite !(dv_lin tb _ Lb), wbv_w_add. unfold alu64, alu. bv_solve.
      - destruct (w_is0 wa) eqn:Z0; [| discriminate H]. apply some_inj in H; subst v.
        rewrite (w_is0_wbv _ Z0). unfold alu64, alu, w0. bv_solve. }
    destruct (is_linear ta && (tb =? neg_tag ta)%uint63) eqn:EN; [| discriminate H].
    apply andb_true_iff in EN as [La Et]. apply Uint63.eqb_spec in Et. subst tb.
    destruct (neg_tag_lin ta La) as [Lb Elb].
    apply some_inj in H; subst v.
    rewrite dv_conc, (dv_lin ta _ La), (dv_lin _ _ Lb), Elb, wbv_w_add. unfold alu64, alu. bv_solve.
  - (* [comment removed for export] *)
    destruct (tb =? 0)%uint63 eqn:Eb.
    { apply eqb_0_eq in Eb. subst tb. rewrite (dv_conc wb). destruct (is_linear ta) eqn:La.
      - apply some_inj in H; subst v. rewrite !(dv_lin ta _ La), wbv_w_sub. unfold alu64, alu. bv_solve.
      - destruct (w_is0 wb) eqn:Z0; [| discriminate H]. apply some_inj in H; subst v.
        rewrite (w_is0_wbv _ Z0). unfold alu64, alu, w0. bv_solve. }
    destruct (ta =? tb)%uint63 eqn:Eab.
    { apply Uint63.eqb_spec in Eab. subst tb. destruct (is_linear ta) eqn:La.
      - apply some_inj in H; subst v. rewrite dv_conc, !(dv_lin ta _ La), wbv_w_sub. unfold alu64, alu. bv_solve.
      - destruct (w_eqb wa wb) eqn:Ew; [| discriminate H]. apply some_inj in H; subst v.
        rewrite (dv_same_word ta wa wb Ew), dv_conc, wbv_w_zero. unfold alu64, alu, w0. bv_solve. }
    destruct ((ta =? 0)%uint63 && is_linear tb) eqn:EN; [| discriminate H].
    apply andb_true_iff in EN as [Ea Lb]. apply eqb_0_eq in Ea. subst ta.
    destruct (neg_tag_lin tb Lb) as [Ln Eln].
    apply some_inj in H; subst v.
    rewrite (dv_conc wa), (dv_lin tb _ Lb), (dv_lin _ _ Ln), Eln, wbv_w_sub. unfold alu64, alu. bv_solve.
  - (* [comment removed for export] *)
    destruct ((ta =? 0)%uint63 && (tb =? 0)%uint63) eqn:E0; [(apply some_inj in H; subst v); exact (CONC eq_refl _)|].
    unfold alu64, alu.
    destruct ((ta =? 0)%uint63 && w_eqb wa w_zero) eqn:E1.
    { destruct (fv_nonzero M (FV tb wb)) as [[|]|] eqn:Hnz; try discriminate. (apply some_inj in H; subst v).
      apply andb_true_iff in E1 as [Ea Ew]. apply eqb_0_eq in Ea. subst ta.
      apply w_eqb_true_iff in Ew. rewrite wZ_w_zero in Ew.
      pose proof (fv_nonzero_sound M _ HM Hnz) as Hne. pose proof (bv_unsigned_in_range _ (dv rho (FV tb wb))).
      rewrite !dv_conc. unfold bv_ltu. rewrite wbv_unsigned, Ew.
      destruct (Z.ltb_spec 0 (bv_unsigned (dv rho (FV tb wb)))); [|lia]. apply wbv_w_one. }
    destruct ((tb =? 0)%uint63 && w_eqb wb w_one) eqn:E2.
    { destruct (fv_nonzero M (FV ta wa)) as [[|]|] eqn:Hnz; try discriminate. (apply some_inj in H; subst v).
      apply andb_true_iff in E2 as [Eb Ew]. apply eqb_0_eq in Eb. subst tb.
      apply w_eqb_true_iff in Ew. rewrite wZ_w_one in Ew.
      pose proof (fv_nonzero_sound M _ HM Hnz) as Hne. pose proof (bv_unsigned_in_range _ (dv rho (FV ta wa))).
      rewrite !dv_conc. unfold bv_ltu. rewrite (wbv_unsigned wb), Ew.
      destruct (Z.ltb_spec (bv_unsigned (dv rho (FV ta wa))) 1); [lia|]. apply wbv_w_zero. }
    destruct ((ta =? tb)%uint63 && fv_inb M (FV ta wa) && fv_inb M (FV tb wb)) eqn:E3.
    { (apply some_inj in H; subst v). apply andb_true_iff in E3 as [E3 Hb]. apply andb_true_iff in E3 as [Eab Ha].
      apply Uint63.eqb_spec in Eab. subst tb.
      destruct (inb_ord M ta wa wb HM Ha Hb) as [Hu _]. rewrite Hu, dv_conc.
      cbn [w_alu]. unfold w_sltu. destruct (w_ltu wa wb); [apply wbv_w_one | apply wbv_w_zero]. }
    destruct ((tb =? 0)%uint63 && w_high wb && fv_inb M (FV ta wa)) eqn:E4.
    { (apply some_inj in H; subst v).
      destruct (ptr_vs_high_sound M (FV ta wa) (FV tb wb) HM E4) as [P1 P2].
      rewrite dv_conc. unfold bv_ltu.
      destruct (Z.ltb_spec (bv_unsigned (dv rho (FV ta wa))) (bv_unsigned (dv rho (FV tb wb)))); [apply wbv_w_one | lia]. }
    destruct ((ta =? 0)%uint63 && w_high wa && fv_inb M (FV tb wb)) eqn:E5; [| discriminate H].
    (apply some_inj in H; subst v).
    destruct (ptr_vs_high_sound M (FV tb wb) (FV ta wa) HM E5) as [P1 P2].
    rewrite dv_conc. unfold bv_ltu.
    destruct (Z.ltb_spec (bv_unsigned (dv rho (FV ta wa))) (bv_unsigned (dv rho (FV tb wb)))); [lia | apply wbv_w_zero].
  - (* [comment removed for export] *)
    destruct ((ta =? 0)%uint63 && (tb =? 0)%uint63) eqn:E0; [(apply some_inj in H; subst v); exact (CONC eq_refl _)|].
    unfold alu64, alu.
    destruct (ta =? tb)%uint63 eqn:Eab.
    { apply Uint63.eqb_spec in Eab. subst tb. destruct (w_eqb wa wb) eqn:Ew; [| discriminate H].
      apply some_inj in H; subst v. rewrite (dv_same_word ta wa wb Ew), dv_conc, wbv_w_zero.
      symmetry. apply bv_xor_diag64. }
    destruct (tb =? 0)%uint63 eqn:Eb.
    { apply eqb_0_eq in Eb. subst tb. rewrite (dv_conc wb). destruct (w_is0 wb) eqn:Z0.
      - apply some_inj in H; subst v. rewrite (w_is0_wbv _ Z0). symmetry. apply bv_xor_0_r64.
      - destruct (is_linear ta && w_eqb wb FxExec.w_ones) eqn:EN; [| discriminate H].
        apply andb_true_iff in EN as [La Eo]. destruct (neg_tag_lin ta La) as [Ln Eln].
        apply some_inj in H; subst v. cbn [w_alu].
        rewrite (dv_lin _ _ Ln), Eln, (dv_lin ta _ La), wbv_w_xor, (w_ones_wbv wb Eo).
        change (wbv FxExec.w_ones) with (wbv W64.w_ones). rewrite wbv_w_ones, !bv_xor_ones. bv_solve. }
    destruct (ta =? 0)%uint63 eqn:Ea; [| discriminate H].
    apply eqb_0_eq in Ea. subst ta. rewrite (dv_conc wa). destruct (w_is0 wa) eqn:Z0.
    + apply some_inj in H; subst v. rewrite (w_is0_wbv _ Z0), bv_xor_comm64. symmetry. apply bv_xor_0_r64.
    + destruct (is_linear tb && w_eqb wa FxExec.w_ones) eqn:EN; [| discriminate H].
      apply andb_true_iff in EN as [Lb Eo]. destruct (neg_tag_lin tb Lb) as [Ln Eln].
      apply some_inj in H; subst v. cbn [w_alu].
      rewrite (dv_lin _ _ Ln), Eln, (dv_lin tb _ Lb), wbv_w_xor, (w_ones_wbv wa Eo).
      change (wbv FxExec.w_ones) with (wbv W64.w_ones).
      rewrite wbv_w_ones, (bv_xor_comm64 (Z_to_bv 64 (-1))), !bv_xor_ones. bv_solve.
  - (* [comment removed for export] *)
    destruct ((ta =? 0)%uint63 && (tb =? 0)%uint63) eqn:E0; [(apply some_inj in H; subst v); exact (CONC eq_refl _)|].
    unfold alu64, alu.
    destruct ((tb =? 0)%uint63 && w_is0 wb) eqn:E1.
    { apply andb_true_iff in E1 as [Eb Z0]. apply eqb_0_eq in Eb. subst tb.
      apply some_inj in H; subst v. rewrite (dv_conc wb), (w_is0_wbv _ Z0). symmetry. apply bv_or_0_r64. }
    destruct ((ta =? 0)%uint63 && w_is0 wa) eqn:E2; [| discriminate H].
    apply andb_true_iff in E2 as [Ea Z0]. apply eqb_0_eq in Ea. subst ta.
    apply some_inj in H; subst v. rewrite (dv_conc wa), (w_is0_wbv _ Z0), bv_or_comm64. symmetry. apply bv_or_0_r64.
  - (* [comment removed for export] *)
    destruct ((ta =? 0)%uint63 && (tb =? 0)%uint63) eqn:E0; [(apply some_inj in H; subst v); exact (CONC eq_refl _)|].
    unfold alu64, alu.
    destruct (tb =? 0)%uint63 eqn:Eb.
    { apply eqb_0_eq in Eb. subst tb. rewrite (dv_conc wb). exact (fv_and_sound M _ _ _ HM H). }
    destruct (ta =? 0)%uint63 eqn:Ea; [| discriminate H].
    apply eqb_0_eq in Ea. subst ta. rewrite (dv_conc wa), bv_and_comm64. exact (fv_and_sound M _ _ _ HM H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wZ_w_not w : wZ (w_not w) = 2 ^ 64 - 1 - wZ w.
Proof.
  unfold w_not. rewrite wZ_w_xor. change (wZ FxExec.w_ones) with (wZ W64.w_ones). rewrite wZ_w_ones.
  change (2 ^ 64 - 1) with (Z.ones 64). apply lxor_ones64. apply wZ_range.
Qed.

Lemma wZ_W64_0 x : wZ (W64 0 x) = to_Z x.
Proof. rewrite wZ_W64. change (to_Z 0 mod 2) with 0. lia. Qed.

Lemma ptr_ival_sound : forall M t w lo hi,
  regs_ok M -> ptr_ival M t w = Some (lo, hi) ->
  to_Z lo <= bv_unsigned (dv rho (FV t w)) <= to_Z hi
  /\ bv_unsigned (dv rho (FV t w)) < 2 ^ 63
  /\ bv_unsigned (dv rho (FV t w)) = bv_unsigned (rho t) + wZ w.
Proof.
  intros M t w lo hi HM H. unfold ptr_ival in H.
  destruct (fv_inb M (FV t w)) eqn:Hin; [|discriminate].
  destruct (iget t M) as [rg|] eqn:Ht; [|discriminate]. destruct w as [top off].
  apply some_inj in H. injection H as Elo Ehi.
  pose proof Hin as Hin'. unfold fv_inb in Hin'. rewrite Ht in Hin'.
  apply andb_true_iff in Hin' as [Hin' Hl62]. apply andb_true_iff in Hin' as [Hin' Hoff].
  apply andb_true_iff in Hin' as [Htop Hlo].
  destruct (inb_unsigned M t top off rg HM Ht Htop Hlo Hoff) as (E1 & E2 & E3 & _).
  destruct (HM t rg Ht) as (_ & _ & _ & _ & _ & [Hclo Hchi] & _).
  apply Uint63.leb_spec in Hoff, Hl62. change (to_Z off_bound) with (2 ^ 62) in *.
  pose proof (i63_range off) as Hoff0. pose proof (i63_range (rg_clo rg)) as Hc0.
  pose proof (i63_range (rg_chi rg)) as Hc1.
  rewrite E1, E3. split; [|split; [exact E2 | reflexivity]].
  split.
  - rewrite Elo. destruct (ltbP (rg_clo rg) off_bound) as [C|C]; change (to_Z off_bound) with (2 ^ 62) in C.
    + rewrite Uint63.add_spec, i63_wB, Z.mod_small by lia. lia.
    + lia.
  - rewrite Ehi. destruct (ltbP (rg_chi rg) off_bound) as [C|C]; change (to_Z off_bound) with (2 ^ 62) in C.
    + rewrite Uint63.add_spec, i63_wB, Z.mod_small by lia. lia.
    + change (to_Z 9223372036854775807) with (2 ^ 63 - 1). lia.
Qed.

Lemma fv_ival_sound : forall M v lo hi,
  regs_ok M -> fv_ival M v = Some (lo, hi) -> wZ lo <= bv_unsigned (dv rho v) <= wZ hi.
Proof.
  intros M [t w] lo hi HM H. unfold fv_ival in H.
  destruct (t =? 0)%uint63 eqn:E0.
  { apply eqb_0_eq in E0. subst t. apply some_inj in H. injection H as -> ->.
    rewrite dv_conc, wbv_unsigned. lia. }
  destruct (is_plain t) eqn:Ep.
  { destruct (ptr_ival M t w) as [[l h]|] eqn:Hp; [|discriminate].
    apply some_inj in H. injection H as -> ->.
    destruct (ptr_ival_sound M t w l h HM Hp) as (Hb & _). rewrite !wZ_W64_0. exact Hb. }
  destruct (vkind t =? 1)%uint63 eqn:Ek; [|discriminate].
  destruct (ptr_ival M (vbase t) (w_not w)) as [[l h]|] eqn:Hp; [|discriminate].
  apply some_inj in H.
  pose proof (f_equal fst H) as Elo. pose proof (f_equal snd H) as Ehi. cbn [fst snd] in Elo, Ehi.
  subst lo hi. clear H.
  destruct (ptr_ival_sound M (vbase t) (w_not w) l h HM Hp) as (Hb & Hlt & Ex).
  rewrite !wZ_w_not, !wZ_W64_0.
  assert (EN : bv_unsigned (dv rho (FV t w))
               = 2 ^ 64 - 1 - bv_unsigned (dv rho (FV (vbase t) (w_not w)))).
  { rewrite Ex, wZ_w_not. unfold dv, dvk. cbn [vtag vw]. rewrite Ek.
    rewrite bv_add_unsigned, bv_opp_unsigned, wbv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64).
    pose proof (bv_unsigned_in_range _ (rho (vbase t))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR.
    pose proof (wZ_range w) as HW. rewrite Ex, wZ_w_not in Hlt.
    rewrite Zplus_mod_idemp_l.
    replace (2 ^ 64 - 1 - (bv_unsigned (rho (vbase t)) + (2 ^ 64 - 1 - wZ w)))
      with (- bv_unsigned (rho (vbase t)) + wZ w) by lia.
    apply Z.mod_small. lia. }
  rewrite EN. lia.
Qed.

Lemma fv_ltu_iv_sound : forall M a b r,
  regs_ok M -> fv_ltu_iv M a b = Some r -> bv_ltu (dv rho a) (dv rho b) = r.
Proof.
  intros M a b r HM H. unfold fv_ltu_iv in H.
  destruct (fv_ival M a) as [[la ha]|] eqn:Ia; [|discriminate].
  destruct (fv_ival M b) as [[lb' hb]|] eqn:Ib; [|discriminate].
  pose proof (fv_ival_sound M a la ha HM Ia) as Ha. pose proof (fv_ival_sound M b lb' hb HM Ib) as Hb.
  unfold bv_ltu. rewrite !w_ltu_spec in H.
  destruct (Z.ltb_spec (wZ ha) (wZ lb')) as [C1|C1].
  - apply some_inj in H. subst r. apply Z.ltb_lt. lia.
  - destruct (Z.ltb_spec (wZ la) (wZ hb)) as [C2|C2]; [discriminate|].
    apply some_inj in H. subst r. apply Z.ltb_ge. lia.
Qed.

Lemma fv_branch_iv_sound : forall M c a b bb,
  regs_ok M -> fv_branch_iv M c a b = Some bb -> branch_taken c (dv rho a) (dv rho b) = bb.
Proof.
  intros M c a b bb HM H. unfold fv_branch_iv in H. cbv zeta in H.
  assert (Hap : (match fv_ltu_iv M a b with
                 | Some true => true
                 | _ => match fv_ltu_iv M b a with Some true => true | _ => false end
                 end) = true -> bv_eqb (dv rho a) (dv rho b) = false).
  { intros E. unfold bv_eqb. apply Z.eqb_neq.
    destruct (fv_ltu_iv M a b) as [[|]|] eqn:E1.
    - pose proof (fv_ltu_iv_sound M a b true HM E1) as L. unfold bv_ltu in L. apply Z.ltb_lt in L. lia.
    - destruct (fv_ltu_iv M b a) as [[|]|] eqn:E2; try discriminate.
      pose proof (fv_ltu_iv_sound M b a true HM E2) as L. unfold bv_ltu in L. apply Z.ltb_lt in L. lia.
    - destruct (fv_ltu_iv M b a) as [[|]|] eqn:E2; try discriminate.
      pose proof (fv_ltu_iv_sound M b a true HM E2) as L. unfold bv_ltu in L. apply Z.ltb_lt in L. lia. }
  destruct c; cbn [branch_taken]; try discriminate H.
  - match type of H with (if ?x then _ else _) = _ => destruct x eqn:E end; [|discriminate].
    apply some_inj in H. subst bb. exact (Hap eq_refl).
  - match type of H with (if ?x then _ else _) = _ => destruct x eqn:E end; [|discriminate].
    apply some_inj in H. subst bb. rewrite (Hap eq_refl). reflexivity.
  - exact (fv_ltu_iv_sound M a b bb HM H).
  - destruct (fv_ltu_iv M a b) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H.
    apply some_inj in H. subst bb. rewrite (fv_ltu_iv_sound M a b r HM E). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srl_unsigned (x y : word) :
  bv_unsigned (alu64 ALU_SRL x y) = bv_unsigned x / 2 ^ (bv_unsigned y mod 64).
Proof.
  unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_shamt6.
  apply Z.shiftr_div_pow2. apply Z.mod_pos_bound. lia.
Qed.

Lemma fv_pg_nonzero_sound : forall M v,
  regs_ok M -> fv_pg_nonzero M v = true -> bv_unsigned (dv rho v) <> 0.
Proof.
  intros M [t w] HM H. unfold fv_pg_nonzero in H.
  destruct (vkind t =? 6)%uint63 eqn:Ek; [|discriminate]. apply Uint63.eqb_spec in Ek.
  destruct (fv_ival M (FV (vbase t) w)) as [[lo hi]|] eqn:Ei; [|discriminate].
  rewrite w_ltu_spec in H. apply Z.ltb_lt in H. rewrite wZ_W64 in H. change (to_Z 0 mod 2) with 0 in H.
  change (to_Z 4095) with 4095 in H.
  pose proof (fv_ival_sound M _ lo hi HM Ei) as [Hlo _].
  rewrite (fk_dv_plain rho (FV (vbase t) w)) in Hlo by (cbn [vtag]; apply fk_vbase_lt7). cbn [vtag vw] in Hlo.
  unfold dv. cbn [vtag vw]. rewrite Ek. change (dvk 6 ?x ?y) with (alu64 ALU_SRL (bv_add x y) (Z_to_bv 64 12)).
  rewrite fk_pg_unsigned.
  set (U := bv_unsigned (bv_add (rho (vbase t)) (wbv w))) in *.
  assert (4096 <= U) by lia. clear - H0. intros E. apply Z.div_small_iff in E; lia.
Qed.

Lemma fv_branch_pg_sound : forall M c a b bb,
  regs_ok M -> fv_branch_pg M c a b = Some bb -> branch_taken c (dv rho a) (dv rho b) = bb.
Proof.
  intros M c a b bb HM H. unfold fv_branch_pg in H. cbv zeta in H.
  match type of H with (if ?x then _ else _) = _ => destruct x eqn:E end; [|discriminate].
  assert (Hne : dv rho a <> dv rho b).
  { apply orb_true_iff in E as [E|E]; apply andb_true_iff in E as [Hp Hz]; apply andb_true_iff in Hz as [Ht Hw].
    - pose proof (fv_pg_nonzero_sound M a HM Hp) as Hnz. rewrite (dv_tag0 b Ht).
      apply w_eqb_true_bv in Hw. rewrite Hw, wbv_w_zero. intros Eq. apply Hnz. rewrite Eq. reflexivity.
    - pose proof (fv_pg_nonzero_sound M b HM Hp) as Hnz. rewrite (dv_tag0 a Ht).
      apply w_eqb_true_bv in Hw. rewrite Hw, wbv_w_zero. intros Eq. apply Hnz. rewrite <- Eq. reflexivity. }
  assert (Hf : bv_eqb (dv rho a) (dv rho b) = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros Eq. apply Hne. apply bv_eq. exact Eq. }
  destruct c; try discriminate H; apply some_inj in H; subst bb; cbn [branch_taken]; rewrite Hf; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fv_inb_s_sound : forall M v rg,
  regs_ok M -> fv_inb_s M v = Some rg ->
  iget (vtag v) M = Some rg
  /\ bv_unsigned (dv rho v) = bv_unsigned (rho (vtag v)) + wZ (vw v)
  /\ to_Z (rg_lo rg) <= wZ (vw v) < to_Z (rg_len rg)
  /\ to_Z (rg_len rg) <= 2 ^ 62.
Proof.
  intros M [t [top off]] rg HM H. unfold fv_inb_s in H.
  destruct (iget t M) as [rg0|] eqn:Ht; [|discriminate].
  match type of H with (if ?x then _ else _) = _ => destruct x eqn:E end; [|discriminate].
  apply some_inj in H. subst rg0.
  apply andb_true_iff in E as [E Hlen]. apply andb_true_iff in E as [E Hoff]. apply andb_true_iff in E as [Htop Hlo].
  pose proof Hoff as Hoff'. apply Uint63.ltb_spec in Hoff'.
  assert (Hoffle : (off <=? rg_len rg)%uint63 = true) by (apply Uint63.leb_spec; lia).
  destruct (inb_unsigned M t top off rg HM Ht Htop Hlo Hoffle) as (E1 & _ & E3 & _).
  cbn [vtag vw]. rewrite E3. apply Uint63.leb_spec in Hlo, Hlen.
  change (to_Z off_bound) with (2 ^ 62) in Hlen.
  split; [exact Ht|]. split; [exact E1|]. split; [lia | exact Hlen].
Qed.

Lemma rg_not_below_sound : forall M ta tb ra rb,
  regs_ok M -> iget ta M = Some ra -> iget tb M = Some rb ->
  to_Z (rg_len ra) <= 2 ^ 62 -> to_Z (rg_lo rb) <= to_Z (rg_len rb) -> to_Z (rg_len rb) <= 2 ^ 62 ->
  rg_not_below ra rb = true ->
  bv_unsigned (rho tb) + to_Z (rg_lo rb) < bv_unsigned (rho ta) + to_Z (rg_len ra).
Proof.
  intros M ta tb ra rb HM Ha Hb Hla Hlob Hlb H. unfold rg_not_below in H.
  apply andb_true_iff in H as [H Hlt]. apply andb_true_iff in H as [Hca Hcb].
  apply Uint63.ltb_spec in Hca, Hcb, Hlt. change (to_Z off_bound) with (2 ^ 62) in Hca, Hcb.
  destruct (HM ta ra Ha) as (_ & _ & _ & _ & _ & [Hcloa _] & _).
  destruct (HM tb rb Hb) as (_ & _ & _ & _ & _ & [_ Hchib] & _).
  pose proof (Uint63.to_Z_bounded (rg_clo ra)). pose proof (Uint63.to_Z_bounded (rg_chi rb)).
  pose proof (Uint63.to_Z_bounded (rg_lo rb)). pose proof (Uint63.to_Z_bounded (rg_len ra)).
  rewrite !Uint63.add_spec in Hlt. change wB with (2 ^ 63) in *.
  rewrite !Z.mod_small in Hlt by lia. lia.
Qed.

Lemma fv_branch_sep_sound : forall M c a b bb,
  regs_ok M -> regions_sep rho M ->
  fv_branch_sep M c a b = Some bb -> branch_taken c (dv rho a) (dv rho b) = bb.
Proof.
  intros M c a b bb HM Hsep H. unfold fv_branch_sep in H.
  destruct (vtag a =? vtag b)%uint63 eqn:Et; [discriminate|]. apply eqb_false_spec in Et.
  destruct (fv_inb_s M a) as [ra|] eqn:Ia; [|discriminate].
  destruct (fv_inb_s M b) as [rb|] eqn:Ib; [|discriminate].
  destruct (fv_inb_s_sound M a ra HM Ia) as (Ga & Ua & Oa & La).
  destruct (fv_inb_s_sound M b rb HM Ib) as (Gb & Ub & Ob & Lb).
  pose proof (Hsep (vtag a) (vtag b) ra rb Et Ga Gb) as Hd.
  assert (Hne : bv_unsigned (dv rho a) <> bv_unsigned (dv rho b)) by lia.
  assert (Hf : bv_eqb (dv rho a) (dv rho b) = false) by (unfold bv_eqb; apply Z.eqb_neq; exact Hne).
  assert (Hab : rg_not_below ra rb = true -> bv_unsigned (dv rho b) < bv_unsigned (dv rho a)).
  { intros Hnb. pose proof (rg_not_below_sound M _ _ ra rb HM Ga Gb La ltac:(lia) Lb Hnb). lia. }
  assert (Hba : rg_not_below rb ra = true -> bv_unsigned (dv rho a) < bv_unsigned (dv rho b)).
  { intros Hnb. pose proof (rg_not_below_sound M _ _ rb ra HM Gb Ga Lb ltac:(lia) La Hnb). lia. }
  destruct c; try discriminate H; cbn [branch_taken].
  - apply some_inj in H. subst bb. exact Hf.
  - apply some_inj in H. subst bb. rewrite Hf. reflexivity.
  - unfold bv_ltu. destruct (rg_not_below ra rb) eqn:E1.
    + apply some_inj in H. subst bb. apply Z.ltb_ge. specialize (Hab eq_refl). lia.
    + destruct (rg_not_below rb ra) eqn:E2; [|discriminate].
      apply some_inj in H. subst bb. apply Z.ltb_lt. exact (Hba eq_refl).
  - unfold bv_ltu. destruct (rg_not_below ra rb) eqn:E1.
    + apply some_inj in H. subst bb. apply negb_true_iff. apply Z.ltb_ge. specialize (Hab eq_refl). lia.
    + destruct (rg_not_below rb ra) eqn:E2; [|discriminate].
      apply some_inj in H. subst bb. apply negb_false_iff. apply Z.ltb_lt. exact (Hba eq_refl).
Qed.

Theorem fv_branch_sound : forall M c a b bb,
  regs_ok M -> regions_sep rho M ->
  fv_branch M c a b = Some bb -> branch_taken c (dv rho a) (dv rho b) = bb.
Proof.
  intros M c a b bb HM Hsep H. unfold fv_branch in H.
  destruct (fv_branch0 M c a b) as [r|] eqn:E0.
  - apply some_inj in H. subst bb. exact (fv_branch0_sound M c a b r HM E0).
  - destruct (fv_branch_iv M c a b) as [r|] eqn:E1.
    + apply some_inj in H. subst bb. exact (fv_branch_iv_sound M c a b r HM E1).
    + destruct (fv_branch_pg M c a b) as [r|] eqn:E2.
      * apply some_inj in H. subst bb. exact (fv_branch_pg_sound M c a b r HM E2).
      * exact (fv_branch_sep_sound M c a b bb HM Hsep H).
Qed.

(* [comment removed for export] *)
Lemma fv_shadow_sound : forall M a b v,
  regs_ok M -> fv_shadow M a b = Some v -> dv rho v = alu64 ALU_SRL (dv rho a) (dv rho b).
Proof.
  intros M [t w] [tb wb] v HM H. unfold fv_shadow in H.
  destruct ((tb =? 0)%uint63 && w_eqb wb (W64 0 3) && fv_inb M (FV t w)) eqn:C; [|discriminate].
  apply andb_true_iff in C as [C Hin]. apply andb_true_iff in C as [Etb Ewb].
  apply eqb_0_eq in Etb. subst tb.
  destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
  destruct (iget (t + 1)%uint63 M) as [rg'|] eqn:Hg'; [|discriminate].
  destruct (rg_kind rg') as [|p] eqn:Ek; [discriminate|].
  destruct ((p =? t)%uint63 && (3 <=? rg_align rg)%uint63 && (rg_align rg <? 64)%uint63) eqn:C2; [|discriminate].
  apply andb_true_iff in C2 as [C2 Hal64]. apply andb_true_iff in C2 as [Ep Hal3].
  apply Uint63.eqb_spec in Ep. subst p. apply Uint63.leb_spec in Hal3. apply Uint63.ltb_spec in Hal64.
  change (to_Z 3) with 3 in Hal3. change (to_Z 64) with 64 in Hal64.
  apply some_inj in H. subst v.
  destruct (fv_inb_unsigned M _ HM Hin) as (Ea & Ea63 & Ew63). cbn [vtag vw] in Ea, Ea63, Ew63.
  destruct (HM t rg Hg) as (_ & _ & _ & _ & Halign & _).
  destruct (HM _ rg' Hg') as (Hpl' & _ & _ & _ & _ & _ & Hk). rewrite Ek in Hk. cbn [rkind_ok] in Hk.
  destruct Hk as [_ Hsh].
  assert (H8 : bv_unsigned (rho t) mod 8 = 0).
  { pose proof (i63_range (rg_align rg)) as Hr.
    apply Z.mod_divide in Halign; [|apply Z.pow_nonzero; lia]. apply Z.mod_divide; [lia|].
    eapply Z.divide_trans; [|exact Halign]. exists (2 ^ (to_Z (rg_align rg) - 3)).
    change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  apply w_eqb_true_iff in Ewb. rewrite wZ_W64_0 in Ewb. change (to_Z 3) with 3 in Ewb.
  apply bv_eq. rewrite (fk_dv_plain rho (FV (t + 1)%uint63 _) Hpl'). cbn [vtag vw].
  rewrite bv_add_unsigned, wbv_unsigned, wZ_w_sub, wZ_w_srl, !wZ_W64_0.
  change (to_Z 3 mod 64) with 3. change (2 ^ 3) with 8.
  unfold alu64, alu. rewrite bv_shiftr_unsigned, dv_conc.
  assert (Esh : bv_unsigned (bv_and (wbv wb) (Z_to_bv 64 63)) = 3).
  { rewrite bv_and_unsigned, wbv_unsigned, Ewb. reflexivity. }
  rewrite Esh, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite Ea, Hsh.
  pose proof (bv_unsigned_in_range _ (rho t)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  pose proof (wZ_range w) as Hw. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (to_Z shadow_K) with 2147450880.
  rewrite Zplus_mod_idemp_r.
  replace (bv_unsigned (rho t) / 8 + 2147450880 + (wZ w / 8 - 2147450880))
    with (bv_unsigned (rho t) / 8 + wZ w / 8) by lia.
  assert (Ediv : (bv_unsigned (rho t) + wZ w) / 8 = bv_unsigned (rho t) / 8 + wZ w / 8).
  { clear - H8. Z.div_mod_to_equations. lia. }
  rewrite Ediv. apply Z.mod_small.
  clear - Hr Hw Ea63. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma fv_pg_sound : forall a wb v,
  fv_pg a wb = Some v -> dv rho v = alu64 ALU_SRL (dv rho a) (wbv wb).
Proof.
  intros [t w] wb v H. unfold fv_pg in H.
  destruct (is_plain t && negb (t =? 0)%uint63 && w_eqb wb (W64 0 12)) eqn:C; [|discriminate].
  apply some_inj in H. subst v. apply andb_true_iff in C as [C Hw]. apply andb_true_iff in C as [Hpl _].
  unfold is_plain in Hpl. apply Uint63.ltb_spec in Hpl. change (to_Z kind_lim) with (2 ^ 60) in Hpl.
  apply w_eqb_true_bv in Hw. rewrite Hw.
  rewrite (fk_dv_ktag7 rho K_PG t w) by (try exact Hpl; cbn; lia). rewrite fk_dvk_PG.
  rewrite (fk_dv_plain rho (FV t w)) by exact Hpl. reflexivity.
Qed.

Lemma fv_srl_sound : forall M a b v,
  regs_ok M -> fv_srl M a b = Some v -> dv rho v = alu64 ALU_SRL (dv rho a) (dv rho b).
Proof.
  intros M a [tb wb] v HM H. unfold fv_srl in H.
  destruct (tb =? 0)%uint63 eqn:Etb; [|discriminate]. apply eqb_0_eq in Etb. subst tb. rewrite dv_conc.
  destruct (fv_ival M a) as [[lo hi]|] eqn:Ei; [|exact (fv_pg_sound a wb v H)].
  destruct (w_eqb (w_srl lo wb) (w_srl hi wb)) eqn:Ec; [|exact (fv_pg_sound a wb v H)].
  apply some_inj in H. subst v. rewrite dv_conc.
  apply w_eqb_true_iff in Ec. rewrite !wZ_w_srl in Ec.
  pose proof (fv_ival_sound M a lo hi HM Ei) as [Hlo Hhi].
  apply bv_eq. rewrite srl_unsigned, !wbv_unsigned, wZ_w_srl.
  set (d := 2 ^ (wZ wb mod 64)) in *.
  assert (Hd : 0 < d) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]).
  symmetry. apply (fk_div_bounded (wZ lo) (wZ hi)); [exact Hd | lia | exact Ec].
Qed.

(* [comment removed for export] *)
Lemma fv_sl3_sound : forall a b v,
  fv_sl3 a b = Some v -> dv rho v = alu64 ALU_SLL (dv rho a) (dv rho b).
Proof.
  intros [t w] [tb wb] v H. unfold fv_sl3 in H.
  destruct (is_plain t && negb (t =? 0)%uint63 && (tb =? 0)%uint63 && w_eqb wb (W64 0 3)) eqn:C; [|discriminate].
  apply some_inj in H. subst v. apply andb_true_iff in C as [C Hw]. apply andb_true_iff in C as [C Etb].
  apply andb_true_iff in C as [Hpl _]. apply eqb_0_eq in Etb. subst tb.
  unfold is_plain in Hpl. apply Uint63.ltb_spec in Hpl. change (to_Z kind_lim) with (2 ^ 60) in Hpl.
  apply w_eqb_true_bv in Hw. rewrite dv_conc, Hw.
  rewrite (fk_dv_ktag7 rho K_SL3 t w) by (try exact Hpl; cbn; lia). rewrite fk_dvk_SL3.
  rewrite (fk_dv_plain rho (FV t w)) by exact Hpl. reflexivity.
Qed.

Theorem fv_alu_sound : forall M op a b v,
  regs_ok M -> fv_alu M op a b = Some v -> dv rho v = alu64 op (dv rho a) (dv rho b).
Proof.
  intros M op a b v HM H. unfold fv_alu in H.
  destruct (fv_alu0 M op a b) as [v0|] eqn:E0.
  - apply some_inj in H. subst v. exact (fv_alu0_sound M op a b v0 HM E0).
  - destruct op; try discriminate H.
    + exact (fv_sl3_sound a b v H).
    + destruct (fv_ltu_iv M a b) as [r|] eqn:E; [|discriminate].
      apply some_inj in H. subst v. rewrite dv_conc. unfold alu64, alu.
      rewrite (fv_ltu_iv_sound M a b r HM E). destruct r; [apply wbv_w_one | apply wbv_w_zero].
    + destruct (fv_shadow M a b) as [v1|] eqn:Es.
      * apply some_inj in H. subst v. exact (fv_shadow_sound M a b v1 HM Es).
      * exact (fv_srl_sound M a b v HM H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma abs_addr_dv : forall M a n, regs_ok M -> dv rho (abs_addr M a n) = dv rho a.
Proof.
  intros M [t [top off]] n HM. unfold abs_addr.
  destruct (t =? 0)%uint63 eqn:E0; [|reflexivity]. apply eqb_0_eq in E0. subst t.
  destruct (abs_find M off n) as [t'|]; [|reflexivity].
  destruct (iget t' M) as [rg|] eqn:Hg; [|reflexivity].
  destruct (is_abs rg && (t' <? kind_lim)%uint63) eqn:Ea; [|reflexivity].
  apply andb_true_iff in Ea as [Ea _]. unfold is_abs in Ea. apply andb_true_iff in Ea as [E1 E2].
  apply Uint63.eqb_spec in E1, E2.
  destruct (HM t' rg Hg) as (Hpl & _ & _ & _ & _ & [Hclo Hchi] & _).
  rewrite E2 in Hchi. change (to_Z 0) with 0 in Hchi.
  pose proof (bv_unsigned_in_range _ (rho t')) as Hr.
  assert (Er : rho t' = Z_to_bv 64 0) by (apply bv_eq; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia).
  rewrite (fk_dv_plain rho (FV t' (W64 top off)) Hpl), dv_conc. cbn [vtag vw]. rewrite Er.
  apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  rewrite Z.add_0_l. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma fm_load_abs_inv : forall IM M a sz sgn v,
  regs_ok M -> fm_load_abs IM M a sz sgn = Some v ->
  exists a', dv rho a' = dv rho a /\ fm_load IM M a' sz sgn = Some v.
Proof.
  intros IM M a sz sgn v HM H. unfold fm_load_abs in H.
  destruct (fm_load IM M a sz sgn) as [v0|] eqn:E.
  - exists a. split; [reflexivity|]. rewrite E. exact H.
  - destruct (vtag a =? 0)%uint63; [|discriminate].
    exists (abs_addr M a (msz_int sz)). split; [apply abs_addr_dv; exact HM | exact H].
Qed.

Lemma fm_store_abs_inv : forall IM M a sz v M',
  regs_ok M -> fm_store_abs IM M a sz v = Some M' ->
  exists a', dv rho a' = dv rho a /\ fm_store IM M a' sz v = Some M'.
Proof.
  intros IM M a sz v M' HM H. unfold fm_store_abs in H.
  destruct (fm_store IM M a sz v) as [M0|] eqn:E.
  - exists a. split; [reflexivity|]. rewrite E. exact H.
  - destruct (vtag a =? 0)%uint63; [|discriminate].
    exists (abs_addr M a (msz_int sz)). split; [apply abs_addr_dv; exact HM | exact H].
Qed.

Lemma fv_conc2_sound : forall f g a b v,
  (forall x y, wbv (f x y) = g (wbv x) (wbv y)) ->
  fv_conc2 f a b = Some v -> dv rho v = g (dv rho a) (dv rho b).
Proof.
  intros f g a b v Hfg H. unfold fv_conc2 in H.
  destruct ((vtag a =? 0)%uint63 && (vtag b =? 0)%uint63) eqn:E; [|discriminate].
  apply andb_true_iff in E as [Ea Eb]. (apply some_inj in H; subst v).
  rewrite dv_conc, (dv_tag0 _ Ea), (dv_tag0 _ Eb). apply Hfg.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fv_alu32_sound : forall op a b v,
  fv_alu32 op a b = Some v ->
  dv rho v = sext 64 (alu32 op (low32 (dv rho a)) (low32 (dv rho b))).
Proof.
  intros op [ta wa] [tb wb] v H. unfold fv_alu32 in H. cbn [vtag vw] in H. cbv zeta in H.
  destruct ((ta =? 0)%uint63 && (tb =? 0)%uint63) eqn:E0.
  { apply andb_true_iff in E0 as [Ea Eb]. apply eqb_0_eq in Ea, Eb. subst ta tb.
    apply some_inj in H; subst v. rewrite !dv_conc. apply w_alu32_spec. }
  destruct op; try discriminate H.
  - (* [comment removed for export] *)
    rewrite alu32_add_sx.
    destruct (tb =? 0)%uint63 eqn:Eb.
    { apply eqb_0_eq in Eb. subst tb. destruct (k32 ta) as [t' |] eqn:Ek; [| discriminate H].
      apply some_inj in H; subst v. destruct (k32_form _ _ Ek) as [F1 F2].
      rewrite F1, (dv_conc wb), wbv_w_add, <- (sx32_add_l (dv rho (FV ta wa))), F2, sx32_add_l. f_equal. bv_solve. }
    destruct (ta =? 0)%uint63 eqn:Ea; [| discriminate H].
    apply eqb_0_eq in Ea. subst ta. destruct (k32 tb) as [t' |] eqn:Ek; [| discriminate H].
    apply some_inj in H; subst v. destruct (k32_form _ _ Ek) as [F1 F2].
    rewrite F1, (dv_conc wa), wbv_w_add.
    replace (bv_add (wbv wa) (dv rho (FV tb wb))) with (bv_add (dv rho (FV tb wb)) (wbv wa)) by bv_solve.
    rewrite <- (sx32_add_l (dv rho (FV tb wb))), F2, sx32_add_l. f_equal. bv_solve.
  - (* [comment removed for export] *)
    rewrite alu32_sub_sx.
    destruct (tb =? 0)%uint63 eqn:Eb.
    { apply eqb_0_eq in Eb. subst tb. destruct (k32 ta) as [t' |] eqn:Ek; [| discriminate H].
      apply some_inj in H; subst v. destruct (k32_form _ _ Ek) as [F1 F2].
      rewrite F1, (dv_conc wb), wbv_w_sub, <- (sx32_sub_l (dv rho (FV ta wa))), F2, sx32_sub_l. f_equal. bv_solve. }
    destruct ((ta =? tb)%uint63 && is_linear ta) eqn:ES.
    { apply andb_true_iff in ES as [Eab La]. apply Uint63.eqb_spec in Eab. subst tb.
      apply some_inj in H; subst v.
      rewrite dv_conc, w_alu32_spec, alu32_sub_sx, !(dv_lin ta _ La). f_equal. bv_solve. }
    destruct ((ta =? 0)%uint63 && is_linear tb) eqn:EN; [| discriminate H].
    apply andb_true_iff in EN as [Ea Lb]. apply eqb_0_eq in Ea. subst ta.
    destruct (neg_tag_lin tb Lb) as [Ln Eln].
    destruct (k32 (neg_tag tb)) as [t' |] eqn:Ek; [| discriminate H].
    apply some_inj in H; subst v. destruct (k32_form _ _ Ek) as [F1 _].
    rewrite F1, Eln, (dv_conc wa), (dv_lin tb _ Lb), wbv_w_sub. f_equal. bv_solve.
Qed.

(* [comment removed for export] *)
Theorem fv_sh32_sound : forall M op a b v,
  regs_ok M -> fv_sh32 M op a b = Some v ->
  dv rho v = sext 64 (alu32 op (low32 (dv rho a)) (low32 (dv rho b))).
Proof.
  intros M op [ta wa] [tb [top lo]] v HM H. unfold fv_sh32 in H. cbn [vtag vw] in H.
  assert (Hop : is_shift_op op /\
          (if ((ta =? 0)%uint63 && (vkind tb =? K_SL3)%uint63 && (2 <=? base_align M tb)%uint63 && (base_align M tb <=? 62)%uint63)
           then Some (FV 0 (w_alu32 op wa (W64 0 ((lo land 3) << 3)))) else None) = Some v).
  { destruct op; try discriminate H; (split; [exact I | exact H]). }
  destruct Hop as [Hop H']. clear H.
  match type of H' with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end.
  apply some_inj in H'. subst v.
  apply andb_true_iff in C as [C Hal62]. apply andb_true_iff in C as [C Hal2]. apply andb_true_iff in C as [Eta Ek].
  apply eqb_0_eq in Eta. subst ta. apply Uint63.eqb_spec in Ek.
  apply Uint63.leb_spec in Hal2, Hal62. change (to_Z 2) with 2 in Hal2. change (to_Z 62) with 62 in Hal62.
  rewrite !dv_conc, w_alu32_spec. f_equal.
  apply sh32_amount_ext; [|exact Hop].
  (* [comment removed for export] *)
  unfold dv. cbn [vtag vw]. rewrite Ek. rewrite fk_dvk_SL3, sll3_mod32.
  pose proof (lb_align M tb HM) as Hlb. unfold lb in Hlb. rewrite Ek in Hlb. cbn [Uint63.eqb orb] in Hlb.
  change ((K_SL3 =? 1)%uint63 || (K_SL3 =? 4)%uint63) with false in Hlb. cbv iota in Hlb.
  assert (H4 : bv_unsigned (rho (vbase tb)) mod 4 = 0).
  { set (al := to_Z (base_align M tb)) in *.
    assert (E : 2 ^ al = 4 * 2 ^ (al - 2)).
    { change 4 with (2 ^ 2). rewrite <- (Z.pow_add_r 2 2 (al - 2)) by lia. f_equal. lia. }
    rewrite E in Hlb. pose proof (Z.pow_pos_nonneg 2 (al - 2) ltac:(lia) ltac:(lia)) as Hp.
    clear - Hlb Hp. Z.div_mod_to_equations. nia. }
  rewrite wbv_unsigned, bv_add_unsigned, !wbv_unsigned, !wZ_W64.
  change (to_Z 0 mod 2) with 0. rewrite Z.mul_0_l, Z.add_0_l.
  rewrite lsl_spec, land_spec'. change (to_Z 3) with 3. change 3 with (Z.ones 2) at 1. rewrite Z.land_ones by lia.
  change (2 ^ 2) with 4. change (2 ^ 3) with 8.
  pose proof (i63_range lo) as Hlo. pose proof (i63_range top) as Htop.
  rewrite (Z.mod_small (to_Z lo mod 4 * 8) wB) by (change wB with (2 ^ 63); Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (to_Z lo mod 4 * 8) 32) by (Z.div_mod_to_equations; lia).
  f_equal. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_mod_divide by (exists (2 ^ 62); reflexivity).
  destruct (Z_mod2_cases (to_Z top)) as [-> | ->]; clear - H4; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma fv_jalr_sound : forall v imm p,
  fv_jalr v imm = Some p ->
  bv_and (dv rho v + wbv imm) (bv_not w1) = Z_to_bv 64 (to_Z p) /\ to_Z p < 2 ^ 62.
Proof.
  intros [tg w] imm p H. unfold fv_jalr in H.
  destruct (tg =? 0)%uint63 eqn:Et; [|discriminate]. apply eqb_0_eq in Et. subst tg.
  destruct (w_jalr_target w imm) as [top lo] eqn:Ej.
  destruct (((top land 1) =? 0)%uint63 && (lo <? 4611686018427387904)%uint63) eqn:E; [|discriminate].
  apply some_inj in H. subst p. apply andb_true_iff in E as [Htop Hlo].
  apply Uint63.ltb_spec in Hlo. change (to_Z 4611686018427387904) with (2^62) in Hlo.
  apply Uint63.eqb_spec in Htop.
  assert (Hm : to_Z top mod 2 = 0) by (rewrite <- i63_land1, Htop; reflexivity).
  split; [|exact Hlo].
  rewrite dv_conc, <- wbv_w_jalr_target, Ej. unfold wbv. f_equal. rewrite wZ_W64, Hm. lia.
Qed.

(* [comment removed for export] *)
Definition resv_hit (r : option word) (a : word) : bool :=
  match r with Some x => Z.eqb (bv_unsigned x) (bv_unsigned a) | None => false end.

Lemma resv_eqb_sound : forall r a b,
  resv_eqb r a = Some b -> resv_hit (option_map (dv rho) r) (dv rho a) = b.
Proof.
  intros [[tr wr]|] [ta wa] b H; cbn [resv_eqb vtag vw] in H; cbn [option_map resv_hit].
  - destruct (tr =? ta)%uint63 eqn:E; [|discriminate]. apply Uint63.eqb_spec in E. subst tr.
    destruct (w_eqb wr wa) eqn:Ew.
    + apply some_inj in H. subst b. rewrite (dv_same_word ta wr wa Ew). apply Z.eqb_refl.
    + destruct (is_linear ta) eqn:La; [| discriminate H]. apply some_inj in H. subst b.
      apply Z.eqb_neq. intros E'. apply bv_eq in E'. apply (dv_same_tag_eq ta _ _ La) in E'.
      apply w_eqb_true_bv in E'. rewrite E' in Ew. discriminate Ew.
  - apply some_inj in H. subst b. reflexivity.
Qed.

Lemma resv_after_store_sound : forall r a r',
  resv_after_store r a = Some r' ->
  option_map (dv rho) r' = (if resv_hit (option_map (dv rho) r) (dv rho a) then None else option_map (dv rho) r).
Proof.
  intros r a r' H. unfold resv_after_store in H. destruct r as [rv|].
  - destruct (resv_eqb (Some rv) a) as [[|]|] eqn:E; try discriminate;
      apply some_inj in H; subst r'; rewrite (resv_eqb_sound _ _ _ E); reflexivity.
  - apply some_inj in H. subst r'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma aligned_for_sound : forall M wd a,
  regs_ok M -> aligned_for wd a M = true -> amo_aligned wd (dv rho a) = true.
Proof.
  intros M wd [t [top off]] HM H. unfold aligned_for in H. apply andb_true_iff in H as [Hoff Hal].
  apply Uint63.eqb_spec in Hoff.
  unfold amo_aligned. apply Z.eqb_eq.
  set (k := amo_bytes wd).
  assert (Hk : k = 4 \/ k = 8) by (destruct wd; cbn; auto).
  assert (Hdiv8 : (k | 2 ^ 63)).
  { destruct Hk as [-> | ->]; [exists (2^61) | exists (2^60)]; reflexivity. }
  assert (Hoffk : (k | to_Z off)).
  { apply Z.mod_divide; [lia|]. pose proof (Uint63.to_Z_bounded off).
    destruct wd; cbn [awidth_mask] in Hoff; unfold k; cbn [amo_bytes].
    - change 4 with (2 ^ 2). rewrite <- (i63_land_ones off 3%uint63 2) by (reflexivity || lia). rewrite Hoff. reflexivity.
    - change 8 with (2 ^ 3). rewrite <- (i63_land_ones off 7%uint63 3) by (reflexivity || lia). rewrite Hoff. reflexivity. }
  assert (HwZ : (k | wZ (W64 top off))).
  { rewrite wZ_W64. apply Z.divide_add_r; [apply Z.divide_mul_r; exact Hdiv8 | exact Hoffk]. }
  assert (Hrho : to_Z t < 2 ^ 60 /\ (k | bv_unsigned (rho t))).
  { destruct (t =? 0)%uint63 eqn:Et.
    - apply eqb_0_eq in Et. subst t. split; [cbn; lia |].
      rewrite Hrho0. rewrite Z_to_bv_small by (unfold bv_modulus; cbn; lia). apply Z.divide_0_r.
    - destruct (iget t M) as [rg|] eqn:Ht; [|discriminate]. apply Uint63.leb_spec in Hal.
      destruct (HM t rg Ht) as (Hpl & _ & _ & _ & Hmod & _). split; [exact Hpl |]. change (to_Z 3) with 3 in Hal.
      apply Z.mod_divide in Hmod; [|apply Z.pow_nonzero; [lia | apply Uint63.to_Z_bounded]].
      eapply Z.divide_trans; [|exact Hmod].
      pose proof (Uint63.to_Z_bounded (rg_align rg)) as Hb.
      replace (to_Z (rg_align rg)) with (3 + (to_Z (rg_align rg) - 3)) by lia.
      rewrite Z.pow_add_r by lia. apply Z.divide_mul_l.
      destruct Hk as [-> | ->]; [exists 2 | exists 1]; reflexivity. }
  destruct Hrho as [Hpl Hrho].
  rewrite (fk_dv_plain rho (FV t (W64 top off)) Hpl). cbn [vtag vw].
  rewrite bv_add_unsigned, wbv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64).
  apply Z.mod_divide; [lia|].
  assert (Hk64 : (k | 2 ^ 64)) by (destruct Hk as [-> | ->]; [exists (2^62) | exists (2^61)]; reflexivity).
  rewrite Z.mod_eq by lia. apply Z.divide_sub_r.
  - apply Z.divide_add_r; assumption.
  - apply Z.divide_mul_l. exact Hk64.
Qed.
End ValSound.
