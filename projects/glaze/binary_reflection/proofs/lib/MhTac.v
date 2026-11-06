(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhBits.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)
Section A. Context {fx : FPState}.
  Lemma land_mod32 : forall a b, 0 <= a -> 0 <= b -> (Z.land a b) mod 2 ^ 32 = Z.land (a mod 2 ^ 32) (b mod 2 ^ 32).
  Proof.
    intros a b Ha Hb. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
    destruct (Z.lt_ge_cases k 32) as [Hl|Hh].
    - rewrite !Z.mod_pow2_bits_low by lia. apply Z.land_spec.
    - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
  Qed.
  Lemma mod64_mod32 : forall x, (x mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32.
  Proof.
    intros x. apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
  Qed.
  Lemma w2le4_low : forall (w : word) v, 0 <= v < 2 ^ 32 -> bv_unsigned w mod 2 ^ 32 = v ->
    word_to_le_bytes 4 w = word_to_le_bytes 4 (Z_to_bv 64 v).
  Proof.
    intros w v Hv E. unfold word_to_le_bytes. apply Z_to_le_bytes_mod. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
    rewrite E. rewrite u_Z2bv by lia. symmetry. apply Z.mod_small. lia.
  Qed.
  Definition hi_bits (fr n : Z) : Z := fr - fr mod 2 ^ n.
  Definition lo_bits (fr n : Z) : Z := fr mod 2 ^ n.
  Lemma hi_bits_shift : forall fr n, 0 <= n -> hi_bits fr n = Z.shiftl (Z.shiftr fr n) n.
  Proof.
    intros fr n Hn. unfold hi_bits. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    pose proof (Z.div_mod fr (2 ^ n) ltac:(apply Z.pow_nonzero; lia)). lia.
  Qed.
  Lemma testbit_hi_bits : forall fr n k, 0 <= n -> 0 <= k ->
    Z.testbit (hi_bits fr n) k = (Z.testbit fr k && (n <=? k))%bool.
  Proof.
    intros fr n k Hn Hk. rewrite hi_bits_shift by lia.
    destruct (Z.lt_ge_cases k n) as [Hl|Hh].
    - rewrite Z.shiftl_spec_low by lia. replace (n <=? k) with false by (symmetry; apply Z.leb_gt; lia). rewrite Bool.andb_false_r. reflexivity.
    - rewrite Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. replace (k - n + n) with k by lia.
      replace (n <=? k) with true by (symmetry; apply Z.leb_le; lia). rewrite Bool.andb_true_r. reflexivity.
  Qed.
  Lemma pow2_mono32 : forall n, 0 <= n <= 32 -> 1 <= 2 ^ n <= 2 ^ 32.
  Proof. intros n Hn. split; [pose proof (Z.pow_pos_nonneg 2 n); lia | apply Z.pow_le_mono_r; lia]. Qed.
  Lemma hi_bits_range : forall fr n, 0 <= fr -> 0 <= n -> 0 <= hi_bits fr n <= fr.
  Proof. intros fr n Hf Hn. unfold hi_bits. pose proof (Z.mod_pos_bound fr (2 ^ n) ltac:(apply Z.pow_pos_nonneg; lia)). pose proof (Z.mod_le fr (2^n) ltac:(lia) ltac:(apply Z.pow_pos_nonneg; lia)). lia. Qed.
  Lemma lo_bits_range : forall fr n, 0 <= fr -> 0 <= n -> 0 <= lo_bits fr n <= fr /\ lo_bits fr n < 2 ^ n.
  Proof. intros fr n Hf Hn. unfold lo_bits. pose proof (Z.mod_pos_bound fr (2 ^ n) ltac:(apply Z.pow_pos_nonneg; lia)). pose proof (Z.mod_le fr (2^n) ltac:(lia) ltac:(apply Z.pow_pos_nonneg; lia)). lia. Qed.
  Lemma ones32_mod : forall n, 0 <= n <= 32 -> (2 ^ 32 - 1) mod 2 ^ n = 2 ^ n - 1.
  Proof.
    intros n Hn. pose proof (pow2_mono32 n Hn).
    symmetry. apply Z.mod_unique with (q := 2 ^ (32 - n) - 1); [left; lia|].
    assert (E : 2 ^ 32 = 2 ^ (32 - n) * 2 ^ n) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). rewrite E. lia.
  Qed.
  Lemma negpow_mod : forall n, 0 <= n <= 32 -> (- 2 ^ n) mod 2 ^ 32 = hi_bits (2 ^ 32 - 1) n.
  Proof.
    intros n Hn. unfold hi_bits. rewrite ones32_mod by lia. pose proof (pow2_mono32 n Hn).
    destruct (Z.eq_dec n 32) as [->|Hne].
    - rewrite Z_mod_zero_opp_full; [lia|]. apply Z.mod_same. lia.
    - assert (2 ^ n < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
      symmetry. apply Z.mod_unique with (q := -1); [left; lia | lia].
  Qed.
  Lemma land_hi : forall fr n, 0 <= fr < 2 ^ 32 -> 0 <= n <= 32 -> Z.land fr (hi_bits (2 ^ 32 - 1) n) = hi_bits fr n.
  Proof.
    intros fr n Hf Hn. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, !testbit_hi_bits by lia.
    replace (2 ^ 32 - 1) with (Z.ones 32) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
    destruct (Z.lt_ge_cases k 32) as [Hl|Hh].
    - rewrite Z.ones_spec_low by lia. reflexivity.
    - rewrite (testbit_high 32 fr k) by lia. reflexivity.
  Qed.
  Lemma neg_mod_congr : forall a b n, 0 < n -> a mod n = b mod n -> (- a) mod n = (- b) mod n.
  Proof. intros a b n Hn E. rewrite <- (Z.sub_0_l a), <- (Z.sub_0_l b). rewrite (Zminus_mod 0 a), (Zminus_mod 0 b), E. reflexivity. Qed.

  Lemma act_hi_word : forall fr ai, 0 <= fr < 2 ^ 32 -> 0 <= ai < 32 ->
    word_to_le_bytes 4 (v_and (s32 fr) (v_subw (Z_to_bv 64 0) (s32 (2 * 2 ^ ai))))
    = word_to_le_bytes 4 (Z_to_bv 64 (hi_bits fr (ai + 1))).
  Proof.
    intros fr ai Hf Hai.
    pose proof (hi_bits_range fr (ai + 1) ltac:(lia) ltac:(lia)) as HR.
    apply w2le4_low; [lia|].
    unfold v_and. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite mod64_mod32.
    rewrite land_mod32 by (apply bv_unsigned_in_range || (pose proof (bv_unsigned_in_range _ (s32 fr)); lia) || (pose proof (bv_unsigned_in_range _ (v_subw (Z_to_bv 64 0) (s32 (2 * 2 ^ ai)))); lia)).
    rewrite u_s32, sx32_mod, (Z.mod_small fr) by lia.
    unfold v_subw. fold (s32 (bv_unsigned (Z_to_bv 64 0) - bv_unsigned (s32 (2 * 2 ^ ai)))).
    rewrite u_s32, sx32_mod, u_Z2bv, u_s32 by lia. rewrite Z.sub_0_l.
    rewrite (neg_mod_congr (sx32 (2 * 2 ^ ai)) (2 ^ (ai + 1)) (2 ^ 32) ltac:(lia)).
    2:{ rewrite sx32_mod. rewrite Z.pow_add_r, Z.pow_1_r, Z.mul_comm by lia. reflexivity. }
    rewrite negpow_mod by lia. apply land_hi; lia.
  Qed.

  Lemma act_lo_word : forall fr ai, 0 <= fr < 2 ^ 32 -> 0 <= ai < 32 ->
    word_to_le_bytes 4 (v_and (s32 fr) (v_addi (s32 (2 * 2 ^ ai)) (-1)))
    = word_to_le_bytes 4 (Z_to_bv 64 (lo_bits fr (ai + 1))).
  Proof.
    intros fr ai Hf Hai.
    pose proof (lo_bits_range fr (ai + 1) ltac:(lia) ltac:(lia)) as [HR _].
    pose proof (pow2_mono32 (ai + 1) ltac:(lia)) as HP.
    apply w2le4_low; [lia|].
    unfold v_and. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite mod64_mod32.
    rewrite land_mod32 by (apply bv_unsigned_in_range || (pose proof (bv_unsigned_in_range _ (s32 fr)); lia) || (pose proof (bv_unsigned_in_range _ (v_addi (s32 (2 * 2 ^ ai)) (-1))); lia)).
    rewrite u_s32, sx32_mod, (Z.mod_small fr) by lia.
    unfold v_addi. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite mod64_mod32.
    rewrite u_s32. rewrite Zplus_mod, sx32_mod, <- Zplus_mod.
    rewrite Z.pow_add_r, Z.pow_1_r, (Z.mul_comm (2 ^ ai) 2) in HP by lia.
    rewrite (Z.mod_small (2 * 2 ^ ai + -1)) by lia.
    replace (2 * 2 ^ ai + -1) with (Z.ones (ai + 1)) by (unfold Z.ones; rewrite Z.shiftl_1_l, Z.pow_add_r, Z.pow_1_r by lia; lia).
    rewrite Z.land_ones by lia. unfold lo_bits. rewrite Z.pow_add_r, Z.pow_1_r, Z.mul_comm by lia. reflexivity.
  Qed.
End A.
End MhBits.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac conjs := repeat match goal with |- _ /\ _ => split end.

(* [comment removed for export] *)
Ltac rnfix :=
  repeat match goal with
         | |- context [@CEIL ?i] => is_evar i; lazymatch goal with R : run_ceil |- _ => unify i R end
         | H : context [@CEIL ?i] |- _ => is_evar i; lazymatch goal with R : run_ceil |- _ => unify i R end
         end.
(* [comment removed for export] *)
Ltac lia_hsep := idtac.
Ltac lia_pairs := idtac.
(* [comment removed for export] *)
Ltac hclr :=
  repeat match goal with
         | H : ((_ <= 65536)%Z \/ _) |- _ => clear H
         | H : ((_ < 65536)%Z \/ _) |- _ => clear H
         end.
(* [comment removed for export] *)
Ltac hkeep1 H :=
  repeat match goal with
         | H' : ((_ <= 65536)%Z \/ _) |- _ => tryif constr_eq H H' then fail else clear H'
         | H' : ((_ < 65536)%Z \/ _) |- _ => tryif constr_eq H H' then fail else clear H'
         end.
Ltac hkeep2 H1 H2 :=
  repeat match goal with
         | H' : ((_ <= 65536)%Z \/ _) |- _ =>
             tryif constr_eq H1 H' then fail else tryif constr_eq H2 H' then fail else clear H'
         | H' : ((_ < 65536)%Z \/ _) |- _ =>
             tryif constr_eq H1 H' then fail else tryif constr_eq H2 H' then fail else clear H'
         end.
(* [comment removed for export] *)
Ltac img_key H :=
  lazymatch type of H with
  | context [((_ <= 65536)%Z \/ (684032 <= g_mem _ ?x)%Z)] => x
  | context [((_ <= 65536)%Z \/ (684032 + 24 <= ?x)%Z)] => x
  | context [((_ <= 65536)%Z \/ (684032 <= rg_base ?r)%Z)] => r
  | context [((_ <= 65536)%Z \/ (684032 <= ?b)%Z)] => b
  | context [((_ < 65536)%Z \/ (684032 <= ?b)%Z)] => b
  end.
Ltac goal_mentions x := lazymatch goal with |- context [x] => idtac end.
(* [comment removed for export] *)
Ltac with_img1f tac :=
  match goal with
  | H : context [((_ <= 65536)%Z \/ _)] |- _ => let x := img_key H in goal_mentions x; solve [ hkeep1 H; tac ]
  | H : context [((_ < 65536)%Z \/ _)] |- _ => let x := img_key H in goal_mentions x; solve [ hkeep1 H; tac ]
  end.
(* [comment removed for export] *)
Ltac with_img1 tac :=
  match goal with
  | H : context [((_ <= 65536)%Z \/ _)] |- _ => solve [ hkeep1 H; tac ]
  | H : context [((_ < 65536)%Z \/ _)] |- _ => solve [ hkeep1 H; tac ]
  end.
(* [comment removed for export] *)
Ltac with_img2 tac :=
  match goal with
  | H1 : context [((_ <= 65536)%Z \/ _)], H2 : context [((_ <= 65536)%Z \/ _)] |- _ => solve [ hkeep2 H1 H2; tac ]
  | H1 : context [((_ <= 65536)%Z \/ _)], H2 : context [((_ < 65536)%Z \/ _)] |- _ => solve [ hkeep2 H1 H2; tac ]
  | H1 : context [((_ < 65536)%Z \/ _)], H2 : context [((_ < 65536)%Z \/ _)] |- _ => solve [ hkeep2 H1 H2; tac ]
  end.
Ltac zlia := Zify.zify; xlia zchecker.
Ltac znia := Zify.zify; xnia zchecker.
(* [comment removed for export] *)
Ltac dclr := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dclr_but K :=
  repeat match goal with H : _ \/ _ |- _ => tryif constr_eq K H then fail else clear H end.
Ltac lean tac := first [ solve [dclr; tac] | tac ].
Ltac lean_but K tac := first [ solve [dclr_but K; tac] | tac ].
Ltac with_img1f_ tac :=
  match goal with
  | H : context [((_ <= 65536)%Z \/ _)] |- _ => let x := img_key H in goal_mentions x; solve [ hkeep1 H; lean_but H tac ]
  | H : context [((_ < 65536)%Z \/ _)] |- _ => let x := img_key H in goal_mentions x; solve [ hkeep1 H; lean_but H tac ]
  end.
Ltac with_img1_ tac :=
  match goal with
  | H : context [((_ <= 65536)%Z \/ _)] |- _ => solve [ hkeep1 H; lean_but H tac ]
  | H : context [((_ < 65536)%Z \/ _)] |- _ => solve [ hkeep1 H; lean_but H tac ]
  end.
Ltac hlia := rnfix; lia_hsep; zlia.
Ltac hnia := rnfix; lia_hsep; znia.
(* [comment removed for export] *)
Ltac lia_goal_ok :=
  lazymatch goal with
  | |- @eq ?T _ _ =>
      lazymatch T with
      | Z => idtac | nat => idtac | N => idtac | positive => idtac | bool => idtac | Prop => idtac
      | _ => fail
      end
  | |- _ => idtac
  end.
Ltac lia ::= rnfix; first [ solve [hclr; lean zlia]
                          | lia_goal_ok; lia_hsep; first [ with_img1f_ zlia | with_img1_ zlia | lia_pairs; with_img2 zlia ] ].
Ltac nia ::= rnfix; first [ solve [hclr; lean znia]
                          | lia_goal_ok; lia_hsep; first [ with_img1f_ znia | with_img1_ znia | lia_pairs; with_img2 znia ] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition keeps_but (clob : list reg) (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, ~ In r clob -> getr regs' r = getr regs r.

Lemma keeps_but_refl : forall clob regs, keeps_but clob regs regs.
Proof. intros clob regs r _. reflexivity. Qed.

Lemma keeps_but_trans : forall clob r1 r2 r3,
  keeps_but clob r1 r2 -> keeps_but clob r2 r3 -> keeps_but clob r1 r3.
Proof. intros clob r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma keeps_but_upd : forall clob regs regs' (rd : reg) v,
  keeps_but clob regs regs' -> In rd clob -> keeps_but clob regs (regupd regs' rd v).
Proof.
  intros clob regs regs' rd v K Hin r Hr. rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hr Hin).
Qed.

(* [comment removed for export] *)
Lemma keeps_but_upd_same : forall clob regs regs' (rd : reg) v,
  keeps_but clob regs regs' -> getr regs rd = v -> rd <> 0%bv -> keeps_but clob regs (regupd regs' rd v).
Proof.
  intros clob regs regs' rd v K Hv Hnz r Hr.
  destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply K, Hr.
Qed.

(* [comment removed for export] *)
Lemma in_regs_dec : forall (r : reg) (l : list reg),
  existsb (fun x => bv_eqb x r) l = true -> In r l.
Proof.
  intros r l H. apply existsb_exists in H as (x & Hx & E).
  unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst x. exact Hx.
Qed.
Lemma not_in_regs_dec : forall (r : reg) (l : list reg),
  forallb (fun x => negb (bv_eqb x r)) l = true -> ~ In r l.
Proof.
  intros r l H Hin. pose proof (proj1 (forallb_forall _ _) H r Hin) as H'. cbn beta in H'.
  rewrite bv_eqb_refl in H'. discriminate H'.
Qed.

Lemma keeps_but_mono : forall clob clob' regs regs',
  keeps_but clob regs regs' -> (forall r, In r clob -> In r clob') -> keeps_but clob' regs regs'.
Proof. intros clob clob' regs regs' K Hs r Hr. apply K. intros Hin. exact (Hr (Hs r Hin)). Qed.

Lemma keeps_but_get : forall clob regs regs' (r : reg),
  keeps_but clob regs regs' -> forallb (fun x => negb (bv_eqb x r)) clob = true -> getr regs' r = getr regs r.
Proof. intros clob regs regs' r K H. apply K. apply not_in_regs_dec. exact H. Qed.

Ltac in_clob := apply in_regs_dec; reflexivity.
Ltac solve_keeps_but :=
  repeat (first [ apply keeps_but_upd; [| in_clob]
                | apply keeps_but_upd_same; [| solve [reflexivity | assumption | symmetry; assumption] | intros E; discriminate E] ]);
  first [apply keeps_but_refl | assumption].

(* [comment removed for export] *)
Ltac kept_rw K :=
  repeat match goal with
  | |- context [getr ?R' ?r] =>
      lazymatch type of K with keeps_but _ ?R R' =>
        rewrite (keeps_but_get _ _ _ r K) by reflexivity end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac stepSTx F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPGen1.
Context {fx : FPState}.

Lemma store_ok_defined : forall (M : mem) (lo hi a : Z) (n : nat),
  defined M lo hi -> (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z -> (0 <= lo)%Z -> (hi < 2 ^ 64)%Z ->
  store_ok RSEGS M (Z_to_bv 64 a) n = true.
Proof.
  intros M lo hi a n HD Hlo Hhi H0 H64.
  apply store_ok_of_all; [rewrite u_Z2bv by lia; lia|].
  intros x Hx. rewrite u_Z2bv in Hx by lia.
  unfold wview. pose proof (HD (bv_unsigned x) ltac:(lia)) as Hd.
  replace (Z_to_bv 64 (bv_unsigned x)) with x in Hd by (symmetry; apply bv_eq; rewrite u_Z2bv by (pose proof (u64_range x); lia); reflexivity).
  destruct (M x); [discriminate | exfalso; apply Hd; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma defined_wbytes : forall (M : mem) lo hi (a : word) bs,
  defined M lo hi -> defined (wbytes M a bs) lo hi.
Proof.
  intros M lo hi a bs HD i Hi.
  pose proof (wbytes_grows bs M a) as G. intros E.
  unfold mem_grows in G. specialize (G (Z_to_bv 64 i)).
  apply (G (HD i Hi)). exact E.
Qed.

(* [comment removed for export] *)
Lemma rdn1_of_byte : forall (M : mem) (a : word) b, M a = Some b -> rdn RSEGS M a 1%nat = Some [b].
Proof. intros M a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma byte_at_rdn1 : forall M a b, byte_at M a b -> rdn RSEGS M (Z_to_bv 64 a) 1%nat = Some [Z_to_bv 8 b].
Proof. intros M a b H. apply rdn1_of_byte. exact H. Qed.

(* [comment removed for export] *)
Lemma u8_of_Z : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply (bv_wrap_small 8). change (bv_modulus 8) with 256%Z. lia. Qed.

End FPGen1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma c_eq_s32_0 : forall a, c_eq (s32 a) (Z_to_bv 64 0) = (a mod 2 ^ 32 =? 0)%Z.
Proof.
  intros a. rewrite <- (s32_small 0) by lia. rewrite c_eq_s32. rewrite Z.mod_0_l by lia. reflexivity.
Qed.

Lemma s32_land_pow2_clear : forall mask i,
  (0 <= mask)%Z -> (0 <= i)%Z -> Z.testbit mask i = false -> s32 (Z.land mask (2 ^ i)) = Z_to_bv 64 0.
Proof.
  intros mask i Hm Hi Hb. apply s32_zero_iff.
  rewrite (proj2 (land_pow2_testbit mask i Hm Hi) Hb). reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
