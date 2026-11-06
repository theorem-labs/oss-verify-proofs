(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import MallocShape.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib GrayLib LeptStructs LeptExec DitherLib DitherLib2 DitherTac DitherTac2.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

Definition tv_ok (t : Z) : Prop := 0 <= t < 2 ^ 30 \/ 2 ^ 64 - 2 ^ 31 <= t < 2 ^ 64.

Lemma tv_ok_0 : tv_ok 0.
Proof. left. lia. Qed.
Lemma tv_range : forall t, tv_ok t -> 0 <= t < 2 ^ 64.
Proof. intros t [H|H]; lia. Qed.

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma rdv_u8 : forall (m : word -> option byte) (a : word) bs, rdn segs m a 1 = Some bs -> 0 <= rdv false 1 bs <= 255.
Proof.
  intros m a bs R. pose proof (rdn_length _ _ _ _ _ R) as L. pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in B. unfold rdv, extz. rewrite u_Z2bv by lia. lia.
Qed.

(* [comment removed for export] *)
Definition tab_rd (sx : bool) (P : Z -> Prop) (cells : list (Z * Z)) (m : word -> option byte) (tab : Z) : Prop :=
  forall (m' : word -> option byte) (k : Z), mframe cells m m' -> 0 <= k <= 255 ->
    exists bs, rdn segs m' (Z_to_bv 64 (tab + 4 * k)) 4 = Some bs /\ P (rdv sx 4 bs).
End WithSegs.

(* [comment removed for export] *)
Lemma dl_addw_tv : forall d t, 0 <= d <= 255 -> tv_ok t ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 d)) (low32 (Z_to_bv 64 t))) = Z_to_bv 64 (d + t).
Proof.
  intros d t Hd [Ht|Ht]; [apply dl_addw; lia|].
  rewrite w_addw. unfold v_addw. rewrite (u_Z2bv d), (u_Z2bv t) by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
  set (x := 2 ^ 64 - t). assert (Hx : 1 <= x <= 2 ^ 31) by (unfold x; lia).
  replace (d + t + 2 ^ 31) with (d - x + 2 ^ 31 + 4294967296 * 2 ^ 32) by (unfold x; change (2 ^ 64) with (4294967296 * 2 ^ 32); lia).
  rewrite Z_mod_plus_full. rewrite (Z.mod_small (d - x + 2 ^ 31)) by lia.
  replace (d - x + 2 ^ 31 - 2 ^ 31) with (d - x) by lia.
  replace (d + t) with (d - x + 1 * 2 ^ 64) by (unfold x; lia). rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tv_nn30 : forall t, tv_ok t -> branch_taken BC_LT (Z_to_bv 64 t) (Z_to_bv 64 0) = false -> 0 <= t < 2 ^ 30.
Proof.
  intros t [Ht|Ht] B; [exact Ht|]. exfalso. cbn [branch_taken] in B. unfold bv_lts in B.
  rewrite (bv_signed_Zs 0) in B by lia. rewrite Z_to_bv_signed in B.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in B. change (2 ^ Z.of_N 64) with (2 ^ 64) in B. change (2 ^ 64 / 2) with (2 ^ 63) in B.
  replace (t + 2 ^ 63) with (t - 2 ^ 63 + 1 * 2 ^ 64) in B by lia. rewrite Z_mod_plus_full in B. rewrite Z.mod_small in B by lia.
  apply Z.ltb_ge in B. lia.
Qed.

(* [comment removed for export] *)
Definition dapart (a na b nb : Z) : Prop := a + na <= b \/ b + nb <= a.
Ltac dl_arith_ap :=
  match goal with H : dapart ?a _ ?b _ |- _ =>
    match goal with |- context [a] => match goal with |- context [b] =>
      let D := fresh "D" in pose proof H as D; unfold dapart in D; dl_arith end end end.

Ltac dl_side regs ::=
  lazymatch goal with
  | |- store_ok _ _ _ _ = true =>
      dl_an; dl_sub_norm;
      first [ match goal with H : store_ok _ _ (Z_to_bv 64 ?z) ?n = true |- store_ok _ _ (Z_to_bv 64 ?z) ?n = true => exact H end
            | match goal with H : store_ok _ _ (Z_to_bv 64 ?z') ?n = true |- store_ok _ _ (Z_to_bv 64 ?z) ?n = true =>
                replace z with z' by dl_zeq; exact H end ]
  | |- exists bs, rdn _ _ _ _ = Some bs /\ _ =>
      eapply dl_read; [ dl_an; dl_sub_norm; reflexivity | | reflexivity ];
      first [ match goal with H : rdn _ _ (Z_to_bv 64 ?z) ?n = Some ?b |- rdn _ _ (Z_to_bv 64 ?z) ?n = Some ?b => exact H end
            | match goal with H : rdn _ _ (Z_to_bv 64 ?z') ?n = Some ?b |- rdn _ _ (Z_to_bv 64 ?z) ?n = Some ?b =>
                replace z with z' by dl_zeq; exact H end ]
  | |- branch_taken _ _ _ = _ => first [ assumption | ex_br | dl_guard ]
  | |- _ => first [ dl_arith | dl_arith_ap | idtac ]
  end.

(* [comment removed for export] *)
Lemma dl_ext4 : forall x, 0 <= x < 2 ^ 31 -> ext_val true 0 4 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. apply ext_val_sx_id; [lia | rewrite u_Z2bv by lia; cbn; lia]. Qed.
Ltac dl_an_pass ::=
  rewrite ?dl_addi0; rewrite ?dl_add; rewrite ?dl_ext4 by lia; rewrite ?dl_addw by lia; rewrite ?dl_zext32 by lia;
  rewrite ?dl_sllw by dl_nia; rewrite ?dl_mulw by dl_nia; rewrite ?dl_add;
  rewrite ?dl_max0 by lia; rewrite ?dl_max0w by lia; rewrite ?dl_sltu0 by lia; rewrite ?dl_slt_true by lia; rewrite ?dl_slt_false by lia; rewrite ?dl_xor11; rewrite ?dl_xor01;
  rewrite ?dl_xor3 by lia; rewrite ?dl_bitword by lia; rewrite ?dl_dibitword by lia; rewrite ?dl_bitword_w by lia; rewrite ?dl_dibitword_w by lia; rewrite ?dl_mulc by dl_nia; rewrite ?dl_add; rewrite ?zbv_addi;
  rewrite ?dl_and3 by dl_al_side.

(* [comment removed for export] *)
Lemma dl_not : forall b, 0 <= b < 2 ^ 64 -> alu64 ALU_XOR (Z_to_bv 64 b) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - b).
Proof.
  intros b Hb. rewrite alu_xor. unfold v_xor. rewrite (u_Z2bv b) by lia. change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64). f_equal.
  assert (E : Z.lxor b (Z.ones 64) = Z.ldiff (Z.ones 64) b).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec. destruct (Z_lt_ge_dec n 64) as [L|GE].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit b n); reflexivity.
    - rewrite Z.ones_spec_high by lia. destruct (Z.eq_dec b 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
      assert (LG : Z.log2 b < 64) by (apply Z.log2_lt_pow2; lia).
      rewrite (Z.bits_above_log2 b n) by lia. reflexivity. }
  rewrite E. rewrite <- Z.sub_nocarry_ldiff.
  - change (Z.ones 64) with (2 ^ 64 - 1). reflexivity.
  - destruct (Z.eq_dec b 0) as [->|NZ]; [reflexivity|]. apply Z.ldiff_ones_r_low; [lia | apply Z.log2_lt_pow2; lia].
Qed.

Ltac dl_u8 := first [ lia | (eapply rdv_u8; eassumption) ].
(* [comment removed for export] *)
Ltac dl_dclass :=
  first [ assumption
        | (eapply rdv_u8; eassumption)
        | (eapply tv_nn30; [eassumption | eassumption])
        | lia ].

Ltac dl_guard ::=
  dl_an; rewrite ?dl_srlw_zero by lia; rewrite ?dl_or_and3 by dl_al_side; rewrite ?dl_not by lia;
  rewrite ?dl_addw_tv by first [ lia | assumption ];
  rewrite ?dl_seqz by dl_lia; rewrite ?dl_sltu0 by dl_lia; rewrite ?dl_sltu_false by dl_lia; rewrite ?dl_slt_false by dl_lia;
  rewrite ?dl_xor00; rewrite ?dl_xor10; rewrite ?dl_xor11; rewrite ?dl_xor01;
  rewrite ?dl_and3 by first [ dl_lia | (apply dl_al4; assumption) | assumption ];
  first [ (* [comment removed for export] *)
          (match goal with |- branch_taken BC_NE (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) = false =>
             replace a with b by lia; cbn [branch_taken]; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity end)
        | (cbn [branch_taken]; unfold bv_eqb, bv_ltu, bv_lts;
           rewrite ?bv_signed_Zs by dl_lia; rewrite ?u_Z2bv by dl_lia;
           first [ apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge
                 | (apply negb_true_iff; first [apply Z.eqb_neq | apply Z.ltb_ge])
                 | (apply negb_false_iff; first [apply Z.eqb_eq | apply Z.ltb_lt]) ];
           dl_lia) ].
