(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

(* [comment removed for export] *)
Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zb8_length_nat, ?zw32_length_nat, ?zh16_length_nat in *.

Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap32_mod32 : forall z, (bv_swrap 32 z mod 2^32 = z mod 2^32)%Z.
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
  replace (z + 2^31 - 2^31)%Z with z by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sx32_mod32 : forall bb, (0 <= bb < 2^32)%Z -> (bv_unsigned (sx32 (Z_to_bv 64 bb)) mod 4294967296 = bb)%Z.
Proof.
  intros bb Hbb. unfold sx32. rewrite (unsigned_lit bb) by lia. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^32 * 2^32)%Z.
  rewrite Zaux.Zmod_mod_mult by lia. change 4294967296%Z with (2^32)%Z. rewrite swrap32_mod32. apply Z.mod_small. lia.
Qed.

Lemma lor_mod_pow2 : forall a b n, (0 <= n)%Z -> (Z.lor a b mod 2^n = Z.lor (a mod 2^n) (b mod 2^n))%Z.
Proof. intros a b n Hn. rewrite <- !Z.land_ones by lia. rewrite Z.land_lor_distr_l. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pullw_mod32 : forall bb (b8 : byte), (0 <= bb < 2^32)%Z ->
  ((Z.lor ((bv_unsigned (sx32 (Z_to_bv 64 bb)) * 256) mod 18446744073709551616) (bv_unsigned b8)) mod 4294967296
   = u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8)))%Z.
Proof.
  intros bb b8 Hbb. pose proof (byte_range b8) as Hb. unfold u32.
  change 4294967296%Z with (2^32)%Z. change 18446744073709551616%Z with (2^32 * 2^32)%Z.
  rewrite !lor_mod_pow2 by lia. f_equal.
  rewrite Zaux.Zmod_mod_mult by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^8)%Z with 256%Z.
  rewrite <- (sx32_mod32 bb Hbb) at 2. change 4294967296%Z with (2^32)%Z.
  rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.

Lemma pullw_reg32 : forall bb (b8 : byte), (0 <= bb < 2^32)%Z ->
  (bv_unsigned (Z_to_bv 64 (Z.lor ((bv_unsigned (sx32 (Z_to_bv 64 bb)) * 256) mod 18446744073709551616) (bv_unsigned b8))) mod 4294967296
   = u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8)))%Z.
Proof.
  intros bb b8 Hbb. pose proof (byte_range b8) as Hb.
  rewrite unsigned_lit; [apply pullw_mod32; exact Hbb|].
  pose proof (Z.mod_pos_bound (bv_unsigned (sx32 (Z_to_bv 64 bb)) * 256) 18446744073709551616 ltac:(lia)) as R.
  split; [apply Z.lor_nonneg; lia|].
  apply (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.lor_lt_pow2 _ _ 64); lia.
Qed.

Lemma u32_range : forall x, (0 <= u32 x < 2^32)%Z.
Proof. intros x. unfold u32. apply Z.mod_pos_bound. lia. Qed.
Lemma u32_range' : forall x, (0 <= u32 x < 4294967296)%Z.
Proof. intros x. unfold u32. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_mod32 : forall a m, (0 <= m < 2^32)%Z -> Z.land (a mod 2^32) m = Z.land a m.
Proof.
  intros a m Hm. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z_lt_le_dec i 32).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit m i) with false; [rewrite !Bool.andb_false_r; reflexivity|].
    symmetry. destruct (Z.eq_dec m 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
    apply (Z.lt_le_trans _ 32); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma land_swrap32 : forall x m, (0 <= m < 2^32)%Z -> Z.land (bv_swrap 32 x) m = Z.land x m.
Proof.
  intros x m Hm. rewrite <- (land_mod32 (bv_swrap 32 x)), <- (land_mod32 x) by lia.
  rewrite swrap32_mod32. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma gbval_of_srlw : forall (wb : word) bb bl n sh, (bv_unsigned wb mod 4294967296 = bb)%Z ->
  (n <= bl <= 32)%Z -> (1 <= n)%Z -> (n <= 31)%Z -> sh = (bl - n)%Z ->
  Z.land (bv_swrap 32 (Z.shiftr (bv_unsigned wb mod 4294967296) (sh mod 32))) (2^n - 1) = gbval bb bl n.
Proof.
  intros wb bb bl n sh WB Hbl Hn1 Hn2 ->. unfold gbval.
  assert (Hm : (0 <= 2^n - 1 < 2^32)%Z).
  { split; [pose proof (Z.pow_pos_nonneg 2 n); lia|]. apply (Z.le_lt_trans _ (2^31 - 1)); [|lia].
    apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
  rewrite land_swrap32 by exact Hm. rewrite WB. rewrite Z.mod_small by lia.
  rewrite Z.shiftl_1_l. reflexivity.
Qed.
Lemma land_ones64_mask : forall n, (0 <= n <= 64)%Z -> Z.land 18446744073709551615 (2^n - 1) = (2^n - 1)%Z.
Proof.
  intros n Hn. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  apply Z.mod_small. split; [pose proof (Z.pow_pos_nonneg 2 n); lia|].
  pose proof (Z.pow_le_mono_r 2 n 64). lia.
Qed.
(* [comment removed for export] *)
Lemma gbval_of_srlw64 : forall (wb : word) bb bl n sh, (bv_unsigned wb mod 4294967296 = bb)%Z ->
  (n <= bl <= 32)%Z -> (1 <= n)%Z -> (n <= 31)%Z -> sh = (bl - n)%Z ->
  Z.land (Z.land (bv_swrap 32 (Z.shiftr (bv_unsigned wb mod 4294967296) (sh mod 32))) 18446744073709551615) (2^n - 1)
  = gbval bb bl n.
Proof.
  intros wb bb bl n sh WB Hbl Hn1 Hn2 Hsh. rewrite <- Z.land_assoc. rewrite land_ones64_mask by lia.
  apply (gbval_of_srlw _ _ _ _ _ WB); assumption.
Qed.
(* [comment removed for export] *)
Lemma gbval_of_slli_srli : forall (wb : word) bb bl n sh, (bv_unsigned wb mod 4294967296 = bb)%Z ->
  (n <= bl <= 32)%Z -> (1 <= n)%Z -> (n <= 31)%Z -> sh = (bl - n)%Z ->
  (Z.land (Z.land (bv_swrap 32 (Z.shiftr (bv_unsigned wb mod 4294967296) (sh mod 32))) 18446744073709551615 * 2^(64 - n))
          18446744073709551615 / 2^(64 - n) = gbval bb bl n)%Z.
Proof.
  intros wb bb bl n sh WB Hbl Hn1 Hn2 Hsh.
  rewrite <- (gbval_of_srlw64 wb bb bl n sh WB Hbl Hn1 Hn2 Hsh).
  set (y := bv_swrap 32 _). clearbody y.
  change 18446744073709551615%Z with (Z.ones 64). rewrite !Z.land_ones by lia.
  set (u := (y mod 2^64)%Z). assert (Hu : (0 <= u < 2^64)%Z) by (subst u; apply Z.mod_pos_bound; lia). clearbody u.
  rewrite zb_land_mask by lia.
  replace (2^64)%Z with (2^n * 2^(64-n))%Z at 1 by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r by (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity.
Qed.
Lemma gbval_range : forall bb bl n, (0 <= n)%Z -> (0 <= gbval bb bl n < 2^n)%Z.
Proof. intros bb bl n Hn. unfold gbval. rewrite Z.shiftl_1_l. rewrite zb_land_mask by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.
End ACeilS1.

(* [comment removed for export] *)
Ltac ulia := unset_Z; lia.

(* [comment removed for export] *)
Ltac dpureF_solve DP :=
  eapply (dpureF_frame _ _ _ _ _ _ _ _ _ DP); dmodel_cbn;
  [ (* [comment removed for export] *) first [ exact (dpureF_jwf _ _ _ _ _ _ DP)
                      | pose proof (dpureF_jwf _ _ _ _ _ _ DP) as X__; unfold jk_wf in *;
                        cbn [jk_set_t jk_set_s j_p1 j_p2 j_p3 j_s1 j_s2 j_q1 j_q2] in *; decompose [and] X__; clear X__;
                        repeat split; try assumption;
                        cbn [cells_bytes cbytes app]; rewrite ?length_app, ?length_le4, ?length_le8; first [reflexivity | ulia] ]
  | (* [comment removed for export] *) first [ exact (dpureF_static _ _ _ _ _ _ DP)
                          | pose proof (dpureF_static _ _ _ _ _ _ DP) as X__; unfold jk_static in *;
                            cbn [jk_set_t jk_set_s j_q1 j_q2 j_tol j_toh j_bzalloc j_bzfree j_opaque] in *; exact X__ ]
  | first [reflexivity | ulia] | first [reflexivity | ulia] | first [reflexivity | ulia]
  | first [reflexivity | ulia]
  | (* [comment removed for export] *) first [ exact (dpureF_in _ _ _ _ _ _ DP) | assumption | eapply (in_rel_tail _ _ _ _ _ (dpureF_in _ _ _ _ _ _ DP)); reflexivity | idtac ]
  | (* [comment removed for export] *) first [ cbn [length s_in]; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | apply u32_range | apply u32_range' | let X := fresh "X_" in pose proof (dpureF_bb _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | let X := fresh "X_" in pose proof (dpureF_bl _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | let X := fresh "X_" in pose proof (dpureF_cbn _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *)
    first [ let X := fresh "CR_" in pose proof (dpureF_cbn _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; cbn [length s_in] in *; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | exact (dpureF_snb _ _ _ _ _ _ DP) | let X := fresh "X_" in pose proof (dpureF_snb _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | exact (dpureF_nbu _ _ _ _ _ _ DP) | let X := fresh "X_" in pose proof (dpureF_nbu _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *)
    first [ let X := fresh "RP_" in pose proof (dpureF_rep _ _ _ _ _ _ DP) as X;
            unfold drep in X |- *; dmodel_cbn_in X; dmodel_cbn;
            first [ exact X
                  | (* [comment removed for export] *)
                    decompose [and] X; repeat match goal with |- _ /\ _ => split end; try assumption;
                    first [ apply u32_range | apply u32_range' | ulia ] ]
          | idtac ] ].

(* [comment removed for export] *)
Ltac unify_memF :=
  lazymatch goal with |- ?a = ?b =>
    lazymatch a with MS _ _ _ _ _ ?m1 _ =>
    lazymatch b with MS _ _ _ _ _ ?m2 _ => unify m2 m1 end end end.

(* [comment removed for export] *)
Ltac fuelF :=
  lazymatch goal with |- fuel_ok ?F ?d' ?s' =>
    match goal with H : fuel_ok F ?d ?s |- _ =>
      first [ constr_eq d d'; constr_eq s s'; exact H
            | apply (fuel_ok_eq F d d' s s' H);
              [ cbn [s_in s_out s_avail_out s_tin s_tout s_set_in s_set_tin length]; dmodel_cbn; reflexivity
              | dmodel_cbn; reflexivity ] ]
    end
  end.

(* [comment removed for export] *)
Ltac cut_sideF DP :=
  lazymatch goal with
  | |- dmem _ _ _ _ _ _ _ => close_dmemF
  | |- fuel_ok _ _ _ => fuelF
  | |- rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _ =>
      match goal with H : rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- munch _ (a_m0 _) _ => match goal with H : munch _ (a_m0 _) _ |- _ => exact H end
  | |- wmono _ (a_m0 _) _ => match goal with H : wmono _ (a_m0 _) _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  | |- dpureF _ _ _ _ _ _ => solve [ dpureF_solve DP ]
  end.

Tactic Notation "enter_cutF" uconstr(NEXT) constr(DP) :=
  eapply evt_eq; [ | eapply NEXT ]; only 1: unify_memF; try cut_sideF DP; only 1: (dvF_cbn; dmodel_cbn; st_eq).

(* [comment removed for export] *)
Ltac gbword n w bbmodel :=
  let v := reg_val n in
  let Hw := fresh "W" w in
  assert (Hw : (bv_unsigned v mod 4294967296 = bbmodel)%Z);
  [ | let E := fresh "E" w in remember v as w eqn:E in Hw |- *; clear E ].
