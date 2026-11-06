(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac RefMemcpyLib As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm5ArtLeaf Pm5ArtAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5_code_5a000_5b000 Pm5_code_5f000_60000 Pm5_code_8e000_8f000 Pm5_code_90000_91000 Pm5_code_91000_92000          .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
(* [comment removed for export] *)
Lemma zb8_eq : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.

Lemma at_lit : forall a j, 0 <= a -> 0 <= j -> a + j < 2 ^ 64 -> at_ (Z_to_bv 64 a) j = Z_to_bv 64 (a + j).
Proof.
  intros a j Ha Hj H. unfold at_. rewrite art_u_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cell4_split : forall M a w, 0 <= a -> a + 4 < 2 ^ 64 -> 0 <= w < 2 ^ 32 -> cellA M a 4 w ->
  cellA M a 1 (w mod 256) /\ cellA M (a + 1) 1 (w / 256 mod 256) /\ cellA M (a + 2) 2 (w / 65536).
Proof.
  intros M a w Ha Ha' Hw C. unfold cell in *. unfold word_to_le_bytes in *.
  rewrite (art_u_lit w) in C by lia.
  split; [|split].
  - pose proof (rdn_sub _ M 4 (Z_to_bv 64 a) _ 0 1 C ltac:(lia)) as R. rewrite at_lit in R by lia. change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R.
    rewrite R. cbn [sub firstn skipn Z_to_le_bytes]. rewrite art_u_lit by (pose proof (Z.mod_pos_bound w 256); lia).
    do 2 f_equal. apply zb8_eq. rewrite Z.mod_mod by lia. reflexivity.
  - pose proof (rdn_sub _ M 4 (Z_to_bv 64 a) _ 1 1 C ltac:(lia)) as R. rewrite at_lit in R by lia. change (Z.of_nat 1) with 1 in R.
    rewrite R. cbn [sub firstn skipn Z_to_le_bytes]. rewrite art_u_lit by (pose proof (Z.mod_pos_bound (w / 256) 256); lia).
    do 2 f_equal. apply zb8_eq. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
  - pose proof (rdn_sub _ M 4 (Z_to_bv 64 a) _ 2 2 C ltac:(lia)) as R. rewrite at_lit in R by lia. change (Z.of_nat 2) with 2 in R.
    rewrite R. cbn [sub firstn skipn Z_to_le_bytes]. rewrite art_u_lit by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite !Z.div_div by lia. change (256 * 256) with 65536.
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cell4_join : forall M a x0 x1 x2, 0 <= a -> a + 4 < 2 ^ 64 -> 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 65536 ->
  cellA M a 1 x0 -> cellA M (a + 1) 1 x1 -> cellA M (a + 2) 2 x2 -> cellA M a 4 (x0 + 256 * x1 + 65536 * x2).
Proof.
  intros M a x0 x1 x2 Ha Ha' H0 H1 H2 C0 C1 C2. unfold cell in *. unfold word_to_le_bytes in *.
  rewrite (art_u_lit x0) in C0 by lia. rewrite (art_u_lit x1) in C1 by lia. rewrite (art_u_lit x2) in C2 by lia. rewrite art_u_lit by lia.
  change 4%nat with (1 + (1 + 2))%nat. erewrite rdn_app; [|exact C0|].
  2:{ replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1) : word).
      2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). cbn [Z.of_nat Pos.of_succ_nat].
          rewrite (Z.mod_small a), (Z.mod_small 1) by lia. rewrite Z.mod_small by lia. reflexivity. }
      erewrite rdn_app; [reflexivity|exact C1|].
      replace (Z_to_bv 64 (a + 1) + nat_to_word 1)%bv with (Z_to_bv 64 (a + 2) : word); [exact C2|].
      apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). cbn [Z.of_nat Pos.of_succ_nat].
      rewrite (Z.mod_small (a + 1)), (Z.mod_small 1) by lia. rewrite !Z.mod_small by lia. lia. }
  cbn [Z_to_le_bytes app Nat.add]. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  set (w := x0 + 256 * x1 + 65536 * x2) in *.
  assert (E0 : w mod 256 = x0 mod 256). { subst w. replace (x0 + 256 * x1 + 65536 * x2) with (x0 + (x1 + 256 * x2) * 256) by lia. rewrite Z_mod_plus_full. reflexivity. }
  assert (E1 : w / 256 = x1 + 256 * x2). { subst w. replace (x0 + 256 * x1 + 65536 * x2) with (x0 + (x1 + 256 * x2) * 256) by lia. rewrite Z_div_plus_full by lia. rewrite Z.div_small by lia. lia. }
  assert (E2 : w / 256 / 256 = x2). { rewrite E1. replace (x1 + 256 * x2) with (x1 + x2 * 256) by lia. rewrite Z_div_plus_full by lia. rewrite Z.div_small by lia. lia. }
  do 2 f_equal; [symmetry; apply zb8_eq; exact E0|]. f_equal; [apply zb8_eq; rewrite E1; replace (x1 + 256 * x2) with (x1 + x2 * 256) by lia; rewrite Z_mod_plus_full; reflexivity|].
  rewrite E2. reflexivity.
Qed.

Tactic Notation "recell_hit" integer(k) := do k (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM end; fail "SHOWST".

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_run_free_hooks_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 32 <= sp -> sp < 2 ^ 64 -> 0x6c4000 + 32 <= sp ->
  wrA M (sp - 32) 32 -> cellA M 0x1ff288 8 0 ->
  msteps ASEGS (mkst regs (0x90ff0 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 0)) raw (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Ch.
  zstep F_90fa8 D_90fa8.
  zsd F_90fac D_90fac (sp - 8) (U raw) ltac:(rewok W).
  zsd F_90fb0 D_90fb0 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_90fb4 D_90fb4 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zstep F_90fb8 D_90fb8.
  stepn F_90fbc D_90fbc.
  zstep F_91054 D_91054.
  stepjr F_91058 D_91058 (0x91008 : bv 64)%bv ltac:(gres; bveq).
  zbtk F_90fc0 D_90fc0.
  zstep F_90fdc D_90fdc.
  stepn F_90fe0 D_90fe0.
  stepjr F_9105c D_9105c (0x9102c : bv 64)%bv ltac:(gres; bveq).
  zstep F_90fe4 D_90fe4. zstep F_90fe8 D_90fe8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ch' : cellA X (0x1ff280 + 8) 8 0) by (recell Ch);
    assert (Cra : cellA X (sp - 8) 8 (U raw)) by (do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
    assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
    assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (apply cell_Wn_hit; lia) end.
  zld F_90fec D_90fec (0x1ff280 + 8) Ch'.
  zbtk F_90ff0 D_90ff0.
  zstep F_9103c D_9103c.
  zld F_91040 D_91040 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_91044 D_91044 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_91048 D_91048 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zstep F_9104c D_9104c.
  stepret F_91050 D_91050 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_int_alloc_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 48 <= sp -> sp < 2 ^ 64 -> 0x6c4000 + 48 <= sp ->
  wrA M (sp - 48) 48 -> cellA M 0x1fd248 1 1 ->
  msteps ASEGS (mkst regs (0x8e7dc : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 0x16e9c0)) 18 (getr regs 18)) 19 (getr regs 19)) raw
     (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Ci.
  zstep F_8e794 D_8e794.
  zsd F_8e798 D_8e798 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_8e79c D_8e79c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_8e7a0 D_8e7a0 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_8e7a4 D_8e7a4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_8e7a8 D_8e7a8 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zstep F_8e7ac D_8e7ac. zstep F_8e7b0 D_8e7b0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ci' : cellA X 0x1fd248 1 1) by (recell Ci);
    assert (Cra : cellA X (sp - 8) 8 (U raw)) by (recell_hit 4);
    assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (recell_hit 3);
    assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (recell_hit 2);
    assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by (recell_hit 1);
    assert (Cs3 : cellA X (sp - 40) 8 (U (getr regs 19))) by (recell_hit 0) end.
  zlb F_8e7b4 D_8e7b4 0x1fd248 Ci'.
  stepfence F_8e7b8 D_8e7b8.
  zbtk F_8e7bc D_8e7bc.
  zstep F_8e8b8 D_8e8b8. zstep F_8e8bc D_8e8bc.
  zld F_8e8c0 D_8e8c0 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_8e8c4 D_8e8c4 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_8e8c8 D_8e8c8 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_8e8cc D_8e8cc (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_8e8d0 D_8e8d0 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zstep F_8e8d4 D_8e8d4.
  stepret F_8e8d8 D_8e8d8 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

Lemma art_sllw_0 : forall x m, 0 <= x < 2 ^ 31 -> 0 <= m -> m * 8 < 2 ^ 64 -> m mod 4 = 0 -> v_sllw (Z_to_bv 64 x) (Z_to_bv 64 (m * 2 ^ 3)) = Z_to_bv 64 x.
Proof.
  intros x m Hx Hm Hm' Hm4. unfold v_sllw. rewrite !art_u_lit by lia.
  replace (m * 2 ^ 3 mod 32) with 0.
  2:{ pose proof (Z.div_mod m 4 ltac:(lia)) as E. rewrite Hm4 in E. replace (m * 2 ^ 3) with ((m / 4) * 32) by lia. rewrite Z_mod_mult. reflexivity. }
  rewrite Z.shiftl_0_r. f_equal. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite (Z.mod_small (x + 2 ^ 31)) by lia. lia.
Qed.

(* [comment removed for export] *)
Definition art_cas23w_ok (b1 : Z) : bool :=
  bv_eqb (v_xor (Z_to_bv 64 (2 + 256 * b1)) (v_and (v_xor (Z_to_bv 64 (2 + 256 * b1)) (Z_to_bv 64 3)) (Z_to_bv 64 255))) (Z_to_bv 64 (3 + 256 * b1)).
Lemma art_cas23w_all : forallb art_cas23w_ok (AsanTab.zrange 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma art_cas23w : forall b1, 0 <= b1 < 256 ->
  v_xor (Z_to_bv 64 (2 + 256 * b1)) (v_and (v_xor (Z_to_bv 64 (2 + 256 * b1)) (Z_to_bv 64 3)) (Z_to_bv 64 255)) = Z_to_bv 64 (3 + 256 * b1).
Proof.
  intros b1 Hb. pose proof art_cas23w_all as H. rewrite forallb_forall in H.
  specialize (H b1 ltac:(unfold AsanTab.zrange; apply AsanTab.in_ziota; rewrite Z2Nat.id by lia; lia)). unfold art_cas23w_ok, bv_eqb in H.
  apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma art_land_m4 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551612 = x / 4 * 4.
Proof.
  intros x Hx. change 18446744073709551612 with (Z.shiftl (Z.ones 62) 2).
  change 4 with (2 ^ 2). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 2) as [L|G].
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
    replace (i - 2 + 2) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [L2|G2].
    + replace ((0 <=? i - 2) && (i - 2 <? 62))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      apply Bool.andb_true_r.
    + assert (Tf : Z.testbit x i = false).
      { destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|].
        apply Z.lt_le_trans with (m := 64); [|lia]. apply Z.log2_lt_pow2; lia. }
      rewrite Tf. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_cas23_fn : forall regs (M rom : word -> option byte) (m b1 : Z),
  getr regs 18 = Z_to_bv 64 m -> 16 <= m -> m + 16 < 2 ^ 47 -> m mod 16 = 0 -> 0 <= b1 < 256 ->
  cellA M m 4 (2 + 256 * b1) -> wrA M m 4 ->
  msteps ASEGS (mkst regs (0x5ae6c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 (m * 2 ^ 3))) 11 (Z_to_bv 64 3)) 12 (Z_to_bv 64 (2 + 256 * b1))) 13 (Z_to_bv 64 m)) 14 (Z_to_bv 64 2)) 15 (Z_to_bv 64 255)) 16 (Z_to_bv 64 3)) 17 (Z_to_bv 64 0))
          (0x5aeac : word) (Wn 4 M m (3 + 256 * b1)) rom).
Proof.
  intros regs M rom m b1 H18 Hm Hm' Hm16 Hb1 Chw Whw.
  assert (Hm4 : m mod 4 = 0). { pose proof (Z.div_mod m 16 ltac:(lia)) as E. rewrite Hm16 in E. rewrite E. replace (16 * (m / 16) + 0) with ((4 * (m / 16)) * 4) by lia. apply Z_mod_mult. }
  stepn F_5ae24 D_5ae24. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612. rewrite art_land_m4 by lia.
  replace (m / 4 * 4) with m by (pose proof (Z.div_mod m 4 ltac:(lia)); lia).
  stepn F_5ae28 D_5ae28. rwH. rewrite art_zb_slli by lia.
  zstep F_5ae2c D_5ae2c. zstep F_5ae30 D_5ae30. zstep F_5ae34 D_5ae34.
  stepn F_5ae38 D_5ae38. rwH. rewrite art_sllw_0 by lia.
  stepn F_5ae3c D_5ae3c. rwH. rewrite art_sllw_0 by lia.
  stepn F_5ae40 D_5ae40. rwH. rewrite art_sllw_0 by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Whw' : wok AsanUbsan.M.loaded_segments X m 4) by (rewok Whw) end.
  (* [comment removed for export] *)
  chain_step; [reflexivity
    | eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m) _ (Z_to_bv 64 (2 + 256 * b1)));
      [exact F_5ae44 | reflexivity | exact D_5ae44 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4
      | exact Chw | apply art_bytes4; lia ]
    | ]. wpc. rewrite art_v_lw_small by lia.
  (* [comment removed for export] *)
  chain_step; [reflexivity | eapply art_step_and_r; [exact F_5ae48 | reflexivity | exact D_5ae48 | reflexivity] | ]. wpc.
  gres. rewrite (art_zb_and (2 + 256 * b1) 255) by lia.
  replace (Z.land (2 + 256 * b1) 255) with 2.
  2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. replace (2 + 256 * b1) with (2 + b1 * 256) by lia. rewrite Z_mod_plus_full. reflexivity. }
  chain_step; [reflexivity
    | eapply art_step_branch_ft_r; [exact F_5ae4c | reflexivity | exact D_5ae4c | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
    | ]. wpc.
  (* [comment removed for export] *)
  chain_step; [reflexivity | eapply art_step_xor_r; [exact F_5ae50 | reflexivity | exact D_5ae50 | reflexivity] | ]. wpc.
  chain_step; [reflexivity | eapply art_step_and_r; [exact F_5ae54 | reflexivity | exact D_5ae54 | reflexivity] | ]. wpc.
  chain_step; [reflexivity | eapply art_step_xor_r; [exact F_5ae58 | reflexivity | exact D_5ae58 | reflexivity] | ]. wpc.
  gres.
  rewrite art_cas23w by lia.
  (* [comment removed for export] *)
  chain_step; [reflexivity
    | eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m));
      [exact F_5ae5c | reflexivity | exact D_5ae5c | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4 | gres; rwH; reflexivity
      | exact Whw' ]
    | ]. wpc.
  change (wbytes ?M0 (Z_to_bv 64 m) (word_to_le_bytes 4 (Z_to_bv 64 (3 + 256 * b1)))) with (Wn 4 M0 m (3 + 256 * b1)).
  zbft F_5ae60 D_5ae60.
  zret.
Qed.

Definition art_enq_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (B cnt bsz csz c m size : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (B + 8) (bsz + size)) (B + 16) (cnt + 1)) (B + 24 + 8 * cnt) m) (c + 24) (csz + size)).

(* [comment removed for export] *)
Lemma art_enqueue_fn : forall regs (M rom : word -> option byte) (raw : word) (sp c B L cnt bsz csz m size : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 size ->
  64 <= sp -> sp < 2 ^ 64 -> 0x6c4000 + 64 <= sp -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= B -> B + 8192 < 2 ^ 64 ->
  1 <= L < 2 ^ 63 -> 0 <= cnt < 1021 -> 0 <= bsz -> bsz + size < 2 ^ 64 -> 0 <= csz -> csz + size < 2 ^ 64 -> 0 <= size -> 0 <= m < 2 ^ 64 ->
  apart (sp - 64) 64 c 32 -> apart (sp - 64) 64 B 8192 -> apart c 32 B 8192 ->
  wrA M (sp - 64) 64 -> wrA M (c + 24) 8 -> wrA M B 8192 ->
  cellA M c 8 L -> cellA M (c + 16) 8 B -> cellA M (B + 16) 8 cnt -> cellA M (B + 8) 8 bsz -> cellA M (c + 24) 8 csz ->
  msteps ASEGS (mkst regs (0x5f66c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 11 (Z_to_bv 64 (csz + size))) 12 (Z_to_bv 64 (B + cnt * 2 ^ 3))) 15 (Z_to_bv 64 (cnt + 1))) 16 (Z_to_bv 64 B)) 17 (Z_to_bv 64 1021)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21))
          raw (art_enq_mem M sp raw regs B cnt bsz csz c m size) rom).
Proof.
  intros regs M rom raw sp c B L cnt bsz csz m size H1 Hret H2 H10 H13 H14 Hsp Hsp' IMG Hc Hc' HB HB' HL Hcnt Hbsz Hbsz' Hcsz Hcsz' Hsize Hm A1 A2 A3 W Wc WB CL CB Ccnt Cbsz Ccsz.
  zstep F_5f624 D_5f624.
  zsd F_5f628 D_5f628 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_5f62c D_5f62c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_5f630 D_5f630 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_5f634 D_5f634 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_5f638 D_5f638 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_5f63c D_5f63c (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_5f640 D_5f640 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (CL' : cellA X c 8 L) by (unfold apart in *; recell CL);
    assert (CB' : cellA X (c + 16) 8 B) by (unfold apart in *; recell CB);
    assert (Ccnt' : cellA X (B + 16) 8 cnt) by (unfold apart in *; recell Ccnt);
    assert (Cbsz' : cellA X (B + 8) 8 bsz) by (unfold apart in *; recell Cbsz) end.
  zld F_5f644 D_5f644 c CL'.
  zbft F_5f648 D_5f648.
  zld F_5f64c D_5f64c (c + 16) CB'.
  zld F_5f650 D_5f650 (B + 16) Ccnt'.
  zstep F_5f654 D_5f654.
  zbtk F_5f658 D_5f658.
  zbft F_5f6e0 D_5f6e0.
  zld F_5f6e4 D_5f6e4 (B + 8) Cbsz'.
  zstep F_5f6e8 D_5f6e8. zstep F_5f6ec D_5f6ec. zstep F_5f6f0 D_5f6f0. zstep F_5f6f4 D_5f6f4.
  zsd F_5f6f8 D_5f6f8 (B + 8) (bsz + size) ltac:(unfold apart in *; rewok WB).
  zsd F_5f6fc D_5f6fc (B + 16) (cnt + 1) ltac:(unfold apart in *; rewok WB).
  zsd F_5f700 D_5f700 (B + 24 + 8 * cnt) m ltac:(unfold apart in *; rewok WB).
  stepn F_5f704 D_5f704.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ccsz' : cellA X (c + 24) 8 csz) by (unfold apart in *; recell Ccsz) end.
  zld F_5f714 D_5f714 (c + 24) Ccsz'.
  zstep F_5f718 D_5f718.
  zsd F_5f71c D_5f71c (c + 24) (csz + size) ltac:(unfold apart in *; rewok Wc).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cra : cellA X (sp - 8) 8 (U raw)) by (unfold apart in *; zcell);
    assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (unfold apart in *; zcell);
    assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (unfold apart in *; zcell);
    assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by (unfold apart in *; zcell);
    assert (Cs3 : cellA X (sp - 40) 8 (U (getr regs 19))) by (unfold apart in *; zcell);
    assert (Cs4 : cellA X (sp - 48) 8 (U (getr regs 20))) by (unfold apart in *; zcell);
    assert (Cs5 : cellA X (sp - 56) 8 (U (getr regs 21))) by (unfold apart in *; zcell) end.
  zld F_5f720 D_5f720 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_5f724 D_5f724 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_5f728 D_5f728 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_5f72c D_5f72c (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_5f730 D_5f730 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_5f734 D_5f734 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_5f738 D_5f738 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_5f73c D_5f73c.
  stepret F_5f740 D_5f740 raw ltac:(rwH; reflexivity).
  unfold art_enq_mem. zret.
Qed.
End FPX.
