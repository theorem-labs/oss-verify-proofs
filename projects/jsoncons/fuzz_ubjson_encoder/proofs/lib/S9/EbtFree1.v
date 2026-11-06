(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac RefMemcpyLib As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac EbtLeaf EbtAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r6b6d0_6b828 Eb0_code_r6de28_6df9c Eb0_code_r3cf10_3de98 Eb0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma zb8_eq : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.

Lemma at_lit : forall a j, 0 <= a -> 0 <= j -> a + j < 2 ^ 64 -> at_ (Z_to_bv 64 a) j = Z_to_bv 64 (a + j).
Proof.
  intros a j Ha Hj H. unfold at_. rewrite art_u_lit by lia. reflexivity.
Qed.

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

#[using="Type"] Lemma art_run_free_hooks_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 32 <= sp -> sp < 2 ^ 64 -> 0x69c000 + 32 <= sp ->
  wrA M (sp - 32) 32 -> cellA M 0x1d7bc8 8 0 ->
  msteps ASEGS (mkst regs (0x89320 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 0)) raw (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Ch.
  zstep F_892d0 D_892d0.
  zsd F_892d4 D_892d4 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_892d8 D_892d8 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_892dc D_892dc (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zstep F_892e0 D_892e0.
  stepn F_892e4 D_892e4.
  zstep F_8937c D_8937c.
  stepjr F_89380 D_89380 (0x89338 : bv 64)%bv ltac:(gres; bveq).
  zbtk F_892e8 D_892e8.
  zstep F_89304 D_89304.
  stepn F_89308 D_89308.
  stepjr F_89384 D_89384 (0x8935c : bv 64)%bv ltac:(gres; bveq).
  zstep F_8930c D_8930c. zstep F_89310 D_89310.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ch' : cellA X (0x1d7bc0 + 8) 8 0) by (recell Ch);
    assert (Cra : cellA X (sp - 8) 8 (U raw)) by (do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
    assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
    assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (apply cell_Wn_hit; lia) end.
  zld F_89314 D_89314 (0x1d7bc0 + 8) Ch'.
  zbtk F_89318 D_89318.
  zstep F_89364 D_89364.
  zld F_89368 D_89368 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_8936c D_8936c (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_89370 D_89370 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zstep F_89374 D_89374.
  stepret F_89378 D_89378 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_int_alloc_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 48 <= sp -> sp < 2 ^ 64 -> 0x69c000 + 48 <= sp ->
  wrA M (sp - 48) 48 -> cellA M 0x1d5b88 1 1 ->
  msteps ASEGS (mkst regs (0x86b0c : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 0x147300)) 18 (getr regs 18)) 19 (getr regs 19)) raw
     (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Ci.
  zstep F_86abc D_86abc.
  zsd F_86ac0 D_86ac0 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_86ac4 D_86ac4 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_86ac8 D_86ac8 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_86acc D_86acc (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_86ad0 D_86ad0 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zstep F_86ad4 D_86ad4. zstep F_86ad8 D_86ad8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ci' : cellA X 0x1d5b88 1 1) by (recell Ci);
    assert (Cra : cellA X (sp - 8) 8 (U raw)) by (recell_hit 4);
    assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (recell_hit 3);
    assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (recell_hit 2);
    assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by (recell_hit 1);
    assert (Cs3 : cellA X (sp - 40) 8 (U (getr regs 19))) by (recell_hit 0) end.
  zlb F_86adc D_86adc 0x1d5b88 Ci'.
  stepfence F_86ae0 D_86ae0.
  zbtk F_86ae4 D_86ae4.
  zstep F_86be0 D_86be0. zstep F_86be4 D_86be4.
  zld F_86be8 D_86be8 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_86bec D_86bec (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_86bf0 D_86bf0 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_86bf4 D_86bf4 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_86bf8 D_86bf8 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zstep F_86bfc D_86bfc.
  stepret F_86c00 D_86c00 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

#[using="Type"] Lemma art_sllw_0 : forall x m, 0 <= x < 2 ^ 31 -> 0 <= m -> m * 8 < 2 ^ 64 -> m mod 4 = 0 -> v_sllw (Z_to_bv 64 x) (Z_to_bv 64 (m * 2 ^ 3)) = Z_to_bv 64 x.
Proof.
  intros x m Hx Hm Hm' Hm4. unfold v_sllw. rewrite !art_u_lit by lia.
  replace (m * 2 ^ 3 mod 32) with 0.
  2:{ pose proof (Z.div_mod m 4 ltac:(lia)) as E. rewrite Hm4 in E. replace (m * 2 ^ 3) with ((m / 4) * 32) by lia. rewrite Z_mod_mult. reflexivity. }
  rewrite Z.shiftl_0_r. f_equal. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite (Z.mod_small (x + 2 ^ 31)) by lia. lia.
Qed.

Definition art_cas23w_ok (b1 : Z) : bool :=
  bv_eqb (v_xor (Z_to_bv 64 (2 + 256 * b1)) (v_and (v_xor (Z_to_bv 64 (2 + 256 * b1)) (Z_to_bv 64 3)) (Z_to_bv 64 255))) (Z_to_bv 64 (3 + 256 * b1)).
#[using="Type"] Lemma art_cas23w_all : forallb art_cas23w_ok (AsanTab.zrange 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma art_cas23w : forall b1, 0 <= b1 < 256 ->
  v_xor (Z_to_bv 64 (2 + 256 * b1)) (v_and (v_xor (Z_to_bv 64 (2 + 256 * b1)) (Z_to_bv 64 3)) (Z_to_bv 64 255)) = Z_to_bv 64 (3 + 256 * b1).
Proof.
  intros b1 Hb. pose proof art_cas23w_all as H. rewrite forallb_forall in H.
  specialize (H b1 ltac:(unfold AsanTab.zrange; apply AsanTab.in_ziota; rewrite Z2Nat.id by lia; lia)). unfold art_cas23w_ok, bv_eqb in H.
  apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

#[using="Type"] Lemma art_land_m4 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551612 = x / 4 * 4.
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

#[using="Type"] Lemma art_cas23_fn : forall regs (M rom : word -> option byte) (m b1 : Z),
  getr regs 18 = Z_to_bv 64 m -> 16 <= m -> m + 16 < 2 ^ 47 -> m mod 16 = 0 -> 0 <= b1 < 256 ->
  cellA M m 4 (2 + 256 * b1) -> wrA M m 4 ->
  msteps ASEGS (mkst regs (0x53368 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 (m * 2 ^ 3))) 11 (Z_to_bv 64 3)) 12 (Z_to_bv 64 (2 + 256 * b1))) 13 (Z_to_bv 64 m)) 14 (Z_to_bv 64 2)) 15 (Z_to_bv 64 255)) 16 (Z_to_bv 64 3)) 17 (Z_to_bv 64 0))
          (0x533a8 : word) (Wn 4 M m (3 + 256 * b1)) rom).
Proof.
  intros regs M rom m b1 H18 Hm Hm' Hm16 Hb1 Chw Whw.
  assert (Hm4 : m mod 4 = 0). { pose proof (Z.div_mod m 16 ltac:(lia)) as E. rewrite Hm16 in E. rewrite E. replace (16 * (m / 16) + 0) with ((4 * (m / 16)) * 4) by lia. apply Z_mod_mult. }
  stepn F_53318 D_53318. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612. rewrite art_land_m4 by lia.
  replace (m / 4 * 4) with m by (pose proof (Z.div_mod m 4 ltac:(lia)); lia).
  stepn F_5331c D_5331c. rwH. rewrite art_zb_slli by lia.
  zstep F_53320 D_53320. zstep F_53324 D_53324. zstep F_53328 D_53328.
  stepn F_5332c D_5332c. rwH. rewrite art_sllw_0 by lia.
  stepn F_53330 D_53330. rwH. rewrite art_sllw_0 by lia.
  stepn F_53334 D_53334. rwH. rewrite art_sllw_0 by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Whw' : wok AsanUbsan.M.loaded_segments X m 4) by (rewok Whw) end.

  chain_step; [reflexivity
    | eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m) _ (Z_to_bv 64 (2 + 256 * b1)));
      [exact F_53338 | reflexivity | exact D_53338 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4
      | exact Chw | apply art_bytes4; lia ]
    | ]. wpc. rewrite art_v_lw_small by lia.

  chain_step; [reflexivity | eapply art_step_and_r; [exact F_5333c | reflexivity | exact D_5333c | reflexivity] | ]. wpc.
  gres. rewrite (art_zb_and (2 + 256 * b1) 255) by lia.
  replace (Z.land (2 + 256 * b1) 255) with 2.
  2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. replace (2 + 256 * b1) with (2 + b1 * 256) by lia. rewrite Z_mod_plus_full. reflexivity. }
  chain_step; [reflexivity
    | eapply art_step_branch_ft_r; [exact F_53340 | reflexivity | exact D_53340 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
    | ]. wpc.

  chain_step; [reflexivity | eapply art_step_xor_r; [exact F_53344 | reflexivity | exact D_53344 | reflexivity] | ]. wpc.
  chain_step; [reflexivity | eapply art_step_and_r; [exact F_53348 | reflexivity | exact D_53348 | reflexivity] | ]. wpc.
  chain_step; [reflexivity | eapply art_step_xor_r; [exact F_5334c | reflexivity | exact D_5334c | reflexivity] | ]. wpc.
  gres.
  rewrite art_cas23w by lia.

  chain_step; [reflexivity
    | eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m));
      [exact F_53350 | reflexivity | exact D_53350 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4 | gres; rwH; reflexivity
      | exact Whw' ]
    | ]. wpc.
  change (wbytes ?M0 (Z_to_bv 64 m) (word_to_le_bytes 4 (Z_to_bv 64 (3 + 256 * b1)))) with (Wn 4 M0 m (3 + 256 * b1)).
  zbft F_53354 D_53354.
  zret.
Qed.

Definition art_enq_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (B cnt bsz csz c m size : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (B + 8) (bsz + size)) (B + 16) (cnt + 1)) (B + 24 + 8 * cnt) m) (c + 24) (csz + size)).

#[using="Type"] Lemma art_enqueue_fn : forall regs (M rom : word -> option byte) (raw : word) (sp c B L cnt bsz csz m size : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 size ->
  64 <= sp -> sp < 2 ^ 64 -> 0x69c000 + 64 <= sp -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= B -> B + 8192 < 2 ^ 64 ->
  1 <= L < 2 ^ 63 -> 0 <= cnt < 1021 -> 0 <= bsz -> bsz + size < 2 ^ 64 -> 0 <= csz -> csz + size < 2 ^ 64 -> 0 <= size -> 0 <= m < 2 ^ 64 ->
  apart (sp - 64) 64 c 32 -> apart (sp - 64) 64 B 8192 -> apart c 32 B 8192 ->
  wrA M (sp - 64) 64 -> wrA M (c + 24) 8 -> wrA M B 8192 ->
  cellA M c 8 L -> cellA M (c + 16) 8 B -> cellA M (B + 16) 8 cnt -> cellA M (B + 8) 8 bsz -> cellA M (c + 24) 8 csz ->
  msteps ASEGS (mkst regs (0x57b68 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 11 (Z_to_bv 64 (csz + size))) 12 (Z_to_bv 64 (B + cnt * 2 ^ 3))) 15 (Z_to_bv 64 (cnt + 1))) 16 (Z_to_bv 64 B)) 17 (Z_to_bv 64 1021)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21))
          raw (art_enq_mem M sp raw regs B cnt bsz csz c m size) rom).
Proof.
  intros regs M rom raw sp c B L cnt bsz csz m size H1 Hret H2 H10 H13 H14 Hsp Hsp' IMG Hc Hc' HB HB' HL Hcnt Hbsz Hbsz' Hcsz Hcsz' Hsize Hm A1 A2 A3 W Wc WB CL CB Ccnt Cbsz Ccsz.
  zstep F_57b18 D_57b18.
  zsd F_57b1c D_57b1c (sp - 8) (U raw) ltac:(rewok W).
  zsd F_57b20 D_57b20 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_57b24 D_57b24 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_57b28 D_57b28 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_57b2c D_57b2c (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_57b30 D_57b30 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_57b34 D_57b34 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (CL' : cellA X c 8 L) by (unfold apart in *; recell CL);
    assert (CB' : cellA X (c + 16) 8 B) by (unfold apart in *; recell CB);
    assert (Ccnt' : cellA X (B + 16) 8 cnt) by (unfold apart in *; recell Ccnt);
    assert (Cbsz' : cellA X (B + 8) 8 bsz) by (unfold apart in *; recell Cbsz) end.
  zld F_57b38 D_57b38 c CL'.
  zbft F_57b3c D_57b3c.
  zld F_57b40 D_57b40 (c + 16) CB'.
  zld F_57b44 D_57b44 (B + 16) Ccnt'.
  zstep F_57b48 D_57b48.
  zbtk F_57b4c D_57b4c.
  zbft F_57bd4 D_57bd4.
  zld F_57bd8 D_57bd8 (B + 8) Cbsz'.
  zstep F_57bdc D_57bdc. zstep F_57be0 D_57be0. zstep F_57be4 D_57be4. zstep F_57be8 D_57be8.
  zsd F_57bec D_57bec (B + 8) (bsz + size) ltac:(unfold apart in *; rewok WB).
  zsd F_57bf0 D_57bf0 (B + 16) (cnt + 1) ltac:(unfold apart in *; rewok WB).
  zsd F_57bf4 D_57bf4 (B + 24 + 8 * cnt) m ltac:(unfold apart in *; rewok WB).
  stepn F_57bf8 D_57bf8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ccsz' : cellA X (c + 24) 8 csz) by (unfold apart in *; recell Ccsz) end.
  zld F_57c08 D_57c08 (c + 24) Ccsz'.
  zstep F_57c0c D_57c0c.
  zsd F_57c10 D_57c10 (c + 24) (csz + size) ltac:(unfold apart in *; rewok Wc).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cra : cellA X (sp - 8) 8 (U raw)) by (unfold apart in *; zcell);
    assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (unfold apart in *; zcell);
    assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (unfold apart in *; zcell);
    assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by (unfold apart in *; zcell);
    assert (Cs3 : cellA X (sp - 40) 8 (U (getr regs 19))) by (unfold apart in *; zcell);
    assert (Cs4 : cellA X (sp - 48) 8 (U (getr regs 20))) by (unfold apart in *; zcell);
    assert (Cs5 : cellA X (sp - 56) 8 (U (getr regs 21))) by (unfold apart in *; zcell) end.
  zld F_57c14 D_57c14 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_57c18 D_57c18 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_57c1c D_57c1c (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_57c20 D_57c20 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_57c24 D_57c24 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_57c28 D_57c28 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_57c2c D_57c2c (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_57c30 D_57c30.
  stepret F_57c34 D_57c34 raw ltac:(rwH; reflexivity).
  unfold art_enq_mem. zret.
Qed.
End FPX.
