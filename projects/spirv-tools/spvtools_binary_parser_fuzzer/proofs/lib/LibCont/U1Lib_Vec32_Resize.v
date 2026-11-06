(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim SumMemcpyBase SumMemcpy LibMaskBits U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts U1Facts U1Lib_Vec32_Index
  U1_code_65e7c_65ee8 U1_code_65f74_66328 U1_code_663dc_66418.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.
Module Ly := U1Layout.

Ltac rdn_fix H :=
  first [ exact H
        | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
            lazymatch type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
              replace a with a' by lia; exact H end end ].
Ltac rdA H := peel; rdn_fix H.
Ltac b2z8 := apply bytes_le_to_Z_8.
Ltac close_pc := lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end; f_equal; apply bv_eq; vm_compute; reflexivity.
Ltac wl := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => wlit v | |- _ => idtac end.
Ltac snl F D := stepn F D; pin; wl.

Ltac zval := gres; pin; imm_norm; apply bv_eq; unfold v_add, v_addi, v_sub, v_slli;
  rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; imm_norm;
  rewrite ?Z.add_0_r, ?Z.sub_0_r, ?Z.add_0_l, ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zminus_mod_idemp_l, ?Z.mod_mod by lia;
  first [ reflexivity | f_equal; lia | rewrite !Z.mod_small by lia; lia ].
Ltac rdW := peel; apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia.
Ltac rdWa a' :=
  lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with a' by lia end;
  peel; apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia.

Ltac cmpz := pin; unfold c_ltu, c_eq, c_lts, bv_ltu, bv_lts, bv_eqb; imm_norm; rewrite ?u64_of_Z by lia; rewrite ?bv_signed_small64 by lia;
  first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | reflexivity].
#[local] Ltac other_regs Hs :=
  intros r Hr; rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto]));
  first [ reflexivity | apply Hs; intros HH; apply Hr; revert HH; (first [solve [clear; cbv; tauto] | cbv; tauto]) ].

Section Resize.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis MALLOC_STACK_pos : (0 <= MALLOC_STACK MI)%Z.
  Hypothesis NEW : new_rule_stmt SEGS Ly.L MI ST (NEW_STACK SEGS Ly.L MI).

  #[local] Notation placed_sep := (placed_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation stack_sep := (stack_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation offimg_sep := (offimg_sep SEGS Ly.L ST ly_rw_img ly_relro_img ly_errno_img).

  Definition u1c65e18 : vec_consts := {| vc_entry := 0x65ebc; vc_stack := 112 |}.

  Definition MA (M : mem) (R : bvmap 5 word) (sp ret v n : Z) : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wslots M sp [getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret])
      (Z_to_bv 64 (sp - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x66028)))
      (Z_to_bv 64 (sp - 80)) (word_to_le_bytes 8 (Z_to_bv 64 v)))
      (Z_to_bv 64 (sp - 88)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 (Z_to_bv 64 v)))
      (Z_to_bv 64 (sp - 104)) (word_to_le_bytes 8 (Z_to_bv 64 0x6613c)))
      (Z_to_bv 64 (sp - 112)) (word_to_le_bytes 8 (Z_to_bv 64 (sp - 64))).

  Lemma LA : forall (fx : FPState) R M (sp ret v n : Z),
    getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp -> getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 n ->
    0 < n < 2 ^ 40 -> 2 ^ 20 <= sp - 112 -> sp < 2 ^ 47 -> 0 <= v -> v + 24 <= 2 ^ 63 -> (v + 24 <= sp - 112 \/ sp <= v) ->
    mdef M (sp - 112) 112 ->
    rdn SEGS M (Z_to_bv 64 v) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    rdn SEGS M (Z_to_bv 64 (v + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    rdn SEGS M (Z_to_bv 64 (v + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    exists Rn,
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x65ebc) M (seg_rom SEGS)) (@mkst fx Rn (Z_to_bv 64 (ly_new Ly.L)) (MA M R sp ret v n) (seg_rom SEGS))
      /\ getr Rn 10%bv = Z_to_bv 64 (4 * n) /\ getr Rn 11%bv = Z_to_bv 64 n /\ getr Rn 1%bv = Z_to_bv 64 0x6643c
      /\ getr Rn 2%bv = Z_to_bv 64 (sp - 112) /\ getr Rn 8%bv = Z_to_bv 64 n /\ getr Rn 9%bv = Z_to_bv 64 0
      /\ getr Rn 3%bv = getr R 3%bv /\ getr Rn 4%bv = getr R 4%bv
      /\ (forall r, In r [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr Rn r = getr R r).
  Proof using.
    intros fx R M sp ret v n Hra Hsp Ha0 Ha1 Hn Hspr Hsphi Hv0 Hv1 WINv HDW F0 F1 F2.
    assert (HOK : store_ok SEGS M (Z_to_bv 64 (sp - 112)) 112 = true) by (apply (mdef_store_ok SEGS M (sp - 112) 112); try lia; exact HDW).
    eexists. split.
    - norm_pc.
      ld_step F_65e7c D_65e7c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F0) ltac:(b2z8).
      ld_step F_65e80 D_65e80 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F1) ltac:(b2z8).
      snl F_65e84 D_65e84. snl F_65e88 D_65e88.
      stepb_ft F_65e8c D_65e8c ltac:(rewrite Ha1; cmpz).
      stepiv F_65e90 D_65e90 (Z_to_bv 64 n) ltac:(gres; pin; imm_norm; apply bv_eq; unfold v_sub; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; imm_norm; rewrite ?Z.sub_0_r, Z.mod_mod by lia; reflexivity).
      stepj F_65e94 D_65e94.

      sv F_65f74 D_65f74 (Z_to_bv 64 (sp - 64)).
      stw F_65f78 D_65f78 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
      stw F_65f7c D_65f7c (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
      stw F_65f80 D_65f80 (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_sub HOK).
      sv F_65f84 D_65f84 (Z_to_bv 64 v).
      ld_step F_65f88 D_65f88 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(peel; rdn_fix F1) ltac:(b2z8).
      ld_step F_65f8c D_65f8c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(peel; rdn_fix F2) ltac:(b2z8).
      snl F_65f90 D_65f90. snl F_65f94 D_65f94.
      sv F_65f98 D_65f98 (Z_to_bv 64 n).
      stepb_ft F_65f9c D_65f9c ltac:(cmpz).
      ld_step F_65fa0 D_65fa0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(peel; rdn_fix F0) ltac:(b2z8).
      snl F_65fa4 D_65fa4. snl F_65fa8 D_65fa8.
      stepiv F_65fac D_65fac (Z_to_bv 64 n) ltac:(gres; pin; imm_norm; apply bv_eq; unfold v_add; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; imm_norm; rewrite ?Z.add_0_l, Z.mod_mod by lia; reflexivity).
      stepiv F_65fb0 D_65fb0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_65fb4 D_65fb4 ltac:(apply c_eq_refl).
      snl F_65fb8 D_65fb8. snl F_65fbc D_65fbc.
      stepb_ft F_65fc0 D_65fc0 ltac:(cmpz).
      sv F_65fc4 D_65fc4 (Z_to_bv 64 n).
      snl F_65fc8 D_65fc8. snl F_65fcc D_65fcc.
      stepb_tk F_65fd0 D_65fd0 ltac:(vm_compute; reflexivity).
      sv F_65fdc D_65fdc (Z_to_bv 64 (sp - 64)).
      sv F_65fe0 D_65fe0 (Z_to_bv 64 v).
      stepj F_65fe4 D_65fe4.

      sv F_660d0 D_660d0 (Z_to_bv 64 (sp - 96)).
      stw F_660d4 D_660d4 (Z_to_bv 64 (sp - 72)) (Z_to_bv 64 0x66028) ltac:(ok_sub HOK).
      stw F_660d8 D_660d8 (Z_to_bv 64 (sp - 80)) (Z_to_bv 64 v) ltac:(ok_sub HOK).
      stw F_660dc D_660dc (Z_to_bv 64 (sp - 88)) (Z_to_bv 64 n) ltac:(ok_sub HOK).
      sv F_660e0 D_660e0 (Z_to_bv 64 0).
      sv F_660e4 D_660e4 (Z_to_bv 64 (sp - 64)).
      stw F_660e8 D_660e8 (Z_to_bv 64 (sp - 40)) (Z_to_bv 64 0) ltac:(ok_sub HOK).
      stw F_660ec D_660ec (Z_to_bv 64 (sp - 32)) (Z_to_bv 64 v) ltac:(ok_sub HOK).
      stepb_ft F_660f0 D_660f0 ltac:(cmpz).
      sv F_660f4 D_660f4 (Z_to_bv 64 v).
      stepj F_660f8 D_660f8.

      sv F_663dc D_663dc (Z_to_bv 64 (sp - 112)).
      stw F_663e0 D_663e0 (Z_to_bv 64 (sp - 104)) (Z_to_bv 64 0x6613c) ltac:(ok_sub HOK).
      stw F_663e4 D_663e4 (Z_to_bv 64 (sp - 112)) (Z_to_bv 64 (sp - 64)) ltac:(ok_sub HOK).
      stepiv F_663e8 D_663e8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_663ec D_663ec ltac:(apply c_eq_refl).
      sv F_663f0 D_663f0 (Z_to_bv 64 n).
      stepiv F_663f4 D_663f4 (Z_to_bv 64 (4 * n)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2 ^ 2) with 4; lia).
      stepj F_663f8 D_663f8.
      unfold MA. close_pc.
    - gres. repeat split; try reflexivity.
      intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  Qed.

  Lemma LB : forall (fx : FPState) R2 Mb (sp v n p : Z) (R : bvmap 5 word),
    getr R2 10%bv = Z_to_bv 64 p -> getr R2 2%bv = Z_to_bv 64 (sp - 112) ->
    getr R2 8%bv = Z_to_bv 64 n -> getr R2 9%bv = Z_to_bv 64 0 ->
    0 < n < 2 ^ 40 -> 2 ^ 20 <= sp - 112 -> sp < 2 ^ 47 -> 0 < v -> v + 24 <= 2 ^ 63 -> 16 <= p -> p mod 16 = 0 -> p + 4 * n <= 2 ^ 63 ->
    (v + 24 <= sp - 112 \/ sp <= v) -> (p + 4 * n <= sp - 112) ->
    mdef Mb (sp - 112) 112 ->
    rdn SEGS Mb (Z_to_bv 64 (sp - 104)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6613c)) ->
    rdn SEGS Mb (Z_to_bv 64 (sp - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (sp - 64))) ->
    rdn SEGS Mb (Z_to_bv 64 (sp - 72)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x66028)) ->
    rdn SEGS Mb (Z_to_bv 64 (sp - 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) ->
    rdn SEGS Mb (Z_to_bv 64 (sp - 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 n)) ->
    rdn SEGS Mb (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) ->
    exists R3,
      msteps SEGS (@mkst fx R2 (Z_to_bv 64 0x6643c) Mb (seg_rom SEGS))
                  (@mkst fx R3 (Z_to_bv 64 0x66204)
                     (wbytes (wbytes (wbytes (wbytes Mb
                        (Z_to_bv 64 (sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 p)))
                        (Z_to_bv 64 (sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 p)))
                        (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 (Z_to_bv 64 p)))
                        (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * n)))) (seg_rom SEGS))
      /\ getr R3 10%bv = Z_to_bv 64 (sp - 64) /\ getr R3 11%bv = Z_to_bv 64 (p + 4 * n) /\ getr R3 12%bv = Z_to_bv 64 p
      /\ getr R3 13%bv = Z_to_bv 64 (4 * n) /\ getr R3 14%bv = Z_to_bv 64 v /\ getr R3 15%bv = Z_to_bv 64 0
      /\ getr R3 16%bv = Z_to_bv 64 (2 ^ 64 - 4) /\ getr R3 17%bv = Z_to_bv 64 p
      /\ getr R3 8%bv = Z_to_bv 64 v /\ getr R3 9%bv = Z_to_bv 64 n /\ getr R3 1%bv = Z_to_bv 64 0x66034 /\ getr R3 2%bv = Z_to_bv 64 (sp - 64)
      /\ (forall r, In r [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R3 r = getr R2 r).
  Proof using.
    intros fx R2 Mb sp v n p R G10 G2 G8 G9 Hn Hspr Hsphi Hv0 Hv1 Hp16 Hpal Hpn WINv Hpsp HDW Q104 Q112 Q72 Q80 Q88 Q32.
    assert (Hp4 : p mod 4 = 0) by (pose proof (Z.div_mod p 16 ltac:(lia)); pose proof (Z.div_mod p 4 ltac:(lia)); pose proof (Z.mod_pos_bound p 4 ltac:(lia)); nia).
    eexists. split.
    - norm_pc.
      sv F_663fc D_663fc (Z_to_bv 64 n).
      ld_step F_66400 D_66400 (word_to_le_bytes 8 (Z_to_bv 64 0x6613c)) (Z_to_bv 64 0x6613c) ltac:(rdn_fix Q104) ltac:(b2z8).
      ld_step F_66404 D_66404 (word_to_le_bytes 8 (Z_to_bv 64 (sp - 64))) (Z_to_bv 64 (sp - 64)) ltac:(rdn_fix Q112) ltac:(b2z8).
      sv F_66408 D_66408 (Z_to_bv 64 (sp - 96)).
      stepjr F_6640c D_6640c (Z_to_bv 64 0x6613c) ltac:(gres; reflexivity).
      stepj F_660fc D_660fc.
      snl F_66104 D_66104.
      stepiv F_66108 D_66108 (Z_to_bv 64 p) ltac:(gres; pin; imm_norm; apply bv_eq; unfold v_add; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; imm_norm; rewrite ?Z.add_0_l, Z.mod_mod by lia; reflexivity).
      stepsltu F_6610c D_6610c (Z_to_bv 64 1) ltac:(gres; pin; apply snez_Z; lia).
      stepiv F_66110 D_66110 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite sltiu_1_Z by lia; destruct (Z.eqb_spec p 0); [lia|reflexivity]).
      stw F_66114 D_66114 (Z_to_bv 64 (sp - 64)) (Z_to_bv 64 p) ltac:(ok_mdef HDW).
      stepb_ft F_66118 D_66118 ltac:(vm_compute; reflexivity).
      snl F_6611c D_6611c. snl F_66120 D_66120.
      snl F_66124 D_66124. snl F_66128 D_66128.
      stepb_ft F_6612c D_6612c ltac:(vm_compute; reflexivity).
      stepb_ft F_66130 D_66130 ltac:(cmpz).
      stepiv F_66134 D_66134 (Z_to_bv 64 (4 * n)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2 ^ 2) with 4; lia).
      stepiv F_66138 D_66138 (Z_to_bv 64 (p + 4 * n)) ltac:(gres; pin; rewrite v_add_Z by lia; f_equal; lia).
      stepiv F_6613c D_6613c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite sltiu_1_Z by lia; destruct (Z.eqb_spec (p + 4 * n) 0); [lia|reflexivity]).
      stw F_66140 D_66140 (Z_to_bv 64 (sp - 56)) (Z_to_bv 64 p) ltac:(ok_mdef HDW).
      stw F_66144 D_66144 (Z_to_bv 64 (sp - 48)) (Z_to_bv 64 p) ltac:(ok_mdef HDW).
      stepb_ft F_66148 D_66148 ltac:(vm_compute; reflexivity).
      stepiv F_6614c D_6614c (Z_to_bv 64 (n + 2 ^ 61)) ltac:(zval).
      stepiv F_66150 D_66150 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_66154 D_66154 ltac:(apply c_eq_refl).
      stepb_ft F_66158 D_66158 ltac:(cmpz).
      stw F_6615c D_6615c (Z_to_bv 64 (sp - 40)) (Z_to_bv 64 (p + 4 * n)) ltac:(ok_mdef HDW).
      ld_step F_66160 D_66160 (word_to_le_bytes 8 (Z_to_bv 64 0x66028)) (Z_to_bv 64 0x66028) ltac:(rdA Q72) ltac:(b2z8).
      ld_step F_66164 D_66164 (word_to_le_bytes 8 (Z_to_bv 64 v)) (Z_to_bv 64 v) ltac:(rdA Q80) ltac:(b2z8).
      ld_step F_66168 D_66168 (word_to_le_bytes 8 (Z_to_bv 64 n)) (Z_to_bv 64 n) ltac:(rdA Q88) ltac:(b2z8).
      sv F_6616c D_6616c (Z_to_bv 64 (sp - 64)).
      stepjr F_66170 D_66170 (Z_to_bv 64 0x66028) ltac:(gres; reflexivity).

      sv F_65fe8 D_65fe8 (Z_to_bv 64 (sp - 64)).
      sv F_65fec D_65fec (Z_to_bv 64 n).
      stepj F_65ff0 D_65ff0.

      ld_step F_66178 D_66178 (word_to_le_bytes 8 (Z_to_bv 64 p)) (Z_to_bv 64 p) ltac:(rdWa (sp - 48)) ltac:(b2z8).
      stepiv F_6617c D_6617c (Z_to_bv 64 (4 * n)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2 ^ 2) with 4; lia).
      stepiv F_66180 D_66180 (Z_to_bv 64 (p + 4 * n)) ltac:(gres; pin; rewrite v_add_Z by lia; f_equal; lia).
      stepsltu F_66184 D_66184 (Z_to_bv 64 1) ltac:(gres; pin; apply snez_Z; lia).
      stepiv F_66188 D_66188 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite sltiu_1_Z by lia; destruct (Z.eqb_spec (p + 4 * n) 0); [lia|reflexivity]).
      stepb_ft F_6618c D_6618c ltac:(vm_compute; reflexivity).
      snl F_66190 D_66190. snl F_66194 D_66194.
      stepiv F_66198 D_66198 (Z_to_bv 64 (n + 2 ^ 61)) ltac:(zval).
      stepiv F_6619c D_6619c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_661a0 D_661a0 ltac:(apply c_eq_refl).
      stepb_ft F_661a4 D_661a4 ltac:(cmpz).
      stepb_ft F_661a8 D_661a8 ltac:(cmpz).
      stepiv F_661ac D_661ac (Z_to_bv 64 (4 * n)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2 ^ 2) with 4; lia).
      ld_step F_661b0 D_661b0 (word_to_le_bytes 8 (Z_to_bv 64 v)) (Z_to_bv 64 v) ltac:(rdA Q32) ltac:(b2z8).
      stepiv F_661b4 D_661b4 (Z_to_bv 64 (p + 4 * n)) ltac:(gres; pin; rewrite v_add_Z by lia; f_equal; lia).
      stepiv F_661b8 D_661b8 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; f_equal; change 3 with (2 ^ 2 - 1); rewrite land_ones_mod by lia; change (2 ^ 2) with 4; exact Hp4).
      stepiv F_661bc D_661bc (Z_to_bv 64 (2 ^ 64 - 4)) ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
      sv F_661c0 D_661c0 (Z_to_bv 64 p).
      close_pc.
    - gres. repeat split; try reflexivity.
      intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  Qed.

  Lemma ZLOOP : forall (fx : FPState) (k : nat) (i p n v : Z) R Mi,
    i + Z.of_nat (S k) = n -> 0 <= i -> 16 <= p -> p + 4 * n <= 2 ^ 63 -> 0 < v < 2 ^ 64 ->
    getr R 12%bv = Z_to_bv 64 (p + 4 * i) -> getr R 13%bv = Z_to_bv 64 (4 * Z.of_nat (S k)) -> getr R 14%bv = Z_to_bv 64 v ->
    getr R 15%bv = Z_to_bv 64 0 -> getr R 16%bv = Z_to_bv 64 (2 ^ 64 - 4) -> getr R 17%bv = Z_to_bv 64 (p + 4 * i) ->
    mdef Mi p (4 * n) ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x66204) Mi (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 0x6622c) M' (seg_rom SEGS))
      /\ (forall r, r <> 12%bv -> r <> 13%bv -> r <> 17%bv -> getr R' r = getr R r)
      /\ stores_in (zwin (p + 4 * i) (p + 4 * n)) Mi M'
      /\ (forall j, i <= j < n -> fld SEGS M' (p + 4 * j) 4 0).
  Proof using.
    intros fx k. induction k as [|k IH]; intros i p n v R Mi Hk Hi Hp Hpn Hv G12 G13 G14 G15 G16 G17 HD.
    - eexists _, (wbytes Mi (Z_to_bv 64 (p + 4 * i)) (word_to_le_bytes 4 (Z_to_bv 64 0))). split; [|split; [|split]].
      + norm_pc.
        stepb_ft F_661c4 D_661c4 ltac:(cmpz).
        stepb_ft F_661c8 D_661c8 ltac:(cmpz).
        stepb_ft F_661cc D_661cc ltac:(pin; apply c_eq_refl).
        stw F_661d0 D_661d0 (Z_to_bv 64 (p + 4 * i)) (Z_to_bv 64 0) ltac:(ok_mdef HD).
        stepb_ft F_661d4 D_661d4 ltac:(cmpz).
        stepb_ft F_661d8 D_661d8 ltac:(cmpz).
        stepiv F_661dc D_661dc (Z_to_bv 64 (p + 4 * (i + 1))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        stepiv F_661e0 D_661e0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        stepiv F_661e4 D_661e4 (Z_to_bv 64 (p + 4 * (i + 1))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        stepb_ft F_661e8 D_661e8 ltac:(apply c_eq_refl).
        close_pc.
      + intros r H12 H13 H17. rewrite !getr_other by assumption. reflexivity.
      + apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; cbn; try lia. intros a Ha. unfold zwin. lia.
      + intros j Hj. replace j with i by lia. unfold fld. apply rdn_wbytes_hit4. rewrite u64_of_Z by lia. lia.
    - set (M1 := wbytes Mi (Z_to_bv 64 (p + 4 * i)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
      set (R1 := regupd (regupd (regupd R 12%bv (Z_to_bv 64 (p + 4 * (i + 1)))) 13%bv (Z_to_bv 64 (4 * Z.of_nat (S k)))) 17%bv (Z_to_bv 64 (p + 4 * (i + 1)))).
      destruct (IH (i + 1) p n v R1 M1 ltac:(lia) ltac:(lia) Hp Hpn Hv
                  ltac:(unfold R1; gres; reflexivity) ltac:(unfold R1; gres; reflexivity) ltac:(unfold R1; gres; exact G14)
                  ltac:(unfold R1; gres; exact G15) ltac:(unfold R1; gres; exact G16) ltac:(unfold R1; gres; reflexivity)
                  ltac:(unfold M1; apply mdef_wbytes; exact HD)) as (R' & M' & RUN & GS & SI & FJ).
      exists R', M'. split; [|split; [|split]].
      + norm_pc.
        stepb_ft F_661c4 D_661c4 ltac:(cmpz).
        stepb_ft F_661c8 D_661c8 ltac:(cmpz).
        stepb_ft F_661cc D_661cc ltac:(pin; apply c_eq_refl).
        stw F_661d0 D_661d0 (Z_to_bv 64 (p + 4 * i)) (Z_to_bv 64 0) ltac:(ok_mdef HD).
        stepb_ft F_661d4 D_661d4 ltac:(cmpz).
        stepb_ft F_661d8 D_661d8 ltac:(cmpz).
        stepiv F_661dc D_661dc (Z_to_bv 64 (p + 4 * (i + 1))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        stepiv F_661e0 D_661e0 (Z_to_bv 64 (4 * Z.of_nat (S k))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        stepiv F_661e4 D_661e4 (Z_to_bv 64 (p + 4 * (i + 1))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        stepb_tk F_661e8 D_661e8 ltac:(cmpz).
        fold M1. fold R1. eapply msteps_trans; [|exact RUN]. close_pc.
      + intros r H12 H13 H17. rewrite (GS r H12 H13 H17). unfold R1. rewrite !getr_other by assumption. reflexivity.
      + eapply stores_in_trans; [| eapply stores_in_weaken; [exact SI|]; intros a Ha; unfold zwin in *; lia].
        unfold M1. apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; cbn; try lia. intros a Ha. unfold zwin. lia.
      + intros j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [| apply FJ; lia].
        eapply fld_agree; [lia | cbn; lia | unfold fld, M1; apply rdn_wbytes_hit4; rewrite u64_of_Z by lia; lia |].
        eapply stores_in_agree; [exact SI|]. intros a Ha. unfold zwin in *; cbn in Ha. split; lia.
  Qed.

  Definition MCf (Mz : mem) (sp v n p : Z) (s2v : word) : mem :=
    let w a z m := wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 z)) in
    w (sp - 40) 0 (w (sp - 64) 0 (w (v + 16) (p + 4 * n) (w (sp - 48) 0 (w (v + 8) (p + 4 * n) (w (sp - 56) 0 (w v p (w (v + 8) 0 (w (sp - 56) p
      (wbytes (w (sp - 88) n (w (sp - 80) v (w (sp - 72) 0x66040 (w (sp - 48) (p + 4 * n) Mz)))) (Z_to_bv 64 (sp - 96)) (word_to_le_bytes 8 s2v)))))))))).

  Lemma v_sltu_irrefl : forall a, 0 <= a < 2 ^ 64 -> v_sltu (Z_to_bv 64 a) (Z_to_bv 64 a) = Z_to_bv 64 0.
  Proof using. intros a Ha. unfold v_sltu. rewrite c_ltu_Z by lia. rewrite Z.ltb_irrefl. reflexivity. Qed.

  Lemma LC : forall (fx : FPState) R4 Mz (sp ret v n p : Z) (R : bvmap 5 word),
    getr R4 10%bv = Z_to_bv 64 (sp - 64) -> getr R4 11%bv = Z_to_bv 64 (p + 4 * n) -> getr R4 8%bv = Z_to_bv 64 v -> getr R4 9%bv = Z_to_bv 64 n ->
    getr R4 1%bv = Z_to_bv 64 0x66034 -> getr R4 2%bv = Z_to_bv 64 (sp - 64) -> getr R4 18%bv = getr R 18%bv ->
    0 < n < 2 ^ 40 -> 2 ^ 20 <= sp - 112 -> sp < 2 ^ 47 -> 0 < v -> v + 24 <= 2 ^ 63 -> 16 <= p -> p + 4 * n <= 2 ^ 63 ->
    (v + 24 <= sp - 112 \/ sp <= v) -> (p + 4 * n <= sp - 112) -> (v + 24 <= p \/ p + 4 * n <= v) ->
    mdef Mz (sp - 112) 112 -> mdef Mz v 24 -> ret_ok (Z_to_bv 64 ret) ->
    rdn SEGS Mz (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret)) ->
    rdn SEGS Mz (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8%bv)) ->
    rdn SEGS Mz (Z_to_bv 64 (sp - 24)) 8 = Some (word_to_le_bytes 8 (getr R 9%bv)) ->
    rdn SEGS Mz (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) ->
    rdn SEGS Mz (Z_to_bv 64 (sp - 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * n))) ->
    rdn SEGS Mz (Z_to_bv 64 (sp - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p)) ->
    rdn SEGS Mz (Z_to_bv 64 v) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    rdn SEGS Mz (Z_to_bv 64 (v + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    rdn SEGS Mz (Z_to_bv 64 (v + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    exists R',
      msteps SEGS (@mkst fx R4 (Z_to_bv 64 0x6622c) Mz (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 ret) (MCf Mz sp v n p (getr R 18%bv)) (seg_rom SEGS))
      /\ getr R' 2%bv = Z_to_bv 64 sp /\ getr R' 1%bv = Z_to_bv 64 ret /\ getr R' 8%bv = getr R 8%bv /\ getr R' 9%bv = getr R 9%bv
      /\ getr R' 18%bv = getr R 18%bv
      /\ (forall r, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R4 r).
  Proof using.
    intros fx R4 Mz sp ret v n p R G10 G11 G8 G9 G1 G2 G18 Hn Hspr Hsphi Hv0 Hv1 Hp16 Hpn WINv Hpsp HDRp HDW HDv Hret
           Q8 Q16 Q24 Q32 Q40 Q56 F0 F1 F2.

    set (M5 := wbytes (wbytes (wbytes (wbytes (wbytes Mz
                 (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * n))))
                 (Z_to_bv 64 (sp - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x66040)))
                 (Z_to_bv 64 (sp - 80)) (word_to_le_bytes 8 (Z_to_bv 64 v)))
                 (Z_to_bv 64 (sp - 88)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
                 (Z_to_bv 64 (sp - 96)) (word_to_le_bytes 8 (getr R 18%bv))).
    assert (HD5 : mdef M5 (sp - 112) 112) by (unfold M5; repeat apply mdef_wbytes; exact HDW).
    assert (HDv5 : mdef M5 v 24) by (unfold M5; repeat apply mdef_wbytes; exact HDv).
    assert (P1 : exists R5, msteps SEGS (@mkst fx R4 (Z_to_bv 64 0x6622c) Mz (seg_rom SEGS)) (@mkst fx R5 u1_memcpy_entry M5 (seg_rom SEGS))
      /\ getr R5 10%bv = Z_to_bv 64 p /\ getr R5 11%bv = Z_to_bv 64 0 /\ getr R5 12%bv = Z_to_bv 64 0 /\ getr R5 1%bv = Z_to_bv 64 0x662c0
      /\ getr R5 2%bv = Z_to_bv 64 (sp - 96) /\ getr R5 8%bv = Z_to_bv 64 (sp - 64) /\ getr R5 9%bv = Z_to_bv 64 v /\ getr R5 18%bv = Z_to_bv 64 p
      /\ (forall r, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R5 r = getr R4 r)).
    { eexists. split.
      - norm_pc.
        sv F_661ec D_661ec (Z_to_bv 64 (p + 4 * n)).
        stw F_661f0 D_661f0 (Z_to_bv 64 (sp - 48)) (Z_to_bv 64 (p + 4 * n)) ltac:(ok_mdef HDW).
        stepjr F_661f4 D_661f4 (Z_to_bv 64 0x66034) ltac:(gres; exact G1).
        sv F_65ff4 D_65ff4 (Z_to_bv 64 (sp - 64)).
        sv F_65ff8 D_65ff8 (Z_to_bv 64 v).
        stepj F_65ffc D_65ffc.

        sv F_661fc D_661fc (Z_to_bv 64 (sp - 96)).
        stw F_66200 D_66200 (Z_to_bv 64 (sp - 72)) (Z_to_bv 64 0x66040) ltac:(ok_mdef HDW).
        stw F_66204 D_66204 (Z_to_bv 64 (sp - 80)) (Z_to_bv 64 v) ltac:(ok_mdef HDW).
        stw F_66208 D_66208 (Z_to_bv 64 (sp - 88)) (Z_to_bv 64 n) ltac:(ok_mdef HDW).
        stw F_6620c D_6620c (Z_to_bv 64 (sp - 96)) (getr R 18%bv) ltac:(ok_mdef HDW).
        sv F_66210 D_66210 (Z_to_bv 64 (sp - 64)).
        sv F_66214 D_66214 (Z_to_bv 64 v).
        ld_step F_66218 D_66218 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA F0) ltac:(b2z8).
        ld_step F_6621c D_6621c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA F1) ltac:(b2z8).
        ld_step F_66220 D_66220 (word_to_le_bytes 8 (Z_to_bv 64 p)) (Z_to_bv 64 p) ltac:(rdA Q56) ltac:(b2z8).
        snl F_66224 D_66224.
        stepiv F_66228 D_66228 (Z_to_bv 64 p) ltac:(zval).
        stepsltu F_6622c D_6622c (Z_to_bv 64 1) ltac:(gres; pin; apply snez_Z; lia).
        stepiv F_66230 D_66230 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite sltiu_1_Z by lia; destruct (Z.eqb_spec p 0); [lia|reflexivity]).
        stepb_ft F_66234 D_66234 ltac:(vm_compute; reflexivity).
        snl F_66238 D_66238. snl F_6623c D_6623c. snl F_66240 D_66240. snl F_66244 D_66244. snl F_66248 D_66248.
        stepb_ft F_6624c D_6624c ltac:(vm_compute; reflexivity).
        snl F_66250 D_66250. snl F_66254 D_66254.
        stepsltu F_66258 D_66258 (Z_to_bv 64 0) ltac:(gres; pin; apply v_sltu_irrefl; lia).
        snl F_6625c D_6625c. snl F_66260 D_66260. snl F_66264 D_66264.
        stepb_ft F_66268 D_66268 ltac:(vm_compute; reflexivity).
        snl F_6626c D_6626c.
        stepb_ft F_66270 D_66270 ltac:(vm_compute; reflexivity).
        stepiv F_66274 D_66274 (Z_to_bv 64 p) ltac:(zval).
        sv F_66278 D_66278 (Z_to_bv 64 p).
        stepj F_6627c D_6627c.
        unfold M5. close_pc.
      - gres. repeat split; try reflexivity; try assumption; try (apply bv_eq; vm_compute; reflexivity).
        intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    destruct P1 as (R5 & RUN1 & G5_10 & G5_11 & G5_12 & G5_1 & G5_2 & G5_8 & G5_9 & G5_18 & G5S).

    assert (MC : mcH SEGS M5 (Z_to_bv 64 p) (Z_to_bv 64 0) 0 []).
    { constructor; rewrite ?u64_of_Z by lia; cbn; try lia; try reflexivity. }
    destruct (u1_memcpy M5 (Z_to_bv 64 p) (Z_to_bv 64 0) 0 [] (seg_rom SEGS) R5 (Z_to_bv 64 0x662c0)
                MC ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) G5_1 G5_10 G5_11 G5_12) as (R6 & RUN6 & KEEP6).
    change (wbytes M5 (Z_to_bv 64 p) []) with M5 in RUN6.
    assert (G6_2 : getr R6 2%bv = Z_to_bv 64 (sp - 96)) by (rewrite (KEEP6 2%bv) by in_cs; exact G5_2).
    assert (G6_8 : getr R6 8%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KEEP6 8%bv) by in_cs; exact G5_8).
    assert (G6_9 : getr R6 9%bv = Z_to_bv 64 v) by (rewrite (KEEP6 9%bv) by in_cs; exact G5_9).
    assert (G6_18 : getr R6 18%bv = Z_to_bv 64 p) by (rewrite (KEEP6 18%bv) by in_cs; exact G5_18).
    assert (Q8' : rdn SEGS M5 (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret))) by (unfold M5; rdA Q8).
    assert (Q16' : rdn SEGS M5 (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8%bv))) by (unfold M5; rdA Q16).
    assert (Q24' : rdn SEGS M5 (Z_to_bv 64 (sp - 24)) 8 = Some (word_to_le_bytes 8 (getr R 9%bv))) by (unfold M5; rdA Q24).
    assert (Q32' : rdn SEGS M5 (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v))) by (unfold M5; rdA Q32).
    assert (Q40' : rdn SEGS M5 (Z_to_bv 64 (sp - 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * n)))) by (unfold M5; rdA Q40).
    assert (Q48' : rdn SEGS M5 (Z_to_bv 64 (sp - 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * n)))) by (unfold M5; rdWa (sp - 48)).
    assert (Q72' : rdn SEGS M5 (Z_to_bv 64 (sp - 72)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x66040))) by (unfold M5; rdWa (sp - 72)).
    assert (Q80' : rdn SEGS M5 (Z_to_bv 64 (sp - 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v))) by (unfold M5; rdWa (sp - 80)).
    assert (Q88' : rdn SEGS M5 (Z_to_bv 64 (sp - 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 n))) by (unfold M5; rdWa (sp - 88)).
    assert (Q96' : rdn SEGS M5 (Z_to_bv 64 (sp - 96)) 8 = Some (word_to_le_bytes 8 (getr R 18%bv))) by (unfold M5; rdWa (sp - 96)).
    assert (F0' : rdn SEGS M5 (Z_to_bv 64 v) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by (unfold M5; rdA F0).
    assert (F1' : rdn SEGS M5 (Z_to_bv 64 (v + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by (unfold M5; rdA F1).
    assert (F2' : rdn SEGS M5 (Z_to_bv 64 (v + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by (unfold M5; rdA F2).
    eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN6|]. norm_pc.
      ld_step F_66280 D_66280 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F0') ltac:(b2z8).
      stw F_66284 D_66284 (Z_to_bv 64 (sp - 56)) (Z_to_bv 64 p) ltac:(ok_mdef HD5).
      stw F_66288 D_66288 (Z_to_bv 64 (v + 8)) (Z_to_bv 64 0) ltac:(ok_mdef HDv5).
      ld_step F_6628c D_6628c (word_to_le_bytes 8 (Z_to_bv 64 p)) (Z_to_bv 64 p) ltac:(rdWa (sp - 56)) ltac:(b2z8).
      stw F_66290 D_66290 (Z_to_bv 64 v) (Z_to_bv 64 p) ltac:(ok_mdef HDv5).
      ld_step F_66294 D_66294 (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * n))) (Z_to_bv 64 (p + 4 * n)) ltac:(rdA Q48') ltac:(b2z8).
      stw F_66298 D_66298 (Z_to_bv 64 (sp - 56)) (Z_to_bv 64 0) ltac:(ok_mdef HD5).
      ld_step F_6629c D_6629c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdWa (v + 8)) ltac:(b2z8).
      stw F_662a0 D_662a0 (Z_to_bv 64 (v + 8)) (Z_to_bv 64 (p + 4 * n)) ltac:(ok_mdef HDv5).
      ld_step F_662a4 D_662a4 (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * n))) (Z_to_bv 64 (p + 4 * n)) ltac:(rdA Q40') ltac:(b2z8).
      stw F_662a8 D_662a8 (Z_to_bv 64 (sp - 48)) (Z_to_bv 64 0) ltac:(ok_mdef HD5).
      ld_step F_662ac D_662ac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA F2') ltac:(b2z8).
      stw F_662b0 D_662b0 (Z_to_bv 64 (v + 16)) (Z_to_bv 64 (p + 4 * n)) ltac:(ok_mdef HDv5).
      ld_step F_662b4 D_662b4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdWa (sp - 56)) ltac:(b2z8).
      stw F_662b8 D_662b8 (Z_to_bv 64 (sp - 64)) (Z_to_bv 64 0) ltac:(ok_mdef HD5).
      stw F_662bc D_662bc (Z_to_bv 64 (sp - 40)) (Z_to_bv 64 0) ltac:(ok_mdef HD5).
      ld_step F_662c0 D_662c0 (word_to_le_bytes 8 (Z_to_bv 64 0x66040)) (Z_to_bv 64 0x66040) ltac:(rdA Q72') ltac:(b2z8).
      ld_step F_662c4 D_662c4 (word_to_le_bytes 8 (Z_to_bv 64 v)) (Z_to_bv 64 v) ltac:(rdA Q80') ltac:(b2z8).
      ld_step F_662c8 D_662c8 (word_to_le_bytes 8 (Z_to_bv 64 n)) (Z_to_bv 64 n) ltac:(rdA Q88') ltac:(b2z8).
      ld_step F_662cc D_662cc (word_to_le_bytes 8 (getr R 18%bv)) (getr R 18%bv) ltac:(rdA Q96') ltac:(b2z8).
      sv F_662d0 D_662d0 (Z_to_bv 64 (sp - 64)).
      stepjr F_662d4 D_662d4 (Z_to_bv 64 0x66040) ltac:(gres; reflexivity).

      sv F_66000 D_66000 (Z_to_bv 64 (sp - 64)).
      stepj F_66004 D_66004.
      ld_step F_662dc D_662dc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdWa (sp - 56)) ltac:(b2z8).
      ld_step F_662e0 D_662e0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdWa (sp - 48)) ltac:(b2z8).
      ld_step F_662e4 D_662e4 (word_to_le_bytes 8 (Z_to_bv 64 v)) (Z_to_bv 64 v) ltac:(rdA Q32') ltac:(b2z8).
      stepb_tk F_662e8 D_662e8 ltac:(apply c_eq_refl).
      ld_step F_66304 D_66304 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdWa (sp - 64)) ltac:(b2z8).
      stepb_tk F_66308 D_66308 ltac:(apply c_eq_refl).
      stepjr F_66320 D_66320 (Z_to_bv 64 0x66048) ltac:(gres; reflexivity).

      ld_step F_66008 D_66008 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(rdA Q8') ltac:(b2z8).
      ld_step F_6600c D_6600c (word_to_le_bytes 8 (getr R 8%bv)) (getr R 8%bv) ltac:(rdA Q16') ltac:(b2z8).
      ld_step F_66010 D_66010 (word_to_le_bytes 8 (getr R 9%bv)) (getr R 9%bv) ltac:(rdA Q24') ltac:(b2z8).
      sv F_66014 D_66014 (Z_to_bv 64 sp).
      stepjr F_66018 D_66018 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
      lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
        unify r' r; replace pc with pc' by (symmetry; imm_norm; exact Hret); replace m' with m by (unfold MCf, M5; reflexivity) end.
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; rewrite (KEEP6 _) by in_cs; apply G5S; exact Hr' |]). destruct Hr.
  Qed.
  Theorem vec32_resize_65e18_spec : vec32_resize_stmt SEGS Ly.L MI ST u1c65e18.
  Proof using AC MI ST MALLOC_STACK_pos NEW.
    intros fx A s R M model sp ret v n K.
    cbn [vc_entry vc_stack u1c65e18]. lazy zeta.
    intros CB Ha0 Ha1 VEC OBJ Hn0 HNMAX ROOM CONT.
    destruct CB as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
    destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    cbn [ly_gp ly_tp ly_errno_off ly_img ly_relro ly_rw Ly.L] in *.
    unfold NEW_STACK in *.
    pose proof ac_bounds_lit as Hceilv.
    destruct VEC as (Hv0 & Hv1 & HDv & Hlen & Hb & F0 & F1 & F2 & FE). clear Hb FE Hlen.
    change (Zlen (@nil Z)) with 0 in F1. rewrite Z.mul_0_r, Z.add_0_l in F1, F2.
    pose proof HROOM as HOK. unfold stack_room in HOK.
    assert (Hspr : 2 ^ 20 <= sp - (112 + (16 + MALLOC_STACK MI))) by (lia).
    pose proof (ai_nmax_bound MI) as HNM. pose proof (ai_big_pos MI) as HBIG.
    assert (Hn : 0 <= n < 2 ^ 40) by lia.
    destruct OBJ as [PLv WINv].
    assert (WINv' : v + 24 <= sp - (112 + (16 + MALLOC_STACK MI)) \/ sp <= v).
    { destruct (Z.lt_ge_cases v sp); [left|right; lia].
      destruct (Z.lt_ge_cases (v + 24) (sp - (112 + (16 + MALLOC_STACK MI)) + 1)); [lia|].
      exfalso. destruct (Z.lt_ge_cases v (sp - (112 + (16 + MALLOC_STACK MI)))).
      - apply (WINv (sp - (112 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (WINv v); unfold zwin; lia. }
    assert (Hvpos : 0 < v).
    { destruct PLv as [H|(q & k & Hin & H1 & H2)]; [lia|]. destruct (ai_live_block MI A M model q k AI Hin) as (_ & _ & Hq & _). lia. }
    assert (HDR : forall a, v <= a < v + 24 -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a).
    { intros a Ha. exact (placed_sep A M model v 24 a AI PLv Ha). }
    assert (WIN : forall a, sp - (112 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a).
    { intros a Ha. apply (stack_sep A M model a AI). lia. }
    assert (HDW : mdef M (sp - (112 + (16 + MALLOC_STACK MI))) (112 + (16 + MALLOC_STACK MI))).
    { eapply store_ok_mdef_offimg; [exact HOK | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }
    unfold fld in F0, F1, F2.
    destruct (Z.eq_dec n 0) as [Hnz|Hnnz].
    -
      subst n.
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
      { norm_pc.
        ld_step F_65e7c D_65e7c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F0) ltac:(b2z8).
        ld_step F_65e80 D_65e80 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F1) ltac:(b2z8).
        snl F_65e84 D_65e84. snl F_65e88 D_65e88.
        stepb_tk F_65e8c D_65e8c ltac:(rewrite Ha1; vm_compute; reflexivity).
        stepb_tk F_65e98 D_65e98 ltac:(rewrite Ha1; vm_compute; reflexivity).
        stepjr F_65ee0 D_65ee0 (Z_to_bv 64 ret) ltac:(gres; exact Hra).
        lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 ret) by (symmetry; imm_norm; exact Hret) end.
        apply mst_refl. }
      cbn [Z.to_nat repeat].
      eapply (CONT A _ M model 0).
      + constructor; [exact AI | exact MS | reflexivity | reflexivity | exact SXI |].
        intros r Hr. unfold callee_saved in Hr.
        repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption]|]). destruct Hr.
      + apply (vec32_nil MI); try assumption; try lia.
      + left. repeat split; reflexivity.
      + apply eff_refl.
    -
      set (M2 := MA M R sp ret v n).
      assert (ST2 : stores_in (zwin (sp - 112) sp) M M2).
      { unfold M2, MA. repeat (eapply stores_in_wbytes_more; [| lia | rewrite length_N_to_le_bytes; cbn; lia | intros a Ha; rewrite length_N_to_le_bytes in Ha; cbn in Ha; unfold zwin; lia]).
        eapply stores_in_weaken; [apply wslots_stores_in; unfold Zlen; cbn; lia|]. intros a Ha. unfold zwin, Zlen in *. cbn in *. lia. }
      assert (HD2 : mdef M2 (sp - (112 + (16 + MALLOC_STACK MI))) (112 + (16 + MALLOC_STACK MI))) by (eapply stores_in_mdef; [exact ST2 | exact HDW]).
      destruct (LA fx R M sp ret v n Hra Hsp Ha0 Ha1 ltac:(lia) ltac:(lia) Hsphi Hv0 Hv1 ltac:(lia)
                  ltac:(eapply mdef_sub; [exact HDW | lia | lia]) F0 F1 F2) as (Rn & RUNA & Rn10 & Rn11 & Rn1 & Rn2 & Rn8 & Rn9 & Rn3 & Rn4 & RnS).
      fold M2 in RUNA.
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact RUNA | ].
      eapply (NEW fx A s Rn M2 model (4 * n) (sp - 112) 0x6643c K).
      + eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST2 |]. intros a Ha. apply WIN. unfold zwin in Ha. lia.
      + exact MS.
      + eapply (roc_stores Ly.L); [exact ROC | exact ST2 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))).
      + eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST2 |].
        intros a Ha. destruct (offimg_sep a (proj2 (WIN a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption.
      + exact SXH.
      + constructor.
        * exact Rn1.
        * unfold ret_ok. apply bv_eq. vm_compute. reflexivity.
        * lia.
        * exact Rn2.
        * replace (sp - 112) with (sp - 16 * 7) by lia. apply mod16_sub. exact Hsp16.
        * lia.
        * rewrite Rn3. exact Hgp.
        * rewrite Rn4. exact Htp.
      + exact Rn10.
      + lia.
      + lia.
      + unfold stack_room. replace (sp - 112 - (16 + MALLOC_STACK MI)) with (sp - (112 + (16 + MALLOC_STACK MI))) by lia.
        apply (mdef_store_ok SEGS M2 _ (112 + (16 + MALLOC_STACK MI))); [exact HD2 | lia | lia | lia].
      + intros a Ha. apply Hwin. unfold zwin in *. lia.
      + exact Hown_sx.
      + exact Herr_sx.
      + rewrite new_size_id by lia. eapply (roomL_room_for SEGS Ly.L MI); [exact AI | lia | exact (ROOM ltac:(lia))].
      +
        intros A1 R2 M3 model1 p AI1 MS1 Hfs1 Hfds1 SX1 KEPT2 R2a0 Hp LADD CAPS1 BIGC1 NEWT1 FR1 DEF1.
        rewrite new_size_id in LADD, FR1 by lia.
        assert (ROC1 : img_ro_clear Ly.L M2).
        { eapply (roc_stores Ly.L); [exact ROC | exact ST2 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))). }
        assert (ROC2 : img_ro_clear Ly.L M3).
        { eapply (roc_frame Ly.L); [exact ROC1 | exact FR1 |]. intros a [Ho|[Hblk|[Hw|He]]].
          - exact (roc_owned SEGS Ly.L MI A1 M3 model1 a AI1 Ho).
          - right. eapply (live_offimg SEGS Ly.L MI); [exact AI1 | apply (live_add_new _ _ _ _ LADD) | exact Hblk].
          - right. apply (proj2 (stack_sep A1 M3 model1 a AI1 ltac:(unfold zwin in Hw; lia))).
          - left. apply ly_errno_rw. exact He. }
        assert (HinP : In (p, 4 * n) (live MI A1)) by (apply (live_add_new _ _ _ _ LADD)).
        destruct (live_range SEGS Ly.L MI A1 M3 model1 p (4 * n) AI1 HinP) as (_ & Hpal & _ & Hpce).
        assert (Hp16 : 16 <= p) by (pose proof (Z.div_mod p 16 ltac:(lia)); lia).
        assert (HDp : mdef M3 p (4 * n)) by (eapply (live_mdef SEGS Ly.L MI); eassumption).
        assert (Hpown : forall a, p <= a < p + 4 * n -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
        { intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption | eapply (live_offimg SEGS Ly.L MI); eassumption]. }
        assert (PLv1 : placed MI A1 v 24) by (eapply (placed_mono SEGS Ly.L MI); [intros blk Hblk; eapply live_add_keeps; eassumption | exact PLv]).
        assert (HDRp : v + 24 <= p \/ p + 4 * n <= v).
        { destruct (placed_new_block_disjoint SEGS Ly.L MI A A1 M M3 model model1 v 24 p (4 * n) AI AI1 PLv LADD ltac:(lia)) as [H|[H|H]]; [left|right|]; lia. }
        assert (WIN1 : forall a, sp - (112 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
        { intros a Ha. apply (stack_sep A1 M3 model1 a AI1). lia. }
        assert (HDR1 : forall a, v <= a < v + 24 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
        { intros a Ha. exact (placed_sep A1 M3 model1 v 24 a AI1 PLv1 Ha). }
        assert (PRES2 : forall a, (sp - 112 <= a < sp) \/ (v <= a < v + 24) -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
        { intros a Ha. assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha; lia).
          apply FR1. rewrite u64_of_Z by lia. intros [Ho|[Hblk|[Hw|He]]].
          - destruct Ha as [H|H]; [exact (proj1 (WIN1 a ltac:(lia)) Ho) | exact (proj1 (HDR1 a H) Ho)].
          - destruct Ha as [H|H]; lia.
          - unfold zwin in Hw. destruct Ha as [H|H]; lia.
          - pose proof (ly_img_low a (ly_errno_img a He)) as Hi.
            destruct Ha as [H|H]; [lia | exact (proj2 (HDR1 a H) (ly_errno_img a He))]. }
        assert (SLT2 : forall a vv (k : nat), (sp - 112 <= a /\ a + Z.of_nat k <= sp) \/ (v <= a /\ a + Z.of_nat k <= v + 24) ->
                  rdn SEGS M2 (Z_to_bv 64 a) k = Some vv -> rdn SEGS M3 (Z_to_bv 64 a) k = Some vv).
        { intros a vv k Ha H. rewrite <- H. apply rdn_agree_win; [lia|lia|]. intros x Hx. apply PRES2. unfold zwin in Hx. lia. }
        assert (R2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 112)) by (rewrite (KEPT2 2%bv) by in_cs; exact Rn2).
        assert (R2_8 : getr R2 8%bv = Z_to_bv 64 n) by (rewrite (KEPT2 8%bv) by in_cs; exact Rn8).
        assert (R2_9 : getr R2 9%bv = Z_to_bv 64 0) by (rewrite (KEPT2 9%bv) by in_cs; exact Rn9).

        assert (M2Q : forall a z, In (a, z) [(sp - 104, 0x6613c); (sp - 112, sp - 64); (sp - 72, 0x66028); (sp - 80, v); (sp - 88, n); (sp - 40, 0); (sp - 32, v)] ->
                      rdn SEGS M2 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 z))).
        { intros a z Hin. cbn in Hin. unfold M2, MA.
          repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; peel; apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia |]). destruct Hin. }
        assert (M2S : forall k, 1 <= k <= 3 -> rdn SEGS M2 (Z_to_bv 64 (sp - 8 * k)) 8
                      = Some (word_to_le_bytes 8 (nth (Z.to_nat (3 - k)) [getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret] (Z_to_bv 64 0)))).
        { intros k Hk. unfold M2, MA. peel. apply wslots_read; unfold Zlen; cbn; lia. }
        assert (M2F : forall a, In a [v; v + 8; v + 16] -> rdn SEGS M2 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
        { intros a Hin. unfold M2, MA. cbn in Hin.
          repeat (destruct Hin as [<-|Hin]; [peel; rewrite wslots_out; [assumption | unfold Zlen; cbn; lia | lia | lia | cbn; lia | unfold Zlen; cbn; lia] |]). destruct Hin. }
        assert (HDW3 : mdef M3 (sp - 112) 112).
        { eapply (mdef_through (fun a => owned MI A a \/ errno_win Ly.L a)); [exact DEF1 | eapply mdef_sub; [exact HD2|lia|lia] | lia | lia |].
          intros a Ha [Ho|He]; [exact (proj1 (WIN a ltac:(lia)) Ho) | exact (proj2 (WIN a ltac:(lia)) (ly_errno_img a He))]. }
        assert (HDv3 : mdef M3 v 24).
        { eapply (mdef_through (fun a => owned MI A a \/ errno_win Ly.L a)); [exact DEF1 | eapply stores_in_mdef; [exact ST2 | exact HDv] | lia | lia |].
          intros a Ha [Ho|He]; [exact (proj1 (HDR a ltac:(lia)) Ho) | exact (proj2 (HDR a ltac:(lia)) (ly_errno_img a He))]. }
        destruct (LB fx R2 M3 sp v n p R R2a0 R2_2 R2_8 R2_9 ltac:(lia) ltac:(lia) Hsphi Hvpos Hv1 Hp16 Hpal ltac:(lia) ltac:(lia) ltac:(lia) HDW3
                    ltac:(apply (SLT2 _ _ 8%nat); [cbn; lia | apply M2Q; (first [solve [clear; cbn; tauto] | cbn; tauto])])
                    ltac:(apply (SLT2 _ _ 8%nat); [cbn; lia | apply M2Q; (first [solve [clear; cbn; tauto] | cbn; tauto])])
                    ltac:(apply (SLT2 _ _ 8%nat); [cbn; lia | apply M2Q; (first [solve [clear; cbn; tauto] | cbn; tauto])])
                    ltac:(apply (SLT2 _ _ 8%nat); [cbn; lia | apply M2Q; (first [solve [clear; cbn; tauto] | cbn; tauto])])
                    ltac:(apply (SLT2 _ _ 8%nat); [cbn; lia | apply M2Q; (first [solve [clear; cbn; tauto] | cbn; tauto])])
                    ltac:(apply (SLT2 _ _ 8%nat); [cbn; lia | apply M2Q; (first [solve [clear; cbn; tauto] | cbn; tauto])]))
          as (R3 & RUN3 & G3_10 & G3_11 & G3_12 & G3_13 & G3_14 & G3_15 & G3_16 & G3_17 & G3_8 & G3_9 & G3_1 & G3_2 & G3S).
        set (M4 := wbytes (wbytes (wbytes (wbytes M3 (Z_to_bv 64 (sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 p)))
                     (Z_to_bv 64 (sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 p))) (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 (Z_to_bv 64 p)))
                     (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * n)))) in *.
        assert (ST34 : stores_in (zwin (sp - 64) (sp - 32)) M3 M4).
        { unfold M4. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [apply stores_in_wbytes | | |] | | |] | | |];
            rewrite ?length_N_to_le_bytes; cbn; try lia; intros a Ha; unfold zwin in *; lia. }
        destruct (ZLOOP fx (Z.to_nat (n - 1)) 0 p n v R3 M4 ltac:(rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia) ltac:(lia) Hp16 ltac:(lia) ltac:(lia)
                    ltac:(rewrite G3_12; f_equal; lia) ltac:(rewrite G3_13; f_equal; rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia) G3_14 G3_15 G3_16
                    ltac:(rewrite G3_17; f_equal; lia) ltac:(unfold M4; repeat apply mdef_wbytes; exact HDp))
          as (R4 & Mz & RUN4 & G4S & SIz & FJ).
        rewrite Z.mul_0_r, Z.add_0_r in SIz.
        assert (ST3z : stores_in (fun a => zwin (sp - 64) (sp - 32) a \/ zwin p (p + 4 * n) a) M3 Mz).
        { eapply stores_in_trans; [eapply stores_in_weaken; [exact ST34|]; intros a Ha; left; exact Ha | eapply stores_in_weaken; [exact SIz|]; intros a Ha; right; exact Ha]. }
        assert (AGz : forall a (k : nat) vv, (sp - 32 <= a /\ a + Z.of_nat k <= sp \/ sp - 112 <= a /\ a + Z.of_nat k <= sp - 64 \/ v <= a /\ a + Z.of_nat k <= v + 24) ->
                  rdn SEGS M3 (Z_to_bv 64 a) k = Some vv -> rdn SEGS Mz (Z_to_bv 64 a) k = Some vv).
        { intros a k vv Ha H. rewrite <- H. apply rdn_agree_win; [lia|lia|]. eapply stores_in_agree; [exact ST3z|].
          intros x Hx. unfold zwin in *. split; [lia|]. intros [Hy|Hy]; lia. }
        assert (M4Q : forall a z, In (a, z) [(sp - 56, p); (sp - 40, p + 4 * n)] -> rdn SEGS Mz (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 z))).
        { intros a z Hin. cbn in Hin.
          assert (H4 : rdn SEGS M4 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 z))).
          { unfold M4. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; peel; apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia |]). destruct Hin. }
          rewrite <- H4. apply rdn_agree_win; [destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; lia | destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; cbn; lia |].
          eapply stores_in_agree; [exact SIz|]. intros x Hx. unfold zwin in *. cbn in Hx.
          destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; split; lia. }
        destruct (LC fx R4 Mz sp ret v n p R
                    ltac:(rewrite G4S by (intros HH; inversion HH); exact G3_10) ltac:(rewrite G4S by (intros HH; inversion HH); exact G3_11)
                    ltac:(rewrite G4S by (intros HH; inversion HH); exact G3_8) ltac:(rewrite G4S by (intros HH; inversion HH); exact G3_9)
                    ltac:(rewrite G4S by (intros HH; inversion HH); exact G3_1) ltac:(rewrite G4S by (intros HH; inversion HH); exact G3_2)
                    ltac:(rewrite G4S by (intros HH; inversion HH); rewrite G3S by (first [solve [clear; cbv; tauto] | cbv; tauto]); rewrite (KEPT2 18%bv) by in_cs; apply RnS; (first [solve [clear; cbv; tauto] | cbv; tauto]))
                    ltac:(lia) ltac:(lia) Hsphi Hvpos Hv1 Hp16 ltac:(lia) ltac:(lia) ltac:(lia) HDRp
                    ltac:(eapply stores_in_mdef; [exact ST3z | exact HDW3]) ltac:(eapply stores_in_mdef; [exact ST3z | exact HDv3]) Hret
                    ltac:(apply (AGz _ 8%nat); [cbn; lia | apply (SLT2 _ _ 8%nat); [cbn; lia | exact (M2S 1 ltac:(lia))]])
                    ltac:(apply (AGz _ 8%nat); [cbn; lia | apply (SLT2 _ _ 8%nat); [cbn; lia | exact (M2S 2 ltac:(lia))]])
                    ltac:(apply (AGz _ 8%nat); [cbn; lia | apply (SLT2 _ _ 8%nat); [cbn; lia | exact (M2S 3 ltac:(lia))]])
                    ltac:(apply (AGz _ 8%nat); [cbn; lia | apply (SLT2 _ _ 8%nat); [cbn; lia | apply M2Q; (first [solve [clear; cbn; tauto] | cbn; tauto])]])
                    ltac:(apply M4Q; (first [solve [clear; cbn; tauto] | cbn; tauto])) ltac:(apply M4Q; (first [solve [clear; cbn; tauto] | cbn; tauto]))
                    ltac:(apply (AGz _ 8%nat); [cbn; lia | apply (SLT2 _ _ 8%nat); [cbn; lia | apply M2F; (first [solve [clear; cbn; tauto] | cbn; tauto])]])
                    ltac:(apply (AGz _ 8%nat); [cbn; lia | apply (SLT2 _ _ 8%nat); [cbn; lia | apply M2F; (first [solve [clear; cbn; tauto] | cbn; tauto])]])
                    ltac:(apply (AGz _ 8%nat); [cbn; lia | apply (SLT2 _ _ 8%nat); [cbn; lia | apply M2F; (first [solve [clear; cbn; tauto] | cbn; tauto])]]))
          as (R' & RUN5 & G'_2 & G'_1 & G'_8 & G'_9 & G'_18 & G'S).
        set (Mf := MCf Mz sp v n p (getr R 18%bv)) in *.
        assert (STzf : stores_in (fun a => zwin (sp - 112) sp a \/ zwin v (v + 24) a) Mz Mf).
        { unfold Mf, MCf. cbv zeta.
          repeat (first [ eapply stores_in_wbytes_more; [| lia | rewrite length_N_to_le_bytes; cbn; lia | intros a Ha; rewrite length_N_to_le_bytes in Ha; cbn in Ha; unfold zwin; lia]
                        | apply stores_in_wbytes; [lia | rewrite length_N_to_le_bytes; cbn; lia | intros a Ha; rewrite length_N_to_le_bytes in Ha; cbn in Ha; unfold zwin; lia] ]).
          apply stores_in_refl. }
        assert (ST3f : stores_in (fun a => zwin (sp - 112) sp a \/ zwin v (v + 24) a \/ zwin p (p + 4 * n) a) M3 Mf).
        { eapply stores_in_trans; [eapply stores_in_weaken; [exact ST3z|] | eapply stores_in_weaken; [exact STzf|]]; intros a Ha; unfold zwin in *; lia. }
        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { eapply msteps_trans; [exact RUN3|]. fold M4. eapply msteps_trans; [exact RUN4|]. exact RUN5. }
        eapply (CONT A1 _ Mf model1 p).
        * constructor.
          -- eapply (stores_in_ainv SEGS Ly.L MI); [exact AI1 | exact ST3f |].
             intros a [Ha|[Ha|Ha]]; [apply WIN1 | apply HDR1 | apply Hpown]; unfold zwin in Ha; lia.
          -- exact MS1. -- exact Hfs1. -- exact Hfds1.
          -- eapply (stores_in_sx SEGS Ly.L ST); [exact SX1 | exact ST3f |].
             intros a Ha. assert (Hni : ~ in_ranges [(0x10000, 0x124000)] a)
               by (destruct Ha as [Ha|[Ha|Ha]]; [apply WIN1 | apply HDR1 | apply Hpown]; unfold zwin in Ha; lia).
             destruct (offimg_sep a Hni) as (X1 & X2 & _). split; assumption.
          -- intros r Hr. pose proof Hr as Hr'. unfold callee_saved in Hr.
             repeat (destruct Hr as [<-|Hr]; [first [ rewrite G'_1; symmetry; exact Hra | rewrite G'_2; symmetry; exact Hsp | exact G'_8 | exact G'_9 | exact G'_18
               | rewrite G'S by (first [solve [clear; cbv; tauto] | cbv; tauto]); rewrite G4S by (intros HH; inversion HH); rewrite G3S by (first [solve [clear; cbv; tauto] | cbv; tauto]); rewrite (KEPT2 _ Hr'); first [exact Rn3 | exact Rn4 | apply RnS; (first [solve [clear; cbv; tauto] | cbv; tauto])] ] |]).
             destruct Hr.
        * unfold CRep.vec32. rewrite Zlen_repeat by lia.
          split; [exact Hv0|]. split; [exact Hv1|]. split; [eapply stores_in_mdef; [exact STzf | eapply stores_in_mdef; [exact ST3z | exact HDv3]] |].
          split; [lia|]. split; [right; repeat split; try assumption; try lia|].
          split. { unfold fld, Mf, MCf. cbv zeta. rdWa v. }
          split. { unfold fld, Mf, MCf. cbv zeta. rdWa (v + 8). }
          split. { unfold fld, Mf, MCf. cbv zeta. rdWa (v + 16). }
          intros i Hi. rewrite Znth_repeat by lia. split; [lia|].
          eapply fld_agree; [lia | cbn; lia | apply FJ; lia |].
          eapply stores_in_agree; [exact STzf|]. intros a Ha. unfold zwin in *. cbn in Ha. split; lia.
        * right. split; [lia|]. cbn. exists (live MI A1). split; [exact LADD | reflexivity].
        * eapply eff_weaken.
          -- eapply (eff_trans MI); [ | | intros a Ha; apply WIN1; unfold W_of in Ha; cbn in Ha; lia].
             ++ eapply (eff_trans MI); [ | | intros a Ha; apply WIN1; unfold W_of in Ha; cbn in Ha; lia].
                ** apply (eff_store MI A M M2 _ (fun a => zwin v (v + 24) a \/ (0 < n /\ zwin p (p + 4 * n) a))); [| exact (proj2 ST2)].
                   intros a HF HW. apply (proj1 ST2). intros Hz. apply HW. unfold W_of, zwin in *. cbn. lia.
                ** eapply (eff_of_new MI A A1 M2 M3 model1 _ (fun a => zwin v (v + 24) a \/ (0 < n /\ zwin p (p + 4 * n) a)) p (4 * n)); try eassumption.
                   --- intros a Ha. unfold W_of, zwin in *. cbn. lia.
                   --- intros a Ha. right. split; [lia|]. unfold zwin. lia.
             ++ apply (eff_store MI A1 M3 Mf _ (fun a => zwin v (v + 24) a \/ (0 < n /\ zwin p (p + 4 * n) a))); [| exact (proj2 ST3f)].
                intros a HF HW. apply (proj1 ST3f). intros [Hz|[Hz|Hz]].
                ** apply HW. unfold W_of, zwin in *. cbn. lia.
                ** apply HF. left. exact Hz.
                ** apply HF. right. split; [lia | exact Hz].
          -- intros a [[H|H]|H]; exact H.
  Qed.
End Resize.
