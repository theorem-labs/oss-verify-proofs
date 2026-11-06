(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require SFModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require SoftFloat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require G_letf2.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgAt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgNot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require JunkAbs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require F_sf_helpers2.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgNotJ.
Module G_frexpl.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SFModel.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec.SoftFloat OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec.FmtFp.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.SFW1_lemmas.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G.G_letf2.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac. Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgNot.   
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.F_sf_helpers2.SF_buildtac. Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgNotJ.

(* [comment removed for export] *)
Definition frexpl_prog (B K_10438 B_letf2 B_1af98 B_1b3d0 : Z) : RStep.ptree :=
  PNode 108%Z
  (PNode 52%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 4064 4
        (PJ_Store_SZ8_nnn 4 2 1 24 4
        (PJ_Store_SZ8_nnn 8 2 8 16 4
        (PJ_Store_SZ8_nnn 12 2 9 8 4
        (PJ_Store_SZ8_nnn 16 2 18 0 4
        (PJ_OpImm_ALU_ADD_nnn 20 8 12 0 4
        (PJ_ShiftImm_ALU_SRL_nnn 24 13 11 48 4
        (PJ_Lui_nn 28 12 8 4
        (PJ_OpImm32_nnn 32 14 12 4095 4
        (PJ_Op_ALU_AND_nnn 36 12 13 14 4
        (PJ_Branch_BC_EQ_nnn 40 12 14 152 4
        (PJ_Branch_BC_NE_nnn 44 12 0 80 4
        (PJ_OpImm_ALU_ADD_nnn 48 9 10 0 4 nil))))))))))))))
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 52 18 11 0 4
        (PJ_OpImm_ALU_ADD_nnn 56 13 0 0 4
        (PJ_Jal_nt 60 1 (jimm21 (B_letf2 - (B + 60))) 4
        (PJ_Branch_BC_EQ_nnn 64 10 0 116 4
        (PJ_Auipc_nt 68 10 (hi20 (K_10438 - (B + 68))) 4
        (PJ_FLoad_FMT_D_nnt 72 10 10 (lo12 (K_10438 - (B + 68))) 4
        (PJ_Jal_nt 76 1 (jimm21 (B_1af98 - (B + 76))) 4
        (PJ_OpImm_ALU_ADD_nnn 80 12 10 0 4
        (PJ_OpImm_ALU_ADD_nnn 84 13 11 0 4
        (PJ_OpImm_ALU_ADD_nnn 88 10 9 0 4
        (PJ_OpImm_ALU_ADD_nnn 92 11 18 0 4
        (PJ_Jal_nt 96 1 (jimm21 (B_1b3d0 - (B + 96))) 4
        (PJ_OpImm_ALU_ADD_nnn 100 12 8 0 4
        (PJ_Jal_nn 104 1 2097048 4 nil))))))))))))))))
  (PNode 160%Z
    (PLeaf
        (PJ_Load_SZ4_true_nnn 108 12 8 0 4
        (PJ_OpImm_ALU_ADD_nnn 112 12 12 3976 4
        (PJ_Store_SZ4_nnn 116 8 12 0 4
        (PJ_Jal_nn 120 0 72 4
        (PJ_Lui_nn 124 14 8 4
        (PJ_Op_ALU_AND_nnn 128 13 13 14 4
        (PJ_Lui_nn 132 14 1048572 4
        (PJ_ShiftImm_ALU_SLL_nnn 136 11 11 16 4
        (PJ_OpImm_ALU_ADD_nnn 140 14 14 2 4
        (PJ_Op_ALU_ADD_nnn 144 12 12 14 4
        (PJ_Lui_nn 148 14 8191 4
        (PJ_ShiftImm_ALU_SRL_nnn 152 11 11 16 4
        (PJ_ShiftImm_ALU_SLL_nnn 156 14 14 37 4 nil))))))))))))))
    (PLeaf
        (PJ_ShiftImm_ALU_SLL_nnn 160 13 13 48 4
        (PJ_Op_ALU_OR_nnn 164 11 11 14 4
        (PJ_Store_SZ4_nnn 168 8 12 0 4
        (PJ_Op_ALU_OR_nnn 172 11 13 11 4
        (PJ_Jal_nn 176 0 16 4
        (PJ_OpImm_ALU_ADD_nnn 180 10 9 0 4
        (PJ_OpImm_ALU_ADD_nnn 184 11 18 0 4
        (PJ_Store_SZ4_nnn 188 8 0 0 4
        (PJ_Load_SZ8_true_nnn 192 1 2 24 4
        (PJ_Load_SZ8_true_nnn 196 8 2 16 4
        (PJ_Load_SZ8_true_nnn 200 9 2 8 4
        (PJ_Load_SZ8_true_nnn 204 18 2 0 4
        (PJ_OpImm_ALU_ADD_nnn 208 2 2 32 4
        (PJ_Jalr_nnn 212 0 1 0 4 nil)))))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_frexpl (IMG : RImg) := frexpl_prog (sym 0x1b174) (sym 0x10438) (sym 0x1b24c) (sym 0x1af98) (sym 0x1b3d0).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_frexpl : CodeAtT img_segs (sym 0x1b174) (PROGAT_CODE_frexpl IMG)}.
  Context {RB_frexpl : RelCode (sym 0x1b174) 216}.
  Context {RO_10438 : RoB img_segs (sym 0x10438) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 112; BV 8 71])}.
  Context {RN_B_letf2_1b174 : RelNear (sym 0x1b174) (sym 0x1b24c)}.
  Context {RN_B_1af98_1b174 : RelNear (sym 0x1b174) (sym 0x1af98)}.
  Context {RN_B_1b3d0_1b174 : RelNear (sym 0x1b174) (sym 0x1b3d0)}.
  Context {RS_K_10438 : RelSym (sym 0x10438)}.
  Context {SPEC_letf2 : letf2_contract}.
  Collection ImgHyps := IMG CODE_frexpl RB_frexpl RO_10438 RN_B_letf2_1b174 RN_B_1af98_1b174 RN_B_1b3d0_1b174 RS_K_10438 SPEC_letf2.


(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)

Definition frexpl_entry := (sym 0x1b174)%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Lemma frexpl_unfold : forall n x e,
  frexpl (S n) x e =
   (let hi := hi64 x in
    let se := Z.shiftr hi 48 in
    let ee := Z.land se 0x7fff in
    if ee =? 0 then
      if negb (f128_le x F128_ZERO =? 0) then
        let k := f128_of_d D_0x1p120 in
        match frexpl n (f128_mul x k) e with Some (x, e) => Some (x, e - 120) | None => None end
      else Some (x, 0)
    else if ee =? 0x7fff then Some (x, e)
    else
      let e := ee - 0x3ffe in
      let hi := Z.lor (Z.lor (Z.land hi 0x8000000000000000) (Z.land hi 0x0000ffffffffffff)) 0x3ffe000000000000 in
      Some (mk128 hi (lo64 x), e))%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition frexpl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P x E : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (P, P + 4)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - 32) (bv_unsigned sp)
    /\ rw_cells img_segs m' P [C4 (Z_to_bv 64 e')]
    /\ frexpl FREXPL_FUEL x E = Some (x', e').

(* [comment removed for export] *)
Lemma frx_mant : forall h, (0 <= h < 2^64)%Z ->
  Z.shiftr (Z.land (Z.shiftl h 16) 18446744073709551615) 16 = Z.land h 281474976710655.
Proof.
  intros h Hh. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec, Z.land_spec, Z.land_spec by lia.
  change 18446744073709551615%Z with (Z.ones 64). change 281474976710655%Z with (Z.ones 48).
  destruct (Z.lt_ge_cases i 48).
  - rewrite Z.shiftl_spec, !Z.ones_spec_low by lia. rewrite !Bool.andb_true_r. f_equal. lia.
  - rewrite (Z.ones_spec_high 64), (Z.ones_spec_high 48) by lia. now rewrite !Bool.andb_false_r.
Qed.
Lemma frx_sign : forall h, (0 <= h < 2^64)%Z ->
  Z.land (Z.shiftl (Z.land (Z.shiftr h 48) 32768) 48) 18446744073709551615 = Z.land h 9223372036854775808.
Proof.
  intros h Hh. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.land_spec. change 18446744073709551615%Z with (Z.ones 64).
  change 32768%Z with (2^15)%Z. change 9223372036854775808%Z with (2^63)%Z.
  rewrite (Z.pow2_bits_eqb 63) by lia.
  destruct (Z.lt_ge_cases i 48).
  - rewrite Z.shiftl_spec_low by lia. destruct (Z.eqb_spec 63 i); [lia|]. now rewrite Bool.andb_false_r.
  - rewrite Z.shiftl_spec_high, Z.land_spec, Z.shiftr_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.ones_spec_low by lia. replace (i - 48 + 48)%Z with i by lia.
      destruct (Z.eqb_spec 15 (i - 48)), (Z.eqb_spec 63 i); try lia; now rewrite ?Bool.andb_true_r, ?Bool.andb_false_r.
    + rewrite Z.ones_spec_high by lia. destruct (Z.eqb_spec 63 i); [lia|]. now rewrite !Bool.andb_false_r.
Qed.

Ltac frx_finish X E' :=
  apply evt_done; unfold frexpl_post; exists X, E';
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [ rewrite ?lo64_mk128, ?hi64_mk128 by zrange; rewrite ?lo64_words, ?hi64_words by lia; ms_eq
         | repeat match goal with |- _ /\ _ => split end; try assumption ].

(* [comment removed for export] *)
Lemma f128_le_cases : forall a b, (f128_le a b = -1 \/ f128_le a b = 0 \/ f128_le a b = 1)%Z.
Proof.
  intros a b. unfold f128_le, nez64. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; try lia.
  all: destruct (Z.eqb _ 0); cbn; lia.
Qed.
Lemma f128_le_land64_zero : forall a b, Z.land (f128_le a b) 18446744073709551615 = 0%Z <-> f128_le a b = 0%Z.
Proof.
  intros a b. destruct (f128_le_cases a b) as [E|[E|E]]; rewrite E; vm_compute; split; intros; lia.
Qed.

Lemma frexpl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (E : Z),
  stk img_segs m (bv_unsigned sp - 32) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  rw_cells img_segs m (bv_unsigned a2) [C4 (Z_to_bv 64 E)] ->
  (bv_unsigned a2 + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  (32 <= bv_unsigned sp)%Z ->
  (let x := (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z in
   Z.land (Z.shiftr (hi64 x) 48) 0x7fff <> 0%Z \/ f128_le x F128_ZERO = 0%Z) ->
  evt img_segs (frexpl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a2) (bv_unsigned a0 + 2^64 * bv_unsigned a1) E m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b174)) fc None m (seg_rom img_segs)).
Proof.
  intros until E. intros ST MI CE SEP SPLO PRE.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 4)]%Z m) as MU.
  pose proof (wmono_refl img_segs m) as WM. pose_word_ranges.
  (* [comment removed for export] *)
  set (P := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 P) by (unfold P; rewrite Z_to_bv_bv_unsigned; reflexivity).
  cbv zeta in PRE. rewrite hi64_words in PRE by lia.
  unfold frexpl_post. change FREXPL_FUEL with 2%nat. rewrite frexpl_unfold.
  rewrite hi64_words, lo64_words by lia. cbv zeta.
  carve_frame 32%nat ST.
  do 6 zstep. do 4 zstep. name_reg 12%Z ee.
  zstep. if_cases Ki; zify_cond Ki; decide_test1_try (ee =? 0%Z)%Z; decide_test1_try (ee =? 32767%Z)%Z.
  - (* [comment removed for export] *)
    do 6 zstep. release_frame FR ST (bv_unsigned sp).
    frx_finish (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z E. decide_tests_b. reflexivity.
  - zstep. if_cases Kz; zify_cond Kz; decide_test1 (ee =? 0%Z)%Z.
    + (* [comment removed for export] *)
      do 7 zstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 (Z.shiftl (Z.land (Z.shiftr (bv_unsigned a1) 48) 32768) 48)) with (Z_to_bv 64 (Z.land (bv_unsigned a1) 9223372036854775808))
        by (rewrite <- (Z_to_bv_land64 (Z.shiftl _ 48)); f_equal; symmetry; apply frx_sign; lia).
      zstep. zstep. zstep. reg_rewrite 11%Z Z.lor_assoc.
      zstep. do 6 zstep. release_frame FR ST (bv_unsigned sp).
      frx_finish (mk128 (Z.lor (Z.lor (Z.land (bv_unsigned a1) 0x8000000000000000) (Z.land (bv_unsigned a1) 0x0000ffffffffffff)) 0x3ffe000000000000) (bv_unsigned a0))%Z (ee - 16382)%Z.
      decide_tests_b. reflexivity.
    + (* [comment removed for export] *)
      do 3 zstep. zstep. call SPEC_letf2. 1:{ assumption. }
      zsimp. rewrite Kz. rewrite Z.mul_0_r, Z.add_0_r.
      zstep. if_cases Kl; zify_cond Kl; rewrite f128_le_land64_zero in Kl.
      * (* [comment removed for export] *) do 3 zstep. do 6 zstep. release_frame FR ST (bv_unsigned sp).
        frx_finish (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z 0%Z. decide_tests_b. unfold F128_ZERO. rewrite Kl. reflexivity.
      * exfalso. unfold F128_ZERO in PRE. change (2^64)%Z with 18446744073709551616%Z in PRE.
        destruct PRE as [PRE|PRE]; [exact (PRE Kz)|]. rewrite PRE in Kl. exact (Kl eq_refl).
Qed.

(* [comment removed for export] *)
Definition frexpl_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (E : Z),
  stk img_segs m (bv_unsigned sp - 32) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  rw_cells img_segs m (bv_unsigned a2) [C4 (Z_to_bv 64 E)] ->
  (bv_unsigned a2 + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  (32 <= bv_unsigned sp)%Z ->
  (let x := (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z in
   Z.land (Z.shiftr (hi64 x) 48) 0x7fff <> 0%Z \/ f128_le x F128_ZERO = 0%Z) ->
  evt img_segs (frexpl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a2) (bv_unsigned a0 + 2^64 * bv_unsigned a1) E m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b174)) fc None m (seg_rom img_segs)).
Lemma frexpl_contract_ok : frexpl_contract.
Proof. exact frexpl_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.
Ltac frx_finish X E' :=
  apply evt_done; unfold frexpl_post; exists X, E';
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [ rewrite ?lo64_mk128, ?hi64_mk128 by zrange; rewrite ?lo64_words, ?hi64_words by lia; ms_eq
         | repeat match goal with |- _ /\ _ => split end; try assumption ].

(* [comment removed for export] *)
Existing Class frexpl_contract.
End G_frexpl.

(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require FmtFp_splitR.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require NElim.
Module G_FmtFp_facts.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec.Prelim OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec.SoftFloat OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec.FmtFp.
Import G_frexpl.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.FmtFp_splitR.FmtFp_split.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.NElim.  
Import ListNotations.
Local Open Scope Z_scope.


(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Collection ImgHyps := IMG.



Lemma land15_bound : forall a, 0 <= Z.land a 32767 <= 32767.
Proof.
  intros a. change 32767 with (Z.ones 15). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound a (2^15) ltac:(lia)). change (Z.ones 15) with (2^15 - 1). lia.
Qed.

(* [comment removed for export] *)
Lemma frexpl_e_range : forall x x' e', frexpl FREXPL_FUEL x 0 = Some (x', e') -> -16501 <= e' <= 16384.
Proof.
  intros x x' e' H. change FREXPL_FUEL with 2%nat in H. rewrite frexpl_unfold in H. cbv zeta in H.
  pose proof (land15_bound (Z.shiftr (hi64 x) 48)) as U1.
  destruct (Z.eqb_spec (Z.land (Z.shiftr (hi64 x) 48) 32767) 0) as [E0|E0].
  - destruct (negb _).
    + rewrite frexpl_unfold in H. cbv zeta in H.
      set (x2 := f128_mul x (f128_of_d D_0x1p120)) in H.
      pose proof (land15_bound (Z.shiftr (hi64 x2) 48)) as U2.
      destruct (Z.eqb_spec (Z.land (Z.shiftr (hi64 x2) 48) 32767) 0) as [E2|E2].
      * destruct (negb _); [discriminate H|]. inversion H; subst. lia.
      * destruct (Z.eqb_spec (Z.land (Z.shiftr (hi64 x2) 48) 32767) 32767); inversion H; subst; lia.
    + inversion H; subst. lia.
  - destruct (Z.eqb_spec (Z.land (Z.shiftr (hi64 x) 48) 32767) 32767); inversion H; subst; lia.
Qed.

(* [comment removed for export] *)
Lemma lxor_signbit_range : forall y, 0 <= y < 2^128 -> 0 <= Z.lxor y F128_SIGNBIT < 2^128.
Proof.
  intros y Hy. unfold F128_SIGNBIT. change 0x80000000000000000000000000000000 with (2^127).
  split. { apply Z.lxor_nonneg. lia. }
  destruct (Z.eq_dec (Z.lxor y (2^127)) 0) as [->|NZ]; [lia|].
  apply Z.log2_lt_pow2. { pose proof (Z.lxor_nonneg y (2^127)). lia. }
  eapply Z.le_lt_trans. { apply Z.log2_lxor; lia. }
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec y 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - rewrite Z.log2_pow2 by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fmt_fp_dig_step : forall k big z y,
  fmt_fp_dig (S k) (big, z, y) =
   (let zv := f128_to_u32 y in
    let y' := f128_mul (f128_of_i32 1000000000) (f128_sub y (f128_of_u32 zv)) in
    if negb (f128_le y' F128_ZERO =? 0) then fmt_fp_dig k (zupd big z zv, z + 1, y')
    else Some (zupd big z zv, z + 1, y')).
Proof. reflexivity. Qed.

Lemma fmt_fp_dig_z : forall k big z y big' z' y',
  fmt_fp_dig k (big, z, y) = Some (big', z', y') -> z < z' /\ length big' = length big.
Proof.
  induction k as [|k IH]; intros big z y big' z' y' H; [discriminate H|].
  rewrite fmt_fp_dig_step in H. cbv zeta in H.
  destruct (negb _).
  - apply IH in H. rewrite zupd_length in H. lia.
  - set (v := f128_to_u32 y) in H. clearbody v. set (y2 := f128_mul _ _) in H. clearbody y2.
    injection H as <- <- <-. rewrite zupd_length. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fmt_fp_strip_step : forall k big a z,
  fmt_fp_strip (S k) big a z = (if (a <? z) && (znth big (z - 1) =? 0) then fmt_fp_strip k big a (z - 1) else Some z).
Proof. reflexivity. Qed.
Lemma fmt_fp_strip_res : forall k big a z z', fmt_fp_strip k big a z = Some z' -> (a <= z)%Z -> a <= z' <= z.
Proof.
  induction k as [|k IH]; intros big a z z' H Haz; [discriminate H|].
  rewrite fmt_fp_strip_step in H. destruct (Z.ltb_spec0 a z); cbn [andb] in H.
  - destruct (znth big (z - 1) =? 0). { apply IH in H; lia. } inversion H; lia.
  - inversion H; lia.
Qed.

Lemma fmt_fp_up_inner_step : forall sh k a big d c,
  fmt_fp_up_inner sh (S k) a (big, d, c) =
   (if a <=? d then
      let x := Z.shiftl (znth big d) sh + c in
      fmt_fp_up_inner sh k a (zupd big d (x mod 1000000000), d - 1, u32 (x / 1000000000))
    else Some (big, d, c)).
Proof. reflexivity. Qed.
Lemma fmt_fp_up_inner_res : forall sh k a big d c big' d' c',
  fmt_fp_up_inner sh k a (big, d, c) = Some (big', d', c') -> (a - 1 <= d)%Z -> d' = a - 1 /\ length big' = length big.
Proof.
  induction k as [|k IH]; intros a big d c big' d' c' H Hd; [discriminate H|].
  rewrite fmt_fp_up_inner_step in H. destruct (Z.leb_spec0 a d).
  - cbv zeta in H. apply IH in H; [|lia]. rewrite zupd_length in H. exact H.
  - inversion H; subst. lia.
Qed.

Lemma fmt_fp_up_step : forall k big a z e2,
  fmt_fp_up (S k) (big, a, z, e2) =
    (if 0 <? e2 then match fmt_fp_up_body (big, a, z, e2) with Some s => fmt_fp_up k s | None => None end
     else Some (big, a, z, e2)).
Proof. reflexivity. Qed.

Lemma fmt_fp_up_nonneg : forall k big a z e2 big' a' z' e2',
  fmt_fp_up k (big, a, z, e2) = Some (big', a', z', e2') -> (0 <= e2)%Z -> e2' = 0%Z.
Proof.
  induction k as [|k IH]; intros big a z e2 big' a' z' e2' H He; [discriminate H|].
  rewrite fmt_fp_up_step in H. destruct (Z.ltb_spec0 0 e2).
  - unfold fmt_fp_up_body in H.
    destruct (fmt_fp_up_inner _ _ _ _) as [[[b1 d1] c1]|]; [|discriminate H].
    destruct (negb (c1 =? 0)).
    + destruct (fmt_fp_strip _ _ _ _) as [z1|]; [|discriminate H]. apply IH in H; lia.
    + destruct (fmt_fp_strip _ _ _ _) as [z1|]; [|discriminate H]. apply IH in H; lia.
  - inversion H; subst. lia.
Qed.

Lemma znth_over : forall l i, (length l <= Z.to_nat i)%nat -> znth l i = 0%Z.
Proof.
  intros l i H. unfold znth. destruct (i <? 0); [reflexivity|]. apply nth_overflow. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fmt_fp_dn_step : forall k p t r big a z e2,
  fmt_fp_dn (S k) p t r (big, a, z, e2) =
    (if e2 <? 0 then match fmt_fp_dn_body p t r (big, a, z, e2) with Some s => fmt_fp_dn k p t r s | None => None end
     else Some (big, a, z, e2)).
Proof. reflexivity. Qed.

Lemma fmt_fp_dn_inner_step : forall sh k z big d c,
  fmt_fp_dn_inner sh (S k) z (big, d, c) =
   (if d <? z then
      fmt_fp_dn_inner sh k z (zupd big d (u32 (Z.shiftr (znth big d) sh + c)), d + 1,
                              u32 (Z.shiftr 1000000000 sh * Z.land (znth big d) (Z.shiftl 1 sh - 1)))
    else Some (big, d, c)).
Proof. reflexivity. Qed.

Lemma fmt_fp_dn_inner_res : forall sh k z big d c big' d' c',
  fmt_fp_dn_inner sh k z (big, d, c) = Some (big', d', c') -> (d <= z)%Z ->
  d' = z /\ length big' = length big /\ ((0 <= c)%Z -> (0 <= c')%Z)
  /\ (forall i, (i < d \/ z <= i)%Z -> znth big' i = znth big i).
Proof.
  induction k as [|k IH]; intros z big d c big' d' c' H Hd; [discriminate H|].
  rewrite fmt_fp_dn_inner_step in H. destruct (Z.ltb_spec0 d z).
  - apply IH in H; [|lia]. rewrite zupd_length in H. (nelim H 4%nat; intros H1 H2 H3 H4).
    split; [exact H1|]. split; [exact H2|]. split.
    + intros _. apply H3. unfold u32. apply Z.mod_pos_bound. lia.
    + intros i Hi. rewrite H4 by lia. apply znth_zupd_neq. lia.
  - inversion H; subst. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
Fixpoint fmt_fp_dn_iter (n : nat) (p t r : Z) (s : list Z * Z * Z * Z) {struct n} : option (list Z * Z * Z * Z) :=
  match n with
  | O => Some s
  | S n' => let '(big, a, z, e2) := s in
            if e2 <? 0 then match fmt_fp_dn_body p t r s with Some s' => fmt_fp_dn_iter n' p t r s' | None => None end
            else None
  end.

(* [comment removed for export] *)
Definition dn_ok (s : list Z * Z * Z * Z) : Prop :=
  let '(big, a, z, e2) := s in (a <= z <= 127)%Z /\ (a = z -> znth big a <> 0%Z).

Definition dn_good (p t r : Z) (s : list Z * Z * Z * Z) : Prop :=
  forall n big a z e2, fmt_fp_dn_iter n p t r s = Some (big, a, z, e2) -> (e2 < 0)%Z -> dn_ok (big, a, z, e2).

Lemma dn_good_now : forall p t r big a z e2, dn_good p t r (big, a, z, e2) -> (e2 < 0)%Z -> dn_ok (big, a, z, e2).
Proof. intros p t r big a z e2 G He. exact (G O big a z e2 eq_refl He). Qed.

Lemma dn_good_next : forall p t r big a z e2 s', dn_good p t r (big, a, z, e2) -> (e2 < 0)%Z ->
  fmt_fp_dn_body p t r (big, a, z, e2) = Some s' -> dn_good p t r s'.
Proof.
  intros p t r big a z e2 s' G He HB n big1 a1 z1 e21 Hn He1.
  apply (G (S n) big1 a1 z1 e21); [|exact He1]. cbn [fmt_fp_dn_iter].
  rewrite (proj2 (Z.ltb_lt e2 0) He). rewrite HB. exact Hn.
Qed.

Lemma fmt_fp_dn_iter_end : forall k n p t r s s1 s2,
  fmt_fp_dn_iter n p t r s = Some s1 -> fmt_fp_dn k p t r s1 = Some s2 -> fmt_fp_dn (n + k) p t r s = Some s2.
Proof.
  induction n as [|n IH]; intros p t r s s1 s2 Hn Hk.
  - cbn in Hn. inversion Hn; subst. exact Hk.
  - cbn [fmt_fp_dn_iter] in Hn. destruct s as [[[big a] z] e2].
    destruct (e2 <? 0) eqn:E; [|discriminate Hn].
    destruct (fmt_fp_dn_body p t r (big, a, z, e2)) as [s'|] eqn:HB; [|discriminate Hn].
    cbn [Nat.add]. rewrite fmt_fp_dn_step, E, HB. eapply IH; eauto.
Qed.

Lemma fmt_fp_dn_more : forall k k' p t r s s2,
  fmt_fp_dn k p t r s = Some s2 -> fmt_fp_dn (k + k') p t r s = Some s2.
Proof.
  induction k as [|k IH]; intros k' p t r s s2 H; [discriminate H|].
  cbn [Nat.add]. destruct s as [[[big a] z] e2]. rewrite fmt_fp_dn_step in H |- *.
  destruct (e2 <? 0); [|exact H].
  destruct (fmt_fp_dn_body p t r (big, a, z, e2)) as [s'|]; [|discriminate H]. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Definition dn_a1 (bigI : list Z) (a : Z) : Z := if znth bigI a =? 0 then a + 1 else a.
Definition dn_bz (bigI : list Z) (z cI : Z) : list Z * Z := if negb (cI =? 0) then (zupd bigI z cI, z + 1) else (bigI, z).
Definition dn_zf (t r need a1 z1 : Z) : Z :=
  let b := if Z.lor t 32 =? CHR_f then r else a1 in if need <? z1 - b then b + need else z1.

Lemma fmt_fp_dn_body_some : forall p t r big a z e2 s1,
  fmt_fp_dn_body p t r (big, a, z, e2) = Some s1 ->
  exists bigI dI cI, fmt_fp_dn_inner (Z.min 9 (- e2)) BIG_FUEL z (big, a, 0) = Some (bigI, dI, cI) /\
    s1 = (fst (dn_bz bigI z cI), dn_a1 bigI a,
          dn_zf t r (1 + u32 (p + LDBL_MANT_DIG / 3 + 8) / 9) (dn_a1 bigI a) (snd (dn_bz bigI z cI)),
          (e2 + Z.min 9 (- e2))%Z).
Proof.
  intros p t r big a z e2 s1 H. unfold fmt_fp_dn_body in H.
  destruct (fmt_fp_dn_inner (Z.min 9 (- e2)) BIG_FUEL z (big, a, 0)) as [[[bigI dI] cI]|] eqn:HI; [|discriminate H].
  exists bigI, dI, cI. split; [reflexivity|].
  unfold dn_bz, dn_a1, dn_zf. cbv beta iota zeta in H.
  destruct (negb (cI =? 0)); cbv beta iota zeta in H; cbv beta iota zeta; injection H as E; subst s1; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zero_from (big : list Z) (z : Z) : Prop := forall i, (z <= i)%Z -> znth big i = 0%Z.

Lemma zero_from_zrepeat : forall n z, (0 <= z)%Z -> zero_from (zrepeat 0 n) z.
Proof.
  intros n z Hz i Hi. unfold znth, zrepeat. destruct (i <? 0); [reflexivity|].
  destruct (nth_in_or_default (Z.to_nat i) (repeat 0%Z (Z.to_nat n)) 0%Z) as [H|H]; [|exact H].
  apply repeat_spec in H. exact H.
Qed.

Lemma fmt_fp_dig_zero : forall k big z y big' z' y',
  fmt_fp_dig k (big, z, y) = Some (big', z', y') -> (0 <= z)%Z -> zero_from big z -> zero_from big' z'.
Proof.
  induction k as [|k IH]; intros big z y big' z' y' H Hz ZF; [discriminate H|].
  rewrite fmt_fp_dig_step in H. cbv zeta in H.
  set (v := f128_to_u32 y) in H. clearbody v. set (y2 := f128_mul _ _) in H. clearbody y2.
  assert (ZF' : zero_from (zupd big z v) (z + 1)).
  { intros i Hi. rewrite znth_zupd_neq by lia. apply ZF. lia. }
  destruct (negb _).
  - eapply IH; [exact H | lia | exact ZF'].
  - injection H as <- <- <-. exact ZF'.
Qed.

Lemma fmt_fp_strip_zeros : forall k big a z z', fmt_fp_strip k big a z = Some z' ->
  forall i, (z' <= i < z)%Z -> znth big i = 0%Z.
Proof.
  induction k as [|k IH]; intros big a z z' H i Hi; [discriminate H|].
  rewrite fmt_fp_strip_step in H. destruct (Z.ltb_spec0 a z); cbn [andb] in H.
  - destruct (Z.eqb_spec (znth big (z - 1)) 0).
    + destruct (Z.eq_dec i (z - 1)) as [->|Hne]; [assumption|]. eapply IH; [exact H|]. lia.
    + injection H as <-. lia.
  - injection H as <-. lia.
Qed.

Lemma fmt_fp_up_inner_same : forall sh k a big d c big' d' c',
  fmt_fp_up_inner sh k a (big, d, c) = Some (big', d', c') ->
  (forall i, (d < i)%Z -> znth big' i = znth big i) /\ (c' <> c -> (a <= d)%Z).
Proof.
  induction k as [|k IH]; intros a big d c big' d' c' H; [discriminate H|].
  rewrite fmt_fp_up_inner_step in H. destruct (Z.leb_spec0 a d).
  - cbv zeta in H. apply IH in H. destruct H as [H _]. split; [|lia].
    intros i Hi. rewrite H by lia. apply znth_zupd_neq. lia.
  - injection H as <- <- <-. split; [reflexivity | intros X; exfalso; exact (X eq_refl)].
Qed.

Lemma fmt_fp_up_zero : forall k big a z e2 big' a' z' e2',
  fmt_fp_up k (big, a, z, e2) = Some (big', a', z', e2') -> zero_from big z -> zero_from big' z'.
Proof.
  induction k as [|k IH]; intros big a z e2 big' a' z' e2' H ZF; [discriminate H|].
  rewrite fmt_fp_up_step in H. destruct (0 <? e2).
  - unfold fmt_fp_up_body in H.
    destruct (fmt_fp_up_inner (Z.min 29 e2) BIG_FUEL a (big, z - 1, 0)) as [[[b1 d1] c1]|] eqn:HI; [|discriminate H].
    pose proof (fmt_fp_up_inner_same _ _ _ _ _ _ _ _ _ HI) as [SAME Hc1].
    assert (ZF1 : zero_from b1 z) by (intros i Hi; rewrite SAME by lia; apply ZF; lia).
    destruct (Z.eqb_spec c1 0); cbn [negb] in H.
    + destruct (fmt_fp_strip BIG_FUEL b1 a z) as [z1|] eqn:HS; [|discriminate H].
      eapply IH; [exact H|]. intros i Hi. destruct (Z.lt_ge_cases i z); [|apply ZF1; lia].
      eapply fmt_fp_strip_zeros; [exact HS | lia].
    + destruct (fmt_fp_strip BIG_FUEL (zupd b1 (a - 1) c1) (a - 1) z) as [z1|] eqn:HS; [|discriminate H].
      eapply IH; [exact H|]. intros i Hi. destruct (Z.lt_ge_cases i z).
      * eapply fmt_fp_strip_zeros; [exact HS | lia].
      * rewrite znth_zupd_neq by lia. apply ZF1. lia.
  - injection H as <- <- <- <-. exact ZF.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dig_words_fact (yv fl : Z) : Prop :=
  forall y1 fr e0 y e2 b' z' y',
    fst (fst (ffp_sign yv fl)) = y1 ->
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) ->
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z) ->
    fmt_fp_dig DIG_FUEL (zrepeat 0 128, (if e2 <? 0 then 0 else 122)%Z, y) = Some (b', z', y') ->
    (z' <= (if e2 <? 0 then 0 else 122) + 6)%Z.

(* [comment removed for export] *)
Definition e2_range_fact (yv fl : Z) : Prop :=
  forall y1 fr e0,
    fst (fst (ffp_sign yv fl)) = y1 ->
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) ->
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     let e2 := if ynz then e0 - 1 - 28 else e0 in
     -1102 <= e2 <= 1024)%Z.

(* [comment removed for export] *)
Definition dn_phase_fact (yv fl p t : Z) : Prop :=
  forall y1 fr e0 y e2 b' z' y' s,
    fst (fst (ffp_sign yv fl)) = y1 ->
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) ->
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z) ->
    fmt_fp_dig DIG_FUEL (zrepeat 0 128, (if e2 <? 0 then 0 else 122)%Z, y) = Some (b', z', y') ->
    fmt_fp_up UP_FUEL (b', (if e2 <? 0 then 0 else 122)%Z, z', e2) = Some s ->
    dn_good (if p <? 0 then 6 else p)%Z t (if e2 <? 0 then 0 else 122)%Z s.

End Img.
End G_FmtFp_facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Import Prelim SoftFloat FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require FmtFp_splitR.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.FmtFp_splitR.FmtFp_split.
Import G_FmtFp_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Local Open Scope Z_scope.


(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Collection ImgHyps := IMG.



(* [comment removed for export] *)
Definition run_to_dn (yv fl p t : Z) (p1 r0 : Z) (big : list Z) (a z : Z) : Prop :=
  exists y1 fr e0 y e2 b' z' y' s e2',
    fst (fst (ffp_sign yv fl)) = y1 /\
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) /\
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z) /\
    p1 = (if p <? 0 then 6 else p) /\ r0 = (if e2 <? 0 then 0 else 122) /\
    fmt_fp_dig DIG_FUEL (zrepeat 0 128, r0, y) = Some (b', z', y') /\
    fmt_fp_up UP_FUEL (b', r0, z', e2) = Some s /\
    fmt_fp_dn DN_FUEL p1 t r0 s = Some (big, a, z, e2').

(* [comment removed for export] *)
Definition words_all_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall i, 0 <= znth big i < 1000000000.

(* [comment removed for export] *)
Definition carry_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall e prefix pl bigR aR zR eR,
    ffp_e big a r0 z = Some e ->
    ffp_R t p1 prefix pl big a r0 z e (ffp_j t p1 e) = Some (bigR, aR, zR, eR) ->
    0 <= aR.

(* [comment removed for export] *)
Definition azr_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall e prefix pl bigR aR zR eR zS,
    ffp_e big a r0 z = Some e ->
    ffp_R t p1 prefix pl big a r0 z e (ffp_j t p1 e) = Some (bigR, aR, zR, eR) ->
    fmt_fp_strip BIG_FUEL bigR aR zR = Some zS ->
    Z.lor t 32 <> CHR_f -> zS <= aR -> aR = r0.

(* [comment removed for export] *)
Definition yn_fact (y : Z) : Prop :=
  Z.land (Z.shiftr (hi64 y) 48) 0x7fff <> 0 \/ f128_le y F128_ZERO = 0.

(* [comment removed for export] *)
Definition below_a_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall k, 0 <= k < a -> znth big k = 0.

End Img.
