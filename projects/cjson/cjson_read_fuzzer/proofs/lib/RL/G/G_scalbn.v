(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac.

(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
(* [comment removed for export] *)

Import ListNotations.

(* [comment removed for export] *)
Definition scalbn_prog (B K_10418 K_10430 : Z) : RStep.ptree :=
  PNode 76%Z
  (PNode 36%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 11 0 1024 4
        (PJ_Branch_BC_LT_nnn 4 10 11 52 4
        (PJ_Auipc_nt 8 11 (hi20 (K_10418 - (B + 8))) 4
        (PJ_FLoad_FMT_D_nnt 12 15 11 (lo12 (K_10418 - (B + 8))) 4
        (PJ_OpImm_ALU_ADD_nnn 16 11 0 2047 4
        (PJ_Fari_F_MUL_FMT_D_nnnn 20 10 10 15 7 4
        (PJ_Branch_BC_LTU_nnn 24 10 11 88 4
        (PJ_Lui_nn 28 11 1 4
        (PJ_OpImm32_nnn 32 11 11 3069 4 nil))))))))))
    (PLeaf
        (PJ_Branch_BC_LTU_nnn 36 10 11 8 4
        (PJ_OpImm_ALU_ADD_nnn 40 10 11 0 4
        (PJ_Fari_F_MUL_FMT_D_nnnn 44 10 10 15 7 4
        (PJ_OpImm_ALU_ADD_nnn 48 10 10 2050 4
        (PJ_Jal_nn 52 0 72 4
        (PJ_OpImm_ALU_ADD_nnn 56 11 0 3073 4
        (PJ_Branch_BC_LT_nnn 60 11 10 64 4
        (PJ_Auipc_nt 64 11 (hi20 (K_10430 - (B + 64))) 4
        (PJ_FLoad_FMT_D_nnt 68 15 11 (lo12 (K_10430 - (B + 64))) 4
        (PJ_OpImm_ALU_ADD_nnn 72 11 0 2104 4 nil))))))))))))
  (PNode 112%Z
    (PLeaf
        (PJ_Fari_F_MUL_FMT_D_nnnn 76 10 10 15 7 4
        (PJ_Branch_BC_LTU_nnn 80 11 10 40 4
        (PJ_Lui_nn 84 11 1048575 4
        (PJ_OpImm32_nnn 88 11 11 1136 4
        (PJ_Branch_BC_LTU_nnn 92 11 10 8 4
        (PJ_OpImm_ALU_ADD_nnn 96 10 11 0 4
        (PJ_Fari_F_MUL_FMT_D_nnnn 100 10 10 15 7 4
        (PJ_OpImm_ALU_ADD_nnn 104 10 10 1938 4
        (PJ_Jal_nn 108 0 16 4 nil))))))))))
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 112 10 10 3073 4
        (PJ_Jal_nn 116 0 8 4
        (PJ_OpImm_ALU_ADD_nnn 120 10 10 969 4
        (PJ_ShiftImm_ALU_SLL_nnn 124 10 10 52 4
        (PJ_OpImm_ALU_ADD_nnn 128 11 0 1023 4
        (PJ_ShiftImm_ALU_SLL_nnn 132 11 11 52 4
        (PJ_Op_ALU_ADD_nnn 136 10 10 11 4
        (PJ_Fmv_FMV_F_X_FMT_D_nn 140 15 10 4
        (PJ_Fari_F_MUL_FMT_D_nnnn 144 10 10 15 7 4
        (PJ_Jalr_nnn 148 0 1 0 4 nil)))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_scalbn (IMG : RImg) := scalbn_prog (sym 0x1bbd8) (sym 0x10418) (sym 0x10430).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_scalbn : CodeAtT img_segs (sym 0x1bbd8) (PROGAT_CODE_scalbn IMG)}.
  Context {RB_scalbn : RelCode (sym 0x1bbd8) 152}.
  Context {RO_10418 : RoB img_segs (sym 0x10418) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 224; BV 8 127])}.
  Context {RO_10430 : RoB img_segs (sym 0x10430) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 96; BV 8 3])}.
  Context {RS_K_10418 : RelSym (sym 0x10418)}.
  Context {RS_K_10430 : RelSym (sym 0x10430)}.
  Collection ImgHyps := IMG CODE_scalbn RB_scalbn RO_10418 RO_10430 RS_K_10418 RS_K_10430.


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition scalbn_entry := (sym 0x1bbd8)%Z.
Definition scalbn_tailpc := (sym 0x1bbd8 + 124)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition two_p1023 : word := Z_to_bv 64 0x7FE0000000000000.   (* [comment removed for export] *)
Definition two_m969  : word := Z_to_bv 64 0x0360000000000000.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition scalbn_u (n : Z) : word := Z_to_bv 64 (Z.shiftl (1023 + n) 52).

(* [comment removed for export] *)
Definition scalbn_reduce (x : word) (n : Z) : word * Z :=
  if (1023 <? n)%Z then
    let y := fmul_d RNE x two_p1023 in let n := (n - 1023)%Z in
    if (1023 <? n)%Z then
      let y := fmul_d RNE y two_p1023 in let n := (n - 1023)%Z in
      (y, if (1023 <? n)%Z then 1023%Z else n)
    else (y, n)
  else if (n <? -1022)%Z then
    let y := fmul_d RNE x two_m969 in let n := (n + 969)%Z in
    if (n <? -1022)%Z then
      let y := fmul_d RNE y two_m969 in let n := (n + 969)%Z in
      (y, if (n <? -1022)%Z then (-1022)%Z else n)
    else (y, n)
  else (x, n).

Definition scalbn_model (x : word) (n : Z) : word :=
  let (y, n') := scalbn_reduce x n in fmul_d RNE y (scalbn_u n').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition scalbn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (x : word) (n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (f15 : word) fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             (bvmap_set 10 (scalbn_model x n) (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ frm0 fc'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma word_signed_cases : forall a : word,
  ((0 <= bv_unsigned a < 2^63)%Z /\ bv_signed a = bv_unsigned a) \/
  ((2^63 <= bv_unsigned a < 2^64)%Z /\ bv_signed a = (bv_unsigned a - 2^64)%Z).
Proof.
  intros a. pose proof (bv_unsigned_in_range 64 a) as Hr. unfold bv_modulus in Hr.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ (Z.of_N 64 - 1))%Z with (2^63)%Z. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *.
  destruct (Z.lt_ge_cases (bv_unsigned a) (2^63)).
  - left. rewrite Z.mod_small by lia. lia.
  - right. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma scalbn_pack : forall (a : word) (n : Z),
  bv_signed a = n -> (-1023 <= n <= 1023)%Z ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned a) 52 + 4607182418800017408) = scalbn_u n.
Proof.
  intros a n Hn Hr. unfold scalbn_u. change 4607182418800017408%Z with (Z.shiftl 1023 52).
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 ?x = bv_wrap 64 ?y) with (x mod 2^64 = y mod 2^64)%Z.
  rewrite !Z.shiftl_mul_pow2 by lia.
  destruct (word_signed_cases a) as [[H1 H2]|[H1 H2]].
  - f_equal. lia.
  - replace (bv_unsigned a) with (n + 2^12 * 2^52)%Z by lia.
    rewrite Z.mul_add_distr_r. change (2^64)%Z with (2^12 * 2^52)%Z at 1.
    rewrite <- Z.add_assoc, (Z.add_comm (2^12 * 2^52 * 2^52)), Z.add_assoc.
    replace (2 ^ 12 * 2 ^ 52 * 2 ^ 52)%Z with ((2^52) * (2^12 * 2^52))%Z by lia.
    rewrite Z.mod_add by lia. change (2^12 * 2^52)%Z with (2^64)%Z. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma scalbn_tail : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (Ft : bvmap 5 word) fc (m : word -> option byte) (n' : Z) (Q : machine_state -> Prop),
  mem_inv img_segs m -> frm0 fc -> bv_signed a0 = n' -> (-1022 <= n' <= 1023)%Z ->
  (forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc',
     frm0 fc' ->
     Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           (bvmap_set 10 (fmul_d RNE (reg_get Ft 10) (scalbn_u n')) (bvmap_set 15 (scalbn_u n') Ft))
           (ret_pc ra) fc' None m (seg_rom img_segs))) ->
  evt img_segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 Ft (Z_to_bv 64 (sym 0x1bbd8 + 124)) fc None m (seg_rom img_segs)).
Proof.
  intros until Q. intros MI FRM Hn Hr HQ.
  do 4 step. rewrite (scalbn_pack a0 n' Hn) by lia.
  do 3 step.
  apply evt_done. apply HQ. exact FRM.
Qed.

Lemma signed_of_add : forall (a : word) (d n : Z),
  bv_signed a = n -> (-2^63 <= n + d < 2^63)%Z ->
  bv_signed (Z_to_bv 64 (bv_unsigned a + d)) = (n + d)%Z.
Proof.
  intros a d n Hn Hr. rewrite Z_to_bv_signed.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z. change (2^64 / 2)%Z with (2^63)%Z.
  destruct (word_signed_cases a) as [[H1 H2]|[H1 H2]].
  - rewrite Z.mod_small by lia. lia.
  - replace (bv_unsigned a + d + 2^63)%Z with ((n + d + 2^63) + 1 * 2^64)%Z by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac scalbn_close :=
  intros; unfold scalbn_post;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split;
  [ simp_regs; f_equal; f_equal; unfold scalbn_model, scalbn_reduce, two_p1023, two_m969;
    repeat match goal with
    | |- context [Z.ltb ?a ?b] =>
        first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
    end;
    (* [comment removed for export] *)
    repeat match goal with |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb_spec0 a b) end;
    match goal with |- fmul_d _ _ (scalbn_u ?a) = fmul_d _ _ (scalbn_u ?b) => replace b with a by lia end;
    reflexivity
  | repeat match goal with |- _ /\ _ => split end; assumption ].

Ltac scalbn_go_tail n' :=
  lazymatch goal with
  | |- evt _ _ (MS _ ?Ft _ _ _ ?m _) =>
      eapply (scalbn_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft _ m n');
      [ assumption | assumption | | lia | scalbn_close ]
  end.

Lemma scalbn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (n : Z),
  mem_inv img_segs m -> frm0 fc -> bv_signed a0 = n -> (-2^31 <= n < 2^31)%Z ->
  evt img_segs (scalbn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (reg_get F 10) n m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1bbd8)) fc None m (seg_rom img_segs)).
Proof.
  intros until n. intros MI FRM Hn Hr.
  pose proof (word_signed_cases a0) as SC.
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl img_segs m) as WM.
  step. step.
  if_cases LT1024; zify_cond LT1024.
  - (* [comment removed for export] *)
    step. step. if_cases GTm1023; zify_cond GTm1023.
    + (* [comment removed for export] *)
      scalbn_go_tail n. exact Hn.
    + (* [comment removed for export] *)
      do 5 step. if_cases GTm1992; zify_cond GTm1992.
      * (* [comment removed for export] *) step. scalbn_go_tail (n + 969)%Z. apply (signed_of_add a0 969 n Hn). lia.
      * do 3 step. if_cases GTm2960; zify_cond GTm2960.
        -- (* [comment removed for export] *) do 3 step. scalbn_go_tail (n + 1938)%Z. apply (signed_of_add a0 1938 n Hn). lia.
        -- (* [comment removed for export] *) do 4 step. scalbn_go_tail (-1022)%Z. vm_compute; reflexivity.
  - (* [comment removed for export] *)
    do 4 step. step. if_cases LT2047; zify_cond LT2047.
    + (* [comment removed for export] *) do 2 step. scalbn_go_tail (n - 1023)%Z. apply (signed_of_add a0 (-1023) n Hn). lia.
    + do 3 step. if_cases LT3069; zify_cond LT3069.
      * (* [comment removed for export] *) do 3 step. scalbn_go_tail (n - 2046)%Z. apply (signed_of_add a0 (-2046) n Hn). lia.
      * (* [comment removed for export] *) do 4 step. scalbn_go_tail 1023%Z. vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Definition scalbn_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (n : Z),
  mem_inv img_segs m -> frm0 fc -> bv_signed a0 = n -> (-2^31 <= n < 2^31)%Z ->
  evt img_segs (scalbn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (reg_get F 10) n m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1bbd8)) fc None m (seg_rom img_segs)).
Lemma scalbn_contract_ok : scalbn_contract.
Proof. exact scalbn_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac scalbn_close :=
  intros; unfold scalbn_post;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split;
  [ simp_regs; f_equal; f_equal; unfold scalbn_model, scalbn_reduce, two_p1023, two_m969;
    repeat match goal with
    | |- context [Z.ltb ?a ?b] =>
        first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
    end;
    
    repeat match goal with |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb_spec0 a b) end;
    match goal with |- fmul_d _ _ (scalbn_u ?a) = fmul_d _ _ (scalbn_u ?b) => replace b with a by lia end;
    reflexivity
  | repeat match goal with |- _ /\ _ => split end; assumption ].
Ltac scalbn_go_tail n' :=
  lazymatch goal with
  | |- evt _ _ (MS _ ?Ft _ _ _ ?m _) =>
      eapply (scalbn_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft _ m n');
      [ assumption | assumption | | lia | scalbn_close ]
  end.

(* [comment removed for export] *)
Existing Class scalbn_contract.
