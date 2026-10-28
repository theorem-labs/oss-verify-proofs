(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0ReadIcpt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r4f7c4_4fa34_b Ba0_code_rd0c58_d0c8c_b Ba0_code_rcc12c_cc154_b Ba0_code_rbd474_bd4ac_b Ba0_code_rbce10_bce1c_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.
#[local] Ltac peel0 :=
  rewrite rdn_wbytes_out;
    [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia
      | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia ].

(* [comment removed for export] *)
Definition ERRNO_OFF : Z := 164.
Definition EISDIR_RET : Z := 18446744073709551595.      (* [comment removed for export] *)

Section RDPOSTE.
  Variable rom : word -> option byte.
  Variables ra : word.
  Variables s tp : Z.
  Hypothesis Hs : (0x1000000 <= s - 2200)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Htp : (4096 <= tp - 164)%Z /\ (tp <= s - 2200)%Z.
  Hypothesis Hret : ret_ok ra.

  Definition RDE (M : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes M
      (Z_to_bv 64 (s - 2136)) (word_to_le_bytes 8 (0x655bc : word)))
      (Z_to_bv 64 (s - 2144)) (word_to_le_bytes 8 (Z_to_bv 64 s)))
      (Z_to_bv 64 (tp - 164)) (word_to_le_bytes 4 (Z_to_bv 64 21)).

  Lemma RDE_out : forall M (x : word), ~ (s - 2144 <= bv_unsigned x < s - 2128)%Z -> ~ (tp - 164 <= bv_unsigned x < tp - 160)%Z -> RDE M x = M x.
  Proof.
    intros M x N1 N2. unfold RDE. pose proof (u64_range x). destruct Hs as [S1' S2']. destruct Htp as [T1' T2'].
    rewrite !wbytes_outside; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.
  Lemma RDE_grows : forall M, mem_grows M (RDE M).
  Proof. intros M. unfold RDE. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Theorem read_icpt_post_err_run : forall regs0 regs M,
    getr regs 10 = Z_to_bv 64 EISDIR_RET -> getr regs 2 = Z_to_bv 64 (s - 2144) -> getr regs 1 = (0x13032c : word) -> getr regs 8 = Z_to_bv 64 s -> getr regs 20 = Z_to_bv 64 1 ->
    getr regs 4 = Z_to_bv 64 tp ->
    store_ok ASEGS M (Z_to_bv 64 (s - 2200)) 2200%nat = true ->
    store_ok ASEGS M (Z_to_bv 64 (tp - 164)) 4%nat = true ->
    rdn ASEGS M (Z_to_bv 64 (s - 2136)) 8%nat = Some (word_to_le_bytes 8 (0x655bc : word)) ->
    rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) ->
    rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) ->
    rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) ->
    rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) ->
    rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) ->
    rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)) ->
    exists regs',
      msteps ASEGS (mkst regs (0x12a8dc : word) M rom) (mkst regs' ra (RDE M) rom)
      /\ getr regs' 10 = Z_to_bv 64 18446744073709551615 /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20
      /\ keeps_but Ba0ReadIcpt_b.RIPL regs regs'.
  Proof.
    intros regs0 regs M H10 H2 H1 H8 H20 H4 WOK EOK RA R1 R2 R3 R4 R5 R6. destruct Hs as [S1' S2']. destruct Htp as [T1' T2']. unfold EISDIR_RET in H10.
    assert (Rce : ret_ok (0x13032c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (R4e : ret_ok (0x655bc : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Rbd : ret_ok (Z_to_bv 64 1149936)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    #[local] Ltac maddrE z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
    #[local] Ltac sokE WOK := match type of WOK with store_ok _ ?M0 _ _ = _ => apply (store_ok_mono _ _ M0) end; [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl |];
                      apply (store_ok_sub ASEGS _ (Z_to_bv 64 (s - 2200)) _ 2200%nat); [unorm; cbn; lia | exact WOK | unorm; lia | unorm; cbn; lia].
    eexists. split.
    - stepret F_1282ec D_1282ec (0x13032c : word) ltac:(rwH; reflexivity).                                   (* [comment removed for export] *)
      stepld F_12dd3c D_12dd3c (0x655bc : word) ltac:(maddrE (s - 2136)%Z; exact RA).                         (* [comment removed for export] *)
      stepiv F_12dd40 D_12dd40 (Z_to_bv 64 (s - 2128)) ltac:(wval).                                          (* [comment removed for export] *)
      stepn F_12dd44 D_12dd44.                                                                                 (* [comment removed for export] *)
      stepn F_1165e0 D_1165e0.
      stepn F_1165e4 D_1165e4.
      stepb_ft F_1165e8 D_1165e8 ltac:(rwH; vm_compute; reflexivity).                                          (* [comment removed for export] *)
      stepiv F_1165ec D_1165ec (Z_to_bv 64 (s - 2144)) ltac:(wval).                                          (* [comment removed for export] *)
      stepsd F_1165f0 D_1165f0 (Z_to_bv 64 (s - 2136)) (0x655bc : word) ltac:(sokE WOK).                      (* [comment removed for export] *)
      stepsd F_1165f4 D_1165f4 (Z_to_bv 64 (s - 2144)) (Z_to_bv 64 s) ltac:(sokE WOK).                        (* [comment removed for export] *)
      stepn F_1165f8 D_1165f8.                                                                                 (* [comment removed for export] *)
      rewrite H10. replace (v_subw (Z_to_bv 64 0) (Z_to_bv 64 18446744073709551595)) with (Z_to_bv 64 21) by (apply bv_eq; vm_compute; reflexivity).
      stepn F_1165fc D_1165fc.                                                                                 (* [comment removed for export] *)
      stepiv F_115eb4 D_115eb4 (Z_to_bv 64 tp) ltac:(wval).                                                   (* [comment removed for export] *)
      stepiv F_115eb8 D_115eb8 (Z_to_bv 64 (tp - 164)) ltac:(wval).                                           (* [comment removed for export] *)
      stepret F_115ebc D_115ebc (Z_to_bv 64 1149936) ltac:(reflexivity).
      chain_step; [ reflexivity
                  | eapply step_sw_at with (a := Z_to_bv 64 (tp - 164)) (v := Z_to_bv 64 21);
                    [ exact F_116600 | reflexivity | exact D_116600 | gres; imm_norm; rewrite ?v_addi_0; reflexivity | gres; reflexivity
                    | apply (store_ok_mono _ _ M); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | exact EOK] ]
                  | step_simpl ].                                                                            (* [comment removed for export] *)
      stepn F_116604 D_116604.                                                                                 (* [comment removed for export] *)
      stepld F_116608 D_116608 (0x655bc : word) ltac:(maddrE (s - 2136)%Z; repeat peel0; apply rdn_wbytes_hit8; unorm; lia).   (* [comment removed for export] *)
      stepld F_11660c D_11660c (Z_to_bv 64 s) ltac:(maddrE (s - 2144)%Z; repeat peel0; apply rdn_wbytes_hit8; unorm; lia).      (* [comment removed for export] *)
      stepiv F_116610 D_116610 (Z_to_bv 64 (s - 2128)) ltac:(wval).                                          (* [comment removed for export] *)
      stepret F_116614 D_116614 (0x655bc : word) ltac:(rwH; reflexivity).
      stepb_ft F_651a4 D_651a4 ltac:(cond).                                                                  (* [comment removed for export] *)
      stepb_tk F_651a8 D_651a8 ltac:(rwH; vm_compute; reflexivity).                                          (* [comment removed for export] *)
      stepiv F_65204 D_65204 (Z_to_bv 64 (s - 2032)) ltac:(wval).                                          (* [comment removed for export] *)
      stepld F_65208 D_65208 ra ltac:(maddrE (s - 8)%Z; repeat peel0; exact R1).
      stepld F_6520c D_6520c (getr regs0 8) ltac:(maddrE (s - 16)%Z; repeat peel0; exact R2).
      stepld F_65210 D_65210 (getr regs0 9) ltac:(maddrE (s - 24)%Z; repeat peel0; exact R3).
      stepld F_65214 D_65214 (getr regs0 18) ltac:(maddrE (s - 32)%Z; repeat peel0; exact R4).
      stepld F_65218 D_65218 (getr regs0 19) ltac:(maddrE (s - 40)%Z; repeat peel0; exact R5).
      stepld F_6521c D_6521c (getr regs0 20) ltac:(maddrE (s - 48)%Z; repeat peel0; exact R6).
      stepiv F_65220 D_65220 (Z_to_bv 64 s) ltac:(wval).
      stepret F_65224 D_65224 ra ltac:(rwH; reflexivity).
      unfold RDE. apply mst_refl.
    - repeat split; gres; rwH; try reflexivity. solve_keeps_but.
  Qed.
End RDPOSTE.
End FPX_1.
