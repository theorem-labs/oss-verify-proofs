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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MemIsZero_b Ba0RegionPoisoned_b Ba0AsanMemset_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_rc2a64_c2bf4_b Ba0_code_rbd474_bd4ac_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub; imm_norm; unorm; first [reflexivity | f_equal; lia].

Lemma ret_ok_11dc70 : ret_ok (0x120260 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma ret_ok_11dcf8 : ret_ok (0x1202e8 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma syscall_ret_ok : forall regs (M rom : word -> option byte) (ret : word) k,
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 k -> (0 <= k < 2 ^ 63)%Z ->
  exists regs', msteps ASEGS (mkst regs (0x118bd0 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ keeps_cs regs regs'.
Proof.
  intros regs M rom ret k H1 Hret H10 Hk.
  eexists. split.
  - stepn F_1165e0 D_1165e0.                                               (* [comment removed for export] *)
    stepiv F_1165e4 D_1165e4 (Z_to_bv 64 (2 ^ 64 - 4095)) ltac:(gres; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
    stepb_tk F_1165e8 D_1165e8 ltac:(cond).                                (* [comment removed for export] *)
    stepret F_116614 D_116614 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; rwH; reflexivity | solve_keeps_cs].
Qed.

Lemma step_subw_at' : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_subw (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma v_lw_small' : forall z, (0 <= z < 2 ^ 31)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lw. rewrite u_Z2bv by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite Z.mod_small; lia.
Qed.
Lemma v_subw_small : forall a b, (0 <= b <= a)%Z -> (a < 2 ^ 31)%Z -> v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b H1 H2. unfold v_subw. rewrite !u_Z2bv by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite Z.mod_small; lia.
Qed.

Lemma lxor_bound64 : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> (0 <= Z.lxor a b < 2 ^ 64)%Z.
Proof.
  intros a b Ha Hb. assert (Hnn : (0 <= Z.lxor a b)%Z) by (apply Z.lxor_nonneg; lia). split; [exact Hnn|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|NE]; [lia|].
  apply Z.log2_lt_pow2; [lia|]. pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as L.
  assert (Z.log2 a < 64)%Z by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
  assert (Z.log2 b < 64)%Z by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]). lia.
Qed.

Definition W64 (M : word -> option byte) (a v : Z) : word -> option byte := wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v)).

Section WV.
  Variable M rom : word -> option byte.
  Variables f q c rem k : Z.           (* [comment removed for export] *)
  Hypothesis Hk : (0 <= k < 2 ^ 63)%Z.
  Hypothesis Hrem : (0 <= rem < 2 ^ 63)%Z.
  Hypothesis Hq : (0 <= q)%Z /\ (q + 32 < 2 ^ 63)%Z.

  (* [comment removed for export] *)
  Lemma wv_ret_A : forall regs,
    getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
    exists regs',
      msteps ASEGS (mkst regs (0x12025c : word) M rom) (mkst regs' (if Z.eqb k rem then (0x120264 : word) else (0x1202f0 : word)) M rom)
      /\ getr regs' 10 = Z_to_bv 64 k /\ keeps_but [1]%bv regs regs'.
  Proof.
    intros regs H10 H22.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x12025c : word) M rom) (mkst r1 (0x118bd0 : word) M rom)
              /\ getr r1 1 = (0x120260 : word) /\ getr r1 10 = Z_to_bv 64 k /\ getr r1 22 = Z_to_bv 64 rem /\ keeps_but [1]%bv regs r1).
    { eexists. split; [stepn F_11dc6c D_11dc6c; apply mst_refl|].
      repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & R1 & R10 & R22 & K1).
    destruct (syscall_ret_ok r1 M rom (0x120260 : word) k R1 ret_ok_11dc70 R10 Hk) as (r2 & RUN2 & V10 & K2).
    assert (V22 : getr r2 22 = Z_to_bv 64 rem) by (rewrite (K2 22%bv) by (cbv; tauto); exact R22).
    destruct (Z.eqb_spec k rem) as [E|NE].
    - eexists. split; [|split].
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
        stepb_ft F_11dc70 D_11dc70 ltac:(cond).                            (* [comment removed for export] *)
        apply mst_refl.
      + exact V10.
      + eapply keeps_but_trans; [exact K1 | apply keeps_but_cs; exact K2].
    - eexists. split; [|split].
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
        stepb_tk F_11dc70 D_11dc70 ltac:(cond).                            (* [comment removed for export] *)
        apply mst_refl.
      + exact V10.
      + eapply keeps_but_trans; [exact K1 | apply keeps_but_cs; exact K2].
  Qed.

  (* [comment removed for export] *)
  Lemma wv_ret_B : forall regs,
    getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem -> getr regs 20 = Z_to_bv 64 q ->
    exists regs',
      msteps ASEGS (mkst regs (0x1202e4 : word) M rom) (mkst regs' (if Z.eqb k rem then (0x120264 : word) else (0x1202f0 : word)) M rom)
      /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = Z_to_bv 64 q /\ keeps_but [1; 19]%bv regs regs'.
  Proof.
    intros regs H10 H22 H20.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x1202e4 : word) M rom) (mkst r1 (0x118bd0 : word) M rom)
              /\ getr r1 1 = (0x1202e8 : word) /\ getr r1 10 = Z_to_bv 64 k /\ getr r1 22 = Z_to_bv 64 rem /\ getr r1 20 = Z_to_bv 64 q /\ keeps_but [1; 19]%bv regs r1).
    { eexists. split; [stepn F_11dcf4 D_11dcf4; apply mst_refl|].
      repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & R1 & R10 & R22 & R20 & K1).
    destruct (syscall_ret_ok r1 M rom (0x1202e8 : word) k R1 ret_ok_11dcf8 R10 Hk) as (r2 & RUN2 & V10 & K2).
    assert (V22 : getr r2 22 = Z_to_bv 64 rem) by (rewrite (K2 22%bv) by (cbv; tauto); exact R22).
    assert (V20 : getr r2 20 = Z_to_bv 64 q) by (rewrite (K2 20%bv) by (cbv; tauto); exact R20).
    destruct (Z.eqb_spec k rem) as [E|NE].
    - eexists. split; [|split; [|split]].
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
        stepiv F_11dcf8 D_11dcf8 (Z_to_bv 64 q) ltac:(wval).               (* [comment removed for export] *)
        stepb_tk F_11dcfc D_11dcfc ltac:(cond).                            (* [comment removed for export] *)
        apply mst_refl.
      + gres; rwH; reflexivity.
      + gres; reflexivity.
      + eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|]. solve_keeps_but.
    - eexists. split; [|split; [|split]].
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
        stepiv F_11dcf8 D_11dcf8 (Z_to_bv 64 q) ltac:(wval).
        stepb_ft F_11dcfc D_11dcfc ltac:(cond).                            (* [comment removed for export] *)
        apply mst_refl.
      + gres; rwH; reflexivity.
      + gres; reflexivity.
      + eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|]. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Variables b1 l1 fd : Z.
  Hypothesis Hf : (0 <= f)%Z /\ (f + 124 <= q \/ q + 32 <= f + 120)%Z /\ (f + 124 < 2 ^ 63)%Z.
  Hypothesis Hfd : (0 <= fd < 2 ^ 31)%Z.
  Hypothesis HFD : rdn ASEGS M (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).
  Hypothesis Hc : (1 <= c <= 2)%Z.
  Hypothesis Hk0 : (0 < k)%Z.

  #[local] Ltac slt_ft := rwH; unfold c_lts, bv_lts; rewrite !signed64_small by lia; first [apply Z.ltb_lt | apply Z.ltb_ge | apply Z.leb_le | apply Z.leb_gt]; lia.
  #[local] Ltac rdw a := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 a) by (symmetry; wval) end.
  #[local] Ltac peel := rewrite rdn_wbytes_out;
      [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
        | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].

  Lemma wv_body_lo : forall regs,
    (k <= l1 < 2 ^ 63)%Z -> (0 <= b1)%Z -> (b1 + k < 2 ^ 64)%Z ->
    rdn ASEGS M (Z_to_bv 64 q) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 b1)) ->
    rdn ASEGS M (Z_to_bv 64 (q + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 l1)) ->
    store_ok ASEGS M (Z_to_bv 64 q) 16%nat = true ->
    getr regs 10 = Z_to_bv 64 k -> getr regs 19 = Z_to_bv 64 q -> getr regs 18 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f ->
    (k <= rem)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x1202f0 : word) M rom) (mkst regs' (0x1202e0 : word) (W64 (W64 M q (b1 + k)) (q + 8) (l1 - k)) rom)
      /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd /\ getr regs' 11 = Z_to_bv 64 q /\ getr regs' 12 = Z_to_bv 64 c
      /\ getr regs' 20 = Z_to_bv 64 q /\ getr regs' 18 = Z_to_bv 64 c /\ getr regs' 22 = Z_to_bv 64 (rem - k)
      /\ keeps_but [18; 20; 22]%bv regs regs'.
  Proof.
    intros regs Hl1 Hb1 Hb1k R0 R8 SOK H10 H19 H18 H22 H9 Hkr.
    destruct Hq as (Hq0 & Hq1). destruct Hf as (Hf0 & Hfq & Hf1).
    assert (SOK0 : store_ok ASEGS M (Z_to_bv 64 q) 8%nat = true).
    { apply (store_ok_sub ASEGS M (Z_to_bv 64 q) _ 16%nat); [unorm; cbn; lia | exact SOK | unorm; lia | unorm; cbn; lia]. }
    assert (SOK8 : store_ok ASEGS (W64 M q (b1 + k)) (Z_to_bv 64 (q + 8)) 8%nat = true).
    { unfold W64. apply (store_ok_mono _ _ M); [apply wbytes_grows|].
      apply (store_ok_sub ASEGS M (Z_to_bv 64 q) _ 16%nat); [unorm; cbn; lia | exact SOK | unorm; lia | unorm; cbn; lia]. }
    assert (R8' : rdn ASEGS (W64 M q (b1 + k)) (Z_to_bv 64 (q + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 l1))).
    { unfold W64. peel. exact R8. }
    assert (HFD' : rdn ASEGS (W64 M q (b1 + k)) (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))).
    { unfold W64. peel. exact HFD. }
    eexists. split.
    - stepb_ft F_11dd00 D_11dd00 ltac:(slt_ft).                                         (* [comment removed for export] *)
      stepld F_11dd04 D_11dd04 (Z_to_bv 64 l1) ltac:(rdw (q + 8)%Z; exact R8).           (* [comment removed for export] *)
      stepov F_11dd08 D_11dd08 (Z_to_bv 64 0) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (l1 <? k)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).   (* [comment removed for export] *)
      stepiv F_11dd0c D_11dd0c (Z_to_bv 64 0) ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).                                     (* [comment removed for export] *)
      stepiv F_11dd10 D_11dd10 (Z_to_bv 64 q) ltac:(wval).                               (* [comment removed for export] *)
      stepld F_11dd14 D_11dd14 (Z_to_bv 64 b1) ltac:(rdw q; exact R0).                   (* [comment removed for export] *)
      stepiv F_11dd18 D_11dd18 (Z_to_bv 64 0) ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).                                     (* [comment removed for export] *)
      stepov F_11dd1c D_11dd1c (Z_to_bv 64 0) ltac:(gres; rwH; unfold v_and; unorm; rewrite Z.land_0_l; reflexivity).                     (* [comment removed for export] *)
      stepiv F_11dd20 D_11dd20 (Z_to_bv 64 k) ltac:(wval).                               (* [comment removed for export] *)
      stepiv F_11dd24 D_11dd24 (Z_to_bv 64 (b1 + k)) ltac:(wval).                        (* [comment removed for export] *)
      stepsd F_11dd28 D_11dd28 (Z_to_bv 64 q) (Z_to_bv 64 (b1 + k)) ltac:(exact SOK0).   (* [comment removed for export] *)
      stepb_tk F_11dd2c D_11dd2c ltac:(cond).                                            (* [comment removed for export] *)
      stepn F_11dcc4 D_11dcc4.                                                           (* [comment removed for export] *)
      stepiv F_11dcc8 D_11dcc8 (Z_to_bv 64 q) ltac:(wval).                               (* [comment removed for export] *)
      stepiv F_11dccc D_11dccc (Z_to_bv 64 (q + 8)) ltac:(wval).                         (* [comment removed for export] *)
      stepld F_11dcd0 D_11dcd0 (Z_to_bv 64 l1) ltac:(rdw (q + 8)%Z; exact R8').          (* [comment removed for export] *)
      stepiv F_11dcd4 D_11dcd4 (Z_to_bv 64 (rem - k)) ltac:(wval).                       (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fd)) (v := Z_to_bv 64 fd);
                     [exact F_11dcd8 | reflexivity | exact D_11dcd8 | rdw (f + 120)%Z; exact HFD' | apply bytes_le_to_Z_4; unorm; lia] | step_simpl; vnorm].   (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_subw_at' with (v := Z_to_bv 64 c); [exact F_11dcdc | reflexivity | exact D_11dcdc | reflexivity
                     | gres; rwH; rewrite v_subw_small by lia; f_equal; lia] | step_simpl].                                                              (* [comment removed for export] *)
      stepiv F_11dce0 D_11dce0 (Z_to_bv 64 (l1 - k)) ltac:(wval).                        (* [comment removed for export] *)
      stepsd F_11dce4 D_11dce4 (Z_to_bv 64 (q + 8)) (Z_to_bv 64 (l1 - k)) ltac:(exact SOK8).   (* [comment removed for export] *)
      stepn F_11dce8 D_11dce8.                                                           (* [comment removed for export] *)
      stepiv F_11dcec D_11dcec (Z_to_bv 64 c) ltac:(wval).                               (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity; try (rewrite v_lw_small' by lia; reflexivity). solve_keeps_but.
  Qed.

  Variables b2 l2 : Z.
  Lemma wv_body_hi : forall regs,
    c = 2%Z -> (0 <= l1 < k)%Z -> (k - l1 <= l2 < 2 ^ 63)%Z -> (0 <= b2)%Z -> (b2 + (k - l1) < 2 ^ 64)%Z ->
    rdn ASEGS M (Z_to_bv 64 (q + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 l1)) ->
    rdn ASEGS M (Z_to_bv 64 (q + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 b2)) ->
    rdn ASEGS M (Z_to_bv 64 (q + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 l2)) ->
    store_ok ASEGS M (Z_to_bv 64 (q + 16)) 16%nat = true ->
    getr regs 10 = Z_to_bv 64 k -> getr regs 19 = Z_to_bv 64 q -> getr regs 18 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f ->
    (k <= rem)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x1202f0 : word) M rom) (mkst regs' (0x1202e0 : word) (W64 (W64 M (q + 16) (b2 + (k - l1))) (q + 24) (l2 - (k - l1))) rom)
      /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd /\ getr regs' 11 = Z_to_bv 64 (q + 16) /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 20 = Z_to_bv 64 (q + 16) /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 22 = Z_to_bv 64 (rem - k)
      /\ keeps_but [18; 20; 22]%bv regs regs'.
  Proof.
    intros regs Hc2 Hl1 Hl2 Hb2 Hb2k R8 R16 R24 SOK H10 H19 H18 H22 H9 Hkr.
    destruct Hq as (Hq0 & Hq1). destruct Hf as (Hf0 & Hfq & Hf1).
    assert (SOK0 : store_ok ASEGS M (Z_to_bv 64 (q + 16)) 8%nat = true).
    { apply (store_ok_sub ASEGS M (Z_to_bv 64 (q + 16)) _ 16%nat); [unorm; cbn; lia | exact SOK | unorm; lia | unorm; cbn; lia]. }
    assert (SOK8 : store_ok ASEGS (W64 M (q + 16) (b2 + (k - l1))) (Z_to_bv 64 (q + 24)) 8%nat = true).
    { unfold W64. apply (store_ok_mono _ _ M); [apply wbytes_grows|].
      apply (store_ok_sub ASEGS M (Z_to_bv 64 (q + 16)) _ 16%nat); [unorm; cbn; lia | exact SOK | unorm; lia | unorm; cbn; lia]. }
    assert (R24' : rdn ASEGS (W64 M (q + 16) (b2 + (k - l1))) (Z_to_bv 64 (q + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 l2))).
    { unfold W64. peel. exact R24. }
    assert (HFD' : rdn ASEGS (W64 M (q + 16) (b2 + (k - l1))) (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))).
    { unfold W64. peel. exact HFD. }
    eexists. split.
    - stepb_ft F_11dd00 D_11dd00 ltac:(slt_ft).                                         (* [comment removed for export] *)
      stepld F_11dd04 D_11dd04 (Z_to_bv 64 l1) ltac:(rdw (q + 8)%Z; exact R8).           (* [comment removed for export] *)
      stepov F_11dd08 D_11dd08 (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (l1 <? k)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).   (* [comment removed for export] *)
      stepiv F_11dd0c D_11dd0c (Z_to_bv 64 16) ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).                                    (* [comment removed for export] *)
      stepiv F_11dd10 D_11dd10 (Z_to_bv 64 (q + 16)) ltac:(wval).                        (* [comment removed for export] *)
      stepld F_11dd14 D_11dd14 (Z_to_bv 64 b2) ltac:(rdw (q + 16)%Z; exact R16).         (* [comment removed for export] *)
      stepiv F_11dd18 D_11dd18 (Z_to_bv 64 (2 ^ 64 - 1)) ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).                          (* [comment removed for export] *)
      stepov F_11dd1c D_11dd1c (Z_to_bv 64 l1) ltac:(gres; rwH; unfold v_and; unorm; change (2 ^ 64 - 1)%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).   (* [comment removed for export] *)
      stepiv F_11dd20 D_11dd20 (Z_to_bv 64 (k - l1)) ltac:(wval).                        (* [comment removed for export] *)
      stepiv F_11dd24 D_11dd24 (Z_to_bv 64 (b2 + (k - l1))) ltac:(wval).                 (* [comment removed for export] *)
      stepsd F_11dd28 D_11dd28 (Z_to_bv 64 (q + 16)) (Z_to_bv 64 (b2 + (k - l1))) ltac:(exact SOK0).   (* [comment removed for export] *)
      stepb_ft F_11dd2c D_11dd2c ltac:(cond).                                            (* [comment removed for export] *)
      stepn F_11dd30 D_11dd30.                                                           (* [comment removed for export] *)
      stepn F_11dd34 D_11dd34.                                                           (* [comment removed for export] *)
      stepiv F_11dcc8 D_11dcc8 (Z_to_bv 64 (q + 16)) ltac:(wval).                        (* [comment removed for export] *)
      stepiv F_11dccc D_11dccc (Z_to_bv 64 (q + 24)) ltac:(wval).                        (* [comment removed for export] *)
      stepld F_11dcd0 D_11dcd0 (Z_to_bv 64 l2) ltac:(rdw (q + 24)%Z; exact R24').        (* [comment removed for export] *)
      stepiv F_11dcd4 D_11dcd4 (Z_to_bv 64 (rem - k)) ltac:(wval).                       (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fd)) (v := Z_to_bv 64 fd);
                     [exact F_11dcd8 | reflexivity | exact D_11dcd8 | rdw (f + 120)%Z; exact HFD' | apply bytes_le_to_Z_4; unorm; lia] | step_simpl; vnorm].   (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_subw_at' with (v := Z_to_bv 64 1); [exact F_11dcdc | reflexivity | exact D_11dcdc | reflexivity
                     | gres; rwH; rewrite Hc2; rewrite v_subw_small by lia; reflexivity] | step_simpl].                                                  (* [comment removed for export] *)
      stepiv F_11dce0 D_11dce0 (Z_to_bv 64 (l2 - (k - l1))) ltac:(wval).                 (* [comment removed for export] *)
      stepsd F_11dce4 D_11dce4 (Z_to_bv 64 (q + 24)) (Z_to_bv 64 (l2 - (k - l1))) ltac:(exact SOK8).   (* [comment removed for export] *)
      stepn F_11dce8 D_11dce8.                                                           (* [comment removed for export] *)
      stepiv F_11dcec D_11dcec (Z_to_bv 64 1) ltac:(wval).                               (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity; try (rewrite v_lw_small' by lia; reflexivity). solve_keeps_but.
  Qed.
End WV.

(* [comment removed for export] *)
Section WVE.
  Variable M rom : word -> option byte.
  Variables f sp buf len wpos wbase fd : Z.
  Hypothesis Hsp : (0 <= sp)%Z /\ (sp + 40 < 2 ^ 63)%Z.
  Hypothesis Hf : (0 <= f)%Z /\ (f + 124 <= sp + 8 \/ sp + 40 <= f)%Z /\ (f + 124 < 2 ^ 63)%Z.
  Hypothesis Hw : (0 <= wbase <= wpos)%Z /\ (wpos < 2 ^ 63)%Z.
  Hypothesis Hlen : (0 <= len < 2 ^ 62)%Z.
  Hypothesis Hbuf : (0 <= buf < 2 ^ 64)%Z.
  Hypothesis Hfd : (0 <= fd < 2 ^ 31)%Z.
  Hypothesis RWP : rdn ASEGS M (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wpos)).
  Hypothesis RWB : rdn ASEGS M (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wbase)).
  Hypothesis RFD : rdn ASEGS M (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).
  Hypothesis SOK : store_ok ASEGS M (Z_to_bv 64 (sp + 8)) 32%nat = true.

  Definition wve_mem : word -> option byte := W64 (W64 (W64 (W64 M (sp + 8) wbase) (sp + 16) (wpos - wbase)) (sp + 24) buf) (sp + 32) len.
  Definition wve_iov : Z := if Z.eqb wpos wbase then (sp + 24)%Z else (sp + 8)%Z.
  Definition wve_cnt : Z := if Z.eqb wpos wbase then 1%Z else 2%Z.

  #[local] Ltac rdw a := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 a) by (symmetry; wval) end.
  #[local] Ltac peel := rewrite rdn_wbytes_out;
      [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
        | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
  #[local] Ltac mysd F D aa vv oktac :=
    chain_step; [reflexivity | eapply step_sd_at with (a := aa) (v := vv);
                   [exact F | reflexivity | exact D | wval | (gres; rwH; reflexivity) | oktac] | step_simpl].
  #[local] Ltac grows := first [apply mem_grows_refl | (eapply mem_grows_trans; [ | apply wbytes_grows ]; grows)].
  #[local] Ltac sok := apply (store_ok_mono _ _ M); [grows|];
      apply (store_ok_sub ASEGS M (Z_to_bv 64 (sp + 8)) _ 32%nat); [unorm; cbn; lia | exact SOK | unorm; lia | unorm; cbn; lia].

  Lemma wv_entry : forall regs,
    getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 sp -> getr regs 11 = Z_to_bv 64 buf -> getr regs 8 = Z_to_bv 64 len ->
    exists regs',
      msteps ASEGS (mkst regs (0x12020c : word) M rom) (mkst regs' (0x120258 : word) wve_mem rom)
      /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd /\ getr regs' 11 = Z_to_bv 64 wve_iov /\ getr regs' 12 = Z_to_bv 64 wve_cnt
      /\ getr regs' 18 = Z_to_bv 64 wve_cnt /\ getr regs' 19 = Z_to_bv 64 wve_iov /\ getr regs' 22 = Z_to_bv 64 (wpos - wbase + len)
      /\ keeps_but [18; 19; 22]%bv regs regs'.
  Proof.
    intros regs H9 H2 H11 H8. destruct Hsp as (Hs0 & Hs1). destruct Hf as (Hf0 & Hfs & Hf1). destruct Hw as (Hw0 & Hw1).
    assert (RFD' : rdn ASEGS wve_mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))).
    { unfold wve_mem, W64. peel. peel. peel. peel. exact RFD. }
    pose proof (lxor_bound64 wpos wbase ltac:(lia) ltac:(lia)) as XB.
    unfold wve_iov, wve_cnt. unfold wve_mem, W64 in *. destruct (Z.eqb_spec wpos wbase) as [E|NE].
    - eexists. split.
      + stepld F_11dc1c D_11dc1c (Z_to_bv 64 wpos) ltac:(rdw (f + 40)%Z; exact RWP).        (* [comment removed for export] *)
        stepld F_11dc20 D_11dc20 (Z_to_bv 64 wbase) ltac:(rdw (f + 56)%Z; exact RWB).       (* [comment removed for export] *)
        stepiv F_11dc24 D_11dc24 (Z_to_bv 64 (wpos - wbase)) ltac:(wval).                   (* [comment removed for export] *)
        stepn F_11dc28 D_11dc28.                                                            (* [comment removed for export] *)
        mysd F_11dc2c D_11dc2c (Z_to_bv 64 (sp + 8)) (Z_to_bv 64 wbase) ltac:(sok).
        mysd F_11dc30 D_11dc30 (Z_to_bv 64 (sp + 16)) (Z_to_bv 64 (wpos - wbase)) ltac:(sok).
        mysd F_11dc34 D_11dc34 (Z_to_bv 64 (sp + 24)) (Z_to_bv 64 buf) ltac:(sok).
        mysd F_11dc38 D_11dc38 (Z_to_bv 64 (sp + 32)) (Z_to_bv 64 len) ltac:(sok).
        stepiv F_11dc3c D_11dc3c (Z_to_bv 64 (wpos - wbase + len)) ltac:(wval).             (* [comment removed for export] *)
        stepov F_11dc40 D_11dc40 (Z_to_bv 64 0) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu, v_xor; rewrite E, Z.lxor_nilpotent; reflexivity).   (* [comment removed for export] *)
        stepb_tk F_11dc44 D_11dc44 ltac:(cond).                                             (* [comment removed for export] *)
        stepiv F_11dc50 D_11dc50 (Z_to_bv 64 (sp + 24)) ltac:(wval).                        (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fd)) (v := Z_to_bv 64 fd);
                       [exact F_11dc54 | reflexivity | exact D_11dc54 | rdw (f + 120)%Z; exact RFD' | apply bytes_le_to_Z_4; unorm; lia] | step_simpl; vnorm].
        stepiv F_11dc58 D_11dc58 (Z_to_bv 64 1) ltac:(wval).                                (* [comment removed for export] *)
        stepn F_11dc5c D_11dc5c.                                                            (* [comment removed for export] *)
        stepiv F_11dc60 D_11dc60 (Z_to_bv 64 (sp + 24)) ltac:(wval).                        (* [comment removed for export] *)
        stepiv F_11dc64 D_11dc64 (Z_to_bv 64 1) ltac:(wval).                                (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; rwH; try reflexivity; try (rewrite v_lw_small' by lia; reflexivity). solve_keeps_but.
    - eexists. split.
      + stepld F_11dc1c D_11dc1c (Z_to_bv 64 wpos) ltac:(rdw (f + 40)%Z; exact RWP).
        stepld F_11dc20 D_11dc20 (Z_to_bv 64 wbase) ltac:(rdw (f + 56)%Z; exact RWB).
        stepiv F_11dc24 D_11dc24 (Z_to_bv 64 (wpos - wbase)) ltac:(wval).
        stepn F_11dc28 D_11dc28.
        mysd F_11dc2c D_11dc2c (Z_to_bv 64 (sp + 8)) (Z_to_bv 64 wbase) ltac:(sok).
        mysd F_11dc30 D_11dc30 (Z_to_bv 64 (sp + 16)) (Z_to_bv 64 (wpos - wbase)) ltac:(sok).
        mysd F_11dc34 D_11dc34 (Z_to_bv 64 (sp + 24)) (Z_to_bv 64 buf) ltac:(sok).
        mysd F_11dc38 D_11dc38 (Z_to_bv 64 (sp + 32)) (Z_to_bv 64 len) ltac:(sok).
        stepiv F_11dc3c D_11dc3c (Z_to_bv 64 (wpos - wbase + len)) ltac:(wval).
        stepov F_11dc40 D_11dc40 (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu, v_xor; unorm;
              assert (Z.lxor wpos wbase <> 0)%Z by (rewrite Z.lxor_eq_0_iff; exact NE);
              replace (0 <? Z.lxor wpos wbase)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).   (* [comment removed for export] *)
        stepb_ft F_11dc44 D_11dc44 ltac:(cond).                                             (* [comment removed for export] *)
        stepiv F_11dc48 D_11dc48 (Z_to_bv 64 (sp + 8)) ltac:(wval).                         (* [comment removed for export] *)
        stepn F_11dc4c D_11dc4c.                                                            (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fd)) (v := Z_to_bv 64 fd);
                       [exact F_11dc54 | reflexivity | exact D_11dc54 | rdw (f + 120)%Z; exact RFD' | apply bytes_le_to_Z_4; unorm; lia] | step_simpl; vnorm].
        stepiv F_11dc58 D_11dc58 (Z_to_bv 64 2) ltac:(wval).
        stepn F_11dc5c D_11dc5c.
        stepiv F_11dc60 D_11dc60 (Z_to_bv 64 (sp + 8)) ltac:(wval).
        stepiv F_11dc64 D_11dc64 (Z_to_bv 64 2) ltac:(wval).
        apply mst_refl.
      + repeat split; gres; rwH; try reflexivity; try (rewrite v_lw_small' by lia; reflexivity). solve_keeps_but.
  Qed.
End WVE.
End FPX_1.
