(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib Pm9MemIsZero Pm9RegionPoisoned
  Pm9AsanMemset Pm9AsanMemcpy Pm9StrlenIcpt Pm9TlsGetAddr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_64000_65000 Pm9_code_8b000_8c000     .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Lemma v_sll_lit : forall i k, (0 <= k < 64)%Z -> (0 <= i < 2 ^ 64)%Z -> v_sll (Z_to_bv 64 i) (Z_to_bv 64 k) = Z_to_bv 64 (i * 2 ^ k).
Proof.
  intros i k Hk Hi. unfold v_sll. rewrite !u_Z2bv by lia. rewrite (Z.mod_small k 64) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma v_srl_lit : forall i k, (0 <= k < 64)%Z -> (0 <= i < 2 ^ 64)%Z -> v_srl (Z_to_bv 64 i) (Z_to_bv 64 k) = Z_to_bv 64 (i / 2 ^ k).
Proof.
  intros i k Hk Hi. unfold v_srl. rewrite !u_Z2bv by lia. rewrite (Z.mod_small k 64) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma u_Z2bv8 : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256%Z. lia. Qed.

Lemma wbytes_out_any_gc : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m addr bs x = m x.
Proof.
  intros bs m addr x Hnw [Hx|Hx]; [apply wbytes_below; assumption | apply wbytes_above; exact Hx].
Qed.

Section FPX_0. Context {fx : PropExec.FPState}.
Lemma step_sll_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_SLL rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_sll (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_sll segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_srl_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_SRL rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_srl (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_srl segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_subw_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_subw (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
End FPX_0.

Ltac stepsv F D vv tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Op ALU_SLL _ _ _, _) => eapply step_sll_at with (v := vv)
    | decode_any _ = Some (Op ALU_SRL _ _ _, _) => eapply step_srl_at with (v := vv)
    | decode_any _ = Some (Op32 ALU_SUB _ _ _, _) => eapply step_subw_at with (v := vv)
    end;
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

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
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mldq F D z R :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | exact (bytes_le_to_Z_8 _)]
    | step_simpl; vnorm].
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
#[local] Ltac mlbq F D z R :=
  chain_step; [reflexivity
    | eapply step_lb; [exact F | reflexivity | exact D | maddr z; exact R]
    | step_simpl; vnorm].
#[local] Ltac stepsdq F D aa vv oktac :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wval | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
    | step_simpl].

Section INNER.
  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  Variables fs c nfr nlog frsz flb sparg bot : Z.
  Variables flag rs : Z -> Z.
  Hypothesis Hc : (0 <= c <= 10)%Z.
  Hypothesis Hnlog : nlog = (14 - c)%Z.
  Hypothesis Hnfr : nfr = (2 ^ nlog)%Z.
  Hypothesis Hfrsz : frsz = (2 ^ (6 + c))%Z.
  Hypothesis Hflb : flb = (fs + 4096 + 32768 - 2 * nfr)%Z.
  Hypothesis Hfs : (0x6b4000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
  Hypothesis HL : rdn ASEGS M (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).
  Hypothesis HF : forall i, (0 <= i < nfr)%Z -> rdn ASEGS M (Z_to_bv 64 (flb + i)) 1%nat = Some [Z_to_bv 8 (flag i)] /\ (0 <= flag i < 256)%Z.
  Hypothesis HR : forall i, (0 <= i < nfr)%Z -> flag i <> 0%Z ->
    rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs i)))
    /\ (0 <= rs i < 2 ^ 64)%Z /\ (rs i <= bot \/ sparg <= rs i)%Z.

  Lemma nfr_facts : (16 <= nfr <= 16384)%Z /\ (64 <= frsz <= 65536)%Z /\ (nfr * frsz = 2 ^ 20)%Z /\ (0 <= nlog <= 14)%Z.
  Proof.
    subst nlog nfr frsz. assert (E : (14 - c + (6 + c) = 20)%Z) by lia.
    repeat split; try lia.
    - change 16%Z with (2 ^ 4)%Z. apply Z.pow_le_mono_r; lia.
    - change 16384%Z with (2 ^ 14)%Z. apply Z.pow_le_mono_r; lia.
    - change 64%Z with (2 ^ 6)%Z. apply Z.pow_le_mono_r; lia.
    - change 65536%Z with (2 ^ 16)%Z. apply Z.pow_le_mono_r; lia.
    - rewrite <- Z.pow_add_r by lia. rewrite E. reflexivity.
  Qed.

  Definition gi_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 27 = Z_to_bv 64 i /\ getr rg 24 = Z_to_bv 64 flb /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 20 = Z_to_bv 64 c
    /\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096) /\ getr rg 21 = Z_to_bv 64 (6 + c) /\ getr rg 18 = Z_to_bv 64 bot
    /\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 19 = Z_to_bv 64 nlog.

  Definition gi_keeps (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 27%bv -> getr regs' r = getr regs r.

  #[local] Ltac kp := intros r N10 N11 N12 N27; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

  Lemma gc_inner_run : forall (q : nat) regs i,
    gi_inv regs i -> (0 <= i)%Z -> (i + Z.of_nat q + 1 = nfr)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x64b4c : word) M rom) (mkst regs' (0x64adc : word) M rom)
      /\ gi_inv regs' nfr /\ gi_keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs i (H27 & H24 & H25 & H20 & H7 & H8 & H21 & H18 & H9 & H19) Hi Hq;
      pose proof nfr_facts as (N1 & N2 & N3 & N4); destruct Hfs as [Fs1 Fs2]; destruct Hsp as [Sp1 Sp2];
      destruct (HF i ltac:(lia)) as [Fi Bi].
    -
      assert (Hdiv : ((i + 1) / 2 ^ nlog = 1)%Z) by (rewrite <- Hnfr; replace (i + 1)%Z with nfr by lia; apply Z.div_same; lia).
      destruct (Z.eq_dec (flag i) 0) as [F0|F1].
      + eexists. split.
        * stepiv F_64b04 D_64b04 (Z_to_bv 64 (flb + i)) ltac:(wval).
          chain_step; [reflexivity | eapply step_lbu; [exact F_64b08 | reflexivity | exact D_64b08 | maddr (flb + i)%Z; exact Fi] | step_simpl; vnorm].
          stepb_tk F_64b0c D_64b0c ltac:(rewrite (u_Z2bv8 (flag i)) by lia; cond).
          stepiv F_64af8 D_64af8 (Z_to_bv 64 (i + 1)) ltac:(wval).
          stepsv F_64afc D_64afc (Z_to_bv 64 1) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
          stepb_tk F_64b00 D_64b00 ltac:(cond).
          apply mst_refl.
        * split; [unfold gi_inv; post | kp].
      + destruct (HR i ltac:(lia) F1) as (Ri & Bri & NC).
        destruct (Z.le_gt_cases (rs i) bot) as [LE|GT].
        * eexists. split.
          -- stepiv F_64b04 D_64b04 (Z_to_bv 64 (flb + i)) ltac:(wval).
             chain_step; [reflexivity | eapply step_lbu; [exact F_64b08 | reflexivity | exact D_64b08 | maddr (flb + i)%Z; exact Fi] | step_simpl; vnorm].
             stepb_ft F_64b0c D_64b0c ltac:(rewrite (u_Z2bv8 (flag i)) by lia; cond).
             mldq F_64b10 D_64b10 (fs + 88)%Z HL.
             stepn F_64b14 D_64b14.
             stepsv F_64b18 D_64b18 (Z_to_bv 64 (c * 2 ^ 20)) ltac:(gres; rwH; apply v_sll_lit; lia).
             stepn F_64b1c D_64b1c.
             stepiv F_64b20 D_64b20 (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20)) ltac:(wval).
             stepiv F_64b24 D_64b24 (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20 + 32768)) ltac:(wval).
             stepsv F_64b28 D_64b28 (Z_to_bv 64 (i * frsz)) ltac:(gres; rwH; rewrite v_sll_lit by lia; rewrite <- Hfrsz; reflexivity).
             stepiv F_64b2c D_64b2c (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz)) ltac:(gres; rwH; unfold v_add; unorm; f_equal; nia).
             mldq F_64b30 D_64b30 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)%Z Ri.
             stepb_tk F_64b34 D_64b34 ltac:(cond).
             stepiv F_64af8 D_64af8 (Z_to_bv 64 (i + 1)) ltac:(wval).
             stepsv F_64afc D_64afc (Z_to_bv 64 1) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
             stepb_tk F_64b00 D_64b00 ltac:(cond).
             apply mst_refl.
          -- split; [unfold gi_inv; post | kp].
        * eexists. split.
          -- stepiv F_64b04 D_64b04 (Z_to_bv 64 (flb + i)) ltac:(wval).
             chain_step; [reflexivity | eapply step_lbu; [exact F_64b08 | reflexivity | exact D_64b08 | maddr (flb + i)%Z; exact Fi] | step_simpl; vnorm].
             stepb_ft F_64b0c D_64b0c ltac:(rewrite (u_Z2bv8 (flag i)) by lia; cond).
             mldq F_64b10 D_64b10 (fs + 88)%Z HL.
             stepn F_64b14 D_64b14.
             stepsv F_64b18 D_64b18 (Z_to_bv 64 (c * 2 ^ 20)) ltac:(gres; rwH; apply v_sll_lit; lia).
             stepn F_64b1c D_64b1c.
             stepiv F_64b20 D_64b20 (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20)) ltac:(wval).
             stepiv F_64b24 D_64b24 (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20 + 32768)) ltac:(wval).
             stepsv F_64b28 D_64b28 (Z_to_bv 64 (i * frsz)) ltac:(gres; rwH; rewrite v_sll_lit by lia; rewrite <- Hfrsz; reflexivity).
             stepiv F_64b2c D_64b2c (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz)) ltac:(gres; rwH; unfold v_add; unorm; f_equal; nia).
             mldq F_64b30 D_64b30 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)%Z Ri.
             stepb_ft F_64b34 D_64b34 ltac:(cond).
             stepb_tk F_64b38 D_64b38 ltac:(cond).
             stepiv F_64af8 D_64af8 (Z_to_bv 64 (i + 1)) ltac:(wval).
             stepsv F_64afc D_64afc (Z_to_bv 64 1) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
             stepb_tk F_64b00 D_64b00 ltac:(cond).
             apply mst_refl.
          -- split; [unfold gi_inv; post | kp].
    - assert (Hdiv : ((i + 1) / 2 ^ nlog = 0)%Z) by (apply Z.div_small; rewrite <- Hnfr; lia).
      eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x64b4c : word) M rom) (fun rg => gi_inv rg (i + 1) /\ gi_keeps regs rg)).
      + destruct (Z.eq_dec (flag i) 0) as [F0|F1].
        * eexists. split.
          -- stepiv F_64b04 D_64b04 (Z_to_bv 64 (flb + i)) ltac:(wval).
             chain_step; [reflexivity | eapply step_lbu; [exact F_64b08 | reflexivity | exact D_64b08 | maddr (flb + i)%Z; exact Fi] | step_simpl; vnorm].
             stepb_tk F_64b0c D_64b0c ltac:(rewrite (u_Z2bv8 (flag i)) by lia; cond).
             stepiv F_64af8 D_64af8 (Z_to_bv 64 (i + 1)) ltac:(wval).
             stepsv F_64afc D_64afc (Z_to_bv 64 0) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
             stepb_ft F_64b00 D_64b00 ltac:(cond).
             apply mst_refl.
          -- split; [unfold gi_inv; post | kp].
        * destruct (HR i ltac:(lia) F1) as (Ri & Bri & NC).
          destruct (Z.le_gt_cases (rs i) bot) as [LE|GT].
          -- eexists. split.
             ++ stepiv F_64b04 D_64b04 (Z_to_bv 64 (flb + i)) ltac:(wval).
                chain_step; [reflexivity | eapply step_lbu; [exact F_64b08 | reflexivity | exact D_64b08 | maddr (flb + i)%Z; exact Fi] | step_simpl; vnorm].
                stepb_ft F_64b0c D_64b0c ltac:(rewrite (u_Z2bv8 (flag i)) by lia; cond).
                mldq F_64b10 D_64b10 (fs + 88)%Z HL.
                stepn F_64b14 D_64b14.
                stepsv F_64b18 D_64b18 (Z_to_bv 64 (c * 2 ^ 20)) ltac:(gres; rwH; apply v_sll_lit; lia).
                stepn F_64b1c D_64b1c.
                stepiv F_64b20 D_64b20 (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20)) ltac:(wval).
                stepiv F_64b24 D_64b24 (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20 + 32768)) ltac:(wval).
                stepsv F_64b28 D_64b28 (Z_to_bv 64 (i * frsz)) ltac:(gres; rwH; rewrite v_sll_lit by lia; rewrite <- Hfrsz; reflexivity).
                stepiv F_64b2c D_64b2c (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz)) ltac:(gres; rwH; unfold v_add; unorm; f_equal; nia).
                mldq F_64b30 D_64b30 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)%Z Ri.
                stepb_tk F_64b34 D_64b34 ltac:(cond).
                stepiv F_64af8 D_64af8 (Z_to_bv 64 (i + 1)) ltac:(wval).
                stepsv F_64afc D_64afc (Z_to_bv 64 0) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
                stepb_ft F_64b00 D_64b00 ltac:(cond).
                apply mst_refl.
             ++ split; [unfold gi_inv; post | kp].
          -- eexists. split.
             ++ stepiv F_64b04 D_64b04 (Z_to_bv 64 (flb + i)) ltac:(wval).
                chain_step; [reflexivity | eapply step_lbu; [exact F_64b08 | reflexivity | exact D_64b08 | maddr (flb + i)%Z; exact Fi] | step_simpl; vnorm].
                stepb_ft F_64b0c D_64b0c ltac:(rewrite (u_Z2bv8 (flag i)) by lia; cond).
                mldq F_64b10 D_64b10 (fs + 88)%Z HL.
                stepn F_64b14 D_64b14.
                stepsv F_64b18 D_64b18 (Z_to_bv 64 (c * 2 ^ 20)) ltac:(gres; rwH; apply v_sll_lit; lia).
                stepn F_64b1c D_64b1c.
                stepiv F_64b20 D_64b20 (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20)) ltac:(wval).
                stepiv F_64b24 D_64b24 (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20 + 32768)) ltac:(wval).
                stepsv F_64b28 D_64b28 (Z_to_bv 64 (i * frsz)) ltac:(gres; rwH; rewrite v_sll_lit by lia; rewrite <- Hfrsz; reflexivity).
                stepiv F_64b2c D_64b2c (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz)) ltac:(gres; rwH; unfold v_add; unorm; f_equal; nia).
                mldq F_64b30 D_64b30 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)%Z Ri.
                stepb_ft F_64b34 D_64b34 ltac:(cond).
                stepb_tk F_64b38 D_64b38 ltac:(cond).
                stepiv F_64af8 D_64af8 (Z_to_bv 64 (i + 1)) ltac:(wval).
                stepsv F_64afc D_64afc (Z_to_bv 64 0) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
                stepb_ft F_64b00 D_64b00 ltac:(cond).
                apply mst_refl.
             ++ split; [unfold gi_inv; post | kp].
      + cbv beta. intros r1 (I1 & K1).
        destruct (IH r1 (i + 1)%Z I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN | split; [exact P2 |]].
        intros r N10 N11 N12 N27. rewrite (K2 r N10 N11 N12 N27). apply K1; assumption.
  Qed.
End INNER.

Definition gc_facts (c nfr frsz k1 : Z) : Prop :=
  nfr = (2 ^ (14 - c))%Z /\ frsz = (2 ^ (6 + c))%Z /\ (64 * 2 ^ c = frsz)%Z /\ (32 * k1 = 32768 - 2 * nfr)%Z /\ (0 <= k1 < 1024)%Z
  /\ Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (18446744073709551615 * 2 ^ (10 - c)))) 1023) = Z_to_bv 64 k1.

Lemma gc_facts_all : forall c, (0 <= c <= 10)%Z -> exists nfr frsz k1, gc_facts c nfr frsz k1.
Proof.
  intros c Hc.
  assert (E : (c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10)%Z) by lia.
  exists (2 ^ (14 - c))%Z, (2 ^ (6 + c))%Z, (1024 - 2 ^ (10 - c))%Z. unfold gc_facts.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    repeat split; first [reflexivity | apply bv_eq; vm_compute; reflexivity | vm_compute; first [reflexivity | discriminate]].
Qed.

Lemma swrap32_small : forall z, (- 2 ^ 31 <= z < 2 ^ 31)%Z -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
  rewrite Z.mod_small; lia.
Qed.

Section CLASS.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables t fs sparg bot : Z.
  Variables flag rs : Z -> Z -> Z.
  Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Hfs : (0x6b4000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
  Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.

  Hypothesis HCF : forall M, (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M x = mem0 x) ->
    rdn ASEGS M (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))
    /\ (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z ->
          rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z)
    /\ (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z -> flag c i <> 0%Z ->
          rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * 2 ^ (6 + c) + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i)))
          /\ (0 <= rs c i < 2 ^ 64)%Z /\ (rs c i <= bot \/ sparg <= rs c i)%Z).

  Definition gcl_inv (rg : bvmap 5 word) (c : Z) : Prop :=
    getr rg 20 = Z_to_bv 64 c /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096)
    /\ getr rg 18 = Z_to_bv 64 bot /\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 2 = Z_to_bv 64 (t - 144).
  Definition gcl_keeps (regs regs' : bvmap 5 word) : Prop :=
    forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 27%bv -> r <> 21%bv -> r <> 24%bv -> r <> 19%bv -> r <> 20%bv -> getr regs' r = getr regs r.
  Definition out_gc (M : word -> option byte) : Prop := forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M x = mem0 x.

  Definition slot32 (M M' : word -> option byte) : Prop := forall x : word, ~ (t - 112 <= bv_unsigned x < t - 104)%Z -> M' x = M x.

  #[local] Ltac hide_dj := try hide Hfs.
  #[local] Ltac kp8 := intros r; intros; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

  Lemma gc_class_run : forall regs M c,
    gcl_inv regs c -> (0 <= c <= 10)%Z -> out_gc M -> mem_grows mem0 M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x64ae8 : word) M rom) (mkst regs' (0x64adc : word) M' rom)
      /\ gcl_inv regs' c /\ gcl_keeps regs regs' /\ out_gc M' /\ mem_grows mem0 M' /\ slot32 M M'.
  Proof.
    hide_dj.
    intros regs M c (H20 & H25 & H7 & H8 & H18 & H9 & H2) Hc HO HG.
    destruct (gc_facts_all c Hc) as (nfr & frsz & k1 & (Fn & Ff & Ff2 & Fk & Fk1 & Fand)).
    assert (Nb : (16 <= nfr <= 16384)%Z).
    { rewrite Fn. split; [change 16%Z with (2 ^ 4)%Z | change 16384%Z with (2 ^ 14)%Z]; apply Z.pow_le_mono_r; lia. }
    assert (Fb : (64 <= frsz <= 65536)%Z).
    { rewrite Ff. split; [change 64%Z with (2 ^ 6)%Z | change 65536%Z with (2 ^ 16)%Z]; apply Z.pow_le_mono_r; lia. }
    unhide Hfs. destruct Hfs as (Fs1 & Fs2 & Fs3). hide Fs3.
    destruct (HCF M HO) as (CL & _).
    set (M' := wbytes M (Z_to_bv 64 (t - 112)) (word_to_le_bytes 8 (Z_to_bv 64 frsz))).
    assert (HO' : out_gc M') by (intros x Hx; unfold M'; pose proof (u64_range x);
      destruct Hx as [Hx|Hx]; [rewrite wbytes_below; [apply HO; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]
                           | rewrite wbytes_above; [apply HO; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]]).
    destruct (HCF M' HO') as (CL' & CF' & CR').
    assert (exists flb, flb = fs + 4096 + 32768 - 2 * nfr)%Z as (flb & Hflb) by (eexists; reflexivity).
    assert (GM' : mem_grows mem0 M') by (unfold M'; eapply mem_grows_trans; [exact HG | apply wbytes_grows]).

    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x64ae8 : word) M rom) (mkst r1 (0x64b4c : word) M' rom)
              /\ (gi_inv fs c (14 - c) flb sparg bot r1 0 /\ getr r1 2 = Z_to_bv 64 (t - 144) /\ gcl_keeps regs r1)).
    { eexists. split.
      - stepn F_64aa0 D_64aa0.
        mldq F_64aa4 D_64aa4 (fs + 88)%Z CL.
        stepn F_64aa8 D_64aa8.
        stepsv F_64aac D_64aac (Z_to_bv 64 (10 - c)) ltac:(gres; rwH; unfold v_subw; unorm; rewrite swrap32_small by lia; reflexivity).
        stepiv F_64ab0 D_64ab0 (Z_to_bv 64 (6 + c)) ltac:(wval).
        stepiv F_64ab4 D_64ab4 (Z_to_bv 64 18446744073709551615) ltac:(gres; apply bv_eq; vm_compute; reflexivity).
        stepsv F_64ab8 D_64ab8 (Z_to_bv 64 (18446744073709551615 * 2 ^ (10 - c))) ltac:(gres; rwH; apply v_sll_lit; lia).
        stepiv F_64abc D_64abc (Z_to_bv 64 k1) ltac:(gres; rwH; unfold v_andi; change (bv_wrap 64 1023) with 1023%Z; exact Fand).
        stepn F_64ac0 D_64ac0.
        stepiv F_64ac4 D_64ac4 (Z_to_bv 64 (20 - c)) ltac:(wval).
        stepsv F_64ac8 D_64ac8 (Z_to_bv 64 (32 * k1)) ltac:(gres; rwH; rewrite v_sll_lit by lia; change (2 ^ 5)%Z with 32%Z; f_equal; lia).
        stepiv F_64acc D_64acc (Z_to_bv 64 (14 - c)) ltac:(wval).
        stepiv F_64ad0 D_64ad0 (Z_to_bv 64 flb) ltac:(wval).
        stepn F_64ad4 D_64ad4.
        stepsv F_64ad8 D_64ad8 (Z_to_bv 64 frsz) ltac:(gres; rwH; rewrite v_sll_lit by lia; rewrite Ff2; reflexivity).
        stepsdq F_64adc D_64adc (Z_to_bv 64 (t - 112)) (Z_to_bv 64 frsz)
          ltac:(apply (store_ok_mono _ _ mem0); [exact HG|];
                apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (t - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
        change (wbytes M (Z_to_bv 64 (t - 112)) (word_to_le_bytes 8 (Z_to_bv 64 frsz))) with M'.
        stepn F_64ae0 D_64ae0.
        apply mst_refl.
      - split; [unfold gi_inv; post | split; [gres; rwH; reflexivity | unfold gcl_keeps; kp8]]. }
    destruct S1 as (r1 & RUN1 & I1 & X1 & K1).

    assert (HF' : forall i, (0 <= i < nfr)%Z -> rdn ASEGS M' (Z_to_bv 64 (flb + i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z).
    { intros i Hi. replace (flb + i)%Z with (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)%Z by (rewrite <- Fn; lia).
      apply CF'; [exact Hc | rewrite <- Fn; exact Hi]. }
    assert (HR' : forall i, (0 <= i < nfr)%Z -> flag c i <> 0%Z ->
              rdn ASEGS M' (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i)))
              /\ (0 <= rs c i < 2 ^ 64)%Z /\ (rs c i <= bot \/ sparg <= rs c i)%Z).
    { intros i Hi Hf. rewrite Ff. apply CR'; [exact Hc | rewrite <- Fn; exact Hi | exact Hf]. }
    pose proof (gc_inner_run M' rom fs c nfr (14 - c) frsz flb sparg bot (flag c) (rs c) Hc eq_refl Fn Ff Hflb (conj Fs1 Fs2) Hsp CL' HF' HR'
                  (Z.to_nat (nfr - 1)) r1 0 I1 ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r2 & RUN2 & I2 & K2).
    exists r2, M'. split; [| split; [| split; [| split; [exact HO' | split; [exact GM' |]]]]].
    - eapply msteps_trans; [exact RUN1 | exact RUN2].
    - destruct I2 as (J27 & J24 & J25 & J20 & J7 & J8 & J21 & J18 & J9 & J19). unfold gcl_inv.
      repeat split; try assumption. rewrite (K2 2%bv) by (intros E; discriminate E). exact X1.
    - intros r N10 N11 N12 N27 N21 N24 N19 N20. rewrite (K2 r N10 N11 N12 N27). apply K1; assumption.
    - intros x Hx. unfold M'. pose proof (u64_range x).
      destruct (Z.lt_ge_cases (bv_unsigned x) (t - 112)) as [L|G].
      + rewrite wbytes_below; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
      + rewrite wbytes_above; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.

  Lemma gc_classes_run : forall (q : nat) regs M c,
    gcl_inv regs c -> (0 <= c)%Z -> (c + Z.of_nat q = 10)%Z -> out_gc M -> mem_grows mem0 M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x64ae8 : word) M rom) (mkst regs' (0x64cc0 : word) M' rom)
      /\ getr regs' 25 = Z_to_bv 64 fs /\ getr regs' 2 = Z_to_bv 64 (t - 144) /\ gcl_keeps regs regs' /\ out_gc M' /\ mem_grows mem0 M' /\ slot32 M M'.
  Proof.
    hide_dj.
    induction q as [|q IH]; intros regs M c HI Hc Hq HO HG.
    - destruct (gc_class_run regs M c HI ltac:(lia) HO HG) as (r1 & M1 & RUN1 & I1 & K1 & O1 & G1 & S1).
      destruct I1 as (H20 & H25 & H7 & H8 & H18 & H9 & H2).
      eexists. exists M1. split; [| split; [| split; [| split; [| split; [exact O1 | split; [exact G1 | exact S1]]]]]].
      + eapply msteps_trans; [exact RUN1|].
        stepiv F_64a94 D_64a94 (Z_to_bv 64 11) ltac:(wval).
        stepn F_64a98 D_64a98.
        stepb_tk F_64a9c D_64a9c ltac:(cond).
        apply mst_refl.
      + gres. exact H25.
      + gres. exact H2.
      + unfold gcl_keeps. intros r; intros. repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]).
        apply K1; assumption.
    - destruct (gc_class_run regs M c HI ltac:(lia) HO HG) as (r1 & M1 & RUN1 & I1 & K1 & O1 & G1 & S1).
      destruct I1 as (H20 & H25 & H7 & H8 & H18 & H9 & H2).
      assert (S2 : exists r2, msteps ASEGS (mkst r1 (0x64adc : word) M1 rom) (mkst r2 (0x64ae8 : word) M1 rom)
                /\ (gcl_inv r2 (c + 1) /\ gcl_keeps r1 r2)).
      { eexists. split.
        - stepiv F_64a94 D_64a94 (Z_to_bv 64 (c + 1)) ltac:(wval).
          stepn F_64a98 D_64a98.
          stepb_ft F_64a9c D_64a9c ltac:(cond).
          apply mst_refl.
        - split; [unfold gcl_inv; post | unfold gcl_keeps; kp8]. }
      destruct S2 as (r2 & RUN2 & I2 & K2).
      destruct (IH r2 M1 (c + 1)%Z I2 ltac:(lia) ltac:(lia) O1 G1) as (r3 & M3 & RUN3 & J25 & J2 & K3 & O3 & G3 & S3).
      exists r3, M3. split; [| split; [exact J25 | split; [exact J2 | split; [| split; [exact O3 | split; [exact G3 |]]]]]].
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3].
      + intros r; intros. rewrite (K3 r) by assumption. rewrite (K2 r) by assumption. apply K1; assumption.
      + intros x Hx. rewrite (S3 x Hx). apply S1, Hx.
  Qed.
End CLASS.

Section WHOLE.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables t fs sparg tpv key tsd ctx th top botth g48 g50 g58 g60 g40 g35 : Z.
  Variables flag rs : Z -> Z -> Z.
  Hypothesis Hs_def : bv_unsigned sp = t.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 80 <= 2 ^ 64)%Z.
  Hypothesis Htop : (botth < top)%Z /\ (0 <= botth)%Z /\ (top < 2 ^ 64)%Z /\ (botth <= sparg <= top)%Z.
  Hypothesis Hfs : (0x6b4000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = true.
  Hypothesis Hg : (0 <= g48 < 2 ^ 64)%Z /\ (0 <= g50 < 2 ^ 64)%Z /\ (0 <= g58 < 2 ^ 64)%Z /\ (0 <= g60 < 2 ^ 64)%Z /\ (0 <= g40 < 2 ^ 64)%Z /\ (0 <= g35 < 2 ^ 64)%Z.

  Hypothesis HC : forall M', (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x) ->
     rdn ASEGS M' (0x15d560 : word) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0x15d564 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
     rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\
     rdn ASEGS M' (0x154500 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g48)) /\
     rdn ASEGS M' (0x154508 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g50)) /\
     rdn ASEGS M' (0x154510 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g58)) /\
     rdn ASEGS M' (0x154518 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g60)) /\
     rdn ASEGS M' (0x1544f8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\
     rdn ASEGS M' (0x103a8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35)) /\
     rdn ASEGS M' (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)) /\
     (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z ->
          rdn ASEGS M' (Z_to_bv 64 (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z) /\
     (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z -> flag c i <> 0%Z ->
          rdn ASEGS M' (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * 2 ^ (6 + c) + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i)))
          /\ (0 <= rs c i < 2 ^ 64)%Z /\ (rs c i <= botth \/ sparg <= rs c i)%Z).

  #[local] Ltac hide_dj := try hide Hfs.
  Lemma sp_sg : sp = Z_to_bv 64 t.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Definition F13 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (t - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (t - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (t - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (t - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (t - 56)) (word_to_le_bytes 8 (getr rg 21)))
      (Z_to_bv 64 (t - 64)) (word_to_le_bytes 8 (getr rg 22)))
      (Z_to_bv 64 (t - 72)) (word_to_le_bytes 8 (getr rg 23)))
      (Z_to_bv 64 (t - 80)) (word_to_le_bytes 8 (getr rg 24)))
      (Z_to_bv 64 (t - 88)) (word_to_le_bytes 8 (getr rg 25)))
      (Z_to_bv 64 (t - 96)) (word_to_le_bytes 8 (getr rg 26)))
      (Z_to_bv 64 (t - 104)) (word_to_le_bytes 8 (getr rg 27)).

  Theorem gc_run : forall regs,
    getr regs 10 = Z_to_bv 64 fs -> getr regs 11 = Z_to_bv 64 sparg -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mj,
      msteps ASEGS (mkst regs (0x64a18 : word) mem0 rom) (mkst regs' ra (wbytes Mj (Z_to_bv 64 (fs + 96)) [Z_to_bv 8 0]) rom)
      /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> Mj x = mem0 x) /\ mem_grows mem0 Mj.
  Proof.
    hide_dj.
    intros regs H10 H11 H4 H2 H1. rewrite sp_sg in H2.
    destruct Ht as [Ta Tb]. destruct Hth as [Th1 Th2]. destruct Htop as (Tp1 & Tp2 & Tp3 & Tp4).
    unhide Hfs. destruct Hfs as (Fs1 & Fs2 & Fs3). hide Fs3.
    assert (Hra : ret_ok (0x64a5c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    #[local] Ltac oout := intros x Hx; pose proof (u64_range x);
       destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
                              | rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
    #[local] Ltac sok := apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); first [apply mem_grows_refl | assumption] |];
                        apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (t - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia].
    assert (O13 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> F13 regs x = mem0 x) by (unfold F13; oout).
    assert (G13 : mem_grows mem0 (F13 regs)) by (unfold F13; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).

    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x64a18 : word) mem0 rom) (mkst r1 (0x8ae84 : word) (F13 regs) rom)
              /\ (getr r1 9 = Z_to_bv 64 sparg /\ getr r1 25 = Z_to_bv 64 fs /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 2 = Z_to_bv 64 (t - 144)
                  /\ getr r1 1 = (0x64a5c : word) /\ keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv regs r1)).
    { unfold F13. eexists. split.
      - stepiv F_649d0 D_649d0 (Z_to_bv 64 (t - 144)) ltac:(wval).
        stepsd F_649d4 D_649d4 (Z_to_bv 64 (t - 8)) ra ltac:(sok).
        stepsd F_649d8 D_649d8 (Z_to_bv 64 (t - 16)) (getr regs 8) ltac:(sok).
        stepsd F_649dc D_649dc (Z_to_bv 64 (t - 24)) (getr regs 9) ltac:(sok).
        stepsd F_649e0 D_649e0 (Z_to_bv 64 (t - 32)) (getr regs 18) ltac:(sok).
        stepsd F_649e4 D_649e4 (Z_to_bv 64 (t - 40)) (getr regs 19) ltac:(sok).
        stepsd F_649e8 D_649e8 (Z_to_bv 64 (t - 48)) (getr regs 20) ltac:(sok).
        stepsd F_649ec D_649ec (Z_to_bv 64 (t - 56)) (getr regs 21) ltac:(sok).
        stepsd F_649f0 D_649f0 (Z_to_bv 64 (t - 64)) (getr regs 22) ltac:(sok).
        stepsd F_649f4 D_649f4 (Z_to_bv 64 (t - 72)) (getr regs 23) ltac:(sok).
        stepsd F_649f8 D_649f8 (Z_to_bv 64 (t - 80)) (getr regs 24) ltac:(sok).
        stepsd F_649fc D_649fc (Z_to_bv 64 (t - 88)) (getr regs 25) ltac:(sok).
        stepsd F_64a00 D_64a00 (Z_to_bv 64 (t - 96)) (getr regs 26) ltac:(sok).
        stepsd F_64a04 D_64a04 (Z_to_bv 64 (t - 104)) (getr regs 27) ltac:(sok).
        stepiv F_64a08 D_64a08 (Z_to_bv 64 sparg) ltac:(wval).
        stepiv F_64a0c D_64a0c (Z_to_bv 64 fs) ltac:(wval).
        stepn F_64a10 D_64a10.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q9 & Q25 & Q4 & Q2 & Q1 & K1).

    destruct (get_current_thread_run r1 (F13 regs) rom (0x64a5c : word) (t - 144) tpv key tsd ctx th Q2 Q4 Q1 Hra ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
                ltac:(replace (t - 144 - 16)%Z with (t - 160)%Z by lia; unfold F13; sok)) as (r2 & RUN2 & T10 & T2 & T1 & K2).
    { intros M' HM'. assert (O' : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x).
      { intros x Hx. rewrite (HM' x) by lia. apply O13. exact Hx. }
      destruct (HC M' O') as (C1 & C2 & C3 & C4 & C5 & _). repeat split; assumption. }
    set (M14 := wbytes (F13 regs) (Z_to_bv 64 (t - 144 - 8)) (word_to_le_bytes 8 (0x64a5c : word))) in RUN2.
    assert (O14 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M14 x = mem0 x).
    { intros x Hx. rewrite <- (O13 x Hx). unfold M14. revert x Hx. oout. }
    assert (G14 : mem_grows mem0 M14) by (unfold M14; eapply mem_grows_trans; [exact G13 | apply wbytes_grows]).
    assert (T9 : getr r2 9 = Z_to_bv 64 sparg) by (rewrite (K2 9%bv) by (cbv; intuition discriminate); exact Q9).
    assert (T25 : getr r2 25 = Z_to_bv 64 fs) by (rewrite (K2 25%bv) by (cbv; intuition discriminate); exact Q25).
    assert (T4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (K2 4%bv) by (cbv; intuition discriminate); exact Q4).
    destruct (HC M14 O14) as (_ & _ & _ & _ & _ & D40 & D8 & D16 & E48 & E50 & _).
    set (M15 := wbytes M14 (Z_to_bv 64 (t - 120)) (word_to_le_bytes 8 (Z_to_bv 64 g50))).
    set (M16 := wbytes M15 (Z_to_bv 64 (t - 128)) (word_to_le_bytes 8 (Z_to_bv 64 g58))).
    set (M17 := wbytes M16 (Z_to_bv 64 (t - 136)) (word_to_le_bytes 8 (Z_to_bv 64 g60))).
    set (M18 := wbytes M17 (Z_to_bv 64 (t - 144)) (word_to_le_bytes 8 (Z_to_bv 64 g40))).
    assert (O15 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M15 x = mem0 x) by (intros x Hx; rewrite <- (O14 x Hx); unfold M15; revert x Hx; oout).
    assert (O16 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M16 x = mem0 x) by (intros x Hx; rewrite <- (O15 x Hx); unfold M16; revert x Hx; oout).
    assert (O17 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M17 x = mem0 x) by (intros x Hx; rewrite <- (O16 x Hx); unfold M17; revert x Hx; oout).
    assert (O18 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M18 x = mem0 x) by (intros x Hx; rewrite <- (O17 x Hx); unfold M18; revert x Hx; oout).
    assert (G18 : mem_grows mem0 M18) by (unfold M18, M17, M16, M15; do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); exact G14).
    destruct (HC M15 O15) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E58 & _).
    destruct (HC M16 O16) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E60 & _).
    destruct (HC M17 O17) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E40 & _).
    destruct (HC M18 O18) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E35 & _).

    assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x64a5c : word) M14 rom) (mkst r3 (0x64ae8 : word) M18 rom)
              /\ (gcl_inv t fs sparg botth r3 0 /\ keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv r2 r3)).
    { eexists. split.
      - stepb_ft F_64a14 D_64a14 ltac:(cond).
        stepiv F_64a18 D_64a18 (Z_to_bv 64 th) ltac:(wval).
        stepn F_64a1c D_64a1c.
        mlbq F_8b000 D_8b000 (th + 40)%Z D40.
        stepfence F_8b004 D_8b004.
        stepb_tk F_8b008 D_8b008 ltac:(rwH; cbn; cond).
        mldq F_8b040 D_8b040 (th + 8)%Z D8.
        mldq F_8b044 D_8b044 (th + 16)%Z D16.
        stepov F_8b048 D_8b048 (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
        stepn F_8b04c D_8b04c.
        stepov F_8b050 D_8b050 (Z_to_bv 64 top) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).
        stepret F_8b054 D_8b054 (0x64a68 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        stepiv F_64a20 D_64a20 (Z_to_bv 64 top) ltac:(wval).
        stepiv F_64a24 D_64a24 (Z_to_bv 64 th) ltac:(wval).
        stepn F_64a28 D_64a28.
        mlbq F_8b058 D_8b058 (th + 40)%Z D40.
        stepfence F_8b05c D_8b05c.
        stepb_tk F_8b060 D_8b060 ltac:(rwH; cbn; cond).
        mldq F_8b098 D_8b098 (th + 8)%Z D8.
        mldq F_8b09c D_8b09c (th + 16)%Z D16.
        stepov F_8b0a0 D_8b0a0 (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
        stepn F_8b0a4 D_8b0a4.
        stepov F_8b0a8 D_8b0a8 (Z_to_bv 64 botth) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm; rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).
        stepret F_8b0ac D_8b0ac (0x64a74 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        stepb_ft F_64a2c D_64a2c ltac:(cond).
        stepiv F_64a30 D_64a30 (Z_to_bv 64 botth) ltac:(wval).
        stepb_ft F_64a34 D_64a34 ltac:(cond).
        stepn F_64a38 D_64a38.
        stepn F_64a3c D_64a3c.
        stepn F_64a40 D_64a40.
        stepn F_64a44 D_64a44.
        stepn F_64a48 D_64a48.
        stepn F_64a4c D_64a4c.
        stepn F_64a50 D_64a50.
        stepn F_64a54 D_64a54.
        stepiv F_64a58 D_64a58 (Z_to_bv 64 (fs + 4096)) ltac:(wval).
        mld F_64a5c D_64a5c (0x154500 : word) E48.
        mld F_64a60 D_64a60 (0x154508 : word) E50.
        stepsdq F_64a64 D_64a64 (Z_to_bv 64 (t - 120)) (Z_to_bv 64 g50) ltac:(unfold M14, F13; sok).
        change (wbytes M14 (Z_to_bv 64 (t - 120)) (word_to_le_bytes 8 (Z_to_bv 64 g50))) with M15.
        mld F_64a68 D_64a68 (0x154510 : word) E58.
        stepsdq F_64a6c D_64a6c (Z_to_bv 64 (t - 128)) (Z_to_bv 64 g58) ltac:(unfold M15, M14, F13; sok).
        change (wbytes M15 (Z_to_bv 64 (t - 128)) (word_to_le_bytes 8 (Z_to_bv 64 g58))) with M16.
        mld F_64a70 D_64a70 (0x154518 : word) E60.
        stepsdq F_64a74 D_64a74 (Z_to_bv 64 (t - 136)) (Z_to_bv 64 g60) ltac:(unfold M16, M15, M14, F13; sok).
        change (wbytes M16 (Z_to_bv 64 (t - 136)) (word_to_le_bytes 8 (Z_to_bv 64 g60))) with M17.
        mld F_64a78 D_64a78 (0x1544f8 : word) E40.
        stepsdq F_64a7c D_64a7c (Z_to_bv 64 (t - 144)) (Z_to_bv 64 g40) ltac:(unfold M17, M16, M15, M14, F13; sok).
        change (wbytes M17 (Z_to_bv 64 (t - 144)) (word_to_le_bytes 8 (Z_to_bv 64 g40))) with M18.
        mld F_64a80 D_64a80 (0x103a8 : word) E35.
        stepn F_64a84 D_64a84.
        stepn F_64a88 D_64a88.
        stepn F_64a8c D_64a8c.
        stepn F_64a90 D_64a90.
        apply mst_refl.
      - split; [unfold gcl_inv; post | solve_keeps_but]. }
    destruct S3 as (r3 & RUN3 & I3 & K3).

    assert (HCF' : forall M, (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M x = mem0 x) ->
      rdn ASEGS M (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))
      /\ (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z ->
            rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z)
      /\ (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z -> flag c i <> 0%Z ->
            rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * 2 ^ (6 + c) + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i)))
            /\ (0 <= rs c i < 2 ^ 64)%Z /\ (rs c i <= botth \/ sparg <= rs c i)%Z)).
    { intros M HM. destruct (HC M HM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C15 & C16 & C17). split; [exact C15 | split; [exact C16 | exact C17]]. }
    unhide Fs3.
    pose proof (gc_classes_run mem0 rom t fs sparg botth flag rs) as GCL.
    repeat lazymatch type of GCL with
      | forall q : nat, _ => fail
      | ?P -> _ => let H := fresh in assert (H : P) by (first [exact Hok | exact HCF' | lia]); specialize (GCL H); clear H
      end.
    destruct (GCL 10%nat r3 M18 0%Z I3 ltac:(lia) eq_refl O18 G18) as (r4 & M4 & RUN4 & J25 & J2 & K4 & O4 & G4 & S4). clear GCL.
    set (M5 := wbytes M4 (Z_to_bv 64 (fs + 96)) [Z_to_bv 8 0]).

    assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18 \/ k = 40 /\ v = getr regs 19 \/ k = 48 /\ v = getr regs 20 \/ k = 56 /\ v = getr regs 21 \/ k = 64 /\ v = getr regs 22 \/ k = 72 /\ v = getr regs 23 \/ k = 80 /\ v = getr regs 24 \/ k = 88 /\ v = getr regs 25 \/ k = 96 /\ v = getr regs 26 \/ k = 104 /\ v = getr regs 27)%Z ->
                 rdn ASEGS M5 (Z_to_bv 64 (t - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v Hk. assert (Hk' : (8 <= k <= 104)%Z) by lia.
      rewrite (rdn_ext ASEGS 8 M5 (F13 regs)); [| unorm; cbn; lia |].
      - unfold F13. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]]]]]];
          repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ]);
          apply rdn_wbytes_hit8; unorm; lia.
      - intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. pose proof (u64_range x).
        unfold M5. rewrite wbytes_out_any_gc; [| cbn [length Z.of_nat Pos.to_nat]; unorm; lia | cbn [length Z.of_nat Pos.to_nat]; unorm; lia].
        rewrite (S4 x) by lia.
        unfold M18, M17, M16, M15, M14. rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]. }
    #[local] Ltac slv := first [split; reflexivity | left; split; reflexivity | right; slv].
    eexists. exists M4. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (fs + 96)) (b := Z_to_bv 8 0);
          [exact F_64c78 | reflexivity | exact D_64c78 | wval | gres; reflexivity | apply bv_eq; vm_compute; reflexivity
          | apply (store_ok_mono _ _ mem0 M4 _ G4); exact Hwfs ] | step_simpl; vnorm].
      change (wbytes M4 (Z_to_bv 64 (fs + 96)) [Z_to_bv 8 0]) with M5.
      stepld F_64c7c D_64c7c (ra) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 8)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64c80 D_64c80 (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 16)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64c84 D_64c84 (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 24)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64c88 D_64c88 (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 32)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64c8c D_64c8c (getr regs 19) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 40)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64c90 D_64c90 (getr regs 20) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 48)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64c94 D_64c94 (getr regs 21) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 56)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64c98 D_64c98 (getr regs 22) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 64)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64c9c D_64c9c (getr regs 23) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 72)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64ca0 D_64ca0 (getr regs 24) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 80)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64ca4 D_64ca4 (getr regs 25) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 88)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64ca8 D_64ca8 (getr regs 26) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 96)) by (symmetry; wval) end; apply SL; slv).
      stepld F_64cac D_64cac (getr regs 27) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 104)) by (symmetry; wval) end; apply SL; slv).
      stepiv F_64cb0 D_64cb0 (Z_to_bv 64 t) ltac:(wval).
      stepret F_64cb4 D_64cb4 ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - split; [gres; symmetry; apply sp_sg|]. split; [gres; reflexivity|]. split; [| split; [exact O4 | exact G4]].
      intros r Hcs. cbv in Hcs.
      destruct Hcs as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]; gres;
        first [ reflexivity | rewrite H1; reflexivity | rewrite H2; reflexivity
              | rewrite (K4 _) by (intros E; discriminate E); rewrite (K3 _) by (cbv; intuition discriminate);
                rewrite (K2 _) by (cbv; intuition discriminate); rewrite (K1 _) by (cbv; intuition discriminate); reflexivity ].
  Qed.
End WHOLE.
End FPX_1.
