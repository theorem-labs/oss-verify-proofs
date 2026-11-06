(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefReadLib RefEnframeArith.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound   AsanRegionPoisoned AsanReadCheck.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import Asan_code_75000_76000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := ImgA.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPW_0. Context {fx : PropExec.FPState}.

Lemma rd1_of_rdn1 : forall m (a : word) c, rdn SEGS m a 1 = Some [c] -> AxSymExec3Sound.AX2S.rd1 SEGS m a <> None.
Proof.
  intros m a c H. unfold AxSymExec3Sound.AX2S.rd1. cbn [rdn] in H.
  destruct (match m a with Some b => Some b | None => seg_rom SEGS a end); [discriminate | discriminate].
Qed.

(* [comment removed for export] *)
Lemma rdn8_of_bytes : forall m (a : Z),
  (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  (forall j, (0 <= j < 8)%Z -> exists c, rdn SEGS m (Z_to_bv 64 (a + j)) 1 = Some [c]) ->
  exists bs (v : word), rdn SEGS m (Z_to_bv 64 a) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v.
Proof.
  intros m a Ha Ha8 Hb.
  destruct (AxSymExec3Sound.AX2S.rdn_defined SEGS m 8 (Z_to_bv 64 a) ltac:(rewrite zbv_u by lia; lia)) as (bs & Hbs & Hlen).
  { intros j Hj. rewrite zbv_u by lia. destruct (Hb (Z.of_nat j) ltac:(lia)) as [c Hc]. eapply rd1_of_rdn1. exact Hc. }
  exists bs, (Z_to_bv 64 (bytes_le_to_Z bs)). split; [exact Hbs|].
  pose proof (AxSymExec3Sound.AX2S.bytes_le_to_Z_bound bs) as B. rewrite Hlen in B. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B.
  rewrite zbv_u; [reflexivity | lia].
Qed.

Lemma v_andi_7 : forall z, (0 <= z < 2 ^ 64)%Z -> v_andi (Z_to_bv 64 z) 7 = Z_to_bv 64 (z mod 8).
Proof.
  intros z Hz. unfold v_andi. rewrite zbv_u by exact Hz. change (bv_wrap 64 7) with (Z.ones 3).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma v_andi_255_0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0.
Proof. apply bv_eq. reflexivity. Qed.

Lemma v_sltu_0_l : forall z, (0 <= z < 2 ^ 64)%Z -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 (if (0 <? z)%Z then 1 else 0).
Proof.
  intros z Hz. unfold v_sltu. rewrite c_ltu_zbv by lia. destruct (0 <? z)%Z; reflexivity.
Qed.

Lemma v_lb_small : forall (b : byte), (bv_unsigned b < 128)%Z -> v_lb b = Z_to_bv 64 (bv_unsigned b).
Proof. intros b Hb. unfold v_lb. rewrite bv_signed_small8 by exact Hb. reflexivity. Qed.

Lemma v_and_0_l : forall (x : word), v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof. intros x. unfold v_and. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.land_0_l. reflexivity. Qed.

Lemma v_and_1_0 : v_and (Z_to_bv 64 1) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. apply bv_eq. reflexivity. Qed.

Lemma v_xori_1_1 : v_xori (Z_to_bv 64 1) 1 = Z_to_bv 64 0.
Proof. apply bv_eq. reflexivity. Qed.

Lemma v_slt_small : forall a b, (0 <= a < 2 ^ 63)%Z -> (0 <= b < 2 ^ 63)%Z ->
  v_slt (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if (a <? b)%Z then 1 else 0).
Proof. intros a b Ha Hb. unfold v_slt. rewrite c_lts_zbv by assumption. destruct (a <? b)%Z; reflexivity. Qed.

(* [comment removed for export] *)
Lemma last_test_zero : forall (b1 : byte) (e : Z) (x : word),
  (0 <= e < 8)%Z ->
  (bv_unsigned b1 = 0 \/ e < bv_unsigned b1 < 128)%Z ->
  v_and (v_sltu (Z_to_bv 64 0) (v_lb b1)) (v_xori (v_slt (Z_to_bv 64 e) (v_lb b1)) 1) = Z_to_bv 64 0.
Proof.
  intros b1 e x He Hb1. pose proof (bv_unsigned_in_range 8 b1) as Hr. change (bv_modulus 8) with 256%Z in Hr.
  destruct Hb1 as [Hz | Hk].
  - rewrite v_lb_small by lia. rewrite Hz. rewrite (v_sltu_0_l 0) by lia. cbn [Z.ltb]. apply v_and_0_l.
  - rewrite v_lb_small by lia. rewrite v_sltu_0_l by lia. rewrite v_slt_small by lia.
    replace (0 <? bv_unsigned b1)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    replace (e <? bv_unsigned b1)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite v_xori_1_1. apply v_and_1_0.
Qed.
End FPW_0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.
Section QS.
  Variables (mem rom : word -> option byte) (beg n : Z) (b1 : byte).
  Hypothesis Hn : (1 <= n <= 64)%Z.
  Hypothesis Hbeg : (0 <= beg)%Z.
  Hypothesis Hbeg64 : (beg + 64 < 2 ^ 64)%Z.
  Hypothesis C1 : cell mem 0x129ea8 0x132278.
  Hypothesis C2 : cell mem 0x132278 SB.
  (* [comment removed for export] *)
  Definition s1 : Z := (SB + beg / 8)%Z.
  Definition s2 : Z := (SB + (beg + n - 1) / 8)%Z.
  (* [comment removed for export] *)
  Hypothesis Hrdw : forall a, (s1 / 8 * 8 <= a < s2 / 8 * 8 + 8)%Z -> exists c, rdn SEGS mem (Z_to_bv 64 a) 1 = Some [c].
  (* [comment removed for export] *)
  Hypothesis Hz : forall g, (beg / 8 <= g < (beg + n - 1) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0).
  Hypothesis Hlast : mem (Z_to_bv 64 (SB + (beg + n - 1) / 8)) = Some b1.
  Hypothesis Hb1 : (bv_unsigned b1 = 0 \/ (beg + n - 1) mod 8 < bv_unsigned b1 < 128)%Z.

  Lemma qs_arith :
    (0 <= s1)%Z /\ (s2 + 8 < 2 ^ 64)%Z /\ (s1 <= s2 <= s1 + 8)%Z
    /\ (s1 / 8 * 8 <= s1 < s1 / 8 * 8 + 8)%Z /\ (s2 / 8 * 8 <= s2 < s2 / 8 * 8 + 8)%Z /\ (s1 / 8 * 8 <= s2 / 8 * 8)%Z /\ (0 <= s1 / 8 * 8)%Z
    /\ (0 <= beg + n - 1 < 2 ^ 64)%Z /\ (0 <= (beg + n - 1) / 8 < 2 ^ 64)%Z /\ (0 <= beg / 8 < 2 ^ 64)%Z
    /\ (0 <= (beg + n - 1) mod 8 < 8)%Z.
  Proof.
    pose proof SB_val. unfold s1, s2, SB.
    pose proof (Z.div_le_mono beg (beg + n - 1) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (2147450880 + beg / 8) (2147450880 + (beg + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.mod_pos_bound (beg + n - 1) 8 ltac:(lia)). lia.
  Qed.

  Lemma rd_w : forall a, (s1 / 8 * 8 <= a)%Z -> (a + 8 <= s2 / 8 * 8 + 8)%Z ->
    exists bs (v : word), rdn SEGS mem (Z_to_bv 64 a) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v.
  Proof.
    intros a H1 H2. pose proof qs_arith. apply rdn8_of_bytes; [lia | lia |]. intros j Hj. apply Hrdw. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma qs_loop : forall k regs (c : Z),
    (s1 <= c < s2)%Z -> k = Z.to_nat (s2 - c) ->
    getr regs 13 = Z_to_bv 64 c -> getr regs 14 = Z_to_bv 64 s2 -> getr regs 15 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x75d38 : word) mem rom) (mkst regs' (0x75d48 : word) mem rom)
      /\ getr regs' 15 = Z_to_bv 64 0
      /\ (forall r, r <> 13 -> r <> 15 -> r <> 16 -> getr regs' r = getr regs r).
  Proof.
    pose proof qs_arith as QA.
    induction k as [|k IH]; intros regs c Hc Hk H13 H14 H15; [lia|].
    assert (Zc : mem (Z_to_bv 64 c) = Some (Z_to_bv 8 0)).
    { replace c with (SB + (c - SB))%Z by lia. apply Hz. unfold s1, s2 in Hc. lia. }
    assert (RDc : rdn SEGS mem (Z_to_bv 64 c) 1 = Some [Z_to_bv 8 0]) by (cbn [rdn]; rewrite Zc; reflexivity).
    destruct (Z.eq_dec (c + 1) s2) as [Hend | Hmore].
    - eexists. split; [|split].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_75d38 eq_refl D_75d38); gr; rewrite ?H13; zn; rewrite Z.add_0_r; exact RDc).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_75d3c eq_refl D_75d3c)). gr. rewrite H13. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_75d40 eq_refl D_75d40)). gr. rewrite H15.
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. rewrite v_or_zero.
        eapply mst_step; [reflexivity | eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_75d44 eq_refl D_75d44); gr; rewrite H14, Hend; br_eq |].
        step_simpl. imm_norm. apply mst_refl.
      + gr. reflexivity.
      + intros r N13 N15 N16. repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
    - edestruct (IH (regupd (regupd (regupd regs 16 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (c + 1))) 15 (Z_to_bv 64 0)) (c + 1)%Z)
        as (regs' & Hms & P15 & Pother); [lia | lia | gr; reflexivity | gr; exact H14 | gr; reflexivity |].
      exists regs'. split; [|split; [exact P15|]].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_75d38 eq_refl D_75d38); gr; rewrite ?H13; zn; rewrite Z.add_0_r; exact RDc).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_75d3c eq_refl D_75d3c)). gr. rewrite H13. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_75d40 eq_refl D_75d40)). gr. rewrite H15.
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. rewrite v_or_zero.
        eapply mst_step; [reflexivity | eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_75d44 eq_refl D_75d44); gr; rewrite H14; br_eq |].
        step_simpl. imm_norm. exact Hms.
      + intros r N13 N15 N16. rewrite (Pother r N13 N15 N16).
        repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
  Qed.

  Theorem qc_src_run : forall regs,
    getr regs 11 = Z_to_bv 64 beg -> getr regs 12 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 (beg + n) ->
    exists regs',
      msteps SEGS (mkst regs (0x75a2c : word) mem rom) (mkst regs' (0x75a64 : word) mem rom)
      /\ getr regs' 19 = Z_to_bv 64 (beg + n - 1)
      /\ (forall r, r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 -> r <> 19 -> getr regs' r = getr regs r).
  Proof.
    intros regs H11 H12 H19. pose proof SB_val as HSB.
    pose proof qs_arith as QA. destruct QA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
    destruct (rd_w (s1 / 8 * 8)%Z ltac:(lia) ltac:(lia)) as (bs1 & w1 & RD1 & V1).
    destruct (rd_w (s2 / 8 * 8)%Z ltac:(lia) ltac:(lia)) as (bs2 & w2 & RD2 & V2).
    (* [comment removed for export] *)
    assert (LINE : forall regs0,
      getr regs0 11 = Z_to_bv 64 beg -> getr regs0 12 = Z_to_bv 64 n -> getr regs0 19 = Z_to_bv 64 (beg + n) ->
      msteps SEGS (mkst regs0 (0x75a2c : word) mem rom)
        (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs0 13 (Z_to_bv 64 0x129a2c)) 13 (Z_to_bv 64 0x132278)) 14 (Z_to_bv 64 SB)) 19 (Z_to_bv 64 (beg + n - 1))) 13 (Z_to_bv 64 (beg / 8))) 15 (Z_to_bv 64 ((beg + n - 1) / 8))) 13 (Z_to_bv 64 s1)) 14 (Z_to_bv 64 s2)) 15 (Z_to_bv 64 (s1 / 8 * 8))) 16 (Z_to_bv 64 (s2 / 8 * 8))) 15 w1)
              (0x75a58 : word) mem rom)).
    { intros regs0 G11 G12 G19.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x129a2c) F_75a2c eq_refl D_75a2c);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_75a30 D_75a30 0x132278%Z C1 G11.
      mld F_75a34 D_75a34 SB C2 G11.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_75a38 eq_refl D_75a38)). gr. rewrite G19. zn.
      replace (beg + n + -1)%Z with (beg + n - 1)%Z by lia.
      (* [comment removed for export] *)
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_75a3c eq_refl D_75a3c)). gr. rewrite G11, (v_srli_3 beg) by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_75a40 eq_refl D_75a40)). gr. rewrite (v_srli_3 (beg + n - 1)) by lia.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_75a44 eq_refl D_75a44)). gr. rewrite v_add_zbv by lia. fold s1.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_75a48 eq_refl D_75a48)). gr. rewrite v_add_zbv by lia. fold s2.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_75a4c eq_refl D_75a4c)). gr. rewrite v_andi_m8 by lia.
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_75a50 eq_refl D_75a50)). gr. rewrite v_andi_m8 by lia.
      (* [comment removed for export] *)
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ w1 F_75a54 eq_refl D_75a54);
                   [ gr; zn; rewrite Z.add_0_r; exact RD1 | exact V1 ]).
      apply mst_refl. }
    (* [comment removed for export] *)
    destruct (bv_eq_dec 64 (v_or w2 w1) (Z_to_bv 64 0)) as [Hor | Hor].
    - (* [comment removed for export] *)
      eexists. split; [|split].
      + eapply msteps_trans; [apply (LINE regs H11 H12 H19)|].
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ w2 F_75a58 eq_refl D_75a58);
                     [ gr; zn; rewrite Z.add_0_r; exact RD2 | exact V2 ]).
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_75a5c eq_refl D_75a5c)). gr. rewrite Hor.
        eapply mst_step; [reflexivity | eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_75a60 eq_refl D_75a60); gr; rewrite getr_zero; reflexivity |].
        step_simpl. imm_norm. apply mst_refl.
      + gr. reflexivity.
      + intros r N13 N14 N15 N16 N17 N19. repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
    - (* [comment removed for export] *)
      assert (RDl : rdn SEGS mem (Z_to_bv 64 s2) 1 = Some [b1]) by (cbn [rdn]; unfold s2; rewrite Hlast; reflexivity).
      pose proof (last_test_zero b1 ((beg + n - 1) mod 8) (Z_to_bv 64 0) ltac:(lia) Hb1) as LT.
      set (regsA := (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 13 (Z_to_bv 64 0x129a2c)) 13 (Z_to_bv 64 0x132278)) 14 (Z_to_bv 64 SB)) 19 (Z_to_bv 64 (beg + n - 1))) 13 (Z_to_bv 64 (beg / 8))) 15 (Z_to_bv 64 ((beg + n - 1) / 8))) 13 (Z_to_bv 64 s1)) 14 (Z_to_bv 64 s2)) 15 (Z_to_bv 64 (s1 / 8 * 8))) 16 (Z_to_bv 64 (s2 / 8 * 8))) 15 w1) 16 w2) 15 (v_or w2 w1)) 15 (v_lb b1))).
      set (regsB := (regupd (regupd (regupd (regupd (regupd regsA 16 (Z_to_bv 64 ((beg + n - 1) mod 8))) 17 (v_sltu (Z_to_bv 64 0) (v_lb b1))) 15 (v_slt (Z_to_bv 64 ((beg + n - 1) mod 8)) (v_lb b1))) 15 (v_xori (v_slt (Z_to_bv 64 ((beg + n - 1) mod 8)) (v_lb b1)) 1)) 15 (Z_to_bv 64 0))).
      assert (PRE : msteps SEGS (mkst regs (0x75a2c : word) mem rom) (mkst regsB (0x75d34 : word) mem rom)).
      { eapply msteps_trans; [apply (LINE regs H11 H12 H19)|].
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ w2 F_75a58 eq_refl D_75a58);
                     [ gr; zn; rewrite Z.add_0_r; exact RD2 | exact V2 ]).
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_75a5c eq_refl D_75a5c)). gr.
        eapply mst_step; [reflexivity | eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_75a60 eq_refl D_75a60); gr; rewrite getr_zero;
                                        unfold c_eq; apply bv_eqb_neq; exact Hor |].
        step_simpl. imm_norm.
        (* [comment removed for export] *)
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_75d1c eq_refl D_75d1c); gr; zn; rewrite Z.add_0_r; exact RDl).
        (* [comment removed for export] *)
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_75d20 eq_refl D_75d20)). gr. rewrite v_andi_7 by lia.
        (* [comment removed for export] *)
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_75d24 eq_refl D_75d24)). gr. rewrite getr_zero.
        (* [comment removed for export] *)
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_75d28 eq_refl D_75d28)). gr.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_75d2c eq_refl D_75d2c)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_75d30 eq_refl D_75d30)). gr.
        change (Z_to_bv 64 0 : word) with (Z_to_bv 64 0) in LT. rewrite LT.
        apply mst_refl. }
      assert (B13 : getr regsB 13 = Z_to_bv 64 s1) by (unfold regsB, regsA; gr; reflexivity).
      assert (B14 : getr regsB 14 = Z_to_bv 64 s2) by (unfold regsB, regsA; gr; reflexivity).
      assert (B15 : getr regsB 15 = Z_to_bv 64 0) by (unfold regsB, regsA; gr; reflexivity).
      assert (B19 : getr regsB 19 = Z_to_bv 64 (beg + n - 1)) by (unfold regsB, regsA; gr; reflexivity).
      assert (Bother : forall r, r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 -> r <> 19 -> getr regsB r = getr regs r).
      { intros r N13 N14 N15 N16 N17 N19. unfold regsB, regsA.
        repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity. }
      (* [comment removed for export] *)
      destruct (Z.eq_dec s1 s2) as [Heq | Hne].
      + eexists. split; [|split].
        * eapply msteps_trans; [exact PRE|].
          eapply mst_step; [reflexivity | eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_75d34 eq_refl D_75d34); rewrite B13, B14, Heq; br_lt |].
          step_simpl. imm_norm.
          (* [comment removed for export] *)
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_75d48 eq_refl D_75d48)). rewrite B15, v_andi_255_0.
          eapply mst_step; [reflexivity | eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_75d4c eq_refl D_75d4c); gr; rewrite getr_zero; reflexivity |].
          step_simpl. imm_norm. apply mst_refl.
        * gr. exact B19.
        * intros r N13 N14 N15 N16 N17 N19. repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])).
          apply Bother; assumption.
      + destruct (qs_loop (Z.to_nat (s2 - s1)) regsB s1 ltac:(lia) eq_refl B13 B14 B15) as (regsL & HmsL & L15 & Lother).
        eexists. split; [|split].
        * eapply msteps_trans; [exact PRE|].
          eapply mst_step; [reflexivity | eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_75d34 eq_refl D_75d34); rewrite B13, B14; br_lt |].
          step_simpl. imm_norm.
          eapply msteps_trans; [exact HmsL|].
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_75d48 eq_refl D_75d48)). rewrite L15, v_andi_255_0.
          eapply mst_step; [reflexivity | eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_75d4c eq_refl D_75d4c); gr; rewrite getr_zero; reflexivity |].
          step_simpl. imm_norm. apply mst_refl.
        * gr. rewrite Lother by (intros E; discriminate E). exact B19.
        * intros r N13 N14 N15 N16 N17 N19. repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])).
          rewrite Lother by assumption. apply Bother; assumption.
  Qed.
End QS.
End FPW_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPW_2. Context {fx : PropExec.FPState}.
Section QD.
  Variables (mem rom : word -> option byte) (beg n : Z) (b1 : byte).
  Hypothesis Hn : (1 <= n <= 64)%Z.
  Hypothesis Hbeg : (0 <= beg)%Z.
  Hypothesis Hbeg64 : (beg + 64 < 2 ^ 64)%Z.
  Hypothesis C1 : cell mem 0x129ea8 0x132278.
  Hypothesis C2 : cell mem 0x132278 SB.
  (* [comment removed for export] *)
  Definition d1 : Z := (SB + beg / 8)%Z.
  Definition d2 : Z := (SB + (beg + n - 1) / 8)%Z.
  (* [comment removed for export] *)
  Hypothesis Hrdw : forall a, (d1 / 8 * 8 <= a < d2 / 8 * 8 + 8)%Z -> exists c, rdn SEGS mem (Z_to_bv 64 a) 1 = Some [c].
  (* [comment removed for export] *)
  Hypothesis Hz : forall g, (beg / 8 <= g < (beg + n - 1) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0).
  Hypothesis Hlast : mem (Z_to_bv 64 (SB + (beg + n - 1) / 8)) = Some b1.
  Hypothesis Hb1 : (bv_unsigned b1 = 0 \/ (beg + n - 1) mod 8 < bv_unsigned b1 < 128)%Z.

  Lemma qd_arith :
    (0 <= d1)%Z /\ (d2 + 8 < 2 ^ 64)%Z /\ (d1 <= d2 <= d1 + 8)%Z
    /\ (d1 / 8 * 8 <= d1 < d1 / 8 * 8 + 8)%Z /\ (d2 / 8 * 8 <= d2 < d2 / 8 * 8 + 8)%Z /\ (d1 / 8 * 8 <= d2 / 8 * 8)%Z /\ (0 <= d1 / 8 * 8)%Z
    /\ (0 <= beg + n - 1 < 2 ^ 64)%Z /\ (0 <= (beg + n - 1) / 8 < 2 ^ 64)%Z /\ (0 <= beg / 8 < 2 ^ 64)%Z
    /\ (0 <= (beg + n - 1) mod 8 < 8)%Z.
  Proof.
    pose proof SB_val. unfold d1, d2, SB.
    pose proof (Z.div_le_mono beg (beg + n - 1) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (2147450880 + beg / 8) (2147450880 + (beg + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.mod_pos_bound (beg + n - 1) 8 ltac:(lia)). lia.
  Qed.

  Lemma rd_wd : forall a, (d1 / 8 * 8 <= a)%Z -> (a + 8 <= d2 / 8 * 8 + 8)%Z ->
    exists bs (v : word), rdn SEGS mem (Z_to_bv 64 a) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v.
  Proof.
    intros a H1 H2. pose proof qd_arith. apply rdn8_of_bytes; [lia | lia |]. intros j Hj. apply Hrdw. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma qd_loop : forall k regs (c : Z),
    (d1 <= c < d2)%Z -> k = Z.to_nat (d2 - c) ->
    getr regs 13 = Z_to_bv 64 c -> getr regs 14 = Z_to_bv 64 d2 -> getr regs 15 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x75e38 : word) mem rom) (mkst regs' (0x75e48 : word) mem rom)
      /\ getr regs' 15 = Z_to_bv 64 0
      /\ (forall r, r <> 13 -> r <> 15 -> r <> 16 -> getr regs' r = getr regs r).
  Proof.
    pose proof qd_arith as QA.
    induction k as [|k IH]; intros regs c Hc Hk H13 H14 H15; [lia|].
    assert (Zc : mem (Z_to_bv 64 c) = Some (Z_to_bv 8 0)).
    { replace c with (SB + (c - SB))%Z by lia. apply Hz. unfold d1, d2 in Hc. lia. }
    assert (RDc : rdn SEGS mem (Z_to_bv 64 c) 1 = Some [Z_to_bv 8 0]) by (cbn [rdn]; rewrite Zc; reflexivity).
    destruct (Z.eq_dec (c + 1) d2) as [Hend | Hmore].
    - eexists. split; [|split].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_75e38 eq_refl D_75e38); gr; rewrite ?H13; zn; rewrite Z.add_0_r; exact RDc).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_75e3c eq_refl D_75e3c)). gr. rewrite H13. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_75e40 eq_refl D_75e40)). gr. rewrite H15.
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. rewrite v_or_zero.
        eapply mst_step; [reflexivity | eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_75e44 eq_refl D_75e44); gr; rewrite H14, Hend; br_eq |].
        step_simpl. imm_norm. apply mst_refl.
      + gr. reflexivity.
      + intros r N13 N15 N16. repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
    - edestruct (IH (regupd (regupd (regupd regs 16 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (c + 1))) 15 (Z_to_bv 64 0)) (c + 1)%Z)
        as (regs' & Hms & P15 & Pother); [lia | lia | gr; reflexivity | gr; exact H14 | gr; reflexivity |].
      exists regs'. split; [|split; [exact P15|]].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_75e38 eq_refl D_75e38); gr; rewrite ?H13; zn; rewrite Z.add_0_r; exact RDc).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_75e3c eq_refl D_75e3c)). gr. rewrite H13. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_75e40 eq_refl D_75e40)). gr. rewrite H15.
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. rewrite v_or_zero.
        eapply mst_step; [reflexivity | eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_75e44 eq_refl D_75e44); gr; rewrite H14; br_eq |].
        step_simpl. imm_norm. exact Hms.
      + intros r N13 N15 N16. rewrite (Pother r N13 N15 N16).
        repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
  Qed.

  Theorem qc_dst_run : forall regs,
    getr regs 10 = Z_to_bv 64 beg -> getr regs 12 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (beg + n) ->
    exists regs',
      msteps SEGS (mkst regs (0x75a74 : word) mem rom) (mkst regs' (0x75aac : word) mem rom)
      /\ getr regs' 20 = Z_to_bv 64 (beg + n - 1)
      /\ (forall r, r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 -> r <> 20 -> getr regs' r = getr regs r).
  Proof.
    intros regs H10 H12 H20. pose proof SB_val as HSB.
    pose proof qd_arith as QA. destruct QA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
    destruct (rd_wd (d1 / 8 * 8)%Z ltac:(lia) ltac:(lia)) as (bs1 & w1 & RD1 & V1).
    destruct (rd_wd (d2 / 8 * 8)%Z ltac:(lia) ltac:(lia)) as (bs2 & w2 & RD2 & V2).
    (* [comment removed for export] *)
    assert (LINE : forall regs0,
      getr regs0 10 = Z_to_bv 64 beg -> getr regs0 12 = Z_to_bv 64 n -> getr regs0 20 = Z_to_bv 64 (beg + n) ->
      msteps SEGS (mkst regs0 (0x75a74 : word) mem rom)
        (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs0 13 (Z_to_bv 64 0x129a74)) 13 (Z_to_bv 64 0x132278)) 14 (Z_to_bv 64 SB)) 20 (Z_to_bv 64 (beg + n - 1))) 13 (Z_to_bv 64 (beg / 8))) 15 (Z_to_bv 64 ((beg + n - 1) / 8))) 13 (Z_to_bv 64 d1)) 14 (Z_to_bv 64 d2)) 15 (Z_to_bv 64 (d1 / 8 * 8))) 16 (Z_to_bv 64 (d2 / 8 * 8))) 15 w1)
              (0x75aa0 : word) mem rom)).
    { intros regs0 G10 G12 G20.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x129a74) F_75a74 eq_refl D_75a74);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_75a78 D_75a78 0x132278%Z C1 G10.
      mld F_75a7c D_75a7c SB C2 G10.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_75a80 eq_refl D_75a80)). gr. rewrite G20. zn.
      replace (beg + n + -1)%Z with (beg + n - 1)%Z by lia.
      (* [comment removed for export] *)
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_75a84 eq_refl D_75a84)). gr. rewrite G10, (v_srli_3 beg) by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_75a88 eq_refl D_75a88)). gr. rewrite (v_srli_3 (beg + n - 1)) by lia.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_75a8c eq_refl D_75a8c)). gr. rewrite v_add_zbv by lia. fold d1.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_75a90 eq_refl D_75a90)). gr. rewrite v_add_zbv by lia. fold d2.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_75a94 eq_refl D_75a94)). gr. rewrite v_andi_m8 by lia.
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_75a98 eq_refl D_75a98)). gr. rewrite v_andi_m8 by lia.
      (* [comment removed for export] *)
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ w1 F_75a9c eq_refl D_75a9c);
                   [ gr; zn; rewrite Z.add_0_r; exact RD1 | exact V1 ]).
      apply mst_refl. }
    (* [comment removed for export] *)
    destruct (bv_eq_dec 64 (v_or w2 w1) (Z_to_bv 64 0)) as [Hor | Hor].
    - (* [comment removed for export] *)
      eexists. split; [|split].
      + eapply msteps_trans; [apply (LINE regs H10 H12 H20)|].
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ w2 F_75aa0 eq_refl D_75aa0);
                     [ gr; zn; rewrite Z.add_0_r; exact RD2 | exact V2 ]).
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_75aa4 eq_refl D_75aa4)). gr. rewrite Hor.
        eapply mst_step; [reflexivity | eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_75aa8 eq_refl D_75aa8); gr; rewrite getr_zero; reflexivity |].
        step_simpl. imm_norm. apply mst_refl.
      + gr. reflexivity.
      + intros r N13 N14 N15 N16 N17 N20. repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
    - (* [comment removed for export] *)
      assert (RDl : rdn SEGS mem (Z_to_bv 64 d2) 1 = Some [b1]) by (cbn [rdn]; unfold d2; rewrite Hlast; reflexivity).
      pose proof (last_test_zero b1 ((beg + n - 1) mod 8) (Z_to_bv 64 0) ltac:(lia) Hb1) as LT.
      set (regsA := (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 13 (Z_to_bv 64 0x129a74)) 13 (Z_to_bv 64 0x132278)) 14 (Z_to_bv 64 SB)) 20 (Z_to_bv 64 (beg + n - 1))) 13 (Z_to_bv 64 (beg / 8))) 15 (Z_to_bv 64 ((beg + n - 1) / 8))) 13 (Z_to_bv 64 d1)) 14 (Z_to_bv 64 d2)) 15 (Z_to_bv 64 (d1 / 8 * 8))) 16 (Z_to_bv 64 (d2 / 8 * 8))) 15 w1) 16 w2) 15 (v_or w2 w1)) 15 (v_lb b1))).
      set (regsB := (regupd (regupd (regupd (regupd (regupd regsA 16 (Z_to_bv 64 ((beg + n - 1) mod 8))) 17 (v_sltu (Z_to_bv 64 0) (v_lb b1))) 15 (v_slt (Z_to_bv 64 ((beg + n - 1) mod 8)) (v_lb b1))) 15 (v_xori (v_slt (Z_to_bv 64 ((beg + n - 1) mod 8)) (v_lb b1)) 1)) 15 (Z_to_bv 64 0))).
      assert (PRE : msteps SEGS (mkst regs (0x75a74 : word) mem rom) (mkst regsB (0x75e34 : word) mem rom)).
      { eapply msteps_trans; [apply (LINE regs H10 H12 H20)|].
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ w2 F_75aa0 eq_refl D_75aa0);
                     [ gr; zn; rewrite Z.add_0_r; exact RD2 | exact V2 ]).
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_75aa4 eq_refl D_75aa4)). gr.
        eapply mst_step; [reflexivity | eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_75aa8 eq_refl D_75aa8); gr; rewrite getr_zero;
                                        unfold c_eq; apply bv_eqb_neq; exact Hor |].
        step_simpl. imm_norm.
        (* [comment removed for export] *)
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_75e1c eq_refl D_75e1c); gr; zn; rewrite Z.add_0_r; exact RDl).
        (* [comment removed for export] *)
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_75e20 eq_refl D_75e20)). gr. rewrite v_andi_7 by lia.
        (* [comment removed for export] *)
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_75e24 eq_refl D_75e24)). gr. rewrite getr_zero.
        (* [comment removed for export] *)
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_75e28 eq_refl D_75e28)). gr.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_75e2c eq_refl D_75e2c)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_75e30 eq_refl D_75e30)). gr.
        change (Z_to_bv 64 0 : word) with (Z_to_bv 64 0) in LT. rewrite LT.
        apply mst_refl. }
      assert (B13 : getr regsB 13 = Z_to_bv 64 d1) by (unfold regsB, regsA; gr; reflexivity).
      assert (B14 : getr regsB 14 = Z_to_bv 64 d2) by (unfold regsB, regsA; gr; reflexivity).
      assert (B15 : getr regsB 15 = Z_to_bv 64 0) by (unfold regsB, regsA; gr; reflexivity).
      assert (B20 : getr regsB 20 = Z_to_bv 64 (beg + n - 1)) by (unfold regsB, regsA; gr; reflexivity).
      assert (Bother : forall r, r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 -> r <> 20 -> getr regsB r = getr regs r).
      { intros r N13 N14 N15 N16 N17 N20. unfold regsB, regsA.
        repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity. }
      (* [comment removed for export] *)
      destruct (Z.eq_dec d1 d2) as [Heq | Hne].
      + eexists. split; [|split].
        * eapply msteps_trans; [exact PRE|].
          eapply mst_step; [reflexivity | eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_75e34 eq_refl D_75e34); rewrite B13, B14, Heq; br_lt |].
          step_simpl. imm_norm.
          (* [comment removed for export] *)
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_75e48 eq_refl D_75e48)). rewrite B15, v_andi_255_0.
          eapply mst_step; [reflexivity | eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_75e4c eq_refl D_75e4c); gr; rewrite getr_zero; reflexivity |].
          step_simpl. imm_norm. apply mst_refl.
        * gr. exact B20.
        * intros r N13 N14 N15 N16 N17 N20. repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])).
          apply Bother; assumption.
      + destruct (qd_loop (Z.to_nat (d2 - d1)) regsB d1 ltac:(lia) eq_refl B13 B14 B15) as (regsL & HmsL & L15 & Lother).
        eexists. split; [|split].
        * eapply msteps_trans; [exact PRE|].
          eapply mst_step; [reflexivity | eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_75e34 eq_refl D_75e34); rewrite B13, B14; br_lt |].
          step_simpl. imm_norm.
          eapply msteps_trans; [exact HmsL|].
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_75e48 eq_refl D_75e48)). rewrite L15, v_andi_255_0.
          eapply mst_step; [reflexivity | eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_75e4c eq_refl D_75e4c); gr; rewrite getr_zero; reflexivity |].
          step_simpl. imm_norm. apply mst_refl.
        * gr. rewrite Lother by (intros E; discriminate E). exact B20.
        * intros r N13 N14 N15 N16 N17 N20. repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])).
          rewrite Lother by assumption. apply Bother; assumption.
  Qed.
End QD.
End FPW_2.

(* [comment removed for export] *)
