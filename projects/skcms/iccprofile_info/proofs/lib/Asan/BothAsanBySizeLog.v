(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk Frame WalkTac RefMemcpyLib AgentLib
  Utf8Lib AsanUtf8Lib AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums BothSumsAsanSpecs
  BothAsanBySizeLogSpec BothAsan_code_bsl.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache.
Open Scope Z_scope.

Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation W8 v := (word_to_le_bytes 8 v).
Section WithFP1. Context {FP : PropExec.FPState}.
Lemma lenW8_bsl : forall v : word, length (W8 v) = 8%nat.
Proof. intros v. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

Lemma v_slli3_Z : forall i, 0 <= i -> 8 * i < 2 ^ 64 -> v_slli (Z_to_bv 64 i) 3 = Z_to_bv 64 (8 * i).
Proof.
  intros i Hi H8. unfold v_slli. rewrite u64_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 3) with 8. f_equal. lia.
Qed.

Section BSL.
  Variables (R : bvmap 5 word) (M : word -> option byte) (i s : Z).
  Hypothesis Hi : 0 <= i <= 63.
  Hypothesis Hs0 : 0 <= s.
  Hypothesis Hs : s + 616 < 2 ^ 64.
  Hypothesis HR11 : getr R 11%bv = Z_to_bv 64 i.
  Hypothesis HR9 : getr R 9%bv = Z_to_bv 64 s.
  Hypothesis Hst : forall a, s + 96 <= a < s + 616 -> store_ok ASEGS M (Z_to_bv 64 a) 1 = true.

  (* [comment removed for export] *)
  Lemma st8 : forall a, s + 96 <= a -> a + 8 <= s + 616 -> store_ok ASEGS M (Z_to_bv 64 a) 8 = true.
  Proof.
    intros a Ha1 Ha2. apply store_ok_of_all; [rewrite u64_lit by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
    pose proof (Hst (bv_unsigned x) ltac:(lia)) as H1. rewrite Z_to_bv_bv_unsigned in H1.
    exact (store_ok_all ASEGS M 1 x ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) H1 x
             ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma rd8 : forall a, s + 96 <= a -> a + 8 <= s + 616 ->
    exists v : word, rdn ASEGS M (Z_to_bv 64 a) 8 = Some (W8 v).
  Proof.
    intros a Ha1 Ha2.
    destruct (APSX.store_ok_rdn ASEGS asan_segs_wr 8 M (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
                (st8 a Ha1 Ha2)) as (bs & Hrd & Hlen).
    pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hb0.
    exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite Hrd. f_equal.
    rewrite <- Hlen. unfold word_to_le_bytes. rewrite u64_lit by lia. symmetry. apply Z_to_le_bytes_lez.
  Qed.

  (* [comment removed for export] *)
  Definition M2 (v : word) : word -> option byte :=
    wbytes (wbytes M (Z_to_bv 64 (s + 96)) (W8 (getr R 12%bv))) (Z_to_bv 64 (s + 8 * i + 104)) (W8 (v_addi v 1)).

  Lemma M2_outside : forall v (x : word), bv_unsigned x < s + 96 \/ s + 616 <= bv_unsigned x -> M2 v x = M x.
  Proof.
    intros v x Hx. unfold M2.
    rewrite !wbytes_outside; rewrite ?lenW8_bsl; unfold in_rng; rewrite ?u64_lit by lia;
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia. reflexivity.
  Qed.

  Lemma M2_grows : forall v, mem_grows M (M2 v).
  Proof. intros v. unfold M2. eapply mem_grows_trans; apply wbytes_grows. Qed.

  Theorem bysizelog_walk : forall rom,
    exists regs' (v : word),
      msteps ASEGS (mkst R (0x35f94 : word) M rom) (mkst regs' (0x35fac : word) (M2 v) rom)
      /\ (forall r, bs_clob r = false -> getr regs' r = getr R r).
  Proof.
    intros rom.
    destruct (rd8 (s + 8 * i + 104) ltac:(lia) ltac:(lia)) as (v & Hv).
    eexists _, v. split.
    - sn F_35f94 D_35f94; pin (8 * i) ltac:(apply v_slli3_Z; lia).                      (* [comment removed for export] *)
      sn F_35f98 D_35f98; pin (s + 8 * i) ltac:(rewrite v_add_ZZ; reflexivity).         (* [comment removed for export] *)
      mld F_35f9c D_35f9c v Hv.                                                          (* [comment removed for export] *)
      sn F_35fa0 D_35fa0.                                                                (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := Z_to_bv 64 (s + 96));
          [ exact F_35fa4 | reflexivity | exact D_35fa4
          | gres; imm_norm; rwH; rewrite v_addi_Z; f_equal; lia
          | gres; reflexivity
          | apply st8; lia ]
        | step_simpl]; vnorm.                                                            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := Z_to_bv 64 (s + 8 * i + 104));
          [ exact F_35fa8 | reflexivity | exact D_35fa8
          | gres; imm_norm; rwH; rewrite v_addi_Z; f_equal; lia
          | gres; reflexivity
          | eapply store_ok_mono; [apply wbytes_grows | apply st8; lia] ]
        | step_simpl]; vnorm.                                                            (* [comment removed for export] *)
      unfold M2. apply mst_refl.
    - intros r Hr. unfold bs_clob in Hr.
      repeat (apply orb_false_iff in Hr; destruct Hr as [Hr ?N]).
      repeat match goal with N : bv_eqb r ?k = false |- _ =>
        apply (f_equal negb) in N; cbn [negb] in N;
        let X := fresh in assert (X : r <> k) by (intros ->; unfold bv_eqb in N; rewrite Z.eqb_refl in N; discriminate N); clear N end.
      gres. repeat (rewrite getr_other by assumption). reflexivity.
  Qed.
End BSL.

Theorem asan_bysizelog : bysizelog_spec ASEGS 0x35f94 0x35fac.
Proof.
  intros mem regs i s Hi Hs0 Hs H11 H9 Hst.
  destruct (bysizelog_walk regs mem i s Hi Hs0 Hs H11 H9 Hst (seg_rom ASEGS)) as (regs' & v & Hms & Hregs).
  exists regs', (M2 regs mem i s v). split; [|split; [exact Hregs | split; [apply M2_outside; lia | apply M2_grows]]].
  match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
    replace (Z_to_bv 64 0x35f94) with p by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 0x35fac) with q by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.
End WithFP1.

