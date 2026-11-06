(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhASlotW4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhCtz OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhSzc OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhMallocH OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac post := repeat split; gres; try reflexivity; try assumption; try solve_keeps_but.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Meta.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis M_sz : sz_img m.

  Lemma aMeta : forall regs rom,
    getr regs 8 = Z_to_bv 64 sc ->
    exists regs',
      msteps RSEGS (mkst regs (0x67490 : word) m rom) (mkst regs' (0x66c68 : word) m rom)
      /\ getr regs' 19 = Z_to_bv 64 (2 * sc) /\ getr regs' 25 = Z_to_bv 64 A_TAB_SC
      /\ getr regs' 24 = Z_to_bv 64 (size_class sc) /\ getr regs' 1 = Z_to_bv 64 0x674a8
      /\ keeps_but [1; 10; 19; 24; 25]%bv regs regs'.
  Proof using M_sz Hsc.
    intros regs rom H8. unfold A_TAB_SC.
    destruct (sz_entry m sc M_sz Hsc) as (bs & Hbs & Hv). pose proof (size_class_pos sc Hsc) as SP.
    eexists. split.
    - stepn F_6743c D_6743c. rewrite H8, (v_slli_Z sc 1) by lia. change (2 ^ 1)%Z with 2%Z.
      stepn F_67440 D_67440.
      stepn F_67444 D_67444. vals_lit.
      stepn F_67448 D_67448. rewrite (v_add_ZZ 145772 (sc * 2)) by lia.
      replace (145772 + sc * 2)%Z with (0x2396c + 2 * sc)%Z by lia.
      stepLHU F_6744c D_6744c bs (Z_to_bv 64 (size_class sc)) ltac:(addr_norm; exact Hbs) ltac:(rewrite Hv; u_norm; lia).
      stepn F_67450 D_67450.
      pu_refl.
    - post. f_equal. lia.
  Qed.
End Meta.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Grp0.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc mt u scl : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hmt : (0 < mt < 2^64)%Z.
  Hypothesis Hu : (0 <= u < 2^64)%Z.
  Hypothesis Hscl : (1 <= scl < 2^16)%Z.
  Hypothesis M_use : rdn RSEGS m (Z_to_bv 64 (ctx_usage sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 u)).
  Hypothesis M_pg : rdn RSEGS m (Z_to_bv 64 A_PAGESIZE) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).

  Lemma aGrp0 : forall regs rom,
    getr regs 10 = Z_to_bv 64 mt -> getr regs 23 = Z_to_bv 64 (MLOCK + 8 * sc) -> getr regs 24 = Z_to_bv 64 scl ->
    exists regs',
      msteps RSEGS (mkst regs (0x674a8 : word) m rom) (mkst regs' (0x674c8 : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 mt /\ getr regs' 10 = Z_to_bv 64 u /\ getr regs' 11 = Z_to_bv 64 4096
      /\ getr regs' 12 = Z_to_bv 64 8 /\ getr regs' 24 = Z_to_bv 64 (16 * scl)
      /\ keeps_but [9; 10; 11; 12; 24]%bv regs regs'.
  Proof using M_pg M_use Hscl Hmt Hsc.
    intros regs rom H10 H23 H24. unfold ctx_usage, CTX, MLOCK, A_PAGESIZE in *.
    eexists. split.
    - stepn F_67454 D_67454. rewrite H10.
      stepn F_67458 D_67458.
      stepb_ft F_6745c D_6745c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepLD F_67460 D_67460 (word_to_le_bytes 8 (Z_to_bv 64 u)) (Z_to_bv 64 u)
        ltac:(unfold v_addi; unorm; replace (700048 + 8 * sc + 472)%Z with (700056 + 464 + 8 * sc)%Z by lia; exact M_use)
        ltac:(apply bytes_le_to_Z_8).
      stepn F_67464 D_67464.
      stepLD F_67468 D_67468 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
        ltac:(addr_norm; exact M_pg) ltac:(apply bytes_le_to_Z_8).
      stepn F_6746c D_6746c.
      stepn F_67470 D_67470. rewrite H24, (v_slli_Z scl 4) by lia. change (2 ^ 4)%Z with 16%Z.
      pu_refl.
    - post. f_equal. lia.
  Qed.
End Grp0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition g4cnt (size cnt : Z) : Z := if (cnt =? 1)%Z then (if (2048 <? size + 16)%Z then 1 else 2) else cnt.

Section G4.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (size cnt : Z).
  Hypothesis Hsize : (16 <= size <= 16 * 8191)%Z.
  Hypothesis Hcnt : (1 <= cnt <= 64)%Z.

  Lemma g4cnt_rng : (1 <= g4cnt size cnt <= 64)%Z.
  Proof using Hcnt. unfold g4cnt. destruct (cnt =? 1)%Z; [destruct (2048 <? size + 16)%Z|]; lia. Qed.

  Ltac g4_pre H19 H24 H11 :=
    stepn F_67500 D_67500; rewrite H24; addi_renorm;
    stepn F_67504 D_67504;
    stepn F_67508 D_67508; rewrite H11; vals_lit.

  Lemma aG4 : forall regs rom,
    getr regs 19 = Z_to_bv 64 cnt -> getr regs 24 = Z_to_bv 64 size -> getr regs 11 = Z_to_bv 64 4096 ->
    exists regs',
      msteps RSEGS (mkst regs (0x67554 : word) m rom)
                   (mkst regs' ((if (size * g4cnt size cnt + 16 <=? 2048)%Z then 0x675c0 else 0x6757c) : word) m rom)
      /\ getr regs' 19 = Z_to_bv 64 (g4cnt size cnt) /\ getr regs' 14 = Z_to_bv 64 (size * g4cnt size cnt)
      /\ getr regs' 15 = Z_to_bv 64 (size * g4cnt size cnt + 16) /\ getr regs' 12 = Z_to_bv 64 (size + 16)
      /\ getr regs' 13 = Z_to_bv 64 2048
      /\ keeps_but [12; 13; 14; 15; 19]%bv regs regs'.
  Proof using Hcnt Hsize.
    intros regs rom H19 H24 H11. pose proof g4cnt_rng as CR.
    set (c' := g4cnt size cnt) in *.
    assert (M64 : (0 <= size * c' <= 16 * 8191 * 64)%Z) by nia.
    (* [comment removed for export] *)
    assert (PRE : forall r0, getr r0 19 = Z_to_bv 64 cnt -> getr r0 24 = Z_to_bv 64 size -> getr r0 11 = Z_to_bv 64 4096 ->
      exists r1, msteps RSEGS (mkst r0 (0x67554 : word) m rom) (mkst r1 (0x67570 : word) m rom)
        /\ getr r1 19 = Z_to_bv 64 c' /\ getr r1 24 = Z_to_bv 64 size /\ getr r1 12 = Z_to_bv 64 (size + 16) /\ getr r1 13 = Z_to_bv 64 2048
        /\ keeps_but [12; 13; 14; 15; 19]%bv r0 r1).
    { intros r0 R19 R24 R11. subst c'. unfold g4cnt in *.
      destruct (cnt =? 1)%Z eqn:E1.
      - apply Z.eqb_eq in E1.
        destruct (2048 <? size + 16)%Z eqn:E2.
        + eexists. split.
          * g4_pre R19 R24 R11.
            stepb_ft F_6750c D_6750c ltac:(rewrite R19, E1; apply c_eq_refl).
            stepn F_67510 D_67510. unfold v_sltu. rewrite c_ltu_Z, E2 by lia.
            stepn F_67514 D_67514.
            stepn F_67518 D_67518.
            pu_refl.
          * post.
        + eexists. split.
          * g4_pre R19 R24 R11.
            stepb_ft F_6750c D_6750c ltac:(rewrite R19, E1; apply c_eq_refl).
            stepn F_67510 D_67510. unfold v_sltu. rewrite c_ltu_Z, E2 by lia.
            stepn F_67514 D_67514.
            stepn F_67518 D_67518.
            pu_refl.
          * post.
      - apply Z.eqb_neq in E1. eexists. split.
        + g4_pre R19 R24 R11.
          stepb_tk F_6750c D_6750c ltac:(rewrite R19, c_eq_Z by lia; apply Z.eqb_neq; lia).
          pu_refl.
        + post. }
    destruct (PRE regs H19 H24 H11) as (r1 & S1 & A19 & A24 & A12 & A13 & K1).
    destruct (size * c' + 16 <=? 2048)%Z eqn:LE.
    - apply Z.leb_le in LE. eexists. split.
      + eapply msteps_trans; [exact S1|].
        stepn F_6751c D_6751c. rewrite A24, A19, (v_mul_Z size c') by lia.
        stepn F_67520 D_67520. addi_renorm.
        stepb_tk F_67524 D_67524 ltac:(rewrite A13; unfold c_ltu; rewrite ?Bool.negb_true_iff; unfold bv_ltu; u_norm; apply Z.ltb_ge; lia).
        pu_refl.
      + post. all: try (eapply keeps_but_trans; [exact K1 | solve_keeps_but]).
    - apply Z.leb_gt in LE. eexists. split.
      + eapply msteps_trans; [exact S1|].
        stepn F_6751c D_6751c. rewrite A24, A19, (v_mul_Z size c') by lia.
        stepn F_67520 D_67520. addi_renorm.
        stepb_ft F_67524 D_67524 ltac:(rewrite A13; unfold c_ltu; rewrite ?Bool.negb_false_iff; unfold bv_ltu; u_norm; apply Z.ltb_lt; lia).
        pu_refl.
      + post. all: try (eapply keeps_but_trans; [exact K1 | solve_keeps_but]).
  Qed.
End G4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma szc_x_16 : forall k, (0 <= k)%Z -> szc_x (16 * k + 12) = k.
Proof.
  intros k Hk. rewrite szc_x_eq by lia. symmetry. apply (Z.div_unique _ _ _ 15); lia.
Qed.

Section Ncls.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (scl c : Z).     (* [comment removed for export] *)
  Hypothesis Hscl : (1 <= scl)%Z.
  Hypothesis Hc : (1 <= c)%Z.
  Hypothesis Hroom : (16 * scl * c + 16 <= 2048)%Z.
  Hypothesis M_ctz : img_clear m A_TAB_CTZ (A_TAB_CTZ + 32).
  Hypothesis M_sz : sz_img m.

  Definition ncls_n : Z := 16 * scl * c + 12.
  Definition clobNcls : list reg := [1; 10; 11; 12; 13; 14; 18]%bv.

  Lemma ncls_x : szc_x ncls_n = (scl * c)%Z.
  Proof using Hroom Hc Hscl. unfold ncls_n. replace (16 * scl * c)%Z with (16 * (scl * c))%Z by lia. apply szc_x_16. nia. Qed.

  Lemma aNcls : forall regs rom,
    getr regs 14 = Z_to_bv 64 (16 * scl * c) -> getr regs 25 = Z_to_bv 64 A_TAB_SC ->
    exists regs',
      msteps RSEGS (mkst regs (0x675c0 : word) m rom) (mkst regs' (0x672b0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (size_to_class ncls_n) /\ getr regs' 18 = Z_to_bv 64 (size_to_class ncls_n)
      /\ getr regs' 11 = Z_to_bv 64 ncls_n /\ getr regs' 1 = Z_to_bv 64 0x67690
      /\ keeps_but clobNcls regs regs'.
  Proof using M_sz M_ctz Hroom Hc Hscl.
    intros regs rom H14 H25. unfold A_TAB_SC, A_TAB_CTZ in *.
    assert (Hsc_pos : (1 <= scl * c <= 127)%Z) by nia.
    assert (Hstc : size_to_class ncls_n = szc_of_x (scl * c)) by (unfold size_to_class; rewrite ncls_x; reflexivity).
    set (x := (scl * c)%Z) in *.
    assert (E16 : (16 * scl * c = x * 2 ^ 4)%Z) by (change (2 ^ 4)%Z with 16%Z; lia).
    (* [comment removed for export] *)
    Ltac ncls_pre H14 E16 x :=
      stepn F_6756c D_6756c; rewrite H14; addi_renorm;
      stepn F_67570 D_67570;
      stepn F_67574 D_67574; rewrite H14, E16, (v_srli_Z (x * 2 ^ 4) 4), Z.div_mul by (change (2 ^ 4)%Z with 16%Z; lia).
    destruct (Z_lt_dec x 10) as [LT|GE].
    - (* [comment removed for export] *)
      rewrite (szc_of_x_lt10 x) in Hstc by lia. rewrite Hstc.
      eexists. split.
      + ncls_pre H14 E16 x.
        stepb_tk F_67578 D_67578 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
        stepn F_67630 D_67630. sextw_norm x.
        stepn F_67634 D_67634.
        stepn F_67638 D_67638.
        pu_refl.
      + post. unfold ncls_n. f_equal. lia.
    - (* [comment removed for export] *)
      assert (Hx10 : (10 <= x)%Z) by lia.
      pose proof (szc_t_rng x ltac:(unfold XMAX; lia)) as TR. set (t := szc_t x) in *.
      assert (P2 : (0 < 2 ^ t <= 4096)%Z).
      { split; [apply Z.pow_pos_nonneg; lia|]. change 4096%Z with (2 ^ 12)%Z. apply Z.pow_le_mono_r; lia. }
      change (2 ^ 31)%Z with 2147483648%Z in *.
      pose proof (ctzix_rng t ltac:(lia)) as CR.
      rewrite (szc_of_x_ge10 x Hx10) in Hstc. fold t in Hstc. cbv zeta in Hstc.
      replace (4 * t - 4 + 1)%Z with (4 * t - 3)%Z in Hstc by lia. replace (4 * t - 4 + 2)%Z with (4 * t - 2)%Z in Hstc by lia.
      pose proof (size_class_pos (4 * t - 3) ltac:(lia)) as SP1.
      pose proof (size_class_pos (4 * t - 4) ltac:(lia)) as SP0.
      pose proof (size_class_pos (4 * t - 2) ltac:(lia)) as SP2.
      destruct (sz_entry m (4 * t - 3) M_sz ltac:(lia)) as (bs1 & Hbs1 & Hv1).
      destruct (sz_entry m (4 * t - 4) M_sz ltac:(lia)) as (bs0 & Hbs0 & Hv0).
      destruct (sz_entry m (4 * t - 2) M_sz ltac:(lia)) as (bs2 & Hbs2 & Hv2).
      (* [comment removed for export] *)
      Ltac ncls_mid x t bs1 Hbs1 Hv1 H25 :=
        stepb_ft F_67578 D_67578 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
        stepn F_6757c D_6757c; addi_renorm;
        stepn F_67580 D_67580;
        stepn F_67584 D_67584; iso_fold (iso_c1 (Z_to_bv 64 (x + 1)));
        stepn F_67588 D_67588; iso_fold (iso_c2 (Z_to_bv 64 (x + 1)));
        stepn F_6758c D_6758c; iso_fold (iso_c3 (Z_to_bv 64 (x + 1)));
        stepn F_67590 D_67590; iso_fold (iso_c4 (Z_to_bv 64 (x + 1)));
        stepn F_67594 D_67594; iso_fold (iso_c5 (Z_to_bv 64 (x + 1)));
        stepn F_67598 D_67598; iso_fold (iso_c6 (Z_to_bv 64 (x + 1)));
        stepn F_6759c D_6759c; iso_fold (iso_c7 (Z_to_bv 64 (x + 1)));
        stepn F_675a0 D_675a0; iso_fold (iso_c8 (Z_to_bv 64 (x + 1)));
        stepn F_675a4 D_675a4; iso_fold (iso_c9 (Z_to_bv 64 (x + 1)));
        stepn F_675a8 D_675a8; iso_fold (iso_c10 (Z_to_bv 64 (x + 1)));
        stepn F_675ac D_675ac; iso_fold (iso_c11 (Z_to_bv 64 (x + 1)));
        stepn F_675b0 D_675b0; iso_fold (iso_c12 (Z_to_bv 64 (x + 1)));
        stepn F_675b4 D_675b4; iso_fold (iso_c13 (Z_to_bv 64 (x + 1)));
        stepn F_675b8 D_675b8; iso_fold (iso_c14 (Z_to_bv 64 (x + 1)));
        stepn F_675bc D_675bc; iso_fold (iso_c15 (Z_to_bv 64 (x + 1)));
        stepn F_675c0 D_675c0; iso_fold (iso_c16 (Z_to_bv 64 (x + 1)));
        match goal with |- context [regupd _ 10 ?v] => change v with (iso_bv (Z_to_bv 64 (x + 1))) end;
        rewrite (iso_bv_pow2 x) by (unfold XMAX; lia); fold t;
        rewrite <- (s32_small (2 ^ t)) by lia;
        stepn F_675c4 D_675c4;
        stepn F_675c8 D_675c8; vals_lit;
        stepn F_675cc D_675cc; vals_lit;
        stepn F_675d0 D_675d0;
        stepn F_675d4 D_675d4; (let CZ := fresh in pose proof (ctz_srliw t ltac:(lia)) as CZ; unfold CTZC in CZ; rewrite CZ; clear CZ);
        stepn F_675d8 D_675d8; rewrite (v_add_ZZ 145740 (ctzix t)) by lia;
        (let TB := fresh in pose proof (ctz_tab_read m t M_ctz ltac:(lia)) as TB; unfold A_TAB_CTZ in TB;
         stepLBU F_675dc D_675dc (Z_to_bv 8 t) ltac:(addr_norm; replace (145740 + ctzix t + 0)%Z with (145740 + ctzix t)%Z by lia; rdn_by TB);
         clear TB);
        rewrite (u8_Z2bv t) by lia;
        stepn F_675e0 D_675e0;
        stepn F_675e4 D_675e4;
        match goal with |- context [regupd _ 10 ?v] => change v with (ix_a0 t) end; rewrite (ix_a0_val t) by lia;
        stepn F_675e8 D_675e8;
        stepn F_675ec D_675ec; rewrite (v_sub_ZZ 121 (124 - 4 * t)) by lia; replace (121 - (124 - 4 * t))%Z with (4 * t - 3)%Z by lia;
        stepn F_675f0 D_675f0; rewrite (v_slli_Z (4 * t - 3) 1) by lia; change (2 ^ 1)%Z with 2%Z;
        stepn F_675f4 D_675f4; rewrite H25, (v_add_ZZ 145772 ((4 * t - 3) * 2)) by lia;
        replace (145772 + (4 * t - 3) * 2)%Z with (0x2396c + 2 * (4 * t - 3))%Z by lia;
        stepLHU F_675f8 D_675f8 bs1 (Z_to_bv 64 (size_class (4 * t - 3))) ltac:(addr_norm; exact Hbs1) ltac:(rewrite Hv1; u_norm; lia).
      (* [comment removed for export] *)
      Ltac ncls_tail x t c0 i2 b nb bs2 Hbs2 Hv2 B2 H25 :=
        stepn F_67614 D_67614; rewrite (v_sub_ZZ c0 (124 - 4 * t)) by lia; replace (c0 - (124 - 4 * t))%Z with i2 by lia;
        stepn F_67618 D_67618; rewrite (v_slli_Z i2 1) by lia; change (2 ^ 1)%Z with 2%Z;
        stepn F_6761c D_6761c; rewrite H25, (v_add_ZZ 145772 (i2 * 2)) by lia; replace (145772 + i2 * 2)%Z with (0x2396c + 2 * i2)%Z by lia;
        stepLHU F_67620 D_67620 bs2 (Z_to_bv 64 (size_class i2)) ltac:(addr_norm; exact Hbs2) ltac:(rewrite Hv2; u_norm; lia);
        stepn F_67624 D_67624;
        match goal with |- context [regupd _ 10 ?v] => replace v with (Z_to_bv 64 b)
          by (change v with (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 (size_class i2))); unfold v_sltu; rewrite c_ltu_Z, B2 by lia; reflexivity) end;
        stepn F_67628 D_67628;
        stepn F_6762c D_6762c; rewrite (v_or_Z i2 nb) by lia; rewrite (lor_even_bit i2 nb) by (first [apply ev4a | apply ev4b | lia]);
        stepn F_67630 D_67630; sextw_norm (i2 + nb)%Z;
        stepn F_67634 D_67634;
        stepn F_67638 D_67638;
        pu_refl.
      (* [comment removed for export] *)
      eassert (PRE : msteps RSEGS (mkst regs (0x675c0 : word) m rom) _).
      { ncls_pre H14 E16 x. ncls_mid x t bs1 Hbs1 Hv1 H25. pu_refl. }
      destruct (x <? size_class (4 * t - 3))%Z eqn:B1.
      + apply Z.ltb_lt in B1 as B1'.
        destruct (x <? size_class (4 * t - 4))%Z eqn:B2; rewrite Hstc.
        * eexists. split.
          -- eapply msteps_trans; [exact PRE|].
             stepb_tk F_675fc D_675fc ltac:(rewrite c_ltu_Z by lia; exact B1).
             stepn F_67610 D_67610.
             ncls_tail x t 120%Z (4 * t - 4)%Z 1%Z 0%Z bs0 Hbs0 Hv0 B2 H25.
          -- post; unfold ncls_n; try (f_equal; lia).
        * eexists. split.
          -- eapply msteps_trans; [exact PRE|].
             stepb_tk F_675fc D_675fc ltac:(rewrite c_ltu_Z by lia; exact B1).
             stepn F_67610 D_67610.
             ncls_tail x t 120%Z (4 * t - 4)%Z 0%Z 1%Z bs0 Hbs0 Hv0 B2 H25.
          -- post; unfold ncls_n; try (f_equal; lia).
      + apply Z.ltb_ge in B1 as B1'.
        destruct (x <? size_class (4 * t - 2))%Z eqn:B2; rewrite Hstc.
        * eexists. split.
          -- eapply msteps_trans; [exact PRE|].
             stepb_ft F_675fc D_675fc ltac:(rewrite c_ltu_Z by lia; exact B1).
             stepn F_67600 D_67600.
             stepn F_67604 D_67604.
             ncls_tail x t 122%Z (4 * t - 2)%Z 1%Z 0%Z bs2 Hbs2 Hv2 B2 H25.
          -- post; unfold ncls_n; try (f_equal; lia).
        * eexists. split.
          -- eapply msteps_trans; [exact PRE|].
             stepb_ft F_675fc D_675fc ltac:(rewrite c_ltu_Z by lia; exact B1).
             stepn F_67600 D_67600.
             stepn F_67604 D_67604.
             ncls_tail x t 122%Z (4 * t - 2)%Z 0%Z 1%Z bs2 Hbs2 Hv2 B2 H25.
          -- post; unfold ncls_n; try (f_equal; lia).
  Qed.
End Ncls.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Nenf.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (j idx g2 ctr : Z).
  Hypothesis Hj : (0 <= j < 48)%Z.
  Hypothesis Hidx : (0 <= idx < 32)%Z.
  Hypothesis Hg2 : (0 <= g2 < 2^64)%Z.
  Hypothesis Hctr : (0 <= ctr < 2^32)%Z.
  Hypothesis M_actj : rdn RSEGS m (Z_to_bv 64 (ctx_active j)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g2)).
  Hypothesis M_ctr : rdn RSEGS m (Z_to_bv 64 ctx_mmap_counter) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ctr)).
  Hypothesis M_sz : sz_img m.

  Lemma aNenf : forall regs rom,
    getr regs 10 = Z_to_bv 64 idx -> getr regs 18 = Z_to_bv 64 j -> getr regs 22 = Z_to_bv 64 MLOCK -> getr regs 25 = Z_to_bv 64 A_TAB_SC ->
    exists regs',
      msteps RSEGS (mkst regs (0x67690 : word) m rom) (mkst regs' (0x67b54 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 g2 /\ getr regs' 11 = Z_to_bv 64 idx
      /\ getr regs' 12 = Z_to_bv 64 (16 * size_class j - 4) /\ getr regs' 13 = s32 ctr
      /\ getr regs' 1 = Z_to_bv 64 0x676c0
      /\ keeps_but [1; 10; 11; 12; 13; 18]%bv regs regs'.
  Proof using M_sz M_ctr M_actj Hctr Hidx Hj.
    intros regs rom H10 H18 H22 H25. unfold ctx_active, ctx_mmap_counter, CTX, MLOCK, A_TAB_SC in *.
    destruct (sz_entry m j M_sz Hj) as (bs & Hbs & Hv). pose proof (size_class_pos j Hj) as SP.
    eexists. split.
    - stepb_ft F_6763c D_6763c ltac:(rewrite H10; apply c_lts_pos_0; u_norm; lia).
      stepn F_67640 D_67640. rewrite H10.
      stepn F_67644 D_67644. rewrite H18, (v_slli_Z j 3) by lia. change (2 ^ 3)%Z with 8%Z.
      stepn F_67648 D_67648. rewrite H18, (v_slli_Z j 1) by lia. change (2 ^ 1)%Z with 2%Z.
      stepn F_6764c D_6764c. rewrite H22, (v_add_ZZ 700048 (j * 8)) by lia.
      stepn F_67650 D_67650. rewrite H25, (v_add_ZZ 145772 (j * 2)) by lia.
      replace (145772 + j * 2)%Z with (0x2396c + 2 * j)%Z by lia.
      stepLHU F_67654 D_67654 bs (Z_to_bv 64 (size_class j)) ltac:(addr_norm; exact Hbs) ltac:(rewrite Hv; u_norm; lia).
      stepLD F_67658 D_67658 (word_to_le_bytes 8 (Z_to_bv 64 g2)) (Z_to_bv 64 g2)
        ltac:(unfold v_addi; unorm; replace (700048 + j * 8 + 88)%Z with (700056 + 80 + 8 * j)%Z by lia; exact M_actj)
        ltac:(apply bytes_le_to_Z_8).
      stepLD F_6765c D_6765c (word_to_le_bytes 4 (Z_to_bv 64 ctr)) (Z_to_bv 64 ctr)
        ltac:(addr_norm; exact M_ctr) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepn F_67660 D_67660. rewrite (v_slli_Z (size_class j) 4) by lia. change (2 ^ 4)%Z with 16%Z.
      stepn F_67664 D_67664. addi_renorm.
      stepn F_67668 D_67668.
      pu_refl.
    - post. f_equal. lia.
  Qed.
End Nenf.
End UbMhASlotW4.
Module UbMhASlotW4b.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhCtz OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhSzc OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhMallocH OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2 UbMhASlotW4 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac post := repeat split; gres; try reflexivity; try assumption; try solve_keeps_but.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zero_run (size : Z) (M : mem) (a : Z) (r : nat) : mem :=
  match r with
  | O => M
  | S r' => zero_run size (wbytes M (Z_to_bv 64 a) [Z_to_bv 8 0]) (a + size)%Z r'
  end.

Section ZeroLoop.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (size : Z).
  Hypothesis Hsize : (16 <= size <= 2048)%Z.

  Lemma zero_run_grows : forall r M a, mem_grows M (zero_run size M a r).
  Proof using.
    induction r as [|r IH]; intros M a; cbn [zero_run]; [apply mem_grows_refl|].
    eapply mem_grows_trans; [apply wbytes_grows | apply IH].
  Qed.

  Lemma zero_loop : forall r a M regs rom,
    (1 <= r)%nat -> (HEAPLO <= a)%Z -> (a + (Z.of_nat r - 1) * size + 1 <= CEIL)%Z ->
    (forall k, (k < r)%nat -> store_ok RSEGS M (Z_to_bv 64 (a + Z.of_nat k * size)) 1%nat = true) ->
    getr regs 11 = Z_to_bv 64 (Z.of_nat r) -> getr regs 12 = Z_to_bv 64 a -> getr regs 24 = Z_to_bv 64 size ->
    exists regs',
      msteps RSEGS (mkst regs (0x676e8 : word) M rom) (mkst regs' (0x676f8 : word) (zero_run size M a r) rom)
      /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (a + Z.of_nat r * size)
      /\ keeps_but [11; 12]%bv regs regs'.
  Proof using Hsize.
    ceil; unfold HEAPLO. induction r as [|r IH]; intros a M regs rom Hr Ha Hb SOK H11 H12 H24; [lia|].
    pose proof (SOK 0%nat ltac:(lia)) as S0. rewrite Z.mul_0_l, Z.add_0_r in S0.
    rewrite Nat2Z.inj_succ in *.
    destruct (Nat.eq_dec r 0) as [->|NZ].
    - eexists. split.
      + stepSTx F_67694 D_67694 (Z_to_bv 64 a) (Z_to_bv 64 0) ltac:(exact S0). rewrite (u_Z2bv 0) by lia.
        stepn F_67698 D_67698. rewrite H11. addi_renorm.
        stepn F_6769c D_6769c. rewrite H12, H24, (v_add_ZZ a size) by lia.
        stepb_ft F_676a0 D_676a0 ltac:(apply c_eq_refl).
        pu_refl.
      + cbn [zero_run]. post. f_equal. lia.
    - assert (SOK' : forall k, (k < r)%nat ->
               store_ok RSEGS (wbytes M (Z_to_bv 64 a) [Z_to_bv 8 0]) (Z_to_bv 64 (a + size + Z.of_nat k * size)) 1%nat = true).
      { intros k Hk. eapply store_ok_mono; [apply wbytes_grows|].
        replace (a + size + Z.of_nat k * size)%Z with (a + Z.of_nat (S k) * size)%Z by (rewrite Nat2Z.inj_succ; lia).
        apply SOK. lia. }
      edestruct (IH (a + size)%Z (wbytes M (Z_to_bv 64 a) [Z_to_bv 8 0])
                    (regupd (regupd regs 11 (Z_to_bv 64 (Z.of_nat r))) 12 (Z_to_bv 64 (a + size))) rom)
        as (r2 & S2 & A11 & A12 & K2); [lia | lia | lia | exact SOK' | gres; reflexivity | gres; reflexivity | gres; exact H24 |].
      eexists. split.
      + stepSTx F_67694 D_67694 (Z_to_bv 64 a) (Z_to_bv 64 0) ltac:(exact S0). rewrite (u_Z2bv 0) by lia.
        stepn F_67698 D_67698. rewrite H11. addi_renorm.
        replace (Z.succ (Z.of_nat r) - 1)%Z with (Z.of_nat r) by lia.
        stepn F_6769c D_6769c. rewrite H12, H24, (v_add_ZZ a size) by lia.
        stepb_tk F_676a0 D_676a0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
        exact S2.
      + cbn [zero_run]. post. rewrite A12. f_equal. lia.
        eapply keeps_but_trans; [| exact K2]. solve_keeps_but.
  Qed.
End ZeroLoop.

Ltac sok B SOK := store_ok_peel; eapply (store_ok_sub _ _ _ _ B); [ | exact SOK | | ]; zsimp; lia.
Ltac sextw_norm x := rewrite v_addiw_Z_s32 by lia; rewrite (s32_small (x + 0)) by lia; replace (x + 0)%Z with x by lia.

Section Low12.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma low12 : forall w, (0 <= w < 2^64)%Z -> v_srli (v_slli (Z_to_bv 64 w) 52) 52 = Z_to_bv 64 (w mod 4096).
  Proof using.
    intros w Hw. unfold v_srli, v_slli. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2^64)%Z. rewrite (Z.mod_small w) by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    change (2^64)%Z with (4096 * 4503599627370496)%Z. change (2^52)%Z with 4503599627370496%Z.
    rewrite Zdiv.Zmult_mod_distr_r, Z.div_mul by lia.
    pose proof (Z.mod_pos_bound w 4096 ltac:(lia)). rewrite (Z.mod_small (w mod 4096)) by lia. reflexivity.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma land31 : forall a, Z.land a 31 = (a mod 32)%Z.
  Proof using. intros a. change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
End Low12.

Section Nzero.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (mt p W0 b3 scl c : Z).
  #[local] Notation size := (16 * scl)%Z.
  Hypothesis Hscl : (1 <= scl <= 127)%Z.
  Hypothesis Hc : (1 <= c <= 32)%Z.
  Hypothesis Hroom : (size * c + 16 <= 2048)%Z.
  Hypothesis Hmt : (HEAPLO <= mt)%Z /\ (mt + 40 <= CEIL)%Z /\ ((mt + 40 <= IMG_LO)%Z \/ (IMG_HI <= mt)%Z).
  Hypothesis Hp : (HEAPLO + 16 <= p)%Z /\ (p + 13 + size * c <= CEIL)%Z.
  Hypothesis Hapart : (mt + 40 <= p - 4 \/ p + 13 + size * c <= mt)%Z.
  Hypothesis HW0 : (0 <= W0 < 2^64)%Z.
  Hypothesis Hb3 : (0 <= b3 < 256)%Z.
  Hypothesis M_W : rdn RSEGS m (Z_to_bv 64 (mt + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W0)).
  Hypothesis SOK_mt : store_ok RSEGS m (Z_to_bv 64 mt) 40%nat = true.
  Hypothesis M_b3 : rdn RSEGS m (Z_to_bv 64 (p - 3)) 1%nat = Some [Z_to_bv 8 b3].
  Hypothesis SOK_p3 : store_ok RSEGS m (Z_to_bv 64 (p - 3)) 1%nat = true.
  Hypothesis SOK_z : forall k, (0 <= k <= c)%Z -> store_ok RSEGS m (Z_to_bv 64 (p + 12 + k * size)) 1%nat = true.

  Definition m_nz1 : mem :=
    wbytes (wbytes m (Z_to_bv 64 (mt + 32)) (word_to_le_bytes 8 (Z_to_bv 64 (W0 mod 4096))))
           (Z_to_bv 64 (p - 3)) [Z_to_bv 8 (b3 mod 32 + 192)].
  Definition m_nz : mem := zero_run size m_nz1 (p + 12) (Z.to_nat (c + 1)).

  Lemma aNzero : forall regs rom,
    getr regs 10 = Z_to_bv 64 p -> getr regs 9 = Z_to_bv 64 mt -> getr regs 19 = Z_to_bv 64 c -> getr regs 24 = Z_to_bv 64 size ->
    exists regs',
      msteps RSEGS (mkst regs (0x676c0 : word) m rom) (mkst regs' (0x679b8 : word) m_nz rom)
      /\ getr regs' 11 = Z_to_bv 64 (c - 1) /\ getr regs' 12 = Z_to_bv 64 (c - 1) /\ getr regs' 25 = Z_to_bv 64 c
      /\ getr regs' 10 = Z_to_bv 64 p
      /\ keeps_but [11; 12; 25]%bv regs regs'.
  Proof using SOK_z SOK_p3 M_b3 SOK_mt M_W Hb3 HW0 Hapart Hp Hmt Hroom Hc Hscl RN.
    intros regs rom H10 H9 H19 H24. ceil; unfold HEAPLO in *. unfold m_nz.
    pose proof (Z.mod_pos_bound b3 32 ltac:(lia)) as MB. pose proof (Z.mod_pos_bound W0 4096 ltac:(lia)) as MW.
    assert (SZ : forall k, (k < Z.to_nat (c + 1))%nat -> store_ok RSEGS m_nz1 (Z_to_bv 64 (p + 12 + Z.of_nat k * size)) 1%nat = true).
    { intros k Hk. unfold m_nz1. eapply store_ok_mono; [eapply mem_grows_trans; apply wbytes_grows|]. apply SOK_z. lia. }
    assert (PRE : exists r1, msteps RSEGS (mkst regs (0x676c0 : word) m rom) (mkst r1 (0x676e8 : word) m_nz1 rom)
      /\ getr r1 11 = Z_to_bv 64 (Z.of_nat (Z.to_nat (c + 1))) /\ getr r1 12 = Z_to_bv 64 (p + 12) /\ getr r1 24 = Z_to_bv 64 size
      /\ getr r1 19 = Z_to_bv 64 c /\ getr r1 10 = Z_to_bv 64 p /\ keeps_but [11; 12; 25]%bv regs r1).
    { unfold m_nz1. eexists. split.
      - stepLD F_6766c D_6766c (word_to_le_bytes 8 (Z_to_bv 64 W0)) (Z_to_bv 64 W0) ltac:(addr_norm; exact M_W) ltac:(apply bytes_le_to_Z_8).
        stepn F_67670 D_67670.
        stepn F_67674 D_67674. rewrite (low12 W0) by lia.
        stepSTx F_67678 D_67678 (Z_to_bv 64 (mt + 32)) (Z_to_bv 64 (W0 mod 4096)) ltac:(sok 40%nat SOK_mt).
        stepLBU F_6767c D_6767c (Z_to_bv 8 b3) ltac:(addr_norm; rdn_by M_b3). rewrite (u8_Z2bv b3) by lia.
        stepn F_67680 D_67680. rewrite H19, v_addiw_Z_s32, s32_small by lia.
        stepn F_67684 D_67684. rewrite (v_andi_Z b3 31), land31 by lia.
        stepn F_67688 D_67688. addi_renorm.
        stepSTx F_6768c D_6768c (Z_to_bv 64 (p - 3)) (Z_to_bv 64 (b3 mod 32 + 192)) ltac:(store_ok_peel; exact SOK_p3).
        rewrite (u_Z2bv (b3 mod 32 + 192)) by lia.
        stepn F_67690 D_67690. rewrite H10. addi_renorm.
        pu_refl.
      - post. f_equal. lia. }
    destruct PRE as (r1 & S1 & B11 & B12 & B24 & B19 & B10 & K1).
    edestruct (zero_loop size ltac:(lia) (Z.to_nat (c + 1)) (p + 12)%Z m_nz1 r1 rom) as (r2 & S2 & A11 & A12 & K2);
      [lia | unfold HEAPLO; lia | ceil; rewrite Z2Nat.id by lia; lia | exact SZ | exact B11 | exact B12 | exact B24 |].
    rewrite Z2Nat.id in A12 by lia.
    eexists. split.
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
      stepn F_676a4 D_676a4. kept_rw K2. rewrite B19. addi_renorm.
      stepn F_676a8 D_676a8. kept_rw K2. rewrite B19.
      stepn F_676ac D_676ac.
      stepn F_676b0 D_676b0.
      pu_refl.
    - post. all: try (kept_rw K2; first [exact B10 | reflexivity]).
      eapply keeps_but_trans; [exact K1|].
      eapply keeps_but_trans; [exact (fun r Hr => K2 r ltac:(intros Hin; apply Hr; cbv in Hin |- *; tauto)) |].
      solve_keeps_but.
  Qed.
End Nzero.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CommonLib.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Lemma rdn_wbytes_hit4 : forall segs M (a v : word),
    (bv_unsigned a + 4 <= 2^64)%Z ->
    rdn segs (wbytes M a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
  Proof using.
    intros segs M a v Hnw. pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) M a) as H.
    rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
  Qed.

  Lemma bytes_inj : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
  Proof using.
    induction l1 as [|b1 l1 IH]; destruct l2 as [|b2 l2]; cbn; intros H; try discriminate; [reflexivity|].
    injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
  Qed.
  Ltac bytes_compute := apply bytes_inj; vm_compute; reflexivity.

  (* [comment removed for export] *)
  Lemma av_bytes_n : forall k, (k < 32)%nat ->
    word_to_le_bytes 4 (v_addi (v_sllw (Z_to_bv 64 2) (Z_to_bv 64 (Z.of_nat k))) (-1))
    = word_to_le_bytes 4 (Z_to_bv 64 (2 ^ (Z.of_nat k + 1) - 1)).
  Proof using. intros k Hk. enum_nat k 32%nat ltac:(bytes_compute). Qed.
  Lemma av_bytes : forall a, (0 <= a < 32)%Z ->
    word_to_le_bytes 4 (v_addi (v_sllw (Z_to_bv 64 2) (Z_to_bv 64 a)) (-1)) = word_to_le_bytes 4 (Z_to_bv 64 (2 ^ (a + 1) - 1)).
  Proof using. intros a Ha. rewrite <- (Z2Nat.id a) by lia. apply av_bytes_n. lia. Qed.

  (* [comment removed for export] *)
  Lemma fr_bytes_n : forall kc ka, (1 <= kc <= 32)%nat -> (ka < kc)%nat ->
    word_to_le_bytes 4 (v_add (v_sllw (Z_to_bv 64 2) (Z_to_bv 64 (Z.of_nat kc - 1)))
                              (v_xori (v_lw (Z_to_bv 64 (2 ^ (Z.of_nat ka + 1) - 1))) (-1)))
    = word_to_le_bytes 4 (Z_to_bv 64 (2 ^ Z.of_nat kc - 2 ^ (Z.of_nat ka + 1))).
  Proof using.
    intros kc ka H1 H2.
    (* [comment removed for export] *)
    enum_nat kc 33%nat ltac:(idtac; enum_nat ka 32%nat ltac:(first [bytes_compute | exfalso; lia])).
  Qed.
  Lemma fr_bytes : forall c a, (1 <= c <= 32)%Z -> (0 <= a <= c - 1)%Z ->
    word_to_le_bytes 4 (v_add (v_sllw (Z_to_bv 64 2) (Z_to_bv 64 (c - 1)))
                              (v_xori (v_lw (Z_to_bv 64 (2 ^ (a + 1) - 1))) (-1)))
    = word_to_le_bytes 4 (Z_to_bv 64 (2 ^ c - 2 ^ (a + 1))).
  Proof using.
    intros c a Hc Ha. rewrite <- (Z2Nat.id a), <- (Z2Nat.id c) by lia. apply fr_bytes_n; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma avm1_bytes_n : forall k, (k < 32)%nat ->
    word_to_le_bytes 4 (v_addi (v_lw (Z_to_bv 64 (2 ^ (Z.of_nat k + 1) - 1))) (-1))
    = word_to_le_bytes 4 (Z_to_bv 64 (2 ^ (Z.of_nat k + 1) - 2)).
  Proof using. intros k Hk. enum_nat k 32%nat ltac:(bytes_compute). Qed.
  Lemma avm1_bytes : forall a, (0 <= a < 32)%Z ->
    word_to_le_bytes 4 (v_addi (v_lw (Z_to_bv 64 (2 ^ (a + 1) - 1))) (-1)) = word_to_le_bytes 4 (Z_to_bv 64 (2 ^ (a + 1) - 2)).
  Proof using. intros a Ha. rewrite <- (Z2Nat.id a) by lia. apply avm1_bytes_n. lia. Qed.

  (* [comment removed for export] *)
  Lemma land_low_high0 : forall a b k, (0 <= a < 2 ^ k)%Z -> (0 <= b)%Z -> (0 <= k)%Z -> Z.land a (b * 2 ^ k) = 0%Z.
  Proof using.
    intros a b k Ha Hb Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k) as [L|G].
    - rewrite (Z.mul_pow2_bits_low b k n) by lia. apply Bool.andb_false_r.
    - destruct (Z.eq_dec a 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
      assert (A2 : (a < 2 ^ n)%Z) by (eapply Z.lt_le_trans; [apply (proj2 Ha)|]; apply Z.pow_le_mono_r; lia).
      rewrite (Z.bits_above_log2 a n); [reflexivity | lia | apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))); exact A2].
  Qed.
  Lemma lor_low_high : forall a b k, (0 <= a < 2 ^ k)%Z -> (0 <= b)%Z -> (0 <= k)%Z -> Z.lor a (b * 2 ^ k) = (a + b * 2 ^ k)%Z.
  Proof using.
    intros a b k Ha Hb Hk. rewrite <- Z.lxor_lor by (apply land_low_high0; lia).
    symmetry. apply Z.add_nocarry_lxor. apply land_low_high0; lia.
  Qed.
  Lemma land_hi12 : forall x, (0 <= x < 2 ^ 64)%Z -> Z.land x (2 ^ 64 - 4096) = (x - x mod 4096)%Z.
  Proof using.
    intros x Hx.
    replace (2 ^ 64 - 4096)%Z with (Z.shiftl (Z.ones 52) 12) by reflexivity.
    apply Z.bits_inj'. intros n Hn.
    rewrite Z.land_spec, Z.shiftl_spec by lia.
    replace (x - x mod 4096)%Z with (Z.shiftl (Z.shiftr x 12) 12).
    2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 12)%Z with 4096%Z.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    rewrite Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases n 12) as [L|G].
    - rewrite (Z.testbit_neg_r (Z.shiftr x 12)) by lia. rewrite (Z.testbit_neg_r (Z.ones 52)) by lia. apply Bool.andb_false_r.
    - rewrite Z.shiftr_spec by lia. replace (n - 12 + 12)%Z with n by lia.
      destruct (Z.lt_ge_cases n 64) as [L2|G2].
      + rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
      + rewrite Z.ones_spec_high by lia.
        destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
        assert (A2 : (x < 2 ^ n)%Z) by (eapply Z.lt_le_trans; [apply (proj2 Hx)|]; apply Z.pow_le_mono_r; lia).
        rewrite (Z.bits_above_log2 x n); [reflexivity | lia | apply (proj1 (Z.log2_lt_pow2 x n ltac:(lia))); exact A2].
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma sc_shift : forall sc, (0 <= sc < 64)%Z -> v_srli (v_slli (Z_to_bv 64 sc) 58) 52 = Z_to_bv 64 (sc * 64).
  Proof using.
    intros sc Hsc. rewrite (v_slli_Z sc 58) by (try lia; change (2 ^ 64)%Z with (64 * 2 ^ 58)%Z; lia).
    rewrite v_srli_Z; [| change (2 ^ 64)%Z with (64 * 2 ^ 58)%Z; lia | lia].
    f_equal. change (2 ^ 58)%Z with (64 * 2 ^ 52)%Z. rewrite Z.mul_assoc, Z.div_mul by lia. reflexivity.
  Qed.
End CommonLib.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Common.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (mt p sc c aidx u W1 b8 : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hc : (1 <= c <= 32)%Z.
  Hypothesis Haidx : (0 <= aidx <= c - 1)%Z.
  Hypothesis Hu : (0 <= u < 2^64)%Z.
  Hypothesis Hmt : (HEAPLO <= mt)%Z /\ (mt + 40 <= CEIL)%Z /\ ((mt + 40 <= IMG_LO)%Z \/ (IMG_HI <= mt)%Z).
  Hypothesis Hp : (HEAPLO <= p)%Z /\ (p + 16 <= CEIL)%Z /\ ((p + 16 <= IMG_LO)%Z \/ (IMG_HI <= p)%Z).   (* [comment removed for export] *)
  Hypothesis Hapart : (mt + 40 <= p \/ p + 16 <= mt)%Z.
  Hypothesis HW1 : (0 <= W1 < 2^63)%Z.
  Hypothesis Hb8 : (0 <= b8 < 256)%Z.
  Hypothesis M_use : rdn RSEGS m (Z_to_bv 64 (ctx_usage sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 u)).
  Hypothesis M_act0 : rdn RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis M_W1 : rdn RSEGS m (Z_to_bv 64 (mt + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W1)).
  Hypothesis M_nx : rdn RSEGS m (Z_to_bv 64 (mt + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis M_pv : rdn RSEGS m (Z_to_bv 64 mt) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis M_b8 : rdn RSEGS m (Z_to_bv 64 (p + 8)) 1%nat = Some [Z_to_bv 8 b8].
  Hypothesis SOKc : store_ok RSEGS m (Z_to_bv 64 CTX) 928%nat = true.
  Hypothesis SOK_mt : store_ok RSEGS m (Z_to_bv 64 mt) 40%nat = true.
  Hypothesis SOK_p : store_ok RSEGS m (Z_to_bv 64 p) 9%nat = true.

  Definition AVc : Z := 2 ^ (aidx + 1) - 1.            (* [comment removed for export] *)
  Definition FRc : Z := 2 ^ c - 2 ^ (aidx + 1).        (* [comment removed for export] *)
  Definition AVc' : Z := 2 ^ (aidx + 1) - 2.           (* [comment removed for export] *)
  Definition Wn : Z := sc * 64 + (c - 1) + (W1 - W1 mod 4096) + 32.   (* [comment removed for export] *)
  Definition AIb : Z := Z.lor (Z.land b8 224) aidx.    (* [comment removed for export] *)

  Definition m_com : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (ctx_usage sc)) (word_to_le_bytes 8 (Z_to_bv 64 (u + c))))
      (Z_to_bv 64 (mt + 24)) (word_to_le_bytes 4 (Z_to_bv 64 AVc)))
      (Z_to_bv 64 (mt + 28)) (word_to_le_bytes 4 (Z_to_bv 64 FRc)))
      (Z_to_bv 64 (mt + 16)) (word_to_le_bytes 8 (Z_to_bv 64 p)))
      (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 mt)))
      (Z_to_bv 64 (p + 8)) [Z_to_bv 8 AIb])
      (Z_to_bv 64 (mt + 32)) (word_to_le_bytes 8 (Z_to_bv 64 Wn)))
      (Z_to_bv 64 (mt + 24)) (word_to_le_bytes 4 (Z_to_bv 64 AVc')))
      (Z_to_bv 64 mt) (word_to_le_bytes 8 (Z_to_bv 64 mt)))
      (Z_to_bv 64 (mt + 8)) (word_to_le_bytes 8 (Z_to_bv 64 mt)))
      (Z_to_bv 64 (ctx_active sc)) (word_to_le_bytes 8 (Z_to_bv 64 mt)).

  Lemma land_le_l' : forall a k, (0 <= a)%Z -> (Z.land a k <= a)%Z.
  Proof using. intros a k Ha. pose proof (Z.sub_land_same_l a k). pose proof (proj2 (Z.land_nonneg a (Z.lnot k)) (or_introl Ha)). lia. Qed.

  Lemma aCommon : forall regs rom,
    getr regs 23 = Z_to_bv 64 (MLOCK + 8 * sc) -> getr regs 21 = Z_to_bv 64 (ctx_active sc) -> getr regs 8 = Z_to_bv 64 sc ->
    getr regs 25 = Z_to_bv 64 c -> getr regs 9 = Z_to_bv 64 mt -> getr regs 10 = Z_to_bv 64 p ->
    getr regs 11 = Z_to_bv 64 (c - 1) -> getr regs 12 = Z_to_bv 64 aidx ->
    exists regs',
      msteps RSEGS (mkst regs (0x679b8 : word) m rom) (mkst regs' (0x67b10 : word) m_com rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 mt
      /\ keeps_but [8; 10; 11; 12; 13; 14]%bv regs regs'.
  Proof using SOK_p SOK_mt SOKc M_b8 M_pv M_nx M_W1 M_act0 M_use Hb8 HW1 Hapart Hp Hmt Hu Haidx Hc Hsc RN.
    intros regs rom H23 H21 H8 H25 H9 H10 H11 H12.
    ceil; unfold ctx_usage, ctx_active, CTX, MLOCK, HEAPLO in *. unfold m_com, AVc, FRc, AVc', Wn, AIb, ctx_usage, ctx_active, CTX.
    (* [comment removed for export] *)
    assert (P1 : (2 <= 2 ^ (aidx + 1))%Z) by (change 2%Z with (2 ^ 1)%Z at 1; apply Z.pow_le_mono_r; lia).
    assert (P2 : (2 ^ (aidx + 1) <= 2 ^ c)%Z) by (apply Z.pow_le_mono_r; lia).
    assert (P3 : (2 ^ c <= 2 ^ 32)%Z) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 32)%Z with 4294967296%Z in P3.
    pose proof (Z.mod_pos_bound W1 4096 ltac:(lia)) as MW.
    assert (LB : (0 <= Z.land b8 224 <= b8)%Z) by (split; [apply Z.land_nonneg; left; lia | apply land_le_l'; lia]).
    pose proof (Z_lor_range32 (Z.land b8 224) aidx ltac:(lia) ltac:(lia)) as LO. change (2 ^ 32)%Z with 4294967296%Z in LO.
    assert (L1 : Z.lor (sc * 64) (c - 1) = (sc * 64 + (c - 1))%Z).
    { rewrite Z.lor_comm. change 64%Z with (2 ^ 6)%Z. rewrite lor_low_high; [lia | | lia | lia]. change (2 ^ 6)%Z with 64%Z. lia. }
    assert (DM : (W1 - W1 mod 4096 = (W1 / 4096) * 2 ^ 12)%Z).
    { change (2 ^ 12)%Z with 4096%Z. pose proof (Z.div_mod W1 4096 ltac:(lia)). lia. }
    assert (DP : (0 <= W1 / 4096)%Z) by (apply Z.div_pos; lia).
    assert (L2 : Z.lor (sc * 64 + (c - 1)) (W1 - W1 mod 4096) = (sc * 64 + (c - 1) + (W1 - W1 mod 4096))%Z).
    { rewrite DM. apply lor_low_high; [change (2 ^ 12)%Z with 4096%Z; lia | exact DP | lia]. }
    eexists. split.
    - stepLD F_67964 D_67964 (word_to_le_bytes 8 (Z_to_bv 64 u)) (Z_to_bv 64 u)
        ltac:(unfold v_addi; unorm; replace (700048 + 8 * sc + 472)%Z with (700056 + 464 + 8 * sc)%Z by lia; exact M_use)
        ltac:(apply bytes_le_to_Z_8).
      stepn F_67968 D_67968. rewrite H25, (v_add_ZZ u c) by lia.
      stepn F_6796c D_6796c.
      stepSTx F_67970 D_67970 (Z_to_bv 64 (700056 + 464 + 8 * sc)) (Z_to_bv 64 (u + c)) ltac:(sok 928%nat SOKc).
      stepn F_67974 D_67974. rewrite H12.
      stepn F_67978 D_67978.
      match goal with |- context [regupd _ 13 ?v] =>
        stepSTx F_6797c D_6797c (Z_to_bv 64 (mt + 24)) v ltac:(sok 40%nat SOK_mt) end.
      rewrite (av_bytes aidx) by lia.
      stepLD F_67980 D_67980 (word_to_le_bytes 4 (Z_to_bv 64 (2 ^ (aidx + 1) - 1))) (Z_to_bv 64 (2 ^ (aidx + 1) - 1))
        ltac:(addr_norm; apply rdn_wbytes_hit4; u_norm; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_67984 D_67984. rewrite H11.
      stepn F_67988 D_67988.
      stepn F_6798c D_6798c.
      match goal with |- context [regupd _ 13 ?v] =>
        stepSTx F_67990 D_67990 (Z_to_bv 64 (mt + 28)) v ltac:(sok 40%nat SOK_mt) end.
      rewrite (fr_bytes c aidx) by lia.
      stepSTx F_67994 D_67994 (Z_to_bv 64 (mt + 16)) (Z_to_bv 64 p) ltac:(sok 40%nat SOK_mt).
      stepSTx F_67998 D_67998 (Z_to_bv 64 p) (Z_to_bv 64 mt) ltac:(sok 9%nat SOK_p).
      stepLD F_6799c D_6799c (word_to_le_bytes 8 (Z_to_bv 64 p)) (Z_to_bv 64 p) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
      stepLBU F_679a0 D_679a0 (Z_to_bv 8 b8) ltac:(addr_norm; rdn_by M_b8). rewrite (u8_Z2bv b8) by lia.
      stepn F_679a4 D_679a4. rewrite H12, (v_andi_Z aidx 31), land31, (Z.mod_small aidx 32) by lia.
      stepn F_679a8 D_679a8. rewrite H11, (v_andi_Z (c - 1) 31), land31, (Z.mod_small (c - 1) 32) by lia.
      stepn F_679ac D_679ac. rewrite (v_andi_Z b8 224) by lia.
      stepn F_679b0 D_679b0. rewrite (v_or_Z (Z.land b8 224) aidx) by lia.
      stepSTx F_679b4 D_679b4 (Z_to_bv 64 (p + 8)) (Z_to_bv 64 (Z.lor (Z.land b8 224) aidx)) ltac:(sok 9%nat SOK_p).
      rewrite (u_Z2bv (Z.lor (Z.land b8 224) aidx)) by lia.
      stepLD F_679b8 D_679b8 (word_to_le_bytes 8 (Z_to_bv 64 W1)) (Z_to_bv 64 W1) ltac:(addr_norm; rdn_by M_W1) ltac:(apply bytes_le_to_Z_8).
      stepn F_679bc D_679bc.
      stepn F_679c0 D_679c0. rewrite H8.
      stepn F_679c4 D_679c4. rewrite (sc_shift sc) by lia.
      stepn F_679c8 D_679c8. rewrite (v_and_Z W1 18446744073709547520) by lia.
      replace (Z.land W1 18446744073709547520) with (W1 - W1 mod 4096)%Z
        by (change 18446744073709547520%Z with (2 ^ 64 - 4096)%Z; symmetry; apply land_hi12; lia).
      stepn F_679cc D_679cc. rewrite (v_or_Z (sc * 64) (c - 1)), L1 by lia.
      stepn F_679d0 D_679d0. rewrite (v_or_Z (sc * 64 + (c - 1)) (W1 - W1 mod 4096)), L2 by lia.
      stepn F_679d4 D_679d4.
      match goal with |- context [regupd _ 10 (v_addi ?w 32)] =>
        replace (v_addi w 32) with (Z_to_bv 64 (sc * 64 + (c - 1) + (W1 - W1 mod 4096) + 32))
          by (unfold v_addi; unorm; reflexivity) end.
      stepSTx F_679d8 D_679d8 (Z_to_bv 64 (mt + 32)) (Z_to_bv 64 (sc * 64 + (c - 1) + (W1 - W1 mod 4096) + 32)) ltac:(sok 40%nat SOK_mt).
      stepLD F_679dc D_679dc (word_to_le_bytes 4 (Z_to_bv 64 (2 ^ (aidx + 1) - 1))) (Z_to_bv 64 (2 ^ (aidx + 1) - 1))
        ltac:(addr_norm; do 5 rdn_peel1; apply rdn_wbytes_hit4; u_norm; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_679e0 D_679e0.
      match goal with |- context [regupd _ 10 ?v] =>
        stepSTx F_679e4 D_679e4 (Z_to_bv 64 (mt + 24)) v ltac:(sok 40%nat SOK_mt) end.
      rewrite (avm1_bytes aidx) by lia.
      stepLD F_679e8 D_679e8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by M_nx) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_679ec D_679ec ltac:(apply c_eq_refl).
      stepLD F_679f4 D_679f4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by M_pv) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_679f8 D_679f8 ltac:(apply c_eq_refl).
      stepLD F_67a00 D_67a00 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by M_act0) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_67a04 D_67a04 ltac:(apply c_eq_refl).
      stepSTx F_67a20 D_67a20 (Z_to_bv 64 mt) (Z_to_bv 64 mt) ltac:(sok 40%nat SOK_mt).
      stepSTx F_67a24 D_67a24 (Z_to_bv 64 (mt + 8)) (Z_to_bv 64 mt) ltac:(sok 40%nat SOK_mt).
      stepn F_67a28 D_67a28.
      stepSTx F_67a2c D_67a2c (Z_to_bv 64 (700056 + 80 + 8 * sc)) (Z_to_bv 64 mt) ltac:(sok 928%nat SOKc).
      stepn F_67a30 D_67a30.
      pu_refl.
    - post.
  Qed.
End Common.
End UbMhASlotW4b.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhCtz OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhSzc OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhMallocH OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2 UbMhASlotW4 UbMhASlotW4b OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac post := repeat split; gres; try reflexivity; try assumption; try solve_keeps_but.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition small_cnt_tab : list Z := [30;30;30; 31;15;15; 20;10;10; 31;15;7; 25;12;6; 21;10;5; 18;8;4; 31;15;7; 28;14;6]%Z.
Definition med_cnt_tab : list Z := [28; 24; 20; 32]%Z.
Definition small_tab (sc i : Z) : Z := nth (Z.to_nat (3 * sc + i)) small_cnt_tab 0%Z.
Definition med_tab (k : Z) : Z := nth (Z.to_nat k) med_cnt_tab 0%Z.

(* [comment removed for export] *)
Definition small_sel (sc u : Z) : Z :=
  if (4 * small_tab sc 0 <=? u)%Z then small_tab sc 0
  else if (4 * small_tab sc 1 <=? u)%Z then small_tab sc 1
  else small_tab sc 2.
(* [comment removed for export] *)
Fixpoint halve1 (f : nat) (c u : Z) : Z :=
  match f with
  | O => c
  | S f' => if (4 * c <=? u)%Z then c else if Z.odd (c / 2) then (c / 2)%Z else halve1 f' (c / 2) u
  end.
(* [comment removed for export] *)
Fixpoint halve2 (f : nat) (size c : Z) : Z :=
  match f with
  | O => c
  | S f' => if (size * c / 2 ^ 20 =? 0)%Z then c else halve2 f' size (c / 2)
  end.
Definition gsel (sc scl u : Z) : Z :=
  if (sc <=? 8)%Z then small_sel sc u else halve2 6 (16 * scl) (halve1 6 (med_tab (sc mod 4)) u).

(* [comment removed for export] *)
Lemma small_tab_rng : forall sc i, (0 <= sc <= 8)%Z -> (0 <= i <= 2)%Z -> (4 <= small_tab sc i <= 31)%Z.
Proof.
  intros sc i Hsc Hi.
  assert (E : exists k, (k < 27)%nat /\ Z.to_nat (3 * sc + i) = k) by (exists (Z.to_nat (3 * sc + i)); split; lia).
  destruct E as (k & Hk & Ek). unfold small_tab. rewrite Ek.
  enum_nat k 27%nat ltac:(cbn; lia).
Qed.

Lemma halve1_cases : forall u k, (0 <= k <= 3)%Z ->
  In (halve1 6 (med_tab k) u) [28; 14; 7; 24; 12; 6; 3; 20; 10; 5; 32; 16; 8; 4; 2; 1]%Z.
Proof.
  intros u k Hk.
  assert (E : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3)%Z) by lia.
  destruct E as [->|[->|[->| ->]]];
    [change (med_tab 0) with 28%Z | change (med_tab 1) with 24%Z | change (med_tab 2) with 20%Z | change (med_tab 3) with 32%Z];
    cbn -[Z.leb Z.mul];
    repeat (match goal with |- context [if (4 * ?c <=? ?uu)%Z then _ else _] => destruct (4 * c <=? uu)%Z end); cbn; tauto.
Qed.

(* [comment removed for export] *)
Definition gsel_c1s : list Z := [28; 14; 7; 24; 12; 6; 3; 20; 10; 5; 32; 16; 8; 4; 2; 1]%Z.
Definition gsel_ok2 (k c1 : Z) : bool :=
  let g := halve2 6 (16 * size_class k) c1 in ((1 <=? g) && (g <=? 32) && (16 * size_class k * g <? 2 ^ 20))%Z.
Lemma gsel_big_check : forallb (fun n => forallb (gsel_ok2 (Z.of_nat n)) gsel_c1s) (seq 9 39) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma gsel_big : forall k c1, (9 <= k < 48)%Z -> In c1 gsel_c1s ->
  (1 <= halve2 6 (16 * size_class k) c1 <= 32)%Z /\ (16 * size_class k * halve2 6 (16 * size_class k) c1 < 2 ^ 20)%Z.
Proof.
  intros k c1 Hk Hc.
  pose proof (proj1 (forallb_forall _ _) gsel_big_check (Z.to_nat k) ltac:(apply in_seq; lia)) as H.
  pose proof (proj1 (forallb_forall _ _) H c1 Hc) as H2. unfold gsel_ok2 in H2.
  rewrite Z2Nat.id in H2 by lia.
  apply andb_prop in H2 as [H2 H3]. apply andb_prop in H2 as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia.
Qed.

Lemma gsel_facts : forall sc scl u, (0 <= sc < 48)%Z -> scl = size_class sc ->
  (1 <= gsel sc scl u <= 32)%Z /\ (16 * scl * gsel sc scl u < 2 ^ 20)%Z /\ (sc = 7%Z -> (gsel sc scl u <= 31)%Z).
Proof.
  intros sc scl u Hsc ->. unfold gsel.
  destruct (sc <=? 8)%Z eqn:E8.
  - apply Z.leb_le in E8. unfold small_sel.
    pose proof (small_tab_rng sc 0 ltac:(lia) ltac:(lia)). pose proof (small_tab_rng sc 1 ltac:(lia) ltac:(lia)).
    pose proof (small_tab_rng sc 2 ltac:(lia) ltac:(lia)).
    assert (SC : (1 <= size_class sc <= 9)%Z).
    { assert (E : exists k, (k < 9)%nat /\ sc = Z.of_nat k) by (exists (Z.to_nat sc); split; lia).
      destruct E as (k & Hk & ->).
      enum_nat k 9%nat ltac:(match goal with |- context [size_class ?x] => let v := eval vm_compute in (size_class x) in change (size_class x) with v end; lia). }
    destruct (4 * small_tab sc 0 <=? u)%Z; [|destruct (4 * small_tab sc 1 <=? u)%Z]; (split; [lia|]); split; try nia.
    all: intros _; lia.
  - apply Z.leb_gt in E8.
    pose proof (Z.mod_pos_bound sc 4 ltac:(lia)) as MB.
    pose proof (halve1_cases u (sc mod 4) ltac:(lia)) as HC.
    (* [comment removed for export] *)
    destruct (gsel_big sc (halve1 6 (med_tab (sc mod 4)) u) ltac:(lia) HC) as [G1 G2].
    split; [exact G1 | split; [exact G2 | intros ->; lia]].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Tabs.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Lemma small_tab_none : forall k, (k < 27)%nat ->
    rdn RSEGS (fun _ => None) (Z_to_bv 64 (A_TAB_SMALL + Z.of_nat k)) 1%nat = Some [Z_to_bv 8 (nth k small_cnt_tab 0%Z)].
  Proof using. intros k Hk. enum_nat k 27%nat ltac:(vm_compute; reflexivity). Qed.
  Lemma small_tab_read : forall mem sc i, img_clear mem A_TAB_SC (A_TAB_MED + 4) -> (0 <= sc <= 8)%Z -> (0 <= i <= 2)%Z ->
    rdn RSEGS mem (Z_to_bv 64 (A_TAB_SMALL + 3 * sc + i)) 1%nat = Some [Z_to_bv 8 (small_tab sc i)].
  Proof using.
    intros mem sc i Himg Hsc Hi. unfold small_tab.
    rewrite (rdn_img RSEGS mem _ 1 A_TAB_SC (A_TAB_MED + 4) Himg) by (unfold A_TAB_SC, A_TAB_SMALL, A_TAB_MED; cbn; lia).
    pose proof (small_tab_none (Z.to_nat (3 * sc + i)) ltac:(lia)) as R. rewrite Z2Nat.id in R by lia.
    rewrite <- Z.add_assoc. exact R.
  Qed.
  Lemma med_tab_none : forall k, (k < 4)%nat ->
    rdn RSEGS (fun _ => None) (Z_to_bv 64 (A_TAB_MED + Z.of_nat k)) 1%nat = Some [Z_to_bv 8 (nth k med_cnt_tab 0%Z)].
  Proof using. intros k Hk. enum_nat k 4%nat ltac:(vm_compute; reflexivity). Qed.
  Lemma med_tab_read : forall mem k, img_clear mem A_TAB_SC (A_TAB_MED + 4) -> (0 <= k <= 3)%Z ->
    rdn RSEGS mem (Z_to_bv 64 (A_TAB_MED + k)) 1%nat = Some [Z_to_bv 8 (med_tab k)].
  Proof using.
    intros mem k Himg Hk. unfold med_tab.
    rewrite (rdn_img RSEGS mem _ 1 A_TAB_SC (A_TAB_MED + 4) Himg) by (unfold A_TAB_SC, A_TAB_MED; cbn; lia).
    pose proof (med_tab_none (Z.to_nat k) ltac:(lia)) as R. rewrite Z2Nat.id in R by lia. exact R.
  Qed.
  Lemma med_tab_rng : forall k, (0 <= k <= 3)%Z -> (20 <= med_tab k <= 32)%Z /\ Z.land (med_tab k) 1 = 0%Z.
  Proof using.
    intros k Hk. assert (E : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3)%Z) by lia.
    destruct E as [->|[->|[->| ->]]];
    [change (med_tab 0) with 28%Z | change (med_tab 1) with 24%Z | change (med_tab 2) with 20%Z | change (med_tab 3) with 32%Z]; (split; [lia | reflexivity]).
  Qed.


  Lemma land3_mod4 : forall a, Z.land a 3 = (a mod 4)%Z.
  Proof using. intros a. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

  Lemma c_lts_ZZ : forall a b, (0 <= a < 2 ^ 63)%Z -> (0 <= b < 2 ^ 63)%Z -> c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
  Proof using. intros a b Ha Hb. rewrite c_lts_small by (u_norm; lia). unfold bv_ltu. u_norm. reflexivity. Qed.

  Lemma v_srliw_small : forall a s, (0 <= a < 2 ^ 31)%Z -> (0 <= s)%Z -> v_srliw (Z_to_bv 64 a) s = Z_to_bv 64 (a / 2 ^ s).
  Proof using.
    intros a s Ha Hs. unfold v_srliw. rewrite (u_Z2bv a) by lia.
    unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite (Z.mod_small a) by lia.
    rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) Hs).
    assert (0 <= a / 2 ^ s <= a)%Z by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]).
    rewrite swrap32_small by lia. reflexivity.
  Qed.

  Lemma land2_odd : forall c, (0 <= c)%Z -> Z.land c 2 = (if Z.odd (c / 2) then 2 else 0)%Z.
  Proof using.
    intros c Hc. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
    change 2%Z with (2 ^ 1)%Z at 1. rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eq_dec n 1) as [->|NE].
    - rewrite Z.eqb_refl, Bool.andb_true_r. change 1%Z with (Z.succ 0). rewrite <- Z.div2_bits, Z.bit0_odd by lia.
      destruct (Z.odd (c / 2)); reflexivity.
    - replace (1 =? n)%Z with false by (symmetry; apply (proj2 (Z.eqb_neq 1 n)); lia). rewrite Bool.andb_false_r.
      symmetry; destruct (Z.odd (c / 2)); [change 2%Z with (2 ^ 1)%Z; rewrite Z.pow2_bits_eqb by lia; apply (proj2 (Z.eqb_neq 1 n)); lia | apply Z.bits_0].
  Qed.
End Tabs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Gsel.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc scl u : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hscl : scl = size_class sc.
  Hypothesis Hu : (0 <= u < 2^64)%Z.
  Hypothesis M_tab : img_clear m A_TAB_SC (A_TAB_MED + 4).
  #[local] Notation size := (16 * scl)%Z.

  Lemma scl_rng : (1 <= scl <= 8191)%Z.
  Proof using Hscl Hsc sc. rewrite Hscl. apply size_class_pos. exact Hsc. Qed.

  (* [comment removed for export] *)
  Lemma gsel_loop1 : forall n c regs rom,
    (0 <= c <= 32)%Z -> (c < 2 ^ Z.of_nat n)%Z ->
    getr regs 13 = Z_to_bv 64 c -> getr regs 10 = Z_to_bv 64 u ->
    exists regs',
      msteps RSEGS (mkst regs (0x67518 : word) m rom) (mkst regs' (0x67540 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 (halve1 n c u) /\ (0 <= halve1 n c u <= c)%Z
      /\ keeps_but [12; 13; 14]%bv regs regs'.
  Proof using Hu.
    induction n as [|n IH]; intros c regs rom Hc Hn H13 H10.
    - cbn in Hn. assert (c = 0)%Z by lia. subst c. cbn [halve1].
      eexists. split.
      + stepn F_674c4 D_674c4. rewrite H13. rewrite (v_slliw_lit 0 2) by lia.
        stepb_tk F_674c8 D_674c8 ltac:(rewrite H10; unfold c_ltu; rewrite ?Bool.negb_true_iff; unfold bv_ltu; u_norm; apply Z.ltb_ge; lia).
        stepn F_674e8 D_674e8. rewrite H13.
        pu_refl.
      + post; try lia.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia. cbn [halve1].
      destruct (4 * c <=? u)%Z eqn:B4.
      + apply Z.leb_le in B4. eexists. split.
        * stepn F_674c4 D_674c4. rewrite H13. rewrite (v_slliw_lit c 2) by lia. change (2 ^ 2)%Z with 4%Z.
          stepb_tk F_674c8 D_674c8 ltac:(rewrite H10; unfold c_ltu; rewrite ?Bool.negb_true_iff; unfold bv_ltu; u_norm; apply Z.ltb_ge; lia).
          stepn F_674e8 D_674e8. rewrite H13.
          pu_refl.
        * post; try lia.
      + apply Z.leb_gt in B4.
        assert (D2 : (0 <= c / 2 <= 16)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
        assert (D2c : (c / 2 <= c)%Z) by (apply Z.div_le_upper_bound; lia).
        assert (D2n : (c / 2 < 2 ^ Z.of_nat n)%Z) by (apply Z.div_lt_upper_bound; lia).
        pose proof (land2_odd c ltac:(lia)) as L2.
        destruct (Z.odd (c / 2)) eqn:OD; try rewrite OD in L2.
        * eexists. split.
          -- stepn F_674c4 D_674c4. rewrite H13. rewrite (v_slliw_lit c 2) by lia. change (2 ^ 2)%Z with 4%Z.
             stepb_ft F_674c8 D_674c8 ltac:(rewrite H10; unfold c_ltu; rewrite ?Bool.negb_false_iff; unfold bv_ltu; u_norm; apply Z.ltb_lt; lia).
             stepn F_674cc D_674cc. rewrite H13, (v_srliw_small c 1) by lia. change (2 ^ 1)%Z with 2%Z.
             stepn F_674d0 D_674d0. rewrite H13, (v_andi_Z c 2), L2 by lia.
             stepn F_674d4 D_674d4.
             stepb_ft F_674d8 D_674d8 ltac:(cond_compute).
             stepn F_674dc D_674dc.
             pu_refl.
          -- post; try lia.
        * edestruct (IH (c / 2)%Z (regupd (regupd (regupd (regupd regs 12 (Z_to_bv 64 (c * 4))) 12 (Z_to_bv 64 (c / 2))) 14 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (c / 2))) rom)
            as (r2 & S2 & A12 & R2 & K2); [lia | lia | gres; reflexivity | gres; exact H10 |].
          eexists. split.
          -- stepn F_674c4 D_674c4. rewrite H13. rewrite (v_slliw_lit c 2) by lia. change (2 ^ 2)%Z with 4%Z.
             stepb_ft F_674c8 D_674c8 ltac:(rewrite H10; unfold c_ltu; rewrite ?Bool.negb_false_iff; unfold bv_ltu; u_norm; apply Z.ltb_lt; lia).
             stepn F_674cc D_674cc. rewrite H13, (v_srliw_small c 1) by lia. change (2 ^ 1)%Z with 2%Z.
             stepn F_674d0 D_674d0. rewrite H13, (v_andi_Z c 2), L2 by lia.
             stepn F_674d4 D_674d4.
             stepb_tk F_674d8 D_674d8 ltac:(cond_compute).
             exact S2.
          -- post; try lia. eapply keeps_but_trans; [| exact K2]. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma gsel_loop2 : forall n c regs rom,
    (0 <= c <= 32)%Z -> (c < 2 ^ Z.of_nat n)%Z ->
    getr regs 12 = Z_to_bv 64 c -> getr regs 24 = Z_to_bv 64 size ->
    exists regs',
      msteps RSEGS (mkst regs (0x67540 : word) m rom) (mkst regs' (0x67554 : word) m rom)
      /\ getr regs' 19 = Z_to_bv 64 (halve2 n size c) /\ (0 <= halve2 n size c <= c)%Z
      /\ keeps_but [12; 13; 19]%bv regs regs'.
  Proof using Hscl Hsc sc.
    pose proof scl_rng as SR.
    induction n as [|n IH]; intros c regs rom Hc Hn H12 H24.
    - cbn in Hn. assert (c = 0)%Z by lia. subst c. cbn [halve2].
      eexists. split.
      + stepn F_674ec D_674ec. rewrite H12.
        stepn F_674f0 D_674f0. rewrite H24, H12, (v_mul_Z size 0) by lia.
        stepn F_674f4 D_674f4. rewrite (v_srli_Z (size * 0) 20) by lia.
        replace (size * 0 / 2 ^ 20)%Z with 0%Z by (rewrite Z.mul_0_r; reflexivity).
        stepn F_674f8 D_674f8. try rewrite (v_srliw_small 0 1) by lia.
        stepb_ft F_674fc D_674fc ltac:(apply c_eq_refl).
        pu_refl.
      + post; try lia.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia. cbn [halve2].
      assert (MR : (0 <= size * c <= 16 * 8191 * 32)%Z) by nia.
      assert (QR : (0 <= size * c / 2 ^ 20 < 2 ^ 40)%Z).
      { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 20 * 2 ^ 40)%Z with (2 ^ 60)%Z. lia. }
      assert (D2 : (0 <= c / 2 <= 16)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      assert (D2c : (c / 2 <= c)%Z) by (apply Z.div_le_upper_bound; lia).
      assert (D2n : (c / 2 < 2 ^ Z.of_nat n)%Z) by (apply Z.div_lt_upper_bound; lia).
      destruct (size * c / 2 ^ 20 =? 0)%Z eqn:BQ.
      + apply Z.eqb_eq in BQ. eexists. split.
        * stepn F_674ec D_674ec. rewrite H12.
          stepn F_674f0 D_674f0. rewrite H24, H12, (v_mul_Z size c) by lia.
          stepn F_674f4 D_674f4. rewrite (v_srli_Z (size * c) 20), BQ by lia.
          stepn F_674f8 D_674f8. rewrite (v_srliw_small c 1) by lia. change (2 ^ 1)%Z with 2%Z.
          stepb_ft F_674fc D_674fc ltac:(apply c_eq_refl).
          pu_refl.
        * post; try lia.
      + apply Z.eqb_neq in BQ.
        edestruct (IH (c / 2)%Z (regupd (regupd (regupd (regupd regs 19 (Z_to_bv 64 c)) 12 (Z_to_bv 64 (size * c))) 13 (Z_to_bv 64 (size * c / 2 ^ 20))) 12 (Z_to_bv 64 (c / 2))) rom)
            as (r2 & S2 & A19 & R2 & K2); [lia | lia | gres; reflexivity | gres; exact H24 |].
        eexists. split.
        * stepn F_674ec D_674ec. rewrite H12.
          stepn F_674f0 D_674f0. rewrite H24, H12, (v_mul_Z size c) by lia.
          stepn F_674f4 D_674f4. rewrite (v_srli_Z (size * c) 20) by lia.
          stepn F_674f8 D_674f8. rewrite (v_srliw_small c 1) by lia. change (2 ^ 1)%Z with 2%Z.
          stepb_tk F_674fc D_674fc ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact BQ).
          exact S2.
        * post; try lia. eapply keeps_but_trans; [| exact K2]. solve_keeps_but.
  Qed.

  Ltac geu_tk' := unfold c_ltu; rewrite ?Bool.negb_true_iff; unfold bv_ltu; u_norm; apply Z.ltb_ge; lia.
  Ltac geu_ft' := unfold c_ltu; rewrite ?Bool.negb_false_iff; unfold bv_ltu; u_norm; apply Z.ltb_lt; lia.

  Lemma aGsel : forall regs rom,
    getr regs 10 = Z_to_bv 64 u -> getr regs 12 = Z_to_bv 64 8 -> getr regs 8 = Z_to_bv 64 sc ->
    getr regs 19 = Z_to_bv 64 (2 * sc) -> getr regs 24 = Z_to_bv 64 size -> getr regs 25 = Z_to_bv 64 A_TAB_SC ->
    exists regs',
      msteps RSEGS (mkst regs (0x674c8 : word) m rom) (mkst regs' (0x67554 : word) m rom)
      /\ getr regs' 19 = Z_to_bv 64 (gsel sc scl u)
      /\ keeps_but [12; 13; 14; 19]%bv regs regs'.
  Proof using M_tab Hu Hscl Hsc.
    intros regs rom H10 H12 H8 H19 H24 H25. unfold gsel. pose proof scl_rng as SR.
    destruct (sc <=? 8)%Z eqn:E8.
    - apply Z.leb_le in E8. unfold small_sel.
      pose proof (small_tab_read m sc 0 M_tab ltac:(lia) ltac:(lia)) as T0.
      pose proof (small_tab_read m sc 1 M_tab ltac:(lia) ltac:(lia)) as T1.
      pose proof (small_tab_read m sc 2 M_tab ltac:(lia) ltac:(lia)) as T2. unfold A_TAB_SMALL in T0, T1, T2.
      pose proof (small_tab_rng sc 0 ltac:(lia) ltac:(lia)) as R0. pose proof (small_tab_rng sc 1 ltac:(lia) ltac:(lia)) as R1.
      pose proof (small_tab_rng sc 2 ltac:(lia) ltac:(lia)) as R2.
      Ltac g2_pre H12 H8 H19 T0 :=
        stepb_ft F_67474 D_67474 ltac:(rewrite H12, H8, c_lts_ZZ by lia; apply Z.ltb_ge; lia);
        stepn F_67478 D_67478; rewrite H19, H8, (v_add_ZZ (2 * sc) sc) by lia;
        stepn F_6747c D_6747c;
        stepn F_67480 D_67480; vals_lit;
        stepn F_67484 D_67484; rewrite (v_add_ZZ 145868 (2 * sc + sc)) by lia;
        replace (145868 + (2 * sc + sc))%Z with (145868 + 3 * sc)%Z by lia;
        stepLBU F_67488 D_67488 (Z_to_bv 8 (small_tab sc 0)) ltac:(addr_norm; first [exact T0 | replace (145868 + 3 * sc)%Z with (145868 + 3 * sc + 0)%Z by lia; exact T0]);
        rewrite (u8_Z2bv (small_tab sc 0)) by lia;
        stepn F_6748c D_6748c; rewrite (v_slli_Z (small_tab sc 0) 2) by lia; change (2 ^ 2)%Z with 4%Z.
      destruct (4 * small_tab sc 0 <=? u)%Z eqn:B0.
      + apply Z.leb_le in B0. eexists. split.
        * g2_pre H12 H8 H19 T0.
          stepb_tk F_67490 D_67490 ltac:(rewrite H10; geu_tk').
          pu_refl.
        * post; try (f_equal; lia).
      + apply Z.leb_gt in B0.
        destruct (4 * small_tab sc 1 <=? u)%Z eqn:B1.
        * apply Z.leb_le in B1. eexists. split.
          -- g2_pre H12 H8 H19 T0.
             stepb_ft F_67490 D_67490 ltac:(rewrite H10; geu_ft').
             stepLBU F_67494 D_67494 (Z_to_bv 8 (small_tab sc 1)) ltac:(unfold v_addi; unorm; exact T1).
             rewrite (u8_Z2bv (small_tab sc 1)) by lia.
             stepn F_67498 D_67498. rewrite (v_slli_Z (small_tab sc 1) 2) by lia. change (2 ^ 2)%Z with 4%Z.
             stepb_tk F_6749c D_6749c ltac:(rewrite H10; geu_tk').
             pu_refl.
          -- post; try (f_equal; lia).
        * apply Z.leb_gt in B1. eexists. split.
          -- g2_pre H12 H8 H19 T0.
             stepb_ft F_67490 D_67490 ltac:(rewrite H10; geu_ft').
             stepLBU F_67494 D_67494 (Z_to_bv 8 (small_tab sc 1)) ltac:(unfold v_addi; unorm; exact T1).
             rewrite (u8_Z2bv (small_tab sc 1)) by lia.
             stepn F_67498 D_67498. rewrite (v_slli_Z (small_tab sc 1) 2) by lia. change (2 ^ 2)%Z with 4%Z.
             stepb_ft F_6749c D_6749c ltac:(rewrite H10; geu_ft').
             stepLBU F_674a0 D_674a0 (Z_to_bv 8 (small_tab sc 2)) ltac:(unfold v_addi; unorm; exact T2).
             rewrite (u8_Z2bv (small_tab sc 2)) by lia.
             stepn F_674a4 D_674a4.
             pu_refl.
          -- post.
    - apply Z.leb_gt in E8.
      pose proof (Z.mod_pos_bound sc 4 ltac:(lia)) as MB.
      pose proof (med_tab_read m (sc mod 4) M_tab ltac:(lia)) as TM. unfold A_TAB_MED in TM.
      pose proof (med_tab_rng (sc mod 4) ltac:(lia)) as [MR ME].
      set (c0 := med_tab (sc mod 4)) in *.
      assert (PRE : exists r0, msteps RSEGS (mkst regs (0x674c8 : word) m rom) (mkst r0 (0x67518 : word) m rom)
        /\ getr r0 13 = Z_to_bv 64 c0 /\ getr r0 10 = Z_to_bv 64 u /\ getr r0 24 = Z_to_bv 64 size
        /\ keeps_but [12; 13; 14; 19]%bv regs r0).
      { eexists. split.
        - stepb_tk F_67474 D_67474 ltac:(rewrite H12, H8, c_lts_ZZ by lia; apply Z.ltb_lt; lia).
          stepn F_674a8 D_674a8. rewrite H8, (v_andi_Z sc 3), land3_mod4 by lia.
          stepn F_674ac D_674ac.
          stepn F_674b0 D_674b0. vals_lit.
          stepn F_674b4 D_674b4. rewrite (v_add_ZZ 145895 (sc mod 4)) by lia.
          stepLBU F_674b8 D_674b8 (Z_to_bv 8 c0) ltac:(addr_norm; first [exact TM | replace (145895 + sc mod 4 + 0)%Z with (145895 + sc mod 4)%Z by lia; exact TM]).
          rewrite (u8_Z2bv c0) by lia.
          stepn F_674bc D_674bc. rewrite (v_andi_Z c0 1), ME by lia.
          stepb_ft F_674c0 D_674c0 ltac:(cond_compute).
          pu_refl.
        - post. }
      destruct PRE as (r0 & S0 & A13 & A10 & A24 & K0).
      edestruct (gsel_loop1 6 c0 r0 rom) as (r1 & S1 & B12 & R1 & K1); [lia | change (2 ^ Z.of_nat 6)%Z with 64%Z; lia | exact A13 | exact A10 |].
      edestruct (gsel_loop2 6 (halve1 6 c0 u) r1 rom) as (r2 & S2 & C19 & R2 & K2); [lia | change (2 ^ Z.of_nat 6)%Z with 64%Z; lia | exact B12 | kept_rw K1; exact A24 |].
      exists r2. split; [| split; [exact C19|]].
      + eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1 | exact S2].
      + eapply keeps_but_trans; [exact K0|]. eapply keeps_but_trans.
        * exact (fun r Hr => K1 r ltac:(intros Hin; apply Hr; cbv in Hin |- *; tauto)).
        * exact (fun r Hr => K2 r ltac:(intros Hin; apply Hr; cbv in Hin |- *; tauto)).
  Qed.
End Gsel.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nosmall_of (b : Z) : Z := if (b <? 100)%Z then 0 else 1.
Definition bounce_upd (b : Z) : Z := if (b <? 99)%Z then b + 1 else 150.

Section M1.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc b useq seq : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hb : (0 <= b < 256)%Z.
  Hypothesis Huseq : (0 <= useq < 256)%Z.
  Hypothesis Hseq : (0 <= seq < 256)%Z.
  Hypothesis M_seq : rdn RSEGS m (Z_to_bv 64 ctx_seq) 1%nat = Some [Z_to_bv 8 seq].
  Hypothesis SOKc : store_ok RSEGS m (Z_to_bv 64 CTX) 928%nat = true.

  Lemma c_lts_pos_neg : forall a (y : word), (0 <= a < 2 ^ 63)%Z -> (2 ^ 63 <= bv_unsigned y)%Z -> c_lts (Z_to_bv 64 a) y = false.
  Proof using.
    intros a y Ha Hy. unfold c_lts, bv_lts. rewrite bv_signed_small by (u_norm; lia). rewrite bv_signed_hi by exact Hy.
    apply Z.ltb_ge. pose proof (u64_range y). u_norm. lia.
  Qed.

  Lemma nosmall_norm : v_xori (v_sltiu (Z_to_bv 64 b) 100) 1 = Z_to_bv 64 (nosmall_of b).
  Proof using Hb.
    unfold nosmall_of, v_sltiu. u_norm. change (bv_wrap 64 100) with 100%Z.
    destruct (b <? 100)%Z; apply bv_eq; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma aM1out : forall regs rom,
    getr regs 8 = Z_to_bv 64 sc -> getr regs 22 = Z_to_bv 64 MLOCK -> (sc < 7 \/ 38 < sc)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x6757c : word) m rom) (mkst regs' (0x67830 : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 seq
      /\ keeps_but [13; 15; 16]%bv regs regs'.
  Proof using M_seq Hseq Hsc.
    intros regs rom H8 H22 Hout. unfold ctx_seq, CTX, MLOCK in *.
    destruct Hout as [L|G].
    - eexists. split.
      + stepn F_67528 D_67528. rewrite H8, v_addiw_Z_s32, s32_neg_small by lia.
        stepn F_6752c D_6752c.
        stepb_tk F_67530 D_67530 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
        stepn F_67608 D_67608.
        stepn F_6760c D_6760c.
        stepLBU F_677d8 D_677d8 (Z_to_bv 8 seq) ltac:(addr_norm; exact M_seq). rewrite (u8_Z2bv seq) by lia.
        pu_refl.
      + post.
    - eexists. split.
      + stepn F_67528 D_67528. rewrite H8, v_addiw_Z_s32, s32_small by lia.
        stepn F_6752c D_6752c.
        stepb_tk F_67530 D_67530 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
        stepn F_67608 D_67608.
        stepn F_6760c D_6760c.
        stepLBU F_677d8 D_677d8 (Z_to_bv 8 seq) ltac:(addr_norm; exact M_seq). rewrite (u8_Z2bv seq) by lia.
        pu_refl.
      + post.
  Qed.

  Section In.
    Hypothesis Hin : (7 <= sc <= 38)%Z.
    Hypothesis M_bnc : rdn RSEGS m (Z_to_bv 64 (ctx_bounces (sc - 7))) 1%nat = Some [Z_to_bv 8 b].
    Hypothesis M_useq : rdn RSEGS m (Z_to_bv 64 (ctx_unmap_seq (sc - 7))) 1%nat = Some [Z_to_bv 8 useq].

    (* [comment removed for export] *)
    Ltac m1_pre H8 H22 :=
      stepn F_67528 D_67528; rewrite H8, v_addiw_Z_s32, s32_small by lia; replace (sc + -7)%Z with (sc - 7)%Z by lia;
      stepn F_6752c D_6752c;
      stepb_ft F_67530 D_67530 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
      stepn F_67534 D_67534; rewrite H22, (v_add_ZZ 700048 (sc - 7)) by lia;
      stepLBU F_67538 D_67538 (Z_to_bv 8 b) ltac:(unfold v_addi; unorm; replace (700048 + (sc - 7) + 888)%Z with (700056 + 880 + (sc - 7))%Z by lia; exact M_bnc);
      rewrite (u8_Z2bv b) by lia;
      stepLBU F_6753c D_6753c (Z_to_bv 8 useq) ltac:(unfold v_addi; unorm; replace (700048 + (sc - 7) + 856)%Z with (700056 + 848 + (sc - 7))%Z by lia; exact M_useq);
      rewrite (u8_Z2bv useq) by lia;
      stepn F_67540 D_67540;
      stepn F_67544 D_67544; rewrite nosmall_norm.

    (* [comment removed for export] *)
    Lemma aM1nb : forall regs rom,
      getr regs 8 = Z_to_bv 64 sc -> getr regs 22 = Z_to_bv 64 MLOCK -> (useq = 0 \/ 10 <= seq - useq)%Z ->
      exists regs',
        msteps RSEGS (mkst regs (0x6757c : word) m rom) (mkst regs' (0x67830 : word) m rom)
        /\ getr regs' 13 = Z_to_bv 64 (nosmall_of b) /\ getr regs' 16 = Z_to_bv 64 seq
        /\ keeps_but [5; 6; 13; 15; 16; 17]%bv regs regs'.
    Proof using M_useq M_bnc Hin M_seq Hseq Huseq Hb Hsc.
      intros regs rom H8 H22 Hnb. unfold ctx_seq, ctx_bounces, ctx_unmap_seq, CTX, MLOCK in *.
      destruct (Z.eq_dec useq 0) as [Z0|NZ].
      - eexists. split.
        + m1_pre H8 H22.
          stepb_tk F_67548 D_67548 ltac:(rewrite Z0; apply c_eq_refl).
          stepLBU F_677d8 D_677d8 (Z_to_bv 8 seq) ltac:(addr_norm; exact M_seq). rewrite (u8_Z2bv seq) by lia.
          pu_refl.
        + post.
      - assert (D10 : (10 <= seq - useq)%Z) by lia.
        eexists. split.
        + m1_pre H8 H22.
          stepb_ft F_67548 D_67548 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact NZ).
          stepLBU F_6754c D_6754c (Z_to_bv 8 seq) ltac:(addr_norm; exact M_seq). rewrite (u8_Z2bv seq) by lia.
          stepn F_67550 D_67550. rewrite (v_sub_ZZ seq useq) by lia.
          stepn F_67554 D_67554.
          stepb_tk F_67558 D_67558 ltac:(rewrite c_lts_ZZ by lia; apply Z.ltb_lt; lia).
          pu_refl.
        + post.
    Qed.

    (* [comment removed for export] *)
    Definition m_bnc : mem := wbytes m (Z_to_bv 64 (ctx_bounces (sc - 7))) [Z_to_bv 8 (bounce_upd b)].

    Lemma aM1b : forall regs rom,
      getr regs 8 = Z_to_bv 64 sc -> getr regs 22 = Z_to_bv 64 MLOCK -> useq <> 0%Z -> (seq - useq <= 9)%Z ->
      exists regs',
        msteps RSEGS (mkst regs (0x6757c : word) m rom) (mkst regs' (0x67830 : word) m_bnc rom)
        /\ getr regs' 13 = Z_to_bv 64 (nosmall_of b) /\ getr regs' 16 = Z_to_bv 64 seq
        /\ keeps_but [5; 6; 13; 15; 16; 17]%bv regs regs'.
    Proof using M_useq M_bnc Hin SOKc M_seq Hseq Huseq Hb Hsc.
      intros regs rom H8 H22 NZ D9. unfold m_bnc. unfold ctx_seq, ctx_bounces, ctx_unmap_seq, CTX, MLOCK in *. unfold bounce_upd.
      (* [comment removed for export] *)
      assert (CMP : c_lts (Z_to_bv 64 9) (v_sub (Z_to_bv 64 seq) (Z_to_bv 64 useq)) = false).
      { destruct (Z_le_gt_dec useq seq).
        - rewrite (v_sub_ZZ seq useq) by lia. rewrite c_lts_ZZ by lia. apply Z.ltb_ge. lia.
        - apply c_lts_pos_neg; [lia|]. unfold v_sub. rewrite (u_Z2bv seq), (u_Z2bv useq), Z_to_bv_unsigned by lia. unfold bv_wrap.
          change (bv_modulus 64) with (2 ^ 64)%Z.
          rewrite <- (Z.mod_unique (seq - useq) (2 ^ 64) (-1) (seq - useq + 2 ^ 64)) by lia. lia. }
      destruct (b <? 99)%Z eqn:B99.
      - apply Z.ltb_lt in B99. eexists. split.
        + m1_pre H8 H22.
          stepb_ft F_67548 D_67548 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact NZ).
          stepLBU F_6754c D_6754c (Z_to_bv 8 seq) ltac:(addr_norm; exact M_seq). rewrite (u8_Z2bv seq) by lia.
          stepn F_67550 D_67550.
          stepn F_67554 D_67554.
          stepb_ft F_67558 D_67558 ltac:(exact CMP).
          stepn F_6755c D_6755c.
          stepb_tk F_67560 D_67560 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
          stepn F_677d0 D_677d0. addi_renorm.
          stepSTx F_677d4 D_677d4 (Z_to_bv 64 (700056 + 880 + (sc - 7))) (Z_to_bv 64 (b + 1)) ltac:(sok 928%nat SOKc).
          rewrite (u_Z2bv (b + 1)) by lia.
          stepLBU F_677d8 D_677d8 (Z_to_bv 8 seq) ltac:(addr_norm; rdn_by M_seq). rewrite (u8_Z2bv seq) by lia.
          pu_refl.
        + post.
      - apply Z.ltb_ge in B99. eexists. split.
        + m1_pre H8 H22.
          stepb_ft F_67548 D_67548 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact NZ).
          stepLBU F_6754c D_6754c (Z_to_bv 8 seq) ltac:(addr_norm; exact M_seq). rewrite (u8_Z2bv seq) by lia.
          stepn F_67550 D_67550.
          stepn F_67554 D_67554.
          stepb_ft F_67558 D_67558 ltac:(exact CMP).
          stepn F_6755c D_6755c.
          stepb_ft F_67560 D_67560 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepn F_67564 D_67564.
          stepn F_67568 D_67568.
          stepSTx F_677d4 D_677d4 (Z_to_bv 64 (700056 + 880 + (sc - 7))) (Z_to_bv 64 150) ltac:(sok 928%nat SOKc).
          rewrite (u_Z2bv 150) by lia.
          stepLBU F_677d8 D_677d8 (Z_to_bv 8 seq) ltac:(addr_norm; rdn_by M_seq). rewrite (u8_Z2bv seq) by lia.
          pu_refl.
        + post.
    Qed.
  End In.
End M1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Seq.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (M : mem) (seq : Z).
  Hypothesis Hseq : (0 <= seq < 256)%Z.
  Hypothesis SOKc : store_ok RSEGS M (Z_to_bv 64 CTX) 928%nat = true.

  Definition m_seqN : mem := wbytes M (Z_to_bv 64 ctx_seq) [Z_to_bv 8 (seq + 1)].
  Definition m_seqW : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (ctx_unmap_seq 0)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (ctx_unmap_seq 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (ctx_unmap_seq 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (ctx_unmap_seq 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 ctx_seq) [Z_to_bv 8 1].

  Lemma aSeqN : forall regs rom,
    getr regs 16 = Z_to_bv 64 seq -> getr regs 22 = Z_to_bv 64 MLOCK -> seq <> 255%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x67830 : word) M rom) (mkst regs' (0x6785c : word) m_seqN rom)
      /\ getr regs' 15 = Z_to_bv 64 31 /\ getr regs' 16 = Z_to_bv 64 (seq + 1)
      /\ keeps_but [15; 16]%bv regs regs'.
  Proof using SOKc Hseq.
    intros regs rom H16 H22 NE. unfold m_seqN, ctx_seq, ctx_unmap_seq, CTX, MLOCK in *.
    eexists. split.
    - stepn F_677dc D_677dc.
      stepb_tk F_677e0 D_677e0 ltac:(rewrite H16, c_eq_Z by lia; apply Z.eqb_neq; exact NE).
      stepn F_677fc D_677fc. rewrite H16. addi_renorm.
      stepn F_67800 D_67800.
      stepSTx F_67804 D_67804 (Z_to_bv 64 (700056 + 912)) (Z_to_bv 64 (seq + 1)) ltac:(sok 928%nat SOKc).
      rewrite (u_Z2bv (seq + 1)) by lia.
      pu_refl.
    - post.
  Qed.

  Lemma aSeqW : forall regs rom,
    getr regs 16 = Z_to_bv 64 seq -> getr regs 22 = Z_to_bv 64 MLOCK -> seq = 255%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x67830 : word) M rom) (mkst regs' (0x6785c : word) m_seqW rom)
      /\ getr regs' 15 = Z_to_bv 64 31 /\ getr regs' 16 = Z_to_bv 64 1
      /\ keeps_but [15; 16]%bv regs regs'.
  Proof using SOKc.
    intros regs rom H16 H22 E. unfold m_seqW, ctx_seq, ctx_unmap_seq, CTX, MLOCK in *.
    eexists. split.
    - stepn F_677dc D_677dc.
      stepb_ft F_677e0 D_677e0 ltac:(rewrite H16, E; apply c_eq_refl).
      stepSTx F_677e4 D_677e4 (Z_to_bv 64 (700056 + 848 + 0)) (Z_to_bv 64 0) ltac:(sok 928%nat SOKc).
      stepSTx F_677e8 D_677e8 (Z_to_bv 64 (700056 + 848 + 8)) (Z_to_bv 64 0) ltac:(sok 928%nat SOKc).
      stepSTx F_677ec D_677ec (Z_to_bv 64 (700056 + 848 + 16)) (Z_to_bv 64 0) ltac:(sok 928%nat SOKc).
      stepSTx F_677f0 D_677f0 (Z_to_bv 64 (700056 + 848 + 24)) (Z_to_bv 64 0) ltac:(sok 928%nat SOKc).
      stepn F_677f4 D_677f4.
      stepn F_677f8 D_677f8.
      stepn F_67800 D_67800.
      stepSTx F_67804 D_67804 (Z_to_bv 64 (700056 + 912)) (Z_to_bv 64 1) ltac:(sok 928%nat SOKc).
      rewrite (u_Z2bv 1) by lia.
      pu_refl.
    - post.
  Qed.
End Seq.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ucoarse (sc u u1 : Z) : Z := if ((sc <? 32) && (sc mod 2 =? 0))%Z%bool then (u + u1) mod 2 ^ 64 else u.   (* [comment removed for export] *)
Definition mred (sc size cnt u' nosm : Z) : Z :=
  if ((4 * cnt <=? u') || negb (nosm =? 0))%Z%bool then cnt
  else if (sc mod 4 =? 1)%Z then (if (32768 <? size * cnt)%Z then 2 else cnt)
  else if (sc mod 4 =? 2)%Z then (if (16384 <? size * cnt)%Z then 3 else cnt)
  else if (sc mod 4 =? 0)%Z then (if (32768 <? size * cnt)%Z then 3 else if (8192 <? size * cnt)%Z then 5 else cnt)
  else cnt.

Section M2.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (M : mem) (sc scl cnt u u1 nosm : Z).
  #[local] Notation size := (16 * scl)%Z.
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hscl : (1 <= scl <= 8191)%Z.
  Hypothesis Hcnt : (1 <= cnt <= 32)%Z.
  Hypothesis Hu : (0 <= u < 2^64)%Z.
  Hypothesis Hu1 : (0 <= u1 < 2^64)%Z.
  Hypothesis Hnosm : (0 <= nosm <= 1)%Z.
  Hypothesis M_use1 : (sc < 32)%Z -> (sc mod 2 = 0)%Z ->
    rdn RSEGS M (Z_to_bv 64 (ctx_usage (sc + 1))) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 u1)).
  #[local] Notation u' := (ucoarse sc u u1).

  Lemma ucoarse_rng : (0 <= u' < 2^64)%Z.
  Proof using Hu.
    unfold ucoarse. pose proof (Z.mod_pos_bound (u + u1) (2 ^ 64) ltac:(lia)).
    destruct ((sc <? 32) && (sc mod 2 =? 0))%Z%bool; lia.
  Qed.

  Lemma aM2 : forall regs rom,
    getr regs 15 = Z_to_bv 64 31 -> getr regs 8 = Z_to_bv 64 sc -> getr regs 23 = Z_to_bv 64 (MLOCK + 8 * sc) ->
    getr regs 10 = Z_to_bv 64 u -> getr regs 19 = Z_to_bv 64 cnt -> getr regs 13 = Z_to_bv 64 nosm ->
    getr regs 11 = Z_to_bv 64 4096 -> getr regs 14 = Z_to_bv 64 (size * cnt) ->
    exists regs',
      msteps RSEGS (mkst regs (0x6785c : word) M rom) (mkst regs' (0x678e4 : word) M rom)
      /\ getr regs' 25 = Z_to_bv 64 (mred sc size cnt u' nosm) /\ getr regs' 10 = Z_to_bv 64 u'
      /\ keeps_but [5; 10; 15; 16; 17; 19; 25]%bv regs regs'.
  Proof using M_use1 Hnosm Hu1 Hu Hcnt Hscl Hsc.
    intros regs rom H15 H8 H23 H10 H19 H13 H11 H14. unfold ctx_usage, CTX, MLOCK in *.
    pose proof (Z.mod_pos_bound sc 2 ltac:(lia)) as MB2. pose proof (Z.mod_pos_bound sc 4 ltac:(lia)) as MB4.
    pose proof ucoarse_rng as UR.
    assert (SCM : (0 <= size * cnt <= 16 * 8191 * 32)%Z) by nia.
    (* [comment removed for export] *)
    assert (PRE : exists r1, msteps RSEGS (mkst regs (0x6785c : word) M rom) (mkst r1 (0x67870 : word) M rom)
      /\ getr r1 10 = Z_to_bv 64 u' /\ getr r1 8 = Z_to_bv 64 sc /\ getr r1 19 = Z_to_bv 64 cnt /\ getr r1 13 = Z_to_bv 64 nosm
      /\ getr r1 11 = Z_to_bv 64 4096 /\ getr r1 14 = Z_to_bv 64 (size * cnt)
      /\ keeps_but [5; 10; 15; 16; 17; 19; 25]%bv regs r1).
    { unfold ucoarse. destruct (Z_lt_dec sc 32) as [L32|G32].
      - replace (sc <? 32)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
        destruct (Z.eq_dec (sc mod 2) 0) as [EV|OD].
        + replace (sc mod 2 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia).
          eexists. split.
          * stepb_ft F_67808 D_67808 ltac:(rewrite H15, H8, c_lts_ZZ by lia; apply Z.ltb_ge; lia).
            stepn F_6780c D_6780c. rewrite H8, (v_andi_Z sc 1), land1_mod2, EV by lia.
            stepb_ft F_67810 D_67810 ltac:(apply c_eq_refl).
            stepLD F_67814 D_67814 (word_to_le_bytes 8 (Z_to_bv 64 u1)) (Z_to_bv 64 u1)
              ltac:(unfold v_addi; unorm; replace (700048 + 8 * sc + 480)%Z with (700056 + 464 + 8 * (sc + 1))%Z by lia; exact (M_use1 L32 EV))
              ltac:(apply bytes_le_to_Z_8).
            stepn F_67818 D_67818. rewrite H10, (v_add_ZZ u1 u) by lia. rewrite (Z.add_comm u1 u), (Z_to_bv_mod64 (u + u1)).
            pu_refl.
          * post.
        + replace (sc mod 2 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
          eexists. split.
          * stepb_ft F_67808 D_67808 ltac:(rewrite H15, H8, c_lts_ZZ by lia; apply Z.ltb_ge; lia).
            stepn F_6780c D_6780c. rewrite H8, (v_andi_Z sc 1), land1_mod2 by lia. replace (sc mod 2)%Z with 1%Z by lia.
            stepb_tk F_67810 D_67810 ltac:(cond_compute).
            pu_refl.
          * post.
      - replace (sc <? 32)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
        eexists. split.
        + stepb_tk F_67808 D_67808 ltac:(rewrite H15, H8, c_lts_ZZ by lia; apply Z.ltb_lt; lia).
          pu_refl.
        + post. }
    destruct PRE as (r1 & S1 & A10 & A8 & A19 & A13 & A11 & A14 & K1).
    set (uu := ucoarse sc u u1) in *.
    (* [comment removed for export] *)
    Ltac geu_tk := unfold c_ltu; rewrite ?Bool.negb_true_iff; unfold bv_ltu; u_norm; apply Z.ltb_ge; lia.
    Ltac geu_ft := unfold c_ltu; rewrite ?Bool.negb_false_iff; unfold bv_ltu; u_norm; apply Z.ltb_lt; lia.
    assert (MAIN : exists r2, msteps RSEGS (mkst r1 (0x67870 : word) M rom) (mkst r2 (0x678e4 : word) M rom)
      /\ getr r2 25 = Z_to_bv 64 (mred sc size cnt uu nosm) /\ getr r2 10 = Z_to_bv 64 uu
      /\ keeps_but [5; 10; 15; 16; 17; 19; 25]%bv r1 r2).
    { unfold mred.
      destruct (4 * cnt <=? uu)%Z eqn:B4.
      { apply Z.leb_le in B4. cbn [orb]. eexists. split.
        - stepn F_6781c D_6781c. rewrite A19, (v_slliw_lit cnt 2) by lia. change (2 ^ 2)%Z with 4%Z.
          stepb_tk F_67820 D_67820 ltac:(rewrite A10; geu_tk).
          stepn F_6788c D_6788c. rewrite A19.
          pu_refl.
        - post. }
      apply Z.leb_gt in B4. cbn [orb].
      destruct (Z.eq_dec nosm 0) as [N0|N1].
      2:{ replace (nosm =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. eexists. split.
          - stepn F_6781c D_6781c. rewrite A19, (v_slliw_lit cnt 2) by lia. change (2 ^ 2)%Z with 4%Z.
            stepb_ft F_67820 D_67820 ltac:(rewrite A10; geu_ft).
            stepb_tk F_67824 D_67824 ltac:(rewrite A13, c_eq_Z by lia; apply Z.eqb_neq; lia).
            stepn F_6788c D_6788c. rewrite A19.
            pu_refl.
          - post. }
      replace (nosm =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
      (* [comment removed for export] *)
      Ltac m2_pre A19 A10 A13 A8 A11 N0 :=
        stepn F_6781c D_6781c; rewrite A19, (v_slliw_lit cnt 2) by lia; change (2 ^ 2)%Z with 4%Z;
        stepb_ft F_67820 D_67820 ltac:(rewrite A10; geu_ft);
        stepb_ft F_67824 D_67824 ltac:(rewrite A13, N0; apply c_eq_refl);
        stepn F_67828 D_67828; rewrite A8, (v_andi_Z sc 3), land3_mod4 by lia;
        stepn F_6782c D_6782c;
        stepn F_67830 D_67830; rewrite A11; vals_lit.
      destruct (Z.eq_dec (sc mod 4) 1) as [E1|N1'].
      { rewrite E1. cbn [Z.eqb Pos.eqb].
        destruct (32768 <? size * cnt)%Z eqn:BS.
        - apply Z.ltb_lt in BS. eexists. split.
          + m2_pre A19 A10 A13 A8 A11 N0. rewrite E1.
            stepb_ft F_67834 D_67834 ltac:(cond_compute).
            stepb_ft F_67838 D_67838 ltac:(rewrite A14; geu_ft).
            stepn F_6783c D_6783c.
            stepn F_67840 D_67840.
            pu_refl.
          + post.
        - apply Z.ltb_ge in BS. eexists. split.
          + m2_pre A19 A10 A13 A8 A11 N0. rewrite E1.
            stepb_ft F_67834 D_67834 ltac:(cond_compute).
            stepb_tk F_67838 D_67838 ltac:(rewrite A14; geu_tk).
            stepn F_67844 D_67844.
            stepb_tk F_67848 D_67848 ltac:(cond_compute).
            stepn F_6785c D_6785c. unfold v_sltu. rewrite A14, c_ltu_Z by lia. replace (32768 <? size * cnt)%Z with false by (symmetry; apply Z.ltb_ge; lia).
            stepn F_67860 D_67860.
            stepn F_67864 D_67864.
            stepb_ft F_67868 D_67868 ltac:(cond_compute).
            stepn F_6786c D_6786c. rewrite A19.
            stepn F_67870 D_67870.
            stepb_tk F_67878 D_67878 ltac:(cond_compute).
            pu_refl.
          + post. }
      destruct (Z.eq_dec (sc mod 4) 2) as [E2|N2'].
      { rewrite E2. cbn [Z.eqb Pos.eqb].
        destruct (16384 <? size * cnt)%Z eqn:BS.
        - apply Z.ltb_lt in BS. eexists. split.
          + m2_pre A19 A10 A13 A8 A11 N0. rewrite E2.
            stepb_tk F_67834 D_67834 ltac:(cond_compute).
            stepn F_67844 D_67844.
            stepb_ft F_67848 D_67848 ltac:(cond_compute).
            stepn F_6784c D_6784c. rewrite A11. vals_lit.
            stepb_ft F_67850 D_67850 ltac:(rewrite A14; geu_ft).
            stepn F_67854 D_67854.
            stepn F_67858 D_67858.
            pu_refl.
          + post.
        - apply Z.ltb_ge in BS. eexists. split.
          + m2_pre A19 A10 A13 A8 A11 N0. rewrite E2.
            stepb_tk F_67834 D_67834 ltac:(cond_compute).
            stepn F_67844 D_67844.
            stepb_ft F_67848 D_67848 ltac:(cond_compute).
            stepn F_6784c D_6784c. rewrite A11. vals_lit.
            stepb_tk F_67850 D_67850 ltac:(rewrite A14; geu_tk).
            stepn F_6785c D_6785c. unfold v_sltu. rewrite A14, c_ltu_Z by lia. replace (32768 <? size * cnt)%Z with false by (symmetry; apply Z.ltb_ge; lia).
            stepn F_67860 D_67860.
            stepn F_67864 D_67864.
            stepb_ft F_67868 D_67868 ltac:(cond_compute).
            stepn F_6786c D_6786c. rewrite A19.
            stepn F_67870 D_67870.
            stepb_tk F_67878 D_67878 ltac:(cond_compute).
            pu_refl.
          + post. }
      destruct (Z.eq_dec (sc mod 4) 0) as [E0|N0'].
      { rewrite E0. cbn [Z.eqb Pos.eqb].
        destruct (32768 <? size * cnt)%Z eqn:BS.
        - apply Z.ltb_lt in BS. eexists. split.
          + m2_pre A19 A10 A13 A8 A11 N0. rewrite E0.
            stepb_tk F_67834 D_67834 ltac:(cond_compute).
            stepn F_67844 D_67844.
            stepb_tk F_67848 D_67848 ltac:(cond_compute).
            stepn F_6785c D_6785c. unfold v_sltu. rewrite A14, c_ltu_Z by lia. replace (32768 <? size * cnt)%Z with true by (symmetry; apply Z.ltb_lt; lia).
            stepn F_67860 D_67860.
            stepn F_67864 D_67864.
            stepb_tk F_67868 D_67868 ltac:(cond_compute).
            stepn F_67874 D_67874.
            stepb_ft F_67878 D_67878 ltac:(cond_compute).
            stepb_tk F_6787c D_6787c ltac:(rewrite A14, c_ltu_Z by lia; apply Z.ltb_lt; lia).
            pu_refl.
          + post.
        - apply Z.ltb_ge in BS.
          destruct (8192 <? size * cnt)%Z eqn:BS2.
          + apply Z.ltb_lt in BS2. eexists. split.
            * m2_pre A19 A10 A13 A8 A11 N0. rewrite E0.
              stepb_tk F_67834 D_67834 ltac:(cond_compute).
              stepn F_67844 D_67844.
              stepb_tk F_67848 D_67848 ltac:(cond_compute).
              stepn F_6785c D_6785c. unfold v_sltu. rewrite A14, c_ltu_Z by lia. replace (32768 <? size * cnt)%Z with false by (symmetry; apply Z.ltb_ge; lia).
              stepn F_67860 D_67860.
              stepn F_67864 D_67864.
              stepb_ft F_67868 D_67868 ltac:(cond_compute).
              stepn F_6786c D_6786c. rewrite A19.
              stepn F_67870 D_67870.
              stepb_ft F_67878 D_67878 ltac:(cond_compute).
              stepb_ft F_6787c D_6787c ltac:(rewrite A14, c_ltu_Z by lia; apply Z.ltb_ge; lia).
              stepn F_67880 D_67880. rewrite A11. vals_lit.
              stepb_ft F_67884 D_67884 ltac:(rewrite A14; geu_ft).
              stepn F_67888 D_67888.
              stepn F_6788c D_6788c.
              pu_refl.
            * post.
          + apply Z.ltb_ge in BS2. eexists. split.
            * m2_pre A19 A10 A13 A8 A11 N0. rewrite E0.
              stepb_tk F_67834 D_67834 ltac:(cond_compute).
              stepn F_67844 D_67844.
              stepb_tk F_67848 D_67848 ltac:(cond_compute).
              stepn F_6785c D_6785c. unfold v_sltu. rewrite A14, c_ltu_Z by lia. replace (32768 <? size * cnt)%Z with false by (symmetry; apply Z.ltb_ge; lia).
              stepn F_67860 D_67860.
              stepn F_67864 D_67864.
              stepb_ft F_67868 D_67868 ltac:(cond_compute).
              stepn F_6786c D_6786c. rewrite A19.
              stepn F_67870 D_67870.
              stepb_ft F_67878 D_67878 ltac:(cond_compute).
              stepb_ft F_6787c D_6787c ltac:(rewrite A14, c_ltu_Z by lia; apply Z.ltb_ge; lia).
              stepn F_67880 D_67880. rewrite A11. vals_lit.
              stepb_tk F_67884 D_67884 ltac:(rewrite A14; geu_tk).
              stepn F_6788c D_6788c. rewrite A19.
              pu_refl.
            * post. }
      assert (E3 : (sc mod 4 = 3)%Z) by lia. rewrite E3. cbn [Z.eqb Pos.eqb].
      eexists. split.
      - m2_pre A19 A10 A13 A8 A11 N0. rewrite E3.
        stepb_tk F_67834 D_67834 ltac:(cond_compute).
        stepn F_67844 D_67844.
        stepb_tk F_67848 D_67848 ltac:(cond_compute).
        stepn F_6785c D_6785c.
        stepn F_67860 D_67860.
        stepn F_67864 D_67864.
        match goal with |- context [regupd _ 17 ?v] =>
          replace v with (Z_to_bv 64 0) by (unfold v_sltu, v_sltiu; rewrite ?A14; destruct (c_ltu _ _); apply bv_eq; vm_compute; reflexivity) end.
        stepb_ft F_67868 D_67868 ltac:(cond_compute).
        stepn F_6786c D_6786c. rewrite A19.
        stepn F_67870 D_67870.
        stepb_tk F_67878 D_67878 ltac:(cond_compute).
        pu_refl.
      - post. }
    destruct MAIN as (r2 & S2 & B25 & B10 & K2).
    exists r2. split; [eapply msteps_trans; [exact S1 | exact S2]|].
    split; [exact B25|]. split; [exact B10|]. eapply keeps_but_trans; [exact K1 | exact K2].
  Qed.
End M2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rup (x : Z) : Z := x + Z.land (2 ^ 64 - x) 4095.
Definition m3 (size cnt2 req u' nosm : Z) : Z * Z :=
  let needed := rup (size * cnt2 + 16) in
  let req' := rup (req + 20) in
  if (negb (nosm =? 0) || (7 <? cnt2))%Z%bool then (cnt2, needed)
  else if (req' <? size + 16)%Z then (1%Z, req')
  else if (req' <? 16384)%Z then (cnt2, needed)
  else if (u' <? 2 * cnt2)%Z then (1%Z, req') else (cnt2, needed).

Lemma rup_spec : forall x, (0 < x <= 2 ^ 62)%Z -> (rup x mod 4096 = 0 /\ x <= rup x < x + 4096)%Z.
Proof.
  intros x Hx. unfold rup. change 4095%Z with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12)%Z with 4096%Z.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  pose proof (Z.mod_pos_bound (2 ^ 64 - x) 4096 ltac:(lia)). split; [|lia].
  change (2 ^ 64)%Z with (4096 * 4503599627370496)%Z in *. nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma m3_facts : forall size cnt2 req u' nosm,
  (16 <= size <= 16 * 8191)%Z -> (1 <= cnt2 <= 32)%Z -> (0 <= req < 2 ^ 40)%Z ->
  let '(cnt3, needed3) := m3 size cnt2 req u' nosm in
  (needed3 mod 4096 = 0)%Z /\ (1 <= cnt3 <= cnt2)%Z /\ (0 < needed3 <= 2 ^ 41)%Z /\
  ((size * cnt3 + 16 <= needed3)%Z \/ (cnt3 = 1 /\ needed3 = rup (req + 20) /\ (needed3 < size + 16 \/ 16384 <= needed3)))%Z.
Proof.
  intros size cnt2 req u' nosm Hs Hc Hr. unfold m3.
  pose proof (rup_spec (size * cnt2 + 16) ltac:(nia)) as [R1 R2].
  pose proof (rup_spec (req + 20) ltac:(lia)) as [Q1 Q2].
  destruct (negb (nosm =? 0) || (7 <? cnt2))%Z%bool; [cbn; nia|].
  destruct (rup (req + 20) <? size + 16)%Z eqn:B1; [apply Z.ltb_lt in B1; cbn; nia|]. apply Z.ltb_ge in B1.
  destruct (rup (req + 20) <? 16384)%Z eqn:B2; [apply Z.ltb_lt in B2; cbn; nia|]. apply Z.ltb_ge in B2.
  destruct (u' <? 2 * cnt2)%Z; cbn; nia.
Qed.

Section M3.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (M : mem) (scl cnt2 req u' nosm : Z).
  #[local] Notation size := (16 * scl)%Z.
  Hypothesis Hscl : (1 <= scl <= 8191)%Z.
  Hypothesis Hcnt2 : (1 <= cnt2 <= 32)%Z.
  Hypothesis Hreq : (0 <= req < 2^40)%Z.
  Hypothesis Hu' : (0 <= u' < 2^64)%Z.
  Hypothesis Hnosm : (0 <= nosm <= 1)%Z.

  Lemma land4095_rng : forall x, (0 <= Z.land x 4095 < 4096)%Z.
  Proof using. intros x. change 4095%Z with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

  Lemma aM3 : forall regs rom,
    getr regs 24 = Z_to_bv 64 size -> getr regs 25 = Z_to_bv 64 cnt2 -> getr regs 11 = Z_to_bv 64 4096 ->
    getr regs 13 = Z_to_bv 64 nosm -> getr regs 18 = Z_to_bv 64 req -> getr regs 12 = Z_to_bv 64 (size + 16) ->
    getr regs 10 = Z_to_bv 64 u' ->
    exists regs',
      msteps RSEGS (mkst regs (0x678e4 : word) M rom) (mkst regs' (0x67940 : word) M rom)
      /\ getr regs' 25 = Z_to_bv 64 (fst (m3 size cnt2 req u' nosm)) /\ getr regs' 19 = Z_to_bv 64 (snd (m3 size cnt2 req u' nosm))
      /\ keeps_but [11; 13; 14; 15; 16; 19; 25]%bv regs regs'.
  Proof using Hnosm Hu' Hreq Hcnt2 Hscl.
    intros regs rom H24 H25 H11 H13 H18 H12 H10. unfold m3.
    set (needed := rup (size * cnt2 + 16)). set (req' := rup (req + 20)).
    assert (SC : (16 <= size * cnt2 <= 16 * 8191 * 32)%Z) by nia.
    pose proof (land4095_rng (2 ^ 64 - 16 - size * cnt2)) as L1. pose proof (land4095_rng (2 ^ 64 - 20 - req)) as L2.
    assert (En : needed = (size * cnt2 + Z.land (2 ^ 64 - 16 - size * cnt2) 4095 + 16)%Z).
    { unfold needed, rup. replace (2 ^ 64 - (size * cnt2 + 16))%Z with (2 ^ 64 - 16 - size * cnt2)%Z by lia. lia. }
    assert (Er : req' = (req + Z.land (2 ^ 64 - 20 - req) 4095 + 20)%Z).
    { unfold req', rup. replace (2 ^ 64 - (req + 20))%Z with (2 ^ 64 - 20 - req)%Z by lia. lia. }
    (* [comment removed for export] *)
    Ltac m3_pre H24 H25 H11 En nd :=
      stepn F_67890 D_67890; rewrite H24, H25, (v_mul_Z (16 * _) cnt2) by lia;
      stepn F_67894 D_67894;
      stepn F_67898 D_67898; rewrite (v_sub_ZZ 18446744073709551600 (16 * _ * cnt2)) by lia;
      stepn F_6789c D_6789c; rewrite H11; vals_lit;
      stepn F_678a0 D_678a0; rewrite (v_and_Z (18446744073709551600 - 16 * _ * cnt2) 4095) by lia;
      change 18446744073709551600%Z with (2 ^ 64 - 16)%Z;
      stepn F_678a4 D_678a4; rewrite v_add_ZZ by lia;
      stepn F_678a8 D_678a8;
      match goal with |- context [regupd _ 19 (v_addi ?w 16)] =>
        replace (v_addi w 16) with (Z_to_bv 64 nd) by (rewrite En; unfold v_addi; unorm; f_equal; lia) end.
    (* [comment removed for export] *)
    Ltac m3_req H18 Er rq :=
      stepn F_678b8 D_678b8;
      stepn F_678bc D_678bc; rewrite H18, (v_sub_ZZ 18446744073709551596 req) by lia;
      stepn F_678c0 D_678c0; rewrite (v_and_Z 4095 (18446744073709551596 - req)) by lia; rewrite (Z.land_comm 4095);
      change 18446744073709551596%Z with (2 ^ 64 - 20)%Z;
      stepn F_678c4 D_678c4; rewrite H18, v_add_ZZ by lia;
      stepn F_678c8 D_678c8;
      match goal with |- context [regupd _ 13 (v_addi ?w 20)] =>
        replace (v_addi w 20) with (Z_to_bv 64 rq) by (rewrite Er; unfold v_addi; unorm; f_equal; lia) end.
    destruct (negb (nosm =? 0) || (7 <? cnt2))%Z%bool eqn:B0.
    { (* [comment removed for export] *)
      destruct (Z.eq_dec nosm 0) as [N0|N1].
      - rewrite N0 in B0. cbn in B0. apply Z.ltb_lt in B0.
        eexists. split.
        + m3_pre H24 H25 H11 En needed.
          stepb_ft F_678ac D_678ac ltac:(rewrite H13, N0; apply c_eq_refl).
          stepn F_678b0 D_678b0.
          stepb_tk F_678b4 D_678b4 ltac:(rewrite H25, c_ltu_Z by lia; apply Z.ltb_lt; lia).
          pu_refl.
        + post.
      - eexists. split.
        + m3_pre H24 H25 H11 En needed.
          stepb_tk F_678ac D_678ac ltac:(rewrite H13, c_eq_Z by lia; apply Z.eqb_neq; lia).
          pu_refl.
        + post. }
    apply Bool.orb_false_iff in B0 as [Bn B7]. apply Bool.negb_false_iff in Bn. apply Z.eqb_eq in Bn. apply Z.ltb_ge in B7.
    pose proof (rup_spec (req + 20) ltac:(lia)) as [Q1 Q2]. fold req' in Q1, Q2.
    destruct (req' <? size + 16)%Z eqn:B1.
    { apply Z.ltb_lt in B1. eexists. split.
      - m3_pre H24 H25 H11 En needed.
        stepb_ft F_678ac D_678ac ltac:(rewrite H13, Bn; apply c_eq_refl).
        stepn F_678b0 D_678b0.
        stepb_ft F_678b4 D_678b4 ltac:(rewrite H25, c_ltu_Z by lia; apply Z.ltb_ge; lia).
        m3_req H18 Er req'.
        stepb_ft F_678cc D_678cc ltac:(rewrite H12; unfold c_ltu; rewrite ?Bool.negb_false_iff; unfold bv_ltu; u_norm; apply Z.ltb_lt; lia).
        stepn F_678d0 D_678d0.
        stepn F_678d4 D_678d4.
        stepn F_678d8 D_678d8.
        pu_refl.
      - post. }
    apply Z.ltb_ge in B1.
    destruct (req' <? 16384)%Z eqn:B2.
    { apply Z.ltb_lt in B2. eexists. split.
      - m3_pre H24 H25 H11 En needed.
        stepb_ft F_678ac D_678ac ltac:(rewrite H13, Bn; apply c_eq_refl).
        stepn F_678b0 D_678b0.
        stepb_ft F_678b4 D_678b4 ltac:(rewrite H25, c_ltu_Z by lia; apply Z.ltb_ge; lia).
        m3_req H18 Er req'.
        stepb_tk F_678cc D_678cc ltac:(rewrite H12; unfold c_ltu; rewrite ?Bool.negb_true_iff; unfold bv_ltu; u_norm; apply Z.ltb_ge; lia).
        stepn F_678dc D_678dc. rewrite H11. vals_lit.
        stepb_tk F_678e0 D_678e0 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
        pu_refl.
      - post. }
    apply Z.ltb_ge in B2.
    destruct (u' <? 2 * cnt2)%Z eqn:B3.
    { apply Z.ltb_lt in B3. eexists. split.
      - m3_pre H24 H25 H11 En needed.
        stepb_ft F_678ac D_678ac ltac:(rewrite H13, Bn; apply c_eq_refl).
        stepn F_678b0 D_678b0.
        stepb_ft F_678b4 D_678b4 ltac:(rewrite H25, c_ltu_Z by lia; apply Z.ltb_ge; lia).
        m3_req H18 Er req'.
        stepb_tk F_678cc D_678cc ltac:(rewrite H12; unfold c_ltu; rewrite ?Bool.negb_true_iff; unfold bv_ltu; u_norm; apply Z.ltb_ge; lia).
        stepn F_678dc D_678dc. rewrite H11. vals_lit.
        stepb_ft F_678e0 D_678e0 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
        stepn F_678e4 D_678e4. rewrite H25, (v_slliw_lit cnt2 1) by lia. change (2 ^ 1)%Z with 2%Z.
        stepb_tk F_678e8 D_678e8 ltac:(rewrite H10, c_ltu_Z by lia; apply Z.ltb_lt; lia).
        stepn F_678d0 D_678d0.
        stepn F_678d4 D_678d4.
        stepn F_678d8 D_678d8.
        pu_refl.
      - post; try (f_equal; lia). }
    apply Z.ltb_ge in B3. eexists. split.
    - m3_pre H24 H25 H11 En needed.
      stepb_ft F_678ac D_678ac ltac:(rewrite H13, Bn; apply c_eq_refl).
      stepn F_678b0 D_678b0.
      stepb_ft F_678b4 D_678b4 ltac:(rewrite H25, c_ltu_Z by lia; apply Z.ltb_ge; lia).
      m3_req H18 Er req'.
      stepb_tk F_678cc D_678cc ltac:(rewrite H12; unfold c_ltu; rewrite ?Bool.negb_true_iff; unfold bv_ltu; u_norm; apply Z.ltb_ge; lia).
      stepn F_678dc D_678dc. rewrite H11. vals_lit.
      stepb_ft F_678e0 D_678e0 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
      stepn F_678e4 D_678e4. rewrite H25, (v_slliw_lit cnt2 1) by lia. change (2 ^ 1)%Z with 2%Z.
      stepb_ft F_678e8 D_678e8 ltac:(rewrite H10, c_ltu_Z by lia; apply Z.ltb_ge; lia).
      pu_refl.
    - post.
  Qed.
End M3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section M4.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (M : mem) (needed : Z).
  Hypothesis Hn : (0 <= needed < 2^64)%Z.
  Lemma aM4 : forall regs rom,
    getr regs 19 = Z_to_bv 64 needed ->
    exists regs',
      msteps RSEGS (mkst regs (0x67940 : word) M rom) (mkst regs' (0x682e8 : word) M rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 needed /\ getr regs' 12 = Z_to_bv 64 3
      /\ getr regs' 13 = Z_to_bv 64 34 /\ getr regs' 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr regs' 15 = Z_to_bv 64 0
      /\ getr regs' 18 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr regs' 1 = Z_to_bv 64 0x67960
      /\ keeps_but [1; 10; 11; 12; 13; 14; 15; 18]%bv regs regs'.
  Proof using.
    intros regs rom H19.
    eexists. split.
    - stepn F_678ec D_678ec.
      stepn F_678f0 D_678f0.
      stepn F_678f4 D_678f4.
      stepn F_678f8 D_678f8.
      stepn F_678fc D_678fc.
      stepn F_67900 D_67900. rewrite H19.
      stepn F_67904 D_67904.
      stepn F_67908 D_67908.
      pu_refl.
    - post.
  Qed.
End M4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aidx_of (size cnt : Z) : Z :=
  let q := 4080 / size in if (cnt <? q)%Z then cnt - 1 else if (q =? 0)%Z then 0 else q - 1.

Lemma aidx_of_rng : forall size cnt, (16 <= size)%Z -> (1 <= cnt)%Z -> (0 <= aidx_of size cnt <= cnt - 1)%Z.
Proof.
  intros size cnt Hs Hc. unfold aidx_of. pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)).
  destruct (cnt <? 4080 / size)%Z eqn:B1; [apply Z.ltb_lt in B1; lia|]. apply Z.ltb_ge in B1.
  destruct (4080 / size =? 0)%Z eqn:B2; [lia|]. apply Z.eqb_neq in B2. lia.
Qed.

Section M5.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (M : mem) (mt p0 W0 ctr needed cnt scl : Z).
  #[local] Notation size := (16 * scl)%Z.
  Hypothesis Hscl : (1 <= scl <= 8191)%Z.
  Hypothesis Hcnt : (1 <= cnt <= 32)%Z.
  Hypothesis Hmt : (HEAPLO <= mt)%Z /\ (mt + 40 <= CEIL)%Z /\ ((mt + 40 <= IMG_LO)%Z \/ (IMG_HI <= mt)%Z).
  Hypothesis Hp0 : (0 <= p0 < 2^64 - 1)%Z.
  Hypothesis HW0 : (0 <= W0 < 2^64)%Z.
  Hypothesis Hctr : (0 <= ctr < 2^32)%Z.
  Hypothesis Hn : (0 < needed <= 2^41)%Z /\ (needed mod 4096 = 0)%Z.
  Hypothesis M_W : rdn RSEGS M (Z_to_bv 64 (mt + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W0)).
  Hypothesis M_ctr : rdn RSEGS M (Z_to_bv 64 ctx_mmap_counter) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ctr)).
  Hypothesis SOK_mt : store_ok RSEGS M (Z_to_bv 64 mt) 40%nat = true.
  Hypothesis SOKc : store_ok RSEGS M (Z_to_bv 64 CTX) 928%nat = true.

  Definition m_m5 : mem :=
    wbytes (wbytes M (Z_to_bv 64 (mt + 32)) (word_to_le_bytes 8 (Z_to_bv 64 (W0 mod 4096 + needed))))
           (Z_to_bv 64 ctx_mmap_counter) (word_to_le_bytes 4 (Z_to_bv 64 ((ctr + 1) mod 2 ^ 32))).

  Lemma aM5 : forall regs rom,
    getr regs 10 = Z_to_bv 64 p0 -> getr regs 18 = Z_to_bv 64 (2 ^ 64 - 1) -> getr regs 19 = Z_to_bv 64 needed ->
    getr regs 9 = Z_to_bv 64 mt -> getr regs 24 = Z_to_bv 64 size -> getr regs 22 = Z_to_bv 64 MLOCK -> getr regs 25 = Z_to_bv 64 cnt ->
    exists regs',
      msteps RSEGS (mkst regs (0x67960 : word) M rom) (mkst regs' (0x679b8 : word) m_m5 rom)
      /\ getr regs' 10 = Z_to_bv 64 p0 /\ getr regs' 11 = Z_to_bv 64 (cnt - 1) /\ getr regs' 12 = Z_to_bv 64 (aidx_of size cnt)
      /\ getr regs' 25 = Z_to_bv 64 cnt
      /\ keeps_but [11; 12; 13; 14]%bv regs regs'.
  Proof using SOKc SOK_mt M_ctr M_W Hn Hctr HW0 Hp0 Hmt Hcnt Hscl RN.
    intros regs rom H10 H18 H19 H9 H24 H22 H25. unfold m_m5, aidx_of. ceil; unfold ctx_mmap_counter, CTX, MLOCK, HEAPLO in *.
    destruct Hn as [Hn1 Hn2]. pose proof (Z.mod_pos_bound W0 4096 ltac:(lia)) as MW.
    set (q := (4080 / size)%Z).
    assert (Hq : (0 <= q <= 255)%Z) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (LN : Z.land needed 18446744073709547520 = needed).
    { change 18446744073709547520%Z with (2 ^ 64 - 4096)%Z. rewrite land_hi12 by lia. lia. }
    assert (DM : (needed = (needed / 4096) * 2 ^ 12)%Z).
    { change (2 ^ 12)%Z with 4096%Z. pose proof (Z.div_mod needed 4096 ltac:(lia)). lia. }
    assert (LO : Z.lor (W0 mod 4096) needed = (W0 mod 4096 + needed)%Z).
    { rewrite DM. apply lor_low_high; [change (2 ^ 12)%Z with 4096%Z; lia | apply Z.div_pos; lia | lia]. }
    (* [comment removed for export] *)
    assert (PRE : exists r1, msteps RSEGS (mkst regs (0x67960 : word) M rom)
        (mkst r1 (0x6799c : word) (wbytes (wbytes M (Z_to_bv 64 (mt + 32)) (word_to_le_bytes 8 (Z_to_bv 64 (W0 mod 4096 + needed))))
           (Z_to_bv 64 (700056 + 12)) (word_to_le_bytes 4 (Z_to_bv 64 ((ctr + 1) mod 2 ^ 32)))) rom)
      /\ getr r1 10 = Z_to_bv 64 p0 /\ getr r1 11 = Z_to_bv 64 q /\ getr r1 12 = Z_to_bv 64 cnt /\ getr r1 25 = Z_to_bv 64 cnt
      /\ keeps_but [11; 12; 13; 14]%bv regs r1).
    { eexists. split.
      - stepb_ft F_6790c D_6790c ltac:(rewrite H10, H18, c_eq_Z by lia; apply Z.eqb_neq; lia).
        stepn F_67910 D_67910.
        stepLD F_67914 D_67914 (word_to_le_bytes 8 (Z_to_bv 64 W0)) (Z_to_bv 64 W0) ltac:(addr_norm; exact M_W) ltac:(apply bytes_le_to_Z_8).
        stepn F_67918 D_67918. rewrite H19, (v_and_Z needed 18446744073709547520), LN by lia.
        stepn F_6791c D_6791c.
        stepn F_67920 D_67920. vals_lit.
        stepn F_67924 D_67924.
        all: try (gres; rewrite H24; u_norm; lia).
        rewrite H24.
        match goal with |- context [regupd _ 11 ?v] =>
          replace v with (Z_to_bv 64 q) by (subst q; unfold v_divu; u_norm; reflexivity) end.
        stepLD F_67928 D_67928 (word_to_le_bytes 4 (Z_to_bv 64 ctr)) (Z_to_bv 64 ctr)
          ltac:(addr_norm; exact M_ctr) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
        rewrite v_lw_s32 by lia.
        stepn F_6792c D_6792c.
        stepn F_67930 D_67930. rewrite (low12 W0) by lia.
        stepn F_67934 D_67934. rewrite (v_or_Z (W0 mod 4096) needed), LO by lia.
        stepn F_67938 D_67938.
        stepSTx F_6793c D_6793c (Z_to_bv 64 (mt + 32)) (Z_to_bv 64 (W0 mod 4096 + needed)) ltac:(sok 40%nat SOK_mt).
        stepSTx F_67940 D_67940 (Z_to_bv 64 (700056 + 12)) (v_addi (s32 ctr) 1) ltac:(sok 928%nat SOKc).
        rewrite (w2le4_low (v_addi (s32 ctr) 1) ((ctr + 1) mod 2 ^ 32)).
        2:{ apply Z.mod_pos_bound. lia. }
        2:{ unfold v_addi. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. rewrite u_s32.
            rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists (2^32)%Z; reflexivity].
            rewrite <- Zplus_mod_idemp_l, sx32_mod, Zplus_mod_idemp_l. reflexivity. }
        stepn F_67944 D_67944. rewrite H25.
        pu_refl.
      - post. }
    destruct PRE as (r1 & S1 & A10 & A11 & A12 & A25 & K1).
    destruct (cnt <? q)%Z eqn:B1.
    - apply Z.ltb_lt in B1. eexists. split.
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_67948 D_67948 ltac:(rewrite A25, A11, c_ltu_Z by lia; apply Z.ltb_lt; lia).
        stepn F_67950 D_67950. rewrite A12. addi_renorm.
        stepn F_67954 D_67954. unfold v_sltu. rewrite A12, c_ltu_Z by lia. replace (cnt <? cnt - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia).
        stepn F_67958 D_67958.
        stepn F_6795c D_6795c. rewrite (v_and_Z 18446744073709551615 (cnt - 1)) by lia.
        rewrite Z.land_comm. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones, (Z.mod_small (cnt - 1)) by lia.
        stepn F_67960 D_67960. rewrite A25. addi_renorm.
        pu_refl.
      + post; try (eapply keeps_but_trans; [exact K1 | solve_keeps_but]).
    - apply Z.ltb_ge in B1.
      destruct (q =? 0)%Z eqn:B2.
      + apply Z.eqb_eq in B2. eexists. split.
        * eapply msteps_trans; [exact S1|].
          stepb_ft F_67948 D_67948 ltac:(rewrite A25, A11, c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepn F_6794c D_6794c. rewrite A11, B2.
          stepn F_67950 D_67950.
          stepn F_67954 D_67954.
          stepn F_67958 D_67958.
          stepn F_6795c D_6795c.
          stepn F_67960 D_67960. rewrite A25. addi_renorm.
          pu_refl.
        * post; try (eapply keeps_but_trans; [exact K1 | solve_keeps_but]).
      + apply Z.eqb_neq in B2. eexists. split.
        * eapply msteps_trans; [exact S1|].
          stepb_ft F_67948 D_67948 ltac:(rewrite A25, A11, c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepn F_6794c D_6794c. rewrite A11.
          stepn F_67950 D_67950. addi_renorm.
          stepn F_67954 D_67954. unfold v_sltu. rewrite c_ltu_Z by lia. replace (q <? q - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia).
          stepn F_67958 D_67958.
          stepn F_6795c D_6795c. rewrite (v_and_Z 18446744073709551615 (q - 1)) by lia.
          rewrite Z.land_comm. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones, (Z.mod_small (q - 1)) by lia.
          stepn F_67960 D_67960. rewrite A25. addi_renorm.
          pu_refl.
        * post; try (eapply keeps_but_trans; [exact K1 | solve_keeps_but]).
  Qed.
End M5.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Open Scope Z_scope.
(* [comment removed for export] *)
Ltac size_class_eval :=
  repeat match goal with
  | |- context [size_class ?x] => let v := eval vm_compute in (size_class x) in change (size_class x) with v
  | H : context [size_class ?x] |- _ => let v := eval vm_compute in (size_class x) in change (size_class x) with v in H
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hx_malloc : forall n sc0 sc,
  0 <= n < MMAP_THRESHOLD -> sc0 = size_to_class n ->
  (sc = sc0 \/ (sc = sc0 + 1 /\ sc0 mod 2 = 0 /\ 4 <= sc0 < 32 /\ sc0 <> 6)) ->
  2048 < 16 * size_class sc + 16 -> size_class sc <= 255 ->
  4080 - 4 - n < 16 * size_class sc.
Proof.
  intros n sc0 sc Hn Hsc0 Hsc Hbig Hsmall.
  pose proof (size_to_class_rng n Hn) as R. rewrite <- Hsc0 in R.
  assert (M : sc0 = 0 \/ 16 * size_class (sc0 - 1) < n + 4).
  { destruct (Z.eq_dec sc0 0) as [E|NE]; [left; exact E | right].
    destruct (Z_lt_le_dec (16 * size_class (sc0 - 1)) (n + 4)) as [L|G]; [exact L | exfalso].
    pose proof (size_to_class_min n (sc0 - 1) Hn ltac:(lia) G). lia. }
  assert (E : exists k, (k < 48)%nat /\ sc0 = Z.of_nat k) by (exists (Z.to_nat sc0); split; lia).
  destruct E as (k & Hk & Ek). clear Hsc0. subst sc0. unfold MMAP_THRESHOLD in Hn.
  destruct Hsc as [-> | (-> & HE & HR & H6)];
    enum_nat k 48%nat ltac:(size_class_eval; first [lia | exfalso; revert HE;
      match goal with |- (?a mod 2 = 0 -> False) => let v := eval vm_compute in (a mod 2) in change (a mod 2) with v; lia end]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mred_cases : forall sc size cnt u' nosm,
  let c2 := mred sc size cnt u' nosm in
  c2 = cnt \/ (c2 = 2 /\ 32768 < size * cnt) \/ (c2 = 3 /\ 16384 < size * cnt) \/ (c2 = 5 /\ 8192 < size * cnt <= 32768).
Proof.
  intros sc size cnt u' nosm. unfold mred.
  destruct ((4 * cnt <=? u') || negb (nosm =? 0))%bool; [cbn; lia|].
  destruct (sc mod 4 =? 1); [destruct (32768 <? size * cnt) eqn:B; [apply Z.ltb_lt in B|apply Z.ltb_ge in B]; cbn; lia|].
  destruct (sc mod 4 =? 2); [destruct (16384 <? size * cnt) eqn:B; [apply Z.ltb_lt in B|apply Z.ltb_ge in B]; cbn; lia|].
  destruct (sc mod 4 =? 0); [|cbn; lia].
  destruct (32768 <? size * cnt) eqn:B; [apply Z.ltb_lt in B|apply Z.ltb_ge in B]; [cbn; lia|].
  destruct (8192 <? size * cnt) eqn:B2; [apply Z.ltb_lt in B2|apply Z.ltb_ge in B2]; cbn; lia.
Qed.

Lemma mred_mod3 : forall sc size cnt u' nosm, sc mod 4 = 3 -> mred sc size cnt u' nosm = cnt.
Proof.
  intros sc size cnt u' nosm H3. unfold mred. rewrite H3. cbn [Z.eqb Pos.eqb].
  destruct ((4 * cnt <=? u') || negb (nosm =? 0))%bool; reflexivity.
Qed.

Lemma m3_cases : forall size cnt2 req u' nosm,
  let '(cnt3, needed3) := m3 size cnt2 req u' nosm in
  (cnt3 = cnt2 /\ needed3 = rup (size * cnt2 + 16)) \/ (cnt3 = 1 /\ needed3 = rup (req + 20)).
Proof.
  intros size cnt2 req u' nosm. unfold m3.
  destruct (negb (nosm =? 0) || (7 <? cnt2))%bool; [cbn; lia|].
  destruct (rup (req + 20) <? size + 16); [cbn; lia|].
  destruct (rup (req + 20) <? 16384); [cbn; lia|].
  destruct (u' <? 2 * cnt2); cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma size_class_page : forall sc, 0 <= sc < 48 ->
  1 <= size_class sc <= 8191 /\
  (4096 mod (16 * size_class sc) = 0 -> (sc = 0 /\ size_class sc = 1) \/ (sc = 1 /\ size_class sc = 2) \/ (sc = 3 /\ size_class sc = 4) \/ (sc = 7 /\ size_class sc = 8)).
Proof.
  intros sc Hsc.
  assert (E : exists k, (k < 48)%nat /\ sc = Z.of_nat k) by (exists (Z.to_nat sc); split; lia).
  destruct E as (k & Hk & ->).
  enum_nat k 48%nat ltac:(size_class_eval; split; [lia|];
    match goal with |- (?a mod ?b = 0 -> _) => let v := eval vm_compute in (a mod b) in change (a mod b) with v end;
    intros H; first [discriminate H | lia]).
Qed.

Lemma mmap_arm_facts : forall sc cnt req u' nosm,
  0 <= sc < 48 -> 1 <= cnt <= 32 -> 16 * size_class sc * cnt < 2 ^ 20 -> (sc = 7 -> cnt <= 31) ->
  2048 < 16 * size_class sc * cnt + 16 -> 0 <= req < 2 ^ 40 ->
  let size := 16 * size_class sc in
  let cnt2 := mred sc size cnt u' nosm in
  let '(cnt3, needed3) := m3 size cnt2 req u' nosm in
  (1 <= cnt3 <= 32 /\ size * cnt3 < 2 ^ 20)
  /\ (aidx_of size cnt3 < cnt3 - 1 -> 4096 mod size <> 0)
  /\ (needed3 <= 2 ^ 20 \/ (cnt3 = 1 /\ needed3 = rup (req + 20))).
Proof.
  intros sc cnt req u' nosm Hsc Hcnt H20 H7 Hbig Hreq. cbn zeta.
  pose proof (size_class_page sc Hsc) as [SV SP].
  set (v := size_class sc) in *.
  pose proof (mred_cases sc (16 * v) cnt u' nosm) as MC. cbn zeta in MC.
  pose proof (mred_mod3 sc (16 * v) cnt u' nosm) as M3c.
  set (cnt2 := mred sc (16 * v) cnt u' nosm) in *.
  pose proof (m3_cases (16 * v) cnt2 req u' nosm) as TC.
  pose proof (m3_facts (16 * v) cnt2 req u' nosm) as TF.
  destruct (m3 (16 * v) cnt2 req u' nosm) as [cnt3 needed3].
  assert (C2 : 1 <= cnt2 <= 32 /\ 16 * v * cnt2 < 2 ^ 20) by (clear - Hcnt H20 MC SV; change (2 ^ 20) with 1048576 in *; lia).
  specialize (TF ltac:(lia) ltac:(lia) ltac:(lia)). cbn zeta in TF. destruct TF as (TF1 & TF2 & TF3 & TF4).
  assert (C3 : 1 <= cnt3 <= cnt2) by lia.
  split; [change (2 ^ 20) with 1048576 in *; nia|]. split.
  - (* [comment removed for export] *)
    intros Hlt Hmod. destruct (SP Hmod) as [[-> Ev]|[[-> Ev]|[[-> Ev]|[-> Ev]]]]; rewrite Ev in *.
    + lia.
    + lia.
    + specialize (M3c eq_refl). unfold aidx_of in Hlt. change (4080 / (16 * 4)) with 63 in Hlt.
      destruct (cnt3 <? 63) eqn:B; [apply Z.ltb_lt in B; lia | apply Z.ltb_ge in B; lia].
    + specialize (M3c eq_refl). specialize (H7 eq_refl). unfold aidx_of in Hlt. change (4080 / (16 * 8)) with 31 in Hlt.
      destruct (cnt3 <? 31) eqn:B; [apply Z.ltb_lt in B; lia | apply Z.ltb_ge in B]. cbn in Hlt. lia.
  - (* [comment removed for export] *)
    destruct TC as [[E3 En]|[E3 En]]; [left | right; lia].
    pose proof (rup_spec (16 * v * cnt2 + 16) ltac:(lia)) as [R1 R2]. rewrite En.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    change (2 ^ 20) with 1048576 in *. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
