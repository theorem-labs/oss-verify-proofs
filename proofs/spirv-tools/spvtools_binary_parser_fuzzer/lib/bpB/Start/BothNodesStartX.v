(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BStepTac BShapeAlg BpinAlg BAgentLib BHoare BRefLayout BothAcct BothAcctShape.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BxSymExec3Sound BxSymRun3 BothPlan BothPlanSound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothNodesAux BothStartLoops BothPlanCore Bcfg.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section NodesD.

  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Context {SC : StepCfg}.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis E_SP0 : AP.expr_vars_lt nx0 e_sp0_early = true.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  #[local] Notation Hv := (BothNodesAux.Hv A).
  #[local] Notation lazy_cover_vis := (BothNodesAux.lazy_cover_vis SEGS A LIMIT SINV argH FS0 HULL_ok).
  #[local] Notation H_off_segments_vis := (BothNodesAux.H_off_segments_vis SEGS A SEGS_in_hull).
  #[local] Notation mrestrict_Hv_high := (BothNodesAux.mrestrict_Hv_high A).
  #[local] Notation Mr_grows_Hv := (BothNodesAux.Mr_grows_Hv A argH).

  Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
  Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
  Hypothesis Fe1 : fetch_word SEGS (Z_to_bv 64 (x_envscan A)) = Some we1.
  Hypothesis Fe2 : fetch_word SEGS (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
  Hypothesis Fe3 : fetch_word SEGS (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
  Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
  Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
  Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
  Hypothesis Fp0 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
  Hypothesis Fp1 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
  Hypothesis Fp2 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A)) = Some wp2.
  Hypothesis Fp3 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
  Hypothesis Fp4 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
  Hypothesis Ep : is_ecall wp0 = false /\ is_ecall wp1 = false /\ is_ecall wp2 = false /\ is_ecall wp3 = false /\ is_ecall wp4 = false.
  Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hsp_lo : sp_window_lo <= bv_unsigned sp.
  Hypothesis Hsp_hi : bv_unsigned sp <= sp_window_hi.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  Let bsb := build_stack_bytes ph sp argv envp uid hw rdraw.

  Let EA := usp + 8 * argc + 16.
  Let STR0 := usp + 8 * argc + 8 * envc + 184.

  Hypothesis SINV_vals : forall E M, SINV E M ->
    uE E e_envp = EA /\ ev E V_ENVC = Z_to_bv 64 envc /\ uE E e_str0 = STR0.
  Hypothesis SINV_envp : forall E M (a : word), SINV E M ->
    EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem ph sp argv envp uid hw rdraw a.
  Hypothesis SINV_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M a = wrap_mem ph sp argv envp uid hw rdraw a.

  Hypothesis SINV_sp0 : forall E M, SINV E M -> uE E e_sp0_early = usp.

  Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma len_s0 : Z.of_nat (length s0) <= 131071.
  Proof. unfold s0. apply (valid_argv_str_len argv 0 Hva). destruct Hva as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. unfold sp_window_lo in Hsp_lo. lia. Qed.
  Lemma usp_hi : usp <= 0x800000000000.
  Proof. unfold usp. unfold sp_window_hi in Hsp_hi. lia. Qed.
  Lemma bsb_nw : usp + Z.of_nat (length bsb) < 2 ^ 64.
  Proof. unfold usp, bsb. apply lay_bsb_nw; assumption. Qed.

  Lemma STR0_eq : cat_argv_ptr sp argv envp 0 = Z_to_bv 64 STR0.
  Proof.
    pose proof len_av. pose proof len_ev. pose proof usp_hi.
    rewrite (cat_argv_ptr_offset sp argv envp 0) by (destruct Hva as [Hl _]; lia).
    unfold cat_string_base. rewrite nat_to_word_add_merge, word_add_nat.
    lazymatch goal with |- Z_to_bv 64 ?a = Z_to_bv 64 ?b => replace a with b; [reflexivity|] end.
    change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat.
    unfold cat_struct_size, auxv_size, STR0, usp, argc, envc. lia.
  Qed.

  Lemma rd_envp_k : forall M k, (k < length envp)%nat ->
    (forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem ph sp argv envp uid hw rdraw a) ->
    rdn SEGS M (Z_to_bv 64 (EA + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (cat_envp_ptr sp argv envp k)).
  Proof.
    intros M k Hk HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi.
    assert (Hk' : Z.of_nat k < envc) by (unfold envc; lia).
    rewrite (rdn_ext SEGS 8 M (wrap_mem ph sp argv envp uid hw rdraw)).
    - rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold EA in *; lia | rewrite u64_lit; unfold EA in *; [change (Z.of_nat 8) with 8|]; lia].
      rewrite <- n_to_le_8_spec.
      rewrite <- (read_envp_ptr_k SEGS ph sp rdraw argv envp uid hw Hva Hve Hsp_hi k Hk).
      f_equal. rewrite word_add_nat. f_equal. unfold envp_off, EA, argc, usp. lia.
    - rewrite u64_lit; unfold EA in *; [change (Z.of_nat 8) with 8|]; lia.
    - intros a Ha. rewrite u64_lit in Ha by (unfold EA in *; lia). change (Z.of_nat 8) with 8 in Ha. apply HM. lia.
  Qed.

  Lemma rd_envp_null : forall M,
    (forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem ph sp argv envp uid hw rdraw a) ->
    rdn SEGS M (Z_to_bv 64 (EA + 8 * Z.of_nat (length envp))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof.
    intros M HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi.
    rewrite (rdn_ext SEGS 8 M (wrap_mem ph sp argv envp uid hw rdraw)).
    - rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold EA, envc in *; lia | rewrite u64_lit; unfold EA, envc in *; [change (Z.of_nat 8) with 8|]; lia].
      rewrite <- n_to_le_8_spec.
      rewrite <- (read_envp_null SEGS ph sp rdraw argv envp uid hw Hva Hve Hsp_hi).
      f_equal. rewrite word_add_nat. f_equal. unfold envp_off, EA, argc, usp. lia.
    - rewrite u64_lit; unfold EA, envc in *; [change (Z.of_nat 8) with 8|]; lia.
    - intros a Ha. rewrite u64_lit in Ha by (unfold EA, envc in *; lia). change (Z.of_nat 8) with 8 in Ha. apply HM. unfold envc. lia.
  Qed.

  Lemma rd_str0_j : forall M j, (j <= length s0)%nat ->
    (forall a : word, STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M a = wrap_mem ph sp argv envp uid hw rdraw a) ->
    rdn SEGS M (Z_to_bv 64 (STR0 + Z.of_nat j)) 1 = Some [byte_at s0 j].
  Proof.
    intros M j Hj HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi. pose proof len_s0.
    rewrite (rdn_ext SEGS 1 M (wrap_mem ph sp argv envp uid hw rdraw)).
    - rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold STR0 in *; lia | rewrite u64_lit; unfold STR0 in *; [change (Z.of_nat 1) with 1|]; lia].
      unfold byte_at, s0.
      rewrite <- (read_argv_byte_k ph SEGS sp argv envp 0 j uid hw rdraw ltac:(destruct Hva as [Hl _]; lia) Hj bsb_nw).
      f_equal. rewrite STR0_eq, word_add_nat, u64_lit by (unfold STR0 in *; lia). reflexivity.
    - rewrite u64_lit; unfold STR0 in *; [change (Z.of_nat 1) with 1|]; lia.
    - intros a Ha. rewrite u64_lit in Ha by (unfold STR0 in *; lia). change (Z.of_nat 1) with 1 in Ha. apply HM. lia.
  Qed.

  Theorem x_sound_envscan : x_stmt SEGS A nx0 LIMIT SINV argH FS0 XEnvScan.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_envscan in Hn.
    destruct (Z.eqb (pc cs) (x_envscan A) && len_eqb (kn cs) (reg cs 9) e_envp)%bool eqn:Hc; [|discriminate].
    injection Hn as <-. apply andb_prop in Hc as [Hpc Heq]. apply Z.eqb_eq in Hpc.
    pose proof len_av as Lav. pose proof len_ev as Lev. pose proof usp_lo as U1. pose proof usp_hi as U2.
    destruct Xenv as (X1 & X2 & X3). destruct Ee as (Ee1 & Ee2 & Ee3).
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    destruct (SINV_vals E FULL HS) as (V1 & V2 & V3).
    pose proof (len_eqb_sound SEGS E _ (kn cs) (reg cs 9) e_envp (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Heq) as H9e.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as H9.
    replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) in H9 by (apply bv_eq; reflexivity). rewrite H9e in H9.
    assert (H9' : getr R 9%bv = Z_to_bv 64 (EA + 8 * Z.of_nat 0)).
    { rewrite H9. apply bv_eq. rewrite u64_lit by (unfold EA; lia). unfold uE in V1. rewrite V1. lia. }

    set (H2 := Hv E cs model).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    assert (HM : forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> mrestrict H2 FULL a = wrap_mem ph sp argv envp uid hw rdraw a).
    { intros a Ha. unfold H2. pose proof (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC) as HT. pose proof (SINV_sp0 E FULL HS) as HU. unfold uE in HU.
      rewrite mrestrict_Hv_high by (rewrite HT, HU; unfold EA, usp in *; lia). eapply SINV_envp; [exact HS | exact Ha]. }
    destruct (env_loop SEGS (x_envscan A) we1 we2 we3 ltac:(lia) Fe1 Fe2 Fe3 Ee1 Ee2 Ee3 De1 De2 De3
                (mrestrict H2 FULL) (seg_rom SEGS) EA (length envp) (cat_envp_ptr sp argv envp)
                ltac:(unfold EA, envc in *; lia)
                ltac:(intros k Kk; split; [apply rd_envp_k; [exact Kk | exact HM] | apply (cat_envp_ptr_nz ph sp rdraw argv envp uid hw Hva Hve Hsp_lo Hsp_hi k Kk)])
                (rd_envp_null _ HM) (length envp) 0%nat R ltac:(lia) H9') as [R' [Hms Hpost]].
    unfold cfg_of. fold ms.
    assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (mrestrict H2 FULL) (seg_rom SEGS))).
    { unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
    apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (mrestrict H2 FULL) (seg_rom SEGS)))
      with (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
    rewrite munrestrict_mrestrict.
    specialize (Hk E R' FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold cfg_of, pc in Hk. cbn [set_pc set_reg with_ss a_ss mk_ss s_pc] in Hk. rewrite X3 in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].

    unfold set_pc, set_reg. rewrite !a_ss_with_ss, !with_ss_idem. cbn [s_regs s_know s_next].
    eapply cs_ok_frame; [exact SINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
    cbn [s_regs]. destruct Hpost as (P9 & P10 & Pag).
    eapply (regs_ok_post2 E _ R R' 9 9%bv _ 10 10%bv); [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | lia | lia | reflexivity | reflexivity | | |].
    - rewrite P9. unfold eadd, escale. rewrite !mkAlu_denot, mkMd_denot, !edenot_lit. fold (reg cs 9). rewrite H9e.
      apply bv_eq. rewrite !u_add64, u_mul64, !u64_lit by lia. cbn [edenot]. rewrite V2, u64_lit by lia. unfold uE in V1. rewrite V1.
      rewrite (Z.mod_small (8 * envc)) by lia. rewrite (Z.mod_small (8 * envc + 8)) by lia.
      rewrite Z.mod_small by (unfold EA; lia). unfold envc. lia.
    - rewrite P10. rewrite edenot_lit. reflexivity.
    - intros r N1 N2. apply (Pag r). intros [H|H]; [exact (N1 H) | exact (N2 H)].
  Qed.

  Theorem x_sound_pnscan : x_stmt SEGS A nx0 LIMIT SINV argH FS0 XPnScan.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_pnscan in Hn.
    destruct (reg_lit cs 10) as [p|] eqn:Hp10; [|discriminate].
    destruct (reg_lit cs 12) as [c|] eqn:Hp12; [|discriminate].
    destruct c as [|pc|pc]; try discriminate.
    do 6 (destruct pc as [pc|pc|]; try discriminate).
    lazymatch type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [|discriminate] end.
    injection Hn as <-.
    apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Hlo].
    apply andb_prop in Hc as [Hc Hwr]. apply andb_prop in Hc as [Hpc Heq].
    apply Z.eqb_eq in Hpc. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
    pose proof len_av as Lav. pose proof len_ev as Lev. pose proof usp_lo as U1. pose proof usp_hi as U2. pose proof len_s0 as Ls0.
    destruct Xpn as (X1 & X2 & X3). destruct Ep as (Ep0 & Ep1 & Ep2 & Ep3 & Ep4).
    pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    destruct (SINV_vals E FULL HS) as (V1 & V2 & V3).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.

    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 p HC ltac:(lia) Hp10) as [H10 Hpr].
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 12 _ HC ltac:(lia) Hp12) as [H12 _].
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in H12 by (apply bv_eq; reflexivity).
    pose proof (len_eqb_sound SEGS E _ (kn cs) (reg cs 11) (eaddz e_str0 1) HK Heq) as H11e.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as H11.
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in H11 by (apply bv_eq; reflexivity). rewrite H11e in H11.
    assert (H11' : getr R 11%bv = Z_to_bv 64 (STR0 + Z.of_nat 0 + 1)).
    { rewrite H11. unfold eaddz. rewrite mkAlu_denot, edenot_lit. apply bv_eq. rewrite u_add64, !u64_lit by (unfold STR0; lia).
      unfold uE in V3. rewrite V3. rewrite Z.mod_small by (unfold STR0; lia). lia. }

    destruct (kwritable_sound SEGS E _ (kn cs) (kn cs) (ELit 0) p 8 HK HK Hwr ltac:(lia)) as (HKW & _ & _).
    unfold estart in HKW. cbn [a_base a_off] in HKW. rewrite edenot_lit, u64_lit in HKW by lia. rewrite Z.add_0_l in HKW.
    change (Z.to_nat 8) with 8%nat in HKW.

    set (H2 := Hv E cs model).
    set (M0 := mrestrict H2 FULL).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    assert (Hst0 : store_ok SEGS M0 (Z_to_bv 64 p) 8 = true).
    { eapply store_ok_mono; [apply Mr_grows_Hv | exact HKW]. }
    assert (HM : forall a : word, STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M0 a = wrap_mem ph sp argv envp uid hw rdraw a).
    { intros a Ha. unfold M0, H2. pose proof (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC) as HT. pose proof (SINV_sp0 E FULL HS) as HU. unfold uE in HU.
      rewrite mrestrict_Hv_high by (rewrite HT, HU; unfold STR0, usp in *; lia). eapply SINV_str0; [exact HS | exact Ha]. }
    destruct (pn_loop SEGS (x_pnscan A) wp0 wp1 wp2 wp3 wp4 ltac:(lia) Fp0 Fp1 Fp2 Fp3 Fp4 Ep0 Ep1 Ep2 Ep3 Ep4 Dp0 Dp1 Dp2 Dp3 Dp4
                M0 (seg_rom SEGS) p STR0 s0
                ltac:(unfold KHI in *; lia) ltac:(unfold STR0; lia) ltac:(left; unfold STR0, KHI in *; lia)
                (valid_argv_str_nz argv 0 Hva ltac:(destruct Hva as [Hl _]; lia))
                (fun j Hj => rd_str0_j M0 j Hj HM) Hst0
                s0 0%nat R M0 eq_refl ltac:(lia) H10 H11' H12 (cellrel_refl M0 p)) as (R' & M' & Hms & Hpost & HM').
    unfold cfg_of. fold ms.
    assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) M' (seg_rom SEGS))).
    { unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
    apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) M' (seg_rom SEGS)))
      with (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) (munrestrict H2 FULL M') (seg_rom SEGS)).
    set (FULL' := munrestrict H2 FULL M').
    assert (HF : forall a : word, bv_unsigned a < p \/ p + 8 <= bv_unsigned a -> FULL' a = FULL a).
    { intros a Ha. unfold FULL', munrestrict. destruct (H2 a) eqn:H2a; [reflexivity|].
      destruct HM' as [HM1 _]. rewrite (HM1 a Ha). unfold M0, mrestrict. rewrite H2a. reflexivity. }

    set (v := nxt cs). set (E' := ext1 E v (getr R' 11%bv)).
    assert (Hag : env_agree v E E') by apply ext1_agree.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH E_SP0 argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
    pose proof (hid_agree A nx0 argH argH_agree v E E' cs model Hag Fle Fallow) as Hhid.
    specialize (Hk E' R' FULL' model' (conj (env_agree_le nx0 v E E' Hag Fle) Hag)).
    unfold cfg_of, pc in Hk. cbn [a_ss with_ss mk_ss s_pc] in Hk. rewrite X3 in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].

    eapply cs_ok_frame; [exact SINV_frame | exact HC' | exact Hsame | | | reflexivity | |].
    - rewrite (allowA_agree A v E E' cs Hag Fallow). exact Hinv'.
    - cbn [s_regs]. destruct Hpost as (P11 & P13 & Pag).
      eapply (regs_ok_post2 E' _ R R' 11 11%bv _ 13 13%bv); [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') | lia | lia | lia | reflexivity | reflexivity | | |].
      + cbn [edenot]. unfold E'. rewrite ext1_at. reflexivity.
      + rewrite P13, edenot_lit. reflexivity.
      + intros r N1 N2. apply (Pag r). intros [H|H]; [exact (N1 H) | exact (N2 H)].
    - cbn [s_know]. unfold Mr. rewrite Hhid.
      apply (know_ok_havoc SEGS E' (mrestrict (hid A argH E cs model) FULL)).
      + apply kimg_cut_sound. pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC') as HK'. unfold Mr in HK'. rewrite Hhid in HK'. exact HK'.
      + intros x Hx. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite !u64_lit in Hx by lia.
        unfold mrestrict. rewrite HF by lia. reflexivity.
      + intros x Hx. unfold mrestrict in *. destruct (hid A argH E cs model x) eqn:Hh; [exact Hx|].
        unfold FULL', munrestrict. unfold hid in Hh. apply orb_false_iff in Hh as [_ Hvx].
        unfold H2 at 1. unfold Hv. rewrite Hvx. cbn [negb].
        destruct HM' as [_ HM2]. apply HM2. unfold M0, mrestrict, H2, Hv. rewrite Hvx. cbn [negb]. exact Hx.
    - intros a Ha. rewrite Hhid in Ha. unfold hid in Ha. apply orb_prop in Ha as [Ha|Ha].
      + apply HF. right. pose proof (argH_high E a Ha). unfold CEIL, KHI in *. lia.
      + unfold FULL', munrestrict. unfold H2 at 1. unfold Hv. rewrite Ha. reflexivity.
  Qed.

End NodesD.

Lemma some_inj_acs : forall a b : acs, Some a = Some b -> a = b.
Proof. intros a b H. exact (f_equal (fun o => match o with Some x => x | None => a end) H). Qed.

Section LayoutSound.
  Variable SEGS : list Segment.
  Context {SC : StepCfg}.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.

  Lemma e_argv1w_ge2 : forall E, 2 <= bv_unsigned (ev E V_ARGC) -> edenot E e_argv1w = edenot E e_str1.
  Proof.
    intros E H. unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit by lia.
    replace (1 <? bv_unsigned (ev E V_ARGC)) with true by (symmetry; apply Z.ltb_lt; lia).
    pose proof (u64_range (edenot E e_str1)). rewrite Z.mul_1_l. apply Z.mod_small. lia.
  Qed.

  Lemma e_argv1w_le1 : forall E, bv_unsigned (ev E V_ARGC) <= 1 -> edenot E e_argv1w = edenot E (ELit 0).
  Proof.
    intros E H. unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, !u64_lit by lia.
    replace (1 <? bv_unsigned (ev E V_ARGC)) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  Qed.

  Lemma kw_argv1_respell : forall E M v v',
    kentry_ok SEGS E M (kw_argv1 v) -> edenot E v' = edenot E v -> kentry_ok SEGS E M (kw_argv1 v').
  Proof. intros E M v v' HK Hv. unfold kw_argv1 in *. cbn [kentry_ok] in *. rewrite Hv. exact HK. Qed.

  Theorem x_sound_layout : x_stmt SEGS A nx0 LIMIT SINV argH FS0 XLayout.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_layout in Hn.
    destruct (existsb (kentry_eqb (kw_argv1 e_argv1w)) (kn cs)) eqn:Hex; [|discriminate]. cbn [negb] in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.

    apply existsb_exists in Hex as [K0 [Hin Heqb]]. apply kentry_eqb_eq in Heqb. subst K0.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HK0.
    assert (HK' : know_ok SEGS E (Mr A argH E cs model FULL)
                    (List.filter (fun K => negb (kentry_eqb (kw_argv1 e_argv1w) K)) (kn cs)))
      by (apply know_ok_filter; exact HK).
    assert (FIN : forall v, edenot E v = edenot E e_argv1w ->
                  cs' = set_kn cs (kw_argv1 v :: List.filter (fun K => negb (kentry_eqb (kw_argv1 e_argv1w) K)) (kn cs)) ->
                  srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T).
    { intros v Hv ->. specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
      rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
      apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK'].
      eapply kw_argv1_respell; [exact HK0 | exact Hv]. }

    destruct args as [|[z| | | | | | |] [|e2 l2]]; try discriminate; destruct z as [|pz|pz]; try discriminate;
      try (destruct pz; try discriminate).
    -
      destruct (xhi (kn cs) (EVar V_ARGC)) as [hi|] eqn:Hhi; [|discriminate].
      destruct (Z.leb hi 1) eqn:Hle; [|discriminate]. apply Z.leb_le in Hle. apply some_inj_acs in Hn.
      pose proof (xhi_sound SEGS E _ (kn cs) (EVar V_ARGC) hi HK Hhi) as B. cbn [edenot] in B.
      apply (FIN (ELit 0)); [|symmetry; exact Hn]. symmetry. apply e_argv1w_le1. lia.
    -
      destruct (xlo (kn cs) (EVar V_ARGC)) as [lo|] eqn:Hlo; [|discriminate].
      destruct (Z.leb 2 lo) eqn:Hle; [|discriminate]. apply Z.leb_le in Hle. apply some_inj_acs in Hn.
      pose proof (xlo_sound SEGS E _ (kn cs) (EVar V_ARGC) lo HK Hlo) as B. cbn [edenot] in B.
      apply (FIN e_str1); [|symmetry; exact Hn]. symmetry. apply e_argv1w_ge2. lia.
  Qed.
End LayoutSound.

