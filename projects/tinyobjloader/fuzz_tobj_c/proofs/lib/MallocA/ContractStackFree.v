(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "true"; "nat"; "list"; "prod"; "app"; "pair"; "andb"; "None"; "false"; "option"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rw"; "valuation"; "sv"; "SVar"; "FcsrFrm0"; "SLit"; "mkSS"; "rm"; "swf"; "cell"; "agree_below"; "sprop"; "sprop_below"; "SAlu"; "eval"; "mkCell"; "smatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "L_stack_free"; "V_FL"; "JL_stack_free"; "Kc_ok"; "Pre_stack_freeI"; "stack_free_contractA"; "stack_free_contractA_ex"; "stack_win"; "O_got"; "O_rtc"; "V_DEPTH"; "ae_ret_stack_free"; "ae_stack_free"; "base_sv"; "flag_obj"; "flagbyte_obj"; "frame_obj"; "pre_facts"; "stack_malloc_depth"; "A_globals"; "J_stack_free_pre"; "J_stack_free_preT"; "frame_flag"; "mem_keptA"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "div"; "add"; "pow"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "check_cfgA"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_frames"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_live"; "ag_fsb"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "NW"; "F_sf"; "Post_sf"; "Pre_sf"; "O_khigh"; "vG"; "O_fshadow"; "cuts_sf"; "exits_sf"; "f5_cells"; "gsv"; "shb"; "win_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "fs_frame_size"; "Sh"; "FS_total"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "entailsA"; "mkAX"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractStackFree.SF"; "sf_checks"; "R_sf"; "rho1_of"; "s_sf"; "st3"; "objs0"; "st1"; "st2"; "st2x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@Stdlib.Lists.List"; "In"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "in_ranges"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "vmd"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require TopGlueA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.TopGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SF.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (c : Z) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S3bVAInv;Vc;VA;VKc;A4").

Definition objs0 (c : Z) : list sobj := ltac2:(tb__ "0|2|
S8S12S1S12S2dS1S12S36S16PcA1M0Vc;A2S1S12S34G0Vc;S16S27A1M1A3S1S12S35G1S2S1cA1A2S2S12A1A3A3A3A3S39A3").
Definition st1 (c : Z) : sstate := ltac2:(tb__ "0|0|
S19S32S24Vc;A2S69S67S17SbS15A1S8S12S78Vc;A1S1S12S57S2S12A1A3A3S37S38A1S53ScA9").
Definition st2 (c : Z) : sstate := ltac2:(tb__ "0|1|
S19S32S24Vc;A2S69S67S17SbS15A1S8S12S8S12S78Vc;A1S1S12S57S2S12A1M0A3A3S1S12S59Vc;S2S7S7S0S5A2S15A2A1A2G0A3A3S37S38A1S53ScA9").

Definition rho1_of (rho : valuation) : valuation := ltac2:(tb__ "0|1|
S8dVrho;S58S65Q40M0S40S64G0S13Vrho;PcA2A2Z8A2A2A3").

Lemma rho1_agree : ltac2:(tb__ "0|0|
S14S1dS58R1S75R1A1A3Frho;").
Proof.
  intros rho. split; [|split; [intros; reflexivity | intros; reflexivity]].
  intros i Hi. unfold rho1_of. rewrite rho_set_rw_other; [reflexivity | lia].
Qed.

Lemma J_rm_only : ltac2:(tb__ "0|4|
S0S49S25S14S14S6S63Q40A1M0A1S6S82A1S81SeG0SdS63Q8A1A1F_;S1aR4A1S1aR5A1A3SeG0S13R5PcM1A2S13R6G1A2A3SeG0S13R6P18M2A2S13R7G2A2A3SeG0S13R7S27A2S13R8S27A2A3SeG0S13R8PaM3A2S13R9G3A2A3SeG0S13R9S30A2S13RaS30A2A3VJ;ReRdRcRbR9R8R7A7VJ;RfReRdRbRaR9R8A7F_;F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FKc;FA;Fc;").
Proof.
  intros c A Kc rho rho' tp tr md Hrm H12 H24 H16 H10 H15 (HA & HK & Htp & Hin & Hfl & Htop).
  unfold J, J_stack_free_preT, tp_ok, top_high. rewrite H12, H24, H16, H10, H15. split; [|repeat split; auto].
  unfold AInv, AInvA in *. rewrite Hrm. exact HA.
Qed.

Lemma sf_instantiate : ltac2:(tb__ "0|0|
S3S0S49S25S14S6S63Q40A1A1S7cSfS3fZ0R6A2S3eR6ZbA2A2SeS3S1bS79R7A1A1S4A3SeS3S1bS7aR8A1A1S4A3SeS3S80S1eS1fS53A1S54RaR9A2A3S4A3S5fRbS50S4aR9A1A1S62A3S70Vsegs;VJ;RbRaR9A3S2aS24RbA2R8R7R6A6S70Vsegs;VJ;RcRbRaA3S56S24RdRcA3S75R9A1R8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;Fc;Fhi;").
Proof.
  intros hi c A Kc rho tp w Hc Hwf1 Hwf2 Hfb Hwin H.
  set (rho1 := rho1_of rho).

  pose proof H as [HsmA HJ]. destruct HJ as (HA & HK & Htp & Hin & Hfl & Htop).
  pose proof HA as (HG & HR & HF & HRest & HM).
  destruct (aa_frames_fact _ A _ _ HF Hin) as (c' & pos & u & v & Hc' & Hsz & Ebusy & Hnotin & Hpos & Hf & Hnth).
  assert (c' = c) by (apply fs_frame_size_inj; lia). subst c'. clear Hsz.
  pose proof (fs_geom_nums (aa_geom A) c pos HG Hc Hpos) as NUM. cbn zeta in NUM.
  rewrite <- Hf in NUM. destruct NUM as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  set (F := ag_fsb (aa_geom A)) in *. set (f := bv_unsigned (rw rho 12%positive)) in *.
  assert (Efl : bv_unsigned (rw rho V_FL) = fs_flags F c + pos).
  { rewrite Hfl. unfold frame_flag. cbn [fst snd]. unfold fs_flag_addr. rewrite fs_class_of_size_ok by lia.
    fold F. rewrite Hf, fs_pos_frame by lia. reflexivity. }

  assert (H1 : SPA segs (J c A Kc) (Pre_stack_freeI AE_A c) rho1 tp w).
  { eapply SPA_agree; [| |exact H].
    - eapply agree_below_le; [|apply rho1_agree]. cbv. discriminate.
    - apply J_rm_only; reflexivity. }
  clear H HsmA.

  pose proof (topG_range (aa_geom A)) as TG. pose proof (proj1 (geom_bands _ HG)) as WB. fold F in WB.
  rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in *. unfold IMG_HI in N8. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB.
  assert (E12 : rw rho1 12%positive = rw rho 12%positive) by reflexivity.
  assert (E16 : rw rho1 V_FL = rw rho V_FL) by reflexivity.
  assert (Erm : rm rho1 = rm rho) by reflexivity.

  assert (H2 : SPA segs (J c A Kc) (mkAX (st1 c) [] base_sv) rho1 tp w).
  { change (mkAX (st1 c) [] base_sv) with
      (ax_setS (Pre_stack_freeI AE_A c)
         (let S := ax_S (Pre_stack_freeI AE_A c) in
          mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [carved (SLit 0) 0xf20e0 0xf20f8 khigh_cells]) (ss_facts S) NW (ss_lenient S))).
    eapply SPA_carve_obj; [exact H1 | exact Hwf1 | cbv; discriminate | cbn [eval]; rewrite ?u64_lit; try lia ..].
    all: cbn [eval]; rewrite ?u64_lit by lia.
    all: try lia.
    - unfold cells_inside, khigh_cells. repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
    -
      pose proof (proj1 H1) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
      pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
      assert (Hhigh : holds rho1 F_sp_high).
      { apply (proj1 (Forall_forall _ _) HFa). cbn. tauto. }
      destruct (stack_win_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
      cbn [ss_objs ax_S Pre_stack_freeI mkA objs0 app]. unfold A_globals, frame_obj, flag_obj, flagbyte_obj, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
      pose proof (fs_frame_size_pos c ltac:(lia)).
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint;
        try (rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E12, ?E16, ?u64_lit by lia; fold f; lia).
      destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia.
    -
      intros off Hoff. split; [apply wok_of_imageA; lia|].
      rewrite Erm.
      pose proof (cells_ok_nth _ _ 20 _ HR eq_refl) as C20. pose proof (cells_ok_nth _ _ 21 _ HR eq_refl) as C21.
      pose proof (cells_ok_nth _ _ 22 _ HR eq_refl) as C22. unfold cell_ok in C20, C21, C22. cbn [c_addr c_w c_val] in C20, C21, C22.
      destruct (Z_lt_dec off 0xf20e8); [|destruct (Z_lt_dec off 0xf20f0)].
      + eexists. rewrite <- view_in by lia. replace (0 + off) with (991456 + Z.of_nat (Z.to_nat (off - 991456))) by lia. apply C20. lia.
      + eexists. rewrite <- view_in by lia. replace (0 + off) with (991464 + Z.of_nat (Z.to_nat (off - 991464))) by lia. apply C21. lia.
      + eexists. rewrite <- view_in by lia. replace (0 + off) with (991472 + Z.of_nat (Z.to_nat (off - 991472))) by lia. apply C22. lia.
    - unfold cells_in_view, khigh_cells. rewrite Erm.
      pose proof (cells_ok_nth _ _ 20 _ HR eq_refl) as C20. pose proof (cells_ok_nth _ _ 21 _ HR eq_refl) as C21.
      pose proof (cells_ok_nth _ _ 22 _ HR eq_refl) as C22. unfold cell_ok in C20, C21, C22. cbn [c_addr c_w c_val] in C20, C21, C22.
      repeat apply Forall_cons; try apply Forall_nil; intros j Hj; cbn [eval]; rewrite Z.add_0_l; rewrite <- view_in by lia.
      + exact (C20 j Hj). + exact (C21 j Hj). + exact (C22 j Hj).
    - apply xwords_clear_nil. }
  clear H1.
  assert (EvG : rw rho1 vG = Z_to_bv 64 (f / 8)) by (unfold rho1, rho1_of; rewrite rho_set_rw_at; reflexivity).
  pose proof (urange (rw rho 12%positive)) as R12. fold f in R12.
  assert (Esh : bv_unsigned (eval rho1 (SAlu ALU_ADD (gsv (SVar 12)) shb)) = Sh f).
  { unfold shb. cbn [eval]. fold (gsv (SVar 12)). rewrite add_val, gsv_val. cbn [eval]. rewrite ?E12. fold f. rewrite !u64_lit by (unfold SHADOW_OFF; lia).
    unfold Sh, SHADOW_OFF. rewrite Z.mod_small by lia. reflexivity. }
  assert (ShF : Sh (F + 36864) <= Sh f) by (apply Sh_mono; lia).
  assert (ShE : Sh f + fs_frame_size c / 8 <= Sh (F + 11571200)).
  { unfold Sh. replace (f / 8 + SHADOW_OFF + fs_frame_size c / 8) with ((f + fs_frame_size c) / 8 + SHADOW_OFF).
    - apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
    - replace f with (f / 8 * 8) at 1 by (pose proof (Z.div_mod f 8); pose proof (Z.mod_divide f 64); lia).
      rewrite Z.div_add_l by lia. lia. }

  assert (ShLo : 0x800b7600 <= Sh (F + 36864)) by (unfold Sh, SHADOW_OFF; lia).
  assert (ShHi : Sh (F + 11571200) < 17594333495296) by (unfold Sh, SHADOW_OFF; lia).
  pose proof (fs_frame_size_pos c ltac:(lia)) as SZP.
  assert (SZ8 : 0 <= fs_frame_size c / 8) by (apply Z.div_pos; lia).
  destruct HF as (Flen & Fcls & Fhint & Fflags & Ffree & Fsh).
  fold F in Fhint, Fflags, Ffree, Fsh. rewrite FS_frames_off_val, FS_total_val in Fsh.

  assert (H3 : SPA segs (J c A Kc) (mkAX (st2 c) [] base_sv) rho1 tp w).
  { change (mkAX (st2 c) [] base_sv) with
      (ax_setS (mkAX (st1 c) [] base_sv)
         (let S := ax_S (mkAX (st1 c) [] base_sv) in
          mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [carved (SAlu ALU_ADD (gsv (SVar 12)) shb) 0 (fs_frame_size c / 8) []]) (ss_facts S) NW (ss_lenient S))).
    eapply SPA_carve_obj; [exact H2 | exact Hwf2 | cbv; discriminate | rewrite ?Esh; try lia ..].
    all: rewrite ?Esh. all: try lia.
    - constructor.
    -
      pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
      pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
      assert (Hhigh : holds rho1 F_sp_high).
      { apply (proj1 (Forall_forall _ _) HFa). cbn. tauto. }
      destruct (stack_win_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
      cbn [ss_objs ax_S st1 objs0 app]. unfold A_globals, frame_obj, flag_obj, flagbyte_obj, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI, O_khigh, carved.
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint;
        try (rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite ?E12, ?E16, ?u64_lit by lia; fold f; lia).
      destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *. lia.
    -
      intros off Hoff. rewrite Erm.
      destruct (Fsh (Sh f + off) ltac:(lia)) as [b Hb].
      unfold restrictv in Hb. destruct (fs_footb (aa_geom A) (Sh f + off)) eqn:FB; [|discriminate].
      rewrite view_in in Hb by lia.
      exact (wok_rd_off_image (rm rho) (Sh f + off) b ltac:(lia) Hb).
    - constructor.
    - apply xwords_clear_nil. }
  clear H2.

  change (Pre_sf AE_A hi c) with (ax_with_facts (mkAX (st2 c) [] base_sv) (F_sf hi c)).
  eapply SPA_refacts; [exact H3 | exact Hfb |].
  intros Hold. unfold F_sf.
  pose proof (urange (rw rho V_FL)) as R16.
  assert (A8 : bv_unsigned (eval rho1 (SAlu ALU_SLL (SVar vG) (SLit 3))) = f).
  { cbn [eval]. rewrite sll_val, EvG, u64_lit by lia. change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia.
    change (2 ^ 3) with 8. rewrite Z.mod_small; [|split; [lia|]]. all: pose proof (Z.div_mod f 8); pose proof (Z.mod_divide f 64); try lia.
    all: assert (f mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply (Z.divide_trans _ 64); [exists 8; reflexivity| apply Z.mod_divide; lia]); lia. }
  apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|exact Hold]]].
  -
    destruct hi; unfold win_hyp in Hwin; fold F in Hwin; unfold F_win, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in *;
      repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?add_val, ?E12, ?E16, ?u64_lit; fold f; lia.
  - repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?add_val, ?E12, ?E16, ?u64_lit; fold f; lia.
  - cbn [eval] in A8. unfold F8, g8. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?add_val, ?A8, ?E12, ?EvG, ?u64_lit; fold f; lia.
Qed.

Definition idxs_sf : list nat := ltac2:(tb__ "0|0|
S1S5U0S1S5U4S1S5U5S1S5U1S1S5U2S1S5U3S1S5U6S1S5U7S2S5A1A3A3A3A3A3A3A3A3").
Definition R_sf (c : Z) : list sobj := ltac2:(tb__ "0|4|
S1S12S36S16PcA1M0Vc;A2S1S12S34G0Vc;S16S27A1M1A3S1S12S35G1S1S1cS22S18Z0A1M2Z1G2A3S2S1cA1A3A2S1S12S57S1S12S59Vc;S5cS43S40S40S60Vc;A1Z8M3A2G3A2A1A1A2S2S12A1A3A3A3A3A3").
Definition st2x (hi : bool) (c : Z) : sstate := ltac2:(tb__ "0|0|
S19S31S24Vc;A2S68S52A1S67S17SbS15A1S8S12S1S12S2dS1S12S2eS1S12S2fS2S12A1A3A3A3S74Vc;A1A3S54Vhi;Vc;A2S53ScA9").
Definition st3 (hi : bool) (c : Z) : sstate := ltac2:(tb__ "0|0|
S19S31S24Vc;A2S68S52A1S67S17SbS15A1S1S12S2dS1S12S2eS1S12S2fS2S12A1A3A3A3S54Vhi;Vc;A2S53ScA9").
Definition s_sf (hi : bool) (c : Z) : wsub := ltac2:(tb__ "0|0|
S8cS66S77Vhi;Vc;A2S6dS26S24Vc;A2A1A3").

Definition J_T (Kc : KcA) : jpredA := fun _ _ t m => Kc t m.

Lemma R_sf_ranges : ltac2:(tb__ "0|6|
S0S14S63Q40M0A1S0S0SfS3fZ0R5A2S3eR5ZbA2A2S3fZ40S60R6A1A2SeS0S64G0S13R6PcM1A2A2R4A3SeS0S64G0S13R7S27A2A2R4A3SeS0S64G0S21R8S20S8bS5dS16G1A1A1S5eA3A2A2S61R6A1A3S3eS41R7S60RaA1A2S42Z2Z3eA2M2A2S3eS41R7Z1A2G2A2S3eS41S61R9A1S40S60RcA1Z8M3A2A2G2A2S84RcS74RdA1RbA3S64G0RcA2S0S11SfS3fRcR1A2S3eR1S41RcS60RfA1M4A2A2A2S11SeS0R1RbA3S11SfS3fZf20e0R1A2S3eR1Zf20f8A2A2SfS3fS61RcA1M5R1A2S3eR1S41G5S40G4G3A2A2A2A2A2A2A2Tz;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ffl;Ff;Fa;FrhoE;Fc;").
Proof.
  intros c rhoE a f fl Hc SZP E12 E16 Esh B1 B2 B3 (o & Hin & Hr) z. subst z.
  assert (SZ8 : 0 <= fs_frame_size c / 8) by (apply Z.div_pos; lia).
  pose proof (urange (rw rhoE 12%positive)). pose proof (urange (rw rhoE V_FL)).
  assert (0 <= Sh f) by (unfold Sh, SHADOW_OFF; lia).
  unfold R_sf in Hin. cbn [In] in Hin.
  unfold frame_obj, flag_obj, flagbyte_obj, O_khigh, O_fshadow, carved in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; rewrite obj_range_mk in Hr by lia; cbn [fst snd ob_base] in Hr; rewrite ?Esh in Hr;
    try (cbn [eval] in Hr; rewrite ?E12, ?E16, ?u64_lit in Hr by lia); lia.
Qed.

Lemma sf_rebuild : ltac2:(tb__ "0|5|
S3S0S49S14S6S63Q40M0A1M1A1S6S82A1M2S88S81SfS3fZ0R7A2S3eR7ZbA2A2VAInv;R7R6R5R2A4S64G0S13R7PcA2A2S0S7fS7S0S0A2M3S9S0S0R1S60RaA1A4S4bR9A1A3SeS0S64G0S13R9S27A2A2S3cS4aRaA1S9S0S0R2S60RbA1A4A2A3SeG1S13RaS58A2S65G0S40R3Z8A2A2A3S23Vsegs;RbS7bReRdA2S9G2S89R9S8aS86R7RaR8A3S87R7A1A2A4A4S85RcS74ReA1S86R8RbR9A3A3S14S10S49S49S10S6G3A1M4G4S10G4G4SfVAInv;R3R4RfRcA4SfSeG4S4fR3A1S4fR11A1A3SfSeG4S4bR11A1S8G3R2S1G3S9S0S0R9S60R12A1A4R1A3A3A3SfSeG4S4bR3A1S8G3R2R1A3A3SfSeS0S4eR3A1S4eR11A1A3SfSeS0S4dR3A1S4dR11A1A3SfSeS0S4cR3A1S4cR11A1A3SfSeS51S4aR3A1S4aR11A1A3S3dVCST;VXGL;R11R3S1aR10A1S1aR4A1A6A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Trho3;F_;F_;F_;F_;Tf;F_;F_;Fmd;Fms;Ftr;Ftp;FrhoE;FA;Fc;Fhi;").
Proof.
  intros hi c A rhoE tp tr ms md Hc HA f Hin Hfl EvG Hsm rho3.
  pose proof HA as (HG & HR & HF & HRest & HM).
  destruct (aa_frames_fact _ A _ _ HF Hin) as (c' & pos & u & v & Hc' & Hsz & Ebusy & Hnotin & Hpos & Hf & Hnth).
  assert (c' = c) by (apply fs_frame_size_inj; lia). subst c'. clear Hsz Hc'.
  pose proof (fs_geom_nums (aa_geom A) c pos HG Hc Hpos) as NUM. cbn zeta in NUM.
  rewrite <- Hf in NUM. destruct NUM as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  set (F := ag_fsb (aa_geom A)) in *.
  pose proof (topG_range (aa_geom A)) as TG. pose proof (proj1 (geom_bands _ HG)) as WB. fold F in WB.
  rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in *. unfold IMG_HI in N8. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB.
  set (fl := fs_flags F c + pos).
  assert (Efl : bv_unsigned (rw rhoE V_FL) = fl).
  { rewrite Hfl. unfold frame_flag. cbn [fst snd]. unfold fs_flag_addr. rewrite fs_class_of_size_ok by lia.
    fold F. rewrite Hf, fs_pos_frame by lia. reflexivity. }
  pose proof (urange (rw rhoE 12%positive)) as R12. fold f in R12.
  assert (Esh : bv_unsigned (eval rhoE (SAlu ALU_ADD (gsv (SVar 12)) shb)) = Sh f).
  { unfold shb. cbn [eval]. fold (gsv (SVar 12)). rewrite add_val, gsv_val. cbn [eval]. rewrite ?E12. fold f. rewrite !u64_lit by (unfold SHADOW_OFF; lia).
    unfold Sh, SHADOW_OFF. rewrite Z.mod_small by lia. reflexivity. }
  assert (ShF : Sh (F + 36864) <= Sh f) by (apply Sh_mono; lia).
  assert (ShE : Sh f + fs_frame_size c / 8 <= Sh (F + 11571200)).
  { unfold Sh. replace (f / 8 + SHADOW_OFF + fs_frame_size c / 8) with ((f + fs_frame_size c) / 8 + SHADOW_OFF).
    - apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
    - replace f with (f / 8 * 8) at 1 by (pose proof (Z.div_mod f 8); pose proof (Z.mod_divide f 64); lia).
      rewrite Z.div_add_l by lia. lia. }
  assert (ShLo : 0x800b7600 <= Sh (F + 36864)) by (unfold Sh, SHADOW_OFF; lia).
  assert (ShHi : Sh (F + 11571200) < 17594333495296) by (unfold Sh, SHADOW_OFF; lia).
  pose proof (fs_frame_size_pos c ltac:(lia)) as SZP.
  assert (SZ8 : 0 <= fs_frame_size c / 8) by (apply Z.div_pos; lia).

  set (A' := fs_release A c pos).
  assert (HB : nth_error (aa_fs_busy A) (Z.to_nat c) = Some (u ++ (pos, f) :: v)) by (rewrite Hnth, Ebusy; reflexivity).
  destruct (frames_of_release (aa_fs_busy A) 0 (Z.to_nat c) u pos f v HB) as (l1 & l2 & E1 & E2).
  rewrite Z.add_0_l, Z2Nat.id in E1 by lia.
  assert (EB' : aa_fs_busy A' = list_upd (aa_fs_busy A) (Z.to_nat c) (u ++ v)).
  { unfold A', fs_release. cbn [aa_fs_busy]. f_equal. change (nth (Z.to_nat c) (aa_fs_busy A) []) with (fs_busy A c).
    rewrite Ebusy. apply remove_pos_split. exact Hnotin. }

  pose proof (absorb_carved_cells segs rhoE (st2x hi c) tr (vms md tp ms) (vmd md) [stack_win; O_got; O_rtc] (R_sf c)
                (SVar 12) 0 (fs_frame_size c - 8) [] Hsm eq_refl ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(constructor)) as [_ P1].
  pose proof (absorb_carved_cells segs rhoE (st2x hi c) tr (vms md tp ms) (vmd md) [stack_win; O_got; O_rtc] (R_sf c)
                (SVar 12) (fs_frame_size c - 8) (fs_frame_size c) [(fs_frame_size c - 8, 8%nat, SVar V_FL)] Hsm eq_refl
                ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; apply Forall_cons; [cbn; lia|apply Forall_nil])) as [_ P2].
  pose proof (absorb_carved_cells segs rhoE (st2x hi c) tr (vms md tp ms) (vmd md) [stack_win; O_got; O_rtc] (R_sf c)
                (SVar V_FL) 0 1 [(0, 1%nat, SLit 0)] Hsm eq_refl
                ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; apply Forall_cons; [cbn; lia|apply Forall_nil])) as [C3 _].
  pose proof (absorb_carved_cells segs rhoE (st2x hi c) tr (vms md tp ms) (vmd md) [stack_win; O_got; O_rtc] (R_sf c)
                (SLit 0) 0xf20e0 0xf20f8 khigh_cells Hsm eq_refl
                ltac:(right; right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside, khigh_cells; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)) as [C4 _].
  pose proof (absorb_carved_cells segs rhoE (st2x hi c) tr (vms md tp ms) (vmd md) [stack_win; O_got; O_rtc] (R_sf c)
                (SAlu ALU_ADD (gsv (SVar 12)) shb) 0 (fs_frame_size c / 8) (f5_cells (Z.to_nat (fs_frame_size c / 8 / 8))) Hsm eq_refl
                ltac:(right; right; right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as P5.
  assert (CI5 : forall k n, 8 * Z.of_nat k <= n -> cells_inside 0 n (f5_cells k)).
  { induction k as [|k IH]; intros n Hn; [constructor|]. cbn [f5_cells]. apply Forall_cons; [cbn; lia|]. apply IH. lia. }
  specialize (P5 ltac:(apply CI5; rewrite Z2Nat.id by lia; pose proof (Z.div_mod (fs_frame_size c) 64); pose proof (Z.div_mod (fs_frame_size c / 8) 8); nia)).
  destruct P5 as [_ P5]. cbn zeta in P5.
  cbn [eval] in P1, P2, C3, C4. rewrite Esh in P5. rewrite Efl in C3. fold f in P1, P2. rewrite u64_lit in C4 by lia.
  fold rho3 in P1, P2, C3, C4, P5.

  set (v3 := view segs (rm rho3)). set (vE := view segs (rm rhoE)).
  assert (V1 : forall z, f <= z < f + fs_frame_size c -> exists x, v3 z = Some x).
  { intros z Hz. unfold v3. rewrite view_in by lia.
    destruct (Z_lt_dec z (f + fs_frame_size c - 8)).
    - destruct (P1 (z - f) ltac:(lia)) as [x Hx]. exists x. replace z with (f + (z - f)) at 1 by lia. exact Hx.
    - destruct (P2 (z - f) ltac:(lia)) as [x Hx]. exists x. replace z with (f + (z - f)) at 1 by lia. exact Hx. }
  assert (V2 : v3 fl = Some (Z_to_bv 8 0)).
  { unfold v3. pose proof (urange (rw rhoE V_FL)). rewrite view_in by lia.
    unfold cells_in_view in C3. apply Forall_inv in C3. specialize (C3 0%nat ltac:(lia)). cbn [Z.of_nat] in C3. rewrite !Z.add_0_r in C3. exact C3. }
  assert (V4 : forall z, Sh f <= z < Sh f + fs_frame_size c / 8 -> exists x, v3 z = Some x).
  { intros z Hz. unfold v3. rewrite view_in by (unfold Sh, SHADOW_OFF in *; lia).
    destruct (P5 (z - Sh f) ltac:(lia)) as [x Hx]. exists x. replace z with (Sh f + (z - Sh f)) at 1 by lia. exact Hx. }
  assert (V5 : forall z, ~ (f <= z < f + fs_frame_size c \/ z = fl \/ 0xf20e0 <= z < 0xf20f8 \/ Sh f <= z < Sh f + fs_frame_size c / 8) -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by lia; reflexivity.
    rewrite !view_in by lia. unfold rho3. unfold rd_of. rewrite rm_absorb_out; [reflexivity|].
    intros Hin'. apply Hz.
    pose proof (R_sf_ranges c rhoE (Z_to_bv 64 z) f fl Hc SZP eq_refl Efl Esh ltac:(lia) ltac:(lia) ltac:(unfold Sh, SHADOW_OFF in *; lia) Hin') as X.
    cbn zeta in X. rewrite u64_lit in X by lia. exact X. }

  assert (V3 : forall z, 0xf20e0 <= z < 0xf20f8 -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. rewrite !view_in by lia.
    pose proof (cells_ok_nth _ _ 20 _ HR eq_refl) as C20. pose proof (cells_ok_nth _ _ 21 _ HR eq_refl) as C21.
    pose proof (cells_ok_nth _ _ 22 _ HR eq_refl) as C22. unfold cell_ok in C20, C21, C22. cbn [c_addr c_w c_val] in C20, C21, C22.
    unfold cells_in_view, khigh_cells in C4.
    pose proof (Forall_inv C4) as D20. pose proof (Forall_inv (Forall_inv_tail C4)) as D21. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail C4))) as D22.
    cbn [eval] in D20, D21, D22.
    destruct (Z_lt_dec z 0xf20e8); [|destruct (Z_lt_dec z 0xf20f0)].
    - specialize (C20 (Z.to_nat (z - 991456)) ltac:(lia)). specialize (D20 (Z.to_nat (z - 991456)) ltac:(lia)).
      rewrite view_in in C20 by lia. replace (991456 + Z.of_nat (Z.to_nat (z - 991456))) with z in C20 by lia.
      replace (0 + 991456 + Z.of_nat (Z.to_nat (z - 991456))) with z in D20 by lia. rewrite C20, D20. reflexivity.
    - specialize (C21 (Z.to_nat (z - 991464)) ltac:(lia)). specialize (D21 (Z.to_nat (z - 991464)) ltac:(lia)).
      rewrite view_in in C21 by lia. replace (991464 + Z.of_nat (Z.to_nat (z - 991464))) with z in C21 by lia.
      replace (0 + 991464 + Z.of_nat (Z.to_nat (z - 991464))) with z in D21 by lia. rewrite C21, D21. reflexivity.
    - specialize (C22 (Z.to_nat (z - 991472)) ltac:(lia)). specialize (D22 (Z.to_nat (z - 991472)) ltac:(lia)).
      rewrite view_in in C22 by lia. replace (991472 + Z.of_nat (Z.to_nat (z - 991472))) with z in C22 by lia.
      replace (0 + 991472 + Z.of_nat (Z.to_nat (z - 991472))) with z in D22 by lia. rewrite C22, D22. reflexivity. }
  destruct HF as (Flen & Fcls & Fhint & Fflags & Ffree & Fsh).
  fold F vE in Fhint, Fflags, Ffree, Fsh. rewrite FS_frames_off_val, FS_total_val in Fsh.
  assert (Hlenc : (Z.to_nat c < length (aa_fs_busy A))%nat) by (rewrite Flen; lia).
  assert (EBc : forall c0, 0 <= c0 -> fs_busy A' c0 = if c0 =? c then u ++ v else fs_busy A c0).
  { intros c0 Hc0. apply (fs_busy_release A c pos c0 u v); auto; try lia. fold F. rewrite <- Hf. exact Ebusy. }
  assert (EBB : forall c0 p0, 0 <= c0 -> busyb A' c0 p0 = busyb A c0 p0 && negb ((c0 =? c) && (p0 =? pos))).
  { intros c0 p0 Hc0. unfold busyb. rewrite EBc by lia. destruct (Z.eqb_spec c0 c).
    - subst c0. rewrite Ebusy, !existsb_app. cbn [existsb fst andb].
      destruct (Z.eqb_spec p0 pos).
      + subst p0. rewrite Z.eqb_refl. cbn [negb]. rewrite andb_false_r.
        rewrite (existsb_pos_false u pos Hnotin). cbn.
        apply existsb_pos_false. destruct (Fcls c Hc) as [Hnd _]. rewrite Ebusy, map_app in Hnd. cbn in Hnd.
        intros Hv. apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. right. exact Hv.
      + replace (pos =? p0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb]. rewrite andb_true_r. reflexivity.
    - cbn [andb negb]. rewrite andb_true_r. reflexivity. }

  assert (HF' : fs_inv (restrictv (fs_footb (aa_geom A)) v3) A').
  { split; [|split; [|split; [|split; [|split]]]].
    - unfold A', fs_release. cbn [aa_fs_busy]. rewrite length_list_upd. exact Flen.
    - intros c0 Hc0. change (aa_geom A') with (aa_geom A). fold F. rewrite EBc by lia. destruct (Z.eqb_spec c0 c).
      + subst c0. destruct (Fcls c Hc) as [Hnd Hpf]. rewrite Ebusy in Hnd, Hpf. split.
        * rewrite map_app in *. cbn in Hnd. eapply NoDup_remove_1. exact Hnd.
        * intros pf Hpf'. apply Hpf. apply in_app_or in Hpf' as [X|X]; apply in_or_app; [left; exact X | right; right; exact X].
      + exact (Fcls c0 Hc0).
    - change (aa_geom A') with (aa_geom A). fold F. change (aa_fs_hint A') with (aa_fs_hint A).
      destruct Fhint as [Hhl Fhint]. split; [exact Hhl|]. intros c0 Hc0. destruct (Fhint c0 Hc0) as [Hhr Hhc]. split; [exact Hhr|].
      intros k Hk. cbn [c_addr c_w c_val]. specialize (Hhc k Hk). cbn [c_addr c_w c_val] in Hhc. unfold fs_hint_cell in *.
      unfold FS_NCLASSES in Hc0.
      cbn [c_addr c_w c_val] in Hk.
      unfold restrictv in Hhc |- *. rewrite fs_footb_true1 in Hhc by (fold F; lia). rewrite fs_footb_true1 by (fold F; lia).
      rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia). exact Hhc.
    - change (aa_geom A') with (aa_geom A). fold F. intros c0 p0 Hc0 Hp0. rewrite EBB by lia.
      pose proof (fs_geom_nums (aa_geom A) c0 p0 HG Hc0 Hp0) as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. destruct M as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
      unfold restrictv. rewrite fs_footb_true2 by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia).
      destruct (Z.eqb_spec c0 c); [destruct (Z.eqb_spec p0 pos)|].
      + subst c0 p0. cbn [andb negb]. rewrite andb_false_r. fold fl. exact V2.
      + cbn [andb negb]. rewrite andb_true_r.
        assert (fs_flags F c0 + p0 <> fl) by (intros E; destruct (fs_flags_inj F c0 p0 c pos Hc0 Hp0 Hc Hpos E); lia).
        rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia).
        specialize (Fflags c0 p0 Hc0 Hp0). unfold restrictv in Fflags.
        rewrite fs_footb_true2 in Fflags by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). exact Fflags.
      + cbn [andb negb]. rewrite andb_true_r.
        assert (fs_flags F c0 + p0 <> fl) by (intros E; destruct (fs_flags_inj F c0 p0 c pos Hc0 Hp0 Hc Hpos E); lia).
        rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia).
        specialize (Fflags c0 p0 Hc0 Hp0). unfold restrictv in Fflags.
        rewrite fs_footb_true2 in Fflags by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). exact Fflags.
    - change (aa_geom A') with (aa_geom A). fold F. intros c0 p0 Hc0 Hp0 Hfree z Hz. rewrite EBB in Hfree by lia.
      pose proof (fs_geom_nums (aa_geom A) c0 p0 HG Hc0 Hp0) as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. destruct M as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
      unfold restrictv. rewrite fs_footb_true2 by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia).
      destruct (Z.eq_dec c0 c) as [Ec|Nc]; [destruct (Z.eq_dec p0 pos) as [Ep|Np]|].
      + subst c0 p0. rewrite <- Hf in Hz. apply V1. lia.
      + destruct (fs_frames_disjoint F c0 p0 c pos Hc0 Hp0 Hc Hpos ltac:(lia)) as [D|D]; rewrite <- Hf in D;
        rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia);
        (subst c0; replace (p0 =? pos) with false in Hfree by (symmetry; apply Z.eqb_neq; lia); rewrite Z.eqb_refl in Hfree; cbn in Hfree; rewrite andb_true_r in Hfree;
         specialize (Ffree c p0 Hc Hp0 Hfree z Hz); unfold restrictv in Ffree;
         rewrite fs_footb_true2 in Ffree by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia); exact Ffree).
      + destruct (fs_frames_disjoint F c0 p0 c pos Hc0 Hp0 Hc Hpos ltac:(lia)) as [D|D]; rewrite <- Hf in D;
        rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia);
        (replace (c0 =? c) with false in Hfree by (symmetry; apply Z.eqb_neq; lia); cbn in Hfree; rewrite andb_true_r in Hfree;
         specialize (Ffree c0 p0 Hc0 Hp0 Hfree z Hz); unfold restrictv in Ffree;
         rewrite fs_footb_true2 in Ffree by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia); exact Ffree).
    - change (aa_geom A') with (aa_geom A). fold F. rewrite FS_frames_off_val, FS_total_val. intros z Hz.
      unfold restrictv. rewrite fs_footb_true3 by (fold F; rewrite FS_frames_off_val, FS_total_val; lia).
      destruct (Z_le_dec (Sh f) z); [destruct (Z_lt_dec z (Sh f + fs_frame_size c / 8))|].
      1: apply V4; lia.
      all: rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia); specialize (Fsh z Hz); unfold restrictv in Fsh;
           rewrite fs_footb_true3 in Fsh by (fold F; rewrite FS_frames_off_val, FS_total_val; lia); exact Fsh. }
  assert (HA' : AInv A' rho3 tp md).
  { apply (AInvA_fs_update segs A A' rhoE rho3 tp md HA).
    - unfold A', fs_release, same_but_fs. cbn. repeat split; reflexivity.
    - intros z Hz. fold v3 vE.
      destruct (Z_le_dec 0xf20e0 z); [destruct (Z_lt_dec z 0xf20f8)|]; [apply V3; lia| |];
      apply V5; intros [X|[X|[X|X]]]; try lia;
      try (rewrite fs_footb_true2 in Hz by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia); discriminate);
      try (rewrite fs_footb_true3 in Hz by (fold F; rewrite FS_frames_off_val, FS_total_val; lia); discriminate).
    - exact HF'. }
  exists A', l1, l2.
  split; [exact HA'|]. split; [reflexivity|]. split; [exact E1|]. split; [unfold aa_frames; rewrite EB'; exact E2|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].

  assert (FRAME' : forall f' s', In (f', s') (aa_frames A') ->
            exists c' p', 0 <= c' < 11 /\ 0 <= p' < fs_num_iter c' /\ s' = fs_frame_size c' /\ f' = fs_frame F c' p'
                          /\ (c' <> c \/ p' <> pos) /\ frame_flag (aa_geom A) (f', s') = fs_flags F c' + p').
  { intros f' s' Hin'. destruct (aa_frames_fact _ A' _ _ HF' Hin') as (c' & p' & u' & v' & Hc'' & Hs' & Eb' & Hn' & Hp' & Hf' & _).
    change (aa_geom A') with (aa_geom A) in Hf'. fold F in Hf'.
    exists c', p'. split; [exact Hc''|]. split; [exact Hp'|]. split; [exact Hs'|]. split; [exact Hf'|]. split.
    - destruct (Z.eq_dec c' c) as [->|]; [|left; assumption]. right. intros ->.
      rewrite EBc in Eb' by lia. rewrite Z.eqb_refl in Eb'.
      destruct (Fcls c Hc) as [Hnd _]. rewrite Ebusy, map_app in Hnd. cbn in Hnd. apply NoDup_remove_2 in Hnd. apply Hnd.
      rewrite <- map_app, Eb', map_app. cbn. apply in_or_app. right. left. reflexivity.
    - unfold frame_flag. cbn [fst snd]. unfold fs_flag_addr. rewrite Hs', fs_class_of_size_ok by lia. fold F.
      rewrite Hf', fs_pos_frame by lia. reflexivity. }
  destruct HRest as (Hsep & _).
  assert (NOCL : forall x, f <= x < f + fs_frame_size c -> ~ client_addrA CST A' x).
  { intros x Hx [[S|[L|[FR|C]]]|FL].
    - change (aa_geom A') with (aa_geom A) in S. lia.
    - destruct L as (b & n & Hbn & Hx'). change (aa_live A') with (aa_live A) in Hbn.
      destruct (Hsep b n Hbn) as (S1 & S2 & S3 & S4 & _). fold F in S4. rewrite FS_total_val in S4. unfold IMG_HI in S2. lia.
    - destruct FR as (f' & s' & Hin' & Hx'). destruct (FRAME' f' s' Hin') as (c' & p' & Hc'' & Hp' & -> & -> & Hne & _).
      destruct (fs_frames_disjoint F c' p' c pos Hc'' Hp' Hc Hpos Hne) as [D|D]; rewrite <- Hf in D; [lia|].
      pose proof (fs_frame_size_pos c' ltac:(lia)). lia.
    - destruct (HCST x C) as [X _]. unfold IMG_LO, IMG_HI in X. lia.
    - destruct FL as ([f' s'] & Hin' & Ex). destruct (FRAME' f' s' Hin') as (c' & p' & Hc'' & Hp' & -> & -> & Hne & E').
      change (aa_geom A') with (aa_geom A) in Ex. rewrite E' in Ex. subst x.
      pose proof (fs_geom_nums (aa_geom A) c' p' HG Hc'' Hp') as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. repeat match goal with H : context [ag_fsb (aa_geom A)] |- _ => fold F in H end. lia. }
  assert (CLB : forall AA_ x, aa_live AA_ = aa_live A -> (forall f' s', In (f', s') (aa_frames AA_) -> In (f', s') (aa_frames A) \/ In (f', s') (aa_frames A')) ->
                aa_geom AA_ = aa_geom A -> client_addrA CST AA_ x -> 0 <= x < 2 ^ 47 /\ (x < 2147446784 \/ 17594333495296 <= x)).
  { unfold IMG_HI. intros AA_ x HL HFR HGe [[S|[L|[FR|C]]]|FL].
    - rewrite HGe in S. lia.
    - destruct L as (b & n & Hbn & Hx'). rewrite HL in Hbn. destruct (Hsep b n Hbn) as (S1 & S2 & S3 & S4 & _ & _ & _ & S8). fold F in S4. rewrite FS_total_val in S4. unfold IMG_HI in S2.
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in S8. lia.
    - destruct FR as (f' & s' & Hin' & Hx').
      assert (FS : exists c' p', 0 <= c' < 11 /\ 0 <= p' < fs_num_iter c' /\ s' = fs_frame_size c' /\ f' = fs_frame F c' p').
      { destruct (HFR _ _ Hin') as [I|I].
        - destruct (aa_frames_fact _ A _ _ (conj Flen (conj Fcls (conj Fhint (conj Fflags (conj Ffree Fsh))))) I) as (c' & p' & ? & ? & Hc'' & Hs' & _ & _ & Hp' & Hf' & _). exists c', p'. auto.
        - destruct (FRAME' _ _ I) as (c' & p' & Hc'' & Hp' & Hs' & Hf' & _). exists c', p'. auto. }
      destruct FS as (c' & p' & Hc'' & Hp' & -> & ->).
      pose proof (fs_geom_nums (aa_geom A) c' p' HG Hc'' Hp') as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. repeat match goal with H : context [ag_fsb (aa_geom A)] |- _ => fold F in H end. lia.
    - destruct (HCST x C) as [X _]. unfold IMG_LO, IMG_HI in X. lia.
    - destruct FL as ([f' s'] & Hin' & Ex). rewrite HGe in Ex. subst x.
      assert (FS : exists c' p', 0 <= c' < 11 /\ 0 <= p' < fs_num_iter c' /\ s' = fs_frame_size c' /\ f' = fs_frame F c' p').
      { destruct (HFR _ _ Hin') as [I|I].
        - destruct (aa_frames_fact _ A _ _ (conj Flen (conj Fcls (conj Fhint (conj Fflags (conj Ffree Fsh))))) I) as (c' & p' & ? & ? & Hc'' & Hs' & _ & _ & Hp' & Hf' & _). exists c', p'. auto.
        - destruct (FRAME' _ _ I) as (c' & p' & Hc'' & Hp' & Hs' & Hf' & _). exists c', p'. auto. }
      destruct FS as (c' & p' & Hc'' & Hp' & -> & ->).
      unfold frame_flag. cbn [fst snd]. unfold fs_flag_addr. rewrite fs_class_of_size_ok by lia. fold F. rewrite fs_pos_frame by lia.
      pose proof (fs_geom_nums (aa_geom A) c' p' HG Hc'' Hp') as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. repeat match goal with H : context [ag_fsb (aa_geom A)] |- _ => fold F in H end. lia. }
  assert (SHB : forall x, 0 <= x < 2 ^ 47 -> 0x7fff8000 <= Sh x < 17594333495296) by (intros x Hx; unfold Sh, SHADOW_OFF; lia).
  assert (CSH : forall AA_ a, aa_live AA_ = aa_live A -> (forall f' s', In (f', s') (aa_frames AA_) -> In (f', s') (aa_frames A) \/ In (f', s') (aa_frames A')) ->
                aa_geom AA_ = aa_geom A -> client_shadowA CST XGL AA_ a -> 0x7fff8000 <= a < 17594333495296).
  { intros AA_ a HL HFR HGe [(x & Hx & ->)|(x & Hx & ->)]; apply SHB; [eapply (fun h => proj1 (CLB AA_ x HL HFR HGe h)); eauto|].
    destruct (HXGL x Hx). unfold IMG_HI in *. lia. }
  assert (AFR0 : forall f' s', In (f', s') (aa_frames A) -> In (f', s') (aa_frames A) \/ In (f', s') (aa_frames A')) by (intros; left; assumption).
  split.
  2:{
    intros x j Hx Hj Hdef.
    assert (Bx : 0 <= x < 2 ^ 47).
    { destruct Hx as [[C1 C2]|GX]; [exact (proj1 (CLB A x eq_refl AFR0 eq_refl C1)) | destruct (HXGL x GX); unfold IMG_HI in *; lia]. }
    pose proof (SHB x Bx) as SB.
    destruct (word_byte_range (Sh x) j ltac:(lia) Hj) as (W1 & W2 & W3).
    set (a := word_byte (Sh x) j) in *.
    destruct (in_ranges_dec rhoE (R_sf c) a) as [Hi|Hn]; [| unfold rho3; rewrite rm_absorb_out by exact Hn; exact Hdef].
    pose proof (R_sf_ranges c rhoE a f fl Hc SZP eq_refl Efl Esh ltac:(lia) ltac:(lia) ltac:(unfold Sh, SHADOW_OFF in *; lia) Hi) as X.
    cbn zeta in X. rewrite W2 in X.
    assert (SA : (Sh x / 8 * 8) mod 8 = 0) by (apply Z_mod_mult).
    destruct X as [X|[X|[X|X]]]; try (exfalso; unfold Sh, SHADOW_OFF in *; lia).
    destruct (V4 (Sh x / 8 * 8 + j) X) as [y Hy]. unfold v3 in Hy. rewrite view_in in Hy by exact W1.
    assert (BND : 0x646000 <= Sh x / 8 * 8 + j < 2 ^ 64) by (clear -SB W1 W3 Hj; lia).
    pose proof (rd_off_image (rm rho3) _ _ BND Hy) as M. rewrite <- W2, Z_to_bv_bv_unsigned in M.
    rewrite M. discriminate. }
  intros a Ha Hcl.
  destruct (in_ranges_dec rhoE (R_sf c) (Z_to_bv 64 a)) as [Hi|Hn]; [| unfold rho3; apply rm_absorb_out; exact Hn].
  exfalso.
  pose proof (R_sf_ranges c rhoE (Z_to_bv 64 a) f fl Hc SZP eq_refl Efl Esh ltac:(lia) ltac:(lia) ltac:(unfold Sh, SHADOW_OFF in *; lia) Hi) as X.
  cbn zeta in X. rewrite u64_lit in X by lia.
  assert (AFR : forall f' s', In (f', s') (aa_frames A) -> In (f', s') (aa_frames A) \/ In (f', s') (aa_frames A')) by (intros; left; assumption).
  assert (AFR' : forall f' s', In (f', s') (aa_frames A') -> In (f', s') (aa_frames A) \/ In (f', s') (aa_frames A')) by (intros; right; assumption).
  destruct X as [X|[X|[X|X]]].
  -
    destruct Hcl as [(_ & C' & _)|(C1 & C2 & _)]; [exact (NOCL a X C')|].
    pose proof (CSH A' a eq_refl AFR' eq_refl C2). lia.
  -
    subst a. destruct Hcl as [(_ & C' & _)|(C1 & C2 & _)].
    + destruct C' as [[S|[L|[FR|C]]]|FL].
      * change (aa_geom A') with (aa_geom A) in S. lia.
      * destruct L as (b & n & Hbn & Hx'). change (aa_live A') with (aa_live A) in Hbn. destruct (Hsep b n Hbn) as (S1 & S2 & S3 & S4 & _). fold F in S4. rewrite FS_total_val in S4. unfold IMG_HI in S2. lia.
      * destruct FR as (f' & s' & Hin' & Hx'). destruct (FRAME' f' s' Hin') as (c' & p' & Hc'' & Hp' & -> & -> & Hne & _).
        pose proof (fs_geom_nums (aa_geom A) c' p' HG Hc'' Hp') as M. cbn zeta in M. fold F in M.
        rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. repeat match goal with H : context [ag_fsb (aa_geom A)] |- _ => fold F in H end. lia.
      * destruct (HCST _ C) as [Y _]. unfold IMG_LO, IMG_HI in Y. lia.
      * destruct FL as ([f' s'] & Hin' & E). destruct (FRAME' f' s' Hin') as (c' & p' & Hc'' & Hp' & -> & -> & Hne & E').
        change (aa_geom A') with (aa_geom A) in E. rewrite E' in E. unfold fl in E. destruct (fs_flags_inj F c' p' c pos Hc'' Hp' Hc Hpos ltac:(lia)). lia.
    + pose proof (CSH A' _ eq_refl AFR' eq_refl C2). lia.
  -
    destruct Hcl as [(C' & _)|(C1 & C2 & _)].
    + destruct C' as [[S|[L|[FR|C]]]|FL].
      * lia.
      * destruct L as (b & n & Hbn & Hx'). destruct (Hsep b n Hbn) as (S1 & S2 & S3 & S4 & _). fold F in S4. rewrite FS_total_val in S4. unfold IMG_HI in S2. lia.
      * destruct FR as (f' & s' & Hin' & Hx').
        destruct (aa_frames_fact _ A _ _ (conj Flen (conj Fcls (conj Fhint (conj Fflags (conj Ffree Fsh))))) Hin') as (c' & p' & ? & ? & Hc'' & -> & _ & _ & Hp' & -> & _).
        pose proof (fs_geom_nums (aa_geom A) c' p' HG Hc'' Hp') as M. cbn zeta in M. fold F in M.
        rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. repeat match goal with H : context [ag_fsb (aa_geom A)] |- _ => fold F in H end. lia.
      * destruct (HCST _ C) as [_ Y].
        assert (Y' : cells_footb (rtc_cells_img RTC_A G0) a = true); [|rewrite Y' in Y; discriminate].
        unfold cells_footb. apply existsb_exists.
        destruct (Z_lt_dec a 0xf20e8); [|destruct (Z_lt_dec a 0xf20f0)].
        -- exists (mkACell 0xf20e0 8 K_HIGH_MEM_END). split; [ first [ solve [ cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity ] | cbn; tauto ] |]. unfold in_cellb. cbn [c_addr c_w Z.of_nat]. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
        -- exists (mkACell 0xf20e8 8 0). split; [ first [ solve [ cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity ] | cbn; tauto ] |]. unfold in_cellb. cbn [c_addr c_w Z.of_nat]. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
        -- exists (mkACell 0xf20f0 8 0). split; [ first [ solve [ cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity ] | cbn; tauto ] |]. unfold in_cellb. cbn [c_addr c_w Z.of_nat]. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
      * destruct FL as ([f' s'] & Hin' & E).
        destruct (aa_frames_fact _ A _ _ (conj Flen (conj Fcls (conj Fhint (conj Fflags (conj Ffree Fsh))))) Hin') as (c' & p' & ? & ? & Hc'' & Es & _ & _ & Hp' & Ef & _).
        unfold frame_flag in E. cbn [fst snd] in E. unfold fs_flag_addr in E. rewrite Es, fs_class_of_size_ok in E by lia. fold F in E.
        rewrite Ef, fs_pos_frame in E by lia.
        pose proof (fs_geom_nums (aa_geom A) c' p' HG Hc'' Hp') as M. cbn zeta in M. fold F in M.
        rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. repeat match goal with H : context [ag_fsb (aa_geom A)] |- _ => fold F in H end. lia.
    + pose proof (CSH A _ eq_refl AFR eq_refl C1). lia.
  -
    destruct Hcl as [(_ & C' & _)|(C1 & C2 & _)].
    + pose proof (CLB A' a eq_refl AFR' eq_refl C'). unfold Sh, SHADOW_OFF, IMG_HI in *. lia.
    + destruct C2 as [(x & Cx & Ex)|(x & Gx & Ex)].
      * pose proof (CLB A' x eq_refl AFR' eq_refl Cx) as Bx.
        assert (f <= x < f + fs_frame_size c).
        { subst a. unfold Sh in X.
          pose proof (Z.div_mod f 8). pose proof (Z.div_mod x 8). pose proof (Z.mod_pos_bound x 8). pose proof (Z.mod_pos_bound f 8).
          assert (f mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply (Z.divide_trans _ 64); [exists 8; reflexivity| apply Z.mod_divide; lia]).
          split; [nia|].
          destruct (Z_lt_dec x (f + fs_frame_size c)); [lia|].
          assert ((f + fs_frame_size c) / 8 <= x / 8) by (apply Z.div_le_mono; lia).
          replace f with (f / 8 * 8) in H4 at 1 by lia. rewrite Z.div_add_l in H4 by lia. lia. }
        exact (NOCL x H Cx).
      * destruct (HXGL x Gx). unfold IMG_HI in *. subst a. unfold Sh, SHADOW_OFF in X. lia.
Qed.

Lemma sf_reabstract : ltac2:(tb__ "0|1|
S3S0S49S25S14S6S63Q40A1A1S7cS14SfS3fZ0R7A2S3eR7ZbA2A2SeS3S6bS6cS77R9R8A2S2S7S15S15A2A1S33A3S26S24R8A2S76R9R8A2A3S4A3SeS3S83S76RaR9A2S66A2S4A3S70Vsegs;S48S14S1dS52S75R8A1R1A3Lr;VJ;RaR9R8A3A2S55S24RbRaA3R4R6R5A6S6fVsegs;S66R8R7S1S7S6aS6eA2M0S9S6aS6eS26S24RbA2S28VAInv;VCST;VXGL;RbRaR9A6A4S2G0A1A3R6A6F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;Fc;Fhi;").
Proof.
  intros hi c A Kc rho tp w rhoE Hc Hent Hid H.
  destruct w as [tr [ms md]]. destruct H as [HsmA [Hag HJ]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct HJ as (HA & HK & Htp & Hin & Hfl & Htop).

  assert (Ha : SPA segs (J_T Kc) (mkAX (st2x hi c) [] base_sv) rhoE tp (tr, mkCfg ms md)).
  { change (mkAX (st2x hi c) [] base_sv) with
      (ax_setS (Post_sf AE_A hi c) (set_objs (ax_S (Post_sf AE_A hi c)) (select (ss_objs (ax_S (Post_sf AE_A hi c))) idxs_sf))).
    apply SPA_select; [split; [exact HsmA | exact HK] | reflexivity | |].
    - intros i Hi. cbn in Hi. cbn. intuition lia.
    - intros i Hi. cbn in Hi. cbn. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%nat by lia. intuition lia. }

  pose proof (SPA_unobj segs (J_T Kc) rhoE (mkAX (st2x hi c) [] base_sv) [stack_win; O_got; O_rtc] (R_sf c) tp tr ms md
                eq_refl Ha (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho3 := rho_absorb rhoE (R_sf c) (vms md tp ms)) in Hb.
  change (ax_setS (mkAX (st2x hi c) [] base_sv) (set_objs (ax_S (mkAX (st2x hi c) [] base_sv)) [stack_win; O_got; O_rtc]))
    with (mkAX (st3 hi c) [] base_sv) in Hb.

  pose proof (smatchA_entails segs _ _ _ rho3 tp _ Hent (proj1 Hb)) as Hc3.
  set (rho4 := rho_sub rho3 (s_sf hi c)) in Hc3.

  exists (L_stack_free AE_A c), (JL_stack_free AInv CST XGL c A Kc), rho4, tp.
  split; [left; reflexivity|]. split; [|split; [exact Hc3|]].
  {
    pose proof (rho_sub_agree (s_sf hi c) NF rho3 Hid) as Hag4. fold rho4 in Hag4.
    destruct Hag as (Hagw & Hagl & _). destruct Hag4 as (H4w & H4l & _).
    split.
    - intros i Hi. rewrite <- H4w by exact Hi. unfold rho3. cbn [rho_absorb rw].
      rewrite <- Hagw by (unfold GW, NF in *; lia). unfold rho1_of. rewrite rho_set_rw_other; [reflexivity|]. unfold vG, NF in *. lia.
    - intros l. rewrite <- H4l. unfold rho3. cbn [rho_absorb rl]. rewrite <- Hagl. reflexivity. }
  cbn [w_tr w_cfg cfg_model fst snd].
  destruct Hag as (Hagw & Hagl & Hagm).
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive).
  { rewrite <- Hagw by (unfold GW; lia). unfold rho1_of. rewrite rho_set_rw_other; [reflexivity|]. unfold vG. lia. }
  assert (EvG : rw rhoE vG = Z_to_bv 64 (bv_unsigned (rw rhoE 12%positive) / 8)).
  { rewrite <- Hagw by (unfold GW, vG; lia). unfold rho1_of. rewrite rho_set_rw_at, E12. reflexivity. }
  pose proof (proj1 (proj1 Ha)) as Hsm2. unfold virt in Hsm2. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm2.
  destruct (sf_rebuild hi c A rhoE tp tr ms md Hc HA Hin Hfl EvG Hsm2) as (A' & l1 & l2 & HA' & HL & E1 & E2 & HV & HKm & HKf & HGe & KEPT).
  fold rho3 in HA', KEPT.
  exists A', l1, l2.
  split; [unfold AInv, AInvA in *; exact HA'|].
  split; [exact HL|]. split; [rewrite <- E12; exact E1|]. split; [exact E2|].
  split; [exact HV|]. split; [exact HKm|]. split; [exact HKf|]. split; [exact HGe|].
  split; [|split; [exact HK | reflexivity]].
  destruct KEPT as [KEPT KEPTW]. split.
  - intros a Ha0 Hcl. unfold rho4. cbn [rho_sub rm]. rewrite (KEPT a Ha0); [rewrite <- Hagm; reflexivity|].
    destruct Hcl as [H|(S1 & S2 & D)]; [left; exact H | right; split; [exact S1 | split; [exact S2 | rewrite <- Hagm; exact D]]].
  - intros x j Hx Hj Hdef. unfold rho4. cbn [rho_sub rm]. apply (KEPTW x j Hx Hj). rewrite <- Hagm. exact Hdef.
Qed.

Lemma J_stableA : ltac2:(tb__ "0|0|
S0S49S25S29R1A1S72Vsegs;S52VJ;R4R3R2A3A3F_;FKc;FA;Fc;").
Proof.
  intros c A Kc HKc rho rho' tp tr md md' Hag Hme (HA & HK & Htp & Hin & Hfl & Htop).
  destruct Hag as (Hw & Hl & Hm).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  assert (E12 : rw rho' 12%positive = rw rho 12%positive) by (symmetry; apply Hw; unfold GW; lia).
  assert (E24 : rw rho' 24%positive = rw rho 24%positive) by (symmetry; apply Hw; unfold GW; lia).
  assert (E16 : rw rho' V_FL = rw rho V_FL) by (symmetry; apply Hw; unfold GW, V_FL; lia).
  assert (E10 : rw rho' 10%positive = rw rho 10%positive) by (symmetry; apply Hw; unfold GW; lia).
  assert (E15 : rw rho' V_DEPTH = rw rho V_DEPTH) by (symmetry; apply Hw; unfold GW, V_DEPTH; lia).
  split; [|split; [|split; [|split; [|split; [|unfold top_high; rewrite E10, E15; exact Htop]]]]].
  - apply (AInvA_mat segs A rho' tp md md'); [|exact Hme]. unfold AInv, AInvA in *. rewrite Erm. exact HA.
  - destruct Hme as ((mat' & ->) & _). rewrite with_vm_backing_with_vm. apply HKc. exact HK.
  - unfold tp_ok in *. rewrite E24. exact Htp.
  - rewrite E12. exact Hin.
  - rewrite E16, E12. exact Hfl.
Qed.

Definition sf_checks (hi : bool) (c : Z) : bool := ltac2:(tb__ "0|1|
SaSaSaSaSaS1bS79Vc;A1A1S1bS7aVc;A1A1A2S80S1eS1fS53A1S54Vhi;Vc;A2A3A2S6bS6cS77Vhi;Vc;A2S2S7S15S15A2A1S33A3S26S24Vc;A2S76Vhi;Vc;A2M0A3A2S83G0S66A2A2S47Vsegs;U190S2S0A1S52S5aVhi;Vc;A2S5bVhi;Vc;A2A6A2").

Lemma sf_checks_5 : ltac2:(tb__ "0|0|
S3SeS3S73R1Z5A2S4A3Fhi;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sf_checks_6 : ltac2:(tb__ "0|0|
S3SeS3S73R1Z6A2S4A3Fhi;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem stack_free_contract : ltac2:(tb__ "0|1|
S0S3SeS3S73R1R2A2S4A3Fhi;SfS3fZ0R2A2S3eR2ZbA2A2S7cOF_;S49S25S14S6S63Q40A1A1S29R3A1S71Vsegs;R6S3aVAInv;R9R5R4A4A3S7eVsegs;R7S70Vsegs;VJ;RaR6R5A3S2aS24RaA2R4R3A5S6fVsegs;S66R4R3S1S7S6aS6eA2M0S9S6aS6eS26S24RaA2S28VAInv;VCST;VXGL;RaR6R5A6A4S2G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;F_;F_;Fc;").
Proof.
  intros c CFh Hc ok A Kc rho tp HKc Hokf0.
  assert (Hokf : ok_frameA segs ok (J c A Kc)).
  { apply (ok_frameA_stack_free_T segs AInv); [|exact Hokf0]. intros A0 r r' t m H E. unfold AInv, AInvA in *. rewrite E. exact H. }

  apply (triple_by_pure _ _ (exists hi, win_hyp hi (ag_fsb (aa_geom A)) FS_total));
    [intros w [_ (HA & _)]; exact (win_hyp_cases _ _ (proj1 (geom_bands _ (proj1 HA)))) | intros [hi Hwin]].
  specialize (CFh hi). rename CFh into CF.
  unfold sf_checks in CF. repeat (apply andb_prop in CF; destruct CF as [CF ?]).
  rename CF into W1. rename H3 into W2. rename H2 into FB. rename H1 into ENT. rename H0 into WID. rename H into CERT.
  eapply triple_conseq; [intros w' Hw; exact (sf_instantiate hi c A Kc rho tp w' Hc W1 W2 FB Hwin Hw) | intros w' Hw; exact Hw |].
  eapply triple_conseq; [intros w' Hw; exact (SPA_withG_intro segs _ GW (Pre_sf AE_A hi c) (rho1_of rho) tp w' Hw) | intros w' Hw; exact Hw |].
  apply (cfg_soundA segs 400%nat [] GW (cuts_sf hi c) (exits_sf hi c) (withGA (fun r => agree_below GW (rho1_of rho) r) (J c A Kc)) ok
           (LQPA segs NF rho tp [(L_stack_free AE_A c, JL_stack_free AInv CST XGL c A Kc)]) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hokf; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply J_stableA; exact HKc].
  - exact CERT.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [| intros w' Hw; exact Hw | apply triple_refl].
    intros w' Hw. right. exact (sf_reabstract hi c A Kc rho tp w' rhoE Hc ENT WID Hw).
  - left. reflexivity.
Qed.

Theorem stack_free_contract_5 : ltac2:(tb__ "0|0|
S2bVsegs;S24VAInv;VCST;VXGL;Z5A6").
Proof. apply stack_free_contractA_of_T. apply stack_free_contract; [exact sf_checks_5 | lia]. Qed.
Theorem stack_free_contract_6 : ltac2:(tb__ "0|0|
S2bVsegs;S24VAInv;VCST;VXGL;Z6A6").
Proof. apply stack_free_contractA_of_T. apply stack_free_contract; [exact sf_checks_6 | lia]. Qed.

Lemma sf_echeck_5 : ltac2:(tb__ "0|4|
S3SeS3S46Vsegs;U190S2S0A1S52S1S44S45S56S24R1Z5M0A3Z1S18Z0M1A1M2A3S2S44A1M3A3S1S44S45S55S24R1G0A3G1G2A3G3A3A6S4A3Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sf_echeck_6 : ltac2:(tb__ "0|4|
S3SeS3S46Vsegs;U190S2S0A1S52S1S44S45S56S24R1Z6M0A3Z1S18Z0M1A1M2A3S2S44A1M3A3S1S44S45S55S24R1G0A3G1G2A3G3A3A6S4A3Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem stack_free_contract_ex : ltac2:(tb__ "0|4|
S0S3SeS3S73R1R2A2S4A3Fhi;S3SeS3S46Vsegs;U190S2S0A1S52S1S44S45S56S24R1R3A3Z1S18Z0M0A1M1A3S2S44A1M2A3S1S44S45S55S24R1R3A3G0G1A3G2A3A6S4A3Fhi;SfS3fG0R3A2S3eR3ZbA2A2S49S25S14S6S63Q40A1A1S29R3A1S7dVsegs;S70Vsegs;VJ;R9R5R4A3S2aS24R9A2R3R2A5S6fVsegs;S66R3R2S1S7S6aS6eA2M3S9S6aS6eS26S24R9A2S28VAInv;VCST;VXGL;R9R5R4A6A4S2G3A1A3A5A3F_;Ftp;Frho;FKc;FA;F_;F_;F_;Fc;").
Proof.
  intros c CFh CEh Hc A Kc rho tp HKc.
  apply (etriple_by_pure _ (exists hi, win_hyp hi (ag_fsb (aa_geom A)) FS_total));
    [intros w [_ (HA & _)]; exact (win_hyp_cases _ _ (proj1 (geom_bands _ (proj1 HA)))) | intros [hi Hwin]].
  specialize (CFh hi). rename CFh into CF. specialize (CEh hi). rename CEh into CE.
  unfold sf_checks in CF. repeat (apply andb_prop in CF; destruct CF as [CF ?]).
  rename CF into W1. rename H3 into W2. rename H2 into FB. rename H1 into ENT. rename H0 into WID. clear H.
  eapply etriple_conseq; [intros w' Hw; exact (sf_instantiate hi c A Kc rho tp w' Hc W1 W2 FB Hwin Hw) | intros w' Hw; exact Hw |].
  eapply etriple_conseq; [intros w' Hw; exact (SPA_withG_intro segs _ GW (Pre_sf AE_A hi c) (rho1_of rho) tp w' Hw) | intros w' Hw; exact Hw |].
  change (Pre_sf AE_A hi c) with (vna_state (mkVNA (Pre_sf AE_A hi c) 1 (SLit 0))).
  apply (cfg_complete_autoA segs 400%nat [] GW [mkVNA (Pre_sf AE_A hi c) 1 (SLit 0)] [mkVNA (Post_sf AE_A hi c) 0 (SLit 0)]
           (withGA (fun r => agree_below GW (rho1_of rho) r) (J c A Kc))
           (LQPA segs NF rho tp [(L_stack_free AE_A c, JL_stack_free AInv CST XGL c A Kc)]) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply J_stableA; exact HKc].
  - intros n [<-|[]]. cbv; congruence.
  - exact CE.
  - intros E rhoE [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [| intros w' Hw; exact Hw | apply etriple_refl].
    intros w' Hw. right. exact (sf_reabstract hi c A Kc rho tp w' rhoE Hc ENT WID Hw).
  - left. reflexivity.
Qed.

Theorem stack_free_contract_ex_5 : ltac2:(tb__ "0|0|
S2cVsegs;S24VAInv;VCST;VXGL;Z5A6").
Proof. apply stack_free_contractA_ex_of_T. apply stack_free_contract_ex; [exact sf_checks_5 | exact sf_echeck_5 | lia]. Qed.
Theorem stack_free_contract_ex_6 : ltac2:(tb__ "0|0|
S2cVsegs;S24VAInv;VCST;VXGL;Z6A6").
Proof. apply stack_free_contractA_ex_of_T. apply stack_free_contract_ex; [exact sf_checks_6 | exact sf_echeck_6 | lia]. Qed.

Theorem stack_free_contracts : ltac2:(tb__ "0|0|
S0S7fS0R1S1S0Z5S1S0Z6S2S0A1A3A3A3S2bVsegs;S24VAInv;VCST;VXGL;R2A6F_;Fc;").
Proof. intros c Hin. cbn in Hin. destruct Hin as [<-|[<-|[]]]; [apply stack_free_contract_5 | apply stack_free_contract_6]. Qed.
Theorem stack_free_contracts_ex : ltac2:(tb__ "0|0|
S0S7fS0R1S1S0Z5S1S0Z6S2S0A1A3A3A3S2cVsegs;S24VAInv;VCST;VXGL;R2A6F_;Fc;").
Proof. intros c Hin. cbn in Hin. destruct Hin as [<-|[<-|[]]]; [apply stack_free_contract_ex_5 | apply stack_free_contract_ex_6]. Qed.
End SF.
