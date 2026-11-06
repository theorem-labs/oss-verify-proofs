(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec FPA_asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import SumsAsanSpecs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import
  AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanInit
  AsanNodesMmLib AsanNodesMmA AsanNodesMmB AsanPlanImages SumsAsanClose AsanNodesStartX AsanNodesStartXInit
  AsanNodesArg AsanNodesArgAsan AsanNodesIO AsanNodesIOInit AsanNodesFX AsanNodesFSoundG FContractAsan
  AsanNodesDepot AsanNodesDepotAsan AsanMainLib AsanShape
  AsanNodesRP AsanNodesRPSoundG AsanNodesRPAsan AsanNodesPG AsanNodesPGSoundG AsanNodesPGAsan AsanNodesK1 AsanNodesK1SoundG AsanNodesK1Asan AsanNodesUG AsanNodesUGAsan AsanNodesLC AsanNodesLCTab AsanNodesLCAsan
  AsanNodesHS AsanNodesSD AsanNodesIOSound
  StartupHooks StartupPlanAsan StartupHSAsan PostPlanAsan StartupHSMainAsan AsanStartupCert AsanPostCert AsanStartupE
  MainGlueDefs MainGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

#[local] Notation LIM := target_alloc_limit.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section MCE.
  (* [comment removed for export] *)
  Hypothesis FCA : F_contract_asan ASEGS FPA_asan.

  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable urnd : InputStream.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  #[local] Notation c := (content_of argv fs).
  #[local] Notation SINV := (SINVm APH sp rdraw brk0 argv envp uid hw (content_of argv fs)).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).

  Lemma mc_AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. exact (argH0_high APH sp rdraw argv envp uid hw Hsp Hva E a H). Qed.
  Lemma mc_AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Proof. intros E E' a H. exact (argH0_agree APH sp rdraw argv envp uid hw E E' a H). Qed.
  Lemma mc_SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros. eapply SINVm_frame; eassumption. Qed.
  Lemma mc_SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros. eapply SINVm_agree; eassumption. Qed.
  Lemma mc_S0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
  Proof. intros E M H. eapply SINVm_SINV0. exact H. Qed.
  Lemma mc_AT : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a HS Ha. pose proof (mc_S0 E M HS) as H0. eapply argH0_top; eauto. Qed.
  Lemma mc_S1 : forall E M, SINV E M -> SINV1 sp brk0 argv envp rdraw uid hw E M.
  Proof.
    intros E M HS. pose proof (mc_S0 E M HS) as H0. destruct HS as (_ & H1 & H2 & _).
    split; [exact H0 | split; assumption].
  Qed.

  Lemma mc_hull_okP : AsanPlanSoundSums.APSX.hull_okP ASAN.
  Proof. exact asan_hull_ok. Qed.
  Create HintDb asanimgm.
  Hint Resolve asan_wx asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_nx0_ok asan_hull_res asan_segs_wr
               mc_AH mc_AA mc_SF mc_SA mc_AT mc_hull_okP FCA : asanimgm.

  (* [comment removed for export] *)
  Lemma mc_sys : forall y, sys_stmt ASEGS ASAN NX0 LIM SINV argH fs y.
  Proof. intros y. eapply AsanNodesMmB.node_sys_sound; eauto with asanimgm. Qed.
  Lemma mc_brk2 : brk2_stmt ASEGS ASAN NX0 LIM SINV argH fs.
  Proof. eapply AsanNodesMmB.node_brk2_sound; eauto with asanimgm. Qed.
  Lemma mc_brk2s : brk2s_stmt ASEGS ASAN NX0 LIM SINV argH fs.
  Proof. eapply AsanNodesMmB.node_brk2s_sound; eauto with asanimgm. Qed.
  Lemma mc_mmap2 : mm2_stmt ASEGS ASAN NX0 LIM SINV argH fs (node_mmap2 ASAN NX0 LIM).
  Proof. eapply AsanNodesMmA.node_mmap2_sound_OBL; eauto with asanimgm. Qed.
  Lemma mc_mmapin : forall hole : bool, mm3_stmt ASEGS ASAN NX0 LIM SINV argH fs (node_mmapin ASAN LIM hole).
  Proof. intros hole. eapply AsanNodesMmA.node_mmapin_sound_OBL; eauto with asanimgm. Qed.
  Lemma mc_mprotect2 : mm2_stmt ASEGS ASAN NX0 LIM SINV argH fs (node_mprotect2 ASAN LIM).
  Proof. eapply AsanNodesMmA.node_mprotect2_sound_OBL; eauto with asanimgm. Qed.
  Lemma mc_exit : exit_stmt ASEGS ASAN LIM SINV argH fs.
  Proof. eapply AsanNodesMmB.node_exit_sound; eauto with asanimgm. Qed.
  Lemma mc_join : join_stmt ASEGS ASAN NX0 LIM SINV argH fs.
  Proof. eapply AsanPlanSound2.node_join_sound; eauto with asanimgm. Qed.
  Lemma mc_join_ok : join_ok_stmt ASEGS ASAN LIM SINV argH fs.
  Proof. eapply AsanPlanSound2.node_join_ok; eauto with asanimgm. Qed.

  (* [comment removed for export] *)
  Theorem mc_x : forall x, x_stmt ASEGS ASAN NX0 LIM SINV argH fs x.
  Proof.
    intros [ | | | | | | | | | | ].
    - eapply asan_node_x_sound_XIMemset; eauto with asanimgm.
    - eapply asan_node_x_sound_XIMemcpy; eauto with asanimgm.
    - eapply asan_node_x_sound_XMemset; eauto with asanimgm.
    - eapply asan_node_x_sound_XMemcpy; eauto with asanimgm.
    - eapply asan_node_x_sound_XMemIsZero; eauto with asanimgm.
    - exact (init_x_sound_envscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
               (Z_to_bv 32 0x0004b503) (Z_to_bv 32 0x00848493) (Z_to_bv 32 0xfe051ce3) asan_env_x asan_fe1 asan_fe2 asan_fe3 asan_env_e
               ltac:(vm_refl) ltac:(vm_refl) ltac:(vm_refl)
               sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV mc_S0 mc_SF).
    - exact (init_x_sound_pnscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
               (Z_to_bv 32 0x00b53023) (Z_to_bv 32 0x00158593) (Z_to_bv 32 0xfff5c683) (Z_to_bv 32 0xfec68ae3) (Z_to_bv 32 0xfe069ae3)
               asan_pn_x asan_fp0 asan_fp1 asan_fp2 asan_fp3 asan_fp4 asan_pn_e
               ltac:(vm_refl) ltac:(vm_refl) ltac:(vm_refl)
               ltac:(vm_refl) ltac:(vm_refl)
               sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV mc_S0 mc_SF mc_SA).
    - apply x_sound_layout.
    - eapply asan_node_x_sound_XIStrncpy; eauto with asanimgm.
    - eapply asan_node_x_sound_XPopFree; eauto with asanimgm.
    - intros args cs cs' E R FULL model T _ _ H. discriminate H.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_xn : forall T, H_class_prop T argv fs SINV -> ext_stmt ASEGS ASAN NX0 LIM (XNM T) SINV argH fs.
  Proof.
    intros T HT id args. unfold XNM, XNm, ATAB, RPTAB, FPAR, DPLAY, DPL_asan. cbn [fst snd].
    destruct (Nat.ltb id 10).
    { eapply (asan_ext_sound sp brk0 argv envp rdraw); try eassumption;
        first [exact mc_S1 | exact mc_SF | exact mc_SA]. }
    destruct (Nat.ltb id 100).
    { eapply (io_ext_stmt_init ASEGS ASAN APH); eauto with asanimgm; first [exact mc_S0 | exact HT]. }
    destruct (Nat.ltb id 102).
    { eapply asan_rp_ext_sound; eauto with asanimgm. }
    destruct (Nat.ltb id 103).
    { eapply fn_xn_sound; eauto with asanimgm. }
    destruct (Nat.ltb id 105).
    { eapply hs_xn_sound; eauto with asanimgm. }
    destruct (Nat.ltb id 111).
    { eapply asan_pg_ext_sound; eauto with asanimgm. }
    destruct (Nat.ltb id 113).
    { eapply asan_k1_ext_sound; eauto with asanimgm. }
    destruct (Nat.ltb id 115).
    { eapply asan_dpn_ext_sound; eauto with asanimgm. }
    destruct (Nat.ltb id 120).
    { eapply asan_k1_ext_sound; eauto with asanimgm. }
    destruct (Nat.ltb id 121).
    { eapply sd_xn_sound; eauto with asanimgm. }
    destruct (Nat.ltb id 122).
    { eapply asan_ug_ext_sound; eauto with asanimgm. }   (* [comment removed for export] *)
    { eapply asan_lc_ext_sound; eauto with asanimgm. }   (* [comment removed for export] *)
  Qed.

  Lemma mc_xe : emit_stmt ASEGS ASAN NX0 LIM (XEm ASEGS ASAN NX0) SINV argH fs.
  Proof.
    eapply (asan_emit_sound sp brk0 argv envp rdraw); try eassumption;
      first [exact mc_S1 | exact mc_SF | exact mc_SA].
  Qed.

  Lemma mc_xb : forall T, H_class_prop T argv fs SINV -> ext2_stmt ASEGS ASAN NX0 LIM (XBm ASEGS NX0 T) SINV argH fs.
  Proof.
    intros T HT.
    eapply (io_ext2_stmt_init ASEGS ASAN APH); eauto with asanimgm; first [exact mc_S0 | exact HT].
  Qed.

  (* [comment removed for export] *)
  Lemma mc_VF : forall E M, SINV E M -> know_ok ASEGS E M (vfacts (variant_of c)).
  Proof.
    intros E M HS.
    pose proof HS as (_ & _ & _ & Hb). specialize (Hb 0%nat). cbn [Nat.add] in Hb.
    assert (HC : uE E AsanShape.CFGX = cfglen c).
    { unfold AsanShape.CFGX, JB. rewrite CFGX_denot, Hb, !hbyte_chunk0 by lia. reflexivity. }
    assert (HM : uE E AsanShape.XCM = bz 2 c mod 4).
    { unfold AsanShape.XCM, JB. rewrite XCM_denot, Hb, hbyte_chunk0 by lia. reflexivity. }
    assert (HN : uE E AsanShape.XB1S = bv_swrap 8 (bz 1 c) mod 2 ^ 64).
    { unfold AsanShape.XB1S, JB. rewrite XB1S_denot, Hb, hbyte_chunk0 by lia. reflexivity. }
    unfold uE in HC, HM, HN. pose proof (cfglen_range c) as CR. pose proof (bz_range 2 c) as BR. pose proof (bz_range 1 c) as BR1.
    assert (SW : bv_swrap 8 (bz 1 c) = (if bz 1 c <? 128 then bz 1 c else bz 1 c - 256)).
    { unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
      destruct (Z.ltb_spec (bz 1 c) 128); [rewrite Z.mod_small by lia; lia|].
      replace (bz 1 c + 128) with ((bz 1 c + 128 - 256) + 1 * 256) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
    unfold vfacts, variant_of, v_cfg0, v_cmod, v_cnt. cbn [fst snd].
    constructor; [|constructor; [|constructor; [|constructor]]].
    - destruct (Z.eqb_spec (cfglen c) 0) as [Hz|Hz]; cbn [kentry_ok]; rewrite HC; lia.
    - cbn [kentry_ok]. rewrite HM. lia.
    - destruct (Z.leb_spec 128 (bz 1 c)) as [Hc|Hc]; cbn [kentry_ok]; rewrite HN, SW.
      + destruct (Z.ltb_spec (bz 1 c) 128); [lia|].
        replace (bz 1 c - 256) with ((bz 1 c - 256 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      + destruct (Z.ltb_spec (bz 1 c) 128); [|lia]. rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_noblob : forall h ch, HS_mainA h = Some ch -> acs_noblob ch = true.
  Proof.
    intros h ch E. destruct h as [|h]; [|discriminate E].
    change (Some HS_mainA_0 = Some ch) in E.
    apply (f_equal (fun o => match o with Some c => c | None => HS_mainA_0 end)) in E. cbv beta iota in E.
    rewrite <- E. vm_compute. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Hypothesis ITm_ok : itab_sound ASEGS ITm.
  Variable TREE : nat -> nat -> mtree.
  Hypothesis TREES : forall h ch i, HS_mainA h = Some ch -> (i < 6)%nat ->
    mtree_ok KCm BFUELm FUELm ITm 0 0 (HSA HS_mainA h) (root_class i) (TREE h i) = true.

  Theorem mc_main_holes : holes_stmt ASEGS ASAN LIM HS_mainA (SINV0 APH sp rdraw brk0 argv envp uid hw) argH (HOLESM argv) fs.
  Proof.
    eapply main_holes; try eassumption;
      first [ exact asan_wx | exact asan_in_hull | exact asan_hull_ok | exact asan_shadow_ok | exact asan_nx0_ok
            | exact mc_noblob | exact ITm_ok | exact TREES
            | exact mc_AH | exact mc_AT | exact mc_AA | exact mc_SF | exact mc_SA
            | exact mc_sys | exact mc_brk2 | exact mc_brk2s | exact mc_mmap2 | exact mc_mmapin | exact mc_mprotect2 | exact mc_exit
            | exact mc_x | exact mc_join | exact mc_join_ok | exact mc_xn | exact mc_xe | exact mc_xb | exact mc_VF ].
  Qed.

  (* [comment removed for export] *)
  Theorem asan_realizes_spec_E :
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd))
              (spec argv fs).
  Proof.
    assert (RZ : srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM
                                   (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd))
                  (sd (HOLES_E (HOLESM argv)) t_nil (E0 APH sp rdraw brk0 argv envp uid hw) fs startup_asan_shape)).
    { eapply asan_startup; try eassumption;
        first [exact (HOLESM_agree argv) | exact (HOLESM_nil argv) | exact mc_main_holes]. }
    assert (Heq : sd (HOLES_E (HOLESM argv)) t_nil (E0 APH sp rdraw brk0 argv envp uid hw) fs startup_asan_shape = spec argv fs).
    { unfold startup_asan_shape. cbn [sd]. unfold HOLES_E, post_asan_shape. cbn [sd]. unfold HOLESM.
      repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity. }
    rewrite Heq in RZ. exact RZ.
  Qed.
End MCE.
