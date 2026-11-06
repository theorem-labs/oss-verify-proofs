(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanSpec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanFO
  BothAsanPlanImages BothAsanAcctImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanNodesSL AsanNodesY AsanMainLib AsanMainHooksBoth AsanShape
  AsanMainDefsBoth AsanMainTreeBoth SpinAlgCfg AsanPlanSoundCfg AsanMainCfgBoth.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  AsanNodesMmACfg AsanNodesMmBCfg AsanPlanSound2Cfg AsanNodesStartXInitCfg AsanPlanSoundSumsCfg BothSumsAsanSpecs BothSumsAsanCloseCfg
  BothAsan_code_startx BothAsanNodesStartXAsan AsanNodesArgAsanCfgBoth AsanNodesIOSoundCfg AsanIOAsanCfgBoth AsanEmitAsanCfgBoth AsanNodesRPSoundCfgBoth AsanNodesSLInstCfgBoth
  AsanNodesYSoundCfg AsanNodesGenSoundCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import DepotNodeBoth DepotNodeSoundBoth.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesXLib AsanNodesXLibSoundCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Unset Lia Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma asan_segs_end : Forall (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= img_hi INFO_BOTH) ASEGS.
Proof.
  rewrite asan_segs_eq.
  repeat constructor; cbn [seg_base seg_size img_hi INFO_BOTH
           AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003]; lia.
Qed.
Lemma asan_rw_ok : forall m (x : word), rw_lo INFO_BOTH <= bv_unsigned x < rw_lo INFO_BOTH + rw_len INFO_BOTH -> wview ASEGS m x <> None.
Proof. intros m x Hx. apply asan_rw_window. cbn [rw_lo rw_len INFO_BOTH] in Hx. lia. Qed.
Lemma asan_hull_as : AsFuzzContract.AS_IMGLO <= img_lo INFO_BOTH.
Proof. cbn [img_lo INFO_BOTH]. unfold AsFuzzContract.AS_IMGLO. lia. Qed.

Section MC.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis LIB : AsFuzzContract.as_fuzz_contract ASEGS (XLNB.abi_of INFO_BOTH).

  #[local] Notation c := (content_of argv fs).
  #[local] Notation SINV0' := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation SINV := (SINVm APH sp rdraw brk0 argv envp uid hw (content_of argv fs)).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Let argH_high := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let argH_agree := argH0_agree APH sp rdraw argv envp uid hw.
  Lemma mc_SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros. eapply SINVm_frame; eassumption. Qed.
  Lemma mc_SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros. eapply SINVm_agree; eassumption. Qed.
  Lemma mc_SINV_SINV0 : forall E M, SINV E M -> SINV0' E M.
  Proof. intros E M H. eapply SINVm_SINV0. exact H. Qed.
  Lemma mc_SINV_SINV1 : forall E M, SINV E M -> SINV1 sp rdraw brk0 argv envp uid hw E M.
  Proof. intros E M (H0 & H1 & H2 & _). split; [exact H0|]. split; [exact H1 | exact H2]. Qed.
  Lemma mc_argH_sp : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a H Ha. exact (argH0_sp APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M a (mc_SINV_SINV0 E M H) Ha). Qed.

  #[local] Ltac obl X :=
    exact (X ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok
             argH_high argH_agree mc_SINV_frame mc_SINV_agree mc_argH_sp asan_res_cover NX0_sp0).

  (* [comment removed for export] *)
  Lemma mc_sys : forall y, APSC.sys_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI y.
  Proof. obl node_sys_cfg_OBL. Qed.
  Lemma mc_brk2 : APSC.brk2_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI.
  Proof. obl node_brk2_cfg_OBL. Qed.
  Lemma mc_brku : APSC.brku_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI.
  Proof. obl node_brku_cfg_OBL. Qed.
  Lemma mc_mmap2 : APSC.mm2_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI (node_mmap2 INFO_BOTH NX0 LIM).
  Proof. obl node_mmap2_cfg_OBL. Qed.
  Lemma mc_mmapin : forall hole : bool, APSC.mm3_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI (node_mmapin INFO_BOTH LIM hole).
  Proof. obl node_mmapin_cfg_OBL. Qed.
  Lemma mc_mprotect2 : APSC.mm2_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI (node_mprotect2 INFO_BOTH LIM).
  Proof. obl node_mprotect2_cfg_OBL. Qed.
  Lemma mc_exit : APSC.exit_stmt_cfg ASEGS INFO_BOTH LIM SINV argH fs FPI.
  Proof. obl node_exit_cfg_OBL. Qed.
  Lemma mc_join : APSC.join_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI.
  Proof. exact (node_join_cfg_OBL ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI). Qed.

  (* [comment removed for export] *)
  Lemma mc_x : forall x, APF.xnode_fo x = true -> APSC.x_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI x.
  Proof.
    intros x Hx. destruct x; try discriminate Hx.
    - exact (asan_node_x_cfg_XIMemset NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - exact (asan_node_x_cfg_XIMemcpy NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - exact (asan_node_x_cfg_XMemset NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - exact (asan_node_x_cfg_XMemcpy NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - exact (asan_node_x_cfg_XMemIsZero NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - intros args. apply APSC.x_of_fp. intros FP _.
      eapply (@init_x_sound_envscan FP ASEGS INFO_BOTH APH asan_wx asan_in_hull W_8ea54 W_8ea58 W_8ea5c);
        first [ exact asan_Fe1 | exact asan_Fe2 | exact asan_Fe3 | exact D_8ea54 | exact D_8ea58 | exact D_8ea5c
              | (cbn [x_envscan x_envscan_k INFO_BOTH]; lia) | (repeat split; reflexivity) | eassumption
              | exact mc_SINV_SINV0 | exact mc_SINV_frame ].
    - intros args. apply APSC.x_of_fp. intros FP _.
      eapply (@init_x_sound_pnscan FP ASEGS INFO_BOTH APH asan_wx asan_in_hull asan_hull_ok W_8eb10 W_8eb14 W_8eb18 W_8eb1c W_8eb20);
        first [ exact asan_Fp0 | exact asan_Fp1 | exact asan_Fp2 | exact asan_Fp3 | exact asan_Fp4
              | exact D_8eb10 | exact D_8eb14 | exact D_8eb18 | exact D_8eb1c | exact D_8eb20
              | (cbn [x_pnscan x_pnscan_k INFO_BOTH]; lia) | (repeat split; reflexivity) | eassumption
              | exact mc_SINV_SINV0 | exact mc_SINV_frame | exact mc_SINV_agree ].
    - intros args. apply APSC.x_of_fp. intros FP _. exact (@init_x_sound_layout FP ASEGS INFO_BOTH APH sp rdraw argv envp fs uid hw SINV).
    - exact (asan_node_x_cfg_XIStrncpy NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - exact (asan_node_x_cfg_XPopFree NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_xn : forall T, H_class_prop T argv fs SINV ->
    APSC.ext_stmt_cfg ASEGS INFO_BOTH NX0 LIM (XNm ASEGS INFO_BOTH NX0 RPN.RP_BOTH T) SINV argH fs FPI.
  Proof.
    intros T HT id args. unfold XNm.
    destruct (Nat.ltb id 10); [|destruct (Nat.ltb id 25); [|destruct (Nat.ltb id 40); [|destruct (Nat.ltb id 100);
      [|destruct (Nat.eqb id 105); [|destruct (Nat.eqb id 106); [|destruct (Nat.ltb id 110); [|destruct (Nat.eqb id 112);
      [|destruct (Nat.eqb id 120 || Nat.eqb id 121)%bool]]]]]]]].
    - exact (asan_ext_sound_cfg sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs SINV FPI mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree id args).
    - exact (asan_io_ext_sound_cfg sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs SINV mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree T HT FPI id args).
    - apply APSC.node1_of_fp. intros FP _. exact (@y_xn_sound FP ASEGS INFO_BOTH NX0 LIM asan_shadow_ok SINV argH fs id args).
    - exact (asan_io_ext_sound_cfg sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs SINV mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree T HT FPI id args).
    - apply APSC.node1_of_fp. intros FP _. exact (@asan_sl_ext_sound FP NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs id args).
    - apply APSC.node1_of_fp. intros FP _. exact (@asan_sl_ext_sound FP NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs id args).
    - apply APSC.node1_of_fp. intros FP _. exact (@asan_rp_ext_sound FP NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs id args).
    - (* [comment removed for export] *)
      eapply xn_put_sound_cfg; first [ eassumption | exact asan_hull_ok | exact NX0_sp0 | exact mc_SINV_frame | exact mc_SINV_agree
                                     | exact argH_high | exact argH_agree | exact asan_wx | exact asan_in_hull ].
    - (* [comment removed for export] *)
      apply APSC.node1_of_fp. intros FP _. exact (@gn_xn_sound FP ASEGS INFO_BOTH NX0 LIM SINV argH argH_agree mc_SINV_agree NX0_sp0 fs id args).
    - (* [comment removed for export] *)
      exact (xlib_xn_sound_cfg ASEGS INFO_BOTH NX0 LIM asan_wx asan_in_hull asan_hull_ok asan_segs_wr SINV argH argH_high argH_agree
               mc_SINV_frame mc_SINV_agree NX0_sp0 fs asan_segs_end asan_rw_ok asan_hull_as (XLNB.abi_of INFO_BOTH) LIB id args).
  Qed.

  Lemma mc_xe : APSC.emit_stmt_cfg ASEGS INFO_BOTH NX0 LIM (XEm ASEGS INFO_BOTH NX0) SINV argH fs FPI.
  Proof. exact (asan_emit_sound_cfg sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs SINV FPI mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree). Qed.

  Lemma mc_xb : forall T, H_class_prop T argv fs SINV -> APSC.ext2_stmt_cfg ASEGS INFO_BOTH NX0 LIM (XBm ASEGS NX0 T) SINV argH fs FPI.
  Proof.
    intros T HT.
    exact (asan_io_ext2_sound_cfg sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs SINV mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree T HT FPI).
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
  Section Closed.
    Variable HS_asan : nat -> option acs.
    Hypothesis HSA_noblob : forall h ch, HS_asan h = Some ch -> acs_noblob ch = true.   (* [comment removed for export] *)
    Variables KCm BFUELm FUELm : nat.
    Variable ITm : itab.
    Hypothesis ITm_ok : itab_sound ASEGS ITm.
    Variable TREE : nat -> nat -> mtree.
    Hypothesis TREES : forall h ch i, HS_asan h = Some ch -> (i < 6)%nat ->
      mtree_ok KCm BFUELm FUELm ITm 0 0 (HSA HS_asan h) (root_class i) (TREE h i) = true.

    Lemma mc_run : APSC.run_block_stmt_cfg ASEGS ITm INFO_BOTH NX0 LIM SINV argH fs KCm FPI.
    Proof.
      exact (APSC.run_block_stmt_cfg_all ASEGS ITm ITm_ok INFO_BOTH NX0 LIM (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None)
               asan_wx asan_in_hull asan_hull_ok SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs KCm FPI).
    Qed.

    Theorem main_holes_closed : forall FPS, (forall FP, FPS FP -> FPI FP) ->
      APSC.holes_stmt_cfg ASEGS INFO_BOTH LIM HS_asan SINV0' argH (HOLESM argv) fs FPS.
    Proof.
      exact (main_holes sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit HS_asan HSA_noblob KCm BFUELm FUELm ITm
               mc_run mc_sys mc_brk2 mc_brku mc_mmap2 mc_mmapin mc_mprotect2 mc_exit mc_x mc_join mc_xn mc_xe mc_xb mc_VF TREE TREES).
    Qed.
  End Closed.
End MC.
