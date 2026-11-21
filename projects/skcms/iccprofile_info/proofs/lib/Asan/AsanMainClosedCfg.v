(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the closure takes AsanInit's full launch (with the kernel build at pinned_kernel) and the image's table at the launch's own CONFIG_RSEQ layout (INFO_ASAN_at); launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanSpec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanFO
  AsanPlanImages AsanAcctImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanNodesSL AsanNodesY AsanMainLib AsanShape
  AsanMainDefs AsanMainTree SpinAlgCfg AsanPlanSoundCfg AsanMainCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  AsanNodesMmACfg AsanNodesMmBCfg AsanPlanSound2Cfg AsanNodesStartXInitCfg AsanPlanSoundSumsCfg SumsAsanSpecs SumsAsanCloseCfg
  Asan_code_startx AsanNodesStartXAsan AsanNodesArgAsanCfg AsanNodesIOSoundCfg AsanIOAsanCfg AsanEmitAsanCfg AsanNodesRPSoundCfg AsanNodesSLInstCfg
  AsanNodesYSoundCfg AsanNodesGenSoundCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import DepotNode DepotNodeSound.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesXLib AsanNodesXLibSoundCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Unset Lia Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma asan_segs_end {r : Z} : Forall (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= img_hi (INFO_ASAN_at r)) ASEGS.
Proof.
  rewrite asan_segs_eq.
  repeat constructor; cbn [seg_base seg_size img_hi INFO_ASAN_at
           Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003]; lia.
Qed.
Lemma asan_rw_ok {r : Z} : forall m (x : word), rw_lo (INFO_ASAN_at r) <= bv_unsigned x < rw_lo (INFO_ASAN_at r) + rw_len (INFO_ASAN_at r) -> wview ASEGS m x <> None.
Proof. intros m x Hx. apply asan_rw_window. cbn [rw_lo rw_len INFO_ASAN_at] in Hx. lia. Qed.
Lemma asan_hull_as {r : Z} : AsFuzzContract.AS_IMGLO <= img_lo (INFO_ASAN_at r).
Proof. cbn [img_lo INFO_ASAN_at]. unfold AsFuzzContract.AS_IMGLO. lia. Qed.

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
  (* the ABI does not read the table's layout ([XLN.abi_of] is constant) *)
  Hypothesis LIB : AsFuzzContract.as_fuzz_contract ASEGS (XLN.abi_of (INFO_ASAN_at 1)).
  Variable apc : N.
  Variable mbase : word.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable nofile : word.
  Variable sigmask : word.
  Variable urnd : InputStream.
  Variable kern : KernelBuild.
  Variable execfn : list byte.
  Context {sigpipe_default : bool}.   (* AsanInit's: the launch's SIGPIPE disposition at entry *)
  (** see [AsanInit.pinned_kernel]: [recorded_kernel]'s eight fields; CONFIG_RSEQ free *)
  Hypothesis Hkernel : in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))
    = pinned_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))).
  Hypothesis Hlaunch : valid_launch (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
  (* LPS 727298f3: the image's table at the launch's own CONFIG_RSEQ layout. *)
  #[local] Notation IA := (INFO_ASAN_at (rseq_z (kb_rseq kern))) (only parsing).

  #[local] Notation c := (content_of argv fs).
  #[local] Notation SINV0' := (SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
  #[local] Notation SINV := (SINVm APH sp rdraw brk0 argv envp uid hw (content_of argv fs) apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
  #[local] Notation argH := (argH0 sp rdraw argv envp kern execfn).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  (* [AsanInit.argH0_high] is discharged over the entry pc too, which it does not read
     (AsanNodesArgAsanCfg.argH0_high_asan passes any value). *)
  Let argH_high := argH0_high apc sp rdraw argv envp kern execfn Hsp Hva.
  Let argH_agree := argH0_agree sp rdraw argv envp kern execfn.
  Lemma mc_SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros. eapply SINVm_frame; eassumption. Qed.
  Lemma mc_SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros. eapply SINVm_agree; eassumption. Qed.
  Lemma mc_SINV_SINV0 : forall E M, SINV E M -> SINV0' E M.
  Proof. intros E M H. eapply SINVm_SINV0. exact H. Qed.
  Lemma mc_SINV_SINV1 : forall E M, SINV E M -> SINV1 sp rdraw brk0 argv envp uid hw apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default) E M.
  Proof. intros E M (H0 & H1 & H2 & _). split; [exact H0|]. split; [exact H1 | exact H2]. Qed.
  Lemma mc_argH_sp : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a H Ha. exact (argH0_sp APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn Hsp Hva Hve Hfit Hlau E M a (mc_SINV_SINV0 E M H) Ha). Qed.

  #[local] Ltac obl X :=
    exact (X ASEGS IA NX0 LIM SINV argH fs FPI asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok
             argH_high argH_agree mc_SINV_frame mc_SINV_agree mc_argH_sp asan_res_cover NX0_sp0).

  (* [comment removed for export] *)
  Lemma mc_sys : forall y, APSC.sys_stmt_cfg ASEGS IA NX0 LIM SINV argH fs FPI y.
  Proof. obl node_sys_cfg_OBL. Qed.
  Lemma mc_brk2 : APSC.brk2_stmt_fo ASEGS IA NX0 LIM SINV argH fs FPI.
  Proof. obl node_brk2_cfg_OBL. Qed.
  Lemma mc_brku : APSC.brku_stmt_cfg ASEGS IA NX0 LIM SINV argH fs FPI.
  Proof. obl node_brku_cfg_OBL. Qed.
  Lemma mc_mmap2 : APSC.mm2_stmt_fo ASEGS IA NX0 LIM SINV argH fs FPI (node_mmap2 IA NX0 LIM).
  Proof. obl node_mmap2_cfg_OBL. Qed.
  Lemma mc_mmapin : forall hole : bool, APSC.mm3_stmt_fo ASEGS IA NX0 LIM SINV argH fs FPI (node_mmapin IA LIM hole).
  Proof. obl node_mmapin_cfg_OBL. Qed.
  Lemma mc_mprotect2 : APSC.mm2_stmt_fo ASEGS IA NX0 LIM SINV argH fs FPI (node_mprotect2 IA LIM).
  Proof. obl node_mprotect2_cfg_OBL. Qed.
  Lemma mc_exit : APSC.exit_stmt_cfg ASEGS IA LIM SINV argH fs FPI.
  Proof. obl node_exit_cfg_OBL. Qed.
  Lemma mc_join : APSC.join_stmt_cfg ASEGS IA NX0 LIM SINV argH fs FPI.
  Proof. exact (node_join_cfg_OBL ASEGS IA NX0 LIM SINV argH fs FPI). Qed.

  (* [comment removed for export] *)
  Lemma mc_x : forall x, APF.xnode_fo x = true -> APSC.x_stmt_cfg ASEGS IA NX0 LIM SINV argH fs FPI x.
  Proof.
    intros x Hx. destruct x; try discriminate Hx.
    - exact (asan_node_x_cfg_XIMemset NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - exact (asan_node_x_cfg_XIMemcpy NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - exact (asan_node_x_cfg_XMemset NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - exact (asan_node_x_cfg_XMemcpy NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - exact (asan_node_x_cfg_XMemIsZero NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - intros args. apply APSC.x_of_fp. intros FP _.
      eapply (@init_x_sound_envscan FP ASEGS IA APH asan_wx asan_in_hull W_8dc24 W_8dc28 W_8dc2c);
        first [ exact asan_Fe1 | exact asan_Fe2 | exact asan_Fe3 | exact D_8dc24 | exact D_8dc28 | exact D_8dc2c
              | (cbn [x_envscan x_envscan_k INFO_ASAN_at]; lia) | (repeat split; reflexivity) | reflexivity | eassumption
              | exact mc_SINV_SINV0 | exact mc_SINV_frame ].
    - intros args. apply APSC.x_of_fp. intros FP _.
      eapply (@init_x_sound_pnscan FP ASEGS IA APH asan_wx asan_in_hull asan_hull_ok W_8dce0 W_8dce4 W_8dce8 W_8dcec W_8dcf0);
        first [ exact asan_Fp0 | exact asan_Fp1 | exact asan_Fp2 | exact asan_Fp3 | exact asan_Fp4
              | exact D_8dce0 | exact D_8dce4 | exact D_8dce8 | exact D_8dcec | exact D_8dcf0
              | (cbn [x_pnscan x_pnscan_k INFO_ASAN_at]; lia) | (repeat split; reflexivity) | reflexivity | eassumption
              | exact mc_SINV_SINV0 | exact mc_SINV_frame | exact mc_SINV_agree ].
    - intros args. apply APSC.x_of_fp. intros FP _. exact (@init_x_sound_layout FP ASEGS IA sp rdraw argv envp fs kern execfn SINV).
    - exact (asan_node_x_cfg_XIStrncpy NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
    - exact (asan_node_x_cfg_XPopFree NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs FPI).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_xn : forall T, H_class_prop T argv fs SINV ->
    APSC.ext_stmt_cfg ASEGS IA NX0 LIM (XNm ASEGS IA NX0 RPN.RP_ASAN T) SINV argH fs FPI.
  Proof.
    intros T HT id args. unfold XNm.
    destruct (Nat.ltb id 10); [|destruct (Nat.ltb id 25); [|destruct (Nat.ltb id 40); [|destruct (Nat.ltb id 100);
      [|destruct (Nat.eqb id 105); [|destruct (Nat.eqb id 106); [|destruct (Nat.ltb id 110); [|destruct (Nat.eqb id 112);
      [|destruct (Nat.eqb id 120 || Nat.eqb id 121)%bool]]]]]]]].
    - exact (asan_ext_sound_cfg sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlau SINV FPI mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree id args).
    - exact (asan_io_ext_sound_cfg sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlaunch Hlau SINV mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree T HT FPI id args).
    - apply APSC.node1_of_fp. intros FP _. exact (@y_xn_sound FP ASEGS IA NX0 LIM asan_shadow_ok SINV argH fs id args).
    - exact (asan_io_ext_sound_cfg sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlaunch Hlau SINV mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree T HT FPI id args).
    - apply APSC.node1_of_fp. intros FP _. exact (@asan_sl_ext_sound FP _ NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs id args).
    - apply APSC.node1_of_fp. intros FP _. exact (@asan_sl_ext_sound FP _ NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs id args).
    - apply APSC.node1_of_fp. intros FP _. exact (@asan_rp_ext_sound FP _ NX0 LIM SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs id args).
    - (* [comment removed for export] *)
      eapply xn_put_sound_cfg; first [ eassumption | exact asan_hull_ok | exact NX0_sp0 | exact mc_SINV_frame | exact mc_SINV_agree
                                     | exact argH_high | exact argH_agree | exact asan_wx | exact asan_in_hull ].
    - (* [comment removed for export] *)
      apply APSC.node1_of_fp. intros FP _. exact (@gn_xn_sound FP ASEGS IA NX0 LIM SINV argH argH_agree mc_SINV_agree NX0_sp0 fs id args).
    - (* [comment removed for export] *)
      exact (xlib_xn_sound_cfg ASEGS IA NX0 LIM asan_wx asan_in_hull asan_hull_ok asan_segs_wr SINV argH argH_high argH_agree
               mc_SINV_frame mc_SINV_agree NX0_sp0 fs asan_segs_end asan_rw_ok asan_hull_as (XLN.abi_of IA) LIB id args).
  Qed.

  Lemma mc_xe : APSC.emit_stmt_cfg ASEGS IA NX0 LIM (XEm ASEGS IA NX0) SINV argH fs FPI.
  Proof. exact (asan_emit_sound_cfg sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs kern execfn apc mbase fs stdin gid groups net nofile sigmask urnd Hkernel Hlau SINV FPI mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree). Qed.

  Lemma mc_xb : forall T, H_class_prop T argv fs SINV -> APSC.ext2_stmt_cfg ASEGS IA NX0 LIM (XBm ASEGS IA NX0 T) SINV argH fs FPI.
  Proof.
    intros T HT.
    exact (asan_io_ext2_sound_cfg sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlaunch Hlau SINV mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree T HT FPI).
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
      mtree_ok (rseq_z (kb_rseq kern)) KCm BFUELm FUELm ITm 0 0 (HSA HS_asan h) (root_class i) (TREE h i) = true.

    Lemma mc_run : APSC.run_block_stmt_cfg ASEGS ITm IA NX0 LIM SINV argH fs KCm FPI.
    Proof.
      exact (APSC.run_block_stmt_cfg_all ASEGS ITm ITm_ok IA NX0 LIM (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None)
               asan_wx asan_in_hull asan_hull_ok SINV argH argH_high argH_agree mc_SINV_frame mc_SINV_agree NX0_sp0 fs KCm FPI).
    Qed.

    Theorem main_holes_closed : forall FPS, (forall FP, FPS FP -> FPI FP) ->
      APSC.holes_stmt_cfg ASEGS IA LIM HS_asan SINV0' argH (HOLESM argv) fs FPS.
    Proof.
      exact (main_holes sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit apc mbase stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlau HS_asan HSA_noblob KCm BFUELm FUELm ITm mc_run mc_sys mc_brk2 mc_brku mc_mmap2 mc_mmapin mc_mprotect2 mc_exit mc_x mc_join mc_xn mc_xe mc_xb mc_VF TREE TREES).
    Qed.
  End Closed.
End MC.
