(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the main soundness takes AsanInit's LPS 727298f3 launch and the launch kernel's rseq layout, the run's filesystem is the image's seeded with tmp, the hand-off states follow the launch's rseq layout, and the closure holds at a flag of SpinAlg.srealizesM with the trees' dead-arm check (TREES_DEAD) at the flag true. *)
(* Main soundness and startup share AsanInit's full launch and the launch kernel's rseq layout. *)
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
  MainGlueDefs MainGlue DeadArm.
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
  Context {rsb : bool}.   (* the launch's kb_rseq; the table is ASAN_at/BOTH_at (rseq_z rsb) *)
  (* [comment removed for export] *)
  Hypothesis FCA : F_contract_asan ASEGS FPA_asan.

  (* [comment removed for export] *)
  Let apc : N := Asan.M.init_pc.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable imgfs : Fs.Fs.   (* the IMAGE filesystem; the run's is [fs] = [in_fs INP], see below *)
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable urnd : InputStream.   (* [comment removed for export] *)
  Variable tmp : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Context {sigpipe_default : bool}.   (* AsanInit's: the launch's SIGPIPE disposition at entry *)

  Let INP := @AsanInit.inp argv envp imgfs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default.
  (** The run's filesystem is [in_fs INP] = the image fs seeded with [tmp], NOT the bare image
      fs, exactly as AsanStartupE.v states it.  The two are not convertible ([c0dd863a:theories/LinuxProcessSem/State.v:7691-7692]). *)
  #[local] Notation fs := (in_fs INP).
  Let IMG : img_facts ASEGS (ASAN_at (rseq_z rsb)) APH := asan_img_facts.
  Let Hapc : Z.of_N apc = a_entry (ASAN_at (rseq_z rsb)) := ltac:(vm_compute; reflexivity).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  Hypothesis Hrs : a_rseq (ASAN_at (rseq_z rsb)) = rseq_z (kb_rseq kb).

  (* [asan_startup] asks for [kb_rseq kb = rsb] (AsanStartupE.v:108); this section records the
     same fact one projection out, as [Hrs].  [rseq_z] separates the two booleans, so the two
     statements are equivalent. *)
  Lemma mc_kb : kb_rseq kb = rsb.
  Proof.
    (* [destruct (kb_rseq kb) eqn:E] already substitutes inside [H], so the rewrite is optional
       ([rewrite ?E]). *)
    pose proof Hrs as H. destruct rsb; destruct (kb_rseq kb) eqn:E; rewrite ?E in H;
      vm_compute in H; first [reflexivity | discriminate H].
  Qed.

  #[local] Notation c := (content_of argv fs).
  #[local] Notation SINV := (@SINVm APH apc sp rdraw brk0 mbase argv envp imgfs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default (content_of argv fs)).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).

  Lemma mc_AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. eapply AsanInit.argH0_high with (apc := apc); eassumption. Qed.
  Lemma mc_AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Proof. intros E E' a H. eapply AsanInit.argH0_agree; eassumption. Qed.
  Lemma mc_SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros. eapply SINVm_frame; eassumption. Qed.
  Lemma mc_SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros. eapply SINVm_agree; eassumption. Qed.
  Lemma mc_S0 : forall E M, SINV E M -> @SINV0 APH apc sp rdraw brk0 mbase argv envp imgfs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default E M.
  Proof. intros E M H. eapply SINVm_SINV0. exact H. Qed.
  Lemma mc_AT : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a HS Ha. pose proof (mc_S0 E M HS) as H0. eapply argH0_top; eauto. Qed.
  Lemma mc_S1 : forall E M, SINV E M -> @AsanNodesArgAsan.SINV1 APH apc sp rdraw brk0 mbase argv envp imgfs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default E M.
  Proof.
    intros E M HS. pose proof (mc_S0 E M HS) as H0. destruct HS as (_ & H1 & H2 & _).
    split; [exact H0 | split; assumption].
  Qed.

  Lemma mc_hull_okP : AsanPlanSoundSums.APSX.hull_okP (ASAN_at (rseq_z rsb)).
  Proof. exact asan_hull_ok. Qed.
  Create HintDb asanimgm.
  Hint Resolve asan_wx asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_nx0_ok asan_hull_res asan_segs_wr
               mc_AH mc_AA mc_SF mc_SA mc_AT mc_hull_okP FCA : asanimgm.

  (* [comment removed for export] *)
  Lemma mc_sys : forall fl y, sys_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM SINV argH fs fl y.
  Proof. intros fl y. eapply AsanNodesMmB.node_sys_sound; eauto with asanimgm. Qed.
  Lemma mc_brk2 : forall fl, brk2_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM SINV argH fs fl.
  Proof. intros fl. eapply AsanNodesMmB.node_brk2_sound; eauto with asanimgm. Qed.
  (* [eauto with asanimgm] does not close two goals of [node_munmap2_sound]:
       0 <= img_lo (ASAN_at (rseq_z rsb)) /\ ... /\ img_hi (ASAN_at (rseq_z rsb)) <= KHI
       0 <= shadow_off (ASAN_at (rseq_z rsb)) <= 2 ^ 47
     [AsanNodesMmB.SoundMunmap] states those two hypotheses UNFOLDED (the bodies of [APS.hull_ok], [APS.shadow_ok])
     while the hints state the same facts FOLDED ([asan_hull_ok : APS.hull_ok A],
     [asan_shadow_ok : APS.shadow_ok A]).  [eauto]'s hint index is keyed on the head constant,
     so a hint stated on the other side of a [Definition] is invisible to it; [exact] takes each
     by conversion.  The sibling [node_mmap2_sound_OBL] restates its
     obligations folded for exactly this reason.  Nothing here changes a statement: the same
     section hypotheses are discharged with the same facts. *)
  Lemma mc_munmap2 : forall fl, munmap2_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM SINV argH fs fl.
  Proof.
    intros fl. eapply AsanNodesMmB.node_munmap2_sound;
      first [ exact asan_wx | exact asan_in_hull | exact asan_res_len | exact asan_res_hull
            | exact asan_hull_ok | exact asan_shadow_ok | exact asan_nx0_ok | exact asan_hull_res
            | exact asan_segs_wr | exact mc_AH | exact mc_AA | exact mc_SF | exact mc_SA
            | exact mc_AT | exact FCA | eauto with asanimgm ].
  Qed.
  Lemma mc_brk2s : forall fl, brk2s_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM SINV argH fs fl.
  Proof. intros fl. eapply AsanNodesMmB.node_brk2s_sound; eauto with asanimgm. Qed.
  Lemma mc_mmap2 : forall fl, mm2_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM SINV argH fs fl (node_mmap2 (ASAN_at (rseq_z rsb)) NX0 LIM).
  Proof. eapply AsanNodesMmA.node_mmap2_sound_OBL; eauto with asanimgm. Qed.
  Lemma mc_mmapin : forall fl (hole : bool), mm3_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM SINV argH fs fl (node_mmapin (ASAN_at (rseq_z rsb)) LIM hole).
  Proof. eapply AsanNodesMmA.node_mmapin_sound_OBL; eauto with asanimgm. Qed.
  Lemma mc_mprotect2 : forall fl, mm2_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM SINV argH fs fl (node_mprotect2 (ASAN_at (rseq_z rsb)) LIM).
  Proof. eapply AsanNodesMmA.node_mprotect2_sound_OBL; eauto with asanimgm. Qed.
  Lemma mc_exit : forall fl, exit_stmt ASEGS (ASAN_at (rseq_z rsb)) LIM SINV argH fs fl.
  Proof. intros fl. eapply AsanNodesMmB.node_exit_sound; eauto with asanimgm. Qed.
  Lemma mc_join : forall fl, join_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM SINV argH fs fl.
  Proof. intros fl. eapply AsanPlanSound2.node_join_sound; eauto with asanimgm. Qed.
  Lemma mc_join_ok : join_ok_stmt ASEGS (ASAN_at (rseq_z rsb)) LIM SINV argH fs.
  Proof. eapply AsanPlanSound2.node_join_ok; eauto with asanimgm. Qed.

  (* [comment removed for export] *)
  Theorem mc_x : forall fl x, x_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM SINV argH fs fl x.
  Proof.
    intros fl [ | | | | | | | | | | ].
    - eapply asan_node_x_sound_XIMemset; eauto with asanimgm.
    - eapply asan_node_x_sound_XIMemcpy; eauto with asanimgm.
    - eapply asan_node_x_sound_XMemset; eauto with asanimgm.
    - eapply asan_node_x_sound_XMemcpy; eauto with asanimgm.
    - eapply asan_node_x_sound_XMemIsZero; eauto with asanimgm.
    - eapply init_x_sound_envscan with (ph := APH) (apc := apc)
        (we1 := Z_to_bv 32 0x0004b503) (we2 := Z_to_bv 32 0x00848493) (we3 := Z_to_bv 32 0xfe051ce3);
        solve [ eassumption | exact asan_wx | exact asan_in_hull | exact asan_hull_ok
              | exact asan_env_x | exact asan_fe1 | exact asan_fe2 | exact asan_fe3 | exact asan_env_e
              | vm_refl | exact mc_S0 | exact mc_SF ].
    - eapply init_x_sound_pnscan with (ph := APH) (apc := apc)
        (wp0 := Z_to_bv 32 0x00b53023) (wp1 := Z_to_bv 32 0x00158593) (wp2 := Z_to_bv 32 0xfff5c683)
        (wp3 := Z_to_bv 32 0xfec68ae3) (wp4 := Z_to_bv 32 0xfe069ae3);
        solve [ eassumption | exact asan_wx | exact asan_in_hull | exact asan_hull_ok
              | exact asan_pn_x | exact asan_fp0 | exact asan_fp1 | exact asan_fp2 | exact asan_fp3 | exact asan_fp4 | exact asan_pn_e
              | vm_refl | exact mc_S0 | exact mc_SF | exact mc_SA ].
    - apply x_sound_layout.
    - eapply asan_node_x_sound_XIStrncpy; eauto with asanimgm.
    - eapply asan_node_x_sound_XPopFree; eauto with asanimgm.
    - intros args cs cs' E R FULL model T _ _ H. discriminate H.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_xn : forall T, H_class_prop T argv fs SINV -> forall fl, ext_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM (XNM rsb T) SINV argH fs fl.
  Proof.
    (* [unfold] takes a qualid, never an application: [ATAB] is a Definition of one argument
       (MainGlueDefs.v:76) and unfolding the constant unfolds every application of it. *)
    intros T HT fl id args. unfold XNM, XNm, ATAB, RPTAB, FPAR, DPLAY, DPL_asan. cbn [fst snd].
    destruct (Nat.ltb id 10).
    { eapply asan_ext_sound with (ph := APH) (apc := apc); try eassumption;
        first [exact mc_S1 | exact mc_SF | exact mc_SA]. }
    destruct (Nat.ltb id 100).
    { eapply io_ext_stmt_init with (ph := APH) (apc := apc); eauto with asanimgm; first [exact mc_S0 | exact HT]. }
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

  Lemma mc_xe : forall fl, emit_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM (XEm ASEGS (ASAN_at (rseq_z rsb)) NX0) SINV argH fs fl.
  Proof.
    intros fl. eapply asan_emit_sound with (ph := APH) (apc := apc); try eassumption;
      first [exact mc_S1 | exact mc_SF | exact mc_SA].
  Qed.

  Lemma mc_xb : forall T, H_class_prop T argv fs SINV -> forall fl, ext2_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIM (XBm ASEGS (ASAN_at (rseq_z rsb)) NX0 T) SINV argH fs fl.
  Proof.
    intros T HT fl.
    eapply io_ext2_stmt_init with (ph := APH) (apc := apc); eauto with asanimgm; first [exact mc_S0 | exact HT].
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

  (* The collected hand-off state carries [KWord {| a_base := ELit 0; a_off := 6318336 |} 8 (EBlob false 3 8 8)],
     the libc stack guard copied from the AT_RANDOM draw ([AsanPlanCore.K_RND] = 3), so it reads a byte
     string.  [acs_blob_fixed] is what [cs_ok_reblob] needs: every byte string the state reads sits at
     an index [reblob] leaves alone. *)
  Lemma mc_blob_fixed : forall h ch, (HS_mainA (rseq_z rsb)) h = Some ch -> acs_blob_fixed ch = true.
  Proof.
    intros h ch E. destruct h as [|h]; [|discriminate E].
    (* [HS_mainA_0] is indexed by the launch's layout r (StartupHSMainAsan.v:37): [Some HS_mainA_0] has
       type [option (Z -> acs)].  Both recorded states are closed terms, so both are decided. *)
    cbn [HS_mainA] in E. injection E as E. subst ch.
    destruct rsb; vm_compute; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Hypothesis ITm_ok : itab_sound ASEGS ITm.
  Variable TREE : nat -> nat -> mtree.
  Hypothesis TREES : forall h ch i, (HS_mainA (rseq_z rsb)) h = Some ch -> (i < 6)%nat ->
    mtree_ok (rsb := rsb) KCm BFUELm FUELm ITm 0 0 (HSA rsb (HS_mainA (rseq_z rsb)) h) (root_class i) (TREE h i) = true.

  (* The main trees' dead-arm check (computed per tree, [MainGlue.mtree_dead]); asked at the flag [true] only. *)
  Definition TREES_DEAD : Prop := forall h ch i, (HS_mainA (rseq_z rsb)) h = Some ch -> (i < 6)%nat -> mtree_dead hf26 (TREE h i) = true.

  Theorem mc_main_holes : forall fl, (fl = true -> TREES_DEAD) ->
    holes_stmt ASEGS (ASAN_at (rseq_z rsb)) LIM (HS_mainA (rseq_z rsb)) (@SINV0 APH apc sp rdraw brk0 mbase argv envp imgfs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default) argH (HOLESM argv) fs (fun _ => fl).
  Proof.
    intros fl Hd.
    eapply main_holes; try eassumption;
      first [ exact asan_wx | exact asan_in_hull | exact asan_hull_ok | exact asan_shadow_ok | exact asan_nx0_ok
            | exact mc_blob_fixed | exact ITm_ok | exact TREES
            | exact mc_AH | exact mc_AT | exact mc_AA | exact mc_SF | exact mc_SA
            | exact mc_sys | exact mc_brk2 | exact mc_munmap2 | exact mc_brk2s | exact mc_mmap2 | exact mc_mmapin | exact mc_mprotect2 | exact mc_exit
            | exact mc_x | exact mc_join | exact mc_join_ok | exact mc_xn | exact mc_xe | exact mc_xb | exact mc_VF | exact Hd ].
  Qed.

  (* [comment removed for export] *)
  (* At the flag [fl]: the agreement reads [fl = false] ([asan_realizes_spec_E]), the halting statement
     [fl = true] with the trees' dead-arm check. *)
  Theorem asan_realizes_spec_M : forall fl, (fl = true -> TREES_DEAD) ->
    srealizesM ASEGS fl (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM
                                 INP)
              (spec argv fs).
  Proof.
    intros fl Hd.
    (* [asan_startup] (AsanStartupE.v:235-237) states its shape over [in_fs INP], the RUN's
       filesystem; [fs] abbreviates exactly that, so the two agree by name.  [mc_kb] supplies
       [kb_rseq kb = rsb], which this section records one projection out as [Hrs]. *)
    assert (RZ : srealizesM ASEGS fl (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM INP)
                  (sd (HOLES_E (HOLESM argv)) t_nil (E0 sp rdraw brk0 argv envp uid gid kb execfn) fs startup_asan_shape)).
    { eapply asan_startup; try eassumption;
        first [exact (HOLESM_agree argv) | exact (HOLESM_nil argv) | exact (mc_main_holes fl Hd) | exact mc_kb]. }
    assert (Heq : sd (HOLES_E (HOLESM argv)) t_nil (E0 sp rdraw brk0 argv envp uid gid kb execfn) fs startup_asan_shape = spec argv fs).
    { unfold startup_asan_shape. cbn [sd]. unfold HOLES_E, post_asan_shape. cbn [sd]. unfold HOLESM.
      repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity. }
    rewrite Heq in RZ. exact RZ.
  Qed.

  Theorem asan_realizes_spec_E :
    srealizesE ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM
                                 INP)
              (spec argv fs).
  Proof. exact (asan_realizes_spec_M false (fun H => ltac:(discriminate H))). Qed.
End MCE.
