(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.   
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require AsanNodesCanonSound AsanPlanSoundSums AsanNodesRJoinSound AsanNodesWorldSound.   
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec ShapeAlg SpinAlg AgentLib Spec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanLibNode AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanPlanImagesInit AsanInit AsanStartup
  AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain AsanLibTab.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  AsanNodesIface AsanNodesMmA AsanNodesMmB AsanNodesStartX
  AsanNodesArgSound AsanNodesEmitSound AsanIOSpec AsanNodesIOSound AsanNodesIOInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.





Definition XLIB_STMT (LINV : (word -> option byte) -> Prop) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (FS0 : Fs.Fs),
    valid_sp sp -> valid_argv argv -> valid_envp envp ->
    forall uid hw : word, entry_stack_fits sp argv envp ->
    forall SINV : env -> (word -> option byte) -> Prop,
      (forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M) ->
      (forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
      (forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M) ->
      OBL_lib ASEGS ASAN NX0 AsanInit.LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) LINV FS0 (ALN.summary_lib ASEGS LIBTAB_ASAN ASAN NX0).

Definition XARG_STMT (LINV : (word -> option byte) -> Prop) : Prop :=
  forall (fx : FPState) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (FS0 : Fs.Fs),
    valid_sp sp -> valid_argv argv -> valid_envp envp ->
    forall uid hw : word, entry_stack_fits sp argv envp ->
    forall SV : env -> (word -> option byte) -> Prop,
      (forall E M, SV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M /\ eb E 1%nat = nth 0 argv [] /\ eb E 2%nat = nth 1 argv []) ->
      (forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SV E M -> SV E M') ->
      (forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M) ->
      ext_stmt ASEGS ASAN NX0 AsanInit.LIMIT (AN.xn ASEGS ASAN NX0) SV (argH0 APH sp rdraw argv envp uid hw) LINV FS0
      /\ emit_stmt ASEGS ASAN NX0 AsanInit.LIMIT (AN.xe ASEGS ASAN NX0) SV (argH0 APH sp rdraw argv envp uid hw) LINV FS0.




Lemma argv1_plain_gen : forall argv, valid_argv argv ->
  path_has_slash (nth 1 argv []) = false /\ path_eqb (nth 1 argv []) dotdot_path = false.
Proof.
  intros argv (_ & _ & _ & _ & Htl). destruct argv as [|a0 [|a1 r]]; [split; reflexivity | split; reflexivity |].
  cbn [tl] in Htl. apply Forall_cons_iff in Htl as [[H1 H2] _]. cbn [nth]. split; [exact H1 | exact H2].
Qed.

Section MC.
  Variable LINV : (word -> option byte) -> Prop.
  Hypothesis HLINV : LINV_STMT LINV.
  Hypothesis XALL : XALL_STMT LINV.
  Hypothesis XLIB : XLIB_STMT LINV.
  Hypothesis XARG : XARG_STMT LINV.
  Hypothesis XRP : XRP_STMT LINV.
  
  Variable sp : word.
  Variable rdraw : EntryDraw.   
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.               
  Variables nofile sigmask : word.
  Variable abt : bool.    
  Variable groups : list word.
  Variable net : NetQueue.
  Variable ur : InputStream.   
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.   (* [comment removed for export] *)

  #[local] Notation c := (content_of argv fs).
  #[local] Notation SINV := (SINVm APH sp rdraw brk0 argv envp uid hw (content_of argv fs)).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Let argH_high := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let argH_agree := argH0_agree APH sp rdraw argv envp uid hw.
  Let nx0_ge : APS.nx0_ok NX0 := Nat.le_refl NX0.   (* [comment removed for export] *)
  Let LINV_init := proj1 HLINV.
  Let LINV_frame := proj2 HLINV.
  Lemma mc_SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros. eapply SINVm_frame; eassumption. Qed.
  Lemma mc_SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros. eapply SINVm_agree; eassumption. Qed.
  Lemma mc_SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
  Proof. intros E M H. eapply SINVm_SINV0. exact H. Qed.
  Lemma mc_argH_top : forall E M (a : word), SINV E M -> argH E a = true -> bv_unsigned (edenot E e_sp0) <= bv_unsigned a.   (* [comment removed for export] *)
  Proof. intros E M a HS Ha. exact (argH0_top APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M a (mc_SINV_SINV0 E M HS) Ha). Qed.
  Lemma mc_SINV_SINV1 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M /\ eb E 1%nat = nth 0 argv [] /\ eb E 2%nat = nth 1 argv [].
  Proof. intros E M (H0 & H1 & H2 & _). split; [exact H0|]. split; [exact H1 | exact H2]. Qed.

  (* [comment removed for export] *)
  Lemma argv1_plain : path_has_slash (nth 1 argv []) = false /\ path_eqb (nth 1 argv []) dotdot_path = false.
  Proof. exact (argv1_plain_gen argv Hva). Qed.
  Lemma not_dirref : nth 1 argv [] <> Uapi.dot_path -> path_is_dirref (nth 1 argv []) = false.
  Proof.
    intros Hne. unfold path_is_dirref. rewrite (proj2 argv1_plain), orb_false_r.
    destruct (path_eqb (nth 1 argv []) Uapi.dot_path) eqn:E; [|reflexivity]. exfalso. apply Hne. apply path_eqb_eq. exact E.
  Qed.
  Lemma H_class_conv : forall T (SV : env -> (word -> option byte) -> Prop), H_class_prop T argv fs SV ->
    match ION.io_open T with
    | ION.ONone => True
    | ION.OTooLong => (4096 <= length (nth 1 argv []))%nat
    | ION.ONoEnt => nth 1 argv [] = [] \/ (path_has_slash (nth 1 argv []) = false /\ path_is_dirref (nth 1 argv []) = false /\ (length (nth 1 argv []) <= 4095)%nat /\ fs_lookup fs (nth 1 argv []) = None)
    | ION.ODir => nth 1 argv [] = Uapi.dot_path
    | ION.OFile lo hi => exists c, nth 1 argv [] <> [] /\ path_has_slash (nth 1 argv []) = false /\ path_is_dirref (nth 1 argv []) = false /\ (length (nth 1 argv []) <= 4095)%nat /\ fs_lookup fs (nth 1 argv []) = Some c
                     /\ lo <= flen c <= hi
                     /\ (forall E M, SV E M -> forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (ION.io_blob T + j)%nat = chunk j c)
                     /\ ION.hdr_ok T c
    end.
  Proof.
    intros T SV H. unfold H_class_prop in H. pose proof (proj1 argv1_plain) as Hs.
    destruct (ION.io_open T); try exact H.
    - destruct H as [H|(H1 & H2 & H3)]; [left; exact H | right]. split; [exact Hs|]. split; [apply not_dirref; exact H1|]. split; [exact H2 | exact H3].
    - destruct H as (c0 & H1 & H2 & H3 & H4 & H5 & H6 & H7). exists c0.
      split; [exact H1|]. split; [exact Hs|]. split; [apply not_dirref; exact H2|]. split; [exact H3|]. split; [exact H4|].
      split; [exact H5|]. split; [exact H6 | exact H7].
  Qed.

  (* [comment removed for export] *)
  Lemma mc_sys_sound : forall {fx : FPState} y, sys_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs y.
  Proof. intros fx. exact (AsanNodesMmB.node_sys_sound ASEGS ASAN NX0 LIM SINV argH LINV fs asan_res_len asan_hull_ok asan_shadow_ok argH_agree mc_argH_top nx0_ge mc_SINV_frame mc_SINV_agree LINV_frame asan_lfp_hull). Qed.
  Lemma mc_brk2_sound : forall {fx : FPState}, brk2_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs.
  Proof. intros fx. exact (AsanNodesMmB.node_brk2_sound ASEGS ASAN NX0 LIM SINV argH LINV fs asan_in_hull asan_hull_ok asan_shadow_ok argH_high mc_argH_top mc_SINV_frame LINV_frame asan_lfp_hull). Qed.
  Lemma mc_mmap2_sound : forall {fx : FPState}, mm2_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs (node_mmap2 ASAN NX0 LIM).
  Proof. intros fx. exact (node_mmap2_sound_OBL ASEGS ASAN NX0 LIM SINV argH LINV fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok argH_high argH_agree mc_SINV_frame mc_SINV_agree mc_argH_top nx0_ge asan_res_chain LINV_frame asan_lfp_hull). Qed.
  Lemma mc_mmapin_sound : forall {fx : FPState} (hole : bool), mm3_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs (node_mmapin ASAN LIM hole).
  Proof. intros fx. exact (node_mmapin_sound_OBL ASEGS ASAN NX0 LIM SINV argH LINV fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok argH_high argH_agree mc_SINV_frame mc_SINV_agree mc_argH_top nx0_ge asan_res_chain LINV_frame asan_lfp_hull). Qed.
  Lemma mc_mprotect2_sound : forall {fx : FPState}, mm2_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs (node_mprotect2 ASAN LIM).
  Proof. intros fx. exact (node_mprotect2_sound_OBL ASEGS ASAN NX0 LIM SINV argH LINV fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok argH_high argH_agree mc_SINV_frame mc_SINV_agree mc_argH_top nx0_ge asan_res_chain LINV_frame asan_lfp_hull). Qed.
  Lemma mc_exit_sound : forall {fx : FPState}, exit_stmt ASEGS ASAN LIM SINV argH LINV fs.
  Proof. intros fx. exact (AsanNodesMmB.node_exit_sound ASEGS ASAN LIM SINV argH LINV fs). Qed.

  (* [comment removed for export] *)
  Lemma mc_x_sound : forall {fx : FPState} x, x_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs x.
  Proof. intros fx. exact (XALL fx sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV mc_SINV_SINV0 mc_SINV_frame mc_SINV_agree). Qed.
  Lemma mc_lib_sound : lib_stmt ASEGS ASAN NX0 LIM (XLm ASEGS ASAN NX0) SINV argH LINV fs.
  Proof. exact (XLIB sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV mc_SINV_SINV0 mc_SINV_frame mc_SINV_agree). Qed.

  (* [comment removed for export] *)
  Lemma mc_segs_wr : AsanPlanSoundSums.APSX.segs_wr_ok ASEGS.
  Proof.
    assert (H : forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool ASEGS = true) by (vm_compute; reflexivity).
    intros seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs. rewrite Hw in Hs. exact Hs.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_xn_sound : forall {fx : FPState} T, H_class_prop T argv fs SINV -> ext_stmt ASEGS ASAN NX0 LIM (XNm ASEGS ASAN NX0 RPN.RP_ASAN T) SINV argH LINV fs.
  Proof.
    intros fx T HT id args. unfold XNm.
    destruct (Nat.ltb id 10); [|destruct (Nat.ltb id 100); [|destruct (Nat.ltb id 110); [|destruct (Nat.eqb id 113); [|destruct (Nat.leb 200 id); [destruct (if Nat.eqb id 215 then true else Nat.leb id 205)|]]]]].
    - exact (proj1 (XARG fx sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree) id args).
    - exact (io_ext_stmt_init ASEGS ASAN APH asan_in_hull asan_hull_ok asan_shadow_ok sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit
               SINV mc_SINV_SINV0 mc_SINV_frame mc_SINV_agree LINV LINV_frame T (H_class_conv T SINV HT) id args).
    - exact (XRP fx NX0 LIM SINV argH argH_high argH_agree mc_argH_top nx0_ge mc_SINV_frame mc_SINV_agree fs id args).
    - exact (AsanNodesCanonSound.can_xn_sound ASEGS ASAN NX0 LIM SINV argH LINV fs args).   (* [comment removed for export] *)
    - exact (AsanNodesRJoinSound.xrj_xn_sound ASEGS ASAN NX0 LIM SINV argH LINV fs nx0_ge argH_agree mc_SINV_agree mc_segs_wr id args).   (* [comment removed for export] *)
    - exact (AsanNodesWorldSound.xwd_xn_sound ASEGS ASAN NX0 LIM SINV argH LINV fs nx0_ge argH_agree mc_SINV_agree id args).   (* [comment removed for export] *)
    - intros cs cs' E R FULL model TT _ _ H. discriminate H.
  Qed.

  Lemma mc_xe_sound : forall {fx : FPState}, emit_stmt ASEGS ASAN NX0 LIM (XEm ASEGS ASAN NX0) SINV argH LINV fs.
  Proof. intros fx. exact (proj2 (XARG fx sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV mc_SINV_SINV1 mc_SINV_frame mc_SINV_agree)). Qed.

  Lemma mc_xb_sound : forall {fx : FPState} T, H_class_prop T argv fs SINV -> ext2_stmt ASEGS ASAN NX0 LIM (XBm ASEGS NX0 T) SINV argH LINV fs.
  Proof.
    intros fx T HT.
    exact (io_ext2_stmt_init ASEGS ASAN APH sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit
             SINV mc_SINV_SINV0 mc_SINV_frame mc_SINV_agree LINV LINV_frame T (H_class_conv T SINV HT)).
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
    (* [comment removed for export] *)
    Variable IT0 : itab.
    Hypothesis IT0_ok : itab_sound ASEGS IT0.
    Variable HS_asan : nat -> option acs.
    Variable startup_plan : plan.
    Variable startup_shape : shape.
    Variables KC0 BFUEL FUEL : nat.
    Variable TT0 : nat -> option (acs * plan * shape).   (* [comment removed for export] *)
    Hypothesis startup_cert :
      check ASEGS IT0 ASAN NX0 LIM (RPN.xn ASEGS ASAN NX0 RPN.RP_ASAN) XE0 XB0 XL0 HS_asan HL0 TT0 KC0 BFUEL FUEL None asan_init startup_plan = COk startup_shape.
    Hypothesis TT0_ok : AP.tails_ok0 ASEGS IT0 ASAN NX0 LIM TT0 KC0.   (* [comment removed for export] *)
    Hypothesis startup_all_holes : all_holes startup_shape = true.
    Hypothesis HSA_noblob : forall h ch, HS_asan h = Some ch -> acs_noblob ch = true.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    Variables KCm BFUELm FUELm : nat.
    Variable ITm : itab.
    Variable TTm : nat -> option (acs * plan * shape).
    Hypothesis ITm_ok : itab_sound ASEGS ITm.
    Hypothesis TTm_ok : tails_all_ok KCm BFUELm FUELm ITm TTm.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    Variable TREE : nat -> nat -> mtree.
    Hypothesis TREES : forall h ch i, HS_asan h = Some ch -> (i < 6)%nat ->
      mtree_ok KCm BFUELm FUELm ITm TTm 0 0 (HSA HS_asan h) (root_class i) (TREE h i) = true.

    Theorem asan_realizes_spec_closed :
      srealizes ASEGS (init_config ASEGS ImgA.M.init_pc APH sp brk0 mbase rdraw LIM
                                   (AsanInit.inp argv envp fs stdin uid gid hw groups net ur nofile sigmask abt))
                (spec argv fs).
    Proof.
      exact (asan_realizes_spec LINV HLINV XALL XRP sp rdraw brk0 mbase argv envp fs stdin uid gid hw nofile sigmask abt groups net ur Hsp Hbrk Hva Hve Hfit Huid Hhw
               IT0 IT0_ok HS_asan startup_plan startup_shape KC0 BFUEL FUEL TT0 startup_cert TT0_ok startup_all_holes HSA_noblob
               KCm BFUELm FUELm ITm TTm ITm_ok TTm_ok
               (@mc_sys_sound) (@mc_brk2_sound) (@mc_mmap2_sound) (@mc_mmapin_sound) (@mc_mprotect2_sound) (@mc_exit_sound) (@mc_x_sound)
               (@mc_xn_sound) (@mc_xe_sound) (@mc_xb_sound) mc_lib_sound mc_VF TREE TREES).
    Qed.
  End Closed.
End MC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
