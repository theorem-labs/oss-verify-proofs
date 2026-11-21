(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the process input's new fields; the start-up taken per CONFIG_RSEQ value; the SIGPIPE disposition). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec ShapeAlg SpinAlg AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages BothPlanImages AsanPlanImagesInit AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanStartup BothTableL AsanNodesRP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LINV_STMT_B (LINV : (word -> option byte) -> Prop) : Prop :=
  (forall M : word -> option byte, (forall a : word, in_lfp BOTHL (bv_unsigned a) = true -> M a = None) -> LINV M)
  /\ (forall M M' : word -> option byte, (forall a : word, in_lfp BOTHL (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M').

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition XALL_STMT_B (LINV : (word -> option byte) -> Prop) : Prop :=
  forall (fx : FPState) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (FS0 : Fs.Fs)
    (apc : N) (mbase : word) (fs : Fs.Fs) (stdin : InputStream) (gid : word) (groups : list word) (net : NetQueue) (ur : InputStream) (kern : KernelBuild) (execfn : list byte) (nofile sigmask : word) (abt sdf : bool),
    valid_sp sp -> valid_argv argv -> valid_envp envp ->
    forall uid hw : word, entry_stack_fits sp argv envp ->
    in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) = recorded_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)) ->
    (* twin of AsanStartup.v:62-67 *)
    valid_launch (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) ->
    forall SINV : env -> (word -> option byte) -> Prop,
      (forall E M, SINV E M -> SINV0 BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf E M) ->
      (forall E M M', (forall a, argH0 sp rdraw argv envp kern execfn E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
      (forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M) ->
      forall x, x_stmt BSEGS BOTHL NX0 AsanInit.LIMIT SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0 x.

(* [comment removed for export] *)
Definition XRP_STMT_B (LINV : (word -> option byte) -> Prop) : Prop :=
  forall (fx : FPState) (nx0 : nat) (LIMIT : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool),
    (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
    (forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a) ->
    (forall E M (a : word), SINV E M -> argH E a = true -> bv_unsigned (edenot E e_sp0) <= bv_unsigned a) ->   (* [comment removed for export] *)
    APS.nx0_ok nx0 ->                                                                                               (* [comment removed for export] *)
    (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
    (forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M) ->
    forall FS0 : Fs.Fs,
      ext_stmt BSEGS BOTHL nx0 LIMIT (RPN.xn BSEGS BOTHL nx0 RPN.RP_BOTH) SINV argH LINV FS0.

Section StartupB.
  Variable LINV : (word -> option byte) -> Prop.
  Hypothesis HLINV : LINV_STMT_B LINV.
  Hypothesis XALL : XALL_STMT_B LINV.
  Hypothesis XRP : XRP_STMT_B LINV.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.               (* [comment removed for export] *)
  Variables nofile sigmask : word.
  Variables abt sdf : bool.  (* [comment removed for export] *)  (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  Variable ur : InputStream.   
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.   (* [comment removed for export] *)

  Variable apc : N.
  (* twin of AsanStartup.v:109-115 *)
  Hypothesis Hapc : Z.of_N apc = a_entry BOTHL.
  Variable kern : KernelBuild.
  Variable execfn : list byte.
  Hypothesis Hkernel : in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) = recorded_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)).
  Hypothesis Hlaunch : valid_launch (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf).
  #[local] Notation SINV := (SINV0 BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf).
  #[local] Notation argH := (argH0 sp rdraw argv envp kern execfn).
  #[local] Notation E0a := (E0 sp rdraw brk0 argv envp uid gid hw kern execfn).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound BSEGS IT0.
  (* [comment removed for export] *)
  Variable HS_both : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan : Z -> plan.   (* LPS 727298f3: per CONFIG_RSEQ value, as AsanStartup *)
  Variable startup_shape : Z -> shape.   (* LPS 727298f3: per CONFIG_RSEQ value, as AsanStartup *)
  Variables KC0 BFUEL FUEL : nat.
  (* [comment removed for export] *)
  Variable TT0 : nat -> option (acs * plan * shape).
  Hypothesis startup_cert : forall r, 0 <= r <= 1 ->
    check BSEGS IT0 BOTHL NX0 LIM (RPN.xn BSEGS BOTHL NX0 RPN.RP_BOTH) XE0 XB0 XL0 HS_both HL0 TT0 KC0 BFUEL FUEL None (both_initL_r r) (startup_plan r) = COk (startup_shape r).
  Hypothesis TT0_ok : AP.tails_ok0 BSEGS IT0 BOTHL NX0 LIM TT0 KC0.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_lv : forall h1 h2 E fs', HOLES h1 E fs' = HOLES h2 E fs'.   (* [comment removed for export] *)
  Hypothesis HOLES_sound : forall (fx : FPState), frm_zero fx -> holes_stmt BSEGS BOTHL LIM HS_both SINV argH LINV HOLES fs.

  (* [comment removed for export] *)
  Let AH := argH0_high apc sp rdraw argv envp kern execfn Hsp Hva.
  Let AA := argH0_agree sp rdraw argv envp kern execfn.
  Let AT := argH0_top BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn Hsp Hva Hve Hfit nofile sigmask abt sdf Hlau.   (* [comment removed for export] *)
  Let SF := SINV0_frame BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf.
  Let SA := SINV0_agree BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf.
  Let NG : APS.nx0_ok NX0 := Nat.le_refl NX0.                                   (* [comment removed for export] *)
  Let LI := proj1 HLINV.
  Let LF := proj2 HLINV.

  Theorem both_startup :
    srealizes BSEGS (init_config BSEGS apc BPH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf))
              (sd HOLES t_nil E0a fs (startup_shape (rseq_z (kb_rseq kern)))).
  Proof.
    pose proof bothL_img_facts as IMG.
    rewrite (init_cfg_eq BSEGS BOTHL BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn Hapc nofile sigmask abt sdf).
    pose proof (init_r_cs_ok BSEGS BOTHL BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn IMG Hapc Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw LINV LI bothL_lfp_hull nofile sigmask abt sdf Hkernel Hlaunch Hlau) as HC.
    pose proof (rseq_z_range (kb_rseq kern)) as Hrz.
    pose proof (check_sound BSEGS IT0 IT0_ok BOTHL NX0 LIM HS_both HL0 (RPN.xn BSEGS BOTHL NX0 RPN.RP_BOTH) XE0 XB0 XL0
              both_wx bothL_in_hull bothL_hull_ok bothL_shadow_ok SINV argH AH AA NG SF SA LINV LF
              HOLES HOLES_agree HOLES_nil (fun h1 h2 L E fs' _ _ => HOLES_lv h1 h2 E fs') fs KC0 TT0 (proj1 TT0_ok)
              (fun fx => AsanNodesMmB.node_sys_sound (fx:=fx) BSEGS BOTHL NX0 LIM SINV argH LINV fs bothL_res_len bothL_hull_ok bothL_shadow_ok AA AT NG SF SA LF bothL_lfp_hull)
              (fun fx => AsanNodesMmB.node_brk2_sound (fx:=fx) BSEGS BOTHL NX0 LIM SINV argH LINV fs bothL_in_hull bothL_hull_ok bothL_shadow_ok AH AT SF LF bothL_lfp_hull)
              (fun fx => AsanNodesMmB.node_munmap2_sound (fx:=fx) BSEGS BOTHL NX0 LIM SINV argH LINV bothL_res_len bothL_hull_ok bothL_shadow_ok AA AT NG SF SA LF bothL_lfp_hull fs)
              (fun fx => node_mmap2_sound_OBL (fx:=fx) BSEGS BOTHL NX0 LIM SINV argH LINV fs bothL_in_hull bothL_res_len bothL_res_hull bothL_hull_ok bothL_shadow_ok AH AA SF SA AT NG bothL_res_chain LF bothL_lfp_hull)
              (fun fx => node_mmapin_sound_OBL (fx:=fx) BSEGS BOTHL NX0 LIM SINV argH LINV fs bothL_in_hull bothL_res_len bothL_res_hull bothL_hull_ok bothL_shadow_ok AH AA SF SA AT NG bothL_res_chain LF bothL_lfp_hull)
              (fun fx => node_mprotect2_sound_OBL (fx:=fx) BSEGS BOTHL NX0 LIM SINV argH LINV fs bothL_in_hull bothL_res_len bothL_res_hull bothL_hull_ok bothL_shadow_ok AH AA SF SA AT NG bothL_res_chain LF bothL_lfp_hull)
              (fun fx => AsanNodesMmB.node_exit_sound (fx:=fx) BSEGS BOTHL LIM SINV argH LINV fs)
              (fun fx => XALL fx sp rdraw brk0 argv envp fs apc mbase fs stdin gid groups net ur kern execfn nofile sigmask abt sdf Hsp Hva Hve uid hw Hfit Hkernel Hlaunch Hlau SINV (fun E M H => H) SF SA)
              (fun fx => node_join_sound (fx:=fx) BSEGS BOTHL NX0 LIM SINV argH LINV fs)
              (AsanNodesMmLib.node_zones_sound BSEGS BOTHL LIM SINV argH LINV fs bothL_res_len bothL_hull_ok bothL_res_chain)   (* [comment removed for export] *)
              (AsanNodesMmLib.node_zonehull_sound BSEGS BOTHL LIM SINV argH LINV fs bothL_res_len bothL_hull_ok bothL_res_chain)   (* [comment removed for export] *)
              (fun fx => XRP fx NX0 LIM SINV argH AH AA AT NG SF SA fs) (fun fx => XE0_sound fx _ _ _ _ _ _ _ _) (fun fx => XB0_sound fx _ _ _ _ _ _ _ _)
              (XL0_sound _ _ _ _ _ _ _ _)
              (fun fx => HOLES_sound fx)
              (fun fx _ t T p s Ht Hif => False_rect _ (eq_true_false_abs _ Hif (proj2 TT0_ok t T p s Ht)))   (* [comment removed for export] *)
              FUEL BFUEL None (startup_plan (rseq_z (kb_rseq kern))) (both_initL_r (rseq_z (kb_rseq kern))) (startup_shape (rseq_z (kb_rseq kern)))
              (startup_cert _ Hrz)
              fx0 frm_zero_fx0 _ _ _ _ t_nil HC I eq_refl) as R.
    exact R.
  Qed.
End StartupB.
