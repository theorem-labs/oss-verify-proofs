(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec ShapeAlg SpinAlg AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanPlanImagesInit AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanNodesRP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
Definition XL0 (cs : acs) : option acs := None.   (* [comment removed for export] *)
Definition HL0 (h : nat) : option nat := Some 0%nat.    (* [comment removed for export] *)

Lemma XN0_sound : forall (fx : FPState) SEGS A nx0 LIMIT SINV argH LINV FS0, ext_stmt SEGS A nx0 LIMIT XN0 SINV argH LINV FS0.
Proof. intros ? ? ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall (fx : FPState) SEGS A nx0 LIMIT SINV argH LINV FS0, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH LINV FS0.
Proof. intros ? ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall (fx : FPState) SEGS A nx0 LIMIT SINV argH LINV FS0, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH LINV FS0.
Proof. intros ? ? ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.
Lemma XL0_sound : forall SEGS A nx0 LIMIT SINV argH LINV FS0, lib_stmt SEGS A nx0 LIMIT XL0 SINV argH LINV FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros fx _ cs cs' E R FULL model T _ H. discriminate H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LINV_STMT (LINV : (word -> option byte) -> Prop) : Prop :=
  (forall M : word -> option byte, (forall a : word, in_lfp ASAN (bv_unsigned a) = true -> M a = None) -> LINV M)
  /\ (forall M M' : word -> option byte, (forall a : word, in_lfp ASAN (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M').

(* [comment removed for export] *)
Lemma asan_lfp_hull : forall z, in_lfp ASAN z = true -> img_lo ASAN <= z < img_hi ASAN.
Proof.
  intros z H. unfold in_lfp in H. apply existsb_exists in H as (r & Hin & Hr).
  cbn [lib_fp ASAN] in Hin.
  repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; apply andb_prop in Hr as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; cbn [img_lo img_hi ASAN]; lia|]).
  destruct Hin.
Qed.

(* [comment removed for export] *)
Definition XALL_STMT (LINV : (word -> option byte) -> Prop) : Prop :=
  forall (fx : FPState) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (FS0 : Fs.Fs),
    valid_sp sp -> valid_argv argv -> valid_envp envp ->
    forall uid hw : word, entry_stack_fits sp argv envp ->
    forall SINV : env -> (word -> option byte) -> Prop,
      (forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M) ->
      (forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
      (forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M) ->
      forall x, x_stmt ASEGS ASAN NX0 AsanInit.LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) LINV FS0 x.

(* [comment removed for export] *)
Definition XRP_STMT (LINV : (word -> option byte) -> Prop) : Prop :=
  forall (fx : FPState) (nx0 : nat) (LIMIT : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool),
    (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
    (forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a) ->
    (forall E M (a : word), SINV E M -> argH E a = true -> bv_unsigned (edenot E e_sp0) <= bv_unsigned a) ->   (* [comment removed for export] *)
    APS.nx0_ok nx0 ->                                                                                               (* [comment removed for export] *)
    (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
    (forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M) ->
    forall FS0 : Fs.Fs,
      ext_stmt ASEGS ASAN nx0 LIMIT (RPN.xn ASEGS ASAN nx0 RPN.RP_ASAN) SINV argH LINV FS0.

Section Startup.
  Variable LINV : (word -> option byte) -> Prop.
  Hypothesis HLINV : LINV_STMT LINV.
  Hypothesis XALL : XALL_STMT LINV.
  Hypothesis XRP : XRP_STMT LINV.   (* [comment removed for export] *)
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
  Variable abt : bool.  (* [comment removed for export] *)  (* [comment removed for export] *)
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

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (* [comment removed for export] *)
  Variable HS_asan : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  (* [comment removed for export] *)
  Variable TT0 : nat -> option (acs * plan * shape).
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN NX0 LIM (RPN.xn ASEGS ASAN NX0 RPN.RP_ASAN) XE0 XB0 XL0 HS_asan HL0 TT0 KC0 BFUEL FUEL None asan_init startup_plan = COk startup_shape.
  Hypothesis TT0_ok : AP.tails_ok0 ASEGS IT0 ASAN NX0 LIM TT0 KC0.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_lv : forall h1 h2 E fs', HOLES h1 E fs' = HOLES h2 E fs'.   (* [comment removed for export] *)
  Hypothesis HOLES_sound : forall (fx : FPState), frm_zero fx -> holes_stmt ASEGS ASAN LIM HS_asan SINV argH LINV HOLES fs.

  (* [comment removed for export] *)
  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let AT := argH0_top APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.   (* [comment removed for export] *)
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.
  Let NG : APS.nx0_ok NX0 := Nat.le_refl NX0.                                   (* [comment removed for export] *)
  Let LI := proj1 HLINV.
  Let LF := proj2 HLINV.

  Theorem asan_startup :
    srealizes ASEGS (init_config ASEGS ImgA.M.init_pc APH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp fs stdin uid gid hw groups net ur nofile sigmask abt))
              (sd HOLES t_nil E0a fs startup_shape).
  Proof.
    pose proof asan_img_facts as IMG.
    rewrite (init_cfg_eq ASEGS ASAN APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur nofile sigmask abt ImgA.M.init_pc eq_refl).
    pose proof (init_cs_ok ASEGS ASAN APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur IMG Hsp Hbrk Hva Hve Hfit Huid Hhw LINV LI asan_lfp_hull nofile sigmask abt) as HC.
    pose proof (check_sound ASEGS IT0 IT0_ok ASAN NX0 LIM HS_asan HL0 (RPN.xn ASEGS ASAN NX0 RPN.RP_ASAN) XE0 XB0 XL0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA NG SF SA LINV LF
              HOLES HOLES_agree HOLES_nil (fun h1 h2 L E fs' _ _ => HOLES_lv h1 h2 E fs') fs KC0 TT0 (proj1 TT0_ok)
              (fun fx => AsanNodesMmB.node_sys_sound (fx:=fx) ASEGS ASAN NX0 LIM SINV argH LINV fs asan_res_len asan_hull_ok asan_shadow_ok AA AT NG SF SA LF asan_lfp_hull)
              (fun fx => AsanNodesMmB.node_brk2_sound (fx:=fx) ASEGS ASAN NX0 LIM SINV argH LINV fs asan_in_hull asan_hull_ok asan_shadow_ok AH AT SF LF asan_lfp_hull)
              (fun fx => node_mmap2_sound_OBL (fx:=fx) ASEGS ASAN NX0 LIM SINV argH LINV fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA AT NG asan_res_chain LF asan_lfp_hull)
              (fun fx => node_mmapin_sound_OBL (fx:=fx) ASEGS ASAN NX0 LIM SINV argH LINV fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA AT NG asan_res_chain LF asan_lfp_hull)
              (fun fx => node_mprotect2_sound_OBL (fx:=fx) ASEGS ASAN NX0 LIM SINV argH LINV fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA AT NG asan_res_chain LF asan_lfp_hull)
              (fun fx => AsanNodesMmB.node_exit_sound (fx:=fx) ASEGS ASAN LIM SINV argH LINV fs)
              (fun fx => XALL fx sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF SA)
              (fun fx => node_join_sound (fx:=fx) ASEGS ASAN NX0 LIM SINV argH LINV fs)
              (AsanNodesMmLib.node_zones_sound ASEGS ASAN LIM SINV argH LINV fs asan_res_len asan_hull_ok asan_res_chain)   (* [comment removed for export] *)
              (AsanNodesMmLib.node_zonehull_sound ASEGS ASAN LIM SINV argH LINV fs asan_res_len asan_hull_ok asan_res_chain)   (* [comment removed for export] *)
              (fun fx => XRP fx NX0 LIM SINV argH AH AA AT NG SF SA fs) (fun fx => XE0_sound fx _ _ _ _ _ _ _ _) (fun fx => XB0_sound fx _ _ _ _ _ _ _ _)
              (XL0_sound _ _ _ _ _ _ _ _)
              (fun fx => HOLES_sound fx)
              (fun fx _ t T p s Ht Hif => False_rect _ (eq_true_false_abs _ Hif (proj2 TT0_ok t T p s Ht)))   (* [comment removed for export] *)
              FUEL BFUEL None startup_plan asan_init startup_shape startup_cert
              fx0 frm_zero_fx0 _ _ _ _ t_nil HC I eq_refl) as R.
    exact R.
  Qed.
End Startup.
