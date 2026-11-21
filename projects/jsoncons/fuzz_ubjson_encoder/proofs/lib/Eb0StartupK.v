(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the SIGPIPE disposition as a launch variable; the new launch (process input, auxv, group id, exec file name); the CONFIG_RSEQ flag; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Bo0StartupK.v, 79 lines within its lines 48-291. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg AgentLib Hoare SumsLib
  AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanPlanSound2K AsanPlanSoundSumsK Eb0PlanImagesK AsanInitK
  AsanNodesIfaceK AsanNodesMmLibK AsanNodesMmAK AsanNodesMmBK AsanNodesExtraDefsK AsanNodesExtraK.
Import ListNotations.
Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Open Scope Z_scope.

Section As0.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.

Hypothesis AIMW0 : aim_spec ASEGS0 AIM_ASAN0.

Hypothesis SMEARW0 : forall (mem rom : word -> option byte) regs (x : word),
    getr regs 10 = x -> (2 ^ 46 <= bv_unsigned x < 2 ^ 47)%Z ->
    exists regs',
      msteps ASEGS0 (mkst regs (at_ (Z_to_bv 64 X_MAXVA_ASAN0) 0) mem rom) (mkst regs' (at_ (Z_to_bv 64 X_MAXVA_ASAN0) 180) mem rom)
      /\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
      /\ getr regs' 11 = Z_to_bv 64 18446744073709551615 /\ getr regs' 12 = Z_to_bv 64 3689348814741910323
      /\ getr regs' 13 = Z_to_bv 64 1085102592571150095 /\ getr regs' 14 = Z_to_bv 64 72340172838076673
      /\ getr regs' 15 = Z_to_bv 64 9223301668110598144
      /\ regs_agree (fun r : bv 5 => In r ([10; 11; 12; 13; 14; 15]%bv : list (bv 5))) regs regs'.

Lemma XE0_sound : forall LIMIT SINV argH FS0, emit_stmt ASEGS0 scfg ASAN0 NX0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall LIMIT SINV argH FS0, ext2_stmt ASEGS0 scfg ASAN0 NX0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

Section Hooks.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Theorem XN0_sound : ext_stmt ASEGS0 scfg ASAN0 NX0 LIMIT XN0 SINV argH FS0.
  Proof.
    intros id args cs cs' E R FULL model T HC Hpre Hn Hk. unfold XN0 in Hn.
    destruct (Nat.eqb id 95).
    { exact (xn_addrisinmem_sound ASEGS0 scfg ASAN0 NX0 LIMIT SINV argH FS0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok argH_high e_sp0_init argH_agree SINV_frame SINV_agree
               AIM_ASAN0 AIMW0 args cs cs' E R FULL model T HC Hpre Hn Hk). }
    destruct (Nat.eqb id 97).
    { change X_MAXVA_ASAN0 with (bv_unsigned (Z_to_bv 64 X_MAXVA_ASAN0)) in Hn.
      exact (xn_smearva_sound ASEGS0 scfg ASAN0 NX0 LIMIT SINV argH FS0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok SINV_frame
               (Z_to_bv 64 X_MAXVA_ASAN0) SMEARW0 args cs cs' E R FULL model T HC Hpre Hn Hk). }
    destruct (Nat.eqb id 98); [|discriminate Hn].
    exact (xn_absbytes_sound ASEGS0 scfg ASAN0 NX0 LIMIT SINV argH FS0 e_sp0_init argH_agree SINV_agree asan0_segs_wr args cs cs' E R FULL model T HC Hpre Hn Hk).
  Qed.
End Hooks.

Section Stage.

  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  (* [AsanInitK]'s [Section Init] is parameterised by the full
     [State.mkProcInput_full] field list, so [SINV0]/[argH0]/[E0] discharge all
     fifteen of [AsanInitK.inp]'s arguments plus [mbase] and [apc].  Same block
     as the already-migrated [HandoffBridgeK.v:619-629]. *)
  Variable mbase : word.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.
  Variable apc : N.
  (* the run's CONFIG_RSEQ flag as 0 or 1, [AsanPlanK]'s slot 6 since the auxv's
     size decides where the strings sit ([AsanPlanK.v:30-33]); a certificate is
     checked at one literal value, so this stays free here and is case-split
     where a closed certificate is handed in. *)
  Variable rz : Z.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.

  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation LIM := AsanInitK.LIMIT.
  Let AH := argH0_high sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva.
  Let AA := argH0_agree sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf.
  Let SF := SINV0_frame APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc.
  Let SA := SINV0_agree APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS0 IT0.

  Variable HS : nat -> option acs.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  Definition HOLES (h : nat) (E : env) (fs' : Fs.Fs) : TSet := T fs'.
  Lemma HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Proof. reflexivity. Qed.
  Lemma HOLES_nil : forall h E fs', HOLES h E fs' [].
  Proof. intros. apply T_nil. Qed.
  Lemma HOLES_flat : forall h h' E E' fs', HOLES h E fs' = HOLES h' E' fs'.
  Proof. reflexivity. Qed.
  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH HOLES fs.
  Hypothesis X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 LIM rz SINV argH fs x.
  Variables KC0 BFUEL FUEL : nat.

  Theorem stage_sound : forall p cs0 s,
    check ASEGS0 IT0 ASAN0 NX0 LIM rz XN0 XE0 XB0 HS KC0 BFUEL FUEL None cs0 p = COk s ->
    forall E R FULL model, cs_ok ASEGS0 ASAN0 LIM SINV argH fs E cs0 R FULL model ->
      srealizes ASEGS0 scfg (cfg_of ASEGS0 R (pc cs0) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros p cs0 s Hcert E R FULL model HC.
    exact (check_sound ASEGS0 scfg IT0 IT0_ok ASAN0 NX0 LIM rz HS XN0 XE0 XB0
             Asan0_wx_nowrap asan0_in_hull asan0_hull_ok asan0_shadow_ok SINV argH AH e_sp0_init AA SF SA
             HOLES HOLES_agree HOLES_nil HOLES_flat fs KC0
             (AsanNodesMmBK.node_sys_sound ASEGS0 scfg Halloc ASAN0 NX0 LIM SINV argH fs asan0_res_len asan0_res_hull asan0_hull_ok asan0_shadow_ok AH e_sp0_init AA SF SA)
             (AsanNodesMmBK.node_brk2_sound ASEGS0 scfg Halloc ASAN0 NX0 LIM SINV argH fs asan0_in_hull asan0_res_len asan0_res_hull asan0_hull_ok asan0_shadow_ok AH SF)
             (node_mmap2_sound_OBL ASEGS0 scfg ASAN0 NX0 LIM rz SINV argH fs Halloc Asan0_wx_nowrap asan0_in_hull asan0_res_len asan0_res_hull asan0_hull_ok asan0_shadow_ok AH e_sp0_init AA SF SA asan0_hull_tiled asan0_hull_lt)
             (node_mmapin_sound_OBL ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs Halloc Asan0_wx_nowrap asan0_in_hull asan0_res_len asan0_res_hull asan0_hull_ok asan0_shadow_ok AH e_sp0_init AA SF SA asan0_hull_tiled asan0_hull_lt)
             (node_mprotect2_sound_OBL ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs Halloc Asan0_wx_nowrap asan0_in_hull asan0_res_len asan0_res_hull asan0_hull_ok asan0_shadow_ok AH e_sp0_init AA SF SA asan0_hull_tiled asan0_hull_lt)
             (AsanNodesMmBK.node_exit_sound ASEGS0 scfg ASAN0 LIM SINV argH fs)
             X_ALL
             (node_join_sound ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs)
             (XN0_sound LIM SINV argH fs AH AA SF SA) (XE0_sound _ _ _ _) (XB0_sound _ _ _ _)
             HS_sound FUEL BFUEL None p cs0 s Hcert
             E R FULL model t_nil HC I eq_refl).
  Qed.

  Corollary stage_hole : forall p cs0 s,
    check ASEGS0 IT0 ASAN0 NX0 LIM rz XN0 XE0 XB0 HS KC0 BFUEL FUEL None cs0 p = COk s -> hole_only s = true ->
    forall E R FULL model, cs_ok ASEGS0 ASAN0 LIM SINV argH fs E cs0 R FULL model ->
      srealizes ASEGS0 scfg (cfg_of ASEGS0 R (pc cs0) FULL model) (T (m_fs model)).
  Proof.
    intros p cs0 s Hcert Hho E R FULL model HC.
    apply (srz_conseq ASEGS0 scfg _ (sd HOLES t_nil E (m_fs model) s)); [exact (stage_sound p cs0 s Hcert E R FULL model HC)|].
    exact (hole_only_den NX0 HS XN0 XE0 XB0 HOLES HOLES_flat t_nil E (m_fs model) s Hho).
  Qed.

  Lemma holes_stmt_ext : forall JS : nat -> option acs,
    (forall h c, JS h = Some c ->
       forall E R FULL model, cs_ok ASEGS0 ASAN0 LIM SINV argH fs E c R FULL model ->
         srealizes ASEGS0 scfg (cfg_of ASEGS0 R (pc c) FULL model) (T (m_fs model))) ->
    holes_stmt ASEGS0 scfg ASAN0 LIM (hs_ext HS JS) SINV argH HOLES fs.
  Proof.
    intros JS HJ h ch Hh E R FULL model HC. unfold hs_ext in Hh. unfold HOLES.
    destruct (JS h) as [c|] eqn:Ej.
    - injection Hh as <-. exact (HJ h c Ej E R FULL model HC).
    - exact (HS_sound h ch Hh E R FULL model HC).
  Qed.
End Stage.

Section Startup.

  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool. Variable ur : InputStream.
  (* The kernel build and the exec file name are the two places of
     [State.mkProcInput_full] this cone leaves free; see [AsanInitK.inp]. *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.
  (* [AsanInitK.SINV0] reads [apc] through [entryw]; [rz] is [AsanPlanK]'s
     slot 6, the run's CONFIG_RSEQ flag. *)
  Variable apc : N.
  Variable rz : Z.
  (* [apc] is the image's ELF entry; the callers instantiate it with the image's init_pc
     and discharge this by computation. *)
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN0.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  Hypothesis Hlaunch : valid_launch (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  (* The certificate is checked at the literal flag [rz], and the start state
     [init_cs_ok] proves is [init_acs_of] at the run's own flag: this is where the
     two meet (as in jsoncons/fuzz_bigint's Bo0StartupK.v). *)
  Hypothesis Hrz : rz = rseq_z (kb_rseq (in_kernel (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))).

  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation E0a := (E0 sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation LIM := AsanInitK.LIMIT.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
  Variable HS : nat -> option acs.
  Variable T : Fs.Fs -> TSet.
  Hypothesis T_nil : forall fs', T fs' [].
  Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH (HOLES T) fs.
  Hypothesis X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 LIM rz SINV argH fs x.
  Variables KC0 BFUEL FUEL : nat.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Hypothesis startup_cert :
    check ASEGS0 IT0 ASAN0 NX0 LIM rz XN0 XE0 XB0 HS KC0 BFUEL FUEL None (asan0_init rz) startup_plan = COk startup_shape.

  Theorem as0_startup :
    srealizes ASEGS0 scfg (init_config ASEGS0 apc APH0 sp brk0 mbase rdraw LIM
                                 (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))
              (sd (HOLES T) t_nil E0a fs startup_shape).
  Proof.
    pose proof asan0_img_facts as IMG.

    rewrite (init_cfg_eq ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hapc).
    pose proof (init_cs_ok ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc IMG Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hapc Hlaunch Hlau) as HC.
    (* the certificate's start state at the run's own flag *)
    pose proof startup_cert as SC.
    assert (EI : asan0_init rz = asan0_init (rseq_z (kb_rseq (in_kernel (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))))) by (rewrite <- Hrz; reflexivity).
    rewrite EI in SC.
    exact (stage_sound sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc rz Hsp Hva IT0 IT0_ok HS T T_nil HS_sound X_ALL KC0 BFUEL FUEL
             startup_plan _ startup_shape SC _ _ _ _ HC).
  Qed.

  Corollary as0_startup_hole : hole_only startup_shape = true ->
    srealizes ASEGS0 scfg (init_config ASEGS0 apc APH0 sp brk0 mbase rdraw LIM
                                 (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))
              (T fs).
  Proof.
    intros Hho. pose proof asan0_img_facts as IMG.
    rewrite (init_cfg_eq ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hapc).
    pose proof (init_cs_ok ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc IMG Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hapc Hlaunch Hlau) as HC.
    (* the certificate's start state at the run's own flag *)
    pose proof startup_cert as SC.
    assert (EI : asan0_init rz = asan0_init (rseq_z (kb_rseq (in_kernel (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))))) by (rewrite <- Hrz; reflexivity).
    rewrite EI in SC.
    exact (stage_hole sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc rz Hsp Hva IT0 IT0_ok HS T T_nil HS_sound X_ALL KC0 BFUEL FUEL
             startup_plan _ startup_shape SC Hho _ _ _ _ HC).
  Qed.
End Startup.
End As0.
