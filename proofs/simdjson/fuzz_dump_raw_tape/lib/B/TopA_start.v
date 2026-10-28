(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import PropExec.
Local Instance topa_fx : PropExec.FPState := PropExec.fx0.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import
  ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImagesB AsanInit AsanTablesB
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanNodesStartX AsanNodesStartXAsan AsanSmearA AsanHeapSortA AsanStartupB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => (holes_only a && holes_only b)%bool
  | SAlt2 a b => (holes_only a && holes_only b)%bool
  | _ => false
  end.

Lemma sd_holes_only : forall (HOLES : nat -> env -> Fs.Fs -> TSet) (D : TSet) (E : env) (fs : Fs.Fs) (T : TSet) (s : shape),
  (forall h, t_eq (HOLES h E fs) T) -> holes_only s = true -> t_eq (sd HOLES D E fs s) T.
Proof.
  intros HOLES D E fs T s HH. induction s as [| c | fd ps s' IH | a IHa b IHb | e mid a IHa b IHb | h | ];
    cbn [holes_only sd]; intros Hs; try discriminate.
  - apply andb_prop in Hs as [H1 H2]. intros tr. unfold t_alt2. rewrite (IHa H1 tr), (IHb H2 tr). tauto.
  - apply andb_prop in Hs as [H1 H2]. destruct (bv_unsigned (edenot E e) <=? mid); [exact (IHa H1) | exact (IHb H2)].
  - exact (HH h).
Qed.

Lemma cs_ok_inp : forall segs A nx0 LIMIT SINV argH FS0 E cs R FULL res brk0 mbase sp lim
                         argv envp ifs stdin uid gid groups net hw (n s : word) (ab : bool) urnd tmp,
  cs_ok segs A nx0 LIMIT SINV argH FS0 E cs R FULL
        (init_model res brk0 mbase sp lim (mkProcInput argv envp (fs_seed_tmp ifs tmp) stdin uid gid groups net default_nofile (Z_to_bv 64 0) hw false Sv48)) ->
  cs_ok segs A nx0 LIMIT SINV argH FS0 E cs R FULL
        (init_model res brk0 mbase sp lim (mkProcInput_full argv envp ifs stdin uid gid groups net n s hw ab Sv48 urnd tmp)).
Proof.
  intros. destruct H; constructor; try assumption.
  match goal with H : MInv _ _ |- MInv _ _ => destruct H; constructor; assumption end.
Qed.

Lemma init_cfg_gen : forall segs A (apc : N) ph sp brk0 mbase rdraw lim argv envp ifs stdin uid gid groups net hw (n s : word) (ab : bool) urnd tmp,
  Z.of_N apc = a_entry A ->
  init_config segs apc ph sp brk0 mbase rdraw lim (mkProcInput_full argv envp ifs stdin uid gid groups net n s hw ab Sv48 urnd tmp)
  = cfg_of segs (R0 sp) (a_entry A) (FULL0 ph sp rdraw argv envp uid hw)
           (init_model (segments_reserved segs) brk0 mbase sp lim (mkProcInput_full argv envp ifs stdin uid gid groups net n s hw ab Sv48 urnd tmp)).
Proof.
  intros segs A apc ph sp brk0 mbase rdraw lim argv envp ifs stdin uid gid groups net hw n s ab urnd tmp Hpc.
  unfold init_config, cfg_of. cbn [in_argv in_envp in_uid in_hwcap]. rewrite init_mkst. rewrite Hpc. reflexivity.
Qed.

Section StartupGen.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_both : nat -> option acs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN_B NX0 AsanInit.LIMIT XN0 XE0 XB0 HS_both KC0 BFUEL FUEL None asan_b_init startup_plan = COk startup_shape.
  Hypothesis Hshape : holes_only startup_shape = true.

  Variable T : list (list byte) -> Fs.Fs -> TSet.
  Hypothesis T_nil : forall argv fs, T argv fs [].
  Hypothesis T_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs),
    valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
    holes_stmt ASEGS ASAN_B NX0 AsanInit.LIMIT HS_both (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw)
               (fun _ _ fs' => T argv fs') fs.

  Theorem asan_startup_gen : forall en inp,
    valid_entry (mkImage ASEGS AsanUbsan.M.init_pc APH) en inp -> valid_input_either inp ->
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                                 target_alloc_limit inp)
              (T (in_argv inp) (in_fs inp)).
  Proof using IT0_ok startup_cert Hshape T_nil T_holes.
    intros en inp Hve Hvi.
    destruct en as [sp brk0 mbase rdraw]. destruct inp as [argv envp ifs stdin uid gid groups net nofile sigmask hw abort va urnd tmp].
    destruct Hvi as (Hva & Hvenv & _ & _ & (Huid & _) & _ & _ & _ & Hsv & _).
    rewrite (valid_entry_sv48 _ _ _ Hsv) in Hve. destruct Hve as (Hsp & Hbrk & Hmb & Hfit).
    cbn [in_argv in_envp in_fs in_image_fs in_tmp in_uid in_abort_terminal in_va_size en_sp en_brk en_mmap_base en_draw] in *. subst va.
    set (fs := fs_seed_tmp ifs tmp) in *.
    rewrite (init_cfg_gen ASEGS ASAN_B AsanUbsan.M.init_pc APH sp brk0 mbase rdraw target_alloc_limit
               argv envp ifs stdin uid gid groups net hw nofile sigmask abort urnd tmp eq_refl).
    pose proof (cs_ok_inp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ argv envp ifs stdin uid gid groups net hw nofile sigmask abort urnd tmp
                  (init_cs_ok ASEGS ASAN_B APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net asan_img_facts
                     Hsp Hbrk Hmb Hva Hvenv Hfit Huid)) as HC.
    set (SINV := SINV0 APH sp rdraw brk0 argv envp uid hw) in *.
    set (argH := argH0 APH sp rdraw argv envp uid hw) in *.
    set (HOLES := fun (_ : nat) (_ : env) (fs' : Fs.Fs) => T argv fs').
    pose proof (argH0_high APH sp rdraw argv envp uid hw Hsp Hva) as AH.
    pose proof (argH0_agree APH sp rdraw argv envp uid hw) as AA.
    pose proof (SINV0_frame APH sp rdraw brk0 argv envp uid hw) as SF.
    pose proof (SINV0_agree APH sp rdraw brk0 argv envp uid hw) as SA.
    assert (HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') by (intros; reflexivity).
    assert (HOLES_nil : forall h E fs', HOLES h E fs' []) by (intros h E fs'; exact (T_nil argv fs')).
    pose proof (T_holes sp rdraw brk0 argv envp uid hw fs Hsp Hva Hvenv Hfit) as HOLES_sound.
    apply (srz_conseq ASEGS _ (sd HOLES t_nil (E0 APH sp rdraw brk0 argv envp uid hw) fs startup_shape)).
    - exact (check_sound ASEGS IT0 IT0_ok ASAN_B NX0 AsanInit.LIMIT HS_both XN0 XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              (AsanNodesMmB.node_sys_sound ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AA SF SA)
              (AsanNodesMmB.node_brk2s_sound ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_hull asan_hull_ok asan_shadow_ok AH SF)
              (node_mmap2_sound_OBL ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mmapin_sound_OBL ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mprotect2_sound_OBL ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs)
              (asan_node_x_sound_all sp rdraw brk0 argv envp fs Hsp Hva Hvenv uid hw Hfit SINV (fun E M H => H) SF SA)
              (node_join_sound ASEGS ASAN_B NX0 AsanInit.LIMIT SINV argH fs)
              (XN0_sound _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan asan_b_init startup_shape startup_cert
              _ _ _ _ t_nil HC I eq_refl).
    - apply sd_holes_only; [intros h tr; reflexivity | exact Hshape].
  Qed.
End StartupGen.
