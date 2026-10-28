(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec StoreOk Hoare ShapeAlg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore
  AsanNodesIO AsanNodesArg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxPlanSound2 CxPlanSoundSums CxNodesIface CxNodesMmA CxNodesMmB
  CxNodesIOSound CxNodesIOInit CxNodesArgSound CxNodesEmitSound CxAcctNoLazy.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxHooks HBPlanImage HBAtable HBXAll HBHooksC HBHooks CxNodesJoinZ AsanInit HBArg HBCheck0 HBCheck1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition ha2_XN (T : ION.iotab) : nat -> list expr -> acs -> option acs :=
  xn_plus (AN.xn HASEGS HAT NX0) (xn_plus (ION.xn HASEGS HAT T) (xn_plus (ha_xn NX0) zj_xn)).
Definition ha2_XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := AN.xe HASEGS HAT NX0.
Definition ha2_XB (T : ION.iotab) : nat -> list expr -> acs -> option (acs * acs) := ION.xb HASEGS NX0 T.

Section HA2Check.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation LIM := AsanInit.LIMIT.
  (* [comment removed for export] *)
  Variable SV : env -> (word -> option byte) -> Prop.
  Hypothesis SV_to1 : forall E M, SV E M -> HBArg.SINV1 sp brk0 argv envp rdraw hw uid E M.
  Hypothesis SV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SV E M -> SV E M'.
  Hypothesis SV_agree : forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M.
  Lemma SV_to0_2 : forall E M, SV E M -> SINV0 HAPH sp rdraw brk0 argv envp uid hw E M.
  Proof. intros E M H. exact (proj1 (SV_to1 E M H)). Qed.

  Let AH := argH0_high HAPH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree HAPH sp rdraw argv envp uid hw.
  Let SF := SV_frame.
  Let SA := SV_agree.
  Lemma SP1_2 : forall E M, SV E M -> uE E e_pgsp = pgdown ISP.
  Proof. intros E M H. exact (SINV0_pgsp HAPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M (SV_to0_2 E M H)). Qed.
  Let SP := SP1_2.
  Lemma NXS1_2 : CAP.expr_vars_lt NX0 e_spw = true. Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma ob2_sys : forall y, sys_stmt HASEGS HAT NX0 LIM SV argH ISP fs y.
  Proof.
    apply (CxNodesMmB.node_sys_sound HASEGS HAT NX0 LIM SV argH ISP fs);
      auto using hat_res_len, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS1_2.
  Qed.
  Lemma ob2_brk2 : brk2_stmt HASEGS HAT NX0 LIM SV argH ISP fs.
  Proof.
    apply (CxNodesMmB.node_brk2_sound HASEGS HAT NX0 LIM SV argH ISP fs);
      auto using hat_in_hull, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS1_2, hat_res_len, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob2_mmap2 : mm2_stmt HASEGS HAT NX0 LIM SV argH ISP fs (node_mmap2 HAT NX0 LIM).
  Proof.
    apply (node_mmap2_sound_OBL HASEGS HAT NX0 LIM SV argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS1_2, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob2_mmapin : forall hole : bool, mm3_stmt HASEGS HAT NX0 LIM SV argH ISP fs (node_mmapin HAT LIM hole).
  Proof.
    apply (node_mmapin_sound_OBL HASEGS HAT NX0 LIM SV argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS1_2, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob2_mprotect2 : mm2_stmt HASEGS HAT NX0 LIM SV argH ISP fs (node_mprotect2 HAT LIM).
  Proof.
    apply (node_mprotect2_sound_OBL HASEGS HAT NX0 LIM SV argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS1_2, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob2_exit : exit_stmt HASEGS HAT LIM SV argH ISP fs.
  Proof. apply (CxNodesMmB.node_exit_sound HASEGS HAT LIM SV argH ISP fs). Qed.
  Lemma ob2_join : join_stmt HASEGS HAT NX0 LIM SV argH ISP fs.
  Proof. apply (node_join_sound HASEGS HAT NX0 LIM SV argH ISP fs). Qed.
  Lemma ob2_joinx : joinx_stmt HASEGS HAT NX0 LIM SV argH ISP fs.
  Proof. apply (node_joinx_sound HASEGS HAT NX0 LIM SV argH ISP fs); auto using NXS1_2. Qed.
  Lemma ob2_x : forall x, x_on HAT x = true -> x_stmt HASEGS HAT NX0 LIM SV argH ISP fs x.
  Proof. intros x _. exact (ha_x_all_sinv sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV_to0_2 SF SA x). Qed.

  (* [comment removed for export] *)
  Lemma ha0c2_XN_sound : ext_stmt HASEGS HAT NX0 LIM ha0_XN SV argH ISP fs.
  Proof.
    unfold ha0_XN. apply ext_stmt_plus.
    - apply (HBHooks.ha_xn_sound HAT NX0 LIM SV argH ISP fs hat_segs_wx hat_in_hull hat_hull_ok AH NXS1_2 AA SF SA).
      unfold HBHooksC.MAXVA_GOT, HBHooksC.MAXVA_PTRSLOT, HBMaxVA.MAXVA_PTRCELL. cbn [img_lo img_hi HAT]. lia.
    - exact (zj_xn_sound HASEGS HAT NX0 LIM SV argH ISP fs).
  Qed.
  Lemma ha0c2_XE_sound : emit_stmt HASEGS HAT NX0 LIM ha0_XE SV argH ISP fs.
  Proof. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
  Lemma ha0c2_XB_sound : ext2_stmt HASEGS HAT NX0 LIM ha0_XB SV argH ISP fs.
  Proof. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

  (* [comment removed for export] *)
  Variable T : ION.iotab.
  Let argv1 := nth 1 argv [].
  Hypothesis H_class : match ION.io_open T with
    | ION.ONone => True
    | ION.OTooLong => (4096 <= length argv1)%nat
    | ION.ONoEnt => argv1 = [] \/ (path_has_slash argv1 = false /\ path_is_dirref argv1 = false /\ (length argv1 <= 4095)%nat /\ fs_lookup fs argv1 = None)
    | ION.ODir => path_is_dirref argv1 = true /\ (length argv1 <= 4095)%nat
    | ION.OFile lo hi => exists c, argv1 <> [] /\ path_has_slash argv1 = false /\ path_is_dirref argv1 = false /\ (length argv1 <= 4095)%nat /\ fs_lookup fs argv1 = Some c
                     /\ lo <= flen c <= hi
                     /\ (forall E M, SV E M -> forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (ION.io_blob T + j)%nat = chunk j c)
                     /\ ION.hdr_ok T c
    end.

  Theorem ha2_XN_sound : ext_stmt HASEGS HAT NX0 LIM (ha2_XN T) SV argH ISP fs.
  Proof.
    unfold ha2_XN. apply ext_stmt_plus; [|apply ext_stmt_plus].
    - exact (HBArg.ha_ext_sound sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit fs SV SV_to1 SV_frame SV_agree).
    - exact (CxNodesIOInit.io_ext_stmt_init HASEGS HAT HAPH hat_in_hull hat_hull_ok sp brk0 argv envp fs Hsp Hva Hve uid hw rdraw Hfit SV SV_to0_2 SV_frame SV_agree T H_class).
    - exact ha0c2_XN_sound.
  Qed.
  Theorem ha2_XE_sound : emit_stmt HASEGS HAT NX0 LIM ha2_XE SV argH ISP fs.
  Proof. exact (HBArg.ha_emit_sound sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit fs SV SV_to1 SV_frame SV_agree). Qed.
  Theorem ha2_XB_sound : ext2_stmt HASEGS HAT NX0 LIM (ha2_XB T) SV argH ISP fs.
  Proof. exact (CxNodesIOInit.io_ext2_stmt_init HASEGS HAT HAPH sp brk0 argv envp fs Hsp Hva Hve uid hw rdraw Hfit SV SV_to0_2 SV_frame SV_agree T H_class). Qed.

  Variable HS : nat -> option acs.
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs0, env_agree NX0 E E' -> HOLES h E fs0 = HOLES h E' fs0.
  Hypothesis HOLES_nil : forall h E fs0, HOLES h E fs0 [].
  Hypothesis HOLES_mod : forall h E fs0, HOLES h E fs0 = HOLES (CAP.hole_cls h) E fs0.   (* [comment removed for export] *)
  Hypothesis HS_sound : holes_stmt HASEGS HAT LIM HS SV argH ISP HOLES fs.
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound HASEGS IT.
  Variable KC : nat.
  Variable GC : bool.

  Theorem ha2_check_sound : forall FUEL BFUEL p cs s,
    CAP.check HASEGS IT HAT NX0 LIM (ha2_XN T) ha2_XE (ha2_XB T) HS KC true false GC BFUEL FUEL None cs p = COk s ->
    forall E R FULL model, cs_ok HASEGS HAT LIM SV argH ISP fs E cs R FULL model ->
      crz HASEGS (cfg_of HASEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros FUEL BFUEL p cs s Hchk E R FULL model HC.
    exact (check_sound HASEGS IT IT_ok HAT NX0 LIM HS (ha2_XN T) ha2_XE (ha2_XB T)
              hat_segs_wx hat_in_hull hat_hull_ok hat_shadow_ok hat_zone_ok NXS1_2 SV argH ISP AH AA SF SA SP
              HOLES HOLES_agree HOLES_nil HOLES_mod fs KC GC
              ob2_sys ob2_brk2 ob2_mmap2 ob2_mmapin ob2_mprotect2 ob2_exit ob2_x ob2_join ob2_joinx
              ha2_XN_sound ha2_XE_sound ha2_XB_sound HS_sound
              FUEL BFUEL None p cs s Hchk E R FULL model t_nil HC I eq_refl).
  Qed.
End HA2Check.
