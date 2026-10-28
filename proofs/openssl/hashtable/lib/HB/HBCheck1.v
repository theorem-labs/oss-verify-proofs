(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec StoreOk Hoare ShapeAlg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore
  AsanNodesIO AsanNodesArg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxPlanSound2 CxPlanSoundSums CxNodesIface CxNodesMmA CxNodesMmB
  CxNodesIOSound CxNodesArgSound CxNodesEmitSound CxAcctNoLazy.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxHooks HBPlanImage HBAtable HBXAll HBHooksC HBHooks CxNodesJoinZ AsanInit HBArg HBCheck0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ha1_XN : nat -> list expr -> acs -> option acs := xn_plus (AN.xn HASEGS HAT NX0) (xn_plus (ha_xn NX0) zj_xn).
Definition ha1_XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := AN.xe HASEGS HAT NX0.
Definition ha1_XB (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Section HA1Check.
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
  Lemma SV_to0 : forall E M, SV E M -> SINV0 HAPH sp rdraw brk0 argv envp uid hw E M.
  Proof. intros E M H. exact (proj1 (SV_to1 E M H)). Qed.

  Let AH := argH0_high HAPH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree HAPH sp rdraw argv envp uid hw.
  Let SF := SV_frame.
  Let SA := SV_agree.
  Lemma SP1 : forall E M, SV E M -> uE E e_pgsp = pgdown ISP.
  Proof. intros E M H. exact (SINV0_pgsp HAPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M (SV_to0 E M H)). Qed.
  Let SP := SP1.
  Lemma NXS1 : CAP.expr_vars_lt NX0 e_spw = true. Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma ob1_sys : forall y, sys_stmt HASEGS HAT NX0 LIM SV argH ISP fs y.
  Proof.
    apply (CxNodesMmB.node_sys_sound HASEGS HAT NX0 LIM SV argH ISP fs);
      auto using hat_res_len, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS1.
  Qed.
  Lemma ob1_brk2 : brk2_stmt HASEGS HAT NX0 LIM SV argH ISP fs.
  Proof.
    apply (CxNodesMmB.node_brk2_sound HASEGS HAT NX0 LIM SV argH ISP fs);
      auto using hat_in_hull, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS1, hat_res_len, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob1_mmap2 : mm2_stmt HASEGS HAT NX0 LIM SV argH ISP fs (node_mmap2 HAT NX0 LIM).
  Proof.
    apply (node_mmap2_sound_OBL HASEGS HAT NX0 LIM SV argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS1, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob1_mmapin : forall hole : bool, mm3_stmt HASEGS HAT NX0 LIM SV argH ISP fs (node_mmapin HAT LIM hole).
  Proof.
    apply (node_mmapin_sound_OBL HASEGS HAT NX0 LIM SV argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS1, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob1_mprotect2 : mm2_stmt HASEGS HAT NX0 LIM SV argH ISP fs (node_mprotect2 HAT LIM).
  Proof.
    apply (node_mprotect2_sound_OBL HASEGS HAT NX0 LIM SV argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS1, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob1_exit : exit_stmt HASEGS HAT LIM SV argH ISP fs.
  Proof. apply (CxNodesMmB.node_exit_sound HASEGS HAT LIM SV argH ISP fs). Qed.
  Lemma ob1_join : join_stmt HASEGS HAT NX0 LIM SV argH ISP fs.
  Proof. apply (node_join_sound HASEGS HAT NX0 LIM SV argH ISP fs). Qed.
  Lemma ob1_joinx : joinx_stmt HASEGS HAT NX0 LIM SV argH ISP fs.
  Proof. apply (node_joinx_sound HASEGS HAT NX0 LIM SV argH ISP fs); auto using NXS1. Qed.
  Lemma ob1_x : forall x, x_on HAT x = true -> x_stmt HASEGS HAT NX0 LIM SV argH ISP fs x.
  Proof. intros x _. exact (ha_x_all_sinv sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV_to0 SF SA x). Qed.

  (* [comment removed for export] *)
  Lemma ha0sv_XN_sound : ext_stmt HASEGS HAT NX0 LIM ha0_XN SV argH ISP fs.
  Proof.
    unfold ha0_XN. apply ext_stmt_plus.
    - apply (HBHooks.ha_xn_sound HAT NX0 LIM SV argH ISP fs hat_segs_wx hat_in_hull hat_hull_ok AH NXS1 AA SF SA).
      unfold HBHooksC.MAXVA_GOT, HBHooksC.MAXVA_PTRSLOT, HBMaxVA.MAXVA_PTRCELL. cbn [img_lo img_hi HAT]. lia.
    - exact (zj_xn_sound HASEGS HAT NX0 LIM SV argH ISP fs).
  Qed.
  Lemma ha0sv_XE_sound : emit_stmt HASEGS HAT NX0 LIM ha0_XE SV argH ISP fs.
  Proof. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
  Lemma ha0sv_XB_sound : ext2_stmt HASEGS HAT NX0 LIM ha0_XB SV argH ISP fs.
  Proof. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

  (* [comment removed for export] *)
  Theorem ha1_XN_sound : ext_stmt HASEGS HAT NX0 LIM ha1_XN SV argH ISP fs.
  Proof.
    unfold ha1_XN. apply ext_stmt_plus.
    - exact (HBArg.ha_ext_sound sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit fs SV SV_to1 SV_frame SV_agree).
    - exact ha0sv_XN_sound.
  Qed.
  Theorem ha1_XE_sound : emit_stmt HASEGS HAT NX0 LIM ha1_XE SV argH ISP fs.
  Proof. exact (HBArg.ha_emit_sound sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit fs SV SV_to1 SV_frame SV_agree). Qed.
  Theorem ha1_XB_sound : ext2_stmt HASEGS HAT NX0 LIM ha1_XB SV argH ISP fs.
  Proof. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

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

  Theorem ha0sv_check_sound : forall FUEL BFUEL p cs s,
    CAP.check HASEGS IT HAT NX0 LIM ha0_XN ha0_XE ha0_XB HS KC true false GC BFUEL FUEL None cs p = COk s ->
    forall E R FULL model, cs_ok HASEGS HAT LIM SV argH ISP fs E cs R FULL model ->
      crz HASEGS (cfg_of HASEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros FUEL BFUEL p cs s Hchk E R FULL model HC.
    exact (check_sound HASEGS IT IT_ok HAT NX0 LIM HS ha0_XN ha0_XE ha0_XB
              hat_segs_wx hat_in_hull hat_hull_ok hat_shadow_ok hat_zone_ok NXS1 SV argH ISP AH AA SF SA SP
              HOLES HOLES_agree HOLES_nil HOLES_mod fs KC GC
              ob1_sys ob1_brk2 ob1_mmap2 ob1_mmapin ob1_mprotect2 ob1_exit ob1_x ob1_join ob1_joinx
              ha0sv_XN_sound ha0sv_XE_sound ha0sv_XB_sound HS_sound
              FUEL BFUEL None p cs s Hchk E R FULL model t_nil HC I eq_refl).
  Qed.

  Theorem ha1_check_sound : forall FUEL BFUEL p cs s,
    CAP.check HASEGS IT HAT NX0 LIM ha1_XN ha1_XE ha1_XB HS KC true false GC BFUEL FUEL None cs p = COk s ->
    forall E R FULL model, cs_ok HASEGS HAT LIM SV argH ISP fs E cs R FULL model ->
      crz HASEGS (cfg_of HASEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros FUEL BFUEL p cs s Hchk E R FULL model HC.
    exact (check_sound HASEGS IT IT_ok HAT NX0 LIM HS ha1_XN ha1_XE ha1_XB
              hat_segs_wx hat_in_hull hat_hull_ok hat_shadow_ok hat_zone_ok NXS1 SV argH ISP AH AA SF SA SP
              HOLES HOLES_agree HOLES_nil HOLES_mod fs KC GC
              ob1_sys ob1_brk2 ob1_mmap2 ob1_mmapin ob1_mprotect2 ob1_exit ob1_x ob1_join ob1_joinx
              ha1_XN_sound ha1_XE_sound ha1_XB_sound HS_sound
              FUEL BFUEL None p cs s Hchk E R FULL model t_nil HC I eq_refl).
  Qed.
End HA1Check.
