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
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxHooks HBPlanImage HBAtable HBXAll HBHooksC HBHooks CxNodesJoinZ AsanInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.


Definition ha0_XN : nat -> list expr -> acs -> option acs := xn_plus (ha_xn NX0) zj_xn.
Definition ha0_XE (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition ha0_XB (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Section HA0Check.
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

  #[local] Notation SINV := (SINV0 HAPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation LIM := AsanInit.LIMIT.
  Let AH := argH0_high HAPH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree HAPH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame HAPH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree HAPH sp rdraw brk0 argv envp uid hw.
  Let SP := SINV0_pgsp HAPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  Lemma NXS : CAP.expr_vars_lt NX0 e_spw = true. Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma ob_sys : forall y, sys_stmt HASEGS HAT NX0 LIM SINV argH ISP fs y.
  Proof.
    apply (CxNodesMmB.node_sys_sound HASEGS HAT NX0 LIM SINV argH ISP fs);
      auto using hat_res_len, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS.
  Qed.
  Lemma ob_brk2 : brk2_stmt HASEGS HAT NX0 LIM SINV argH ISP fs.
  Proof.
    apply (CxNodesMmB.node_brk2_sound HASEGS HAT NX0 LIM SINV argH ISP fs);
      auto using hat_in_hull, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS, hat_res_len, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob_mmap2 : mm2_stmt HASEGS HAT NX0 LIM SINV argH ISP fs (node_mmap2 HAT NX0 LIM).
  Proof.
    apply (node_mmap2_sound_OBL HASEGS HAT NX0 LIM SINV argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob_mmapin : forall hole : bool, mm3_stmt HASEGS HAT NX0 LIM SINV argH ISP fs (node_mmapin HAT LIM hole).
  Proof.
    apply (node_mmapin_sound_OBL HASEGS HAT NX0 LIM SINV argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob_mprotect2 : mm2_stmt HASEGS HAT NX0 LIM SINV argH ISP fs (node_mprotect2 HAT LIM).
  Proof.
    apply (node_mprotect2_sound_OBL HASEGS HAT NX0 LIM SINV argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NXS, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma ob_exit : exit_stmt HASEGS HAT LIM SINV argH ISP fs.
  Proof. apply (CxNodesMmB.node_exit_sound HASEGS HAT LIM SINV argH ISP fs). Qed.
  Lemma ob_join : join_stmt HASEGS HAT NX0 LIM SINV argH ISP fs.
  Proof. apply (node_join_sound HASEGS HAT NX0 LIM SINV argH ISP fs). Qed.
  Lemma ob_joinx : joinx_stmt HASEGS HAT NX0 LIM SINV argH ISP fs.
  Proof. apply (node_joinx_sound HASEGS HAT NX0 LIM SINV argH ISP fs); auto using NXS. Qed.


  Lemma ob_x : forall x, x_on HAT x = true -> x_stmt HASEGS HAT NX0 LIM SINV argH ISP fs x.
  Proof. intros x _. exact (ha_x_all_sinv sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SINV (fun E M H => H) SF SA x). Qed.

  Theorem ha0_XN_sound : ext_stmt HASEGS HAT NX0 LIM ha0_XN SINV argH ISP fs.
  Proof.
    unfold ha0_XN. apply ext_stmt_plus.
    - apply (HBHooks.ha_xn_sound HAT NX0 LIM SINV argH ISP fs hat_segs_wx hat_in_hull hat_hull_ok AH NXS AA SF SA).
      unfold HBHooksC.MAXVA_GOT, HBHooksC.MAXVA_PTRSLOT, HBMaxVA.MAXVA_PTRCELL. cbn [img_lo img_hi HAT]. lia.
    - exact (zj_xn_sound HASEGS HAT NX0 LIM SINV argH ISP fs).
  Qed.
  Theorem ha0_XE_sound : emit_stmt HASEGS HAT NX0 LIM ha0_XE SINV argH ISP fs.
  Proof. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
  Theorem ha0_XB_sound : ext2_stmt HASEGS HAT NX0 LIM ha0_XB SINV argH ISP fs.
  Proof. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

  Variable HS : nat -> option acs.
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs0, env_agree NX0 E E' -> HOLES h E fs0 = HOLES h E' fs0.
  Hypothesis HOLES_nil : forall h E fs0, HOLES h E fs0 [].
  Hypothesis HOLES_mod : forall h E fs0, HOLES h E fs0 = HOLES (CAP.hole_cls h) E fs0.   (* [comment removed for export] *)
  Hypothesis HS_sound : holes_stmt HASEGS HAT LIM HS SINV argH ISP HOLES fs.
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound HASEGS IT.
  Variable KC : nat.
  Variable GC : bool.

  Theorem ha0_check_sound : forall FUEL BFUEL p cs s,
    CAP.check HASEGS IT HAT NX0 LIM ha0_XN ha0_XE ha0_XB HS KC true false GC BFUEL FUEL None cs p = COk s ->
    forall E R FULL model, cs_ok HASEGS HAT LIM SINV argH ISP fs E cs R FULL model ->
      crz HASEGS (cfg_of HASEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros FUEL BFUEL p cs s Hchk E R FULL model HC.
    exact (check_sound HASEGS IT IT_ok HAT NX0 LIM HS ha0_XN ha0_XE ha0_XB
              hat_segs_wx hat_in_hull hat_hull_ok hat_shadow_ok hat_zone_ok NXS SINV argH ISP AH AA SF SA SP
              HOLES HOLES_agree HOLES_nil HOLES_mod fs KC GC
              ob_sys ob_brk2 ob_mmap2 ob_mmapin ob_mprotect2 ob_exit ob_x ob_join ob_joinx
              ha0_XN_sound ha0_XE_sound ha0_XB_sound HS_sound
              FUEL BFUEL None p cs s Hchk E R FULL model t_nil HC I eq_refl).
  Qed.
End HA0Check.
