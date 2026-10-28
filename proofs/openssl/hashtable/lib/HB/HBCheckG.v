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
  CxNodesIOSound CxNodesIOInit CxNodesArgSound CxNodesEmitSound CxAcctNoLazy CxNodesStartX CxNodesStartXInit AsanPopFree RtIStrncpy CxXSniffOff.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxHooks HBPlanImage HBAtable HBSums HBSumsSpecs HB_code_startx HBXAll HBHooksC HBHooks CxNodesJoinZ AsanInit HBArg HBCheck0 HBCheck1
  AsanNodesRP HBRPTab HBRP HBRpU HBRpX HBBandD CxBits CxJoinM CxRezero CxRefront CxOdd CxOpt CxOptK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition hagx_xn (NX : nat) (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 16%nat => ION.node_ioctl HASEGS cs
  | 30%nat => CAP.node_mmap_p HASEGS HAT NX AsanInit.LIMIT cs
  | 31%nat => CAP.node_munmap_p HASEGS cs
  | 32%nat => CAP.node_mmap_q HASEGS HAT NX AsanInit.LIMIT cs
  | 33%nat => node_bitspell args cs
  | 34%nat => node_joinx_m HASEGS NX args cs
  | 35%nat => node_join_alt HASEGS args cs
  | 36%nat => node_join_zero args cs
  | 37%nat => node_rezero args cs
  | 38%nat => node_refront args cs
  | 40%nat => node_oddspell args cs
  | 41%nat => RPU.node_rpoison_u HASEGS NX RP_HA args cs      (* [comment removed for export] *)
  | 42%nat => BDN.node_band_diamond HASEGS HAT NX args cs     (* [comment removed for export] *)
  | 43%nat => RPX.node_rpoison_r HASEGS NX RP_HA args cs      (* [comment removed for export] *)
  | 44%nat | 45%nat | 46%nat | 47%nat | 48%nat | 49%nat | 52%nat | 53%nat | 54%nat => optk_xn HAT AsanInit.LIMIT id args cs      (* [comment removed for export] *)      (* [comment removed for export] *)
  | _ => None
  end.
Definition hag_XN (NX : nat) : nat -> list expr -> acs -> option acs :=
  xn_plus (hagx_xn NX) (xn_plus (RPN.xn HASEGS NX RP_HA) (xn_plus (ha_xn NX) zj_xn)).
Definition hag_XE (NX : nat) : nat -> list expr -> acs -> option (Z * list spiece * acs) := AN.xe HASEGS HAT NX.
Definition hag_XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.

Section HAGCheck.
  Variable NX : nat.
  Hypothesis NX_ge : (NX0 <= NX)%nat.
  Hypothesis NX_spw : CAP.expr_vars_lt NX e_spw = true.
  Variable PHI : env -> Prop.
  Hypothesis PHI_agree : forall E E', env_agree NX E E' -> PHI E -> PHI E'.
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

  Definition SVG (E : env) (M : word -> option byte) : Prop := SV E M /\ PHI E.

  Lemma env_agree_NX0 : forall E E', env_agree NX E E' -> env_agree NX0 E E'.
  Proof. intros E E' H. eapply env_agree_le; [exact H | exact NX_ge]. Qed.
  Lemma SVG_to1 : forall E M, SVG E M -> HBArg.SINV1 sp brk0 argv envp rdraw hw uid E M.
  Proof. intros E M [H _]. exact (SV_to1 E M H). Qed.
  Lemma SVG_to0 : forall E M, SVG E M -> SINV0 HAPH sp rdraw brk0 argv envp uid hw E M.
  Proof. intros E M H. exact (proj1 (SVG_to1 E M H)). Qed.
  Lemma SF_g : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SVG E M -> SVG E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact (SV_frame E M M' Hf H1) | exact H2]. Qed.
  Lemma SA_g : forall E E' M, env_agree NX E E' -> SVG E M -> SVG E' M.
  Proof. intros E E' M Hag [H1 H2]. split; [exact (SV_agree E E' M (env_agree_NX0 E E' Hag) H1) | exact (PHI_agree E E' Hag H2)]. Qed.
  Lemma AA_g : forall E E' (a : word), env_agree NX E E' -> argH E a = argH E' a.
  Proof. intros E E' a Hag. exact (argH0_agree HAPH sp rdraw argv envp uid hw E E' a (env_agree_NX0 E E' Hag)). Qed.
  Lemma SP_g : forall E M, SVG E M -> uE E e_pgsp = pgdown ISP.
  Proof. intros E M H. exact (SINV0_pgsp HAPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M (SVG_to0 E M H)). Qed.

  Let AH := argH0_high HAPH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := AA_g. Let SF := SF_g. Let SA := SA_g. Let SP := SP_g.

  (* [comment removed for export] *)
  Lemma obg_sys : forall y, sys_stmt HASEGS HAT NX LIM SVG argH ISP fs y.
  Proof.
    apply (CxNodesMmB.node_sys_sound HASEGS HAT NX LIM SVG argH ISP fs);
      auto using hat_res_len, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NX_spw.
  Qed.
  Lemma obg_brk2 : brk2_stmt HASEGS HAT NX LIM SVG argH ISP fs.
  Proof.
    apply (CxNodesMmB.node_brk2_sound HASEGS HAT NX LIM SVG argH ISP fs);
      auto using hat_in_hull, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NX_spw, hat_res_len, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma obg_mmap2 : mm2_stmt HASEGS HAT NX LIM SVG argH ISP fs (node_mmap2 HAT NX LIM).
  Proof.
    apply (node_mmap2_sound_OBL HASEGS HAT NX LIM SVG argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NX_spw, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma obg_mmapin : forall hole : bool, mm3_stmt HASEGS HAT NX LIM SVG argH ISP fs (node_mmapin HAT LIM hole).
  Proof.
    apply (node_mmapin_sound_OBL HASEGS HAT NX LIM SVG argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NX_spw, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma obg_mprotect2 : mm2_stmt HASEGS HAT NX LIM SVG argH ISP fs (node_mprotect2 HAT LIM).
  Proof.
    apply (node_mprotect2_sound_OBL HASEGS HAT NX LIM SVG argH ISP fs);
      auto using hat_in_hull, hat_res_len, hat_res_hull, hat_hull_ok, hat_shadow_ok, hat_zone_ok, NX_spw, hat_res_cover, hat_hull_ne.
  Qed.
  Lemma obg_exit : exit_stmt HASEGS HAT LIM SVG argH ISP fs.
  Proof. apply (CxNodesMmB.node_exit_sound HASEGS HAT LIM SVG argH ISP fs). Qed.
  Lemma obg_join : join_stmt HASEGS HAT NX LIM SVG argH ISP fs.
  Proof. apply (node_join_sound HASEGS HAT NX LIM SVG argH ISP fs). Qed.
  Lemma obg_joinx : joinx_stmt HASEGS HAT NX LIM SVG argH ISP fs.
  Proof. apply (node_joinx_sound HASEGS HAT NX LIM SVG argH ISP fs); auto using NX_spw. Qed.

  (* [comment removed for export] *)
  Lemma obg_x : forall x, x_on HAT x = true -> x_stmt HASEGS HAT NX LIM SVG argH ISP fs x.
  Proof.
    intros [ | | | | | | | | | | ] _.
    - exact (APSX.node_x_sound_XIMemset HASEGS HAT NX LIMIT hat_segs_wx hat_in_hull hat_hull_ok SVG argH ISP
               AH NX_spw AA SF SA fs ha_fill_spec_imemset).
    - exact (APSX.node_x_sound_XIMemcpy HASEGS HAT NX LIMIT hat_segs_wx hat_in_hull hat_hull_ok SVG argH ISP
               AH NX_spw AA SF SA fs ha_segs_wr ha_copy_spec_imemcpy).
    - exact (APSX.node_x_sound_XMemset HASEGS HAT NX LIMIT hat_segs_wx hat_in_hull hat_hull_ok SVG argH ISP
               AH NX_spw AA SF SA fs ha_fill_spec_memset).
    - exact (APSX.node_x_sound_XMemcpy HASEGS HAT NX LIMIT hat_segs_wx hat_in_hull hat_hull_ok SVG argH ISP
               AH NX_spw AA SF SA fs ha_segs_wr ha_copy_spec_memcpy).
    - exact (APSX.node_x_sound_XMemIsZero HASEGS HAT NX LIMIT hat_segs_wx hat_in_hull hat_hull_ok SVG argH ISP
               AH NX_spw AA SF SA fs ha_miz_spec).
    - (* [comment removed for export] *)
      eapply (x_sound_envscan HASEGS HAT NX LIMIT SVG argH ISP fs hat_segs_wx hat_in_hull hat_hull_ok SF W_51c410 W_51c414 W_51c418);
        [ cbn; lia
        | exact (fetch_at HASEGS _ _ _ eq_refl F_51c410) | exact (fetch_at HASEGS _ _ _ eq_refl F_51c414) | exact (fetch_at HASEGS _ _ _ eq_refl F_51c418)
        | repeat split; reflexivity | exact D_51c410 | exact D_51c414 | exact D_51c418
        | exact Hva | exact Hve | exact (sp_lo sp Hsp) | exact (sp_hi sp Hsp) | reflexivity
        | exact (SINV0_vals HAPH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit SVG SVG_to0)
        | exact (SINV0_envp HAPH sp rdraw brk0 argv envp uid hw SVG SVG_to0) ].
    - (* [comment removed for export] *)
      eapply (x_sound_pnscan HASEGS HAT NX LIMIT SVG argH ISP fs hat_segs_wx hat_in_hull hat_hull_ok AH NX_spw AA SF SA
                W_51c4cc W_51c4d0 W_51c4d4 W_51c4d8 W_51c4dc);
        [ cbn; lia
        | exact (fetch_at HASEGS _ _ _ eq_refl F_51c4cc) | exact (fetch_at HASEGS _ _ _ eq_refl F_51c4d0) | exact (fetch_at HASEGS _ _ _ eq_refl F_51c4d4)
        | exact (fetch_at HASEGS _ _ _ eq_refl F_51c4d8) | exact (fetch_at HASEGS _ _ _ eq_refl F_51c4dc)
        | repeat split; reflexivity | exact D_51c4cc | exact D_51c4d0 | exact D_51c4d4 | exact D_51c4d8 | exact D_51c4dc
        | exact Hva | exact Hve | exact (sp_lo sp Hsp) | exact (sp_hi sp Hsp) | reflexivity
        | exact (SINV0_vals HAPH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit SVG SVG_to0)
        | exact (SINV0_str0 HAPH sp rdraw brk0 argv envp Hva Hve uid hw Hfit SVG SVG_to0 SF) ].
    - apply x_sound_layout.
    - exact (APSX.node_x_sound_XIStrncpy HASEGS HAT NX LIMIT hat_segs_wx hat_in_hull hat_hull_ok SVG argH ISP
               AH NX_spw AA SF SA fs ha_istrncpy_spec).
    - exact (APSX.node_x_sound_XPopFree HASEGS HAT NX LIMIT hat_segs_wx hat_in_hull hat_hull_ok SVG argH ISP
               AH NX_spw AA SF SA fs ha_popfree_spec).
    - apply x_stmt_sniff_off. cbn [sniff_tab HAT]. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem hag_XN_sound : ext_stmt HASEGS HAT NX LIM (hag_XN NX) SVG argH ISP fs.
  Proof.
    unfold hag_XN. apply ext_stmt_plus; [|apply ext_stmt_plus; [|apply ext_stmt_plus]].
    - intros id args. unfold hagx_xn.
      do 16 (destruct id as [|id]; [intros cs cs' E R FULL model T0 _ _ Hn; discriminate Hn|]).
      destruct id as [|id]; [exact (node_ioctl_sound HASEGS HAT NX LIM SVG argH fs ISP SF sp argv envp)|].
      do 13 (destruct id as [|id]; [intros cs cs' E R FULL model T0 _ _ Hn; discriminate Hn|]).
      destruct id as [|id].
      { exact (CxNodesMmA.node_mmap_p_sound HASEGS HAT NX LIM SVG argH ISP fs hat_in_hull hat_res_len hat_hull_ok hat_shadow_ok AH hat_zone_ok NX_spw AA SF SA SP hat_res_cover hat_hull_ne). }
      destruct id as [|id].
      { exact (CxNodesMmB.node_munmap_p_sound HASEGS HAT NX LIM SVG argH ISP hat_res_len hat_hull_ok hat_shadow_ok fs AH SF). }
      destruct id as [|id].
      { exact (CxNodesMmA.node_mmap_q_sound HASEGS HAT NX LIM SVG argH ISP fs hat_in_hull hat_res_len hat_hull_ok hat_shadow_ok AH hat_zone_ok NX_spw AA SF SA SP hat_res_cover hat_hull_ne). }
      destruct id as [|id]; [exact (node_bitspell_sound HASEGS HAT NX LIM SVG argH ISP fs args)|].
      destruct id as [|id]; [apply (node_joinx_m_sound HASEGS HAT NX LIM SVG argH ISP fs); auto using NX_spw|].
      destruct id as [|id]; [exact (node_join_alt_sound HASEGS HAT NX LIM SVG argH ISP fs args)|].
      destruct id as [|id]; [exact (node_join_zero_sound HASEGS HAT NX LIM SVG argH ISP fs args)|].
      destruct id as [|id]; [exact (node_rezero_sound HASEGS HAT NX LIM SVG argH ISP fs args)|].
      destruct id as [|id]; [exact (node_refront_sound HASEGS HAT NX LIM SVG argH ISP fs args)|].
      destruct id as [|id]; [intros cs cs' E R FULL model T0 _ _ Hn; discriminate Hn|].
      destruct id as [|id]; [exact (node_oddspell_sound HASEGS HAT NX LIM SVG argH ISP fs args)|].
      destruct id as [|id].
      { exact (node_rpoison_u_sound HASEGS HAT NX LIM hat_segs_wx hat_in_hull hat_hull_ok SVG argH ISP AH NX_spw AA SF SA fs RP_HA HBRP.ha_rp_img HBRP.ha_rp_spec args). }
      destruct id as [|id].
      { exact (node_band_diamond_sound HASEGS HAT NX LIM hat_segs_wx hat_in_hull hat_hull_ok SVG argH ISP AH NX_spw AA SF SA fs args). }
      destruct id as [|id].
      { exact (node_rpoison_r_sound HASEGS HAT NX LIM hat_segs_wx hat_in_hull hat_hull_ok SVG argH ISP AH NX_spw AA SF SA fs RP_HA HBRP.ha_rp_img HBRP.ha_rp_spec args). }
      do 11 (destruct id as [|id]; [first [exact (optk_xn_sound HASEGS HAT NX LIM SVG argH ISP fs hat_shadow_ok hat_in_hull hat_hull_ok hat_zone_ok AH _ args) | (intros cs cs' E R FULL model T0 X1 X2 Hn; discriminate Hn)]|]).
      intros cs cs' E R FULL model T0 _ _ Hn; discriminate Hn.
    - exact (HBRP.ha_rp_ext_sound NX LIM SVG argH ISP AH NX_spw AA SF SA fs).
    - apply (HBHooks.ha_xn_sound HAT NX LIM SVG argH ISP fs hat_segs_wx hat_in_hull hat_hull_ok AH NX_spw AA SF SA).
      unfold HBHooksC.MAXVA_GOT, HBHooksC.MAXVA_PTRSLOT, HBMaxVA.MAXVA_PTRCELL. cbn [img_lo img_hi HAT]. lia.
    - exact (zj_xn_sound HASEGS HAT NX LIM SVG argH ISP fs).
  Qed.

  Theorem hag_XE_sound : emit_stmt HASEGS HAT NX LIM (hag_XE NX) SVG argH ISP fs.
  Proof.
    pose proof (HBArg.Lay_ha sp argv envp rdraw hw Hsp Hva Hve uid Hfit) as LAY. pose proof HBArg.istrlen_ecalls as EC.
    eapply (xe_sound HASEGS HAT NX LIMIT SVG argH fs hat_in_hull hat_hull_ok ISP (HBArg.argH0_high_ha sp argv envp rdraw hw Hsp Hva uid) NX_spw AA SF SA
             RtStrlen.W_istrlen_0 RtStrlen.W_istrlen_4 RtStrlen.W_istrlen_8 RtStrlen.W_istrlen_12 RtStrlen.W_istrlen_16 RtStrlen.W_istrlen_20 RtStrlen.W_istrlen_24);
      [cbn; lia | exact EC | exact LAY
      | exact (HBArg.vals_of_SV sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit SVG SVG_to1)
      | exact (HBArg.str_of_SV sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit SVG SVG_to1)
      | reflexivity | exact HBArg.Gro_ha | exact HBArg.stdio_ha | exact HBArg.Gfile_ha].
  Qed.

  Theorem hag_XB_sound : ext2_stmt HASEGS HAT NX LIM hag_XB SVG argH ISP fs.
  Proof. unfold ext2_stmt, hag_XB. intros. discriminate. Qed.

  (* [comment removed for export] *)
  Variable HS : nat -> option acs.
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs0, env_agree NX E E' -> HOLES h E fs0 = HOLES h E' fs0.
  Hypothesis HOLES_nil : forall h E fs0, HOLES h E fs0 [].
  Hypothesis HOLES_mod : forall h E fs0, HOLES h E fs0 = HOLES (CAP.hole_cls h) E fs0.
  Hypothesis HS_sound : holes_stmt HASEGS HAT LIM HS SVG argH ISP HOLES fs.
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound HASEGS IT.
  Variable KC : nat.
  Variable GC : bool.

  Theorem hag_check_sound : forall FUEL BFUEL p cs s,
    CAP.check HASEGS IT HAT NX LIM (hag_XN NX) (hag_XE NX) hag_XB HS KC true false GC BFUEL FUEL None cs p = COk s ->
    forall E R FULL model, cs_ok HASEGS HAT LIM SVG argH ISP fs E cs R FULL model ->
      crz HASEGS (cfg_of HASEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros FUEL BFUEL p cs s Hchk E R FULL model HC.
    exact (check_sound HASEGS IT IT_ok HAT NX LIM HS (hag_XN NX) (hag_XE NX) hag_XB
              hat_segs_wx hat_in_hull hat_hull_ok hat_shadow_ok hat_zone_ok NX_spw SVG argH ISP AH AA SF SA SP
              HOLES HOLES_agree HOLES_nil HOLES_mod fs KC GC
              obg_sys obg_brk2 obg_mmap2 obg_mmapin obg_mprotect2 obg_exit obg_x obg_join obg_joinx
              hag_XN_sound hag_XE_sound hag_XB_sound HS_sound
              FUEL BFUEL None p cs s Hchk E R FULL model t_nil HC I eq_refl).
  Qed.
End HAGCheck.
