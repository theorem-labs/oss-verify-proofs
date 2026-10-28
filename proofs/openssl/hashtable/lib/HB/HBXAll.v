(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ZStores AgentLib AsanAcct
  AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CxPlan CxPlanSound CxPlanSoundSums AsanInit
  CxNodesStartX CxNodesStartXInit AsanPopFree RtIStrncpy HBSums HBSumsSpecs HB_code_startx HBPlanImage HBAtable
  CxXSniffOff.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma ha_istrncpy_spec : APSX.istrncpy_spec HASEGS (x_istrncpy HAT) (x_sealed HAT).
Proof.
  intros mem0 dst regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  destruct (ha_istrncpy_sealed mem0 dst (seg_rom HASEGS) regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12) as (regs' & Hrun & Hag).
  assert (EE : Z_to_bv 64 (x_istrncpy HAT) = ha_istrncpy_entry) by (apply bv_eq; reflexivity).
  assert (EB : APSX.SEALED_BYTES = strncpy_sealed_bytes) by reflexivity.
  exists regs'. split; [rewrite EE, EB; exact Hrun|]. split.
  - apply (kept_ok_of_regs_agree istrncpy_clob); [|exact Hag].
    intros r Hr. unfold istrncpy_clob in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; tauto.
  - rewrite (Hag 10%bv); [exact H10|]. unfold istrncpy_clob. cbn [In].
    intros [X|[X|[X|[X|[X|[]]]]]]; apply (f_equal bv_unsigned) in X; cbv in X; discriminate.
Qed.

(* [comment removed for export] *)
Lemma fetch_at : forall segs (a b : word) (w : bv 32),
  bv_unsigned a = bv_unsigned b -> fetch_word segs b = Some w -> fetch_word segs a = Some w.
Proof. intros segs a b w H F. assert (E : a = b) by (apply bv_eq; exact H). rewrite E. exact F. Qed.

Section HAXAll.
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
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis S0 : forall E M, SINV E M -> SINV0 HAPH sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SF : forall E M M', (forall a, argH0 HAPH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  Let AH := argH0_high HAPH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree HAPH sp rdraw argv envp uid hw.

  Theorem ha_x_all_sinv : forall x, x_stmt HASEGS HAT NX0 AsanInit.LIMIT SINV argH ISP fs x.
  Proof.
    intros [ | | | | | | | | | | ].
    - exact (APSX.node_x_sound_XIMemset HASEGS HAT NX0 LIMIT hat_segs_wx hat_in_hull hat_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs ha_fill_spec_imemset).
    - exact (APSX.node_x_sound_XIMemcpy HASEGS HAT NX0 LIMIT hat_segs_wx hat_in_hull hat_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs ha_segs_wr ha_copy_spec_imemcpy).
    - exact (APSX.node_x_sound_XMemset HASEGS HAT NX0 LIMIT hat_segs_wx hat_in_hull hat_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs ha_fill_spec_memset).
    - exact (APSX.node_x_sound_XMemcpy HASEGS HAT NX0 LIMIT hat_segs_wx hat_in_hull hat_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs ha_segs_wr ha_copy_spec_memcpy).
    - exact (APSX.node_x_sound_XMemIsZero HASEGS HAT NX0 LIMIT hat_segs_wx hat_in_hull hat_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs ha_miz_spec).
    - (* [comment removed for export] *)
      eapply (init_x_sound_envscan HASEGS HAT HAPH hat_segs_wx hat_in_hull hat_hull_ok W_51c410 W_51c414 W_51c418);
        [ cbn; lia
        | exact (fetch_at HASEGS _ _ _ eq_refl F_51c410) | exact (fetch_at HASEGS _ _ _ eq_refl F_51c414) | exact (fetch_at HASEGS _ _ _ eq_refl F_51c418)
        | repeat split; reflexivity | exact D_51c410 | exact D_51c414 | exact D_51c418 | try diet_eassumption .. ].
    - (* [comment removed for export] *)
      eapply (init_x_sound_pnscan HASEGS HAT HAPH hat_segs_wx hat_in_hull hat_hull_ok W_51c4cc W_51c4d0 W_51c4d4 W_51c4d8 W_51c4dc);
        [ cbn; lia
        | exact (fetch_at HASEGS _ _ _ eq_refl F_51c4cc) | exact (fetch_at HASEGS _ _ _ eq_refl F_51c4d0) | exact (fetch_at HASEGS _ _ _ eq_refl F_51c4d4)
        | exact (fetch_at HASEGS _ _ _ eq_refl F_51c4d8) | exact (fetch_at HASEGS _ _ _ eq_refl F_51c4dc)
        | repeat split; reflexivity | exact D_51c4cc | exact D_51c4d0 | exact D_51c4d4 | exact D_51c4d8 | exact D_51c4dc | try diet_eassumption .. ].
    - exact (init_x_sound_layout HASEGS HAT HAPH sp rdraw argv envp fs uid hw SINV).
    - exact (APSX.node_x_sound_XIStrncpy HASEGS HAT NX0 LIMIT hat_segs_wx hat_in_hull hat_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs ha_istrncpy_spec).
    - exact (APSX.node_x_sound_XPopFree HASEGS HAT NX0 LIMIT hat_segs_wx hat_in_hull hat_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs ha_popfree_spec).
    - apply x_stmt_sniff_off. cbn [sniff_tab HAT]. lia.
  Qed.
End HAXAll.

