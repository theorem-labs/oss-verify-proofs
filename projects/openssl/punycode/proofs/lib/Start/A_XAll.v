(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.punycode.images Require Import Asan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ZStores AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanNodesStartX AsanNodesStartXInit AsanPopFree AsanXSniffOff.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import RtIStrncpy A_Sums A_SumsSpecs A_code_startx A_PlanImage A_Atable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma A_istrncpy_spec : APSX.istrncpy_spec A_SEGS (x_istrncpy A_T) (x_sealed A_T).
Proof.
  intros mem0 dst regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  destruct (A_istrncpy_sealed mem0 dst (seg_rom A_SEGS) regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12) as (regs' & Hrun & Hag).
  assert (EE : Z_to_bv 64 (x_istrncpy A_T) = A_istrncpy_entry) by (apply bv_eq; reflexivity).
  assert (EB : APSX.SEALED_BYTES = strncpy_sealed_bytes) by reflexivity.
  exists regs'. split; [rewrite EE, EB; exact Hrun|]. split.
  - apply (kept_ok_of_regs_agree istrncpy_clob); [|exact Hag].
    intros r Hr. unfold istrncpy_clob in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; tauto.
  - rewrite (Hag 10%bv); [exact H10|]. unfold istrncpy_clob. cbn [In].
    intros [X|[X|[X|[X|[X|[]]]]]]; apply (f_equal bv_unsigned) in X; cbv in X; discriminate.
Qed.

(* [comment removed for export] *)
Lemma A_fetch_at : forall segs (a b : word) (w : bv 32),
  bv_unsigned a = bv_unsigned b -> fetch_word segs b = Some w -> fetch_word segs a = Some w.
Proof. intros segs a b w H F. assert (E : a = b) by (apply bv_eq; exact H). rewrite E. exact F. Qed.

Section A_XAll.
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
  Hypothesis S0 : forall E M, SINV E M -> SINV0 A_PH sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SF : forall E M M', (forall a, argH0 A_PH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  #[local] Notation argH := (argH0 A_PH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation LIM := AsanInit.LIMIT.
  Let AH := argH0_high A_PH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree A_PH sp rdraw argv envp uid hw.

  Theorem A_x_all_sinv : forall x, x_stmt A_SEGS A_T NX0 LIM SINV argH ISP fs x.
  Proof.
    intros [ | | | | | | | | | | ].
    - exact (APSX.node_x_sound_XIMemset A_SEGS A_T NX0 LIM A_t_segs_wx A_t_in_hull A_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs A_fill_spec_imemset).
    - exact (APSX.node_x_sound_XIMemcpy A_SEGS A_T NX0 LIM A_t_segs_wx A_t_in_hull A_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs A_segs_wr A_copy_spec_imemcpy).
    - exact (APSX.node_x_sound_XMemset A_SEGS A_T NX0 LIM A_t_segs_wx A_t_in_hull A_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs A_fill_spec_memset).
    - exact (APSX.node_x_sound_XMemcpy A_SEGS A_T NX0 LIM A_t_segs_wx A_t_in_hull A_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs A_segs_wr A_copy_spec_memcpy).
    - exact (APSX.node_x_sound_XMemIsZero A_SEGS A_T NX0 LIM A_t_segs_wx A_t_in_hull A_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs A_miz_spec).
    - (* [comment removed for export] *)
      eapply (init_x_sound_envscan A_SEGS A_T A_PH A_t_segs_wx A_t_in_hull A_t_hull_ok LIM W_51e604 W_51e608 W_51e60c);
        [ cbn; lia
        | exact (A_fetch_at A_SEGS _ _ _ eq_refl F_51e604) | exact (A_fetch_at A_SEGS _ _ _ eq_refl F_51e608) | exact (A_fetch_at A_SEGS _ _ _ eq_refl F_51e60c)
        | repeat split; reflexivity | exact D_51e604 | exact D_51e608 | exact D_51e60c | try eassumption .. ].
    - (* [comment removed for export] *)
      eapply (init_x_sound_pnscan A_SEGS A_T A_PH A_t_segs_wx A_t_in_hull A_t_hull_ok LIM W_51e6c0 W_51e6c4 W_51e6c8 W_51e6cc W_51e6d0);
        [ cbn; lia
        | exact (A_fetch_at A_SEGS _ _ _ eq_refl F_51e6c0) | exact (A_fetch_at A_SEGS _ _ _ eq_refl F_51e6c4) | exact (A_fetch_at A_SEGS _ _ _ eq_refl F_51e6c8)
        | exact (A_fetch_at A_SEGS _ _ _ eq_refl F_51e6cc) | exact (A_fetch_at A_SEGS _ _ _ eq_refl F_51e6d0)
        | repeat split; reflexivity | exact D_51e6c0 | exact D_51e6c4 | exact D_51e6c8 | exact D_51e6cc | exact D_51e6d0 | try eassumption .. ].
    - exact (init_x_sound_layout A_SEGS A_T A_PH LIM sp rdraw argv envp fs uid hw SINV).
    - exact (APSX.node_x_sound_XIStrncpy A_SEGS A_T NX0 LIM A_t_segs_wx A_t_in_hull A_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs A_istrncpy_spec).
    - exact (APSX.node_x_sound_XPopFree A_SEGS A_T NX0 LIM A_t_segs_wx A_t_in_hull A_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs A_popfree_spec).
    - apply x_stmt_sniff_off. cbn [sniff_tab A_T]. lia.
  Qed.
End A_XAll.
