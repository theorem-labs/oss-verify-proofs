(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.pem.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ZStores AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanNodesStartX AsanNodesStartXInit AsanPopFree AsanXSniffOff.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import RtIStrncpy B_Sums B_SumsSpecs B_code_startx B_PlanImage B_Gsh B_Atable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma B_istrncpy_spec : APSX.istrncpy_spec B_SEGS (x_istrncpy B_T) (x_sealed B_T).
Proof.
  intros mem0 dst regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  destruct (B_istrncpy_sealed mem0 dst (seg_rom B_SEGS) regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12) as (regs' & Hrun & Hag).
  assert (EE : Z_to_bv 64 (x_istrncpy B_T) = B_istrncpy_entry) by (apply bv_eq; reflexivity).
  assert (EB : APSX.SEALED_BYTES = strncpy_sealed_bytes) by reflexivity.
  exists regs'. split; [rewrite EE, EB; exact Hrun|]. split.
  - apply (kept_ok_of_regs_agree istrncpy_clob); [|exact Hag].
    intros r Hr. unfold istrncpy_clob in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; tauto.
  - rewrite (Hag 10%bv); [exact H10|]. unfold istrncpy_clob. cbn [In].
    intros [X|[X|[X|[X|[X|[]]]]]]; apply (f_equal bv_unsigned) in X; cbv in X; discriminate.
Qed.

(* [comment removed for export] *)
Lemma B_fetch_at : forall segs (a b : word) (w : bv 32),
  bv_unsigned a = bv_unsigned b -> fetch_word segs b = Some w -> fetch_word segs a = Some w.
Proof. intros segs a b w H F. assert (E : a = b) by (apply bv_eq; exact H). rewrite E. exact F. Qed.

Section B_XAll.
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
  Hypothesis S0 : forall E M, SINV E M -> SINV0 B_PH sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SF : forall E M M', (forall a, argH0 B_PH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  #[local] Notation argH := (argH0 B_PH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation LIM := AsanInit.LIMIT.
  Let AH := argH0_high B_PH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree B_PH sp rdraw argv envp uid hw.

  Theorem B_x_all_sinv : forall x, x_stmt B_SEGS B_T NX0 LIM SINV argH ISP fs x.
  Proof.
    intros [ | | | | | | | | | | ].
    - exact (APSX.node_x_sound_XIMemset B_SEGS B_T NX0 LIM B_t_segs_wx B_t_in_hull B_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs B_fill_spec_imemset).
    - exact (APSX.node_x_sound_XIMemcpy B_SEGS B_T NX0 LIM B_t_segs_wx B_t_in_hull B_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs B_segs_wr B_copy_spec_imemcpy).
    - exact (APSX.node_x_sound_XMemset B_SEGS B_T NX0 LIM B_t_segs_wx B_t_in_hull B_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs B_fill_spec_memset).
    - exact (APSX.node_x_sound_XMemcpy B_SEGS B_T NX0 LIM B_t_segs_wx B_t_in_hull B_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs B_segs_wr B_copy_spec_memcpy).
    - exact (APSX.node_x_sound_XMemIsZero B_SEGS B_T NX0 LIM B_t_segs_wx B_t_in_hull B_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs B_miz_spec).
    - (* [comment removed for export] *)
      eapply (init_x_sound_envscan B_SEGS B_T B_PH B_t_segs_wx B_t_in_hull B_t_hull_ok LIM W_552d90 W_552d94 W_552d98);
        [ cbn; lia
        | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_552d90) | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_552d94) | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_552d98)
        | repeat split; reflexivity | exact D_552d90 | exact D_552d94 | exact D_552d98 | try eassumption .. ].
    - (* [comment removed for export] *)
      eapply (init_x_sound_pnscan B_SEGS B_T B_PH B_t_segs_wx B_t_in_hull B_t_hull_ok LIM W_552e4c W_552e50 W_552e54 W_552e58 W_552e5c);
        [ cbn; lia
        | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_552e4c) | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_552e50) | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_552e54)
        | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_552e58) | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_552e5c)
        | repeat split; reflexivity | exact D_552e4c | exact D_552e50 | exact D_552e54 | exact D_552e58 | exact D_552e5c | try eassumption .. ].
    - exact (init_x_sound_layout B_SEGS B_T B_PH LIM sp rdraw argv envp fs uid hw SINV).
    - exact (APSX.node_x_sound_XIStrncpy B_SEGS B_T NX0 LIM B_t_segs_wx B_t_in_hull B_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs B_istrncpy_spec).
    - exact (APSX.node_x_sound_XPopFree B_SEGS B_T NX0 LIM B_t_segs_wx B_t_in_hull B_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs B_popfree_spec).
    - apply x_stmt_sniff_off. cbn [sniff_tab B_T]. lia.
  Qed.
End B_XAll.
