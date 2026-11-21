(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch is the run's whole ProcInput, with the mmap base and the image entry; argH0_high's unread Section variables are supplied from this image's tables). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ZStores AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanNodesStartX AsanNodesStartXInit AsanPopFree AsanXSniffOff.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import RtIStrncpy B_Sums B_SumsSpecs B_code_startx B_PlanImage B_Atable.
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
  (* LPS 08b1429: the launch is the run's whole [ProcInput] and AsanInit's Section takes it. *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Variable fs : Fs.Fs.
  Hypothesis IMG : img_facts B_SEGS B_T B_PH.
  Hypothesis Hapc : Z.of_N AsanUbsan.M.init_pc = a_entry B_T.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk B_SEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis S0 : forall E M, SINV E M -> SINV0 B_PH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp E M.
  Hypothesis SF : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation LIM := AsanInit.LIMIT.
  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
  Proof.
    (* as A_XAll.v:63. *)
    intros E a H.
    eapply argH0_high;
      (* as A_XAll.v:74-91: the probe named "(list Segment)", then "atable", then
         "PhdrInfo" on three successive rounds - Section Init's segs, A and ph, all three
         globals here.  The remaining Section Init variables unification cannot fix are
         named here too rather than discovered one round at a time: apc (an N, reached
         through entryw = Z_to_bv 64 (Z.of_N apc)) and LIM with its LIM_MIN bound
         (AsanInit.v:94-95, discharged by AsanInit.LIMIT_ok at :30).  Hzr (:123) is not a
         dependency of argH0_high (:810); its only use is kunk_atr at :1230. *)
      try first [exact H | exact B_SEGS | exact B_T | exact B_PH | exact AsanUbsan.M.init_pc
                | exact AsanInit.LIMIT | exact AsanInit.LIMIT_ok
                | exact Hsp | exact Hva | exact Hve | exact Hlaunch | exact Hlau
                | exact Hbrk | exact Hmb | exact IMG | exact Hapc | exact Huid | exact Hrdr];
      first [exact H | eassumption | reflexivity].
  Qed.
  Let AA := argH0_agree sp rdraw inp.

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
      eapply (init_x_sound_envscan B_SEGS B_T B_PH B_t_segs_wx B_t_in_hull B_t_hull_ok LIM W_557498 W_55749c W_5574a0);
        [ cbn; lia
        | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_557498) | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_55749c) | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_5574a0)
        | repeat split; reflexivity | exact D_557498 | exact D_55749c | exact D_5574a0 | try eassumption .. ].
    - (* [comment removed for export] *)
      eapply (init_x_sound_pnscan B_SEGS B_T B_PH B_t_segs_wx B_t_in_hull B_t_hull_ok LIM W_557554 W_557558 W_55755c W_557560 W_557564);
        [ cbn; lia
        | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_557554) | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_557558) | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_55755c)
        | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_557560) | exact (B_fetch_at B_SEGS _ _ _ eq_refl F_557564)
        | repeat split; reflexivity | exact D_557554 | exact D_557558 | exact D_55755c | exact D_557560 | exact D_557564 | try eassumption .. ].
    - apply init_x_sound_layout.
    - exact (APSX.node_x_sound_XIStrncpy B_SEGS B_T NX0 LIM B_t_segs_wx B_t_in_hull B_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs B_istrncpy_spec).
    - exact (APSX.node_x_sound_XPopFree B_SEGS B_T NX0 LIM B_t_segs_wx B_t_in_hull B_t_hull_ok SINV argH ISP
               AH NX0_spw AA SF SA fs B_popfree_spec).
    - apply x_stmt_sniff_off. cbn [sniff_tab B_T]. lia.
  Qed.
End B_XAll.
