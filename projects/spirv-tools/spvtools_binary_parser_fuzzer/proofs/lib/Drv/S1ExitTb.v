(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk MemSplit Hoare ShapeAlg ShapeLaws Nodes RefNodes SymExec3 SymExec3Sound SymRun3 SymDrive3 SRealizes SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymExecA SymExecASound S1StartInit S1SpecConsts S1StdioDefs S1StdioWrite S1ExitKn S1ExitDefs S1Exit S1KnCut3 S1ExitTDefs S1ExitT S1_code_cf054_d0138.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
Import SX2. Import SX2S. Import SXA. Import SXAS.

Abbreviation SEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ExitTP.
  Context {fx : FPState}.
  Ltac evl := lazy [edenot ev vals_ev vals1 junk_vals nth app map seq N.to_nat Pos.to_nat Pos.iter_op Nat.add length].
  Ltac krd3 HK a n H :=
    lazymatch type of HK with know_ok ?segs ?Ee ?Mm ?kn =>
      let r := eval vm_compute in (SymDrive3.kread segs kn (ELit 0) a n) in
      lazymatch r with
      | Some ?v =>
        pose proof (SymDrive3.kread_rdn segs Ee Mm kn (ELit 0) a n v HK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
                     ltac:(unfold flat, estart; cbn [a_base a_off edenot]; rewrite (u_small64 0) by lia; lia)) as H;
        unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; rewrite (u_small64 0), Z.add_0_l in H by lia
      | None => fail "krd3: knowledge does not determine this read"
      end end.

  Lemma c1b_run : sym_execA SEGS 3000 true [SW_ENTRY] (SCR [] [] []) (SS EXIT sr_exit [] (kn_exit_tp 0x1212ac) 40) [] = (fst (fst c1b), snd (fst c1b), snd c1b).
  Proof. vm_compute. reflexivity. Qed.
  Lemma k1b_run : carry (s_log (fst (fst c1b))) (kn_exit_tp 0x1212ac) [] = (fst (fst k1b), snd (fst k1b), snd k1b).
  Proof. vm_compute. reflexivity. Qed.
  Lemma c2b_run : sym_execA SEGS 3000 true [] (SCR [] [] []) (SS SW_RET sr2b [] kn2b 72) [] = (fst (fst c2b), snd (fst c2b), snd c2b).
  Proof. vm_compute. reflexivity. Qed.
  Theorem s1_exit_tp_b : forall pend regs mem model code,
    exit_pre_tp 0x1212ac pend regs mem model code ->
    srealizes SEGS (mkCfg (mkst regs (0xd00fc : word) mem (seg_rom SEGS)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 1)) pend) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
  Proof.
    intros pend regs mem model code PRE.
    destruct (tp_entry _ _ _ _ _ _ PRE) as (tid & can & Htid & HR & HK).
    pose proof (etp_sp _ _ _ _ _ _ PRE) as Hsp. pose proof (etp_halt _ _ _ _ _ _ PRE) as Hh. pose proof (etp_lazy _ _ _ _ _ _ PRE) as Hlazy.
    set (vals := vals1 regs tid can) in *. set (E := Env (vals_ev vals) (fun _ : nat => @nil byte)) in *.
    assert (E0 : vals_ev vals 0 = getr regs 2) by reflexivity.

    destruct (runA_sound SEGS 3000 [SW_ENTRY] (SCR [] [] []) EXIT sr_exit (kn_exit_tp 0x1212ac) 40
                (fst (fst c1b)) (snd (fst c1b)) (snd c1b) E mem (seg_rom SEGS) regs
                c1b_run
                HR HK ltac:(rewrite c1b_scs; constructor)) as (R1 & HR1 & Hlf1 & Hms1).
    rewrite c1b_pc in Hms1.
    replace (Z_to_bv 64 EXIT) with (0xd00fc : word) in Hms1 by (apply bv_eq; reflexivity).
    eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms1 |].
    pose proof (carry_after SEGS E mem (s_log (fst (fst c1b))) (kn_exit_tp 0x1212ac) [] (fst (fst k1b)) (snd (fst k1b)) (snd k1b)
                  k1b_run
                  Hlf1 HK ltac:(rewrite k1b_scs; constructor)) as HK1.

    replace (Z_to_bv 64 SW_ENTRY) with (0xd537c : word) by (apply bv_eq; reflexivity).
    set (M1 := mem_denot E mem (s_log (fst (fst c1b)))) in *.
    assert (G2 : getr R1 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) - 240)).
    { rewrite (sr_val E _ R1 2 (EAlu ALU_ADD (EVar 0) (ELit (-240))) HR1 ltac:(vm_compute; reflexivity)).
      subst E. rewrite edenot_sp_off, E0. f_equal; lia. }
    assert (G10 : getr R1 10 = Z_to_bv 64 0xee390) by (rewrite (sr_val E _ R1 10 (ELit 0xee390) HR1 ltac:(vm_compute; reflexivity)); reflexivity).
    assert (G11 : getr R1 11 = Z_to_bv 64 0) by (rewrite (sr_val E _ R1 11 (ELit 0) HR1 ltac:(vm_compute; reflexivity)); reflexivity).
    assert (G12 : getr R1 12 = Z_to_bv 64 0) by (rewrite (sr_val E _ R1 12 (ELit 0) HR1 ltac:(vm_compute; reflexivity)); reflexivity).
    assert (G1 : getr R1 1 = Z_to_bv 64 SW_RET) by (rewrite (sr_val E _ R1 1 (ELit 0xd500c) HR1 ltac:(vm_compute; reflexivity)); reflexivity).
    krd3 HK1 0xee3b8%Z 8%nat Fwpos. krd3 HK1 0xee3c8%Z 8%nat Fwbase. krd3 HK1 0xee408%Z 4%nat Ffd.
    krd3 HK1 0xee3e8%Z 8%nat Fbuf. krd3 HK1 0xee3f0%Z 8%nat Fbsz.
    krd3 HK1 0xed0b8%Z 8%nat Fgot. krd3 HK1 0x120928%Z 8%nat Fcan.
    assert (PEND1 : rdn SEGS M1 (Z_to_bv 64 0x1212a8) (length pend) = Some pend).
    { subst M1. rewrite (rdn_mem_denot_out3 E 0 0x1212a8 0x1216a8); [exact (etp_pend _ _ _ _ _ _ PRE) | | | exact c1b_log | |].
      - subst E. cbn [ev]. rewrite E0. unfold LOGWIN. lia.
      - lia.
      - rewrite u_small64 by lia. lia.
      - rewrite u_small64 by lia. pose proof (etp_plen _ _ _ _ _ _ PRE). lia. }
    replace (map (WriteEv (Z_to_bv 64 1)) pend) with (map (WriteEv (Z_to_bv 64 1)) (pend ++ [])) by (rewrite app_nil_r; reflexivity).
    pose proof (etp_plen _ _ _ _ _ _ PRE) as PLEN.
    eapply (ref_stdio_write R1 M1 model (bv_unsigned (getr regs 2) - 240) 0xee390 0x1212a8 0x1212ac 1
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0x1212a8) (Z_to_bv 64 1024) (ev E 35) (Z_to_bv 64 SW_RET) pend []
              (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
    + exact G2. + exact G10. + exact G11. + exact G12. + exact G1.
    + lia. + lia.
    + eapply store_ok_mono; [subst M1; apply mem_denot_grows|].
      eapply store_ok_sub; [ | exact (etp_stack _ _ _ _ _ _ PRE) | | ]; unfold EXIT_STACK; rewrite ?u_small64 by lia;
        rewrite ?Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    + lia. + lia.
    + constructor; [exact Fwpos | exact Fwbase | exact Ffd | exact Fbuf | exact Fbsz].
    + split; [exact Fgot | exact Fcan].
    + lia.
    + exact (etp_fd1 _ _ _ _ _ _ PRE).
    + exact Hh. + exact Hlazy.
    + lia. + lia. + lia.
    + rewrite u_small64 by lia. reflexivity.
    + cbn [length Z.of_nat]. lia.
    + left. lia.
    + left. rewrite !u_small64 by lia. lia.
    + rewrite !u_small64 by lia. lia.
    + exact PEND1.
    + reflexivity.
    + apply bv_eq. vm_compute. reflexivity.
    + apply t_exit_has_nil.
    +
      clear Hms1. intros R2 M2 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 SWP.
      set (vals2 := vals ++ junk_vals R2). set (E2 := Env (vals_ev vals2) (fun _ : nat => @nil byte)).
      assert (AG : env_agree 40 E E2) by (subst E E2 vals2; apply (vals_app_agree vals (junk_vals R2))).

      assert (HR2 : regs_ok E2 sr2b R2).
      { rewrite sr2b_eq. unfold sr_tp2_of. subst E2 vals2.
        change 40%N with (N.of_nat (length vals)).
        apply (regs_after_call vals (fun _ => []) _ R1 R2 KEPT_SW c1b_vars HR1).
        - intros i Hi. cbv [KEPT_SW In] in Hi.
          repeat (destruct Hi as [<-|Hi]; [split; [lia | rewrite <- nth_all_regs by lia; cbn [nth all_regs];
            first [ assumption
                  | rewrite Q1, G1; reflexivity
                  | rewrite Q2, G2; reflexivity ] ] |]).
          destruct Hi.
        - cbv [KEPT_SW In]. lia. }

      assert (HK2 : know_ok SEGS E2 M2 kn2b).
      { rewrite kn2b_eq. unfold kn_tp2_of. apply Forall_app. split.
        - apply (know_cut3_sound 0 (-352) (-240) ABS_TP 0x122000 SEGS E2 M1 M2).
          + unfold LOGWIN. lia.
          + subst E2 vals2. cbn [ev]. unfold vals_ev. rewrite app_nth1 by (subst vals; rewrite vals1_len; lia).
            change (nth (N.to_nat 0) vals (Z_to_bv 64 0)) with (vals_ev vals 0). rewrite E0. unfold LOGWIN. lia.
          + intros x Hx Habs. apply (swp_agree _ _ _ _ _ _ SWP).
            * subst E2 vals2. cbn [ev] in Hx. unfold vals_ev in Hx. rewrite app_nth1 in Hx by (subst vals; rewrite vals1_len; lia).
              change (nth (N.to_nat 0) vals (Z_to_bv 64 0)) with (vals_ev vals 0) in Hx. rewrite E0 in Hx. lia.
            * unfold ABS_TP in Habs. apply Forall_cons_iff in Habs as [H1 Habs]. cbn [fst snd] in H1. lia.
            * unfold ABS_TP in Habs. apply Forall_cons_iff in Habs as [_ Habs]. apply Forall_cons_iff in Habs as [H2 _]. cbn [fst snd] in H2. lia.
          + exact (swp_grows _ _ _ _ _ _ SWP).
          + unfold ABS_TP. repeat (apply Forall_cons; [cbn [snd]; lia|]). apply Forall_nil.
          + eapply know_ok_agree; [exact AG | exact k1b_vars | exact HK1].
        - repeat apply Forall_cons; try apply Forall_nil.
          + eapply kword_lit_intro; [cbn; lia | lia | cbn; lia | exact (swp_wend _ _ _ _ _ _ SWP) | vm_compute; reflexivity].
          + apply kword_rdn_intro; [cbn; lia | lia | cbn; lia | exact (swp_wpos _ _ _ _ _ _ SWP)].
          + apply kword_rdn_intro; [cbn; lia | lia | cbn; lia | exact (swp_wbase _ _ _ _ _ _ SWP)]. }

      destruct (runA_sound SEGS 3000 [] (SCR [] [] []) SW_RET sr2b kn2b 72
                  (fst (fst c2b)) (snd (fst c2b)) (snd c2b) E2 M2 (seg_rom SEGS) R2
                  c2b_run
                  HR2 HK2 ltac:(rewrite c2b_scs; constructor)) as (R3 & HR3 & _ & Hms3).
      rewrite c2b_pc in Hms3.
      replace (Z_to_bv 64 EXIT_ECALL) with (0xcfe0c : word) in Hms3 by (apply bv_eq; reflexivity).
      eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms3 |].
      eapply (srz_exit_at SEGS); [exact F_cfdd8 | exact E_cfdd8 | exact Hh | exact Hlazy | |].
      * left. rewrite (sr_val E2 _ R3 17 (ELit 94) HR3 c2b_a7). reflexivity.
      * rewrite (sr_val E2 _ R3 10 (EVar 2) HR3 c2b_a0). subst E2 vals2. cbn [edenot ev]. unfold vals_ev.
        rewrite app_nth1 by (subst vals; rewrite vals1_len; lia). subst vals. cbn. exact (etp_a0 _ _ _ _ _ _ PRE).
  Qed.
End ExitTP.
