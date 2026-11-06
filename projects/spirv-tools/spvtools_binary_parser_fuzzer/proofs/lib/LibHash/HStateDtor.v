(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_666bc_667d8.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_667d4 : bv 32 := 0x00008067.
Lemma F_667d4 : fetch_word Plain.M.loaded_segments (0x66814 : word) = Some W_667d4.
Proof. vm_refl. Qed.
Lemma D_667d4 : decode_any W_667d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_666bc_667d8.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.S1_code_6db30_6db3c.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff FPSteps SumMemsetLib SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HRepFacts HStmts HConstsS1 HCommon.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStateDtor.S1_code_666bc_667d8. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import S1_code_6db30_6db3c.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.

Definition SDT      : Z := 0x666fc.
Definition V3_PC    : Z := 0x66710.
Definition V2_PC    : Z := 0x66728.
Definition V1_PC    : Z := 0x66740.
Definition M3_PC    : Z := 0x66758.
Definition LOOP3    : Z := 0x66760.
Definition DRET3    : Z := 0x6676c.
Definition A3_PC    : Z := 0x66774.
Definition M2_PC    : Z := 0x6678c.
Definition LOOP2    : Z := 0x66794.
Definition DRET2    : Z := 0x667a0.
Definition A2_PC    : Z := 0x667a8.
Definition M1_PC    : Z := 0x667c0.
Definition LOOP1    : Z := 0x667c8.
Definition DRET1    : Z := 0x667d4.
Definition A1_PC    : Z := 0x667dc.
Definition RET_PC   : Z := 0x66814.
Definition DELSZ    : Z := 0x6db74.
Definition DELETE   : Z := 0x6db70.

Definition STOPS : list Z :=
  [DELSZ; V3_PC; V2_PC; V1_PC; M3_PC; LOOP3; A3_PC; M2_PC; LOOP2; A2_PC; M1_PC; LOOP1; A1_PC; RET_PC].

Section Dtor.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Variable DEL_STACK : Z.
  Hypothesis DEL_STACK_nn : 0 <= DEL_STACK.
  Hypothesis DEL : delete_rule_stmt SEGS L MI DEL_STACK.

  Hypothesis HLdel : ly_delete L = DELETE.
  Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
  Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
  Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.

  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI HLimg_lo HLrw_img HLerr_rw).
  #[local] Abbreviation umapx_via_eff' := (umapx_via_eff L MI HLimg_lo HLrw_img HLerr_rw).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI HLimg_lo HLerr_rw).

  Lemma del_call : forall fx A M model R (p n spc r : Z) K,
    ainv MI A M model -> mstd model -> img_ro_clear L M ->
    getr R 1%bv = Z_to_bv 64 r -> ret_ok (Z_to_bv 64 r) -> 0 <= r < 2 ^ 64 ->
    getr R 2%bv = Z_to_bv 64 spc -> spc mod 16 = 0 -> spc < 2 ^ 47 ->
    getr R 3%bv = Z_to_bv 64 (ly_gp L) -> getr R 4%bv = Z_to_bv 64 (ly_tp L) ->
    getr R 10%bv = Z_to_bv 64 p -> (p = 0 /\ n = 0 \/ In (p, n) (live MI A)) ->
    alloc_ceiling + DEL_STACK <= spc -> 0x122000 <= spc - DEL_STACK ->
    defined M (spc - DEL_STACK) DEL_STACK ->
    (forall a, zwin (spc - DEL_STACK) spc a -> ~ owned MI A a) ->
    (forall A' R' M' model',
        ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
        kept R R' -> live_del p (live MI A) (live MI A') ->
        eff MI A A' M M' (spc - DEL_STACK, spc) (fun a => p <= a < p + n) ->
        defined M' (spc - DEL_STACK) DEL_STACK ->
        (forall a, zwin (spc - DEL_STACK) spc a -> ~ owned MI A' a) ->
        srealizes SEGS (cfg fx R' r M' model') K) ->
    srealizes SEGS (cfg fx R DELSZ M model) K.
  Proof using AC L MI DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw.
    intros fx A M model R p n spc r K AI MS ROC H1 Hret Hr H2 Hsp16 Hsphi H3 H4 H10 Hp Hce Hlo Hdef Hwin POST.
    pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ].
    { unfold DELSZ. norm_pc. stepj F_6db34 D_6db34. apply mst_refl. }
    replace (0x6db70%bv : word) with (Z_to_bv 64 (ly_delete L)) by (rewrite HLdel; apply bv_eq; reflexivity).
    eapply (DEL fx A R M model p n spc r K AI MS ROC).
    - constructor; assumption.
    - exact H10.
    - exact Hp.
    - lia.
    - apply stack_room_of_defined; [lia | lia | lia | exact Hdef].
    - exact Hwin.
    - intros A' R2 M' model' AI' MS' Hfs Hfds KEPT LDEL CAPS BIGC OWN FR DEF.
      assert (Hdef' : defined M' (spc - DEL_STACK) DEL_STACK).
      { intros i Hi. destruct (DEF (Z_to_bv 64 (spc - DEL_STACK + i)) (Hdef i Hi)) as [Hm|[Ho|[Hq|He]]];
          [exact Hm| exfalso | exfalso | exfalso].
        - rewrite u64_of_Z in Ho by lia. exact (Hwin (spc - DEL_STACK + i) ltac:(unfold zwin; lia) Ho).
        - rewrite u64_of_Z in Hq by lia. destruct Hp as [[-> ->]|Hin]; [lia|].
          destruct (live_facts' A M model p n AI Hin) as (_ & _ & Hpc & _). lia.
        - rewrite u64_of_Z in He by lia. pose proof (HLimg_lo _ (HLrw_img _ (HLerr_rw _ He))). lia. }
      assert (Hwin' : forall a, zwin (spc - DEL_STACK) spc a -> ~ owned MI A' a).
      { intros a Ha Ho. destruct (OWN a Ho) as [Ho0|Hq]; [exact (Hwin a Ha Ho0)|]. unfold zwin in Ha.
        destruct Hp as [[-> ->]|Hin]; [lia|]. destruct (live_facts' A M model p n AI Hin) as (_ & _ & Hpc & _). lia. }
      apply (POST A' R2 M' model' AI' MS' Hfs Hfds KEPT LDEL); [| exact Hdef' | exact Hwin'].
      eapply eff_of_del; [exact CAPS | exact BIGC | exact OWN | exact FR | exact DEF | | intros a Ha; exact Ha
                        | intros a Ha; destruct Hp as [[-> ->]|Hin]; [lia | exact (live_offimg' A M model p n a AI Hin Ha)]].
      intros a Ha. exact Ha.
  Qed.

  Definition PRES : list reg := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
  Lemma pres_cs : forall r, In r PRES -> In r callee_saved.
  Proof using. intros r Hr. unfold PRES in Hr. unfold callee_saved. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr. Qed.

  Section Loops.
    Variables (sp : Z) (Rb : bvmap 5 word).
    Hypothesis Hsp16 : sp mod 16 = 0.
    Hypothesis Hsplo : alloc_ceiling + (32 + DEL_STACK) <= sp.
    Hypothesis Hsphi : sp < 2 ^ 47.
    Hypothesis Hspimg : 0x122000 <= sp - (32 + DEL_STACK).
    Hypothesis Rb2 : getr Rb 2%bv = Z_to_bv 64 (sp - 32).
    Hypothesis Rb3 : getr Rb 3%bv = Z_to_bv 64 (ly_gp L).
    Hypothesis Rb4 : getr Rb 4%bv = Z_to_bv 64 (ly_tp L).

    Definition nodes_foot {V : Type} (NS : Z) (l : list (Z * (Z * V))) (a : Z) : Prop :=
      exists p, In p (map fst l) /\ p <= a < p + NS.

    Definition free_loop_at (LOOP EXIT : Z) : Prop :=
      forall (V : Type) (NS : Z) (l : list (Z * (Z * V))) fx A M model R K,
      l <> [] -> 24 <= NS ->
      ainv MI A M model -> mstd model -> img_ro_clear L M ->
      pres PRES Rb R -> getr R 10%bv = Z_to_bv 64 (hdaddr l) ->
      (forall p k v, In (p, (k, v)) l -> In (p, NS) (live MI A)) ->
      NoDup (map fst l) -> chain SEGS M l ->
      defined M (sp - 32 - DEL_STACK) (32 + DEL_STACK) ->
      (forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A a) ->
      (forall A' M' model' R',
          ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
          pres PRES Rb R' ->
          eff MI A A' M M' (sp - 32 - DEL_STACK, sp - 32) (nodes_foot NS l) ->
          lapply (live MI A) (map (fun e => LDel (fst e)) l) (live MI A') ->
          defined M' (sp - 32 - DEL_STACK) (32 + DEL_STACK) ->
          (forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A' a) ->
          srealizes SEGS (cfg fx R' EXIT M' model') K) ->
      srealizes SEGS (cfg fx R LOOP M model) K.

    Lemma free_loop3 : free_loop_at LOOP3 A3_PC.
    Proof using AC L MI DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw sp Rb Hsp16 Hsplo Hsphi Hspimg Rb2 Rb3 Rb4.
      intros V NS l.
      induction l as [|[p [k v]] rest IH]; intros fx A M model R K Hne HNS AI MS ROC HP H10 Hlive Hnd Hch Hdef Hwin POST;
        [exfalso; exact (Hne eq_refl)|].
      pose proof ceiling_lt as Hcl.
      cbn [hdaddr] in H10. cbn [map fst] in Hnd.
      destruct Hch as [Hnext Hchr]. pose proof (proj1 Hnext) as Hnxr.
      destruct (live_facts' A M model p NS AI (Hlive p k v (or_introl eq_refl))) as (_ & Hp0 & Hpce & Hpown).

      pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 (hdaddr rest)]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.
      xruns HR HK 100%nat STOPS (SCR [] [EVar 40] []) 50%N.
      { split_scs; try sc_auto1. }
      lazymatch goal with H : regs_ok E _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HR1; rename Rx into R1 end.
      rreg HR1 10%bv G10. rreg HR1 1%bv G1. rreg HR1 9%bv G9.
      pose proof (syms_id_sound _ _ _ _ PRES HR1 eq_refl) as Ha1.
      eapply (del_call fx A M model R1 p NS (sp - 32) DRET3 K AI MS ROC G1);
      [ apply bv_eq; vm_compute; reflexivity
      | unfold DRET3; lia
      | rewrite (Ha1 2%bv) by inl; rewrite (HP 2%bv) by inl; exact Rb2
      | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16
      | lia
      | rewrite (Ha1 3%bv) by inl; rewrite (HP 3%bv) by inl; exact Rb3
      | rewrite (Ha1 4%bv) by inl; rewrite (HP 4%bv) by inl; exact Rb4
      | exact G10
      | right; exact (Hlive p k v (or_introl eq_refl))
      | lia | lia
      | intros i Hi; apply Hdef; lia
      | intros a Ha; apply Hwin; unfold zwin in *; lia
      | ].

      intros A' R2 M' model' AI' MS' Hfs Hfds KEPT LDEL EFF1 DEF' WIN'.
      assert (HP2 : pres PRES Rb R2).
      { eapply (pres_kept PRES Rb R1 R2 pres_cs); [|exact KEPT]. eapply pres_trans; [exact HP|]. intros r Hr. apply Ha1. exact Hr. }
      assert (G9' : getr R2 9%bv = Z_to_bv 64 (hdaddr rest)) by (rewrite (KEPT 9%bv) by inl; exact G9).
      assert (Hdef' : defined M' (sp - 32 - DEL_STACK) (32 + DEL_STACK)).
      { intros i Hi. destruct (Z.lt_ge_cases i DEL_STACK); [apply DEF'; lia|].
        apply (defined_via_eff L MI HLimg_lo HLrw_img HLerr_rw A A' M M' _ _ (sp - 32 - DEL_STACK) (32 + DEL_STACK) EFF1 ltac:(lia) ltac:(lia)
                 ltac:(intros j Hj; apply Hwin; unfold zwin; lia) ltac:(intros j Hj; cbn beta; lia) Hdef i Hi). }
      assert (Hwin' : forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A' a).
      { intros a Ha Ho. destruct (ef_own _ _ _ _ _ _ _ _ _ EFF1 a Ho) as [Ho0|[[_ [_ Hn]]|Hq]].
        - exact (Hwin a Ha Ho0).
        - exact (Hdef (a - (sp - 32 - DEL_STACK)) ltac:(unfold zwin in Ha; lia) ltac:(replace (sp - 32 - DEL_STACK + (a - (sp - 32 - DEL_STACK))) with a by lia; exact Hn)).
        - unfold zwin in Ha. lia. }

      pose (E2 := Eseed R2 [Z_to_bv 64 (hdaddr rest)]).
      assert (HR2 : regs_ok E2 (srs sr_id [(9%bv, EVar 32)]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK2 : know_ok SEGS E2 M' []) by constructor.
      destruct rest as [|[p' [k' v']] rest'].
      -
        cbn [hdaddr] in *.
        xruns HR2 HK2 100%nat STOPS (SCR [false] [] []) 50%N.
        { split_scs; try sc_auto1. }
        lazymatch goal with H : regs_ok E2 _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HR3; rename Rx into R3 end.
        apply (POST A' M' model' R3 AI' MS' Hfs Hfds).
        + eapply pres_trans; [exact HP2|]. intros r Hr. apply (syms_id_sound _ _ _ _ PRES HR3 eq_refl). exact Hr.
        + eapply eff_weaken; [exact EFF1|]. intros a Ha. exists p. split; [left; reflexivity | exact Ha].
        + cbn. exists (live MI A'). split; [exact LDEL | reflexivity].
        + exact Hdef'.
        + exact Hwin'.
      -
        xruns HR2 HK2 100%nat STOPS (SCR [true] [] []) 50%N.
        { split_scs; try sc_auto1. cbn [sc_denot]. evs. cbn [hdaddr].
          destruct (live_facts' A M model p' NS AI (Hlive p' k' v' (or_intror (or_introl eq_refl)))) as (_ & Hp0' & Hp1' & _).
          rewrite br_ne by lia. bool_lia. }
        cbn [hdaddr] in *.
        lazymatch goal with H : regs_ok E2 _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HR3; rename Rx into R3 end.
        assert (Hlive' : forall q kq vq, In (q, (kq, vq)) ((p', (k', v')) :: rest') -> In (q, NS) (live MI A')).
        { intros q kq vq Hin. apply (proj2 (LDEL q NS)). split; [apply (Hlive q kq vq); right; exact Hin|].
          intros ->. inversion Hnd as [| x l0 Hnotin Hnd']. apply Hnotin. apply base.list_elem_of_In. exact (in_map fst _ _ Hin). }
        assert (ROC' : img_ro_clear L M').
        { eapply (img_ro_clear_via_eff' A A' M M' model _ _ ROC AI EFF1); [| cbn; lia].
          intros a Ha. cbn beta in Ha. exact (live_offimg' A M model p NS a AI (Hlive p k v (or_introl eq_refl)) Ha). }
        eapply (IH fx A' M' model' R3 K ltac:(discriminate) HNS AI' MS' ROC').
        + eapply pres_trans; [exact HP2|]. intros r Hr. apply (syms_id_sound _ _ _ _ PRES HR3 eq_refl). exact Hr.
        + rreg HR3 10%bv G. exact G.
        + exact Hlive'.
        + inversion Hnd; assumption.
        +
          eapply (chain_agree SEGS V M M'); [exact Hchr|]. intros q kq vq Hin.
          destruct (live_facts' A M model q NS AI (Hlive q kq vq (or_intror Hin))) as (_ & Hq0 & Hqce & Hqown).
          assert (Hpq : p <> q).
          { intros <-. inversion Hnd as [| x l0 Hnotin Hnd']. apply Hnotin. apply base.list_elem_of_In. exact (in_map fst _ _ Hin). }
          pose proof (ai_live_disjoint MI A M model q NS p NS AI (Hlive q kq vq (or_intror Hin)) (Hlive p k v (or_introl eq_refl)) ltac:(congruence)) as Hapq.
          split; [|lia].
          intros i Hi. apply (ef_frame _ _ _ _ _ _ _ _ _ EFF1). rewrite u64_of_Z by lia.
          intros [Ho|[Ho'|[Hnm|[Hf|[Hw|He]]]]].
          * exact (proj1 (Hqown (q + i) ltac:(lia)) Ho).
          * destruct (ef_own _ _ _ _ _ _ _ _ _ EFF1 _ Ho') as [Ho0|[[_ [_ Hn]]|Hf]].
            -- exact (proj1 (Hqown (q + i) ltac:(lia)) Ho0).
            -- exact (proj2 (Hqown (q + i) ltac:(lia)) Hn).
            -- unfold apart in Hapq. lia.
          * destruct Hnm as (_ & _ & Hn). exact (proj2 (Hqown (q + i) ltac:(lia)) Hn).
          * unfold apart in Hapq. lia.
          * unfold W_of in Hw. cbn in Hw. lia.
          * exact (live_offimg' A M model q NS (q + i) AI (Hlive q kq vq (or_intror Hin)) ltac:(lia) (HLrw_img _ (HLerr_rw _ He))).
        + exact Hdef'.
        + exact Hwin'.
        +
          intros A'' M'' model'' R'' AI'' MS'' Hfs' Hfds' HP'' EFF2 LAP2 Hdef'' Hwin''.
          apply (POST A'' M'' model'' R'' AI'' MS''); [congruence | congruence | exact HP'' | | | exact Hdef'' | exact Hwin''].
          * eapply eff_weaken; [eapply eff_trans; [exact EFF1 | exact EFF2 |]|].
            -- intros a Ha. apply Hwin''. unfold W_of in Ha. cbn in Ha. unfold zwin. lia.
            -- intros a [Ha|(q & Hq & Hqa)]; [exists p; split; [left; reflexivity| exact Ha]|].
               exists q. split; [right; exact Hq | exact Hqa].
          * cbn. exists (live MI A'). split; [exact LDEL | exact LAP2].
    Qed.

    Lemma free_loop2 : free_loop_at LOOP2 A2_PC.
    Proof using AC L MI DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw sp Rb Hsp16 Hsplo Hsphi Hspimg Rb2 Rb3 Rb4.
      intros V NS l.
      induction l as [|[p [k v]] rest IH]; intros fx A M model R K Hne HNS AI MS ROC HP H10 Hlive Hnd Hch Hdef Hwin POST;
        [exfalso; exact (Hne eq_refl)|].
      pose proof ceiling_lt as Hcl.
      cbn [hdaddr] in H10. cbn [map fst] in Hnd.
      destruct Hch as [Hnext Hchr]. pose proof (proj1 Hnext) as Hnxr.
      destruct (live_facts' A M model p NS AI (Hlive p k v (or_introl eq_refl))) as (_ & Hp0 & Hpce & Hpown).

      pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 (hdaddr rest)]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.
      xruns HR HK 100%nat STOPS (SCR [] [EVar 40] []) 50%N.
      { split_scs; try sc_auto1. }
      lazymatch goal with H : regs_ok E _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HR1; rename Rx into R1 end.
      rreg HR1 10%bv G10. rreg HR1 1%bv G1. rreg HR1 9%bv G9.
      pose proof (syms_id_sound _ _ _ _ PRES HR1 eq_refl) as Ha1.
      eapply (del_call fx A M model R1 p NS (sp - 32) DRET2 K AI MS ROC G1);
      [ apply bv_eq; vm_compute; reflexivity
      | unfold DRET2; lia
      | rewrite (Ha1 2%bv) by inl; rewrite (HP 2%bv) by inl; exact Rb2
      | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16
      | lia
      | rewrite (Ha1 3%bv) by inl; rewrite (HP 3%bv) by inl; exact Rb3
      | rewrite (Ha1 4%bv) by inl; rewrite (HP 4%bv) by inl; exact Rb4
      | exact G10
      | right; exact (Hlive p k v (or_introl eq_refl))
      | lia | lia
      | intros i Hi; apply Hdef; lia
      | intros a Ha; apply Hwin; unfold zwin in *; lia
      | ].

      intros A' R2 M' model' AI' MS' Hfs Hfds KEPT LDEL EFF1 DEF' WIN'.
      assert (HP2 : pres PRES Rb R2).
      { eapply (pres_kept PRES Rb R1 R2 pres_cs); [|exact KEPT]. eapply pres_trans; [exact HP|]. intros r Hr. apply Ha1. exact Hr. }
      assert (G9' : getr R2 9%bv = Z_to_bv 64 (hdaddr rest)) by (rewrite (KEPT 9%bv) by inl; exact G9).
      assert (Hdef' : defined M' (sp - 32 - DEL_STACK) (32 + DEL_STACK)).
      { intros i Hi. destruct (Z.lt_ge_cases i DEL_STACK); [apply DEF'; lia|].
        apply (defined_via_eff L MI HLimg_lo HLrw_img HLerr_rw A A' M M' _ _ (sp - 32 - DEL_STACK) (32 + DEL_STACK) EFF1 ltac:(lia) ltac:(lia)
                 ltac:(intros j Hj; apply Hwin; unfold zwin; lia) ltac:(intros j Hj; cbn beta; lia) Hdef i Hi). }
      assert (Hwin' : forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A' a).
      { intros a Ha Ho. destruct (ef_own _ _ _ _ _ _ _ _ _ EFF1 a Ho) as [Ho0|[[_ [_ Hn]]|Hq]].
        - exact (Hwin a Ha Ho0).
        - exact (Hdef (a - (sp - 32 - DEL_STACK)) ltac:(unfold zwin in Ha; lia) ltac:(replace (sp - 32 - DEL_STACK + (a - (sp - 32 - DEL_STACK))) with a by lia; exact Hn)).
        - unfold zwin in Ha. lia. }

      pose (E2 := Eseed R2 [Z_to_bv 64 (hdaddr rest)]).
      assert (HR2 : regs_ok E2 (srs sr_id [(9%bv, EVar 32)]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK2 : know_ok SEGS E2 M' []) by constructor.
      destruct rest as [|[p' [k' v']] rest'].
      -
        cbn [hdaddr] in *.
        xruns HR2 HK2 100%nat STOPS (SCR [false] [] []) 50%N.
        { split_scs; try sc_auto1. }
        lazymatch goal with H : regs_ok E2 _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HR3; rename Rx into R3 end.
        apply (POST A' M' model' R3 AI' MS' Hfs Hfds).
        + eapply pres_trans; [exact HP2|]. intros r Hr. apply (syms_id_sound _ _ _ _ PRES HR3 eq_refl). exact Hr.
        + eapply eff_weaken; [exact EFF1|]. intros a Ha. exists p. split; [left; reflexivity | exact Ha].
        + cbn. exists (live MI A'). split; [exact LDEL | reflexivity].
        + exact Hdef'.
        + exact Hwin'.
      -
        xruns HR2 HK2 100%nat STOPS (SCR [true] [] []) 50%N.
        { split_scs; try sc_auto1. cbn [sc_denot]. evs. cbn [hdaddr].
          destruct (live_facts' A M model p' NS AI (Hlive p' k' v' (or_intror (or_introl eq_refl)))) as (_ & Hp0' & Hp1' & _).
          rewrite br_ne by lia. bool_lia. }
        cbn [hdaddr] in *.
        lazymatch goal with H : regs_ok E2 _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HR3; rename Rx into R3 end.
        assert (Hlive' : forall q kq vq, In (q, (kq, vq)) ((p', (k', v')) :: rest') -> In (q, NS) (live MI A')).
        { intros q kq vq Hin. apply (proj2 (LDEL q NS)). split; [apply (Hlive q kq vq); right; exact Hin|].
          intros ->. inversion Hnd as [| x l0 Hnotin Hnd']. apply Hnotin. apply base.list_elem_of_In. exact (in_map fst _ _ Hin). }
        assert (ROC' : img_ro_clear L M').
        { eapply (img_ro_clear_via_eff' A A' M M' model _ _ ROC AI EFF1); [| cbn; lia].
          intros a Ha. cbn beta in Ha. exact (live_offimg' A M model p NS a AI (Hlive p k v (or_introl eq_refl)) Ha). }
        eapply (IH fx A' M' model' R3 K ltac:(discriminate) HNS AI' MS' ROC').
        + eapply pres_trans; [exact HP2|]. intros r Hr. apply (syms_id_sound _ _ _ _ PRES HR3 eq_refl). exact Hr.
        + rreg HR3 10%bv G. exact G.
        + exact Hlive'.
        + inversion Hnd; assumption.
        +
          eapply (chain_agree SEGS V M M'); [exact Hchr|]. intros q kq vq Hin.
          destruct (live_facts' A M model q NS AI (Hlive q kq vq (or_intror Hin))) as (_ & Hq0 & Hqce & Hqown).
          assert (Hpq : p <> q).
          { intros <-. inversion Hnd as [| x l0 Hnotin Hnd']. apply Hnotin. apply base.list_elem_of_In. exact (in_map fst _ _ Hin). }
          pose proof (ai_live_disjoint MI A M model q NS p NS AI (Hlive q kq vq (or_intror Hin)) (Hlive p k v (or_introl eq_refl)) ltac:(congruence)) as Hapq.
          split; [|lia].
          intros i Hi. apply (ef_frame _ _ _ _ _ _ _ _ _ EFF1). rewrite u64_of_Z by lia.
          intros [Ho|[Ho'|[Hnm|[Hf|[Hw|He]]]]].
          * exact (proj1 (Hqown (q + i) ltac:(lia)) Ho).
          * destruct (ef_own _ _ _ _ _ _ _ _ _ EFF1 _ Ho') as [Ho0|[[_ [_ Hn]]|Hf]].
            -- exact (proj1 (Hqown (q + i) ltac:(lia)) Ho0).
            -- exact (proj2 (Hqown (q + i) ltac:(lia)) Hn).
            -- unfold apart in Hapq. lia.
          * destruct Hnm as (_ & _ & Hn). exact (proj2 (Hqown (q + i) ltac:(lia)) Hn).
          * unfold apart in Hapq. lia.
          * unfold W_of in Hw. cbn in Hw. lia.
          * exact (live_offimg' A M model q NS (q + i) AI (Hlive q kq vq (or_intror Hin)) ltac:(lia) (HLrw_img _ (HLerr_rw _ He))).
        + exact Hdef'.
        + exact Hwin'.
        +
          intros A'' M'' model'' R'' AI'' MS'' Hfs' Hfds' HP'' EFF2 LAP2 Hdef'' Hwin''.
          apply (POST A'' M'' model'' R'' AI'' MS''); [congruence | congruence | exact HP'' | | | exact Hdef'' | exact Hwin''].
          * eapply eff_weaken; [eapply eff_trans; [exact EFF1 | exact EFF2 |]|].
            -- intros a Ha. apply Hwin''. unfold W_of in Ha. cbn in Ha. unfold zwin. lia.
            -- intros a [Ha|(q & Hq & Hqa)]; [exists p; split; [left; reflexivity| exact Ha]|].
               exists q. split; [right; exact Hq | exact Hqa].
          * cbn. exists (live MI A'). split; [exact LDEL | exact LAP2].
    Qed.

    Lemma free_loop1 : free_loop_at LOOP1 A1_PC.
    Proof using AC L MI DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw sp Rb Hsp16 Hsplo Hsphi Hspimg Rb2 Rb3 Rb4.
      intros V NS l.
      induction l as [|[p [k v]] rest IH]; intros fx A M model R K Hne HNS AI MS ROC HP H10 Hlive Hnd Hch Hdef Hwin POST;
        [exfalso; exact (Hne eq_refl)|].
      pose proof ceiling_lt as Hcl.
      cbn [hdaddr] in H10. cbn [map fst] in Hnd.
      destruct Hch as [Hnext Hchr]. pose proof (proj1 Hnext) as Hnxr.
      destruct (live_facts' A M model p NS AI (Hlive p k v (or_introl eq_refl))) as (_ & Hp0 & Hpce & Hpown).

      pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 (hdaddr rest)]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.
      xruns HR HK 100%nat STOPS (SCR [] [EVar 40] []) 50%N.
      { split_scs; try sc_auto1. }
      lazymatch goal with H : regs_ok E _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HR1; rename Rx into R1 end.
      rreg HR1 10%bv G10. rreg HR1 1%bv G1. rreg HR1 9%bv G9.
      pose proof (syms_id_sound _ _ _ _ PRES HR1 eq_refl) as Ha1.
      eapply (del_call fx A M model R1 p NS (sp - 32) DRET1 K AI MS ROC G1);
      [ apply bv_eq; vm_compute; reflexivity
      | unfold DRET1; lia
      | rewrite (Ha1 2%bv) by inl; rewrite (HP 2%bv) by inl; exact Rb2
      | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16
      | lia
      | rewrite (Ha1 3%bv) by inl; rewrite (HP 3%bv) by inl; exact Rb3
      | rewrite (Ha1 4%bv) by inl; rewrite (HP 4%bv) by inl; exact Rb4
      | exact G10
      | right; exact (Hlive p k v (or_introl eq_refl))
      | lia | lia
      | intros i Hi; apply Hdef; lia
      | intros a Ha; apply Hwin; unfold zwin in *; lia
      | ].

      intros A' R2 M' model' AI' MS' Hfs Hfds KEPT LDEL EFF1 DEF' WIN'.
      assert (HP2 : pres PRES Rb R2).
      { eapply (pres_kept PRES Rb R1 R2 pres_cs); [|exact KEPT]. eapply pres_trans; [exact HP|]. intros r Hr. apply Ha1. exact Hr. }
      assert (G9' : getr R2 9%bv = Z_to_bv 64 (hdaddr rest)) by (rewrite (KEPT 9%bv) by inl; exact G9).
      assert (Hdef' : defined M' (sp - 32 - DEL_STACK) (32 + DEL_STACK)).
      { intros i Hi. destruct (Z.lt_ge_cases i DEL_STACK); [apply DEF'; lia|].
        apply (defined_via_eff L MI HLimg_lo HLrw_img HLerr_rw A A' M M' _ _ (sp - 32 - DEL_STACK) (32 + DEL_STACK) EFF1 ltac:(lia) ltac:(lia)
                 ltac:(intros j Hj; apply Hwin; unfold zwin; lia) ltac:(intros j Hj; cbn beta; lia) Hdef i Hi). }
      assert (Hwin' : forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A' a).
      { intros a Ha Ho. destruct (ef_own _ _ _ _ _ _ _ _ _ EFF1 a Ho) as [Ho0|[[_ [_ Hn]]|Hq]].
        - exact (Hwin a Ha Ho0).
        - exact (Hdef (a - (sp - 32 - DEL_STACK)) ltac:(unfold zwin in Ha; lia) ltac:(replace (sp - 32 - DEL_STACK + (a - (sp - 32 - DEL_STACK))) with a by lia; exact Hn)).
        - unfold zwin in Ha. lia. }

      pose (E2 := Eseed R2 [Z_to_bv 64 (hdaddr rest)]).
      assert (HR2 : regs_ok E2 (srs sr_id [(9%bv, EVar 32)]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK2 : know_ok SEGS E2 M' []) by constructor.
      destruct rest as [|[p' [k' v']] rest'].
      -
        cbn [hdaddr] in *.
        xruns HR2 HK2 100%nat STOPS (SCR [false] [] []) 50%N.
        { split_scs; try sc_auto1. }
        lazymatch goal with H : regs_ok E2 _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HR3; rename Rx into R3 end.
        apply (POST A' M' model' R3 AI' MS' Hfs Hfds).
        + eapply pres_trans; [exact HP2|]. intros r Hr. apply (syms_id_sound _ _ _ _ PRES HR3 eq_refl). exact Hr.
        + eapply eff_weaken; [exact EFF1|]. intros a Ha. exists p. split; [left; reflexivity | exact Ha].
        + cbn. exists (live MI A'). split; [exact LDEL | reflexivity].
        + exact Hdef'.
        + exact Hwin'.
      -
        xruns HR2 HK2 100%nat STOPS (SCR [true] [] []) 50%N.
        { split_scs; try sc_auto1. cbn [sc_denot]. evs. cbn [hdaddr].
          destruct (live_facts' A M model p' NS AI (Hlive p' k' v' (or_intror (or_introl eq_refl)))) as (_ & Hp0' & Hp1' & _).
          rewrite br_ne by lia. bool_lia. }
        cbn [hdaddr] in *.
        lazymatch goal with H : regs_ok E2 _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HR3; rename Rx into R3 end.
        assert (Hlive' : forall q kq vq, In (q, (kq, vq)) ((p', (k', v')) :: rest') -> In (q, NS) (live MI A')).
        { intros q kq vq Hin. apply (proj2 (LDEL q NS)). split; [apply (Hlive q kq vq); right; exact Hin|].
          intros ->. inversion Hnd as [| x l0 Hnotin Hnd']. apply Hnotin. apply base.list_elem_of_In. exact (in_map fst _ _ Hin). }
        assert (ROC' : img_ro_clear L M').
        { eapply (img_ro_clear_via_eff' A A' M M' model _ _ ROC AI EFF1); [| cbn; lia].
          intros a Ha. cbn beta in Ha. exact (live_offimg' A M model p NS a AI (Hlive p k v (or_introl eq_refl)) Ha). }
        eapply (IH fx A' M' model' R3 K ltac:(discriminate) HNS AI' MS' ROC').
        + eapply pres_trans; [exact HP2|]. intros r Hr. apply (syms_id_sound _ _ _ _ PRES HR3 eq_refl). exact Hr.
        + rreg HR3 10%bv G. exact G.
        + exact Hlive'.
        + inversion Hnd; assumption.
        +
          eapply (chain_agree SEGS V M M'); [exact Hchr|]. intros q kq vq Hin.
          destruct (live_facts' A M model q NS AI (Hlive q kq vq (or_intror Hin))) as (_ & Hq0 & Hqce & Hqown).
          assert (Hpq : p <> q).
          { intros <-. inversion Hnd as [| x l0 Hnotin Hnd']. apply Hnotin. apply base.list_elem_of_In. exact (in_map fst _ _ Hin). }
          pose proof (ai_live_disjoint MI A M model q NS p NS AI (Hlive q kq vq (or_intror Hin)) (Hlive p k v (or_introl eq_refl)) ltac:(congruence)) as Hapq.
          split; [|lia].
          intros i Hi. apply (ef_frame _ _ _ _ _ _ _ _ _ EFF1). rewrite u64_of_Z by lia.
          intros [Ho|[Ho'|[Hnm|[Hf|[Hw|He]]]]].
          * exact (proj1 (Hqown (q + i) ltac:(lia)) Ho).
          * destruct (ef_own _ _ _ _ _ _ _ _ _ EFF1 _ Ho') as [Ho0|[[_ [_ Hn]]|Hf]].
            -- exact (proj1 (Hqown (q + i) ltac:(lia)) Ho0).
            -- exact (proj2 (Hqown (q + i) ltac:(lia)) Hn).
            -- unfold apart in Hapq. lia.
          * destruct Hnm as (_ & _ & Hn). exact (proj2 (Hqown (q + i) ltac:(lia)) Hn).
          * unfold apart in Hapq. lia.
          * unfold W_of in Hw. cbn in Hw. lia.
          * exact (live_offimg' A M model q NS (q + i) AI (Hlive q kq vq (or_intror Hin)) ltac:(lia) (HLrw_img _ (HLerr_rw _ He))).
        + exact Hdef'.
        + exact Hwin'.
        +
          intros A'' M'' model'' R'' AI'' MS'' Hfs' Hfds' HP'' EFF2 LAP2 Hdef'' Hwin''.
          apply (POST A'' M'' model'' R'' AI'' MS''); [congruence | congruence | exact HP'' | | | exact Hdef'' | exact Hwin''].
          * eapply eff_weaken; [eapply eff_trans; [exact EFF1 | exact EFF2 |]|].
            -- intros a Ha. apply Hwin''. unfold W_of in Ha. cbn in Ha. unfold zwin. lia.
            -- intros a [Ha|(q & Hq & Hqa)]; [exists p; split; [left; reflexivity| exact Ha]|].
               exists q. split; [right; exact Hq | exact Hqa].
          * cbn. exists (live MI A'). split; [exact LDEL | exact LAP2].
    Qed.
  End Loops.

  Section Main.
    Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
    Variables (sp ret st : Z) (c : stateC) (K : TSet).
    Hypothesis CB : callB MI ST A0 s R0 M0 model0 sp ret (STATE_DTOR_STACK DEL_STACK).
    Hypothesis H10 : getr R0 10%bv = Z_to_bv 64 st.
    Hypothesis SR : state_rep MI A0 M0 st c.
    Hypothesis ASP : above_sp MI A0 sp st 240.
    Hypothesis CONT : forall A' R' M' model',
        retB MI ST A' s R0 R' M' model0 model' ->
        lapply (live MI A0) (map (fun b => LDel (fst b)) (state_blocks c)) (live MI A') ->
        eff MI A0 A' M0 M' (sp - STATE_DTOR_STACK DEL_STACK, sp) (state_foot st c) ->
        defined M' st 240 ->
        srealizes SEGS (cfg fx R' ret M' model') K.

    Definition P1 : list (Z * Z) := umap_blocks 24 (t3a (st_m1 c)) (t3b (st_m1 c)) (t3c (st_m1 c)).
    Definition P2 : list (Z * Z) := umap_blocks 32 (t3a (st_m2 c)) (t3b (st_m2 c)) (t3c (st_m2 c)).
    Definition P3 : list (Z * Z) := umap_blocks 24 (t3a (st_m3 c)) (t3b (st_m3 c)) (t3c (st_m3 c)).
    Definition P4 : list (Z * Z) := vec_blocks (st_v1 c).
    Definition P5 : list (Z * Z) := vec_blocks (st_v2 c).
    Definition P6 : list (Z * Z) := vec_blocks (st_v3 c).
    Lemma SB : state_blocks c = P1 ++ P2 ++ P3 ++ P4 ++ P5 ++ P6.
    Proof using c. reflexivity. Qed.

    Definition W : Z * Z := (sp - (32 + DEL_STACK), sp).
    Definition inblk (bs : list (Z * Z)) (a : Z) : Prop := exists b, In b bs /\ fst b <= a < fst b + snd b.

    Definition FK (off : Z) (bs : list (Z * Z)) (a : Z) : Prop := (st + off <= a < st + 240) \/ inblk bs a.

    Definition base_ok (R : bvmap 5 word) : Prop :=
      getr R 2%bv = Z_to_bv 64 (sp - 32) /\ getr R 3%bv = Z_to_bv 64 (ly_gp L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp L)
      /\ getr R 8%bv = Z_to_bv 64 st
      /\ forall r, In r [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R r = getr R0 r.

    Definition frame (M : mem) : Prop :=
      cell8 SEGS M (sp - 8) ret /\ cell8 SEGS M (sp - 16) (bv_unsigned (getr R0 8%bv)) /\ cell8 SEGS M (sp - 24) (bv_unsigned (getr R0 9%bv)).

    Record dst (off : Z) (bs : list (Z * Z)) (A : AS MI) (M : mem) (model : Model) (R : bvmap 5 word) : Prop := DST {
      d_ai : ainv MI A M model;
      d_ms : mstd model;
      d_fs : m_fs model = m_fs model0;
      d_fds : m_fds model = m_fds model0;
      d_regs : base_ok R;
      d_frame : frame M;
      d_def : defined M (sp - 32 - DEL_STACK) (32 + DEL_STACK);
      d_win : forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A a;
      d_eff : eff MI A0 A M0 M W (FK off bs);
      d_lap : lapply (live MI A0) (map (fun b => LDel (fst b)) bs) (live MI A);
      d_sub : forall b, In b bs -> In b (state_blocks c);
      d_odef : defined M st 240
    }.

    Let AI0 := cb_ainv _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let MS0 := cb_mstd _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let CR0 := cb_regs _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let ROC0 := cb_roc _ _ _ _ _ _ _ _ _ _ _ _ CB.

    Lemma sp_facts : sp mod 16 = 0 /\ alloc_ceiling + (32 + DEL_STACK) <= sp /\ sp < 2 ^ 47 /\ 0x122000 <= sp - (32 + DEL_STACK).
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret CB.
      destruct CR0. pose proof (cb_ceil _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hc. unfold STATE_DTOR_STACK in Hc.
      pose proof ac_bounds_lit. repeat split; try assumption; lia.
    Qed.
    Let SPF := sp_facts.

    Lemma umap_blocks_live : forall NS V nval obj bl bc (ents : list (Z * (Z * V))) b,
      umapx MI NS nval A0 M0 obj bl bc ents -> In b (umap_blocks NS bl bc ents) -> In b (live MI A0).
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret CB.
      intros NS V nval obj bl bc ents [p n] U Hb. unfold umap_blocks in Hb. apply in_app_iff in Hb.
      destruct Hb as [Hb | Hb].
      - destruct (Z.eqb_spec bc 0); [destruct Hb|]. destruct Hb as [Hb|[]]. injection Hb as <- <-.
        destruct (u_blive U) as [[? ?]|[_ Hin]]; [lia | exact Hin].
      - apply in_map_iff in Hb. destruct Hb as ([p' [k v]] & Hpp & Hin). cbn in Hpp. injection Hpp as <- <-.
        exact (proj1 (u_node U p' k v Hin)).
    Qed.

    Lemma vec_blocks_live : forall v vv, vraw MI A0 M0 v (t3a vv) (t3b vv) (t3c vv) ->
      forall b, In b (vec_blocks vv) -> In b (live MI A0).
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret CB.
      intros v vv VR b Hb. unfold vec_blocks in Hb. destruct (Z.eqb_spec (t3a vv) 0) as [Hz|Hnz]; [destruct Hb|].
      destruct Hb as [<-|[]]. destruct (vr_blk _ _ _ _ _ _ _ _ _ VR) as [(Hb0 & _)|(_ & Hin & _)]; [lia | exact Hin].
    Qed.

    Lemma blocks_live : forall b, In b (state_blocks c) -> In b (live MI A0).
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret st c CB SR.
      intros b Hb. rewrite SB in Hb. unfold P1, P2, P3, P4, P5, P6 in Hb.
      apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [exact (umap_blocks_live _ _ _ _ _ _ _ _ (sr_m1 _ _ _ _ _ _ _ SR) Hb)|].
      apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [exact (umap_blocks_live _ _ _ _ _ _ _ _ (sr_m2 _ _ _ _ _ _ _ SR) Hb)|].
      apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [exact (umap_blocks_live _ _ _ _ _ _ _ _ (sr_m3 _ _ _ _ _ _ _ SR) Hb)|].
      apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [exact (vec_blocks_live _ _ (sr_v1 _ _ _ _ _ _ _ SR) b Hb)|].
      apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [exact (vec_blocks_live _ _ (sr_v2 _ _ _ _ _ _ _ SR) b Hb)|].
      exact (vec_blocks_live _ _ (sr_v3 _ _ _ _ _ _ _ SR) b Hb).
    Qed.

    Lemma nodup_app_ne : forall (l1 l2 : list (Z * Z)) b b',
      NoDup (map fst (l1 ++ l2)) -> In b l1 -> In b' l2 -> fst b <> fst b'.
    Proof using.
      intros l1 l2 b b' Hnd H1 H2 Heq.
      revert Hnd H1. induction l1 as [|x l1 IH]; intros Hnd H1; [destruct H1|].
      cbn in Hnd. inversion Hnd as [|y l Hni Hnd']. subst.
      destruct H1 as [<-|H1].
      - apply Hni. apply base.list_elem_of_In. rewrite Heq, map_app. apply in_app_iff. right. apply in_map. exact H2.
      - exact (IH Hnd' H1).
    Qed.

    Lemma blocks_apart : forall b b', In b (state_blocks c) -> In b' (state_blocks c) -> fst b <> fst b' ->
      apart (fst b) (snd b) (fst b') (snd b').
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret st c CB SR.
      intros [p n] [q m] Hb Hb' Hne. cbn in *.
      exact (ai_live_disjoint MI A0 M0 model0 p n q m AI0 (blocks_live _ Hb) (blocks_live _ Hb') Hne).
    Qed.

    Ltac zpc z := lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
                    replace pc with (Z_to_bv 64 z : word) by (apply bv_eq; vm_compute; reflexivity) end.

    Lemma blkP :
      (forall M1 R1, dst 240 [] A0 M1 model0 R1 -> getr R1 10%bv = Z_to_bv 64 st ->
                    srealizes SEGS (cfg fx R1 V3_PC M1 model0) K) ->
      srealizes SEGS (cfg fx R0 SDT M0 model0) K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn fx A0 s R0 M0 model0 sp ret st c K CB H10 SR ASP.
      intros POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct CR0 as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      destruct ASP as (Hstsp & Hsthi & Hstown).
      pose proof (cb_room _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hroom. unfold STATE_DTOR_STACK in Hroom.
      pose proof (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hwin0. unfold STATE_DTOR_STACK in Hwin0.
      pose proof (defined_of_stack_room M0 sp (32 + DEL_STACK) ltac:(lia) ltac:(lia) ltac:(lia) Hroom) as Hdef0.
      pose (E := Eseed R0 [Z_to_bv 64 st; Z_to_bv 64 sp; getr R0 1%bv; getr R0 8%bv; getr R0 9%bv]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (1%bv, EVar 34); (8%bv, EVar 35); (9%bv, EVar 36)]) R0).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; first [assumption | reflexivity]. }
      assert (HK : know_ok SEGS E M0 [KWr (SA (EVar 33) (-32)) (ELit 32)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        eapply (kwr_stack_sub _ _ _ _ sp (32 + DEL_STACK)); [evs; reflexivity | reflexivity | lia | lia | lia | exact Hroom]. }
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1. }
      rreg HR' 2%bv G2. rreg HR' 3%bv G3. rreg HR' 4%bv G4. rreg HR' 8%bv G8. rreg HR' 10%bv G10.
      pose proof (syms_id_sound _ _ _ _ [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl) as Gs.
      postrun.
      rewrite <- (Z_to_bv_bv_unsigned 64 (getr R0 9)), <- (Z_to_bv_bv_unsigned 64 (getr R0 8)). rewrite Hra.
      set (M1 := wbytes (wbytes (wbytes M0 _ _) _ _) _ _).
      assert (HM1w : forall x : word, (bv_unsigned x < sp - 32 \/ sp <= bv_unsigned x) -> M1 x = M0 x).
      { intros x Hx. unfold M1.
        rewrite !wbytes_outside; [reflexivity| ..];
          rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
      assert (HM1g : forall x : word, M0 x <> None -> M1 x <> None).
      { intros x Hx. unfold M1. repeat apply wbytes_grows. exact Hx. }
      pose proof (u64_range (getr R0 9)) as Hr9. pose proof (u64_range (getr R0 8)) as Hr8.
      apply (POST M1 R'); [|exact G10].
      constructor.
      - eapply (ai_frame MI); [exact AI0 | | exact HM1g | reflexivity | reflexivity].
        intros x Ho. apply HM1w. pose proof (u64_range x).
        destruct (Z.lt_ge_cases (bv_unsigned x) (sp - 32)); [left; assumption|].
        destruct (Z.le_gt_cases sp (bv_unsigned x)); [right; assumption|].
        exfalso. exact (proj1 (Hwin0 (bv_unsigned x) ltac:(unfold zwin; lia)) Ho).
      - exact MS0. - reflexivity. - reflexivity.
      - unfold base_ok. rewrite G2, G3, G4, G8. rewrite w_addm by lia. replace (sp + -32) with (sp - 32) by lia.
        repeat split; try reflexivity; try assumption.
      - unfold frame, M1, cell8. split; [|split].
        + do 2 (apply cellw_wb_other; [| lia | rewrite length_N_to_le_bytes; change (Z.of_nat 8) with 8; lia | lia | cbn; lia | rewrite length_N_to_le_bytes; unfold apart; cbn; lia]).
          replace (sp - 8) with (sp + -8) by lia. apply cellw_store; [cbn; lia | lia | cbn; lia | cbn; lia].
        + do 1 (apply cellw_wb_other; [| lia | rewrite length_N_to_le_bytes; change (Z.of_nat 8) with 8; lia | lia | cbn; lia | rewrite length_N_to_le_bytes; unfold apart; cbn; lia]).
          replace (sp - 16) with (sp + -16) by lia. apply cellw_store; [cbn; lia | lia | cbn; lia | cbn; lia].
        + replace (sp - 24) with (sp + -24) by lia. apply cellw_store; [cbn; lia | lia | cbn; lia | cbn; lia].
      - unfold M1. repeat apply defined_wbytes. intros i Hi. replace (sp - 32 - DEL_STACK + i) with (sp - (32 + DEL_STACK) + i) by lia. apply Hdef0. lia.
      - intros a Ha. apply (proj1 (Hwin0 a ltac:(unfold zwin in *; lia))).
      - apply eff_store; [|exact HM1g]. intros x HF HW. apply HM1w. unfold W, W_of in HW. cbn in HW.
        pose proof (u64_range x). lia.
      - reflexivity.
      - intros b [].
      - unfold M1. repeat apply defined_wbytes. intros i Hi. apply (sr_def _ _ _ _ _ _ _ SR). lia.
    Qed.

    Lemma eff_widen : forall (A A' : AS MI) M M' (W W' : Z * Z) F,
      eff MI A A' M M' W F -> (forall a, W_of W a -> W_of W' a) -> eff MI A A' M M' W' F.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret CB.
      intros A A' M M' W0 W' F E HW. destruct E as [C B O FR D OI]. constructor; try assumption.
      intros a Hn. apply FR. intros [H|[H|[H|[H|[H|H]]]]]; apply Hn; try tauto. right; right; right; right; left. apply HW, H.
    Qed.

    Lemma base_kept : forall R R', base_ok R -> kept R R' -> base_ok R'.
    Proof using L R0 sp st.
      intros R R' (B2 & B3 & B4 & B8 & Bs) HK. unfold base_ok.
      rewrite !(HK _) by inl. repeat split; try assumption.
      intros r Hr. rewrite (HK r); [apply Bs, Hr|]. cbn in Hr. unfold callee_saved. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
    Qed.

    Lemma blk_range : forall b, In b (state_blocks c) -> 0 <= snd b /\ 0 < fst b /\ fst b + snd b <= alloc_ceiling.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret st c CB SR.
      intros [p n] Hb. destruct (live_facts' A0 M0 model0 p n AI0 (blocks_live _ Hb)) as (Hn & Hp & Hpn & _). cbn. lia.
    Qed.

    Lemma FK_not_low : forall off bs a, (forall b, In b bs -> In b (state_blocks c)) ->
      FK off bs a -> a < st + off -> alloc_ceiling <= a -> False.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret st c CB SR.
      intros off bs a SUB [Ho | (b & Hb & Hba)] Hlt Hce; [lia|].
      destruct (blk_range b (SUB b Hb)) as (_ & _ & Hbc). lia.
    Qed.

    Lemma foot_offimg : forall a, (st <= a < st + 240) \/ inblk (state_blocks c) a -> ~ in_ranges (ly_img L) a.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLimg_lo A0 s R0 M0 model0 sp ret st c CB SR ASP.
      intros a Ha Himg. pose proof (HLimg_lo a Himg) as Hlt. destruct SPF as (_ & Hsplo & _). destruct ASP as (Hstsp & _).
      destruct Ha as [Ho | ([p n] & Hb & Hba)]; [lia|]. cbn in Hba.
      exact (live_offimg' A0 M0 model0 p n a AI0 (blocks_live _ Hb) Hba Himg).
    Qed.

    Lemma roc_of_eff : forall A M (F : Z -> Prop) bs,
      eff MI A0 A M0 M W F -> (forall b, In b bs -> In b (state_blocks c)) ->
      (forall a, F a -> (st <= a < st + 240) \/ inblk bs a) -> img_ro_clear L M.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLimg_lo HLerr_rw A0 s R0 M0 model0 sp ret st c CB SR ASP.
      intros A M F bs EF SUB HF. destruct SPF as (_ & Hsplo & _).
      eapply (img_ro_clear_via_eff' A0 A M0 M model0 W F ROC0 AI0 EF); [| unfold W; cbn; lia].
      intros a Ha. apply foot_offimg. destruct (HF a Ha) as [Ho | (b & Hb & Hba)]; [left; exact Ho | right].
      exists b. split; [exact (SUB b Hb) | exact Hba].
    Qed.

    Lemma d_roc : forall off bs A M model R, dst off bs A M model R -> 0 <= off -> img_ro_clear L M.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLimg_lo HLerr_rw A0 s R0 M0 model0 sp ret st c CB SR ASP.
      intros off bs A M model R D Hoff. eapply (roc_of_eff A M (FK off bs) bs (d_eff _ _ _ _ _ _ D) (d_sub _ _ _ _ _ _ D)).
      intros a [Ho | Hb]; [left; lia | right; exact Hb].
    Qed.

    Lemma d_unowned : forall off bs A M model R, dst off bs A M model R ->
      forall i, 0 <= i < off -> off <= 240 -> ~ owned MI A (st + i).
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret st c CB SR ASP.
      intros off bs A M model R D i Hi Hoff Ho.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). destruct ASP as (Hstsp & Hsthi & Hstown).
      destruct (ef_own _ _ _ _ _ _ _ _ _ (d_eff _ _ _ _ _ _ D) _ Ho) as [Ho0 | [[_ [_ Hn]] | Hf]].
      - exact (Hstown i ltac:(lia) Ho0).
      - exact (sr_def _ _ _ _ _ _ _ SR i ltac:(lia) Hn).
      - exact (FK_not_low off bs (st + i) (d_sub _ _ _ _ _ _ D) Hf ltac:(lia) ltac:(lia)).
    Qed.

    Lemma d_agree : forall off bs A M model R, dst off bs A M model R -> off <= 240 -> agree_on M0 M st off.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLimg_lo HLrw_img HLerr_rw A0 s R0 M0 model0 sp ret st c CB SR ASP.
      intros off bs A M model R D Hoff.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). destruct ASP as (Hstsp & Hsthi & Hstown). pose proof ceiling_lt as Hcl.
      destruct (Z.lt_ge_cases off 0) as [Hneg|Hnn]; [intros i Hi; lia|].
      eapply (agree_above_via_eff' A0 A M0 M W (FK off bs) st off sp (d_eff _ _ _ _ _ _ D));
        [lia | unfold W; cbn; lia | lia | lia | lia | | |].
      - intros i Hi. apply Hstown. lia.
      - intros i Hi. apply (sr_def _ _ _ _ _ _ _ SR). lia.
      - intros i Hi Hf. exact (FK_not_low off bs (st + i) (d_sub _ _ _ _ _ _ D) Hf ltac:(lia) ltac:(lia)).
    Qed.

    Lemma d_cell : forall off bs A M model R a (w : N) v, dst off bs A M model R ->
      cellw SEGS M0 (st + a) w v -> 0 <= a -> a + Z.of_N w <= off -> off <= 240 -> cellw SEGS M (st + a) w v.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLimg_lo HLrw_img HLerr_rw A0 s R0 M0 model0 sp ret st c CB SR ASP.
      intros off bs A M model R a w v D Hc Ha Haw Hoff. destruct ASP as (Hstsp & Hsthi & Hstown). destruct SPF as (_ & Hsplo & _).
      pose proof ac_bounds_lit.
      eapply cellw_agree; [exact Hc | | lia | lia].
      eapply agree_on_sub; [exact (d_agree off bs A M model R D Hoff) | lia | lia].
    Qed.

    Lemma d_defined : forall off bs A M model R a n, dst off bs A M model R ->
      0 <= a -> a + n <= off -> off <= 240 -> defined M (st + a) n.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLimg_lo HLrw_img HLerr_rw A0 s R0 M0 model0 sp ret st c CB SR ASP.
      intros off bs A M model R a n D Ha Han Hoff.
      eapply defined_agree; [| eapply agree_on_sub; [exact (d_agree off bs A M model R D Hoff) | lia | lia]].
      intros i Hi. replace (st + a + i) with (st + (a + i)) by lia. apply (sr_def _ _ _ _ _ _ _ SR). lia.
    Qed.

    Lemma d_live : forall off bs A M model R b, dst off bs A M model R ->
      In b (state_blocks c) -> ~ In (fst b) (map fst bs) -> In b (live MI A).
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret st c CB SR.
      intros off bs A M model R [p n] D Hb Hni. exact (lapply_dels_keep' bs _ _ p n (d_lap _ _ _ _ _ _ D) (blocks_live _ Hb) Hni).
    Qed.

    Lemma del_post : forall (F1 : Z -> Prop) bs A Mw model A' M' (p n : Z),
      ainv MI A Mw model -> frame Mw -> defined Mw (sp - 32 - DEL_STACK) (32 + DEL_STACK) ->
      (forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A a) ->
      eff MI A0 A M0 Mw W F1 -> lapply (live MI A0) (map (fun b => LDel (fst b)) bs) (live MI A) ->
      In (p, n) (state_blocks c) ->
      live_del p (live MI A) (live MI A') ->
      eff MI A A' Mw M' (sp - 32 - DEL_STACK, sp - 32) (fun a => p <= a < p + n) ->
      defined M' (sp - 32 - DEL_STACK) DEL_STACK ->
      (forall a, zwin (sp - 32 - DEL_STACK) (sp - 32) a -> ~ owned MI A' a) ->
      frame M' /\ defined M' (sp - 32 - DEL_STACK) (32 + DEL_STACK) /\ (forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A' a)
      /\ eff MI A0 A' M0 M' W (fun a => F1 a \/ inblk [(p, n)] a)
      /\ lapply (live MI A0) (map (fun b => LDel (fst b)) (bs ++ [(p, n)])) (live MI A').
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLimg_lo HLrw_img HLerr_rw A0 s R0 M0 model0 sp ret st c CB SR.
      intros F1 bs A Mw model A' M' p n AI FR DEF WIN EFF LAP Hb LDEL EFF1 DEF' WIN'.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct CR0 as [_ _ Hretr _ _ _ _ _].
      destruct (blk_range _ Hb) as (Hn0 & Hp0 & Hpc). cbn in Hn0, Hp0, Hpc.
      pose proof (u64_range (getr R0 8%bv)) as Hr8. pose proof (u64_range (getr R0 9%bv)) as Hr9.
      assert (AG : forall a k, sp - 32 <= a -> 0 <= k -> a + k <= sp -> agree_on Mw M' a k).
      { intros a k Ha Hk Hak.
        eapply (agree_above_via_eff' A A' Mw M' _ _ a k (sp - 32) EFF1); [lia | cbn; lia | lia | lia | lia | | |].
        - intros i Hi. apply WIN. unfold zwin. lia.
        - intros i Hi. replace (a + i) with (sp - 32 - DEL_STACK + (a + i - (sp - 32 - DEL_STACK))) by lia. apply DEF. lia.
        - intros i Hi Hf. cbn beta in Hf. lia. }
      assert (WINf : forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A' a).
      { intros a Ha Ho. destruct (ef_own _ _ _ _ _ _ _ _ _ EFF1 a Ho) as [Ho0|[[_ [_ Hm]]|Hq]].
        - exact (WIN a Ha Ho0).
        - exact (DEF (a - (sp - 32 - DEL_STACK)) ltac:(unfold zwin in Ha; lia) ltac:(replace (sp - 32 - DEL_STACK + (a - (sp - 32 - DEL_STACK))) with a by lia; exact Hm)).
        - cbn beta in Hq. unfold zwin in Ha. lia. }
      split; [|split; [|split; [exact WINf|split]]].
      - destruct FR as (F1' & F2' & F3'). unfold frame.
        split; [|split]; (eapply cellw_agree; [eassumption | apply AG; cbn; lia | lia | cbn; lia]).
      - intros i Hi. destruct (Z.lt_ge_cases i DEL_STACK); [apply DEF'; lia|].
        apply (defined_via_eff L MI HLimg_lo HLrw_img HLerr_rw A A' Mw M' _ _ (sp - 32 - DEL_STACK) (32 + DEL_STACK) EFF1 ltac:(lia) ltac:(lia)
                 ltac:(intros j Hj; apply WIN; unfold zwin; lia) ltac:(intros j Hj; cbn beta; lia) DEF i Hi).
      - eapply eff_weaken; [eapply eff_trans; [exact EFF | eapply eff_widen; [exact EFF1|] |]|].
        + intros a Ha. unfold W, W_of in *. cbn in *. lia.
        + intros a Ha. apply WINf. unfold W, W_of in Ha. cbn in Ha. unfold zwin. lia.
        + intros a [Ha|Ha]; [left; exact Ha | right]. exists (p, n). split; [left; reflexivity | exact Ha].
      - rewrite map_app. eapply lapply_app; [exact LAP|]. cbn. exists (live MI A'). split; [exact LDEL | reflexivity].
    Qed.

    Lemma vec_blocks_nz : forall vv, t3a vv <> 0 -> vec_blocks vv = [(t3a vv, t3c vv - t3a vv)].
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret CB. intros vv H. unfold vec_blocks. destruct (Z.eqb_spec (t3a vv) 0); [lia | reflexivity]. Qed.
    Lemma vec_blocks_z : forall vv, t3a vv = 0 -> vec_blocks vv = [].
    Proof using. intros vv H. unfold vec_blocks. rewrite H. reflexivity. Qed.

    Lemma hi_unowned' : forall A M model a, ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a.
    Proof using AC L MI HLimg_lo HLrw_img sp.
      intros A M model a AI Ha Ho.
      destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw|Hoff].
      - pose proof (HLimg_lo _ (HLrw_img _ Hrw)). lia.
      - pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hoff). lia.
    Qed.
    Lemma odef_eff : forall A A' M M' model Wx (F : Z -> Prop),
      ainv MI A M model -> eff MI A A' M M' Wx F -> (forall a, F a -> a < alloc_ceiling) ->
      defined M st 240 -> defined M' st 240.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLimg_lo HLrw_img HLerr_rw A0 s R0 M0 model0 sp ret st CB ASP.
      intros A A' M M' model Wx F AI EF HF HD i Hi.
      destruct ASP as (Hstsp & Hsthi & Hstown). destruct SPF as (_ & Hsplo & Hsphi' & _). pose proof ac_bounds_lit. pose proof ceiling_lt.
      destruct (ef_def _ _ _ _ _ _ _ _ _ EF (st + i) ltac:(lia) (HD i Hi)) as [Hm|[Ho|[Hf|He]]]; [exact Hm | exfalso | exfalso | exfalso].
      - exact (hi_unowned' A M model (st + i) AI ltac:(lia) Ho).
      - pose proof (HF _ Hf). lia.
      - pose proof (HLimg_lo _ (HLrw_img _ (HLerr_rw _ He))). lia.
    Qed.

    Lemma odef_nodes : forall A A' M M' model Wx (NS : Z) {V : Type} (l : list (Z * (Z * V))),
      ainv MI A M model -> eff MI A A' M M' Wx (nodes_foot NS l) -> (forall p k v, In (p, (k, v)) l -> In (p, NS) (state_blocks c)) ->
      defined M st 240 -> defined M' st 240.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLimg_lo HLrw_img HLerr_rw A0 s R0 M0 model0 sp ret st c CB SR ASP.
      intros A A' M M' model Wx NS V l AI EF Hl HD. eapply odef_eff; [exact AI | exact EF | | exact HD].
      intros a (p & Hp & Hpa). apply in_map_iff in Hp. destruct Hp as ([p' kv] & Hpp & Hin). cbn in Hpp. subst p'. destruct kv as [k v].
      destruct (blk_range (p, NS) (Hl p k v Hin)) as (_ & _ & Hbc). cbn in Hbc. lia.
    Qed.

    Lemma blkV3 : forall A M model R,
      dst 240 [] A M model R -> getr R 10%bv = Z_to_bv 64 st ->
      (forall A' M' model' R', dst 216 P6 A' M' model' R' -> srealizes SEGS (cfg fx R' V2_PC M' model') K) ->
      srealizes SEGS (cfg fx R V3_PC M model) K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw fx A0 s R0 M0 model0 sp ret st c K CB SR ASP.
      intros A M model R D G10 POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hstsp & Hsthi & Hstown).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds B FR DEF WIN EFF LAP SUB ODEF]. destruct B as (B2 & B3 & B4 & B8 & Bs).
      pose proof (sr_v3 _ _ _ _ _ _ _ SR) as VR. destruct VR as [Cb0 Ce0 Cc0 Hblk].
      set (vb := t3a (st_v3 c)) in *. set (ve := t3b (st_v3 c)) in *. set (vc := t3c (st_v3 c)) in *.
      pose proof (d_cell _ _ _ _ _ _ 216 8 vb D Cb0 ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cb.
      pose proof (d_cell _ _ _ _ _ _ 232 8 vc D ltac:(replace (st + 232) with (st + 216 + 16) by lia; exact Cc0) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cc.
      unfold cell8 in *. pose proof (proj1 Cb) as Hvbr. pose proof (proj1 Cc) as Hvcr.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 (sp - 32); Z_to_bv 64 st; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 vb; Z_to_bv 64 vc]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (8%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.
      destruct (Z.eq_dec vb 0) as [Hz | Hnz].
      -
        xruns HR HK 100%nat STOPS (SCR [true] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. }
        apply (POST A). constructor; try assumption.
        + rreg HR' 2%bv Q2. rreg HR' 8%bv Q8. pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl) as Qs.
          unfold base_ok. rewrite Q2, Q8, !Qs by inl. repeat split; try assumption.
          intros r Hr. rewrite Qs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
        + eapply eff_weaken; [exact EFF|]. intros a [Ha|(b & [] & _)]. left. lia.
        + unfold P6. rewrite (vec_blocks_z _ Hz). exact LAP.
        + unfold P6. rewrite (vec_blocks_z _ Hz). intros b [].
      -
        assert (Hdef224 : defined M (st + 224) (Z.of_nat 8)) by (eapply (d_defined _ _ _ _ _ _ 224 _ D); cbn; lia).
        xruns HR HK 100%nat STOPS (SCR [false] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_so. exact Hdef224. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        set (Mw := wbytes M _ _).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 10%bv Gc10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
        assert (HMw : forall x : word, ~ (st + 224 <= bv_unsigned x < st + 232) -> Mw x = M x).
        { intros x Hx. pose proof (u64_range x). unfold Mw.
          rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMg : forall x : word, M x <> None -> Mw x <> None) by (intros x Hx; unfold Mw; apply wbytes_grows; exact Hx).
        assert (AIw : ainv MI A Mw model).
        { eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
          intros x Ho. apply HMw. intros Hx.
          exact (d_unowned _ _ _ _ _ _ D (bv_unsigned x - st) ltac:(lia) ltac:(lia) ltac:(replace (st + (bv_unsigned x - st)) with (bv_unsigned x) by lia; exact Ho)). }
        assert (FRw : frame Mw).
        { destruct FR as (F1 & F2 & F3). unfold frame, cell8, Mw. split; [|split]; cellpeel. }
        assert (DEFw : defined Mw (sp - 32 - DEL_STACK) (32 + DEL_STACK)) by (unfold Mw; apply defined_wbytes; exact DEF).
        assert (EFFw : eff MI A0 A M0 Mw W (fun a => FK 240 [] a \/ (st + 224 <= a < st + 232))).
        { eapply eff_weaken; [eapply eff_trans; [exact EFF | |]|].
          - eapply eff_store with (F := fun a : Z => st + 224 <= a < st + 232); [|exact HMg]. intros x HF HW. apply HMw. intros Hx. apply HF. exact Hx.
          - intros a Ha. apply WIN. unfold W, W_of in Ha. cbn in Ha. unfold zwin. lia.
          - intros a Ha. exact Ha. }
        assert (Hin6 : In (vb, vc - vb) (state_blocks c)).
        { rewrite SB. unfold P6. rewrite (vec_blocks_nz _ Hnz). rewrite !in_app_iff. do 5 right. left. reflexivity. }
        assert (ROCw : img_ro_clear L Mw).
        { eapply (roc_of_eff A Mw _ _ EFFw SUB). intros a [[Ho|Hb]|Hr]; [left; lia | right; exact Hb | left; lia]. }
        eapply (del_call fx A Mw model Rc vb (vc - vb) (sp - 32) V2_PC K AIw MS ROCw G1);
          [ apply bv_eq; vm_compute; reflexivity | unfold V2_PC; lia | exact G2
          | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16 | lia
          | rewrite Gs by inl; exact B3 | rewrite Gs by inl; exact B4 | exact Gc10
          | right; exact (d_live _ _ _ _ _ _ (vb, vc - vb) D Hin6 ltac:(intros X; exact X))
          | lia | lia
          | intros i Hi; apply DEFw; lia
          | intros a Ha; apply WIN; unfold zwin in *; lia | ].
        intros A' R' M' model' AI' MS' Hfs' Hfds' KEPT LDEL EFF1 DEF' WIN'.
        destruct (del_post _ [] A Mw model A' M' vb (vc - vb) AIw FRw DEFw WIN EFFw LAP Hin6 LDEL EFF1 DEF' WIN')
          as (FR' & DEF2 & WIN2 & EFF2 & LAP2).
        apply (POST A'). constructor.
        + exact AI'. + exact MS'. + congruence. + congruence.
        + eapply base_kept; [|exact KEPT]. unfold base_ok. rewrite G2, G8, !Gs by inl. repeat split; try assumption.
          intros r Hr. rewrite Gs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
        + exact FR'. + exact DEF2. + exact WIN2.
        + eapply eff_weaken; [exact EFF2|]. unfold P6. rewrite (vec_blocks_nz _ Hnz).
          intros a [[Hf|Ho]|Hb]; [left | left; lia | right; exact Hb]. destruct Hf as [Hf|(b & [] & _)]. lia.
        + unfold P6. rewrite (vec_blocks_nz _ Hnz). exact LAP2.
        + unfold P6. rewrite (vec_blocks_nz _ Hnz). intros b [<-|[]]. exact Hin6.
        + eapply (odef_eff A A' Mw M' model); [exact AIw | exact EFF1 | intros a Ha; cbn beta in Ha; destruct (blk_range _ Hin6) as (_ & _ & Hbc); cbn in Hbc; lia | unfold Mw; apply defined_wbytes; exact ODEF].
    Qed.

    Lemma SB2 : state_blocks c = (P1 ++ P2) ++ (P3 ++ P4 ++ P5 ++ P6).
    Proof using c. rewrite SB, <- !app_assoc. reflexivity. Qed.
    Lemma SB3 : state_blocks c = (P1 ++ P2 ++ P3) ++ (P4 ++ P5 ++ P6).
    Proof using c. rewrite SB, <- !app_assoc. reflexivity. Qed.
    Lemma SB4 : state_blocks c = (P1 ++ P2 ++ P3 ++ P4) ++ (P5 ++ P6).
    Proof using c. rewrite SB, <- !app_assoc. reflexivity. Qed.
    Lemma SB5 : state_blocks c = (P1 ++ P2 ++ P3 ++ P4 ++ P5) ++ P6.
    Proof using c. rewrite SB, <- !app_assoc. reflexivity. Qed.
    Lemma ne_split : forall l1 l2 b b', state_blocks c = l1 ++ l2 -> In b l1 -> In b' l2 -> fst b <> fst b'.
    Proof using AC L MI A0 M0 st c SR. intros l1 l2 b b' Heq H1 H2. eapply (nodup_app_ne l1 l2); [| exact H1 | exact H2]. rewrite <- Heq. exact (sr_nodup _ _ _ _ _ _ _ SR). Qed.

    Lemma blkV2 : forall A M model R,
      dst 216 P6 A M model R ->
      (forall A' M' model' R', dst 192 (P6 ++ P5) A' M' model' R' -> srealizes SEGS (cfg fx R' V1_PC M' model') K) ->
      srealizes SEGS (cfg fx R V2_PC M model) K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw fx A0 s R0 M0 model0 sp ret st c K CB SR ASP.
      intros A M model R D POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hstsp & Hsthi & Hstown).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds B FR DEF WIN EFF LAP SUB ODEF]. destruct B as (B2 & B3 & B4 & B8 & Bs).
      pose proof (sr_v2 _ _ _ _ _ _ _ SR) as VR. destruct VR as [Cb0 Ce0 Cc0 Hblk].
      set (vb := t3a (st_v2 c)) in *. set (ve := t3b (st_v2 c)) in *. set (vc := t3c (st_v2 c)) in *.
      pose proof (d_cell _ _ _ _ _ _ 192 8 vb D Cb0 ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cb.
      pose proof (d_cell _ _ _ _ _ _ 208 8 vc D ltac:(replace (st + 208) with (st + 192 + 16) by lia; exact Cc0) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cc.
      unfold cell8 in *. pose proof (proj1 Cb) as Hvbr. pose proof (proj1 Cc) as Hvcr.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 (sp - 32); Z_to_bv 64 st; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 vb; Z_to_bv 64 vc]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (8%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.
      destruct (Z.eq_dec vb 0) as [Hz | Hnz].
      -
        xruns HR HK 100%nat STOPS (SCR [true] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. }
        apply (POST A). constructor; try assumption.
        + rreg HR' 2%bv Q2. rreg HR' 8%bv Q8. pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl) as Qs.
          unfold base_ok. rewrite Q2, Q8, !Qs by inl. repeat split; try assumption.
          intros r Hr. rewrite Qs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
        + eapply eff_weaken; [exact EFF|]. unfold P5. rewrite (vec_blocks_z _ Hz), app_nil_r. intros a [Ha|Hb]; [left; lia | right; exact Hb].
        + unfold P5. rewrite (vec_blocks_z _ Hz), app_nil_r. exact LAP.
        + unfold P5. rewrite (vec_blocks_z _ Hz), app_nil_r. exact SUB.
      -
        assert (Hdef224 : defined M (st + 200) (Z.of_nat 8)) by (eapply (d_defined _ _ _ _ _ _ 200 _ D); cbn; lia).
        xruns HR HK 100%nat STOPS (SCR [false] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_so. exact Hdef224. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        set (Mw := wbytes M _ _).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 10%bv Gc10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
        assert (HMw : forall x : word, ~ (st + 200 <= bv_unsigned x < st + 208) -> Mw x = M x).
        { intros x Hx. pose proof (u64_range x). unfold Mw.
          rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMg : forall x : word, M x <> None -> Mw x <> None) by (intros x Hx; unfold Mw; apply wbytes_grows; exact Hx).
        assert (AIw : ainv MI A Mw model).
        { eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
          intros x Ho. apply HMw. intros Hx.
          exact (d_unowned _ _ _ _ _ _ D (bv_unsigned x - st) ltac:(lia) ltac:(lia) ltac:(replace (st + (bv_unsigned x - st)) with (bv_unsigned x) by lia; exact Ho)). }
        assert (FRw : frame Mw).
        { destruct FR as (F1 & F2 & F3). unfold frame, cell8, Mw. split; [|split]; cellpeel. }
        assert (DEFw : defined Mw (sp - 32 - DEL_STACK) (32 + DEL_STACK)) by (unfold Mw; apply defined_wbytes; exact DEF).
        assert (EFFw : eff MI A0 A M0 Mw W (fun a => FK 216 P6 a \/ (st + 200 <= a < st + 208))).
        { eapply eff_weaken; [eapply eff_trans; [exact EFF | |]|].
          - eapply eff_store with (F := fun a : Z => st + 200 <= a < st + 208); [|exact HMg]. intros x HF HW. apply HMw. intros Hx. apply HF. exact Hx.
          - intros a Ha. apply WIN. unfold W, W_of in Ha. cbn in Ha. unfold zwin. lia.
          - intros a Ha. exact Ha. }
        assert (Hin5 : In (vb, vc - vb) P5) by (unfold P5; rewrite (vec_blocks_nz _ Hnz); left; reflexivity).
        assert (Hin6 : In (vb, vc - vb) (state_blocks c)) by (rewrite SB, !in_app_iff; do 4 right; left; exact Hin5).
        assert (ROCw : img_ro_clear L Mw).
        { eapply (roc_of_eff A Mw _ _ EFFw SUB). intros a [[Ho|Hb]|Hr]; [left; lia | right; exact Hb | left; lia]. }
        eapply (del_call fx A Mw model Rc vb (vc - vb) (sp - 32) V1_PC K AIw MS ROCw G1);
          [ apply bv_eq; vm_compute; reflexivity | unfold V1_PC; lia | exact G2
          | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16 | lia
          | rewrite Gs by inl; exact B3 | rewrite Gs by inl; exact B4 | exact Gc10
          | right; exact (d_live _ _ _ _ _ _ (vb, vc - vb) D Hin6 ltac:(intros X; apply in_map_iff in X; destruct X as (b' & Hbb & Hb'); exact (ne_split _ _ _ _ SB5 ltac:(rewrite !in_app_iff; do 4 right; exact Hin5) Hb' (eq_sym Hbb))))
          | lia | lia
          | intros i Hi; apply DEFw; lia
          | intros a Ha; apply WIN; unfold zwin in *; lia | ].
        intros A' R' M' model' AI' MS' Hfs' Hfds' KEPT LDEL EFF1 DEF' WIN'.
        destruct (del_post _ P6 A Mw model A' M' vb (vc - vb) AIw FRw DEFw WIN EFFw LAP Hin6 LDEL EFF1 DEF' WIN')
          as (FR' & DEF2 & WIN2 & EFF2 & LAP2).
        apply (POST A'). constructor.
        + exact AI'. + exact MS'. + congruence. + congruence.
        + eapply base_kept; [|exact KEPT]. unfold base_ok. rewrite G2, G8, !Gs by inl. repeat split; try assumption.
          intros r Hr. rewrite Gs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
        + exact FR'. + exact DEF2. + exact WIN2.
        + eapply eff_weaken; [exact EFF2|]. unfold P5. rewrite (vec_blocks_nz _ Hnz).
          intros a [[Hf|Ho]|Hb]; [| left; lia | right; destruct Hb as (b & Hb & Hba); exists b; split; [apply in_app_iff; right; exact Hb | exact Hba]].
          destruct Hf as [Hf|(b & Hb & Hba)]; [left; lia | right]. exists b. split; [apply in_app_iff; left; exact Hb | exact Hba].
        + unfold P5. rewrite (vec_blocks_nz _ Hnz). exact LAP2.
        + unfold P5. rewrite (vec_blocks_nz _ Hnz). intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]]; [exact (SUB b Hb) | exact Hin6].
        + eapply (odef_eff A A' Mw M' model); [exact AIw | exact EFF1 | intros a Ha; cbn beta in Ha; destruct (blk_range _ Hin6) as (_ & _ & Hbc); cbn in Hbc; lia | unfold Mw; apply defined_wbytes; exact ODEF].
    Qed.

    Lemma blkV1 : forall A M model R,
      dst 192 (P6 ++ P5) A M model R ->
      (forall A' M' model' R', dst 168 ((P6 ++ P5) ++ P4) A' M' model' R' -> srealizes SEGS (cfg fx R' M3_PC M' model') K) ->
      srealizes SEGS (cfg fx R V1_PC M model) K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw fx A0 s R0 M0 model0 sp ret st c K CB SR ASP.
      intros A M model R D POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hstsp & Hsthi & Hstown).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds B FR DEF WIN EFF LAP SUB ODEF]. destruct B as (B2 & B3 & B4 & B8 & Bs).
      pose proof (sr_v1 _ _ _ _ _ _ _ SR) as VR. destruct VR as [Cb0 Ce0 Cc0 Hblk].
      set (vb := t3a (st_v1 c)) in *. set (ve := t3b (st_v1 c)) in *. set (vc := t3c (st_v1 c)) in *.
      pose proof (d_cell _ _ _ _ _ _ 168 8 vb D Cb0 ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cb.
      pose proof (d_cell _ _ _ _ _ _ 184 8 vc D ltac:(replace (st + 184) with (st + 168 + 16) by lia; exact Cc0) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cc.
      unfold cell8 in *. pose proof (proj1 Cb) as Hvbr. pose proof (proj1 Cc) as Hvcr.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 (sp - 32); Z_to_bv 64 st; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 vb; Z_to_bv 64 vc]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (8%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.
      destruct (Z.eq_dec vb 0) as [Hz | Hnz].
      -
        xruns HR HK 100%nat STOPS (SCR [true] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. }
        apply (POST A). constructor; try assumption.
        + rreg HR' 2%bv Q2. rreg HR' 8%bv Q8. pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl) as Qs.
          unfold base_ok. rewrite Q2, Q8, !Qs by inl. repeat split; try assumption.
          intros r Hr. rewrite Qs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
        + eapply eff_weaken; [exact EFF|]. unfold P4. rewrite (vec_blocks_z _ Hz), app_nil_r. intros a [Ha|Hb]; [left; lia | right; exact Hb].
        + unfold P4. rewrite (vec_blocks_z _ Hz), app_nil_r. exact LAP.
        + unfold P4. rewrite (vec_blocks_z _ Hz), app_nil_r. exact SUB.
      -
        assert (Hdef224 : defined M (st + 176) (Z.of_nat 8)) by (eapply (d_defined _ _ _ _ _ _ 176 _ D); cbn; lia).
        xruns HR HK 100%nat STOPS (SCR [false] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_so. exact Hdef224. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        set (Mw := wbytes M _ _).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 10%bv Gc10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
        assert (HMw : forall x : word, ~ (st + 176 <= bv_unsigned x < st + 184) -> Mw x = M x).
        { intros x Hx. pose proof (u64_range x). unfold Mw.
          rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMg : forall x : word, M x <> None -> Mw x <> None) by (intros x Hx; unfold Mw; apply wbytes_grows; exact Hx).
        assert (AIw : ainv MI A Mw model).
        { eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
          intros x Ho. apply HMw. intros Hx.
          exact (d_unowned _ _ _ _ _ _ D (bv_unsigned x - st) ltac:(lia) ltac:(lia) ltac:(replace (st + (bv_unsigned x - st)) with (bv_unsigned x) by lia; exact Ho)). }
        assert (FRw : frame Mw).
        { destruct FR as (F1 & F2 & F3). unfold frame, cell8, Mw. split; [|split]; cellpeel. }
        assert (DEFw : defined Mw (sp - 32 - DEL_STACK) (32 + DEL_STACK)) by (unfold Mw; apply defined_wbytes; exact DEF).
        assert (EFFw : eff MI A0 A M0 Mw W (fun a => FK 192 (P6 ++ P5) a \/ (st + 176 <= a < st + 184))).
        { eapply eff_weaken; [eapply eff_trans; [exact EFF | |]|].
          - eapply eff_store with (F := fun a : Z => st + 176 <= a < st + 184); [|exact HMg]. intros x HF HW. apply HMw. intros Hx. apply HF. exact Hx.
          - intros a Ha. apply WIN. unfold W, W_of in Ha. cbn in Ha. unfold zwin. lia.
          - intros a Ha. exact Ha. }
        assert (Hin4 : In (vb, vc - vb) P4) by (unfold P4; rewrite (vec_blocks_nz _ Hnz); left; reflexivity).
        assert (Hin6 : In (vb, vc - vb) (state_blocks c)) by (rewrite SB, !in_app_iff; do 3 right; left; exact Hin4).
        assert (ROCw : img_ro_clear L Mw).
        { eapply (roc_of_eff A Mw _ _ EFFw SUB). intros a [[Ho|Hb]|Hr]; [left; lia | right; exact Hb | left; lia]. }
        eapply (del_call fx A Mw model Rc vb (vc - vb) (sp - 32) M3_PC K AIw MS ROCw G1);
          [ apply bv_eq; vm_compute; reflexivity | unfold M3_PC; lia | exact G2
          | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16 | lia
          | rewrite Gs by inl; exact B3 | rewrite Gs by inl; exact B4 | exact Gc10
          | right; exact (d_live _ _ _ _ _ _ (vb, vc - vb) D Hin6 ltac:(intros X; apply in_map_iff in X; destruct X as (b' & Hbb & Hb'); apply in_app_iff in Hb'; exact (ne_split _ _ _ _ SB4 ltac:(rewrite !in_app_iff; do 3 right; exact Hin4) ltac:(apply in_app_iff; destruct Hb' as [Hb'|Hb']; [right|left]; exact Hb') (eq_sym Hbb))))
          | lia | lia
          | intros i Hi; apply DEFw; lia
          | intros a Ha; apply WIN; unfold zwin in *; lia | ].
        intros A' R' M' model' AI' MS' Hfs' Hfds' KEPT LDEL EFF1 DEF' WIN'.
        destruct (del_post _ (P6 ++ P5) A Mw model A' M' vb (vc - vb) AIw FRw DEFw WIN EFFw LAP Hin6 LDEL EFF1 DEF' WIN')
          as (FR' & DEF2 & WIN2 & EFF2 & LAP2).
        apply (POST A'). constructor.
        + exact AI'. + exact MS'. + congruence. + congruence.
        + eapply base_kept; [|exact KEPT]. unfold base_ok. rewrite G2, G8, !Gs by inl. repeat split; try assumption.
          intros r Hr. rewrite Gs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
        + exact FR'. + exact DEF2. + exact WIN2.
        + eapply eff_weaken; [exact EFF2|]. unfold P4. rewrite (vec_blocks_nz _ Hnz).
          intros a [[Hf|Ho]|Hb]; [| left; lia | right; destruct Hb as (b & Hb & Hba); exists b; split; [apply in_app_iff; right; exact Hb | exact Hba]].
          destruct Hf as [Hf|(b & Hb & Hba)]; [left; lia | right]. exists b. split; [apply in_app_iff; left; exact Hb | exact Hba].
        + unfold P4. rewrite (vec_blocks_nz _ Hnz). exact LAP2.
        + unfold P4. rewrite (vec_blocks_nz _ Hnz). intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]]; [exact (SUB b Hb) | exact Hin6].
        + eapply (odef_eff A A' Mw M' model); [exact AIw | exact EFF1 | intros a Ha; cbn beta in Ha; destruct (blk_range _ Hin6) as (_ & _ & Hbc); cbn in Hbc; lia | unfold Mw; apply defined_wbytes; exact ODEF].
    Qed.

    Definition nblocks {V : Type} (NS : Z) (ents : list (Z * (Z * V))) : list (Z * Z) := map (fun e => (fst e, NS)) ents.
    Definition ablock (bl bc : Z) : list (Z * Z) := if bc =? 0 then [] else [(bl, 8 * bc)].

    Lemma umap_blocks_members : forall {V : Type} NS bl bc (ents : list (Z * (Z * V))) b,
      In b (umap_blocks NS bl bc ents) <-> In b (nblocks NS ents ++ ablock bl bc).
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret CB. intros V NS bl bc ents b. unfold umap_blocks, nblocks, ablock. rewrite !in_app_iff. tauto. Qed.

    Lemma d_blk_agree : forall off bs A M model R b, dst off bs A M model R -> 0 <= off ->
      In b (state_blocks c) -> ~ In (fst b) (map fst bs) -> agree_on M0 M (fst b) (snd b).
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLrw_img HLerr_rw A0 s R0 M0 model0 sp ret st c CB SR ASP.
      intros off bs A M model R [p n] D Hoff Hb Hni. cbn. cbn in Hni.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). destruct ASP as (Hstsp & Hsthi & Hstown). pose proof ceiling_lt as Hcl.
      pose proof (blocks_live _ Hb) as Hlv.
      destruct (live_facts' A0 M0 model0 p n AI0 Hlv) as (Hn0 & Hp0 & Hpc & Hown).
      intros i Hi. apply (ef_frame _ _ _ _ _ _ _ _ _ (d_eff _ _ _ _ _ _ D)). rewrite u64_of_Z by lia.
      intros [Ho|[Ho'|[Hnm|[Hf|[Hw|He]]]]].
      - exact (proj1 (Hown (p + i) ltac:(lia)) Ho).
      - destruct (ef_own _ _ _ _ _ _ _ _ _ (d_eff _ _ _ _ _ _ D) _ Ho') as [Ho0|[[_ [_ Hm]]|Hf]].
        + exact (proj1 (Hown (p + i) ltac:(lia)) Ho0).
        + exact (proj2 (Hown (p + i) ltac:(lia)) Hm).
        + destruct Hf as [Hobj | (b' & Hb' & Hba)]; [lia|].
          assert (Hne : fst b' <> p) by (intros Heq; apply Hni; rewrite <- Heq; apply in_map; exact Hb').
          pose proof (blocks_apart b' (p, n) (d_sub _ _ _ _ _ _ D b' Hb') Hb Hne) as Hap. unfold apart in Hap. cbn in Hap. lia.
      - destruct Hnm as (_ & _ & Hm). exact (proj2 (Hown (p + i) ltac:(lia)) Hm).
      - destruct Hf as [Hobj | (b' & Hb' & Hba)]; [lia|].
        assert (Hne : fst b' <> p) by (intros Heq; apply Hni; rewrite <- Heq; apply in_map; exact Hb').
        pose proof (blocks_apart b' (p, n) (d_sub _ _ _ _ _ _ D b' Hb') Hb Hne) as Hap. unfold apart in Hap. cbn in Hap. lia.
      - unfold W, W_of in Hw. cbn in Hw. lia.
      - exact (live_offimg' A0 M0 model0 p n (p + i) AI0 Hlv ltac:(lia) (HLrw_img _ (HLerr_rw _ He))).
    Qed.

    Lemma loop_post : forall (F1 : Z -> Prop) bs A M A' M' (Fs : Z -> Prop) (nbs : list (Z * Z)),
      frame M -> defined M (sp - 32 - DEL_STACK) (32 + DEL_STACK) ->
      (forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A a) ->
      eff MI A0 A M0 M W F1 -> lapply (live MI A0) (map (fun b => LDel (fst b)) bs) (live MI A) ->
      (forall b, In b nbs -> In b (state_blocks c)) -> (forall a, Fs a -> inblk nbs a) ->
      eff MI A A' M M' (sp - 32 - DEL_STACK, sp - 32) Fs ->
      lapply (live MI A) (map (fun b => LDel (fst b)) nbs) (live MI A') ->
      (forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A' a) ->
      frame M' /\ eff MI A0 A' M0 M' W (fun a => F1 a \/ inblk nbs a)
      /\ lapply (live MI A0) (map (fun b => LDel (fst b)) (bs ++ nbs)) (live MI A').
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLimg_lo HLrw_img HLerr_rw A0 s R0 M0 model0 sp ret st c CB SR.
      intros F1 bs A M A' M' Fs nbs FR DEF WIN EFF LAP SUBn HFs EFF1 LAP1 WIN'.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct CR0 as [_ _ Hretr _ _ _ _ _].
      pose proof (u64_range (getr R0 8%bv)) as Hr8. pose proof (u64_range (getr R0 9%bv)) as Hr9.
      assert (AG : forall a k, sp - 32 <= a -> 0 <= k -> a + k <= sp -> agree_on M M' a k).
      { intros a k Ha Hk Hak.
        eapply (agree_above_via_eff' A A' M M' _ _ a k (sp - 32) EFF1); [lia | cbn; lia | lia | lia | lia | | |].
        - intros i Hi. apply WIN. unfold zwin. lia.
        - intros i Hi. replace (a + i) with (sp - 32 - DEL_STACK + (a + i - (sp - 32 - DEL_STACK))) by lia. apply DEF. lia.
        - intros i Hi Hf. destruct (HFs _ Hf) as (b & Hb & Hba). destruct (blk_range b (SUBn b Hb)) as (_ & _ & Hbc). lia. }
      split; [|split].
      - destruct FR as (F1' & F2' & F3'). unfold frame.
        split; [|split]; (eapply cellw_agree; [eassumption | apply AG; cbn; lia | lia | cbn; lia]).
      - eapply eff_weaken; [eapply eff_trans; [exact EFF | eapply eff_widen; [exact EFF1|] |]|].
        + intros a Ha. unfold W, W_of in *. cbn in *. lia.
        + intros a Ha. apply WIN'. unfold W, W_of in Ha. cbn in Ha. unfold zwin. lia.
        + intros a [Ha|Ha]; [left; exact Ha | right; exact (HFs a Ha)].
      - rewrite map_app. eapply lapply_app; [exact LAP | exact LAP1].
    Qed.

    #[local] Notation ents3 := (t3c (st_m3 c)).
    #[local] Notation bl3 := (t3a (st_m3 c)).
    #[local] Notation bc3 := (t3b (st_m3 c)).
    #[local] Notation ents2 := (t3c (st_m2 c)).
    #[local] Notation bl2 := (t3a (st_m2 c)).
    #[local] Notation bc2 := (t3b (st_m2 c)).
    #[local] Notation ents1 := (t3c (st_m1 c)).
    #[local] Notation bl1 := (t3a (st_m1 c)).
    #[local] Notation bc1 := (t3b (st_m1 c)).

    Definition BS3 : list (Z * Z) := (P6 ++ P5) ++ P4.
    Definition BS2 : list (Z * Z) := (BS3 ++ nblocks 24 ents3) ++ ablock bl3 bc3.
    Definition BS1 : list (Z * Z) := (BS2 ++ nblocks 32 ents2) ++ ablock bl2 bc2.
    Definition BS0 : list (Z * Z) := (BS1 ++ nblocks 24 ents1) ++ ablock bl1 bc1.

    Lemma blkM3 : forall A M model R,
      dst 168 BS3 A M model R ->
      (forall A' M' model' R', dst 168 (BS3 ++ nblocks 24 ents3) A' M' model' R' -> srealizes SEGS (cfg fx R' A3_PC M' model') K) ->
      srealizes SEGS (cfg fx R M3_PC M model) K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw fx A0 s R0 M0 model0 sp ret st c K CB SR ASP.
      intros A M model R D POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hstsp & Hsthi & Hstown).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds B FR DEF WIN EFF LAP SUB ODEF]. destruct B as (B2 & B3 & B4 & B8 & Bs).
      pose proof (sr_m3 _ _ _ _ _ _ _ SR) as U.
      pose proof (d_cell _ _ _ _ _ _ 144 8 (hdaddr ents3) D ltac:(replace (st + 144) with (st + 128 + 16) by lia; exact (h_p1 (u_hdr U))) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cp1.
      unfold cell8 in Cp1. pose proof (proj1 Cp1) as Hhdr.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 (sp - 32); Z_to_bv 64 st; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 (hdaddr ents3)]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (8%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.

      assert (HnP : forall p k v, In (p, (k, v)) ents3 -> In (p, 24) P3).
      { intros p k v Hin. unfold P3, umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin]. }
      assert (HnSB : forall p k v, In (p, (k, v)) ents3 -> In (p, 24) (state_blocks c)).
      { intros p k v Hin. rewrite SB, !in_app_iff. do 2 right; left; exact (HnP p k v Hin). }
      assert (Hbs_sub : forall b', In b' BS3 -> In b' (P4 ++ P5 ++ P6)).
      { intros b' Hb'. unfold BS3 in *. rewrite ?in_app_iff in Hb'. rewrite ?in_app_iff.  tauto. }
      assert (Hnbs : forall p k v, In (p, (k, v)) ents3 -> ~ In p (map fst BS3)).
      { intros p k v Hin X. apply in_map_iff in X. destruct X as (b' & Hbb & Hb').
        exact (ne_split _ _ (p, 24) b' SB3 ltac:(rewrite !in_app_iff; do 2 right; exact (HnP p k v Hin)) (Hbs_sub b' Hb') (eq_sym Hbb)). }
      assert (Hcase : ents3 = [] \/ ents3 <> []) by (destruct ents3; [left; reflexivity | right; discriminate]).
      destruct Hcase as [He | Hne].
      -
        assert (Hz : hdaddr ents3 = 0) by (rewrite He; reflexivity). rewrite Hz in *.
        xruns HR HK 100%nat STOPS (SCR [true] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. }
        apply (POST A). rewrite He. cbn [nblocks map]. rewrite app_nil_r. constructor; try assumption.
        rreg HR' 2%bv Q2. rreg HR' 8%bv Q8. pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl) as Qs.
        unfold base_ok. rewrite Q2, Q8, !Qs by inl. repeat split; try assumption.
        intros r Hr. rewrite Qs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
      -
        assert (Hhd : 0 < hdaddr ents3).
        { destruct ents3 as [|[p0 [k0 v0]] rest0] eqn:He; [exfalso; exact (Hne eq_refl)|]. cbn.
          destruct (u_node U p0 k0 v0 ltac:(try rewrite He; left; reflexivity)) as (_ & Hp & _). lia. }
        xruns HR HK 100%nat STOPS (SCR [false] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. }
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        rreg HRc 2%bv Q2. rreg HRc 8%bv Q8. rreg HRc 10%bv Q10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Qs.
        assert (Bc : base_ok Rc).
        { unfold base_ok. rewrite Q2, Q8, !Qs by inl. repeat split; try assumption.
          intros r Hr. rewrite Qs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr. }
        destruct Bc as (Bc2 & Bc3 & Bc4 & Bc8 & Bcs).
        eapply (free_loop3 sp Rc Hsp16 Hsplo Hsphi Hspimg Bc2 Bc3 Bc4 Z 24 ents3 fx A M model Rc K Hne ltac:(lia) AI MS (d_roc _ _ _ _ _ _ D ltac:(lia))).
        + intros r Hr. reflexivity.
        + exact Q10.
        + intros p k v Hin. exact (d_live _ _ _ _ _ _ (p, 24) D (HnSB p k v Hin) (Hnbs p k v Hin)).
        + exact (u_nodup U).
        + eapply (chain_agree SEGS _ M0 M); [exact (u_chain U)|]. intros q kq vq Hin.
          destruct (u_node U q kq vq Hin) as (_ & Hq0 & Hq1 & _).
          split; [|lia]. eapply agree_on_sub; [exact (d_blk_agree _ _ _ _ _ _ (q, 24) D ltac:(lia) (HnSB q kq vq Hin) (Hnbs q kq vq Hin)) | cbn; lia | cbn; lia].
        + exact DEF.
        + exact WIN.
        +
          intros A' M' model' R' AI' MS' Hfs' Hfds' HP EFF1 LAP1 DEF' WIN'.
          assert (SUBn : forall b, In b (nblocks 24 ents3) -> In b (state_blocks c)).
          { intros b Hb. unfold nblocks in Hb. apply in_map_iff in Hb. destruct Hb as ([p [k v]] & <- & Hin). exact (HnSB p k v Hin). }
          destruct (loop_post _ BS3 A M A' M' (nodes_foot 24 ents3) (nblocks 24 ents3) FR DEF WIN EFF LAP SUBn) as (FR' & EFF2 & LAP2);
            [| exact EFF1 | unfold nblocks; rewrite map_map; exact LAP1 | exact WIN' |].
          { intros a (p & Hp & Hpa). apply in_map_iff in Hp. destruct Hp as ([p' kv] & Hpp & Hin). cbn in Hpp. subst p'.
            exists (p, 24). split; [| exact Hpa]. unfold nblocks. apply in_map_iff. exists (p, kv). split; [reflexivity | exact Hin]. }
          apply (POST A'). constructor.
          * exact AI'. * exact MS'. * congruence. * congruence.
          * unfold base_ok. rewrite !(HP _) by inl. repeat split; try assumption. intros r Hr. rewrite (HP r); [apply Bcs, Hr|].
            cbn in Hr. unfold PRES. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
          * exact FR'. * exact DEF'. * exact WIN'.
          * eapply eff_weaken; [exact EFF2|]. intros a [[Ho|Hb]|Hb]; [left; exact Ho | right | right].
            -- destruct Hb as (b & Hb & Hba). exists b. split; [apply in_app_iff; left; exact Hb | exact Hba].
            -- destruct Hb as (b & Hb & Hba). exists b. split; [apply in_app_iff; right; exact Hb | exact Hba].
          * exact LAP2.
          * intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (SUB b Hb) | exact (SUBn b Hb)].
          * eapply (odef_nodes A A' M M' model); [exact AI | exact EFF1 | exact HnSB | exact ODEF].
    Qed.

    Lemma blkA3 : forall A M model R,
      dst 168 (BS3 ++ nblocks 24 ents3) A M model R ->
      (forall A' M' model' R', dst 128 ((BS3 ++ nblocks 24 ents3) ++ ablock bl3 bc3) A' M' model' R' ->
                               srealizes SEGS (cfg fx R' M2_PC M' model') K) ->
      srealizes SEGS (cfg fx R A3_PC M model) K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw fx A0 s R0 M0 model0 sp ret st c K CB SR ASP.
      intros A M model R D POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hstsp & Hsthi & Hstown).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds B FR DEF WIN EFF LAP SUB ODEF]. destruct B as (B2 & B3 & B4 & B8 & Bs).
      pose proof (sr_m3 _ _ _ _ _ _ _ SR) as U.
      pose proof (d_cell _ _ _ _ _ _ 128 8 bl3 D (h_bl (u_hdr U)) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cbl.
      pose proof (d_cell _ _ _ _ _ _ 136 8 bc3 D ltac:(replace (st + 136) with (st + 128 + 8) by lia; exact (h_bc (u_hdr U))) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cbc.
      unfold cell8 in Cbl, Cbc. pose proof (proj1 Cbl) as Hblr. pose proof (proj1 Cbc) as Hbcr.
      assert (Hbcr2 : 0 <= bc3 <= 26339969) by (pose proof (u_bseq U) as HB; unfold BSEQ in HB; cbn in HB; lia).
      assert (HdefHO : defined M (st + 128) (Z.of_nat 8)) by (eapply (d_defined _ _ _ _ _ _ 128 _ D); cbn; lia).
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 (sp - 32); Z_to_bv 64 st; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 bl3; Z_to_bv 64 bc3]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (8%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.

      assert (HMW : forall Mw, Mw = wbytes M (Z_to_bv 64 (st + 128)) (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
                (forall x : word, ~ (st + 128 <= bv_unsigned x < st + 136) -> Mw x = M x)
                /\ (forall x : word, M x <> None -> Mw x <> None)
                /\ ainv MI A Mw model /\ frame Mw /\ defined Mw (sp - 32 - DEL_STACK) (32 + DEL_STACK)
                /\ eff MI A0 A M0 Mw W (fun a => FK 168 (BS3 ++ nblocks 24 ents3) a \/ (st + 128 <= a < st + 136))).
      { intros Mw ->.
        assert (HMw : forall x : word, ~ (st + 128 <= bv_unsigned x < st + 136) -> wbytes M (Z_to_bv 64 (st + 128)) (word_to_le_bytes 8 (Z_to_bv 64 0)) x = M x).
        { intros x Hx. pose proof (u64_range x).
          rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMg : forall x : word, M x <> None -> wbytes M (Z_to_bv 64 (st + 128)) (word_to_le_bytes 8 (Z_to_bv 64 0)) x <> None)
          by (intros x Hx; apply wbytes_grows; exact Hx).
        split; [exact HMw|]. split; [exact HMg|]. split; [|split; [|split]].
        - eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
          intros x Ho. apply HMw. intros Hx.
          exact (d_unowned _ _ _ _ _ _ D (bv_unsigned x - st) ltac:(lia) ltac:(lia) ltac:(replace (st + (bv_unsigned x - st)) with (bv_unsigned x) by lia; exact Ho)).
        - destruct FR as (F1 & F2 & F3). pose proof (u64_range (getr R0 8%bv)). pose proof (u64_range (getr R0 9%bv)). destruct CR0 as [_ _ Hretr _ _ _ _ _].
          unfold frame, cell8. split; [|split]; cellpeel.
        - apply defined_wbytes; exact DEF.
        - eapply eff_weaken; [eapply eff_trans; [exact EFF | |]|].
          + eapply eff_store with (F := fun a : Z => st + 128 <= a < st + 136); [|exact HMg]. intros x HF HW. apply HMw. intros Hx. apply HF. exact Hx.
          + intros a Ha. apply WIN. unfold W, W_of in Ha. cbn in Ha. unfold zwin. lia.
          + intros a Ha. exact Ha. }
      destruct (Z.eq_dec bc3 0) as [Hz | Hnz].
      -
        assert (Hbl0 : bl3 = 0) by (destruct (u_blive U) as [[_ H]|[H _]]; [exact H | exfalso; exact (H Hz)]).
        rewrite Hbl0 in *.
        xruns HR HK 100%nat STOPS (SCR [true] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. sc_so. exact HdefHO. }
        postrun.
        destruct (HMW _ eq_refl) as (HMw & HMg & AIw & FRw & DEFw & EFFw).
        apply (POST A). unfold ablock. rewrite (proj2 (Z.eqb_eq _ _) Hz), app_nil_r. constructor; try assumption.
        + rreg HR' 2%bv Q2. rreg HR' 8%bv Q8. pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl) as Qs.
          unfold base_ok. rewrite Q2, Q8, !Qs by inl. repeat split; try assumption.
          intros r Hr. rewrite Qs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
        + eapply eff_weaken; [exact EFFw|]. intros a [[Ho|Hb]|Hs]; [left; lia | right; exact Hb | left; lia].
        + apply defined_wbytes; exact ODEF.
      -
        assert (Hbl1 : 0 < bl3) by (exact (u_bl_lo U Hnz)).
        xruns HR HK 100%nat STOPS (SCR [false] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_so. exact HdefHO. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        set (Mw := wbytes M _ _).
        destruct (HMW Mw eq_refl) as (HMw & HMg & AIw & FRw & DEFw & EFFw).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 10%bv Gc10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
        assert (HinP : In (bl3, 8 * bc3) P3).
        { unfold P3, umap_blocks. destruct (Z.eqb_spec bc3 0); [lia|]. apply in_app_iff. left. left. reflexivity. }
        assert (Hin6 : In (bl3, 8 * bc3) (state_blocks c)) by (rewrite SB, !in_app_iff; do 2 right; left; exact HinP).
        assert (Hbs_sub : forall b', In b' BS3 -> In b' (P4 ++ P5 ++ P6)).
        { intros b' Hb'. unfold BS3 in *. rewrite ?in_app_iff in Hb'. rewrite ?in_app_iff.  tauto. }
        assert (Hnbs : ~ In bl3 (map fst (BS3 ++ nblocks 24 ents3))).
        { rewrite map_app, in_app_iff. intros [X|X].
          - apply in_map_iff in X. destruct X as (b' & Hbb & Hb').
            exact (ne_split _ _ (bl3, 8 * bc3) b' SB3 ltac:(rewrite !in_app_iff; do 2 right; exact HinP) (Hbs_sub b' Hb') (eq_sym Hbb)).
          - unfold nblocks in X. rewrite map_map in X. cbn in X. apply in_map_iff in X. destruct X as ([p [k v]] & Hp & Hin). cbn in Hp. subst p.
            pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (u_node U bl3 k v Hin))))))))) Hnz) as Hap.
            unfold apart in Hap. lia. }
        assert (ROCw : img_ro_clear L Mw).
        { eapply (roc_of_eff A Mw _ _ EFFw SUB). intros a [[Ho|Hb]|Hr]; [left; lia | right; exact Hb | left; lia]. }
        eapply (del_call fx A Mw model Rc bl3 (8 * bc3) (sp - 32) M2_PC K AIw MS ROCw G1);
          [ apply bv_eq; vm_compute; reflexivity | unfold M2_PC; lia | exact G2
          | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16 | lia
          | rewrite Gs by inl; exact B3 | rewrite Gs by inl; exact B4 | exact Gc10
          | right; exact (d_live _ _ _ _ _ _ (bl3, 8 * bc3) D Hin6 Hnbs)
          | lia | lia
          | intros i Hi; apply DEFw; lia
          | intros a Ha; apply WIN; unfold zwin in *; lia | ].
        intros A' R' M' model' AI' MS' Hfs' Hfds' KEPT LDEL EFF1 DEF' WIN'.
        destruct (del_post _ _ A Mw model A' M' bl3 (8 * bc3) AIw FRw DEFw WIN EFFw LAP Hin6 LDEL EFF1 DEF' WIN')
          as (FR' & DEF2 & WIN2 & EFF2 & LAP2).
        apply (POST A'). unfold ablock. destruct (Z.eqb_spec bc3 0); [lia|]. constructor.
        + exact AI'. + exact MS'. + congruence. + congruence.
        + eapply base_kept; [|exact KEPT]. unfold base_ok. rewrite G2, G8, !Gs by inl. repeat split; try assumption.
          intros r Hr. rewrite Gs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
        + exact FR'. + exact DEF2. + exact WIN2.
        + eapply eff_weaken; [exact EFF2|].
          intros a [[[Ho|Hb]|Hs]|Hb]; [left; lia | right | left; lia | right].
          * destruct Hb as (b & Hb & Hba). exists b. split; [apply in_app_iff; left; exact Hb | exact Hba].
          * destruct Hb as (b & Hb & Hba). exists b. split; [apply in_app_iff; right; exact Hb | exact Hba].
        + exact LAP2.
        + intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]]; [exact (SUB b Hb) | exact Hin6].
        + eapply (odef_eff A A' Mw M' model); [exact AIw | exact EFF1 | intros a Ha; cbn beta in Ha; destruct (blk_range _ Hin6) as (_ & _ & Hbc); cbn in Hbc; lia | unfold Mw; apply defined_wbytes; exact ODEF].
    Qed.

    Lemma blkM2 : forall A M model R,
      dst 128 BS2 A M model R ->
      (forall A' M' model' R', dst 128 (BS2 ++ nblocks 32 ents2) A' M' model' R' -> srealizes SEGS (cfg fx R' A2_PC M' model') K) ->
      srealizes SEGS (cfg fx R M2_PC M model) K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw fx A0 s R0 M0 model0 sp ret st c K CB SR ASP.
      intros A M model R D POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hstsp & Hsthi & Hstown).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds B FR DEF WIN EFF LAP SUB ODEF]. destruct B as (B2 & B3 & B4 & B8 & Bs).
      pose proof (sr_m2 _ _ _ _ _ _ _ SR) as U.
      pose proof (d_cell _ _ _ _ _ _ 104 8 (hdaddr ents2) D ltac:(replace (st + 104) with (st + 88 + 16) by lia; exact (h_p1 (u_hdr U))) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cp1.
      unfold cell8 in Cp1. pose proof (proj1 Cp1) as Hhdr.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 (sp - 32); Z_to_bv 64 st; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 (hdaddr ents2)]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (8%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.

      assert (HnP : forall p k v, In (p, (k, v)) ents2 -> In (p, 32) P2).
      { intros p k v Hin. unfold P2, umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin]. }
      assert (HnSB : forall p k v, In (p, (k, v)) ents2 -> In (p, 32) (state_blocks c)).
      { intros p k v Hin. rewrite SB, !in_app_iff. do 1 right; left; exact (HnP p k v Hin). }
      assert (Hbs_sub : forall b', In b' BS2 -> In b' (P3 ++ P4 ++ P5 ++ P6)).
      { intros b' Hb'. unfold BS2, BS3, P3 in *. rewrite ?in_app_iff in Hb'. rewrite ?in_app_iff. pose proof (umap_blocks_members 24 bl3 bc3 ents3 b') as HP3. rewrite in_app_iff in HP3. tauto. }
      assert (Hnbs : forall p k v, In (p, (k, v)) ents2 -> ~ In p (map fst BS2)).
      { intros p k v Hin X. apply in_map_iff in X. destruct X as (b' & Hbb & Hb').
        exact (ne_split _ _ (p, 32) b' SB2 ltac:(apply in_app_iff; right; exact (HnP p k v Hin)) (Hbs_sub b' Hb') (eq_sym Hbb)). }
      assert (Hcase : ents2 = [] \/ ents2 <> []) by (destruct ents2; [left; reflexivity | right; discriminate]).
      destruct Hcase as [He | Hne].
      -
        assert (Hz : hdaddr ents2 = 0) by (rewrite He; reflexivity). rewrite Hz in *.
        xruns HR HK 100%nat STOPS (SCR [true] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. }
        apply (POST A). rewrite He. cbn [nblocks map]. rewrite app_nil_r. constructor; try assumption.
        rreg HR' 2%bv Q2. rreg HR' 8%bv Q8. pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl) as Qs.
        unfold base_ok. rewrite Q2, Q8, !Qs by inl. repeat split; try assumption.
        intros r Hr. rewrite Qs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
      -
        assert (Hhd : 0 < hdaddr ents2).
        { destruct ents2 as [|[p0 [k0 v0]] rest0] eqn:He; [exfalso; exact (Hne eq_refl)|]. cbn.
          destruct (u_node U p0 k0 v0 ltac:(try rewrite He; left; reflexivity)) as (_ & Hp & _). lia. }
        xruns HR HK 100%nat STOPS (SCR [false] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. }
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        rreg HRc 2%bv Q2. rreg HRc 8%bv Q8. rreg HRc 10%bv Q10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Qs.
        assert (Bc : base_ok Rc).
        { unfold base_ok. rewrite Q2, Q8, !Qs by inl. repeat split; try assumption.
          intros r Hr. rewrite Qs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr. }
        destruct Bc as (Bc2 & Bc3 & Bc4 & Bc8 & Bcs).
        eapply (free_loop2 sp Rc Hsp16 Hsplo Hsphi Hspimg Bc2 Bc3 Bc4 (Z * Z * Z)%type 32 ents2 fx A M model Rc K Hne ltac:(lia) AI MS (d_roc _ _ _ _ _ _ D ltac:(lia))).
        + intros r Hr. reflexivity.
        + exact Q10.
        + intros p k v Hin. exact (d_live _ _ _ _ _ _ (p, 32) D (HnSB p k v Hin) (Hnbs p k v Hin)).
        + exact (u_nodup U).
        + eapply (chain_agree SEGS _ M0 M); [exact (u_chain U)|]. intros q kq vq Hin.
          destruct (u_node U q kq vq Hin) as (_ & Hq0 & Hq1 & _).
          split; [|lia]. eapply agree_on_sub; [exact (d_blk_agree _ _ _ _ _ _ (q, 32) D ltac:(lia) (HnSB q kq vq Hin) (Hnbs q kq vq Hin)) | cbn; lia | cbn; lia].
        + exact DEF.
        + exact WIN.
        +
          intros A' M' model' R' AI' MS' Hfs' Hfds' HP EFF1 LAP1 DEF' WIN'.
          assert (SUBn : forall b, In b (nblocks 32 ents2) -> In b (state_blocks c)).
          { intros b Hb. unfold nblocks in Hb. apply in_map_iff in Hb. destruct Hb as ([p [k v]] & <- & Hin). exact (HnSB p k v Hin). }
          destruct (loop_post _ BS2 A M A' M' (nodes_foot 32 ents2) (nblocks 32 ents2) FR DEF WIN EFF LAP SUBn) as (FR' & EFF2 & LAP2);
            [| exact EFF1 | unfold nblocks; rewrite map_map; exact LAP1 | exact WIN' |].
          { intros a (p & Hp & Hpa). apply in_map_iff in Hp. destruct Hp as ([p' kv] & Hpp & Hin). cbn in Hpp. subst p'.
            exists (p, 32). split; [| exact Hpa]. unfold nblocks. apply in_map_iff. exists (p, kv). split; [reflexivity | exact Hin]. }
          apply (POST A'). constructor.
          * exact AI'. * exact MS'. * congruence. * congruence.
          * unfold base_ok. rewrite !(HP _) by inl. repeat split; try assumption. intros r Hr. rewrite (HP r); [apply Bcs, Hr|].
            cbn in Hr. unfold PRES. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
          * exact FR'. * exact DEF'. * exact WIN'.
          * eapply eff_weaken; [exact EFF2|]. intros a [[Ho|Hb]|Hb]; [left; exact Ho | right | right].
            -- destruct Hb as (b & Hb & Hba). exists b. split; [apply in_app_iff; left; exact Hb | exact Hba].
            -- destruct Hb as (b & Hb & Hba). exists b. split; [apply in_app_iff; right; exact Hb | exact Hba].
          * exact LAP2.
          * intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (SUB b Hb) | exact (SUBn b Hb)].
          * eapply (odef_nodes A A' M M' model); [exact AI | exact EFF1 | exact HnSB | exact ODEF].
    Qed.

    Lemma blkA2 : forall A M model R,
      dst 128 (BS2 ++ nblocks 32 ents2) A M model R ->
      (forall A' M' model' R', dst 88 ((BS2 ++ nblocks 32 ents2) ++ ablock bl2 bc2) A' M' model' R' ->
                               srealizes SEGS (cfg fx R' M1_PC M' model') K) ->
      srealizes SEGS (cfg fx R A2_PC M model) K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw fx A0 s R0 M0 model0 sp ret st c K CB SR ASP.
      intros A M model R D POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hstsp & Hsthi & Hstown).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds B FR DEF WIN EFF LAP SUB ODEF]. destruct B as (B2 & B3 & B4 & B8 & Bs).
      pose proof (sr_m2 _ _ _ _ _ _ _ SR) as U.
      pose proof (d_cell _ _ _ _ _ _ 88 8 bl2 D (h_bl (u_hdr U)) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cbl.
      pose proof (d_cell _ _ _ _ _ _ 96 8 bc2 D ltac:(replace (st + 96) with (st + 88 + 8) by lia; exact (h_bc (u_hdr U))) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cbc.
      unfold cell8 in Cbl, Cbc. pose proof (proj1 Cbl) as Hblr. pose proof (proj1 Cbc) as Hbcr.
      assert (Hbcr2 : 0 <= bc2 <= 26339969) by (pose proof (u_bseq U) as HB; unfold BSEQ in HB; cbn in HB; lia).
      assert (HdefHO : defined M (st + 88) (Z.of_nat 8)) by (eapply (d_defined _ _ _ _ _ _ 88 _ D); cbn; lia).
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 (sp - 32); Z_to_bv 64 st; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 bl2; Z_to_bv 64 bc2]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (8%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.

      assert (HMW : forall Mw, Mw = wbytes M (Z_to_bv 64 (st + 88)) (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
                (forall x : word, ~ (st + 88 <= bv_unsigned x < st + 96) -> Mw x = M x)
                /\ (forall x : word, M x <> None -> Mw x <> None)
                /\ ainv MI A Mw model /\ frame Mw /\ defined Mw (sp - 32 - DEL_STACK) (32 + DEL_STACK)
                /\ eff MI A0 A M0 Mw W (fun a => FK 128 (BS2 ++ nblocks 32 ents2) a \/ (st + 88 <= a < st + 96))).
      { intros Mw ->.
        assert (HMw : forall x : word, ~ (st + 88 <= bv_unsigned x < st + 96) -> wbytes M (Z_to_bv 64 (st + 88)) (word_to_le_bytes 8 (Z_to_bv 64 0)) x = M x).
        { intros x Hx. pose proof (u64_range x).
          rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMg : forall x : word, M x <> None -> wbytes M (Z_to_bv 64 (st + 88)) (word_to_le_bytes 8 (Z_to_bv 64 0)) x <> None)
          by (intros x Hx; apply wbytes_grows; exact Hx).
        split; [exact HMw|]. split; [exact HMg|]. split; [|split; [|split]].
        - eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
          intros x Ho. apply HMw. intros Hx.
          exact (d_unowned _ _ _ _ _ _ D (bv_unsigned x - st) ltac:(lia) ltac:(lia) ltac:(replace (st + (bv_unsigned x - st)) with (bv_unsigned x) by lia; exact Ho)).
        - destruct FR as (F1 & F2 & F3). pose proof (u64_range (getr R0 8%bv)). pose proof (u64_range (getr R0 9%bv)). destruct CR0 as [_ _ Hretr _ _ _ _ _].
          unfold frame, cell8. split; [|split]; cellpeel.
        - apply defined_wbytes; exact DEF.
        - eapply eff_weaken; [eapply eff_trans; [exact EFF | |]|].
          + eapply eff_store with (F := fun a : Z => st + 88 <= a < st + 96); [|exact HMg]. intros x HF HW. apply HMw. intros Hx. apply HF. exact Hx.
          + intros a Ha. apply WIN. unfold W, W_of in Ha. cbn in Ha. unfold zwin. lia.
          + intros a Ha. exact Ha. }
      destruct (Z.eq_dec bc2 0) as [Hz | Hnz].
      -
        assert (Hbl0 : bl2 = 0) by (destruct (u_blive U) as [[_ H]|[H _]]; [exact H | exfalso; exact (H Hz)]).
        rewrite Hbl0 in *.
        xruns HR HK 100%nat STOPS (SCR [true] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. sc_so. exact HdefHO. }
        postrun.
        destruct (HMW _ eq_refl) as (HMw & HMg & AIw & FRw & DEFw & EFFw).
        apply (POST A). unfold ablock. rewrite (proj2 (Z.eqb_eq _ _) Hz), app_nil_r. constructor; try assumption.
        + rreg HR' 2%bv Q2. rreg HR' 8%bv Q8. pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl) as Qs.
          unfold base_ok. rewrite Q2, Q8, !Qs by inl. repeat split; try assumption.
          intros r Hr. rewrite Qs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
        + eapply eff_weaken; [exact EFFw|]. intros a [[Ho|Hb]|Hs]; [left; lia | right; exact Hb | left; lia].
        + apply defined_wbytes; exact ODEF.
      -
        assert (Hbl1 : 0 < bl2) by (exact (u_bl_lo U Hnz)).
        xruns HR HK 100%nat STOPS (SCR [false] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_so. exact HdefHO. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        set (Mw := wbytes M _ _).
        destruct (HMW Mw eq_refl) as (HMw & HMg & AIw & FRw & DEFw & EFFw).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 10%bv Gc10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
        assert (HinP : In (bl2, 8 * bc2) P2).
        { unfold P2, umap_blocks. destruct (Z.eqb_spec bc2 0); [lia|]. apply in_app_iff. left. left. reflexivity. }
        assert (Hin6 : In (bl2, 8 * bc2) (state_blocks c)) by (rewrite SB, !in_app_iff; do 1 right; left; exact HinP).
        assert (Hbs_sub : forall b', In b' BS2 -> In b' (P3 ++ P4 ++ P5 ++ P6)).
        { intros b' Hb'. unfold BS2, BS3, P3 in *. rewrite ?in_app_iff in Hb'. rewrite ?in_app_iff. pose proof (umap_blocks_members 24 bl3 bc3 ents3 b') as HP3. rewrite in_app_iff in HP3. tauto. }
        assert (Hnbs : ~ In bl2 (map fst (BS2 ++ nblocks 32 ents2))).
        { rewrite map_app, in_app_iff. intros [X|X].
          - apply in_map_iff in X. destruct X as (b' & Hbb & Hb').
            exact (ne_split _ _ (bl2, 8 * bc2) b' SB2 ltac:(apply in_app_iff; right; exact HinP) (Hbs_sub b' Hb') (eq_sym Hbb)).
          - unfold nblocks in X. rewrite map_map in X. cbn in X. apply in_map_iff in X. destruct X as ([p [k v]] & Hp & Hin). cbn in Hp. subst p.
            pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (u_node U bl2 k v Hin))))))))) Hnz) as Hap.
            unfold apart in Hap. lia. }
        assert (ROCw : img_ro_clear L Mw).
        { eapply (roc_of_eff A Mw _ _ EFFw SUB). intros a [[Ho|Hb]|Hr]; [left; lia | right; exact Hb | left; lia]. }
        eapply (del_call fx A Mw model Rc bl2 (8 * bc2) (sp - 32) M1_PC K AIw MS ROCw G1);
          [ apply bv_eq; vm_compute; reflexivity | unfold M1_PC; lia | exact G2
          | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16 | lia
          | rewrite Gs by inl; exact B3 | rewrite Gs by inl; exact B4 | exact Gc10
          | right; exact (d_live _ _ _ _ _ _ (bl2, 8 * bc2) D Hin6 Hnbs)
          | lia | lia
          | intros i Hi; apply DEFw; lia
          | intros a Ha; apply WIN; unfold zwin in *; lia | ].
        intros A' R' M' model' AI' MS' Hfs' Hfds' KEPT LDEL EFF1 DEF' WIN'.
        destruct (del_post _ _ A Mw model A' M' bl2 (8 * bc2) AIw FRw DEFw WIN EFFw LAP Hin6 LDEL EFF1 DEF' WIN')
          as (FR' & DEF2 & WIN2 & EFF2 & LAP2).
        apply (POST A'). unfold ablock. destruct (Z.eqb_spec bc2 0); [lia|]. constructor.
        + exact AI'. + exact MS'. + congruence. + congruence.
        + eapply base_kept; [|exact KEPT]. unfold base_ok. rewrite G2, G8, !Gs by inl. repeat split; try assumption.
          intros r Hr. rewrite Gs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
        + exact FR'. + exact DEF2. + exact WIN2.
        + eapply eff_weaken; [exact EFF2|].
          intros a [[[Ho|Hb]|Hs]|Hb]; [left; lia | right | left; lia | right].
          * destruct Hb as (b & Hb & Hba). exists b. split; [apply in_app_iff; left; exact Hb | exact Hba].
          * destruct Hb as (b & Hb & Hba). exists b. split; [apply in_app_iff; right; exact Hb | exact Hba].
        + exact LAP2.
        + intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]]; [exact (SUB b Hb) | exact Hin6].
        + eapply (odef_eff A A' Mw M' model); [exact AIw | exact EFF1 | intros a Ha; cbn beta in Ha; destruct (blk_range _ Hin6) as (_ & _ & Hbc); cbn in Hbc; lia | unfold Mw; apply defined_wbytes; exact ODEF].
    Qed.

    Lemma blkM1 : forall A M model R,
      dst 88 BS1 A M model R ->
      (forall A' M' model' R', dst 88 (BS1 ++ nblocks 24 ents1) A' M' model' R' -> srealizes SEGS (cfg fx R' A1_PC M' model') K) ->
      srealizes SEGS (cfg fx R M1_PC M model) K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLerr_rw fx A0 s R0 M0 model0 sp ret st c K CB SR ASP.
      intros A M model R D POST.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hstsp & Hsthi & Hstown).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds B FR DEF WIN EFF LAP SUB ODEF]. destruct B as (B2 & B3 & B4 & B8 & Bs).
      pose proof (sr_m1 _ _ _ _ _ _ _ SR) as U.
      pose proof (d_cell _ _ _ _ _ _ 64 8 (hdaddr ents1) D ltac:(replace (st + 64) with (st + 48 + 16) by lia; exact (h_p1 (u_hdr U))) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cp1.
      unfold cell8 in Cp1. pose proof (proj1 Cp1) as Hhdr.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 (sp - 32); Z_to_bv 64 st; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 (hdaddr ents1)]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (8%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.

      assert (HnP : forall p k v, In (p, (k, v)) ents1 -> In (p, 24) P1).
      { intros p k v Hin. unfold P1, umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin]. }
      assert (HnSB : forall p k v, In (p, (k, v)) ents1 -> In (p, 24) (state_blocks c)).
      { intros p k v Hin. rewrite SB, !in_app_iff. left; exact (HnP p k v Hin). }
      assert (Hbs_sub : forall b', In b' BS1 -> In b' (P2 ++ P3 ++ P4 ++ P5 ++ P6)).
      { intros b' Hb'. unfold BS1, BS2, BS3, P3, P2 in *. rewrite ?in_app_iff in Hb'. rewrite ?in_app_iff. pose proof (umap_blocks_members 24 bl3 bc3 ents3 b') as HP3. rewrite in_app_iff in HP3. pose proof (umap_blocks_members 32 bl2 bc2 ents2 b') as HP2. rewrite in_app_iff in HP2. tauto. }
      assert (Hnbs : forall p k v, In (p, (k, v)) ents1 -> ~ In p (map fst BS1)).
      { intros p k v Hin X. apply in_map_iff in X. destruct X as (b' & Hbb & Hb').
        exact (ne_split _ _ (p, 24) b' SB ltac:( exact (HnP p k v Hin)) (Hbs_sub b' Hb') (eq_sym Hbb)). }
      assert (Hcase : ents1 = [] \/ ents1 <> []) by (destruct ents1; [left; reflexivity | right; discriminate]).
      destruct Hcase as [He | Hne].
      -
        assert (Hz : hdaddr ents1 = 0) by (rewrite He; reflexivity). rewrite Hz in *.
        xruns HR HK 100%nat STOPS (SCR [true] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. }
        apply (POST A). rewrite He. cbn [nblocks map]. rewrite app_nil_r. constructor; try assumption.
        rreg HR' 2%bv Q2. rreg HR' 8%bv Q8. pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR' eq_refl) as Qs.
        unfold base_ok. rewrite Q2, Q8, !Qs by inl. repeat split; try assumption.
        intros r Hr. rewrite Qs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
      -
        assert (Hhd : 0 < hdaddr ents1).
        { destruct ents1 as [|[p0 [k0 v0]] rest0] eqn:He; [exfalso; exact (Hne eq_refl)|]. cbn.
          destruct (u_node U p0 k0 v0 ltac:(try rewrite He; left; reflexivity)) as (_ & Hp & _). lia. }
        xruns HR HK 100%nat STOPS (SCR [false] [EVar 40] []) 50%N.
        { split_scs; try sc_auto1. }
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        rreg HRc 2%bv Q2. rreg HRc 8%bv Q8. rreg HRc 10%bv Q10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Qs.
        assert (Bc : base_ok Rc).
        { unfold base_ok. rewrite Q2, Q8, !Qs by inl. repeat split; try assumption.
          intros r Hr. rewrite Qs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr. }
        destruct Bc as (Bc2 & Bc3 & Bc4 & Bc8 & Bcs).
        eapply (free_loop1 sp Rc Hsp16 Hsplo Hsphi Hspimg Bc2 Bc3 Bc4 Z 24 ents1 fx A M model Rc K Hne ltac:(lia) AI MS (d_roc _ _ _ _ _ _ D ltac:(lia))).
        + intros r Hr. reflexivity.
        + exact Q10.
        + intros p k v Hin. exact (d_live _ _ _ _ _ _ (p, 24) D (HnSB p k v Hin) (Hnbs p k v Hin)).
        + exact (u_nodup U).
        + eapply (chain_agree SEGS _ M0 M); [exact (u_chain U)|]. intros q kq vq Hin.
          destruct (u_node U q kq vq Hin) as (_ & Hq0 & Hq1 & _).
          split; [|lia]. eapply agree_on_sub; [exact (d_blk_agree _ _ _ _ _ _ (q, 24) D ltac:(lia) (HnSB q kq vq Hin) (Hnbs q kq vq Hin)) | cbn; lia | cbn; lia].
        + exact DEF.
        + exact WIN.
        +
          intros A' M' model' R' AI' MS' Hfs' Hfds' HP EFF1 LAP1 DEF' WIN'.
          assert (SUBn : forall b, In b (nblocks 24 ents1) -> In b (state_blocks c)).
          { intros b Hb. unfold nblocks in Hb. apply in_map_iff in Hb. destruct Hb as ([p [k v]] & <- & Hin). exact (HnSB p k v Hin). }
          destruct (loop_post _ BS1 A M A' M' (nodes_foot 24 ents1) (nblocks 24 ents1) FR DEF WIN EFF LAP SUBn) as (FR' & EFF2 & LAP2);
            [| exact EFF1 | unfold nblocks; rewrite map_map; exact LAP1 | exact WIN' |].
          { intros a (p & Hp & Hpa). apply in_map_iff in Hp. destruct Hp as ([p' kv] & Hpp & Hin). cbn in Hpp. subst p'.
            exists (p, 24). split; [| exact Hpa]. unfold nblocks. apply in_map_iff. exists (p, kv). split; [reflexivity | exact Hin]. }
          apply (POST A'). constructor.
          * exact AI'. * exact MS'. * congruence. * congruence.
          * unfold base_ok. rewrite !(HP _) by inl. repeat split; try assumption. intros r Hr. rewrite (HP r); [apply Bcs, Hr|].
            cbn in Hr. unfold PRES. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
          * exact FR'. * exact DEF'. * exact WIN'.
          * eapply eff_weaken; [exact EFF2|]. intros a [[Ho|Hb]|Hb]; [left; exact Ho | right | right].
            -- destruct Hb as (b & Hb & Hba). exists b. split; [apply in_app_iff; left; exact Hb | exact Hba].
            -- destruct Hb as (b & Hb & Hba). exists b. split; [apply in_app_iff; right; exact Hb | exact Hba].
          * exact LAP2.
          * intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (SUB b Hb) | exact (SUBn b Hb)].
          * eapply (odef_nodes A A' M M' model); [exact AI | exact EFF1 | exact HnSB | exact ODEF].
    Qed.

    Lemma BS0_members : forall b, In b BS0 <-> In b (state_blocks c).
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn A0 s R0 M0 model0 sp ret c CB.
      intros b. unfold BS0, BS1, BS2, BS3. rewrite SB. unfold P1, P2, P3.
      pose proof (umap_blocks_members 24 bl1 bc1 ents1 b) as HP1. pose proof (umap_blocks_members 32 bl2 bc2 ents2 b) as HP2.
      pose proof (umap_blocks_members 24 bl3 bc3 ents3 b) as HP3.
      rewrite !in_app_iff in HP1, HP2, HP3. rewrite !in_app_iff. tauto.
    Qed.

    Lemma finish : forall A' M' model' R' (F : Z -> Prop),
      ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model0 -> m_fds model' = m_fds model0 ->
      eff MI A0 A' M0 M' W F -> (forall a, F a -> (st <= a < st + 240) \/ inblk BS0 a) ->
      lapply (live MI A0) (map (fun b => LDel (fst b)) BS0) (live MI A') ->
      defined M' st 240 ->
      getr R' 1%bv = Z_to_bv 64 ret -> getr R' 2%bv = Z_to_bv 64 sp -> getr R' 3%bv = Z_to_bv 64 (ly_gp L) -> getr R' 4%bv = Z_to_bv 64 (ly_tp L) ->
      getr R' 8%bv = getr R0 8%bv -> getr R' 9%bv = getr R0 9%bv ->
      (forall r, In r [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R0 r) ->
      srealizes SEGS (cfg fx R' ret M' model') K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret st c K CB SR ASP CONT.
      intros A' M' model' R' F AI MS Hfs Hfds EF HF LAP ODEF' G1 G2 G3 G4 G8 G9 Gs.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hstsp & Hsthi & Hstown).
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      assert (HFS : forall a, F a -> state_foot st c a).
      { intros a Ha. destruct (HF a Ha) as [Ho | (b & Hb & Hba)]; [left; exact Ho | right].
        exists b. split; [apply BS0_members; exact Hb | exact Hba]. }
      apply (CONT A' R' M' model').
      - constructor; [exact AI | exact MS | exact Hfs | exact Hfds | |].
        + eapply (sx_inv_via_eff L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw s A0 A' M0 M' model0 W F);
            [exact (cb_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) | exact AI0 | exact EF
            | exact (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) | exact (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) | | unfold W; cbn; lia].
          intros a Ha Himg. pose proof (HLimg_lo a Himg) as Hlt.
          destruct (HFS a Ha) as [Ho | ([p n] & Hb & Hba)]; [lia|]. cbn in Hba.
          exact (live_offimg' A0 M0 model0 p n a AI0 (blocks_live _ Hb) Hba Himg).
        + intros r Hr. unfold callee_saved in Hr. cbn in Hr.
          repeat (destruct Hr as [<-|Hr]); try contradiction;
            first [ rewrite G1; symmetry; exact Hra | rewrite G2; symmetry; exact Hsp2 | rewrite G3; symmetry; exact Hgp | rewrite G4; symmetry; exact Htp
                  | rewrite G8; reflexivity | rewrite G9; reflexivity | apply Gs; inl ].
      - rewrite <- (map_map fst LDel). rewrite <- (map_map fst LDel) in LAP. eapply lapply_dels_equiv; [exact LAP|].
        intros q. rewrite !in_map_iff. split; intros (b & Hq & Hb); exists b; split; [exact Hq | apply BS0_members; exact Hb | exact Hq | apply BS0_members; exact Hb].
      - unfold STATE_DTOR_STACK. eapply eff_weaken; [exact EF | exact HFS].
      - exact ODEF'.
    Qed.

    Lemma blkA1 : forall A M model R,
      dst 88 (BS1 ++ nblocks 24 ents1) A M model R ->
      srealizes SEGS (cfg fx R A1_PC M model) K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret st c K CB SR ASP CONT.
      intros A M model R D.
      destruct SPF as (Hsp16 & Hsplo & Hsphi & Hspimg). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      destruct ASP as (Hstsp & Hsthi & Hstown).
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds B FR DEF WIN EFF LAP SUB ODEF]. destruct B as (B2 & B3 & B4 & B8 & Bs).
      pose proof (sr_m1 _ _ _ _ _ _ _ SR) as U.
      pose proof (d_cell _ _ _ _ _ _ 48 8 bl1 D (h_bl (u_hdr U)) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cbl.
      pose proof (d_cell _ _ _ _ _ _ 56 8 bc1 D ltac:(replace (st + 56) with (st + 48 + 8) by lia; exact (h_bc (u_hdr U))) ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Cbc.
      unfold cell8 in Cbl, Cbc. pose proof (proj1 Cbl) as Hblr. pose proof (proj1 Cbc) as Hbcr.
      assert (Hbcr2 : 0 <= bc1 <= 26339969) by (pose proof (u_bseq U) as HB; unfold BSEQ in HB; cbn in HB; lia).
      assert (HdefHO : defined M (st + 48) (Z.of_nat 8)) by (eapply (d_defined _ _ _ _ _ _ 48 _ D); cbn; lia).
      destruct FR as (F1 & F2 & F3). unfold cell8 in F1, F2, F3.
      pose proof (u64_range (getr R0 8%bv)) as Hr8. pose proof (u64_range (getr R0 9%bv)) as Hr9.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 (sp - 32); Z_to_bv 64 st; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                          Z_to_bv 64 bl1; Z_to_bv 64 bc1; Z_to_bv 64 ret; getr R0 8%bv; getr R0 9%bv]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (8%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M [KDisj (SA (EVar 34) 48) (ELit 8) (SA (EVar 33) 0) (ELit 32)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia]. }

      assert (HMW : forall Mw, Mw = wbytes M (Z_to_bv 64 (st + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
                (forall x : word, ~ (st + 48 <= bv_unsigned x < st + 56) -> Mw x = M x)
                /\ (forall x : word, M x <> None -> Mw x <> None)
                /\ ainv MI A Mw model /\ defined Mw (sp - 32 - DEL_STACK) (32 + DEL_STACK)
                /\ eff MI A0 A M0 Mw W (fun a => FK 88 (BS1 ++ nblocks 24 ents1) a \/ (st + 48 <= a < st + 56))).
      { intros Mw ->.
        assert (HMw : forall x : word, ~ (st + 48 <= bv_unsigned x < st + 56) -> wbytes M (Z_to_bv 64 (st + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)) x = M x).
        { intros x Hx. pose proof (u64_range x).
          rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMg : forall x : word, M x <> None -> wbytes M (Z_to_bv 64 (st + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)) x <> None)
          by (intros x Hx; apply wbytes_grows; exact Hx).
        split; [exact HMw|]. split; [exact HMg|]. split; [|split].
        - eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
          intros x Ho. apply HMw. intros Hx.
          exact (d_unowned _ _ _ _ _ _ D (bv_unsigned x - st) ltac:(lia) ltac:(lia) ltac:(replace (st + (bv_unsigned x - st)) with (bv_unsigned x) by lia; exact Ho)).
        - apply defined_wbytes; exact DEF.
        - eapply eff_weaken; [eapply eff_trans; [exact EFF | |]|].
          + eapply eff_store with (F := fun a : Z => st + 48 <= a < st + 56); [|exact HMg]. intros x HF HW. apply HMw. intros Hx. apply HF. exact Hx.
          + intros a Ha. apply WIN. unfold W, W_of in Ha. cbn in Ha. unfold zwin. lia.
          + intros a Ha. exact Ha. }

      assert (SCf : forall Mx, frame Mx -> forall off n e (w : word),
                 (off = 24 /\ e = EVar 42 /\ w = Z_to_bv 64 ret) \/ (off = 16 /\ e = EVar 43 /\ w = getr R0 8%bv) \/ (off = 8 /\ e = EVar 44 /\ w = getr R0 9%bv) ->
                 n = 8%nat -> sc_denot SEGS Mx E (SCReadBase (SA (EVar 33) off) n false e)).
      { intros Mx (Fa & Fb & Fc) off n e w Hc ->. unfold cell8 in Fa, Fb, Fc.
        destruct Hc as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]].
        - eapply (sc_read_cellw _ _ _ _ _ _ _ _ Fa); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; reflexivity].
        - eapply (sc_read_cellw _ _ _ _ _ _ _ _ Fb); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity].
        - eapply (sc_read_cellw _ _ _ _ _ _ _ _ Fc); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity]. }
      destruct (Z.eq_dec bc1 0) as [Hz | Hnz].
      -
        assert (Hbl0 : bl1 = 0) by (destruct (u_blive U) as [[_ H]|[H _]]; [exact H | exfalso; exact (H Hz)]).
        rewrite Hbl0 in *.
        xruns HR HK 100%nat STOPS (SCR [true] [EVar 40; EVar 42; EVar 43; EVar 44] []) 50%N.
        { split_scs; try sc_auto1; try (sc_so; exact HdefHO).
          all: eapply (SCf M ltac:(split; [exact F1 | split; [exact F2 | exact F3]])); [| reflexivity]; first [left; repeat split; reflexivity | right; left; repeat split; reflexivity | right; right; repeat split; reflexivity]. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
        destruct (HMW _ eq_refl) as (HMw & HMg & AIw & DEFw & EFFw).
        rreg HRr 1%bv G1. rreg HRr 2%bv G2. rreg HRr 8%bv G8. rreg HRr 9%bv G9.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Gs.

        eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ].
        { unfold RET_PC. norm_pc. stepjr F_667d4 D_667d4 (Z_to_bv 64 ret) ltac:(exact G1).
          change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl. }
        eapply (finish A _ model Rr _ AIw MS Hfs Hfds EFFw).
        + intros a [[Ho|Hb]|Hs]; [left; lia | right | left; lia]. destruct Hb as (b & Hb & Hba). exists b. split; [|exact Hba].
          unfold BS0. apply in_app_iff. left. exact Hb.
        + unfold BS0, ablock. rewrite (proj2 (Z.eqb_eq _ _) Hz), app_nil_r. exact LAP.
        + try unfold Mw. apply defined_wbytes. exact ODEF.
        + exact G1.
        + rewrite G2, w_add by lia. f_equal. lia.
        + rewrite Gs by inl. exact B3.
        + rewrite Gs by inl. exact B4.
        + rewrite G8. reflexivity.
        + rewrite G9. reflexivity.
        + intros r Hr. rewrite Gs; [apply Bs, Hr|]. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [inl|]). destruct Hr.
      -
        assert (Hbl1p : 0 < bl1) by (exact (u_bl_lo U Hnz)).
        xruns HR HK 100%nat STOPS (SCR [false] [EVar 40; EVar 41; EVar 42; EVar 43; EVar 44] []) 50%N.
        { split_scs; try sc_auto1; try (sc_so; exact HdefHO).
          all: eapply (SCf M ltac:(split; [exact F1 | split; [exact F2 | exact F3]])); [| reflexivity]; first [left; repeat split; reflexivity | right; left; repeat split; reflexivity | right; right; repeat split; reflexivity]. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
        set (Mw := wbytes M _ _).
        destruct (HMW Mw eq_refl) as (HMw & HMg & AIw & DEFw & EFFw).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 9%bv G9. rreg HRc 10%bv Gc10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
        assert (HinP : In (bl1, 8 * bc1) P1).
        { unfold P1, umap_blocks. destruct (Z.eqb_spec bc1 0); [lia|]. apply in_app_iff. left. left. reflexivity. }
        assert (Hin6 : In (bl1, 8 * bc1) (state_blocks c)) by (rewrite SB, !in_app_iff; left; exact HinP).
        assert (Hbs_sub : forall b', In b' BS1 -> In b' (P2 ++ P3 ++ P4 ++ P5 ++ P6)).
        { intros b' Hb'. unfold BS1, BS2, BS3, P3, P2 in *. rewrite ?in_app_iff in Hb'. rewrite ?in_app_iff.
          pose proof (umap_blocks_members 24 bl3 bc3 ents3 b') as HP3. rewrite in_app_iff in HP3.
          pose proof (umap_blocks_members 32 bl2 bc2 ents2 b') as HP2. rewrite in_app_iff in HP2. tauto. }
        assert (Hnbs : ~ In bl1 (map fst (BS1 ++ nblocks 24 ents1))).
        { rewrite map_app, in_app_iff. intros [X|X].
          - apply in_map_iff in X. destruct X as (b' & Hbb & Hb').
            exact (ne_split _ _ (bl1, 8 * bc1) b' SB ltac:(exact HinP) (Hbs_sub b' Hb') (eq_sym Hbb)).
          - unfold nblocks in X. rewrite map_map in X. cbn in X. apply in_map_iff in X. destruct X as ([p [k v]] & Hp & Hin). cbn in Hp. subst p.
            pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (u_node U bl1 k v Hin))))))))) Hnz) as Hap.
            unfold apart in Hap. lia. }
        assert (G2' : getr Rc 2%bv = Z_to_bv 64 sp) by (rewrite G2, w_add by lia; f_equal; lia).
        pose proof (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hwin0. unfold STATE_DTOR_STACK in Hwin0.
        assert (ROCw : img_ro_clear L Mw).
        { eapply (roc_of_eff A Mw _ _ EFFw SUB). intros a [[Ho|Hb]|Hr]; [left; lia | right; exact Hb | left; lia]. }
        eapply (del_call fx A Mw model Rc bl1 (8 * bc1) sp ret K AIw MS ROCw G1 Hret Hretr G2' Hsp16 Hsphi);
          [ rewrite Gs by inl; exact B3 | rewrite Gs by inl; exact B4 | exact Gc10
          | right; exact (d_live _ _ _ _ _ _ (bl1, 8 * bc1) D Hin6 Hnbs)
          | lia | lia
          | intros i Hi; replace (sp - DEL_STACK + i) with (sp - 32 - DEL_STACK + (32 + i)) by lia; apply DEFw; lia
          | intros a Ha; apply WIN; unfold zwin in *; lia | ].
        intros A' R' M' model' AI' MS' Hfs' Hfds' KEPT LDEL EFF1 DEF' WIN'.
        destruct (blk_range _ Hin6) as (Hn0 & Hp0 & Hpc). cbn in Hn0, Hp0, Hpc.
        assert (WINf : forall a, zwin (sp - 32 - DEL_STACK) sp a -> ~ owned MI A' a).
        { intros a Ha Ho. destruct (ef_own _ _ _ _ _ _ _ _ _ EFF1 a Ho) as [Ho0|[[_ [_ Hm]]|Hq]].
          - exact (WIN a Ha Ho0).
          - exact (DEFw (a - (sp - 32 - DEL_STACK)) ltac:(unfold zwin in Ha; lia) ltac:(replace (sp - 32 - DEL_STACK + (a - (sp - 32 - DEL_STACK))) with a by lia; exact Hm)).
          - cbn beta in Hq. unfold zwin in Ha. lia. }
        eapply (finish A' M' model' R' _ AI' MS' ltac:(congruence) ltac:(congruence)).
        + eapply eff_trans; [exact EFFw | eapply eff_widen; [exact EFF1|] |].
          * intros a Ha. unfold W, W_of in *. cbn in *. lia.
          * intros a Ha. apply WINf. unfold W, W_of in Ha. cbn in Ha. unfold zwin. lia.
        + intros a [[[Ho|Hb]|Hs]|Hb]; [left; lia | right | left; lia | right].
          * destruct Hb as (b & Hb & Hba). exists b. split; [|exact Hba]. unfold BS0. apply in_app_iff. left. exact Hb.
          * exists (bl1, 8 * bc1). split; [|exact Hb]. unfold BS0, ablock. destruct (Z.eqb_spec bc1 0); [lia|]. apply in_app_iff. right. left. reflexivity.
        + unfold BS0, ablock. destruct (Z.eqb_spec bc1 0); [lia|]. rewrite map_app. eapply lapply_app; [exact LAP|].
          cbn. exists (live MI A'). split; [exact LDEL | reflexivity].
        + eapply (odef_eff A A' Mw M' model); [exact AIw | exact EFF1 | intros a Ha; cbn beta in Ha; destruct (blk_range _ Hin6) as (_ & _ & Hbc); cbn in Hbc; lia | unfold Mw; apply defined_wbytes; exact ODEF].
        + rewrite (KEPT 1%bv) by inl. exact G1.
        + rewrite (KEPT 2%bv) by inl. exact G2'.
        + rewrite (KEPT 3%bv) by inl. rewrite Gs by inl. exact B3.
        + rewrite (KEPT 4%bv) by inl. rewrite Gs by inl. exact B4.
        + rewrite (KEPT 8%bv) by inl. rewrite G8. reflexivity.
        + rewrite (KEPT 9%bv) by inl. rewrite G9. reflexivity.
        + intros r Hr. rewrite (KEPT r); [rewrite Gs; [apply Bs, Hr|]|]; cbn in Hr; unfold callee_saved; repeat (destruct Hr as [<-|Hr]; [inl|]); destruct Hr.
    Qed.

    Theorem dtor_correct : srealizes SEGS (cfg fx R0 SDT M0 model0) K.
    Proof using AC L MI ST DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret st c K CB H10 SR ASP CONT.
      apply blkP. intros M1 R1 D1 G10.
      apply (blkV3 A0 M1 model0 R1 D1 G10). intros A2 M2 model2 R2 D2.
      apply (blkV2 _ _ _ _ D2). intros A3 M3 model3 R3 D3.
      apply (blkV1 _ _ _ _ D3). intros A4 M4 model4 R4 D4.
      apply (blkM3 _ _ _ _ D4). intros A5 M5 model5 R5 D5.
      apply (blkA3 _ _ _ _ D5). intros A6 M6 model6 R6 D6.
      apply (blkM2 _ _ _ _ D6). intros A7 M7 model7 R7 D7.
      apply (blkA2 _ _ _ _ D7). intros A8 M8 model8 R8 D8.
      apply (blkM1 _ _ _ _ D8). intros A9 M9 model9 R9 D9.
      exact (blkA1 _ _ _ _ D9).
    Qed.
  End Main.

  Definition state_dtor_stmt' (hc : hconsts) : Prop :=
    forall (fx : FPState) (A : AS MI) (s : LibIface.SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
           (sp ret st : Z) (c : stateC) (K : TSet),
      callB MI ST A s R M model sp ret (STATE_DTOR_STACK DEL_STACK) ->
      getr R 10%bv = Z_to_bv 64 st ->
      state_rep MI A M st c -> above_sp MI A sp st 240 ->
      (forall A' R' M' model',
          retB MI ST A' s R R' M' model model' ->
          lapply (live MI A) (map (fun b => LDel (fst b)) (state_blocks c)) (live MI A') ->
          eff MI A A' M M' (sp - STATE_DTOR_STACK DEL_STACK, sp) (state_foot st c) ->
          defined M' st 240 ->
          srealizes SEGS (cfg fx R' ret M' model') K) ->
      srealizes SEGS (cfg fx R (hc_state_dtor hc) M model) K.
  Theorem state_dtor_spec' : state_dtor_stmt' HConstsS1.hc.
  Proof using AC L MI ST DEL_STACK DEL_STACK_nn DEL HLdel HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw.
    intros fx A s R M model sp ret st c K CB H10 SR ASP CONT.
    eapply dtor_correct; eassumption.
  Qed.

End Dtor.
