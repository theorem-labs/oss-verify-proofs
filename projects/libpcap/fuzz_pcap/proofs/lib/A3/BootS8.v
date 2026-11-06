(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesLibE BackingAlgebra. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanKnow. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodesDrive AsanHeapKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanMemIsZero. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanMemIsZero.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKn2__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootArith__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKn2__Lib.AsanBootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4f__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn7a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS3 BootS4 BootS5 BootS6 BootS7. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4a__A3.BootKn4a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn6a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn7a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn8a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS7.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots8_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).




(* [comment removed for export] *)
Definition L22 : ledger := lgrant L21 60 4096.
Definition L23 : ledger := lgrant L22 61 4096.
Definition L24 : ledger := lpop L23.
Lemma DS_E14_eq : DS_std L21 = DS_E14. Proof. reflexivity. Qed.
Lemma DS_E15_eq : DS_std L22 = DS_E15. Proof. reflexivity. Qed.
Lemma L22_ext : l_maps L22 = [(EVar 60, 4096); (EVar 46, 4096)] ++ l_maps L20. Proof. reflexivity. Qed.
Lemma L23_ext : l_maps L23 = [(EVar 61, 4096); (EVar 60, 4096); (EVar 46, 4096)] ++ l_maps L20. Proof. reflexivity. Qed.
Lemma L24_maps : l_maps L24 = l_maps L22. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition LZ24 (p8 sb p10 p15 : word) : list (word * word) := maps_subtract (LZ18 p8 sb p10) (bv_unsigned p15) (bv_unsigned p15 + 4096).
Definition SR24 : list expr := sr_upd SR_E16 10 (ELit 0).
Definition KN24 : list kentry := Eval vm_compute in (kn_keep MUnmap KN_E16 KN_E16 (EVar 61) 0 (ELit 4096)).
Lemma KN24_eq : kn_keep MUnmap KN_E16 KN_E16 (EVar 61) 0 (ELit 4096) = KN24. Proof. vmeq_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rg_block_sc VI VE HB HK RUN CAR SCT :=
  lazymatch type of VE with valid_entry _ (mkEntry ?sp ?brk ?mbase ?draw) ?inp =>
    let HR := fresh "HR" in let HKN := fresh "HKN" in let HA := fresh "HA" in let HZ := fresh "HZ" in
    let HM := fresh "HM" in let F := fresh "F" in let HMO := fresh "HMO" in let RG := fresh "RG" in
    let HT := fresh "HT" in let Hcl := fresh "Hcl" in let Ht := fresh "Ht" in let HLZ := fresh "HLZ" in
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht];
    let HH := fresh "HH" in let Hwx := fresh "Hwx" in let HAW := fresh "HAW" in let Hh := fresh "Hh" in let HL := fresh "HL" in
    pose proof (rg_off _ _ _ _ _ _ _ RG) as HH; pose proof wx_nowrap as Hwx; pose proof (rg_awf _ _ _ _ _ _ _ RG) as HAW;
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh;
    pose proof (rg_cover _ _ _ _ _ _ _ RG) as HL;
    run_block_K HR HKN HM HL Hh HH Hwx HAW RUN CAR;
    first
    [ lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ =>
      let body := eval unfold m in m in
      lazymatch body with munrestrict ?H ?M (mem_denot (EB _ _ _ ?a ?tid ?c ?pl ?js) _ ?lg) =>
        lazymatch type of F with mfacts _ _ _ _ _ _ _ ?L _ =>
          lazymatch type of HZ with hf_ok _ _ ?hc =>
            destruct (frame_blockS sp brk mbase draw inp VI VE H a tid c pl js M lg hc (lows_of L) ltac:(vmeq_refl)
                        (lows_of_ok sp _ L HMO) (rg_above _ _ _ _ _ _ _ RG) HA HZ) as [HA0 HZ0];
            subst m
          end end end end;
      apply HK; constructor; try assumption;
      [ erewrite sbm_lazy by eassumption; exact HLZ | eapply mfacts_sbm; eassumption | eapply regime_ok_sbm; eassumption]
    | cbn [sc_denot]; SCT ]
  end.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let usp := bv_unsigned sp.

  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).
  #[local] Notation at_E14' := (at_E14 sp brk mbase draw lim inp).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s8_e14 : forall a tid c pl p8 sb p10 p12 js R M mdl K, 2 ^ 25 <= lim -> length js = 44%nat ->
    at_E14' a tid c pl p8 sb p10 p12 js R M mdl ->
    (forall p14 R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl (js ++ [p14]) SR22 KN22 L22 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 js R M mdl K Hlim Hjs (HB & Hsb & E28 & E29 & E36 & E38) HK.
    assert (LEN : length (VB' a tid c pl js) = 60%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    pose proof (p12_factsG sp brk mbase draw lim inp L21 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L21_ext HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (shk_facts sp (SA16 sp brk mbase draw inp VI VE) SLo SHi) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & _).
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E14 KN_E14 L21 (hc6 p8 p10) (LZ18 p8 sb p10) 4096 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - cbn [l_eager L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit A_bytes A8 A7 A5 fst snd]. change (page_round_up_Z 4096) with 4096.
      destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia.
    - cbn [l_maps L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit gws]. change (page_round_up_Z 4096) with 4096. unfold N_PA, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE, IMG_HI, stack_max_size. lia.
    - intros p R' M' mdl' HB'. rewrite <- fetch_internal_mmap_ret_prev. apply (HK p). unfold SR22, L22.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_E14_eq, KN22_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s8_b22 : forall a tid c pl js p8 sb p10 p12 R M mdl K, bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 29 = sb ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR22 KN22 L22 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E15 KN_E15 L22 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hsb E28 E29 HB HK.
    rg_block VI VE HB HK run22L_eq car22L_eq.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s8_e15 : forall a tid c pl js p8 sb p10 p12 R M mdl K, 2 ^ 25 <= lim -> length js = 45%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E15 KN_E15 L22 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall p15 R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl (js ++ [p15]) SR23 KN23 L23 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 61%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    pose proof (p12_factsG sp brk mbase draw lim inp L22 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L22_ext HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (shk_facts sp (SA16 sp brk mbase draw inp VI VE) SLo SHi) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & _).
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E15 KN_E15 L22 (hc6 p8 p10) (LZ18 p8 sb p10) 4096 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - cbn [l_eager L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit A_bytes A8 A7 A5 fst snd]. change (page_round_up_Z 4096) with 4096.
      destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia.
    - cbn [l_maps L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit gws]. change (page_round_up_Z 4096) with 4096. unfold N_PA, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE, IMG_HI, stack_max_size. lia.
    - intros p R' M' mdl' HB'. rewrite <- fetch_internal_mmap_ret_prev. apply (HK p). unfold SR23, L23.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_E15_eq, KN23_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s8_b23a : forall a tid c pl js p8 sb p10 p12 R M mdl K,
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR23 KN23 L23 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR23a KN23a L23 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_tlsvec_ld) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 R M mdl K HB HK. rg_block VI VE HB HK run23a_eq car23a_eq. Qed.

  #[using="Type"] Theorem s8_merge : forall a tid c pl js p8 sb p10 p12 R M mdl,
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR23a KN23a L23 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR23a KN23m L23 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl HB. rewrite <- KN23m_eq. unfold merge23.
    eapply bootS_reknow; [exact HB | auto |]. intros HKN.
    apply kn_merge8_sound; [exact (proj2 merge23_ok)|]. apply kn_merge8_sound; [exact (proj1 merge23_ok)|]. exact HKN.
  Qed.

  (* [comment removed for export] *)
  Definition at_E16 (a tid c : word) (pl : placements) (p8 sb p10 p12 : word) (js : list word) R M mdl : Prop :=
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E16 KN_E16 L23 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12.

  #[using="VI VE"] Theorem s8_b23b : forall a tid c pl js p8 sb p10 p12 R M mdl K, bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 29 = sb -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR23a KN23m L23 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', at_E16 a tid c pl p8 sb p10 p12 js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_munmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_tlsvec_ld) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hsb E28 E29 E36 E38 HB HK.
    assert (HK' : forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E16 KN_E16 L23 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_munmap_ecall) M' ROM) mdl') K).
    { intros R' M' mdl' HB'. apply HK. split; [exact HB' | repeat split; assumption]. }
    clear HK. rg_block VI VE HB HK' run23b_eq car23b_eq.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma fetch_internal_munmap_ecall : fetch_word SEGS (Z_to_bv 64 A_internal_munmap_ecall) = Some ECALLW.
  Proof. vmeq_refl. Qed.

  (* [comment removed for export] *)
  Definition at_E16r (a tid c : word) (pl : placements) (p8 sb p10 p12 p15 : word) (js : list word) R M mdl : Prop :=
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR24 KN24 L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R M mdl /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12
    /\ (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15).   (* [comment removed for export] *)

  #[using="VI VE usp"] Theorem s8_e16 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K,
    ev (EB' a tid c pl js) 61 = p15 ->
    at_E16 a tid c pl p8 sb p10 p12 js R M mdl ->
    (forall R' M' mdl', at_E16r a tid c pl p8 sb p10 p12 p15 js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_munmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_munmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K E61 (HB & Hsb & E28 & E29 & E36 & E38) HK.
    pose proof (p12_factsG sp brk mbase draw lim inp L23 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L23_ext HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (p8_factsG sp brk mbase draw lim inp L23 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L23_ext HB E28) as (P1 & P2 & P3).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (shk_facts sp (SA16 sp brk mbase draw inp VI VE) SLo SHi) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11).
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    (* [comment removed for export] *)
    assert (AP15 : Forall (fun q => bv_unsigned p15 + 4096 <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned p15)
                          (dl (EB' a tid c pl js) ([(EVar 60, 4096); (EVar 46, 4096)] ++ l_maps L20))).
    { destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP.
      rewrite L23_ext in AP. cbn [dl List.map fst snd ivs_apart app] in AP. destruct AP as [AP _].
      change (edenot (EB' a tid c pl js) (EVar 61)) with (ev (EB' a tid c pl js) 61) in AP. rewrite E61, u_small in AP by lia. exact AP. }
    unfold L20, L19, L18, L17, L16, L15, L13, L_E6, lgrant, lgrant_nr, lcommit in AP15. cbn [l_maps dl List.map fst snd app] in AP15.
    change (edenot (EB' a tid c pl js) (EVar 28)) with (ev (EB' a tid c pl js) 28) in AP15.
    change (edenot (EB' a tid c pl js) (EVar 36)) with (ev (EB' a tid c pl js) 36) in AP15. rewrite E28, E36 in AP15.
    repeat (apply Forall_cons_iff in AP15 as [?X AP15]); cbn [fst snd edenot] in *.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE, N_PA, SHB_HI, stack_max_size in *. rewrite !u_small in X3, X4 by lia. rewrite !u_small in X7, X8, X9 by lia.
    eapply (bs_munmap_hd sp brk mbase draw lim inp VI VE (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E16 KN_E16 L23 (hc6 p8 p10) (LZ18 p8 sb p10)
              R M mdl 61 4096 A_internal_munmap_ecall _ ECALLW K HB fetch_internal_munmap_ecall is_ecall_ECALLW).
    - unfold A_internal_munmap_ecall. lia.
    - unfold A_internal_munmap_ecall. lia.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - reflexivity.
    - reflexivity.
    - (* [comment removed for export] *)
      intros x Hx. rewrite E61 in Hx. unfold H8, H7, H6, H5, H4, H3.
      apply hcut_false_of. apply hcut_false_of. unfold hjoin. apply orb_false_intro.
      + apply hcut_false_of. apply hcut_false_of. apply orb_false_intro.
        * apply H2_out. unfold SHB_LO, SHB_HI. clear - Hx X7 X8 X9. lia.   (* [comment removed for export] *)
        * unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE. apply andb_false_iff. destruct X4 as [X4|X4]; [left; apply Z.leb_gt; clear - Hx X4; lia | right; apply Z.ltb_ge; clear - Hx X4; lia].
      + unfold N_PA. apply andb_false_iff. destruct X3 as [X3|X3]; [left; apply Z.leb_gt; clear - Hx X3; lia | right; apply Z.ltb_ge; clear - Hx X3; lia].
    - (* [comment removed for export] *)
      unfold hf_inmaps, hc6, hc3, HC5, lpop. rewrite L23_ext. cbn [List.tl app l_maps].
      repeat constructor.
      + exists (EVar 36, N_PA). split; [cbn [List.tl app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]; repeat (try (left; reflexivity); right)|]. cbn [fst snd]. change (edenot _ (EVar 36)) with (ev (EB' a tid c pl js) 36). rewrite E36. unfold N_PA. lia.
      + exists (EVar 28, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE). split; [cbn [List.tl app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]; repeat (try (left; reflexivity); right)|]. cbn [fst snd]. change (edenot _ (EVar 28)) with (ev (EB' a tid c pl js) 28). rewrite E28. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE. lia.
      + exists (ELit 0x2008fff7000, 0xdfff0001000). split; [cbn [List.tl app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]; repeat (try (left; reflexivity); right)|]. cbn [fst snd edenot]. rewrite u_small by lia. unfold SHB_HI. lia.
      + exists (ELit 0x7fff7000, 2 ^ 28). split; [cbn [List.tl app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]; repeat (try (left; reflexivity); right)|]. cbn [fst snd edenot]. rewrite u_small by lia. unfold SHB_LO. lia.
    - cbn [app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]. repeat (try (left; reflexivity); right).
    - cbn [app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]. repeat (try (left; reflexivity); right).
    - cbn [app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]. repeat (try (left; reflexivity); right).
    - intros R' mdl' HB'. unfold A_internal_munmap_ret. change (426624 + 4) with 426628. hnf.
      replace (Z_to_bv 64 A_internal_munmap_ret) with (Z_to_bv 64 (A_internal_munmap_ecall + 4)) in HK by reflexivity.
      apply HK. split; [| split; [assumption | split; [assumption | split; [assumption | split; [assumption | split; [assumption | unfold SHB_HI; lia]]]]]].
      unfold SR24, L24, LZ24. rewrite <- KN24_eq. rewrite <- E61. exact HB'.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem boot_s8 : forall a tid c pl p8 sb p10 p12 js R M mdl K, 2 ^ 25 <= lim -> length js = 44%nat ->
    at_E14' a tid c pl p8 sb p10 p12 js R M mdl ->
    (forall p14 p15 R' M' mdl',
       at_E16r a tid c pl p8 sb p10 p12 p15 ((js ++ [p14]) ++ [p15]) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_munmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 js R M mdl K Hlim Hjs HE HK. pose proof HE as (_ & Hsb & E28 & E29 & E36 & E38).
    apply (s8_e14 a tid c pl p8 sb p10 p12 js R M mdl K Hlim Hjs HE). intros p14 R0 M0 m0 H0.
    set (js1 := js ++ [p14]) in *.
    assert (L1 : length js1 = 45%nat) by (unfold js1; rewrite length_app, Hjs; reflexivity).
    assert (FX : forall ks, ev (EB' a tid c pl (js1 ++ ks)) 28 = p8 /\ ev (EB' a tid c pl (js1 ++ ks)) 29 = sb
                            /\ ev (EB' a tid c pl (js1 ++ ks)) 36 = p10 /\ ev (EB' a tid c pl (js1 ++ ks)) 38 = p12).
    { intros ks. unfold js1. rewrite <- app_assoc, !ev_EB_app by (rewrite Hjs; lia). repeat split; assumption. }
    destruct (FX []) as (F28 & F29 & F36 & F38). rewrite app_nil_r in F28, F29, F36, F38.
    apply (s8_b22 a tid c pl js1 p8 sb p10 p12 R0 M0 m0 K Hsb F28 F29 H0). intros R1 M1 m1 H1.
    apply (s8_e15 a tid c pl js1 p8 sb p10 p12 R1 M1 m1 K Hlim L1 F28 F38 H1). intros p15 R2 M2 m2 H2'.
    destruct (FX [p15]) as (G28 & G29 & G36 & G38).
    assert (G61 : ev (EB' a tid c pl (js1 ++ [p15])) 61 = p15).
    { replace 61%nat with (16 + 45)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 45), app_nth2, L1 by lia. reflexivity. }
    apply (s8_b23a _ _ _ _ _ _ _ _ _ _ _ _ K H2'). intros R3 M3 m3 H3'.
    pose proof (s8_merge _ _ _ _ _ _ _ _ _ _ _ _ H3') as H4'.
    apply (s8_b23b _ _ _ _ _ _ _ _ _ _ _ _ K Hsb G28 G29 G36 G38 H4'). intros R5 M5 m5 H5'.
    apply (s8_e16 a tid c pl _ p8 sb p10 p12 p15 R5 M5 m5 K G61 H5'). intros R6 M6 m6 H6'.
    exact (HK p14 p15 R6 M6 m6 H6').
  Qed.
End Theorems.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn3c__B3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS5 BootS6 BootS7.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanMemIsZero.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKn2__Lib.AsanBootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn4a. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn6a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn7a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn8a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS4.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS7.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots8_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).




(* [comment removed for export] *)
Definition L22 : ledger := lgrant L21 60 4096.
Definition L23 : ledger := lgrant L22 61 4096.
Definition L24 : ledger := lpop L23.
Lemma DS_E14_eq : DS_std L21 = DS_E14. Proof. reflexivity. Qed.
Lemma DS_E15_eq : DS_std L22 = DS_E15. Proof. reflexivity. Qed.
Lemma L22_ext : l_maps L22 = [(EVar 60, 4096); (EVar 46, 4096)] ++ l_maps L20. Proof. reflexivity. Qed.
Lemma L23_ext : l_maps L23 = [(EVar 61, 4096); (EVar 60, 4096); (EVar 46, 4096)] ++ l_maps L20. Proof. reflexivity. Qed.
Lemma L24_maps : l_maps L24 = l_maps L22. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition LZ24 (p8 sb p10 p15 : word) : list (word * word) := maps_subtract (LZ18 p8 sb p10) (bv_unsigned p15) (bv_unsigned p15 + 4096).
Definition SR24 : list expr := sr_upd SR_E16 10 (ELit 0).
Definition KN24 : list kentry := Eval vm_compute in (kn_keep MUnmap KN_E16 KN_E16 (EVar 61) 0 (ELit 4096)).
Lemma KN24_eq : kn_keep MUnmap KN_E16 KN_E16 (EVar 61) 0 (ELit 4096) = KN24. Proof. vmeq_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rg_block_sc VI VE HB HK RUN CAR SCT :=
  lazymatch type of VE with valid_entry _ (mkEntry ?sp ?brk ?mbase ?draw) ?inp =>
    let HR := fresh "HR" in let HKN := fresh "HKN" in let HA := fresh "HA" in let HZ := fresh "HZ" in
    let HM := fresh "HM" in let F := fresh "F" in let HMO := fresh "HMO" in let RG := fresh "RG" in
    let HT := fresh "HT" in let Hcl := fresh "Hcl" in let Ht := fresh "Ht" in let HLZ := fresh "HLZ" in
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht];
    let HH := fresh "HH" in let Hwx := fresh "Hwx" in let HAW := fresh "HAW" in let Hh := fresh "Hh" in let HL := fresh "HL" in
    pose proof (rg_off _ _ _ _ _ _ _ RG) as HH; pose proof wx_nowrap as Hwx; pose proof (rg_awf _ _ _ _ _ _ _ RG) as HAW;
    pose proof (mf_halted _ _ _ _ _ _ _ _ _ F) as Hh;
    pose proof (rg_cover _ _ _ _ _ _ _ RG) as HL;
    run_block_K HR HKN HM HL Hh HH Hwx HAW RUN CAR;
    first
    [ lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ =>
      let body := eval unfold m in m in
      lazymatch body with munrestrict ?H ?M (mem_denot (EB _ _ _ ?a ?tid ?c ?pl ?js) _ ?lg) =>
        lazymatch type of F with mfacts _ _ _ _ _ _ _ ?L _ =>
          lazymatch type of HZ with hf_ok _ _ ?hc =>
            destruct (frame_blockS sp brk mbase draw inp VI VE H a tid c pl js M lg hc (lows_of L) ltac:(vmeq_refl)
                        (lows_of_ok sp _ L HMO) (rg_above _ _ _ _ _ _ _ RG) HA HZ) as [HA0 HZ0];
            subst m
          end end end end;
      apply HK; constructor; try assumption;
      [ erewrite sbm_lazy by eassumption; exact HLZ | eapply mfacts_sbm; eassumption | eapply regime_ok_sbm; eassumption]
    | cbn [sc_denot]; SCT ]
  end.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let usp := bv_unsigned sp.

  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).
  #[local] Notation at_E14' := (at_E14 sp brk mbase draw lim inp).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s8_e14 : forall a tid c pl p8 sb p10 p12 js R M mdl K, 2 ^ 25 <= lim -> length js = 44%nat ->
    at_E14' a tid c pl p8 sb p10 p12 js R M mdl ->
    (forall p14 R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl (js ++ [p14]) SR22 KN22 L22 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 js R M mdl K Hlim Hjs (HB & Hsb & E28 & E29 & E36 & E38) HK.
    assert (LEN : length (VB' a tid c pl js) = 60%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    pose proof (p12_factsG sp brk mbase draw lim inp L21 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L21_ext HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (shk_facts sp (SA16 sp brk mbase draw inp VI VE) SLo SHi) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & _).
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E14 KN_E14 L21 (hc6 p8 p10) (LZ18 p8 sb p10) 4096 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - cbn [l_eager L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit A_bytes A8 A7 A5 fst snd]. change (page_round_up_Z 4096) with 4096.
      destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia.
    - cbn [l_maps L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit gws]. change (page_round_up_Z 4096) with 4096. unfold N_PA, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, IMG_HI, stack_max_size. lia.
    - intros p R' M' mdl' HB'. rewrite <- fetch_internal_mmap_ret_prev. apply (HK p). unfold SR22, L22.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_E14_eq, KN22_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s8_b22 : forall a tid c pl js p8 sb p10 p12 R M mdl K, bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 29 = sb ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR22 KN22 L22 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E15 KN_E15 L22 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hsb E28 E29 HB HK.
    rg_block VI VE HB HK run22L_eq car22L_eq.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s8_e15 : forall a tid c pl js p8 sb p10 p12 R M mdl K, 2 ^ 25 <= lim -> length js = 45%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E15 KN_E15 L22 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall p15 R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl (js ++ [p15]) SR23 KN23 L23 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 61%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    pose proof (p12_factsG sp brk mbase draw lim inp L22 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L22_ext HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (shk_facts sp (SA16 sp brk mbase draw inp VI VE) SLo SHi) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & _).
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E15 KN_E15 L22 (hc6 p8 p10) (LZ18 p8 sb p10) 4096 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - cbn [l_eager L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit A_bytes A8 A7 A5 fst snd]. change (page_round_up_Z 4096) with 4096.
      destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia.
    - cbn [l_maps L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit gws]. change (page_round_up_Z 4096) with 4096. unfold N_PA, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, IMG_HI, stack_max_size. lia.
    - intros p R' M' mdl' HB'. rewrite <- fetch_internal_mmap_ret_prev. apply (HK p). unfold SR23, L23.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_E15_eq, KN23_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s8_b23a : forall a tid c pl js p8 sb p10 p12 R M mdl K,
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR23 KN23 L23 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR23a KN23a L23 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_tlsvec_ld) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 R M mdl K HB HK. rg_block VI VE HB HK run23a_eq car23a_eq. Qed.

  #[using="Type"] Theorem s8_merge : forall a tid c pl js p8 sb p10 p12 R M mdl,
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR23a KN23a L23 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR23a KN23m L23 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl HB. rewrite <- KN23m_eq. unfold merge23.
    eapply bootS_reknow; [exact HB | auto |]. intros HKN.
    apply kn_merge8_sound; [exact (proj2 merge23_ok)|]. apply kn_merge8_sound; [exact (proj1 merge23_ok)|]. exact HKN.
  Qed.

  (* [comment removed for export] *)
  Definition at_E16 (a tid c : word) (pl : placements) (p8 sb p10 p12 : word) (js : list word) R M mdl : Prop :=
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E16 KN_E16 L23 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12.

  #[using="VI VE"] Theorem s8_b23b : forall a tid c pl js p8 sb p10 p12 R M mdl K, bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 29 = sb -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR23a KN23m L23 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', at_E16 a tid c pl p8 sb p10 p12 js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_munmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_tlsvec_ld) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hsb E28 E29 E36 E38 HB HK.
    assert (HK' : forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E16 KN_E16 L23 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_munmap_ecall) M' ROM) mdl') K).
    { intros R' M' mdl' HB'. apply HK. split; [exact HB' | repeat split; assumption]. }
    clear HK. rg_block VI VE HB HK' run23b_eq car23b_eq.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma fetch_internal_munmap_ecall : fetch_word SEGS (Z_to_bv 64 A_internal_munmap_ecall) = Some ECALLW.
  Proof. vmeq_refl. Qed.

  (* [comment removed for export] *)
  Definition at_E16r (a tid c : word) (pl : placements) (p8 sb p10 p12 p15 : word) (js : list word) R M mdl : Prop :=
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR24 KN24 L24 (hc6 p8 p10) (LZ24 p8 sb p10 p15) R M mdl /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12
    /\ (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15).   (* [comment removed for export] *)

  #[using="VI VE usp"] Theorem s8_e16 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K,
    ev (EB' a tid c pl js) 61 = p15 ->
    at_E16 a tid c pl p8 sb p10 p12 js R M mdl ->
    (forall R' M' mdl', at_E16r a tid c pl p8 sb p10 p12 p15 js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_munmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_munmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K E61 (HB & Hsb & E28 & E29 & E36 & E38) HK.
    pose proof (p12_factsG sp brk mbase draw lim inp L23 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L23_ext HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (p8_factsG sp brk mbase draw lim inp L23 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L23_ext HB E28) as (P1 & P2 & P3).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (shk_facts sp (SA16 sp brk mbase draw inp VI VE) SLo SHi) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11).
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    (* [comment removed for export] *)
    assert (AP15 : Forall (fun q => bv_unsigned p15 + 4096 <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned p15)
                          (dl (EB' a tid c pl js) ([(EVar 60, 4096); (EVar 46, 4096)] ++ l_maps L20))).
    { destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP.
      rewrite L23_ext in AP. cbn [dl List.map fst snd ivs_apart app] in AP. destruct AP as [AP _].
      change (edenot (EB' a tid c pl js) (EVar 61)) with (ev (EB' a tid c pl js) 61) in AP. rewrite E61, u_small in AP by lia. exact AP. }
    unfold L20, L19, L18, L17, L16, L15, L13, L_E6, lgrant, lgrant_nr, lcommit in AP15. cbn [l_maps dl List.map fst snd app] in AP15.
    change (edenot (EB' a tid c pl js) (EVar 28)) with (ev (EB' a tid c pl js) 28) in AP15.
    change (edenot (EB' a tid c pl js) (EVar 36)) with (ev (EB' a tid c pl js) 36) in AP15. rewrite E28, E36 in AP15.
    repeat (apply Forall_cons_iff in AP15 as [?X AP15]); cbn [fst snd edenot] in *.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, N_PA, SHB_HI, stack_max_size in *. rewrite !u_small in X3, X4 by lia. rewrite !u_small in X7, X8, X9 by lia.
    eapply (bs_munmap_hd sp brk mbase draw lim inp VI VE (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E16 KN_E16 L23 (hc6 p8 p10) (LZ18 p8 sb p10)
              R M mdl 61 4096 A_internal_munmap_ecall _ ECALLW K HB fetch_internal_munmap_ecall is_ecall_ECALLW).
    - unfold A_internal_munmap_ecall. lia.
    - unfold A_internal_munmap_ecall. lia.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - reflexivity.
    - reflexivity.
    - (* [comment removed for export] *)
      intros x Hx. rewrite E61 in Hx. unfold H8, H7, H6, H5, H4, H3.
      apply hcut_false_of. apply hcut_false_of. unfold hjoin. apply orb_false_intro.
      + apply hcut_false_of. apply hcut_false_of. apply orb_false_intro.
        * apply H2_out. unfold SHB_LO, SHB_HI. clear - Hx X7 X8 X9. lia.   (* [comment removed for export] *)
        * unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE. apply andb_false_iff. destruct X4 as [X4|X4]; [left; apply Z.leb_gt; clear - Hx X4; lia | right; apply Z.ltb_ge; clear - Hx X4; lia].
      + unfold N_PA. apply andb_false_iff. destruct X3 as [X3|X3]; [left; apply Z.leb_gt; clear - Hx X3; lia | right; apply Z.ltb_ge; clear - Hx X3; lia].
    - (* [comment removed for export] *)
      unfold hf_inmaps, hc6, hc3, HC5, lpop. rewrite L23_ext. cbn [List.tl app l_maps].
      repeat constructor.
      + exists (EVar 36, N_PA). split; [cbn [List.tl app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]; repeat (try (left; reflexivity); right)|]. cbn [fst snd]. change (edenot _ (EVar 36)) with (ev (EB' a tid c pl js) 36). rewrite E36. unfold N_PA. lia.
      + exists (EVar 28, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE). split; [cbn [List.tl app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]; repeat (try (left; reflexivity); right)|]. cbn [fst snd]. change (edenot _ (EVar 28)) with (ev (EB' a tid c pl js) 28). rewrite E28. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE. lia.
      + exists (ELit 0x2008fff7000, 0xdfff0001000). split; [cbn [List.tl app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]; repeat (try (left; reflexivity); right)|]. cbn [fst snd edenot]. rewrite u_small by lia. unfold SHB_HI. lia.
      + exists (ELit 0x7fff7000, 2 ^ 28). split; [cbn [List.tl app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]; repeat (try (left; reflexivity); right)|]. cbn [fst snd edenot]. rewrite u_small by lia. unfold SHB_LO. lia.
    - cbn [app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]. repeat (try (left; reflexivity); right).
    - cbn [app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]. repeat (try (left; reflexivity); right).
    - cbn [app l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit]. repeat (try (left; reflexivity); right).
    - intros R' mdl' HB'. unfold A_internal_munmap_ret. change (426768 + 4) with 426772. hnf.
      replace (Z_to_bv 64 A_internal_munmap_ret) with (Z_to_bv 64 (A_internal_munmap_ecall + 4)) in HK by reflexivity.
      apply HK. split; [| split; [assumption | split; [assumption | split; [assumption | split; [assumption | split; [assumption | unfold SHB_HI; lia]]]]]].
      unfold SR24, L24, LZ24. rewrite <- KN24_eq. rewrite <- E61. exact HB'.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem boot_s8 : forall a tid c pl p8 sb p10 p12 js R M mdl K, 2 ^ 25 <= lim -> length js = 44%nat ->
    at_E14' a tid c pl p8 sb p10 p12 js R M mdl ->
    (forall p14 p15 R' M' mdl',
       at_E16r a tid c pl p8 sb p10 p12 p15 ((js ++ [p14]) ++ [p15]) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_munmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 js R M mdl K Hlim Hjs HE HK. pose proof HE as (_ & Hsb & E28 & E29 & E36 & E38).
    apply (s8_e14 a tid c pl p8 sb p10 p12 js R M mdl K Hlim Hjs HE). intros p14 R0 M0 m0 H0.
    set (js1 := js ++ [p14]) in *.
    assert (L1 : length js1 = 45%nat) by (unfold js1; rewrite length_app, Hjs; reflexivity).
    assert (FX : forall ks, ev (EB' a tid c pl (js1 ++ ks)) 28 = p8 /\ ev (EB' a tid c pl (js1 ++ ks)) 29 = sb
                            /\ ev (EB' a tid c pl (js1 ++ ks)) 36 = p10 /\ ev (EB' a tid c pl (js1 ++ ks)) 38 = p12).
    { intros ks. unfold js1. rewrite <- app_assoc, !ev_EB_app by (rewrite Hjs; lia). repeat split; assumption. }
    destruct (FX []) as (F28 & F29 & F36 & F38). rewrite app_nil_r in F28, F29, F36, F38.
    apply (s8_b22 a tid c pl js1 p8 sb p10 p12 R0 M0 m0 K Hsb F28 F29 H0). intros R1 M1 m1 H1.
    apply (s8_e15 a tid c pl js1 p8 sb p10 p12 R1 M1 m1 K Hlim L1 F28 F38 H1). intros p15 R2 M2 m2 H2'.
    destruct (FX [p15]) as (G28 & G29 & G36 & G38).
    assert (G61 : ev (EB' a tid c pl (js1 ++ [p15])) 61 = p15).
    { replace 61%nat with (16 + 45)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 45), app_nth2, L1 by lia. reflexivity. }
    apply (s8_b23a _ _ _ _ _ _ _ _ _ _ _ _ K H2'). intros R3 M3 m3 H3'.
    pose proof (s8_merge _ _ _ _ _ _ _ _ _ _ _ _ H3') as H4'.
    apply (s8_b23b _ _ _ _ _ _ _ _ _ _ _ _ K Hsb G28 G29 G36 G38 H4'). intros R5 M5 m5 H5'.
    apply (s8_e16 a tid c pl _ p8 sb p10 p12 p15 R5 M5 m5 K G61 H5'). intros R6 M6 m6 H6'.
    exact (HK p14 p15 R6 M6 m6 H6').
  Qed.
End Theorems.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
