(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanMemIsZero. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanMemIsZero.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKn2__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootArith__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKn2__Lib.AsanBootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require Import BootS2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootState BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn3c__B3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn4a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4f__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn7a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS3 BootS4. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn6a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn7a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn8a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS4.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require Import BootS5 BootS6 BootS7. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS8. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW4.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require Import BootS9. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes5. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes5.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes6. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW5.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes6.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn10a.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots10_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let usp := bv_unsigned sp.

  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).
  #[local] Notation at_E18' := (at_E18 sp brk mbase draw lim inp).

  #[using="brk mbase draw inp VI VE"] Lemma SA16' : usp mod 16 = 0. Proof. exact (SA16 sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SLo' : 0x7fff80000000 <= usp. Proof. exact (SL sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SHi' : usp <= 2 ^ 47. Proof. exact (SH sp brk mbase draw inp VI VE). Qed.

  (* [comment removed for export] *)
  Definition L30 : ledger := lgrant L24 83 11571200.
  #[using="Type"] Lemma DS_E18_std : DS_std L24 = DS_E18. Proof. vmeq_refl. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s10_e18 : forall a tid c pl p8 sb p10 p12 p15 js R M mdl K, 2 ^ 25 <= lim -> length js = 67%nat ->
    at_E18' a tid c pl p8 sb p10 p12 p15 js R M mdl ->
    (forall p18 R' M' mdl', bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl (js ++ [p18]) SR30 KN30g L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 p15 js R M mdl K Hlim Hjs (HB & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64) HK.
    assert (LEN : length (VB' a tid c pl js) = 83%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    pose proof (p12_factsG sp brk mbase draw lim inp L24 [(EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof SLo' as SLo. pose proof SHi' as SHi.
    pose proof (shk_facts sp SA16' SLo' SHi') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & _).
    pose proof (x9_facts sp SA16' SLo' SHi') as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15).
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl js SR_E18A KN_E18 L24 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) 11571200 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      (* [comment removed for export] *)
      rewrite ?LEN; try reflexivity; [unfold A_internal_mmap_ecall; lia | | |].
    - cbn [l_eager L24 L23 L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit lpop A_bytes A9 A9a A8 A7 A5 fst snd]. change (page_round_up_Z 11571200) with 11571200.
      unfold HWLO, TPG, NSW.
      assert (B12 : PHI12 p12 - PLO12 p12 <= 12288).
      { clear - Q1 Q4 Q2 Q3 SHi. destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia. }
      clear - Hlim Y8 B12. lia.
    - cbn [l_maps L24 L23 L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit lpop List.tl gws]. change (page_round_up_Z 11571200) with 11571200. unfold N_PA, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. rewrite <- fetch_internal_mmap_ret_prev. apply (HK p). unfold SR30, L30.
      unfold kn_grant in HB'. change (page_round_up_Z 11571200) with 11571200 in HB'. rewrite DS_E18_std, KN30g_eq in HB'. exact HB'.
  Qed.
  #[using="Type"] Theorem s10_merge : forall a tid c pl js p8 sb p10 p12 p15 R M mdl,
    bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl js SR30 KN30g L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl js SR30 KN30 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl HB. rewrite <- KN30_eq.
    eapply bootS_reknow; [exact HB | auto |]. intros HKN. apply kn_merge8_sound; [exact merge30_ok | exact HKN].
  Qed.

  #[using="VI VE"] Theorem s10_b30a : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K,
    bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl js SR30 KN30 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl js SR30a KN30a L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_mcq_src) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K HB HK. rg_block VI VE HB HK run30a_eq car30a_eq. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma ue_add : forall E a b, bv_unsigned (edenot E (EAlu ALU_ADD a b)) = (bv_unsigned (edenot E a) + bv_unsigned (edenot E b)) mod 2 ^ 64.
  Proof. intros. cbn [edenot]. apply u_add64. Qed.
  #[using="Type"] Lemma ue_mul : forall E a b, bv_unsigned (edenot E (EMd M_MUL a b)) = (bv_unsigned (edenot E a) * bv_unsigned (edenot E b)) mod 2 ^ 64.
  Proof. intros. cbn [edenot]. apply u_mul64. Qed.
  #[using="Type"] Lemma ue_srl3 : forall E a, bv_unsigned (edenot E (EAlu ALU_SRL a (ELit 3))) = bv_unsigned (edenot E a) / 8.
  Proof. intros. cbn [edenot]. rewrite u_srl64. rewrite u_lit64a. reflexivity. Qed.
  #[using="sp usp"] Lemma ue_lit : forall E z, 0 <= z < 2 ^ 64 -> bv_unsigned (edenot E (ELit z)) = z.
  Proof. intros. cbn [edenot]. apply u_small. lia. Qed.
  #[using="Type"] Lemma ue_var : forall E i, edenot E (EVar i) = ev E i. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ES : expr := EAlu ALU_ADD (EVar 0) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 8) (EVar 4)))).
  #[using="sp usp"] Lemma ES_val : forall E, bv_unsigned (ev E 0) <= 2 ^ 47 -> bv_unsigned (ev E 1) <= 1024 -> bv_unsigned (ev E 2) <= 256 -> bv_unsigned (ev E 4) <= 280000 ->
    bv_unsigned (edenot E ES) = bv_unsigned (ev E 0) + 8 * (bv_unsigned (ev E 1) + bv_unsigned (ev E 2) + bv_unsigned (ev E 4)).
  Proof.
    intros E H0 H1 H2 H4. pose proof (u64_range (ev E 1)). pose proof (u64_range (ev E 2)). pose proof (u64_range (ev E 4)). pose proof (u64_range (ev E 0)).
    unfold ES. rewrite !ue_add, !ue_mul, !ue_var, !ue_lit by lia.
    rewrite (Z.mod_small (8 * bv_unsigned (ev E 4))) by lia. rewrite (Z.mod_small (8 * bv_unsigned (ev E 2))) by lia. rewrite (Z.mod_small (8 * bv_unsigned (ev E 1))) by lia.
    rewrite (Z.mod_small (8 * bv_unsigned (ev E 2) + 8 * bv_unsigned (ev E 4))) by lia.
    rewrite (Z.mod_small (8 * bv_unsigned (ev E 1) + (8 * bv_unsigned (ev E 2) + 8 * bv_unsigned (ev E 4)))) by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.
  (* [comment removed for export] *)
  Definition Wsrc (S : Z) : Z := (S / 8 + 24 + CSH) / 8 * 8.          (* [comment removed for export] *)
  Definition Wdst : Z := (usp / 8 - 62 + CSH) / 8 * 8.                 (* [comment removed for export] *)

  #[using="VI VE"] Lemma src_facts : forall H A a tid c pl js sr kn L hc lz R M mdl,
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    In (KRange (EAlu ALU_ADD ES (ELit 200)) 140735340871872 140737488355328) kn ->
    In (KRange (EVar 1) 1 1024) kn -> In (KRange (EVar 2) 0 256) kn -> In (KRange (EVar 4) 0 280000) kn ->
    let E := EB' a tid c pl js in let S := bv_unsigned (edenot E ES) in
    S = usp + 8 * (bv_unsigned (ev E 1) + bv_unsigned (ev E 2) + bv_unsigned (ev E 4)) /\ S mod 8 = 0 /\ usp + 8 <= S /\ S + 200 <= 2 ^ 47
    /\ bv_unsigned (edenot E MCQ5s) = Wsrc S /\ bv_unsigned (edenot E MCQ6s) = Wsrc S.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl HB IS I1 I2 I4 E S.
    destruct HB as [_ HKN _ _ _ _ _ _ _ _ _ _].
    pose proof (proj1 (Forall_forall _ _) HKN _ IS) as KS. pose proof (proj1 (Forall_forall _ _) HKN _ I1) as K1.
    pose proof (proj1 (Forall_forall _ _) HKN _ I2) as K2. pose proof (proj1 (Forall_forall _ _) HKN _ I4) as K4.
    cbn [kentry_ok] in KS, K1, K2, K4. rewrite !ue_var in K1, K2, K4. fold E in KS, K1, K2, K4.
    pose proof SLo' as SLo. pose proof SHi' as SHi. pose proof SA16' as SAL.
    assert (E0 : ev E 0 = sp) by (unfold E; apply ev_EB_sp).
    pose proof (ES_val E ltac:(rewrite E0; unfold usp in *; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as SV. rewrite E0 in SV. fold usp in SV. fold S in SV.
    rewrite ue_add, ue_lit, Z.mod_small in KS by (rewrite ?ue_lit; fold S; unfold usp in *; lia). fold S in KS.
    assert (SM : S mod 8 = 0).
    { rewrite SV. rewrite Z.add_mod, Z.mul_comm, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
      pose proof (Z.div_mod usp 16 ltac:(lia)). replace usp with (usp / 16 * 2 * 8) by lia. apply Z_mod_mult. }
    refine (conj SV (conj SM (conj _ (conj _ _)))); [lia | lia |].
    assert (D8 : (S + 192) / 8 = S / 8 + 24) by (pose proof (Z.div_mod S 8 ltac:(lia)); symmetry; apply Z.div_unique with (r := 0); lia).
    assert (D8' : (S + 199) / 8 = S / 8 + 24) by (pose proof (Z.div_mod S 8 ltac:(lia)); symmetry; apply Z.div_unique with (r := 7); lia).
    unfold MCQ5s, MCQ6s, Wsrc, CSH. fold ES. rewrite !ue_mul, !ue_srl3, !ue_add, !ue_srl3, !ue_add, !ue_lit by lia. fold S.
    rewrite !(Z.mod_small (S + _)) by lia. rewrite D8, D8'.
    assert (DSb : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    rewrite !(Z.mod_small (S / 8 + 24 + _)) by lia.
    pose proof (Z.div_mod (S / 8 + 24 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (S / 8 + 24 + 2147450880) 8 ltac:(lia)).
    rewrite !Z.mod_small by lia. lia.
  Qed.
  #[using="Type"] Lemma in30a_facts :
    In (KRange (EAlu ALU_ADD ES (ELit 200)) 140735340871872 140737488355328) KN30a /\ In (KRange (EVar 1) 1 1024) KN30a
    /\ In (KRange (EVar 2) 0 256) KN30a /\ In (KRange (EVar 4) 0 280000) KN30a.
  Proof. repeat split; apply in_kn_of_b; vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s10_re84 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl, length js = 68%nat ->
    bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl js SR30a KN30a L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    let S := bv_unsigned (edenot (EB' a tid c pl js) ES) in
    bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl (js ++ [Z_to_bv 64 (Wsrc S)]) SR31 (KF84 ++ KN30a) L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl
    /\ ev (EB' a tid c pl (js ++ [Z_to_bv 64 (Wsrc S)])) 84 = Z_to_bv 64 (Wsrc S)
    /\ S mod 8 = 0 /\ usp + 8 <= S /\ S + 200 <= 2 ^ 47.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl Hjs HB S.
    assert (LEN : length (VB' a tid c pl js) = 84%nat) by (rewrite length_VB, Hjs; reflexivity).
    destruct in30a_facts as (IS & I1 & I2 & I4).
    pose proof (src_facts _ _ a tid c pl js _ _ _ _ _ R M mdl HB IS I1 I2 I4) as (SV & SM & SL8 & SH & M5 & M6). fold S in SV, SM, SL8, SH, M5, M6.
    pose proof SLo' as SLo.
    assert (WR : 0 <= Wsrc S < 2 ^ 64).
    { unfold Wsrc, CSH. pose proof (Z.div_mod (S / 8 + 24 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (S / 8 + 24 + 2147450880) 8 ltac:(lia)).
      assert (0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia. }
    assert (E84 : ev (EB' a tid c pl (js ++ [Z_to_bv 64 (Wsrc S)])) 84 = Z_to_bv 64 (Wsrc S)).
    { replace 84%nat with (16 + 68)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 68), app_nth2, Hjs by lia. reflexivity. }
    refine (conj _ (conj E84 (conj SM (conj SL8 SH)))).
    set (E' := EB' a tid c pl (js ++ [Z_to_bv 64 (Wsrc S)])) in *.
    assert (AGR : env_agree 84 (EB' a tid c pl js) E').
    { unfold E'. rewrite EB_app, <- LEN. unfold EB. apply vals_app_agree. }
    assert (M5' : edenot E' MCQ5s = ev E' 84).
    { apply bv_eq. rewrite E84, u_small by lia. rewrite <- (edenot_agree 84 _ _ MCQ5s AGR) by (vmeq_refl). exact M5. }
    assert (M6' : edenot E' MCQ6s = ev E' 84).
    { apply bv_eq. rewrite E84, u_small by lia. rewrite <- (edenot_agree 84 _ _ MCQ6s AGR) by (vmeq_refl). exact M6. }
    apply (bs_fresh2 sp brk mbase draw lim inp _ _ a tid c pl js SR30a KN30a L30 _ _ R M mdl [Z_to_bv 64 (Wsrc S)] SR31 KF84 HB);
      rewrite ?LEN; [vmeq_refl | vmeq_refl | vmeq_refl | |].
    - intros HR'. fold E' in HR' |- *. rewrite <- SR31_eq. unfold sr_upds. cbn [fold_left fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
      eapply (regs_ok_upd1 E' _ R R 16%bv); [ | intros X; apply (f_equal bv_unsigned) in X; discriminate X | | intros; reflexivity ].
      1: eapply (regs_ok_upd1 E' _ R R 15%bv); [ exact HR' | intros X; apply (f_equal bv_unsigned) in X; discriminate X | | intros; reflexivity ].
      + rewrite (HR' 15%bv). exact M5'.
      + rewrite (HR' 16%bv). exact M6'.
    - unfold KF84. constructor; [| constructor; [| constructor]]; cbn [kentry_ok]; rewrite ue_var.
      all: fold E'; rewrite E84, u_small by lia.
      + split; [lia|]. unfold Wsrc. apply Z_mod_mult.
      + unfold Wsrc, CSH. pose proof (Z.div_mod (S / 8 + 24 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (S / 8 + 24 + 2147450880) 8 ltac:(lia)).
        assert (usp / 8 <= S / 8) by (apply Z.div_le_mono; lia). assert (S / 8 <= 2 ^ 44 - 25) by (apply Z.div_le_upper_bound; lia).
        pose proof (Z.div_mod usp 8 ltac:(lia)). pose proof (Z.mod_pos_bound usp 8 ltac:(lia)). lia.
  Qed.
  (* [comment removed for export] *)
  #[using="brk mbase draw inp VI VE"] Lemma H9_hidden_high : forall p8 sb p10 p12 a (x : word),
    bv_unsigned sb = SBV p8 -> SHB_HI <= bv_unsigned p8 -> bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE <= usp - stack_max_size ->
    IMG_HI <= bv_unsigned p12 -> bv_unsigned p12 + 65536 <= usp - stack_max_size ->
    bv_unsigned a + 4096 <= usp - stack_max_size ->
    usp / 8 + CSH - 61 <= bv_unsigned x < SHB_HI -> H9 sp p8 sb p10 p12 a x = true.
  Proof.
    intros p8 sb p10 p12 a x Hsb P2 P3 Q2 Q3 TA Hx.
    pose proof SLo' as SLo. pose proof SHi' as SHi. pose proof (u64_range a) as Ua.
    unfold SHB_HI, IMG_HI, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, stack_max_size, SBV, CSH in *.
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    assert (D8 : forall A n, (A + 8 * n) / 8 = A / 8 + n) by (intros A n; replace (A + 8 * n) with (A + n * 8) by lia; rewrite Z.div_add by lia; reflexivity).
    unfold H9. apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ right. unfold TSH, CSH. pose proof (Z.div_le_mono (bv_unsigned a + 2048 + 8 * 1048200) usp 8 ltac:(lia) ltac:(lia)) as DL. rewrite D8 in DL. lia. }
    unfold H9a. apply hhide_old. unfold H8, H7, H6, H5, H4, H3.
    apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ right. unfold SHK. pose proof (Z.div_le_mono (usp - 800 + 8 * 100) usp 8 ltac:(lia) ltac:(lia)) as DL. rewrite D8 in DL. unfold usp in *. lia. }
    apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ right. unfold SH12. pose proof (Z.div_le_mono (bv_unsigned p12 + 8 * 1056768) usp 8 ltac:(lia) ltac:(lia)) as DL. rewrite D8 in DL. lia. }
    apply hjoin_old. apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ right. unfold SHRI, RI. pose proof (Z.div_le_mono (bv_unsigned sb + 2 ^ 37 + 8 * 1049088) usp 8 ltac:(lia) ltac:(lia)) as DL. rewrite D8 in DL. lia. }
    apply (proj2 (hcut_true _ _ _ _)). split; [| left; unfold RI; lia].
    apply hjoin_old. apply H2_in. unfold SHB_LO, SHB_HI. pose proof (Z.div_le_mono 0x7fff80000000 usp 8 ltac:(lia) ltac:(lia)). lia.
  Qed.
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s10_x84 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl (W : Z), 2 ^ 25 <= lim ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 84 = Z_to_bv 64 W -> W mod 8 = 0 -> usp / 8 + CSH <= W -> W + 8 <= SHB_HI ->
    bootS' (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl js SR31 (KF84 ++ KN30a) L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    bootS' (hcut (H9 sp p8 sb p10 p12 a) W 8) ((W / 4096 * 4096, W / 4096 * 4096 + 4096) :: A9 sp sb p12 a) a tid c pl js SR31 KN31 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl W Hlim E28 E38 Hsb E84 WM WL WH HB.
    pose proof SLo' as SLo. pose proof SHi' as SHi.
    pose proof (p8_factsG sp brk mbase draw lim inp L30 [(EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    pose proof (p12_factsG sp brk mbase draw lim inp L30 [(EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    assert (TA : bv_unsigned a + 4096 <= usp - stack_max_size) by (destruct HB as [_ _ _ _ _ _ _ _ _ HT _ _]; exact (proj1 (proj2 (proj2 HT)))).
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    pose proof (rdown_facts W ltac:(unfold CSH in *; lia)) as [R1 R2].
    assert (E84v : bv_unsigned (edenot (EB sp draw inp a tid c pl js) (EVar 84)) = W).
    { rewrite ue_var. change (ev (EB sp draw inp a tid c pl js) 84) with (ev (EB' a tid c pl js) 84). rewrite E84. apply u_small. unfold CSH, SHB_HI in *. lia. }
    pose proof (bs_expose_keep sp brk mbase draw lim inp VI VE (H9 sp p8 sb p10 p12 a) (A9 sp sb p12 a) a tid c pl js SR31 (KF84 ++ KN30a) L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl
                  (EVar 84) 0 8 (W / 4096 * 4096) 4096 0x2008fff7000 SHB_HI HB) as X.
    cbv zeta in X. rewrite E84v, Z.add_0_r in X. unfold KN31. apply X; clear X.
    - exact R2.
    - reflexivity.
    - clear; lia.
    - clear - R1 WL. assert (0 <= usp / 8) by (apply Z.div_pos; [pose proof (u64_range sp); unfold usp; lia | lia]). unfold CSH in *. lia.
    - clear - R1 WH SLo. unfold SHB_HI, stack_max_size in *. lia.
    - clear - R1; lia.
    - clear; lia.
    - clear - R1 R2 WM. pose proof (Z.div_mod W 4096 ltac:(lia)). pose proof (Z.div_mod W 8 ltac:(lia)). lia.
    - clear - WL. assert (0 <= usp / 8) by (apply Z.div_pos; [pose proof (u64_range sp); unfold usp; lia | lia]). unfold IMG_HI, CSH in *. lia.
    - intros x Hx. apply (H9_hidden_high p8 sb p10 p12 a x Hsb P2 P3 Q2 Q3 TA). clear - Hx WL WH. lia.
    - unfold hc6, hc3, HC5. cbn [In]. do 2 right. left. reflexivity.
    - clear - WL SLo. pose proof (Z.div_le_mono 0x7fff80000000 usp 8 ltac:(lia) ltac:(unfold usp in *; lia)). change (0x7fff80000000 / 8) with 17591917608960 in H. unfold CSH in *. lia.
    - exact WH.
    - cbn [l_eager L30 L24 L23 L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit lpop A_bytes A9 A9a A8 A7 A5 fst snd]. unfold HWLO, TPG, NSW.
      pose proof (shk_facts sp SA16' SLo' SHi') as (_ & _ & _ & _ & _ & _ & _ & Y8 & _).
      assert (B12 : PHI12 p12 - PLO12 p12 <= 12288).
      { clear - Q1 Q4 Q2 Q3 SHi. destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia. }
      clear - Hlim Y8 B12. lia.
    - vmeq_refl.
  Qed.
  #[using="VI VE"] Theorem s10_b31a : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (hcut (H9 sp p8 sb p10 p12 a) W 8) ((W / 4096 * 4096, W / 4096 * 4096 + 4096) :: A9 sp sb p12 a) a tid c pl js SR31 KN31 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (hcut (H9 sp p8 sb p10 p12 a) W 8) ((W / 4096 * 4096, W / 4096 * 4096 + 4096) :: A9 sp sb p12 a) a tid c pl js SR31a KN31a L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_mcq_dst) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_mcq_src) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. rg_block VI VE HB HK run31a_eq car31a_eq. Qed.
  (* [comment removed for export] *)
  #[using="brk mbase VI VE"] Lemma dst_facts : forall a tid c pl js, let E := EB' a tid c pl js in
    bv_unsigned (edenot E MCQ5d) = Wdst /\ bv_unsigned (edenot E MCQ6d) = Wdst
    /\ Wdst mod 8 = 0 /\ usp / 8 + CSH - 69 <= Wdst /\ Wdst + 7 <= usp / 8 + CSH - 55.
  Proof.
    intros a tid c pl js E. pose proof SLo' as SLo. pose proof SHi' as SHi. pose proof SA16' as SAL.
    assert (E0 : ev E 0 = sp) by (unfold E; apply ev_EB_sp).
    pose proof (Z.div_mod usp 16 ltac:(lia)) as D16.
    assert (D8 : usp / 8 = 2 * (usp / 16)) by (symmetry; apply Z.div_unique with (r := 0); lia).
    assert (D1 : (usp + -496) / 8 = usp / 8 - 62) by (symmetry; apply Z.div_unique with (r := 0); lia).
    assert (D2 : (usp + -489) / 8 = usp / 8 - 62) by (symmetry; apply Z.div_unique with (r := 7); lia).
    pose proof (Z.div_mod (usp / 8 - 62 + 2147450880) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (usp / 8 - 62 + 2147450880) 8 ltac:(lia)) as M3.
    unfold MCQ5d, MCQ6d, Wdst, CSH. rewrite !ue_mul, !ue_srl3, !ue_add, !(shx_val_gen _ 0), !ue_lit, !E0; fold usp; try (unfold usp in *; lia).
    rewrite D1, D2. rewrite !(Z.mod_small (usp / 8 - 62 + _)) by lia. rewrite !Z.mod_small by lia.
    repeat split; try lia. apply Z_mod_mult.
    all: rewrite ?E0; pose proof SLo' as SL0; unfold usp in *; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s10_re85 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl (W : Z), length js = 69%nat ->
    bootS' (hcut (H9 sp p8 sb p10 p12 a) W 8) ((W / 4096 * 4096, W / 4096 * 4096 + 4096) :: A9 sp sb p12 a) a tid c pl js SR31a KN31a L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    bootS' (hcut (H9 sp p8 sb p10 p12 a) W 8) ((W / 4096 * 4096, W / 4096 * 4096 + 4096) :: A9 sp sb p12 a) a tid c pl (js ++ [Z_to_bv 64 Wdst]) SR32 (KF85 ++ KN31a) L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl
    /\ ev (EB' a tid c pl (js ++ [Z_to_bv 64 Wdst])) 85 = Z_to_bv 64 Wdst.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl W Hjs HB.
    assert (LEN : length (VB' a tid c pl js) = 85%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof SLo' as SLo. pose proof SHi' as SHi.
    pose proof (dst_facts a tid c pl js) as (M5 & M6 & WM & WL & WH).
    assert (WR : 0 <= Wdst < 2 ^ 64).
    { assert (0 <= usp / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold usp in *; lia). unfold CSH in *. lia. }
    assert (E85 : ev (EB' a tid c pl (js ++ [Z_to_bv 64 Wdst])) 85 = Z_to_bv 64 Wdst).
    { replace 85%nat with (16 + 69)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 69), app_nth2, Hjs by lia. reflexivity. }
    refine (conj _ E85).
    set (E' := EB' a tid c pl (js ++ [Z_to_bv 64 Wdst])) in *.
    assert (AGR : env_agree 85 (EB' a tid c pl js) E').
    { unfold E'. rewrite EB_app, <- LEN. unfold EB. apply vals_app_agree. }
    assert (M5' : edenot E' MCQ5d = ev E' 85).
    { apply bv_eq. rewrite E85, u_small by lia. rewrite <- (edenot_agree 85 _ _ MCQ5d AGR) by (vmeq_refl). exact M5. }
    assert (M6' : edenot E' MCQ6d = ev E' 85).
    { apply bv_eq. rewrite E85, u_small by lia. rewrite <- (edenot_agree 85 _ _ MCQ6d AGR) by (vmeq_refl). exact M6. }
    apply (bs_fresh2 sp brk mbase draw lim inp _ _ a tid c pl js SR31a KN31a L30 _ _ R M mdl [Z_to_bv 64 Wdst] SR32 KF85 HB);
      rewrite ?LEN; [vmeq_refl | vmeq_refl | vmeq_refl | |].
    - intros HR'. fold E' in HR' |- *. rewrite <- SR32_eq. unfold sr_upds. cbn [fold_left fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
      eapply (regs_ok_upd1 E' _ R R 16%bv); [ | intros X; apply (f_equal bv_unsigned) in X; discriminate X | | intros; reflexivity ].
      1: eapply (regs_ok_upd1 E' _ R R 15%bv); [ exact HR' | intros X; apply (f_equal bv_unsigned) in X; discriminate X | | intros; reflexivity ].
      + rewrite (HR' 15%bv). exact M5'.
      + rewrite (HR' 16%bv). exact M6'.
    - unfold KF85. constructor; [| constructor; [| constructor]]; cbn [kentry_ok]; rewrite ue_var.
      all: fold E'; rewrite E85, u_small by lia.
      + split; [lia|]. exact WM.
      + assert (0 <= usp / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold usp in *; lia).
        pose proof (Z.div_le_mono 0x7fff80000000 usp 8 ltac:(lia) ltac:(unfold usp in *; lia)). change (0x7fff80000000 / 8) with 17591917608960 in H0.
        unfold CSH, SHB_HI in *. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s10_x85 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl (W : Z), 2 ^ 25 <= lim ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    usp / 8 + CSH <= W -> ev (EB' a tid c pl js) 85 = Z_to_bv 64 Wdst ->
    bootS' (hcut (H9 sp p8 sb p10 p12 a) W 8) ((W / 4096 * 4096, W / 4096 * 4096 + 4096) :: A9 sp sb p12 a) a tid c pl js SR32 (KF85 ++ KN31a) L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    bootS' (hcut (hcut (H9 sp p8 sb p10 p12 a) W 8) Wdst 8) ((Wdst / 4096 * 4096, Wdst / 4096 * 4096 + 4096) :: (W / 4096 * 4096, W / 4096 * 4096 + 4096) :: A9 sp sb p12 a)
           a tid c pl js SR32 KN32 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl W Hlim E28 E38 WL E85 HB.
    pose proof SLo' as SLo. pose proof SHi' as SHi.
    pose proof (x9_facts sp SA16' SLo' SHi') as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & _).
    pose proof (dst_facts a tid c pl js) as (_ & _ & DM & DL & DH).
    pose proof (p12_factsG sp brk mbase draw lim inp L30 [(EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    assert (TA : bv_unsigned a + 4096 <= usp - stack_max_size) by (destruct HB as [_ _ _ _ _ _ _ _ _ HT _ _]; exact (proj1 (proj2 (proj2 HT)))).
    assert (U8 : 0 <= usp / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold usp in *; lia).
    pose proof (Z.div_le_mono 0x7fff80000000 usp 8 ltac:(lia) ltac:(unfold usp in *; lia)) as U8lo. change (0x7fff80000000 / 8) with 17591917608960 in U8lo.
    pose proof (rdown_facts Wdst ltac:(unfold CSH in *; lia)) as [R1 R2].
    assert (E85v : bv_unsigned (edenot (EB sp draw inp a tid c pl js) (EVar 85)) = Wdst).
    { rewrite ue_var. change (ev (EB sp draw inp a tid c pl js) 85) with (ev (EB' a tid c pl js) 85). rewrite E85. apply u_small. unfold CSH in *. lia. }
    (* [comment removed for export] *)
    assert (TW : forall x : word, Wdst <= bv_unsigned x < Wdst + 8 -> XQv sp + CTW <= bv_unsigned x < XQv sp + CTW + 4096).
    { intros x Hx. unfold CTW, CSH in *. unfold XLO, XHI in *.
      assert (D8 : forall A n, (A + 8 * n) / 8 = A / 8 + n) by (intros A n; replace (A + 8 * n) with (A + n * 8) by lia; rewrite Z.div_add by lia; reflexivity).
      pose proof (Z.div_le_mono (usp - 160) (STv sp) 8 ltac:(lia) ltac:(unfold usp; lia)) as A1.
      pose proof (Z.div_le_mono (STv sp) (usp + 8 * 490) 8 ltac:(lia) ltac:(unfold usp; lia)) as A2. rewrite D8 in A2.
      replace (STv sp / 8) with (XQv sp + 1048576) in A1, A2 by (rewrite X6; rewrite Z.mul_comm, Z.div_add_l by lia; reflexivity).
      pose proof (Z.div_mod (usp - 160) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (usp - 160) 8 ltac:(lia)).
      pose proof (Z.div_mod usp 8 ltac:(lia)). pose proof (Z.mod_pos_bound usp 8 ltac:(lia)). clear - Hx DL DH A1 A2 H H0 H1 H2. lia. }
    pose proof (bs_expose_keep sp brk mbase draw lim inp VI VE (hcut (H9 sp p8 sb p10 p12 a) W 8) ((W / 4096 * 4096, W / 4096 * 4096 + 4096) :: A9 sp sb p12 a) a tid c pl js SR32 (KF85 ++ KN31a) L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl
                  (EVar 85) 0 8 (Wdst / 4096 * 4096) 4096 0x2008fff7000 SHB_HI HB) as X.
    cbv zeta in X. rewrite E85v, Z.add_0_r in X. unfold KN32. apply X; clear X.
    - exact R2.
    - reflexivity.
    - clear; lia.
    - clear - R1 DL U8. unfold CSH in *. lia.
    - clear - R1 DH SLo U8. unfold CSH, stack_max_size in *. lia.
    - clear - R1; lia.
    - clear; lia.
    - clear - R1 R2 DM. pose proof (Z.div_mod Wdst 4096 ltac:(lia)). pose proof (Z.div_mod Wdst 8 ltac:(lia)). lia.
    - clear - DL U8lo. unfold IMG_HI, CSH in *. lia.
    - intros x Hx. apply (proj2 (hcut_true _ _ _ _)). split; [| left; clear - Hx WL DH; lia].
      unfold H9. apply (proj2 (hcut_true _ _ _ _)). split.
      2:{ right. unfold TSH, CSH in *. unfold stack_max_size in TA.
          assert (D8 : forall A n, (A + 8 * n) / 8 = A / 8 + n) by (intros A n; replace (A + 8 * n) with (A + n * 8) by lia; rewrite Z.div_add by lia; reflexivity).
          pose proof (Z.div_le_mono (bv_unsigned a + 2048 + 8 * 1048200) usp 8 ltac:(lia) ltac:(lia)) as A3. rewrite D8 in A3. clear - A3 Hx DL. lia. }
      unfold H9a. apply hhide_in. pose proof (TW x Hx) as TWx. clear - TWx. unfold CTW, NSW, CSH in *. lia.
    - unfold hc6, hc3, HC5. cbn [In]. do 2 right. left. reflexivity.
    - clear - DL U8lo. unfold CSH in *. lia.
    - clear - DH U8. unfold CSH, SHB_HI in *. lia.
    - cbn [l_eager L30 L24 L23 L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit lpop A_bytes A9 A9a A8 A7 A5 fst snd]. unfold HWLO, TPG, NSW.
      pose proof (shk_facts sp SA16' SLo' SHi') as (_ & _ & _ & _ & _ & _ & _ & Y8 & _).
      assert (B12 : PHI12 p12 - PLO12 p12 <= 12288).
      { clear - Q1 Q4 Q2 Q3 SHi. destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia. }
      clear - Hlim Y8 B12. lia.
    - vmeq_refl.
  Qed.
  (* [comment removed for export] *)
  Definition H10 (sp p8 sb p10 p12 a : word) (W : Z) : word -> bool := hcut (hcut (H9 sp p8 sb p10 p12 a) W 8) Wdst 8.
  Definition A10 (sp sb p12 a : word) (W : Z) : list (Z * Z) := (Wdst / 4096 * 4096, Wdst / 4096 * 4096 + 4096) :: (W / 4096 * 4096, W / 4096 * 4096 + 4096) :: A9 sp sb p12 a.

  #[using="VI VE"] Theorem s10_b32a : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR32 KN32 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR32a KN32a L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_memcpy) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_mcq_dst) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. rg_block VI VE HB HK run32a_eq car32a_eq. Qed.
  #[using="Type"] Lemma in32a_facts :
    In (KRange (EAlu ALU_ADD ES (ELit 200)) 140735340871872 140737488355328) KN32a /\ In (KRange (EVar 1) 1 1024) KN32a
    /\ In (KRange (EVar 2) 0 256) KN32a /\ In (KRange (EVar 4) 0 280000) KN32a
    /\ In (KBlob (SA ES 184) (ELit 16) 25%nat) KN32a.
  Proof. repeat split; apply in_kn_of_b; vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s10_mc : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), length js = 70%nat ->
    bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR32a KN32a L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl' (w : word),
       bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl ((js ++ [w]) ++ junk_c R' memcpy_clob) SR33 KN33 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_mcq_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memcpy) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hjs HB HK.
    assert (LEN : length (VB' a tid c pl js) = 86%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof SLo' as SLo. pose proof SHi' as SHi.
    destruct in32a_facts as (IS & I1 & I2 & I4 & IB).
    pose proof (src_facts _ _ a tid c pl js _ _ _ _ _ R M mdl HB IS I1 I2 I4) as (SV & SM & SL8 & SH & _ & _).
    set (S := bv_unsigned (edenot (EB' a tid c pl js) ES)) in *.
    (* [comment removed for export] *)
    pose proof HB as HB0. destruct HB0 as [_ HKN _ _ _ _ _ _ _ _ _ _].
    pose proof (proj1 (Forall_forall _ _) HKN _ IB) as KB. cbn [kentry_ok] in KB. destruct KB as (Bfl & Blen & Bby).
    unfold estart, elenZ in Bfl, Blen, Bby. cbn [a_base a_off] in Bfl, Blen, Bby. rewrite ue_lit in Blen, Bby by lia. fold S in Bfl, Blen, Bby.
    set (blob := eb (EB' a tid c pl js) 25) in *.
    set (bs := firstn 8 (skipn 8 blob)).
    assert (LBS : length bs = 8%nat) by (unfold bs; rewrite firstn_length, skipn_length; lia).
    assert (RDN : rdn SEGS (mrestrict (H10 sp p8 sb p10 p12 a W) M) (Z_to_bv 64 (S + 192)) 8 = Some bs).
    { apply rdn_pointwise; [exact LBS | rewrite u_small by lia; lia |]. intros j Hj. rewrite u_small by lia.
      replace (S + 192 + Z.of_nat j) with (S + 184 + (8 + Z.of_nat j)) by lia. rewrite (Bby (8 + Z.of_nat j)) by lia.
      f_equal. unfold bs. rewrite nth_firstn, nth_skipn by lia. replace (Nat.ltb j 8) with true by (symmetry; apply Nat.ltb_lt; lia).
      f_equal. lia. }
    assert (U8 : 0 <= usp / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold usp in *; lia).
    assert (E0v : bv_unsigned (edenot (EB sp draw inp a tid c pl js) (EVar 0)) = usp) by (rewrite ue_var, ev_EB_sp; reflexivity).
    let iW := kidx KN32a (fun K => match K with KWr (SA (EVar 0) k) (ELit n) => (Z.eqb k (-8388608) && Z.eqb n 8388608)%bool | _ => false end) in
    pose proof (cross_musl_memcpy8 sp brk mbase draw lim inp VI VE memcpy_clob 0%nat (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR32a KN32a L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl
                  (EVar 0) (-496) iW (-8388608) 8388608 (S + 192) A_mcq_ret bs (EVar 0) (-496) 8 K HB) as X.
    cbv zeta in X. rewrite LEN, E0v in X. apply X; clear X.
    + reflexivity.
    + clear - SLo; lia.
    + clear; lia.
    + clear; lia.
    + clear; lia.
    + intros r Hr; exact Hr.
    + cbn. intros Hx0. repeat (destruct Hx0 as [Hx0|Hx0]; [discriminate|]). exact Hx0.
    + unfold memcpy_clob. repeat (constructor; [cbn; intros Hx0; repeat (destruct Hx0 as [Hx0|Hx0]; [discriminate|]); exact Hx0|]). constructor.
    + vmeq_refl.
    + vmeq_refl.
    + vmeq_refl.
    + reflexivity.
    + vmeq_refl.
    + replace (sr_get SR32a 11%bv) with (EAlu ALU_ADD ES (ELit 192)) by (vmeq_refl).
      apply bv_eq. rewrite ue_add, ue_lit, u_small by lia. fold S. rewrite Z.mod_small by lia. reflexivity.
    + replace (sr_get SR32a 12%bv) with (ELit 8) by (vmeq_refl). reflexivity.
    + vmeq_refl.
    + apply bv_eq. vmeq_refl.
    + vmeq_refl.
    + clear; lia.
    + clear; lia.
    + clear; lia.
    + clear - SLo; lia.
    + clear; lia.
    + exact LBS.
    + exact RDN.
    + left. clear - SL8. lia.
    + clear - SL8 SLo. lia.
    + clear - SH. lia.
    + intros R' M' mdl' HB' Hfr. apply (HK R' M' mdl' (le_bytes_to_word bs)).
      rewrite !skipn_O in HB'. rewrite KN33_eq in HB'. rewrite <- SR33_eq. exact HB'.
  Qed.
  (* [comment removed for export] *)
  Definition A_brk_ecall0 : Z := 0x95fd8.   (* [comment removed for export] *)
  Definition A_brk_ecall1 : Z := 0x95ffc.   (* [comment removed for export] *)
  #[using="Type"] Lemma fetch_brk_ecall0 : fetch_word SEGS (Z_to_bv 64 A_brk_ecall0) = Some ECALLW. Proof. vmeq_refl. Qed.
  #[using="Type"] Lemma fetch_brk_ecall1 : fetch_word SEGS (Z_to_bv 64 A_brk_ecall1) = Some ECALLW. Proof. vmeq_refl. Qed.

  (* [comment removed for export] *)
  Definition at_E19 (a tid c : word) (pl : placements) (p8 sb p10 p12 p15 : word) (W : Z) (js : list word) R M mdl : Prop :=
    bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR_E19 KN_E19 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12
    /\ (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15)
    /\ ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js) 64 = Z_to_bv 64 (PBv sp)
    /\ ev (EB' a tid c pl js) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl js) 85 = Z_to_bv 64 Wdst /\ usp / 8 + CSH <= W /\ W + 8 <= SHB_HI.

  #[using="VI VE"] Theorem s10_b33a : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR33 KN33 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR_E19 KN_E19 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_brk_ecall0) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_mcq_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_mcq_ret with RET32. change A_brk_ecall0 with PC_E19 in HK. rg_block VI VE HB HK run33a_eq car33a_eq. Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s10_e19 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), length js = 85%nat ->
    bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR_E19 KN_E19 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R', bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl (js ++ [brk]) SR34 KN34 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M mdl ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_brk_ecall0 + 4)) M ROM) mdl) K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_brk_ecall0) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hjs HB HK.
    assert (LEN : length (VB' a tid c pl js) = 101%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (bs_brk_query sp brk mbase draw lim inp VI VE (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR_E19 KN_E19 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15)
                  A_brk_ecall0 ECALLW R M mdl K HB fetch_brk_ecall0 is_ecall_ECALLW) as X.
    cbv zeta in X. rewrite LEN in X. apply X; clear X.
    - unfold A_brk_ecall0; clear; lia.
    - unfold A_brk_ecall0; clear; lia.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - cbn [l_brk L30 L24 L23 L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit lpop]. clear; lia.
    - cbn [l_brk L30 L24 L23 L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit lpop]. reflexivity.
    - intros R' HB'. apply HK. replace (Z_to_bv 64 (bv_unsigned brk + l_brk L30)) with brk in HB'.
      2:{ apply bv_eq. cbn [l_brk L30 L24 L23 L22 L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit lpop]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      replace (KB_brk 101 (l_brk L30)) with (KB_brk' 101 0) in HB' by (vmeq_refl).
      unfold SR34, KN34. exact HB'.
  Qed.
  (* [comment removed for export] *)
  Definition at_E20 (a tid c : word) (pl : placements) (p8 sb p10 p12 p15 : word) (W : Z) (js : list word) R M mdl : Prop :=
    bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR_E20 KN_E20 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12
    /\ (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15)
    /\ ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js) 64 = Z_to_bv 64 (PBv sp)
    /\ ev (EB' a tid c pl js) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl js) 85 = Z_to_bv 64 Wdst /\ usp / 8 + CSH <= W /\ W + 8 <= SHB_HI
    /\ ev (EB' a tid c pl js) 101 = brk.

  #[using="VI VE"] Theorem s10_b34a : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR34 KN34 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10 sp p8 sb p10 p12 a W) (A10 sp sb p12 a W) a tid c pl js SR_E20 KN_E20 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_brk_ecall1) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_brk_ecall0 + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_brk_ecall0 with PC_E19. change A_brk_ecall1 with PC_E20 in HK. rg_block VI VE HB HK run34a_eq car34a_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem boot_s10a : forall a tid c pl p8 sb p10 p12 p15 js R M mdl K, 2 ^ 25 <= lim -> length js = 67%nat ->
    at_E18' a tid c pl p8 sb p10 p12 p15 js R M mdl ->
    (forall (W : Z) ks R' M' mdl', length ks = 19%nat -> at_E20 a tid c pl p8 sb p10 p12 p15 W (js ++ ks) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_brk_ecall1) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 p15 js R M mdl K Hlim Hjs HE HK. pose proof HE as (HB0 & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64).
    assert (LJ : forall R0, length (junk_c R0 memcpy_clob) = 14%nat) by (intros; reflexivity).
    apply (s10_e18 a tid c pl p8 sb p10 p12 p15 js R M mdl K Hlim Hjs HE). intros p18 R1 M1 m1 H1.
    pose proof (s10_merge _ _ _ _ _ _ _ _ _ _ _ _ _ H1) as H1m.
    set (js1 := js ++ [p18]) in *.
    assert (L1 : length js1 = 68%nat) by (unfold js1; rewrite length_app, Hjs; reflexivity).
    assert (F1 : ev (EB' a tid c pl js1) 28 = p8 /\ ev (EB' a tid c pl js1) 29 = sb /\ ev (EB' a tid c pl js1) 36 = p10 /\ ev (EB' a tid c pl js1) 38 = p12
                 /\ ev (EB' a tid c pl js1) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js1) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js1) 64 = Z_to_bv 64 (PBv sp)).
    { unfold js1. rewrite !ev_EB_app by (rewrite Hjs; lia). repeat split; assumption. }
    destruct F1 as (F28 & F29 & F36 & F38 & F62 & F63 & F64).
    apply (s10_b30a a tid c pl js1 p8 sb p10 p12 p15 R1 M1 m1 K H1m). intros R2 M2 m2 H2.
    destruct (s10_re84 a tid c pl js1 p8 sb p10 p12 p15 R2 M2 m2 L1 H2) as (H3 & E84 & SM & SL8 & SH).
    set (S := bv_unsigned (edenot (EB' a tid c pl js1) ES)) in *.
    set (W := Wsrc S) in *.
    set (js2 := js1 ++ [Z_to_bv 64 W]) in *.
    assert (L2 : length js2 = 69%nat) by (unfold js2; rewrite length_app, L1; reflexivity).
    pose proof SLo' as SLo.
    assert (WL : usp / 8 + CSH <= W).
    { unfold W, Wsrc, CSH. pose proof (Z.div_mod (S / 8 + 24 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (S / 8 + 24 + 2147450880) 8 ltac:(lia)).
      assert (usp / 8 + 1 <= S / 8) by (pose proof (Z.div_le_mono (usp + 1 * 8) S 8 ltac:(lia) ltac:(lia)) as DL; rewrite Z.div_add in DL by lia; exact DL). lia. }
    assert (WH : W + 8 <= SHB_HI).
    { unfold W, Wsrc, CSH, SHB_HI. pose proof (Z.div_mod (S / 8 + 24 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (S / 8 + 24 + 2147450880) 8 ltac:(lia)).
      assert (S / 8 <= 2 ^ 44 - 25) by (apply Z.div_le_upper_bound; lia). lia. }
    assert (WM : W mod 8 = 0) by (unfold W, Wsrc; apply Z_mod_mult).
    assert (G : ev (EB' a tid c pl js2) 28 = p8 /\ ev (EB' a tid c pl js2) 29 = sb /\ ev (EB' a tid c pl js2) 36 = p10 /\ ev (EB' a tid c pl js2) 38 = p12
                /\ ev (EB' a tid c pl js2) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js2) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js2) 64 = Z_to_bv 64 (PBv sp)).
    { unfold js2. rewrite !ev_EB_app by (rewrite L1; lia). repeat split; assumption. }
    destruct G as (G28 & G29 & G36 & G38 & G62 & G63 & G64).
    pose proof (s10_x84 a tid c pl js2 p8 sb p10 p12 p15 R2 M2 m2 W Hlim G28 G38 Hsb E84 WM WL WH H3) as H4.
    apply (s10_b31a a tid c pl js2 p8 sb p10 p12 p15 R2 M2 m2 K W H4). intros R3 M3 m3 H5.
    destruct (s10_re85 a tid c pl js2 p8 sb p10 p12 p15 R3 M3 m3 W L2 H5) as (H6 & E85).
    set (js3 := js2 ++ [Z_to_bv 64 Wdst]) in *.
    assert (L3 : length js3 = 70%nat) by (unfold js3; rewrite length_app, L2; reflexivity).
    assert (G' : ev (EB' a tid c pl js3) 28 = p8 /\ ev (EB' a tid c pl js3) 29 = sb /\ ev (EB' a tid c pl js3) 36 = p10 /\ ev (EB' a tid c pl js3) 38 = p12
                 /\ ev (EB' a tid c pl js3) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js3) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js3) 64 = Z_to_bv 64 (PBv sp)
                 /\ ev (EB' a tid c pl js3) 84 = Z_to_bv 64 W).
    { unfold js3. rewrite !ev_EB_app by (rewrite L2; lia). repeat split; assumption. }
    destruct G' as (I28 & I29 & I36 & I38 & I62 & I63 & I64 & I84).
    pose proof (s10_x85 a tid c pl js3 p8 sb p10 p12 p15 R3 M3 m3 W Hlim I28 I38 WL E85 H6) as H7.
    apply (s10_b32a a tid c pl js3 p8 sb p10 p12 p15 R3 M3 m3 K W H7). intros R4 M4 m4 H8'.
    apply (s10_mc a tid c pl js3 p8 sb p10 p12 p15 R4 M4 m4 K W L3 H8'). intros R5 M5 m5 w H9'.
    set (js4 := (js3 ++ [w]) ++ junk_c R5 memcpy_clob) in *.
    assert (L4 : length js4 = 85%nat) by (unfold js4; rewrite !length_app, L3, LJ; reflexivity).
    assert (J : ev (EB' a tid c pl js4) 28 = p8 /\ ev (EB' a tid c pl js4) 29 = sb /\ ev (EB' a tid c pl js4) 36 = p10 /\ ev (EB' a tid c pl js4) 38 = p12
                /\ ev (EB' a tid c pl js4) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js4) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js4) 64 = Z_to_bv 64 (PBv sp)
                /\ ev (EB' a tid c pl js4) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl js4) 85 = Z_to_bv 64 Wdst).
    { unfold js4. rewrite <- app_assoc. rewrite !ev_EB_app by (rewrite L3; lia). repeat split; assumption. }
    destruct J as (J28 & J29 & J36 & J38 & J62 & J63 & J64 & J84 & J85).
    apply (s10_b33a a tid c pl js4 p8 sb p10 p12 p15 R5 M5 m5 K W H9'). intros R6 M6 m6 H10'.
    apply (s10_e19 a tid c pl js4 p8 sb p10 p12 p15 R6 M6 m6 K W L4 H10'). intros R7 H11.
    set (js5 := js4 ++ [brk]) in *.
    assert (N : ev (EB' a tid c pl js5) 28 = p8 /\ ev (EB' a tid c pl js5) 29 = sb /\ ev (EB' a tid c pl js5) 36 = p10 /\ ev (EB' a tid c pl js5) 38 = p12
                /\ ev (EB' a tid c pl js5) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js5) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js5) 64 = Z_to_bv 64 (PBv sp)
                /\ ev (EB' a tid c pl js5) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl js5) 85 = Z_to_bv 64 Wdst).
    { unfold js5. rewrite !ev_EB_app by (rewrite L4; lia). repeat split; assumption. }
    destruct N as (N28 & N29 & N36 & N38 & N62 & N63 & N64 & N84 & N85).
    assert (N101 : ev (EB' a tid c pl js5) 101 = brk).
    { unfold js5. replace 101%nat with (16 + 85)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 85), app_nth2, L4 by lia. reflexivity. }
    apply (s10_b34a a tid c pl js5 p8 sb p10 p12 p15 R7 M6 m6 K W H11). intros R8 M8 m8 H12.
    apply (HK W (((([p18] ++ [Z_to_bv 64 W]) ++ [Z_to_bv 64 Wdst]) ++ [w] ++ junk_c R5 memcpy_clob) ++ [brk]) R8 M8 m8).
    + rewrite !length_app, LJ. reflexivity.
    + unfold js5, js4, js3, js2, js1 in *. rewrite <- !app_assoc in *. split; [exact H12 | repeat split; assumption].
  Qed.
End Theorems.
