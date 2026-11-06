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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKn2__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootArith__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKn2__Lib.AsanBootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4f__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn7a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS3 BootS4 BootS5 BootS6 BootS7 BootS8. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS9 BootNodes5. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4a__A3.BootKn4a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn6a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn7a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn8a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes5.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes6. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS10a. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn10a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10a.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes7. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootT0 BootS10b BootNodesT. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn10b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootT0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodesT.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKn2__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKn2__Lib.AsanBootKn4.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots11w1_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
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
  #[local] Notation at_T0' := (at_T0 sp brk mbase draw lim inp).

  #[using="brk mbase draw inp VI VE"] Lemma SA16c : usp mod 16 = 0. Proof. exact (SA16 sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SLoc : 0x7fff80000000 <= usp. Proof. exact (SL sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SHic : usp <= 2 ^ 47. Proof. exact (SH sp brk mbase draw inp VI VE). Qed.

  #[local] Notation H10' := (H10 sp sp).
  #[local] Notation A10' := (A10 sp sp).
  #[local] Notation LT0 := (L_T0).
  (* [comment removed for export] *)
  Definition WORLD_OK : Prop := STv sp <= usp - 96.

  #[using="VI VE"] Theorem s11_bTa : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W lb : Z), WORLD_OK ->
    ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_T0 KN_T0 (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTa KNTa (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_trace_ld) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC_T0) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb HW E62 HB HK. change A_trace_ld with PCTa in HK.
    pose proof (x9_facts sp SA16c SLoc SHic) as (X1 & X2 & X3 & X4 & X5 & _).
    pose proof SLoc as SLo. pose proof SHic as SHi.
    assert (E0v : ev (EB' a tid c pl js) 0 = sp) by apply ev_EB_sp.
    rg_block_sc VI VE HB HK runTa_eq carTa_eq ltac:(idtac).
    - cbn [branch_taken]. unfold bv_ltu. apply negb_true_iff. apply Z.ltb_ge.
      rewrite (lin1_val _ 0 (-112)) by (rewrite E0v; unfold usp in *; lia). rewrite (lin1_val _ 62 (-16)) by (rewrite E62, u_small by lia; lia).
      rewrite E0v, E62, u_small by lia. unfold WORLD_OK, usp in *. lia.
    - cbn [branch_taken]. unfold bv_ltu. apply negb_false_iff. apply Z.ltb_lt.
      rewrite (lin1_val _ 62 (-8388608)) by (rewrite E62, u_small by lia; lia). rewrite (lin1_val _ 0 (-112)) by (rewrite E0v; unfold usp in *; lia).
      rewrite E0v, E62, u_small by lia. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem s11_merge : forall a tid c pl js p8 sb p10 p12 p15 R M mdl (W lb : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTa KNTa (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTa KNTam (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl W lb HB. rewrite <- KNTam_eq.
    eapply bootS_reknow; [exact HB | auto |]. intros HKN. apply kn_merge44_sound; [exact mergeTa_ok | exact HKN].
  Qed.

  #[using="VI VE"] Theorem s11_bTb : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W lb : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTa KNTam (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTb KNTb (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_trace_ld) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb HB HK. change A_trace_ld with PCTa. change A_internal_mmap_ecall with PCTb in HK. rg_block VI VE HB HK runTb_eq carTb_eq. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma budget11 : forall a tid c pl js p8 sb p12 (W : Z) H A sr kn (L : ledger) pre hc lz R M mdl, 2 ^ 25 <= lim ->
    l_maps L = pre ++ l_maps L20 ->
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    15450112 + 12288 + 1048576 + 8192 + 16384 + 782336 + A_bytes (A10' sb p12 a W) <= lim.
  Proof.
    intros a tid c pl js p8 sb p12 W H A sr kn L pre hc lz R M mdl Hlim HLm HB E28 E38.
    pose proof SLoc as SLo. pose proof SHic as SHi.
    pose proof (p12_factsG sp brk mbase draw lim inp L pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLm HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (shk_facts sp SA16c SLoc SHic) as (_ & _ & _ & _ & _ & _ & _ & Y8 & _).
    assert (B12 : PHI12 p12 - PLO12 p12 <= 12288).
    { clear - Q1 Q4 Q2 Q3 SHi. destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia. }
    cbn [A_bytes A10 A9 A9a A8 A7 A5 fst snd]. unfold HWLO, TPG, NSW.
    clear - Hlim Y8 B12. lia.
  Qed.

  #[local] Notation L1 lb := (lgrant (LT0 lb) 104 1048576).
  #[using="Type"] Lemma LT0_maps : forall lb, l_maps (LT0 lb) = [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] ++ l_maps L20.
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s11_e23 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W lb : Z), 2 ^ 25 <= lim -> length js = 88%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTb KNTb (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall p R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl (js ++ [p]) SRTbg KNTbg (L1 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 104%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget11 a tid c pl js p8 sb p12 W _ _ _ _ (LT0 lb) _ _ _ R M mdl Hlim (LT0_maps lb) HB E28 E38) as BUD.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTb KNTb (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) 1048576 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - change (page_round_up_Z 1048576) with 1048576. change (l_eager (LT0 lb)) with (15450112 + 12288). clear - BUD. lia.
    - change (page_round_up_Z 1048576) with 1048576. rewrite (eq_refl : l_maps (LT0 lb) = (EVar 103, 4096) :: (EVar 102, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. apply (HK p). unfold SRTbg.
      unfold kn_grant in HB'. change (page_round_up_Z 1048576) with 1048576 in HB'. rewrite DS_T0_std, KNTbg_eq in HB'. exact HB'.
  Qed.

  #[using="VI VE"] Theorem s11_bTc : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W lb : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTbg KNTbg (L1 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTc KNTc (L1 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb HB HK. change A_internal_mmap_ecall with PCTb at 1. change A_internal_mmap_ecall with PCTc in HK. rg_block VI VE HB HK runTc_eq carTc_eq. Qed.

  #[local] Notation L2 lb := (lgrant_nr (L1 lb) 105 8388608).
  #[local] Notation H11 p8 sb p10 p12 a W p24 := (hcut (hjoin (H10' p8 sb p10 p12 a W) p24 8388608) (bv_unsigned p24) 4096).
  #[local] Notation A11 sb p12 a W p24 := ((bv_unsigned p24, bv_unsigned p24 + 4096) :: A10' sb p12 a W).
  #[local] Notation hc11 p8 p10 p24 := ((bv_unsigned p24, bv_unsigned p24 + 8388608, Some (Z_to_bv 8 0)) :: hc6 p8 p10).
  #[local] Notation LZ11 p8 sb p10 p15 p24 := ((p24, Z_to_bv 64 8388608) :: LZ30 sp p8 sb p10 p15).
  #[using="Type"] Lemma DS_T1_std : forall lb, DS_std (L1 lb) = DS_T1. Proof. intros lb. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s11_e24 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W lb : Z), 2 ^ 25 <= lim -> length js = 89%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTc KNTc (L1 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall p24 R' M' mdl', bootS' (H11 p8 sb p10 p12 a W p24) (A11 sb p12 a W p24) a tid c pl (js ++ [p24]) SRTcg KNTcx (L2 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 105%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget11 a tid c pl js p8 sb p12 W _ _ _ _ (L1 lb) ((EVar 104, 1048576) :: [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)]) _ _ R M mdl Hlim eq_refl HB E28 E38) as BUD.
    eapply (bs_mmap_rw_nr sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTc KNTc (L1 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) 8388608 16418 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - change (page_round_up_Z 8388608) with 8388608. clear. lia.
    - change (page_round_up_Z 8388608) with 8388608. rewrite (eq_refl : l_maps (L1 lb) = (EVar 104, 1048576) :: (EVar 103, 4096) :: (EVar 102, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. change (page_round_up_Z 8388608) with 8388608 in HB'.
      unfold kn_grant_none in HB'. rewrite DS_T1_std, KNTcg_eq in HB'.
      apply (HK p R' M' mdl'). rewrite <- KNTcx_eq. unfold xpose, SRTcg.
      assert (E105 : ev (EB' a tid c pl (js ++ [p])) 105 = p) by exact (ev_last sp draw inp a tid c pl js p 89 Hjs).
      pose proof HB' as [_ _ _ _ _ _ _ HMO _ _ _ _]. unfold maps_ok in HMO. apply Forall_cons_iff in HMO as [MO _].
      unfold map_ok in MO. cbn [fst snd edenot] in MO. change (ev (EB sp draw inp a tid c pl (js ++ [p])) 105) with (ev (EB' a tid c pl (js ++ [p])) 105) in MO. rewrite E105 in MO.
      destruct MO as (Mal & M4k & _ & Mtop & _).
      pose proof (bs_expose2 sp brk mbase draw lim inp VI VE _ _ a tid c pl (js ++ [p]) _ _ _ _ _ R' M' mdl' (EVar 105) 0 4096 (bv_unsigned p) 4096 (bv_unsigned p) (bv_unsigned p + 8388608) HB') as X.
      cbv zeta in X. cbn [edenot] in X. change (ev (EB sp draw inp a tid c pl (js ++ [p])) 105) with (ev (EB' a tid c pl (js ++ [p])) 105) in X. rewrite E105, Z.add_0_r in X.
      apply X; clear X.
      + exact Mal.
      + reflexivity.
      + clear; lia.
      + clear - M4k; lia.
      + clear - Mtop. unfold stack_max_size in *. lia.
      + clear; lia.
      + clear; lia.
      + clear; lia.
      + intros x Hx. apply hjoin_new. clear - Hx. lia.
      + left. reflexivity.
      + clear; lia.
      + clear; lia.
      + change (l_eager (L2 lb)) with (15450112 + 12288 + 1048576). clear - BUD. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="brk mbase draw inp VI VE"] Lemma H10_hidden_img : forall p8 sb p10 p12 a (W : Z) (x : word),
    bv_unsigned sb = SBV p8 -> SHB_HI <= bv_unsigned p8 -> IMG_HI <= bv_unsigned p12 ->
    (bv_unsigned x < TSH a \/ TSH a + 60 <= bv_unsigned x) -> usp / 8 + CSH <= W ->
    0x7fffa000 <= bv_unsigned x < 0x800b8600 -> H10' p8 sb p10 p12 a W x = true.
  Proof.
    intros p8 sb p10 p12 a W x Hsb P2 Q2 HT WL Hx.
    pose proof SLoc as SLo. pose proof SHic as SHi.
    unfold SHB_HI, IMG_HI, SBV, CSH, A_img_lo, A_img_hi in *.
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    assert (SPD : 17591917608960 <= usp / 8) by (pose proof (Z.div_le_mono 0x7fff80000000 usp 8 ltac:(lia) ltac:(lia)) as DL; change (0x7fff80000000 / 8) with 17591917608960 in DL; exact DL).
    unfold H10. apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ left. unfold Wdst, CSH. fold usp. pose proof (Z.div_mod (usp / 8 - 62 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (usp / 8 - 62 + 2147450880) 8 ltac:(lia)). lia. }
    apply (proj2 (hcut_true _ _ _ _)). split; [| left; lia].
    unfold H9. apply (proj2 (hcut_true _ _ _ _)). split; [| exact HT].
    unfold H9a. apply hhide_old. unfold H8, H7, H6, H5, H4, H3.
    apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ left. unfold SHK. pose proof (Z.div_le_mono (0x7fff80000000 - 800) (bv_unsigned sp - 800) 8 ltac:(lia) ltac:(unfold usp in *; lia)) as DL. change ((0x7fff80000000 - 800) / 8) with 17591917608860 in DL. lia. }
    apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ left. unfold SH12. pose proof (Z.div_le_mono 6303744 (bv_unsigned p12) 8 ltac:(lia) ltac:(lia)) as DL. change (6303744 / 8) with 787968 in DL. lia. }
    apply hjoin_old. apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ left. unfold SHRI, RI. pose proof (Z.div_le_mono (2 ^ 37) (bv_unsigned sb + 2 ^ 37) 8 ltac:(lia) ltac:(lia)) as DL. change (2 ^ 37 / 8) with 17179869184 in DL. lia. }
    apply (proj2 (hcut_true _ _ _ _)). split; [| left; unfold RI; lia].
    apply hjoin_old. apply H2_in. unfold SHB_LO, SHB_HI. lia.
  Qed.

  #[using="VI VE"] Theorem s11_bTd : forall a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K (W lb : Z),
    bootS' (H11 p8 sb p10 p12 a W p24) (A11 sb p12 a W p24) a tid c pl js SRTcg KNTcx (L2 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl ->
    (forall R' M' mdl', bootS' (H11 p8 sb p10 p12 a W p24) (A11 sb p12 a W p24) a tid c pl js SRTd KNTd (L2 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K W lb HB HK. change A_internal_mmap_ecall with PCTc at 1. change A_internal_mmap_ecall with PCTd in HK. rg_block VI VE HB HK runTd_eq carTd_eq. Qed.

  (* [comment removed for export] *)
  #[using="usp"] Lemma p24_apart : forall H A a tid c pl js sr kn lb hc lz R M mdl p24,
    bootS' H A a tid c pl js sr kn (L2 lb) hc lz R M mdl -> ev (EB' a tid c pl js) 105 = p24 ->
    bv_unsigned p24 + 8388608 <= SHB_LO \/ SHB_HI <= bv_unsigned p24.
  Proof.
    intros H A a tid c pl js sr kn lb hc lz R M mdl p24 HB E105.
    destruct HB as [_ _ _ _ _ _ F _ _ _ _ _].
    assert (EV105 : edenot (EB' a tid c pl js) (EVar 105) = p24) by exact E105.
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. clear F.
    change (l_maps (L2 lb)) with ((EVar 105, 8388608) :: (EVar 104, 1048576) :: (EVar 103, 4096) :: (EVar 102, 8192) :: l_maps L30) in AP. rewrite L30_maps in AP.
    cbn [dl List.map fst snd ivs_apart] in AP. destruct AP as [AP _]. rewrite EV105 in AP.
    do 12 (apply Forall_cons_iff in AP as [_ AP]).
    apply Forall_cons_iff in AP as [X1 AP]. apply Forall_cons_iff in AP as [X2 AP]. apply Forall_cons_iff in AP as [X3 _].
    cbn [fst snd edenot] in X1, X2, X3.
    change (bv_unsigned (Z_to_bv 64 8388608)) with 8388608 in *.
    change (bv_unsigned (Z_to_bv 64 2201439137792)) with 2201439137792 in *. change (bv_unsigned (Z_to_bv 64 15392894357504)) with 15392894357504 in *.
    change (bv_unsigned (Z_to_bv 64 2415882240)) with 2415882240 in *. change (bv_unsigned (Z_to_bv 64 2199023255552)) with 2199023255552 in *.
    change (bv_unsigned (Z_to_bv 64 2147446784)) with 2147446784 in *. change (bv_unsigned (Z_to_bv 64 268435456)) with 268435456 in *.
    unfold SHB_LO, SHB_HI. pose proof (u64_range p24). lia.
  Qed.

  #[local] Notation L3 lb := (lgrant (L2 lb) 106 4096).
  #[local] Notation H12 p8 sb p10 p12 a W p24 := (hcut (H11 p8 sb p10 p12 a W p24) 0x7fffa000 779776).
  #[local] Notation A12 sb p12 a W p24 := ((0x7fffa000, 0x7fffa000 + 782336) :: A11 sb p12 a W p24).
  #[using="Type"] Lemma DS_T2_std : forall lb, DS_std (L2 lb) = DS_T2. Proof. intros lb. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s11_e25 : forall a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K (W lb : Z), 2 ^ 25 <= lim -> length js = 90%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> bv_unsigned sb = SBV p8 -> usp / 8 + CSH <= W ->
    (bv_unsigned p24 + 8388608 <= SHB_LO \/ SHB_HI <= bv_unsigned p24) ->
    bootS' (H11 p8 sb p10 p12 a W p24) (A11 sb p12 a W p24) a tid c pl js SRTd KNTd (L2 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl ->
    (forall p25 R' M' mdl', bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl (js ++ [p25]) SRTdg KNTdx3 (L3 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K W lb Hlim Hjs E28 E38 Hsb WL AP24 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 106%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof SLoc as SLo. pose proof SHic as SHi.
    pose proof (budget11 a tid c pl js p8 sb p12 W _ _ _ _ (L2 lb) ((EVar 105, 8388608) :: (EVar 104, 1048576) :: [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)]) _ _ R M mdl Hlim eq_refl HB E28 E38) as BUD.
    pose proof (p8_factsG sp brk mbase draw lim inp (L2 lb) ((EVar 105, 8388608) :: (EVar 104, 1048576) :: [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)]) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    pose proof (p12_factsG sp brk mbase draw lim inp (L2 lb) ((EVar 105, 8388608) :: (EVar 104, 1048576) :: [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)]) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    assert (T4 : bv_unsigned a = A_builtin_tls) by (destruct HB as [_ _ _ _ _ _ _ _ _ HT _ _]; exact (proj2 (proj2 (proj2 HT)))).
    assert (TSHc : TSH a = 2148221854) by (unfold TSH, CSH; rewrite T4; reflexivity).
    (* The image shadow is hidden except the TLS block's shadow (builtin_tls lies in the image). *)
    assert (HID : forall x : word, 0x7fffa000 <= bv_unsigned x < 0x800b8600 -> (bv_unsigned x < TSH a \/ TSH a + 60 <= bv_unsigned x) ->
                  H11 p8 sb p10 p12 a W p24 x = true).
    { intros x Hx HT. apply (proj2 (hcut_true _ _ _ _)). split; [apply hjoin_old; apply (H10_hidden_img p8 sb p10 p12 a W x Hsb P2 Q2 HT WL Hx)|].
      clear - AP24 Hx. unfold SHB_LO, SHB_HI in *. lia. }
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H11 p8 sb p10 p12 a W p24) (A11 sb p12 a W p24) a tid c pl js SRTd KNTd (L2 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) 4096 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - change (page_round_up_Z 4096) with 4096. change (l_eager (L2 lb)) with (15450112 + 12288 + 1048576). cbn [A_bytes fst snd]. clear - BUD. lia.
    - change (page_round_up_Z 4096) with 4096. rewrite (eq_refl : l_maps (L2 lb) = (EVar 105, 8388608) :: (EVar 104, 1048576) :: (EVar 103, 4096) :: (EVar 102, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. apply (HK p R' M' mdl'). unfold SRTdg.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_T2_std, KNTdg_eq in HB'.
      (* The TLS block's shadow is visible and zero (the TLS set-up cleared it): the KFill entry. *)
      assert (TZ : forall x : word, TSH a <= bv_unsigned x < TSH a + 60 -> mrestrict (H11 p8 sb p10 p12 a W p24) M' x = Some (Z_to_bv 8 0)).
      { pose proof HB' as [_ HKN _ _ _ _ _ _ _ _ _ _].
        pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.know_ok_sub_b SEGS _ _ KNTdg [KFill (SA (ELit 0) TSHL) (ELit 60) 0]
                      ltac:(vm_compute; reflexivity) HKN) as KF.
        apply Forall_inv in KF. destruct KF as [_ KF].
        assert (ES : estart (EB' a tid c pl (js ++ [p])) (SA (ELit 0) TSHL) = 2148221854) by reflexivity.
        assert (EL : elenZ (EB' a tid c pl (js ++ [p])) (ELit 60) = 60) by reflexivity.
        rewrite ES, EL in KF. intros x Hx. rewrite TSHc in Hx.
        specialize (KF (bv_unsigned x - 2148221854) ltac:(lia)).
        replace (2148221854 + (bv_unsigned x - 2148221854)) with (bv_unsigned x) in KF by lia.
        rewrite Z_to_bv_bv_unsigned in KF. exact KF. }
      rewrite <- KNTdx3_eq. unfold xpose, ISH_LO, ISH_LEN.
      pose proof (bs_expose3 sp brk mbase draw lim inp VI VE _ _ a tid c pl (js ++ [p]) _ _ _ _ _ R' M' mdl' (ELit 0) 0x7fffa000 779776 0x7fffa000 782336 SHB_LO (SHB_LO + 2 ^ 28) HB') as X3.
      cbv zeta in X3. cbn [edenot] in X3. change (bv_unsigned (Z_to_bv 64 0) + 2147459072) with 2147459072 in X3.
      apply X3; clear X3.
      + reflexivity.
      + reflexivity.
      + clear; lia.
      + clear; lia.
      + clear - SLo; unfold stack_max_size, usp in *; lia.
      + clear; lia.
      + clear; lia.
      + clear; lia.
      + intros x Hx. destruct (Z.lt_ge_cases (bv_unsigned x) (TSH a)) as [L|L].
        * left. apply HID; [clear - Hx; lia | left; exact L].
        * destruct (Z.lt_ge_cases (bv_unsigned x) (TSH a + 60)) as [L2|L2].
          -- right. apply TZ. lia.
          -- left. apply HID; [clear - Hx; lia | right; exact L2].
      + do 4 right; left; reflexivity.
      + unfold SHB_LO; clear; lia.
      + unfold SHB_LO; clear; lia.
      + change (l_eager (L3 lb)) with (15450112 + 12288 + 1048576 + 4096). cbn [A_bytes fst snd]. clear - BUD. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s11_bTe : forall a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K (W lb : Z),
    bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SRTdg KNTdx3 (L3 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl ->
    (forall R' M' mdl', bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SRTe KNTe (L3 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K W lb HB HK. change A_internal_mmap_ecall with PCTd at 1. change A_internal_mmap_ecall with PCTe in HK. rg_block VI VE HB HK runTe_eq carTe_eq. Qed.

  #[local] Notation L4 lb := (lgrant (L3 lb) 107 4096).
  #[using="Type"] Lemma DS_T3_std : forall lb, DS_std (L3 lb) = DS_T3. Proof. intros lb. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s11_e26 : forall a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K (W lb : Z), 2 ^ 25 <= lim -> length js = 91%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SRTe KNTe (L3 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl ->
    (forall p26 R' M' mdl', bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl (js ++ [p26]) SRTeg KNTeg (L4 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K W lb Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 107%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget11 a tid c pl js p8 sb p12 W _ _ _ _ (L3 lb) ((EVar 106, 4096) :: (EVar 105, 8388608) :: (EVar 104, 1048576) :: [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)]) _ _ R M mdl Hlim eq_refl HB E28 E38) as BUD.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SRTe KNTe (L3 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) 4096 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - change (page_round_up_Z 4096) with 4096. change (l_eager (L3 lb)) with (15450112 + 12288 + 1048576 + 4096). cbn [A_bytes fst snd]. clear - BUD. lia.
    - change (page_round_up_Z 4096) with 4096. rewrite (eq_refl : l_maps (L3 lb) = (EVar 106, 4096) :: (EVar 105, 8388608) :: (EVar 104, 1048576) :: (EVar 103, 4096) :: (EVar 102, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. apply (HK p). unfold SRTeg.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_T3_std, KNTeg_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s11_bTf : forall a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K (W lb : Z),
    bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SRTeg KNTeg (L4 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl ->
    (forall R' M' mdl', bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SR_MAIN KN_MAIN (L4 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_main) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K W lb HB HK. change A_internal_mmap_ecall with PCTe. change A_main with PC_MAIN in HK. rg_block VI VE HB HK runTf_eq carTf_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition at_main (a tid c : word) (pl : placements) (p8 sb p10 p12 p15 p24 : word) (W lb : Z) (js : list word)
      (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) : Prop :=
    bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SR_MAIN KN_MAIN (L4 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl
    /\ WORLD_OK /\ (lb = 0 \/ lb = 8192)
    /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12
    /\ (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15)
    /\ ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js) 64 = Z_to_bv 64 (PBv sp)
    /\ ev (EB' a tid c pl js) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl js) 85 = Z_to_bv 64 (Wdst sp) /\ usp / 8 + CSH <= W /\ W + 8 <= SHB_HI
    /\ ev (EB' a tid c pl js) 101 = brk
    /\ ev (EB' a tid c pl js) 105 = p24 /\ (bv_unsigned p24 + 8388608 <= SHB_LO \/ SHB_HI <= bv_unsigned p24).

  #[using="VI VE"] Theorem boot_s11 : forall a tid c pl p8 sb p10 p12 p15 (W lb : Z) js R M mdl K, 2 ^ 25 <= lim -> length js = 88%nat -> WORLD_OK ->
    at_T0' a tid c pl p8 sb p10 p12 p15 W lb js R M mdl ->
    (forall (p24 : word) ks R' M' mdl', length ks = 4%nat ->
       at_main a tid c pl p8 sb p10 p12 p15 p24 W lb (js ++ ks) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_main) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC_T0) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 p15 W lb js R M mdl K Hlim Hjs HW HE HK.
    destruct HE as (HB0 & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101).
    assert (CARRY : forall ks, ev (EB' a tid c pl (js ++ ks)) 28 = p8 /\ ev (EB' a tid c pl (js ++ ks)) 29 = sb /\ ev (EB' a tid c pl (js ++ ks)) 36 = p10
                     /\ ev (EB' a tid c pl (js ++ ks)) 38 = p12 /\ ev (EB' a tid c pl (js ++ ks)) 62 = Z_to_bv 64 (STv sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl (js ++ ks)) 64 = Z_to_bv 64 (PBv sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl (js ++ ks)) 85 = Z_to_bv 64 (Wdst sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 101 = brk).
    { intros ks. rewrite !ev_EB_app by (rewrite Hjs; lia). repeat split; assumption. }
    apply (s11_bTa a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb HW E62 HB0). intros R1 M1 m1 H1.
    pose proof (s11_merge a tid c pl js p8 sb p10 p12 p15 R1 M1 m1 W lb H1) as H1m.
    apply (s11_bTb a tid c pl js p8 sb p10 p12 p15 R1 M1 m1 K W lb H1m). intros R2 M2 m2 H2.
    apply (s11_e23 a tid c pl js p8 sb p10 p12 p15 R2 M2 m2 K W lb Hlim Hjs E28 E38 H2). intros p23 R3 M3 m3 H3.
    set (js1 := js ++ [p23]) in *.
    assert (L1' : length js1 = 89%nat) by (unfold js1; rewrite length_app, Hjs; reflexivity).
    destruct (CARRY [p23]) as (F28 & _ & _ & F38 & _). fold js1 in F28, F38.
    apply (s11_bTc a tid c pl js1 p8 sb p10 p12 p15 R3 M3 m3 K W lb H3). intros R4 M4 m4 H4.
    apply (s11_e24 a tid c pl js1 p8 sb p10 p12 p15 R4 M4 m4 K W lb Hlim L1' F28 F38 H4). intros p24 R5 M5 m5 H5.
    set (js2 := js1 ++ [p24]) in *.
    assert (L2' : length js2 = 90%nat) by (unfold js2; rewrite length_app, L1'; reflexivity).
    assert (G105 : ev (EB' a tid c pl js2) 105 = p24) by (unfold js2; exact (ev_last sp draw inp a tid c pl js1 p24 89 L1')).
    assert (G : ev (EB' a tid c pl js2) 28 = p8 /\ ev (EB' a tid c pl js2) 38 = p12).
    { unfold js2, js1. rewrite <- app_assoc. destruct (CARRY ([p23] ++ [p24])) as (G28 & _ & _ & G38 & _). split; assumption. }
    destruct G as (G28 & G38).
    pose proof (p24_apart _ _ a tid c pl js2 _ _ lb _ _ R5 M5 m5 p24 H5 G105) as AP24.
    apply (s11_bTd a tid c pl js2 p8 sb p10 p12 p15 p24 R5 M5 m5 K W lb H5). intros R6 M6 m6 H6.
    apply (s11_e25 a tid c pl js2 p8 sb p10 p12 p15 p24 R6 M6 m6 K W lb Hlim L2' G28 G38 Hsb WL AP24 H6). intros p25 R7 M7 m7 H7.
    set (js3 := js2 ++ [p25]) in *.
    assert (L3' : length js3 = 91%nat) by (unfold js3; rewrite length_app, L2'; reflexivity).
    assert (I : ev (EB' a tid c pl js3) 28 = p8 /\ ev (EB' a tid c pl js3) 38 = p12).
    { unfold js3, js2, js1. rewrite <- !app_assoc. destruct (CARRY ([p23] ++ [p24] ++ [p25])) as (I28 & _ & _ & I38 & _). split; assumption. }
    destruct I as (I28 & I38).
    apply (s11_bTe a tid c pl js3 p8 sb p10 p12 p15 p24 R7 M7 m7 K W lb H7). intros R8 M8 m8 H8.
    apply (s11_e26 a tid c pl js3 p8 sb p10 p12 p15 p24 R8 M8 m8 K W lb Hlim L3' I28 I38 H8). intros p26 R9 M9 m9 H9.
    apply (s11_bTf a tid c pl (js3 ++ [p26]) p8 sb p10 p12 p15 p24 R9 M9 m9 K W lb H9). intros R10 M10 m10 H10.
    apply (HK p24 ([p23] ++ [p24] ++ [p25] ++ [p26]) R10 M10 m10); [reflexivity|].
    assert (EQ : js ++ [p23] ++ [p24] ++ [p25] ++ [p26] = js3 ++ [p26]) by (unfold js3, js2, js1; rewrite <- !app_assoc; reflexivity).
    unfold at_main. rewrite EQ. split; [exact H10|]. split; [exact HW|]. split; [exact Hlb|]. split; [exact Hsb|].
    rewrite <- EQ. destruct (CARRY ([p23] ++ [p24] ++ [p25] ++ [p26])) as (J28 & J29 & J36 & J38 & J62 & J63 & J64 & J84 & J85 & J101).
    assert (J105 : ev (EB' a tid c pl (js ++ [p23] ++ [p24] ++ [p25] ++ [p26])) 105 = p24).
    { replace (js ++ [p23] ++ [p24] ++ [p25] ++ [p26]) with (js2 ++ ([p25] ++ [p26])) by (unfold js2, js1; rewrite <- !app_assoc; reflexivity).
      rewrite ev_EB_app by (rewrite L2'; lia). exact G105. }
    repeat split; assumption.
  Qed.

End Theorems.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn3c__B3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS5 BootS6 BootS7 BootS9 BootS10a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn10b__B3.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKn2__Lib.AsanBootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn4a. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn6a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn7a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn8a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS4.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS7. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW4.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS9. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes5.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW5.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes6.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn10a.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS10a.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm3.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes7.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn10b. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootT0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10b.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodesT.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKn2__Lib.AsanBootKn4.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots11w1_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
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
  #[local] Notation at_T0' := (at_T0 sp brk mbase draw lim inp).

  #[using="brk mbase draw inp VI VE"] Lemma SA16c : usp mod 16 = 0. Proof. exact (SA16 sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SLoc : 0x7fff80000000 <= usp. Proof. exact (SL sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SHic : usp <= 2 ^ 47. Proof. exact (SH sp brk mbase draw inp VI VE). Qed.

  #[local] Notation H10' := (H10 sp sp).
  #[local] Notation A10' := (A10 sp sp).
  #[local] Notation LT0 := (L_T0).
  (* [comment removed for export] *)
  Definition WORLD_OK : Prop := STv sp <= usp - 96.

  #[using="VI VE"] Theorem s11_bTa : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W lb : Z), WORLD_OK ->
    ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_T0 KN_T0 (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTa KNTa (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_trace_ld) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC_T0) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb HW E62 HB HK. change A_trace_ld with PCTa in HK.
    pose proof (x9_facts sp SA16c SLoc SHic) as (X1 & X2 & X3 & X4 & X5 & _).
    pose proof SLoc as SLo. pose proof SHic as SHi.
    assert (E0v : ev (EB' a tid c pl js) 0 = sp) by apply ev_EB_sp.
    rg_block_sc VI VE HB HK runTa_eq carTa_eq ltac:(idtac).
    - cbn [branch_taken]. unfold bv_ltu. apply negb_true_iff. apply Z.ltb_ge.
      rewrite (lin1_val _ 0 (-112)) by (rewrite E0v; unfold usp in *; lia). rewrite (lin1_val _ 62 (-16)) by (rewrite E62, u_small by lia; lia).
      rewrite E0v, E62, u_small by lia. unfold WORLD_OK, usp in *. lia.
    - cbn [branch_taken]. unfold bv_ltu. apply negb_false_iff. apply Z.ltb_lt.
      rewrite (lin1_val _ 62 (-8388608)) by (rewrite E62, u_small by lia; lia). rewrite (lin1_val _ 0 (-112)) by (rewrite E0v; unfold usp in *; lia).
      rewrite E0v, E62, u_small by lia. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem s11_merge : forall a tid c pl js p8 sb p10 p12 p15 R M mdl (W lb : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTa KNTa (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTa KNTam (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl W lb HB. rewrite <- KNTam_eq.
    eapply bootS_reknow; [exact HB | auto |]. intros HKN. apply kn_merge44_sound; [exact mergeTa_ok | exact HKN].
  Qed.

  #[using="VI VE"] Theorem s11_bTb : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W lb : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTa KNTam (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTb KNTb (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_trace_ld) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb HB HK. change A_trace_ld with PCTa. change A_internal_mmap_ecall with PCTb in HK. rg_block VI VE HB HK runTb_eq carTb_eq. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma budget11 : forall a tid c pl js p8 sb p12 (W : Z) H A sr kn (L : ledger) pre hc lz R M mdl, 2 ^ 25 <= lim ->
    l_maps L = pre ++ l_maps L20 ->
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    15450112 + 12288 + 1048576 + 8192 + 16384 + 782336 + A_bytes (A10' sb p12 a W) <= lim.
  Proof.
    intros a tid c pl js p8 sb p12 W H A sr kn L pre hc lz R M mdl Hlim HLm HB E28 E38.
    pose proof SLoc as SLo. pose proof SHic as SHi.
    pose proof (p12_factsG sp brk mbase draw lim inp L pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLm HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (shk_facts sp SA16c SLoc SHic) as (_ & _ & _ & _ & _ & _ & _ & Y8 & _).
    assert (B12 : PHI12 p12 - PLO12 p12 <= 12288).
    { clear - Q1 Q4 Q2 Q3 SHi. destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia. }
    cbn [A_bytes A10 A9 A9a A8 A7 A5 fst snd]. unfold HWLO, TPG, NSW.
    clear - Hlim Y8 B12. lia.
  Qed.

  #[local] Notation L1 lb := (lgrant (LT0 lb) 104 1048576).
  #[using="Type"] Lemma LT0_maps : forall lb, l_maps (LT0 lb) = [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] ++ l_maps L20.
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s11_e23 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W lb : Z), 2 ^ 25 <= lim -> length js = 88%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTb KNTb (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall p R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl (js ++ [p]) SRTbg KNTbg (L1 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 104%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget11 a tid c pl js p8 sb p12 W _ _ _ _ (LT0 lb) _ _ _ R M mdl Hlim (LT0_maps lb) HB E28 E38) as BUD.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTb KNTb (LT0 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) 1048576 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - change (page_round_up_Z 1048576) with 1048576. change (l_eager (LT0 lb)) with (15450112 + 12288). clear - BUD. lia.
    - change (page_round_up_Z 1048576) with 1048576. rewrite (eq_refl : l_maps (LT0 lb) = (EVar 103, 4096) :: (EVar 102, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. apply (HK p). unfold SRTbg.
      unfold kn_grant in HB'. change (page_round_up_Z 1048576) with 1048576 in HB'. rewrite DS_T0_std, KNTbg_eq in HB'. exact HB'.
  Qed.

  #[using="VI VE"] Theorem s11_bTc : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W lb : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTbg KNTbg (L1 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTc KNTc (L1 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb HB HK. change A_internal_mmap_ecall with PCTb at 1. change A_internal_mmap_ecall with PCTc in HK. rg_block VI VE HB HK runTc_eq carTc_eq. Qed.

  #[local] Notation L2 lb := (lgrant_nr (L1 lb) 105 8388608).
  #[local] Notation H11 p8 sb p10 p12 a W p24 := (hcut (hjoin (H10' p8 sb p10 p12 a W) p24 8388608) (bv_unsigned p24) 4096).
  #[local] Notation A11 sb p12 a W p24 := ((bv_unsigned p24, bv_unsigned p24 + 4096) :: A10' sb p12 a W).
  #[local] Notation hc11 p8 p10 p24 := ((bv_unsigned p24, bv_unsigned p24 + 8388608, Some (Z_to_bv 8 0)) :: hc6 p8 p10).
  #[local] Notation LZ11 p8 sb p10 p15 p24 := ((p24, Z_to_bv 64 8388608) :: LZ30 sp p8 sb p10 p15).
  #[using="Type"] Lemma DS_T1_std : forall lb, DS_std (L1 lb) = DS_T1. Proof. intros lb. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s11_e24 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W lb : Z), 2 ^ 25 <= lim -> length js = 89%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTc KNTc (L1 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall p24 R' M' mdl', bootS' (H11 p8 sb p10 p12 a W p24) (A11 sb p12 a W p24) a tid c pl (js ++ [p24]) SRTcg KNTcx (L2 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 105%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget11 a tid c pl js p8 sb p12 W _ _ _ _ (L1 lb) ((EVar 104, 1048576) :: [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)]) _ _ R M mdl Hlim eq_refl HB E28 E38) as BUD.
    eapply (bs_mmap_rw_nr sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRTc KNTc (L1 lb) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) 8388608 16418 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - change (page_round_up_Z 8388608) with 8388608. clear. lia.
    - change (page_round_up_Z 8388608) with 8388608. rewrite (eq_refl : l_maps (L1 lb) = (EVar 104, 1048576) :: (EVar 103, 4096) :: (EVar 102, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. change (page_round_up_Z 8388608) with 8388608 in HB'.
      unfold kn_grant_none in HB'. rewrite DS_T1_std, KNTcg_eq in HB'.
      apply (HK p R' M' mdl'). rewrite <- KNTcx_eq. unfold xpose, SRTcg.
      assert (E105 : ev (EB' a tid c pl (js ++ [p])) 105 = p) by exact (ev_last sp draw inp a tid c pl js p 89 Hjs).
      pose proof HB' as [_ _ _ _ _ _ _ HMO _ _ _ _]. unfold maps_ok in HMO. apply Forall_cons_iff in HMO as [MO _].
      unfold map_ok in MO. cbn [fst snd edenot] in MO. change (ev (EB sp draw inp a tid c pl (js ++ [p])) 105) with (ev (EB' a tid c pl (js ++ [p])) 105) in MO. rewrite E105 in MO.
      destruct MO as (Mal & M4k & _ & Mtop & _).
      pose proof (bs_expose2 sp brk mbase draw lim inp VI VE _ _ a tid c pl (js ++ [p]) _ _ _ _ _ R' M' mdl' (EVar 105) 0 4096 (bv_unsigned p) 4096 (bv_unsigned p) (bv_unsigned p + 8388608) HB') as X.
      cbv zeta in X. cbn [edenot] in X. change (ev (EB sp draw inp a tid c pl (js ++ [p])) 105) with (ev (EB' a tid c pl (js ++ [p])) 105) in X. rewrite E105, Z.add_0_r in X.
      apply X; clear X.
      + exact Mal.
      + reflexivity.
      + clear; lia.
      + clear - M4k; lia.
      + clear - Mtop. unfold stack_max_size in *. lia.
      + clear; lia.
      + clear; lia.
      + clear; lia.
      + intros x Hx. apply hjoin_new. clear - Hx. lia.
      + left. reflexivity.
      + clear; lia.
      + clear; lia.
      + change (l_eager (L2 lb)) with (15450112 + 12288 + 1048576). clear - BUD. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="brk mbase draw inp VI VE"] Lemma H10_hidden_img : forall p8 sb p10 p12 a (W : Z) (x : word),
    bv_unsigned sb = SBV p8 -> SHB_HI <= bv_unsigned p8 -> IMG_HI <= bv_unsigned p12 ->
    (bv_unsigned x < TSH a \/ TSH a + 60 <= bv_unsigned x) -> usp / 8 + CSH <= W ->
    0x7fffa000 <= bv_unsigned x < 0x800b8800 -> H10' p8 sb p10 p12 a W x = true.
  Proof.
    intros p8 sb p10 p12 a W x Hsb P2 Q2 HT WL Hx.
    pose proof SLoc as SLo. pose proof SHic as SHi.
    unfold SHB_HI, IMG_HI, SBV, CSH, A_img_lo, A_img_hi in *.
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    assert (SPD : 17591917608960 <= usp / 8) by (pose proof (Z.div_le_mono 0x7fff80000000 usp 8 ltac:(lia) ltac:(lia)) as DL; change (0x7fff80000000 / 8) with 17591917608960 in DL; exact DL).
    unfold H10. apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ left. unfold Wdst, CSH. fold usp. pose proof (Z.div_mod (usp / 8 - 62 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (usp / 8 - 62 + 2147450880) 8 ltac:(lia)). lia. }
    apply (proj2 (hcut_true _ _ _ _)). split; [| left; lia].
    unfold H9. apply (proj2 (hcut_true _ _ _ _)). split; [| exact HT].
    unfold H9a. apply hhide_old. unfold H8, H7, H6, H5, H4, H3.
    apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ left. unfold SHK. pose proof (Z.div_le_mono (0x7fff80000000 - 800) (bv_unsigned sp - 800) 8 ltac:(lia) ltac:(unfold usp in *; lia)) as DL. change ((0x7fff80000000 - 800) / 8) with 17591917608860 in DL. lia. }
    apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ left. unfold SH12. pose proof (Z.div_le_mono 6307840 (bv_unsigned p12) 8 ltac:(lia) ltac:(lia)) as DL. change (6307840 / 8) with 788480 in DL. lia. }
    apply hjoin_old. apply (proj2 (hcut_true _ _ _ _)). split.
    2:{ left. unfold SHRI, RI. pose proof (Z.div_le_mono (2 ^ 37) (bv_unsigned sb + 2 ^ 37) 8 ltac:(lia) ltac:(lia)) as DL. change (2 ^ 37 / 8) with 17179869184 in DL. lia. }
    apply (proj2 (hcut_true _ _ _ _)). split; [| left; unfold RI; lia].
    apply hjoin_old. apply H2_in. unfold SHB_LO, SHB_HI. lia.
  Qed.

  #[using="VI VE"] Theorem s11_bTd : forall a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K (W lb : Z),
    bootS' (H11 p8 sb p10 p12 a W p24) (A11 sb p12 a W p24) a tid c pl js SRTcg KNTcx (L2 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl ->
    (forall R' M' mdl', bootS' (H11 p8 sb p10 p12 a W p24) (A11 sb p12 a W p24) a tid c pl js SRTd KNTd (L2 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K W lb HB HK. change A_internal_mmap_ecall with PCTc at 1. change A_internal_mmap_ecall with PCTd in HK. rg_block VI VE HB HK runTd_eq carTd_eq. Qed.

  (* [comment removed for export] *)
  #[using="usp"] Lemma p24_apart : forall H A a tid c pl js sr kn lb hc lz R M mdl p24,
    bootS' H A a tid c pl js sr kn (L2 lb) hc lz R M mdl -> ev (EB' a tid c pl js) 105 = p24 ->
    bv_unsigned p24 + 8388608 <= SHB_LO \/ SHB_HI <= bv_unsigned p24.
  Proof.
    intros H A a tid c pl js sr kn lb hc lz R M mdl p24 HB E105.
    destruct HB as [_ _ _ _ _ _ F _ _ _ _ _].
    assert (EV105 : edenot (EB' a tid c pl js) (EVar 105) = p24) by exact E105.
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. clear F.
    change (l_maps (L2 lb)) with ((EVar 105, 8388608) :: (EVar 104, 1048576) :: (EVar 103, 4096) :: (EVar 102, 8192) :: l_maps L30) in AP. rewrite L30_maps in AP.
    cbn [dl List.map fst snd ivs_apart] in AP. destruct AP as [AP _]. rewrite EV105 in AP.
    do 12 (apply Forall_cons_iff in AP as [_ AP]).
    apply Forall_cons_iff in AP as [X1 AP]. apply Forall_cons_iff in AP as [X2 AP]. apply Forall_cons_iff in AP as [X3 _].
    cbn [fst snd edenot] in X1, X2, X3.
    change (bv_unsigned (Z_to_bv 64 8388608)) with 8388608 in *.
    change (bv_unsigned (Z_to_bv 64 2201439137792)) with 2201439137792 in *. change (bv_unsigned (Z_to_bv 64 15392894357504)) with 15392894357504 in *.
    change (bv_unsigned (Z_to_bv 64 2415882240)) with 2415882240 in *. change (bv_unsigned (Z_to_bv 64 2199023255552)) with 2199023255552 in *.
    change (bv_unsigned (Z_to_bv 64 2147446784)) with 2147446784 in *. change (bv_unsigned (Z_to_bv 64 268435456)) with 268435456 in *.
    unfold SHB_LO, SHB_HI. pose proof (u64_range p24). lia.
  Qed.

  #[local] Notation L3 lb := (lgrant (L2 lb) 106 4096).
  #[local] Notation H12 p8 sb p10 p12 a W p24 := (hcut (H11 p8 sb p10 p12 a W p24) 0x7fffa000 780288).
  #[local] Notation A12 sb p12 a W p24 := ((0x7fffa000, 0x7fffa000 + 782336) :: A11 sb p12 a W p24).
  #[using="Type"] Lemma DS_T2_std : forall lb, DS_std (L2 lb) = DS_T2. Proof. intros lb. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s11_e25 : forall a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K (W lb : Z), 2 ^ 25 <= lim -> length js = 90%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> bv_unsigned sb = SBV p8 -> usp / 8 + CSH <= W ->
    (bv_unsigned p24 + 8388608 <= SHB_LO \/ SHB_HI <= bv_unsigned p24) ->
    bootS' (H11 p8 sb p10 p12 a W p24) (A11 sb p12 a W p24) a tid c pl js SRTd KNTd (L2 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl ->
    (forall p25 R' M' mdl', bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl (js ++ [p25]) SRTdg KNTdx3 (L3 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K W lb Hlim Hjs E28 E38 Hsb WL AP24 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 106%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof SLoc as SLo. pose proof SHic as SHi.
    pose proof (budget11 a tid c pl js p8 sb p12 W _ _ _ _ (L2 lb) ((EVar 105, 8388608) :: (EVar 104, 1048576) :: [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)]) _ _ R M mdl Hlim eq_refl HB E28 E38) as BUD.
    pose proof (p8_factsG sp brk mbase draw lim inp (L2 lb) ((EVar 105, 8388608) :: (EVar 104, 1048576) :: [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)]) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28) as (P1 & P2 & P3).
    pose proof (p12_factsG sp brk mbase draw lim inp (L2 lb) ((EVar 105, 8388608) :: (EVar 104, 1048576) :: [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)]) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    assert (T4 : bv_unsigned a = A_builtin_tls) by (destruct HB as [_ _ _ _ _ _ _ _ _ HT _ _]; exact (proj2 (proj2 (proj2 HT)))).
    assert (TSHc : TSH a = 2148221982) by (unfold TSH, CSH; rewrite T4; reflexivity).
    (* The image shadow is hidden except the TLS block's shadow (builtin_tls lies in the image). *)
    assert (HID : forall x : word, 0x7fffa000 <= bv_unsigned x < 0x800b8800 -> (bv_unsigned x < TSH a \/ TSH a + 60 <= bv_unsigned x) ->
                  H11 p8 sb p10 p12 a W p24 x = true).
    { intros x Hx HT. apply (proj2 (hcut_true _ _ _ _)). split; [apply hjoin_old; apply (H10_hidden_img p8 sb p10 p12 a W x Hsb P2 Q2 HT WL Hx)|].
      clear - AP24 Hx. unfold SHB_LO, SHB_HI in *. lia. }
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H11 p8 sb p10 p12 a W p24) (A11 sb p12 a W p24) a tid c pl js SRTd KNTd (L2 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) 4096 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - change (page_round_up_Z 4096) with 4096. change (l_eager (L2 lb)) with (15450112 + 12288 + 1048576). cbn [A_bytes fst snd]. clear - BUD. lia.
    - change (page_round_up_Z 4096) with 4096. rewrite (eq_refl : l_maps (L2 lb) = (EVar 105, 8388608) :: (EVar 104, 1048576) :: (EVar 103, 4096) :: (EVar 102, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. apply (HK p R' M' mdl'). unfold SRTdg.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_T2_std, KNTdg_eq in HB'.
      (* The TLS block's shadow is visible and zero (the TLS set-up cleared it): the KFill entry. *)
      assert (TZ : forall x : word, TSH a <= bv_unsigned x < TSH a + 60 -> mrestrict (H11 p8 sb p10 p12 a W p24) M' x = Some (Z_to_bv 8 0)).
      { pose proof HB' as [_ HKN _ _ _ _ _ _ _ _ _ _].
        pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.know_ok_sub_b SEGS _ _ KNTdg [KFill (SA (ELit 0) TSHL) (ELit 60) 0]
                      ltac:(vm_compute; reflexivity) HKN) as KF.
        apply Forall_inv in KF. destruct KF as [_ KF].
        assert (ES : estart (EB' a tid c pl (js ++ [p])) (SA (ELit 0) TSHL) = 2148221982) by reflexivity.
        assert (EL : elenZ (EB' a tid c pl (js ++ [p])) (ELit 60) = 60) by reflexivity.
        rewrite ES, EL in KF. intros x Hx. rewrite TSHc in Hx.
        specialize (KF (bv_unsigned x - 2148221982) ltac:(lia)).
        replace (2148221982 + (bv_unsigned x - 2148221982)) with (bv_unsigned x) in KF by lia.
        rewrite Z_to_bv_bv_unsigned in KF. exact KF. }
      rewrite <- KNTdx3_eq. unfold xpose, ISH_LO, ISH_LEN.
      pose proof (bs_expose3 sp brk mbase draw lim inp VI VE _ _ a tid c pl (js ++ [p]) _ _ _ _ _ R' M' mdl' (ELit 0) 0x7fffa000 780288 0x7fffa000 782336 SHB_LO (SHB_LO + 2 ^ 28) HB') as X3.
      cbv zeta in X3. cbn [edenot] in X3. change (bv_unsigned (Z_to_bv 64 0) + 2147459072) with 2147459072 in X3.
      apply X3; clear X3.
      + reflexivity.
      + reflexivity.
      + clear; lia.
      + clear; lia.
      + clear - SLo; unfold stack_max_size, usp in *; lia.
      + clear; lia.
      + clear; lia.
      + clear; lia.
      + intros x Hx. destruct (Z.lt_ge_cases (bv_unsigned x) (TSH a)) as [L|L].
        * left. apply HID; [clear - Hx; lia | left; exact L].
        * destruct (Z.lt_ge_cases (bv_unsigned x) (TSH a + 60)) as [L2|L2].
          -- right. apply TZ. lia.
          -- left. apply HID; [clear - Hx; lia | right; exact L2].
      + do 4 right; left; reflexivity.
      + unfold SHB_LO; clear; lia.
      + unfold SHB_LO; clear; lia.
      + change (l_eager (L3 lb)) with (15450112 + 12288 + 1048576 + 4096). cbn [A_bytes fst snd]. clear - BUD. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s11_bTe : forall a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K (W lb : Z),
    bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SRTdg KNTdx3 (L3 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl ->
    (forall R' M' mdl', bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SRTe KNTe (L3 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K W lb HB HK. change A_internal_mmap_ecall with PCTd at 1. change A_internal_mmap_ecall with PCTe in HK. rg_block VI VE HB HK runTe_eq carTe_eq. Qed.

  #[local] Notation L4 lb := (lgrant (L3 lb) 107 4096).
  #[using="Type"] Lemma DS_T3_std : forall lb, DS_std (L3 lb) = DS_T3. Proof. intros lb. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s11_e26 : forall a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K (W lb : Z), 2 ^ 25 <= lim -> length js = 91%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SRTe KNTe (L3 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl ->
    (forall p26 R' M' mdl', bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl (js ++ [p26]) SRTeg KNTeg (L4 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K W lb Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 107%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget11 a tid c pl js p8 sb p12 W _ _ _ _ (L3 lb) ((EVar 106, 4096) :: (EVar 105, 8388608) :: (EVar 104, 1048576) :: [(EVar 103, 4096); (EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)]) _ _ R M mdl Hlim eq_refl HB E28 E38) as BUD.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SRTe KNTe (L3 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) 4096 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - change (page_round_up_Z 4096) with 4096. change (l_eager (L3 lb)) with (15450112 + 12288 + 1048576 + 4096). cbn [A_bytes fst snd]. clear - BUD. lia.
    - change (page_round_up_Z 4096) with 4096. rewrite (eq_refl : l_maps (L3 lb) = (EVar 106, 4096) :: (EVar 105, 8388608) :: (EVar 104, 1048576) :: (EVar 103, 4096) :: (EVar 102, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. apply (HK p). unfold SRTeg.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_T3_std, KNTeg_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s11_bTf : forall a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K (W lb : Z),
    bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SRTeg KNTeg (L4 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl ->
    (forall R' M' mdl', bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SR_MAIN KN_MAIN (L4 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_main) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_internal_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 p24 R M mdl K W lb HB HK. change A_internal_mmap_ecall with PCTe. change A_main with PC_MAIN in HK. rg_block VI VE HB HK runTf_eq carTf_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition at_main (a tid c : word) (pl : placements) (p8 sb p10 p12 p15 p24 : word) (W lb : Z) (js : list word)
      (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) : Prop :=
    bootS' (H12 p8 sb p10 p12 a W p24) (A12 sb p12 a W p24) a tid c pl js SR_MAIN KN_MAIN (L4 lb) (hc11 p8 p10 p24) (LZ11 p8 sb p10 p15 p24) R M mdl
    /\ WORLD_OK /\ (lb = 0 \/ lb = 8192)
    /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12
    /\ (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15)
    /\ ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js) 64 = Z_to_bv 64 (PBv sp)
    /\ ev (EB' a tid c pl js) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl js) 85 = Z_to_bv 64 (Wdst sp) /\ usp / 8 + CSH <= W /\ W + 8 <= SHB_HI
    /\ ev (EB' a tid c pl js) 101 = brk
    /\ ev (EB' a tid c pl js) 105 = p24 /\ (bv_unsigned p24 + 8388608 <= SHB_LO \/ SHB_HI <= bv_unsigned p24).

  #[using="VI VE"] Theorem boot_s11 : forall a tid c pl p8 sb p10 p12 p15 (W lb : Z) js R M mdl K, 2 ^ 25 <= lim -> length js = 88%nat -> WORLD_OK ->
    at_T0' a tid c pl p8 sb p10 p12 p15 W lb js R M mdl ->
    (forall (p24 : word) ks R' M' mdl', length ks = 4%nat ->
       at_main a tid c pl p8 sb p10 p12 p15 p24 W lb (js ++ ks) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_main) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC_T0) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 p15 W lb js R M mdl K Hlim Hjs HW HE HK.
    destruct HE as (HB0 & Hlb & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101).
    assert (CARRY : forall ks, ev (EB' a tid c pl (js ++ ks)) 28 = p8 /\ ev (EB' a tid c pl (js ++ ks)) 29 = sb /\ ev (EB' a tid c pl (js ++ ks)) 36 = p10
                     /\ ev (EB' a tid c pl (js ++ ks)) 38 = p12 /\ ev (EB' a tid c pl (js ++ ks)) 62 = Z_to_bv 64 (STv sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl (js ++ ks)) 64 = Z_to_bv 64 (PBv sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl (js ++ ks)) 85 = Z_to_bv 64 (Wdst sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 101 = brk).
    { intros ks. rewrite !ev_EB_app by (rewrite Hjs; lia). repeat split; assumption. }
    apply (s11_bTa a tid c pl js p8 sb p10 p12 p15 R M mdl K W lb HW E62 HB0). intros R1 M1 m1 H1.
    pose proof (s11_merge a tid c pl js p8 sb p10 p12 p15 R1 M1 m1 W lb H1) as H1m.
    apply (s11_bTb a tid c pl js p8 sb p10 p12 p15 R1 M1 m1 K W lb H1m). intros R2 M2 m2 H2.
    apply (s11_e23 a tid c pl js p8 sb p10 p12 p15 R2 M2 m2 K W lb Hlim Hjs E28 E38 H2). intros p23 R3 M3 m3 H3.
    set (js1 := js ++ [p23]) in *.
    assert (L1' : length js1 = 89%nat) by (unfold js1; rewrite length_app, Hjs; reflexivity).
    destruct (CARRY [p23]) as (F28 & _ & _ & F38 & _). fold js1 in F28, F38.
    apply (s11_bTc a tid c pl js1 p8 sb p10 p12 p15 R3 M3 m3 K W lb H3). intros R4 M4 m4 H4.
    apply (s11_e24 a tid c pl js1 p8 sb p10 p12 p15 R4 M4 m4 K W lb Hlim L1' F28 F38 H4). intros p24 R5 M5 m5 H5.
    set (js2 := js1 ++ [p24]) in *.
    assert (L2' : length js2 = 90%nat) by (unfold js2; rewrite length_app, L1'; reflexivity).
    assert (G105 : ev (EB' a tid c pl js2) 105 = p24) by (unfold js2; exact (ev_last sp draw inp a tid c pl js1 p24 89 L1')).
    assert (G : ev (EB' a tid c pl js2) 28 = p8 /\ ev (EB' a tid c pl js2) 38 = p12).
    { unfold js2, js1. rewrite <- app_assoc. destruct (CARRY ([p23] ++ [p24])) as (G28 & _ & _ & G38 & _). split; assumption. }
    destruct G as (G28 & G38).
    pose proof (p24_apart _ _ a tid c pl js2 _ _ lb _ _ R5 M5 m5 p24 H5 G105) as AP24.
    apply (s11_bTd a tid c pl js2 p8 sb p10 p12 p15 p24 R5 M5 m5 K W lb H5). intros R6 M6 m6 H6.
    apply (s11_e25 a tid c pl js2 p8 sb p10 p12 p15 p24 R6 M6 m6 K W lb Hlim L2' G28 G38 Hsb WL AP24 H6). intros p25 R7 M7 m7 H7.
    set (js3 := js2 ++ [p25]) in *.
    assert (L3' : length js3 = 91%nat) by (unfold js3; rewrite length_app, L2'; reflexivity).
    assert (I : ev (EB' a tid c pl js3) 28 = p8 /\ ev (EB' a tid c pl js3) 38 = p12).
    { unfold js3, js2, js1. rewrite <- !app_assoc. destruct (CARRY ([p23] ++ [p24] ++ [p25])) as (I28 & _ & _ & I38 & _). split; assumption. }
    destruct I as (I28 & I38).
    apply (s11_bTe a tid c pl js3 p8 sb p10 p12 p15 p24 R7 M7 m7 K W lb H7). intros R8 M8 m8 H8.
    apply (s11_e26 a tid c pl js3 p8 sb p10 p12 p15 p24 R8 M8 m8 K W lb Hlim L3' I28 I38 H8). intros p26 R9 M9 m9 H9.
    apply (s11_bTf a tid c pl (js3 ++ [p26]) p8 sb p10 p12 p15 p24 R9 M9 m9 K W lb H9). intros R10 M10 m10 H10.
    apply (HK p24 ([p23] ++ [p24] ++ [p25] ++ [p26]) R10 M10 m10); [reflexivity|].
    assert (EQ : js ++ [p23] ++ [p24] ++ [p25] ++ [p26] = js3 ++ [p26]) by (unfold js3, js2, js1; rewrite <- !app_assoc; reflexivity).
    unfold at_main. rewrite EQ. split; [exact H10|]. split; [exact HW|]. split; [exact Hlb|]. split; [exact Hsb|].
    rewrite <- EQ. destruct (CARRY ([p23] ++ [p24] ++ [p25] ++ [p26])) as (J28 & J29 & J36 & J38 & J62 & J63 & J64 & J84 & J85 & J101).
    assert (J105 : ev (EB' a tid c pl (js ++ [p23] ++ [p24] ++ [p25] ++ [p26])) 105 = p24).
    { replace (js ++ [p23] ++ [p24] ++ [p25] ++ [p26]) with (js2 ++ ([p25] ++ [p26])) by (unfold js2, js1; rewrite <- !app_assoc; reflexivity).
      rewrite ev_EB_app by (rewrite L2'; lia). exact G105. }
    repeat split; assumption.
  Qed.

End Theorems.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
