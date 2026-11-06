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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes7. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootT0. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn10b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootT0.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots10b_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
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
  #[local] Notation at_E20' := (at_E20 sp brk mbase draw lim inp).

  #[using="brk mbase draw inp VI VE"] Lemma SA16b : usp mod 16 = 0. Proof. exact (SA16 sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SLob : 0x7fff80000000 <= usp. Proof. exact (SL sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SHib : usp <= 2 ^ 47. Proof. exact (SH sp brk mbase draw inp VI VE). Qed.

  #[local] Notation H10' := (H10 sp sp).
  #[local] Notation A10' := (A10 sp sp).
  #[using="Type"] Lemma fetch_musl_mmap_ecall : fetch_word SEGS (Z_to_bv 64 A_musl_mmap_ecall) = Some ECALLW. Proof. vmeq_refl. Qed.
  #[using="Type"] Lemma fetch_musl_mprotect_ecall : fetch_word SEGS (Z_to_bv 64 A_musl_mprotect_ecall) = Some ECALLW. Proof. vmeq_refl. Qed.
  #[using="Type"] Lemma DS_E20_std : DS_std L30 = DS_E20. Proof. vmeq_refl. Qed.


  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma budget10 : forall a tid c pl js p8 sb p10 p12 p15 (W : Z) sr kn (L : ledger) pre R M mdl, 2 ^ 25 <= lim ->
    l_maps L = pre ++ l_maps L20 ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js sr kn L (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    15450112 + 16384 + A_bytes (A10' sb p12 a W) <= lim.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 W sr kn L pre R M mdl Hlim HLm HB E28 E38.
    pose proof SLob as SLo. pose proof SHib as SHi.
    pose proof (p12_factsG sp brk mbase draw lim inp L pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLm HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (shk_facts sp SA16b SLob SHib) as (_ & _ & _ & _ & _ & _ & _ & Y8 & _).
    assert (B12 : PHI12 p12 - PLO12 p12 <= 12288).
    { clear - Q1 Q4 Q2 Q3 SHi. destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia. }
    cbn [A_bytes A10 A9 A9a A8 A7 A5 fst snd]. unfold HWLO, TPG, NSW.
    clear - Hlim Y8 B12. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s10_e20 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), 2 ^ 25 <= lim -> length js = 86%nat ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_E20 KN_E20 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> ev (EB' a tid c pl js) 101 = brk ->
    (* [comment removed for export] *)
    (forall R' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRk0 KN_E20 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_brk_ecall1 + 4)) M ROM) mdl') K) ->
    (* [comment removed for export] *)
    (forall R' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRg0 KNg0 (lbrk L30 101 8192) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15)
                       R' (zfill brk (Z_to_bv 64 8192) M) mdl' ->
       (forall x : word, bv_unsigned brk <= bv_unsigned x < bv_unsigned brk + 8192 -> H10' p8 sb p10 p12 a W x = false) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_brk_ecall1 + 4)) (zfill brk (Z_to_bv 64 8192) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_brk_ecall1) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hlim Hjs HB E28 E38 E101 HKK HKG.
    assert (LEN : length (VB' a tid c pl js) = 102%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget10 a tid c pl js p8 sb p10 p12 p15 W _ _ L30 [(EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] R M mdl Hlim eq_refl HB E28 E38) as BUD.
    assert (Bb : Z_to_bv 64 (bv_unsigned brk + l_brk L30) = brk).
    { apply bv_eq. change (l_brk L30) with 0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    pose proof (bs_brk_grow sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_E20 KN_E20 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15)
                  101%nat 4096 8192 A_brk_ecall1 ECALLW R M mdl K HB fetch_brk_ecall1 is_ecall_ECALLW) as X.
    cbv zeta in X. rewrite Bb in X. apply X; clear X.
    - unfold A_brk_ecall1; clear; lia.
    - unfold A_brk_ecall1; clear; lia.
    - vmeq_refl.
    - exact E101.
    - rewrite LEN. clear. lia.
    - replace (sr_get SR_E20 10%bv) with (EAlu ALU_ADD (EVar 101) (ELit 8192)) by (vmeq_refl).
      cbn [edenot]. change (ev (EB sp draw inp a tid c pl js) 101) with (ev (EB' a tid c pl js) 101). rewrite E101.
      apply bv_eq. rewrite u_add64. reflexivity.
    - change (l_brk L30) with 0. clear; lia.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - clear; lia.
    - clear; lia.
    - vmeq_refl.
    - change (l_eager L30) with 15450112. clear - BUD. lia.
    - intros R' mdl' _ HB'. apply (HKK R' mdl'). exact HB'.
    - intros R' mdl' _ HB' Hvis. apply (HKG R' mdl'); [|exact Hvis].
      unfold kn_brk_grant in HB'. rewrite DS_E20_std in HB'. fold (kn_brk_grant_d DS_E20 101 4096 8192 KN_E20) in HB'. rewrite KNg0_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WLZ (p8 p10 : word) : list (Z * Z) :=
    [(SHB_LO, SHB_HI); (bv_unsigned p8, bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE); (bv_unsigned p10, bv_unsigned p10 + N_PA)].

  #[using="brk mbase draw inp VI VE usp"] Lemma LZ30_shape : forall p8 sb p10 p15,
    bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE <= 2 ^ 63 -> bv_unsigned p10 + N_PA <= 2 ^ 63 ->
    ivs_wf (LZ30 sp p8 sb p10 p15) /\ ivs_pos (LZ30 sp p8 sb p10 p15) /\ ivs_within (LZ30 sp p8 sb p10 p15) (WLZ p8 p10).
  Proof.
    intros p8 sb p10 p15 B8 B10.
    pose proof (x9_facts sp SA16b SLob SHib) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15).
    pose proof HI_A_val as VA. pose proof HI_N_val as VN. pose proof GAP_A_val as GA. pose proof GAP_N_val as GN. pose proof LO_N_val as LN.
    assert (LA : bv_unsigned LO_A = 0x7fff7000) by (vmeq_refl).
    assert (N8 : bv_unsigned (Z_to_bv 64 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE) = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE) by (vmeq_refl).
    assert (N10 : bv_unsigned (Z_to_bv 64 N_PA) = N_PA) by (vmeq_refl).
    pose proof (u64_range p8) as U8. pose proof (u64_range p10) as U10.
    (* [comment removed for export] *)
    assert (S16 : ivs_wf (LZ16 p8) /\ ivs_pos (LZ16 p8) /\ ivs_within (LZ16 p8) (WLZ p8 p10)).
    { unfold LZ16, LZ5. split; [|split].
      - repeat (apply ivs_wf_cons; [apply iv_wf_intro; rewrite ?N8, ?VA, ?VN, ?GA, ?GN, ?LA, ?LN; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE in *; lia|]). apply ivs_wf_nil.
      - repeat (apply ivs_pos_cons; [cbn [snd]; rewrite ?N8, ?VN, ?GN, ?LN; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE; lia|]). apply ivs_pos_nil.
      - apply ivs_within_cons; [exists (bv_unsigned p8, bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE); split; [unfold WLZ; right; left; reflexivity | cbn [fst snd]; rewrite N8; lia]|].
        repeat (apply ivs_within_cons; [exists (SHB_LO, SHB_HI); split; [unfold WLZ; left; reflexivity | cbn [fst snd]; rewrite ?VA, ?VN, ?GA, ?GN, ?LA, ?LN; unfold SHB_LO, SHB_HI; lia]|]).
        apply ivs_within_nil. }
    destruct S16 as (W16 & P16 & I16).
    assert (S17 : ivs_wf (LZ17 p8 sb) /\ ivs_pos (LZ17 p8 sb) /\ ivs_within (LZ17 p8 sb) (WLZ p8 p10)).
    { unfold LZ17. split; [apply maps_subtract_wf; [exact W16 | lia] | split; [apply maps_subtract_pos; assumption | apply maps_subtract_within; assumption]]. }
    destruct S17 as (W17 & P17 & I17).
    assert (S18 : ivs_wf (LZ18 p8 sb p10) /\ ivs_pos (LZ18 p8 sb p10) /\ ivs_within (LZ18 p8 sb p10) (WLZ p8 p10)).
    { unfold LZ18. split; [apply ivs_wf_cons; [apply iv_wf_intro; rewrite N10; unfold N_PA in *; lia | exact W17] | split].
      - apply ivs_pos_cons; [cbn [snd]; rewrite N10; unfold N_PA; lia | exact P17].
      - apply ivs_within_cons; [exists (bv_unsigned p10, bv_unsigned p10 + N_PA); split; [unfold WLZ; do 2 right; left; reflexivity | cbn [fst snd]; rewrite N10; lia] | exact I17]. }
    destruct S18 as (W18 & P18 & I18).
    assert (S24 : ivs_wf (LZ24 p8 sb p10 p15) /\ ivs_pos (LZ24 p8 sb p10 p15) /\ ivs_within (LZ24 p8 sb p10 p15) (WLZ p8 p10)).
    { unfold LZ24. split; [apply maps_subtract_wf; [exact W18 | lia] | split; [apply maps_subtract_pos; assumption | apply maps_subtract_within; assumption]]. }
    destruct S24 as (W24 & P24 & I24).
    (* [comment removed for export] *)
    unfold LZ30. exact (conj W24 (conj P24 I24)).
  Qed.

  #[using="Type"] Lemma L30_maps : l_maps L30 = [(EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096); (EVar 38, 65536); (EVar 37, 4096); (EVar 36, 8388608);
     (EVar 28, 137439023104); (EVar 27, 3727360); (EVar 26, 65536); (ELit 2201439137792, 15392894357504); (ELit 2415882240, 2199023255552);
     (ELit 2147446784, 268435456)].
  Proof. reflexivity. Qed.

  #[using="VI VE usp"] Lemma LZ30_guard_id : forall H A a tid c pl js sr kn hc lz R M mdl p8 sb p10 p15,
    bootS' H A a tid c pl js sr kn (lbrk L30 101 8192) hc lz R M mdl ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 101 = brk ->
    maps_subtract (LZ30 sp p8 sb p10 p15) (bv_unsigned brk) (bv_unsigned brk + 4096) = LZ30 sp p8 sb p10 p15.
  Proof.
    intros H A a tid c pl js sr kn hc lz R M mdl p8 sb p10 p15 HB E28 E36 E101.
    pose proof SLob as SLo. pose proof SHib as SHi.
    destruct HB as [_ _ _ _ _ _ F HMO _ _ _ _].
    assert (EV28 : edenot (EB' a tid c pl js) (EVar 28) = p8) by exact E28.
    assert (EV36 : edenot (EB' a tid c pl js) (EVar 36) = p10) by exact E36.
    assert (EV101 : edenot (EB' a tid c pl js) (EVar 101) = brk) by exact E101.
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. clear F.
    change (l_maps (lbrk L30 101 8192)) with ((EVar 101, 8192) :: l_maps L30) in AP. rewrite L30_maps in AP.
    cbn [dl List.map fst snd ivs_apart] in AP. destruct AP as [AP _]. rewrite EV101, EV28, EV36 in AP.
    repeat (apply Forall_cons_iff in AP as [?X AP]); cbn [fst snd edenot] in *. clear AP.
    clear X X0 X1 X2 X3 X6 X7.
    change (bv_unsigned (Z_to_bv 64 8192)) with 8192 in *. change (bv_unsigned (Z_to_bv 64 8388608)) with 8388608 in *.
    change (bv_unsigned (Z_to_bv 64 137439023104)) with 137439023104 in *.
    change (bv_unsigned (Z_to_bv 64 2201439137792)) with 2201439137792 in *. change (bv_unsigned (Z_to_bv 64 15392894357504)) with 15392894357504 in *.
    change (bv_unsigned (Z_to_bv 64 2415882240)) with 2415882240 in *. change (bv_unsigned (Z_to_bv 64 2199023255552)) with 2199023255552 in *.
    change (bv_unsigned (Z_to_bv 64 2147446784)) with 2147446784 in *. change (bv_unsigned (Z_to_bv 64 268435456)) with 268435456 in *.
    (* [comment removed for export] *)
    pose proof HMO as MO. unfold maps_ok in MO. change (l_maps (lbrk L30 101 8192)) with ((EVar 101, 8192) :: l_maps L30) in MO. rewrite L30_maps in MO.
    assert (M36 : map_ok sp (EB' a tid c pl js) (EVar 36, 8388608)) by (apply (proj1 (Forall_forall _ _) MO); cbn [In]; do 6 right; left; reflexivity).
    assert (M28 : map_ok sp (EB' a tid c pl js) (EVar 28, 137439023104)) by (apply (proj1 (Forall_forall _ _) MO); cbn [In]; do 7 right; left; reflexivity).
    clear MO HMO. unfold map_ok in M36, M28. cbn [fst snd edenot] in M36, M28. rewrite EV36 in M36. rewrite EV28 in M28.
    destruct M36 as (_ & _ & _ & T36 & _). destruct M28 as (_ & _ & _ & T28 & _). unfold stack_max_size in *.
    destruct (LZ30_shape p8 sb p10 p15 ltac:(unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE, usp in *; lia) ltac:(unfold N_PA, usp in *; lia)) as (_ & POS & WIN).
    pose proof (u64_range brk) as UB.
    apply (maps_subtract_id_within _ _ _ (WLZ p8 p10)); [lia | exact POS | exact WIN |].
    intros w Hw. unfold WLZ in Hw. cbn [In] in Hw. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold SHB_LO, SHB_HI, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.N_SPACE, N_PA; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="usp"] Lemma brk_misses_shadow : forall H A a tid c pl js sr kn hc lz R M mdl,
    bootS' H A a tid c pl js sr kn (lbrk L30 101 8192) hc lz R M mdl ->
    ev (EB' a tid c pl js) 101 = brk ->
    bv_unsigned brk + 8192 <= SHB_LO \/ SHB_HI <= bv_unsigned brk.
  Proof.
    intros H A a tid c pl js sr kn hc lz R M mdl HB E101.
    destruct HB as [_ _ _ _ _ _ F _ _ _ _ _].
    assert (EV101 : edenot (EB' a tid c pl js) (EVar 101) = brk) by exact E101.
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. clear F.
    change (l_maps (lbrk L30 101 8192)) with ((EVar 101, 8192) :: l_maps L30) in AP. rewrite L30_maps in AP.
    cbn [dl List.map fst snd ivs_apart] in AP. destruct AP as [AP _]. rewrite EV101 in AP.
    repeat (apply Forall_cons_iff in AP as [?X AP]); cbn [fst snd edenot] in *. clear AP.
    clear X X0 X1 X2 X3 X4 X5 X6 X7.
    change (bv_unsigned (Z_to_bv 64 8192)) with 8192 in *.
    change (bv_unsigned (Z_to_bv 64 2201439137792)) with 2201439137792 in *. change (bv_unsigned (Z_to_bv 64 15392894357504)) with 15392894357504 in *.
    change (bv_unsigned (Z_to_bv 64 2415882240)) with 2415882240 in *. change (bv_unsigned (Z_to_bv 64 2199023255552)) with 2199023255552 in *.
    change (bv_unsigned (Z_to_bv 64 2147446784)) with 2147446784 in *. change (bv_unsigned (Z_to_bv 64 268435456)) with 268435456 in *.
    unfold SHB_LO, SHB_HI. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation Lg := (lbrk L30 101 8192).
  #[using="VI VE"] Theorem s10_bG1 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRg0 KNg0 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG1 KNG1 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_brk_ecall1 + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_brk_ecall1 with PC_E20. change A_musl_mmap_ecall with PCG1 in HK. rg_block VI VE HB HK runG1_eq carG1_eq. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s10_guard : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), length js = 86%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 101 = brk ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG1 KNG1 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall x : word, bv_unsigned brk <= bv_unsigned x < bv_unsigned brk + 8192 -> H10' p8 sb p10 p12 a W x = false) ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl (js ++ [brk]) SRG1 KNG1u Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hjs E28 E36 E101 HB Hvis HK.
    assert (LEN : length (VB' a tid c pl js) = 102%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (LZ30_guard_id _ _ _ _ _ _ _ _ _ _ _ _ _ _ p8 sb p10 p15 HB E28 E36 E101) as LZID.
    pose proof (bs_mmap_fixed_none_guard sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG1 KNG1 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15)
                  101%nat 4096 8192 A_musl_mmap_ecall (l_maps L30) ECALLW R M mdl K HB fetch_musl_mmap_ecall is_ecall_ECALLW) as X.
    cbv zeta in X. change (ev (EB sp draw inp a tid c pl js) 101) with (ev (EB' a tid c pl js) 101) in X. rewrite E101 in X. apply X; clear X.
    - unfold A_musl_mmap_ecall; clear; lia.
    - unfold A_musl_mmap_ecall; clear; lia.
    - vmeq_refl.
    - replace (sr_get SRG1 10%bv) with (EVar 101) by (vmeq_refl). exact E101.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - reflexivity.
    - reflexivity.
    - clear; lia.
    - exact Hvis.
    - destruct (brk_misses_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB E101) as [B|B]; [left | right]; clear - B; lia.
    - intros R' mdl' HB'. rewrite KNG1u_eq, LZID in HB'.
      pose proof (bs_fresh2 sp brk mbase draw lim inp _ _ a tid c pl js SRG1 KNG1u Lg _ _ R' _ mdl' [brk] SRG1 [] HB') as Y.
      cbv zeta in Y. rewrite LEN in Y. apply (HK R' _ mdl'). apply Y; clear Y.
      + vmeq_refl.
      + vmeq_refl.
      + vmeq_refl.
      + auto.
      + constructor.
  Qed.

  #[using="VI VE"] Theorem s10_bG2 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG1 KNG1u Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG2 KNG2 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_musl_mmap_ecall with PCG1 at 1. change A_musl_mmap_ecall with PCG2 in HK. rg_block VI VE HB HK runG2_eq carG2_eq. Qed.

  #[using="Type"] Lemma DS_E22g_std : DS_std Lg = DS_E22g. Proof. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s10_e22G : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), 2 ^ 25 <= lim -> length js = 87%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG2 KNG2 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall p R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl (js ++ [p]) SRG2g KNG2g (lgrant Lg 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 103%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget10 a tid c pl js p8 sb p10 p12 p15 W _ _ Lg [(EVar 101, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] R M mdl Hlim eq_refl HB E28 E38) as BUD.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG2 KNG2 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) 4096 A_musl_mmap_ecall ECALLW
              R M mdl K HB fetch_musl_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_musl_mmap_ecall; lia).
    - change (page_round_up_Z 4096) with 4096. change (l_eager Lg) with (15450112 + 8192). clear - BUD. lia.
    - change (page_round_up_Z 4096) with 4096. rewrite (eq_refl : l_maps Lg = (EVar 101, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. apply (HK p). unfold SRG2g.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_E22g_std, KNG2g_eq in HB'. exact HB'.
  Qed.

  #[using="VI VE"] Theorem s10_bG3 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG2g KNG2g (lgrant Lg 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG3 KNG3 (lgrant Lg 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC_T0) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_musl_mmap_ecall with PCG2. change PC_T0 with PCG3 in HK. rg_block VI VE HB HK runG3_eq carG3_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s10_bK1 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRk0 KN_E20 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK1 KNK1 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_brk_ecall1 + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_brk_ecall1 with PC_E20. change A_musl_mmap_ecall with PCK1 in HK. rg_block VI VE HB HK runK1_eq carK1_eq. Qed.

  #[local] Notation Lk1 := (lgrant_nr L30 102 8192).
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s10_e21K : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), length js = 86%nat ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK1 KNK1 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall q R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl (js ++ [q]) SRK1g KNK1g Lk1 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       In (q, Z_to_bv 64 8192) (vm_noaccess (m_vmmaps mdl')) ->
       (forall x : word, bv_unsigned q <= bv_unsigned x < bv_unsigned q + 8192 -> H10' p8 sb p10 p12 a W x = false) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hjs HB HK.
    assert (LEN : length (VB' a tid c pl js) = 102%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (bs_mmap_none_anon sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK1 KNK1 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15)
                  8192 A_musl_mmap_ecall ECALLW R M mdl K HB fetch_musl_mmap_ecall is_ecall_ECALLW) as X.
    cbv zeta in X. rewrite LEN in X. change (page_round_up_Z 8192) with 8192 in X. apply X; clear X.
    - unfold A_musl_mmap_ecall; clear; lia.
    - unfold A_musl_mmap_ecall; clear; lia.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - clear; lia.
    - rewrite L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros q R' mdl' HB' Hna Hvis. apply (HK q R' _ mdl'); [| exact Hna | exact Hvis].
      unfold kn_grant_none in HB'. rewrite DS_E20_std, KNK1g_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  Ltac rg_block_na VI VE HB HK RUN CAR Hna :=
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
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ =>
        let body := eval unfold m in m in
        lazymatch body with munrestrict ?H ?M (mem_denot (EB _ _ _ ?a ?tid ?c ?pl ?js) _ ?lg) =>
          lazymatch type of F with mfacts _ _ _ _ _ _ _ ?L _ =>
            lazymatch type of HZ with hf_ok _ _ ?hc =>
              destruct (frame_blockS sp brk mbase draw inp VI VE H a tid c pl js M lg hc (lows_of L) ltac:(vmeq_refl)
                          (lows_of_ok sp _ L HMO) (rg_above _ _ _ _ _ _ _ RG) HA HZ) as [HA0 HZ0];
              subst m
            end end end end;
      apply HK;
        [ constructor; try assumption;
          [ erewrite sbm_lazy by eassumption; exact HLZ | eapply mfacts_sbm; eassumption | eapply regime_ok_sbm; eassumption]
        | erewrite sbm_vmmaps by eassumption; exact Hna ]
    end.

  #[using="VI VE"] Theorem s10_bK2 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z) (q : word),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK1g KNK1g Lk1 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    In (q, Z_to_bv 64 8192) (vm_noaccess (m_vmmaps mdl)) ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK2 KNK2 Lk1 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       In (q, Z_to_bv 64 8192) (vm_noaccess (m_vmmaps mdl')) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_mprotect_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W q HB Hna HK. change A_musl_mmap_ecall with PCK1. change A_musl_mprotect_ecall with PCK2 in HK. rg_block_na VI VE HB HK runK2_eq carK2_eq Hna. Qed.

  #[local] Notation Lk2 := (lcommit Lk1 4096).
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s10_mprot : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z) (q : word), 2 ^ 25 <= lim ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> ev (EB' a tid c pl js) 102 = q ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK2 KNK2 Lk1 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    In (q, Z_to_bv 64 8192) (vm_noaccess (m_vmmaps mdl)) ->
    (forall x : word, bv_unsigned q <= bv_unsigned x < bv_unsigned q + 8192 -> H10' p8 sb p10 p12 a W x = false) ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK2m KNK2m Lk2 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_musl_mprotect_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_mprotect_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W q Hlim E28 E38 E102 HB Hna Hvis HK.
    pose proof (budget10 a tid c pl js p8 sb p10 p12 p15 W _ _ Lk1 [(EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] R M mdl Hlim eq_refl HB E28 E38) as BUD.
    pose proof (bs_mprotect_rw sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK2 KNK2 Lk1 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15)
                  102%nat 8192 4096 4096 A_musl_mprotect_ecall ECALLW R M mdl K HB fetch_musl_mprotect_ecall is_ecall_ECALLW) as X.
    cbv zeta in X. change (ev (EB sp draw inp a tid c pl js) 102) with (ev (EB' a tid c pl js) 102) in X. rewrite E102 in X. apply X; clear X.
    - unfold A_musl_mprotect_ecall; clear; lia.
    - unfold A_musl_mprotect_ecall; clear; lia.
    - vmeq_refl.
    - replace (sr_get SRK2 10%bv) with (EAlu ALU_ADD (EVar 102) (ELit 4096)) by (vmeq_refl).
      cbn [edenot]. change (ev (EB sp draw inp a tid c pl js) 102) with (ev (EB' a tid c pl js) 102). rewrite E102.
      apply bv_eq. rewrite u_add64. reflexivity.
    - vmeq_refl.
    - vmeq_refl.
    - left. reflexivity.
    - exact Hna.
    - exact Hvis.
    - clear; lia.
    - clear; lia.
    - reflexivity.
    - reflexivity.
    - clear; lia.
    - change (l_eager Lk1) with 15450112. clear - BUD. lia.
    - intros R' mdl' HB'. apply (HK R' _ mdl'). unfold kn_mprotect in HB'. rewrite KNK2m_eq in HB'. exact HB'.
  Qed.

  #[using="VI VE"] Theorem s10_bK3 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK2m KNK2m Lk2 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK3 KNK3 Lk2 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_musl_mprotect_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_musl_mprotect_ecall with PCK2. change A_musl_mmap_ecall with PCK3 in HK. rg_block VI VE HB HK runK3_eq carK3_eq. Qed.

  #[using="Type"] Lemma DS_E22k_std : DS_std Lk2 = DS_E22k. Proof. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s10_e22K : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), 2 ^ 25 <= lim -> length js = 87%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK3 KNK3 Lk2 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall p R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl (js ++ [p]) SRK3g KNK3g (lgrant Lk2 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 103%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget10 a tid c pl js p8 sb p10 p12 p15 W _ _ Lk2 [(EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] R M mdl Hlim eq_refl HB E28 E38) as BUD.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK3 KNK3 Lk2 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) 4096 A_musl_mmap_ecall ECALLW
              R M mdl K HB fetch_musl_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_musl_mmap_ecall; lia).
    - change (page_round_up_Z 4096) with 4096. change (l_eager Lk2) with (15450112 + 4096). clear - BUD. lia.
    - change (page_round_up_Z 4096) with 4096. rewrite (eq_refl : l_maps Lk2 = (EVar 102, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. apply (HK p). unfold SRK3g.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_E22k_std, KNK3g_eq in HB'. exact HB'.
  Qed.

  #[using="VI VE"] Theorem s10_bK4 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK3g KNK3g (lgrant Lk2 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK4 KNK4 (lgrant Lk2 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC_T0) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_musl_mmap_ecall with PCK3. change PC_T0 with PCK4 in HK. rg_block VI VE HB HK runK4_eq carK4_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Theorem s10_joinG : forall a tid c pl js p8 sb p10 p12 p15 R M mdl (W : Z),
    ev (EB' a tid c pl js) 101 = brk -> ev (EB' a tid c pl js) 102 = brk ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG3 KNG3 (lgrant Lg 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_T0 KN_T0 (L_T0 8192) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl W E101 E102 HB.
    assert (HB1 : bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_T0 KN_T0 (lgrant Lg 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl).
    { eapply bootS_reknow; [exact HB | auto |]. apply know_ok_sub_b. exact (proj1 T0_join). }
    apply (bs_reledger sp brk mbase draw lim inp _ _ a tid c pl js SR_T0 KN_T0 (lgrant Lg 103 4096) (L_T0 8192) _ _ R M mdl HB1).
    - unfold sivden, L_T0, lgrant, lbrk. cbn [l_maps List.map fst snd edenot].
      change (ev (EB sp draw inp a tid c pl js) 102) with (ev (EB' a tid c pl js) 102). change (ev (EB sp draw inp a tid c pl js) 101) with (ev (EB' a tid c pl js) 101).
      rewrite E101, E102. reflexivity.
    - reflexivity.
    - unfold L_T0, lgrant, lbrk. cbn [l_eager]. clear. lia.
  Qed.

  #[using="Type"] Theorem s10_joinK : forall a tid c pl js p8 sb p10 p12 p15 R M mdl (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK4 KNK4 (lgrant Lk2 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_T0 KN_T0 (L_T0 0) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl W HB.
    assert (HB1 : bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_T0 KN_T0 (lgrant Lk2 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl).
    { rewrite <- SRK4_eq. eapply bootS_reknow; [exact HB | auto |]. apply know_ok_sub_b. exact (proj2 T0_join). }
    apply (bs_reledger sp brk mbase draw lim inp _ _ a tid c pl js SR_T0 KN_T0 (lgrant Lk2 103 4096) (L_T0 0) _ _ R M mdl HB1).
    - reflexivity.
    - reflexivity.
    - unfold L_T0, lgrant, lcommit, lgrant_nr. cbn [l_eager]. clear. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="usp"] Lemma ev_last : forall a tid c pl js (w : word) (k : nat), length js = k ->
    ev (EB' a tid c pl (js ++ [w])) (16 + k) = w.
  Proof.
    intros a tid c pl js w k Hk. rewrite (ev_EB_js sp draw inp a tid c pl _ k), app_nth2 by lia. rewrite Hk, Nat.sub_diag. reflexivity.
  Qed.

  #[using="VI VE usp"] Theorem boot_s10b : forall a tid c pl p8 sb p10 p12 p15 (W : Z) js R M mdl K, 2 ^ 25 <= lim -> length js = 86%nat ->
    at_E20' a tid c pl p8 sb p10 p12 p15 W js R M mdl ->
    (forall (lb : Z) ks R' M' mdl', length ks = 2%nat ->
       at_T0 sp brk mbase draw lim inp a tid c pl p8 sb p10 p12 p15 W lb (js ++ ks) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC_T0) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_brk_ecall1) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 p15 W js R M mdl K Hlim Hjs HE HK.
    destruct HE as (HB0 & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101).
    (* [comment removed for export] *)
    assert (CARRY : forall ks, ev (EB' a tid c pl (js ++ ks)) 28 = p8 /\ ev (EB' a tid c pl (js ++ ks)) 29 = sb /\ ev (EB' a tid c pl (js ++ ks)) 36 = p10
                     /\ ev (EB' a tid c pl (js ++ ks)) 38 = p12 /\ ev (EB' a tid c pl (js ++ ks)) 62 = Z_to_bv 64 (STv sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl (js ++ ks)) 64 = Z_to_bv 64 (PBv sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl (js ++ ks)) 85 = Z_to_bv 64 (Wdst sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 101 = brk).
    { intros ks. rewrite !ev_EB_app by (rewrite Hjs; lia). repeat split; assumption. }
    apply (s10_e20 a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hlim Hjs HB0 E28 E38 E101).
    - (* [comment removed for export] *)
      intros R1 m1 H1.
      apply (s10_bK1 a tid c pl js p8 sb p10 p12 p15 R1 M m1 K W H1). intros R2 M2 m2 H2.
      apply (s10_e21K a tid c pl js p8 sb p10 p12 p15 R2 M2 m2 K W Hjs H2). intros q R3 M3 m3 H3 Hna Hvis.
      set (js1 := js ++ [q]) in *.
      assert (L1 : length js1 = 87%nat) by (unfold js1; rewrite length_app, Hjs; reflexivity).
      destruct (CARRY [q]) as (F28 & _ & _ & F38 & _). fold js1 in F28, F38.
      assert (F102 : ev (EB' a tid c pl js1) 102 = q) by (unfold js1; exact (ev_last a tid c pl js q 86 Hjs)).
      apply (s10_bK2 a tid c pl js1 p8 sb p10 p12 p15 R3 M3 m3 K W q H3 Hna). intros R4 M4 m4 H4 Hna4.
      apply (s10_mprot a tid c pl js1 p8 sb p10 p12 p15 R4 M4 m4 K W q Hlim F28 F38 F102 H4 Hna4 Hvis). intros R5 M5 m5 H5.
      apply (s10_bK3 a tid c pl js1 p8 sb p10 p12 p15 R5 M5 m5 K W H5). intros R6 M6 m6 H6.
      apply (s10_e22K a tid c pl js1 p8 sb p10 p12 p15 R6 M6 m6 K W Hlim L1 F28 F38 H6). intros p R7 M7 m7 H7.
      apply (s10_bK4 a tid c pl (js1 ++ [p]) p8 sb p10 p12 p15 R7 M7 m7 K W H7). intros R8 M8 m8 H8.
      pose proof (s10_joinK a tid c pl (js1 ++ [p]) p8 sb p10 p12 p15 R8 M8 m8 W H8) as H9.
      apply (HK 0 ([q] ++ [p]) R8 M8 m8); [reflexivity|].
      unfold at_T0. cbv zeta. rewrite app_assoc. fold js1. split; [exact H9|]. split; [left; reflexivity|]. split; [exact Hsb|].
      unfold js1. rewrite <- app_assoc. destruct (CARRY ([q] ++ [p])) as (G28 & G29 & G36 & G38 & G62 & G63 & G64 & G84 & G85 & G101).
      repeat split; assumption.
    - (* [comment removed for export] *)
      intros R1 m1 H1 Hvis.
      apply (s10_bG1 a tid c pl js p8 sb p10 p12 p15 R1 _ m1 K W H1). intros R2 M2 m2 H2.
      apply (s10_guard a tid c pl js p8 sb p10 p12 p15 R2 M2 m2 K W Hjs E28 E36 E101 H2 Hvis). intros R3 M3 m3 H3.
      set (js1 := js ++ [brk]) in *.
      assert (L1 : length js1 = 87%nat) by (unfold js1; rewrite length_app, Hjs; reflexivity).
      destruct (CARRY [brk]) as (F28 & _ & _ & F38 & _). fold js1 in F28, F38.
      apply (s10_bG2 a tid c pl js1 p8 sb p10 p12 p15 R3 M3 m3 K W H3). intros R4 M4 m4 H4.
      apply (s10_e22G a tid c pl js1 p8 sb p10 p12 p15 R4 M4 m4 K W Hlim L1 F28 F38 H4). intros p R5 M5 m5 H5.
      apply (s10_bG3 a tid c pl (js1 ++ [p]) p8 sb p10 p12 p15 R5 M5 m5 K W H5). intros R6 M6 m6 H6.
      destruct (CARRY ([brk] ++ [p])) as (G28 & G29 & G36 & G38 & G62 & G63 & G64 & G84 & G85 & G101).
      assert (G102 : ev (EB' a tid c pl (js1 ++ [p])) 102 = brk).
      { rewrite ev_EB_app by (rewrite L1; lia). unfold js1. exact (ev_last a tid c pl js brk 86 Hjs). }
      assert (G101' : ev (EB' a tid c pl (js1 ++ [p])) 101 = brk) by (unfold js1; rewrite <- app_assoc; exact G101).
      pose proof (s10_joinG a tid c pl (js1 ++ [p]) p8 sb p10 p12 p15 R6 M6 m6 W G101' G102 H6) as H7.
      apply (HK 8192 ([brk] ++ [p]) R6 M6 m6); [reflexivity|].
      unfold at_T0. cbv zeta. rewrite app_assoc. fold js1. split; [exact H7|]. split; [right; reflexivity|]. split; [exact Hsb|].
      unfold js1. rewrite <- app_assoc. repeat split; assumption.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes7.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn10b. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootT0.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots10b_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
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
  #[local] Notation at_E20' := (at_E20 sp brk mbase draw lim inp).

  #[using="brk mbase draw inp VI VE"] Lemma SA16b : usp mod 16 = 0. Proof. exact (SA16 sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SLob : 0x7fff80000000 <= usp. Proof. exact (SL sp brk mbase draw inp VI VE). Qed.
  #[using="brk mbase draw inp VI VE"] Lemma SHib : usp <= 2 ^ 47. Proof. exact (SH sp brk mbase draw inp VI VE). Qed.

  #[local] Notation H10' := (H10 sp sp).
  #[local] Notation A10' := (A10 sp sp).
  #[using="Type"] Lemma fetch_musl_mmap_ecall : fetch_word SEGS (Z_to_bv 64 A_musl_mmap_ecall) = Some ECALLW. Proof. vmeq_refl. Qed.
  #[using="Type"] Lemma fetch_musl_mprotect_ecall : fetch_word SEGS (Z_to_bv 64 A_musl_mprotect_ecall) = Some ECALLW. Proof. vmeq_refl. Qed.
  #[using="Type"] Lemma DS_E20_std : DS_std L30 = DS_E20. Proof. vmeq_refl. Qed.


  (* [comment removed for export] *)
  #[using="VI VE usp"] Lemma budget10 : forall a tid c pl js p8 sb p10 p12 p15 (W : Z) sr kn (L : ledger) pre R M mdl, 2 ^ 25 <= lim ->
    l_maps L = pre ++ l_maps L20 ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js sr kn L (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    15450112 + 16384 + A_bytes (A10' sb p12 a W) <= lim.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 W sr kn L pre R M mdl Hlim HLm HB E28 E38.
    pose proof SLob as SLo. pose proof SHib as SHi.
    pose proof (p12_factsG sp brk mbase draw lim inp L pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLm HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (shk_facts sp SA16b SLob SHib) as (_ & _ & _ & _ & _ & _ & _ & Y8 & _).
    assert (B12 : PHI12 p12 - PLO12 p12 <= 12288).
    { clear - Q1 Q4 Q2 Q3 SHi. destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia. }
    cbn [A_bytes A10 A9 A9a A8 A7 A5 fst snd]. unfold HWLO, TPG, NSW.
    clear - Hlim Y8 B12. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s10_e20 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), 2 ^ 25 <= lim -> length js = 86%nat ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_E20 KN_E20 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> ev (EB' a tid c pl js) 101 = brk ->
    (* [comment removed for export] *)
    (forall R' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRk0 KN_E20 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_brk_ecall1 + 4)) M ROM) mdl') K) ->
    (* [comment removed for export] *)
    (forall R' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRg0 KNg0 (lbrk L30 101 8192) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15)
                       R' (zfill brk (Z_to_bv 64 8192) M) mdl' ->
       (forall x : word, bv_unsigned brk <= bv_unsigned x < bv_unsigned brk + 8192 -> H10' p8 sb p10 p12 a W x = false) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_brk_ecall1 + 4)) (zfill brk (Z_to_bv 64 8192) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_brk_ecall1) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hlim Hjs HB E28 E38 E101 HKK HKG.
    assert (LEN : length (VB' a tid c pl js) = 102%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget10 a tid c pl js p8 sb p10 p12 p15 W _ _ L30 [(EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] R M mdl Hlim eq_refl HB E28 E38) as BUD.
    assert (Bb : Z_to_bv 64 (bv_unsigned brk + l_brk L30) = brk).
    { apply bv_eq. change (l_brk L30) with 0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    pose proof (bs_brk_grow sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_E20 KN_E20 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15)
                  101%nat 4096 8192 A_brk_ecall1 ECALLW R M mdl K HB fetch_brk_ecall1 is_ecall_ECALLW) as X.
    cbv zeta in X. rewrite Bb in X. apply X; clear X.
    - unfold A_brk_ecall1; clear; lia.
    - unfold A_brk_ecall1; clear; lia.
    - vmeq_refl.
    - exact E101.
    - rewrite LEN. clear. lia.
    - replace (sr_get SR_E20 10%bv) with (EAlu ALU_ADD (EVar 101) (ELit 8192)) by (vmeq_refl).
      cbn [edenot]. change (ev (EB sp draw inp a tid c pl js) 101) with (ev (EB' a tid c pl js) 101). rewrite E101.
      apply bv_eq. rewrite u_add64. reflexivity.
    - change (l_brk L30) with 0. clear; lia.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - clear; lia.
    - clear; lia.
    - vmeq_refl.
    - change (l_eager L30) with 15450112. clear - BUD. lia.
    - intros R' mdl' _ HB'. apply (HKK R' mdl'). exact HB'.
    - intros R' mdl' _ HB' Hvis. apply (HKG R' mdl'); [|exact Hvis].
      unfold kn_brk_grant in HB'. rewrite DS_E20_std in HB'. fold (kn_brk_grant_d DS_E20 101 4096 8192 KN_E20) in HB'. rewrite KNg0_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WLZ (p8 p10 : word) : list (Z * Z) :=
    [(SHB_LO, SHB_HI); (bv_unsigned p8, bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE); (bv_unsigned p10, bv_unsigned p10 + N_PA)].

  #[using="brk mbase draw inp VI VE usp"] Lemma LZ30_shape : forall p8 sb p10 p15,
    bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE <= 2 ^ 63 -> bv_unsigned p10 + N_PA <= 2 ^ 63 ->
    ivs_wf (LZ30 sp p8 sb p10 p15) /\ ivs_pos (LZ30 sp p8 sb p10 p15) /\ ivs_within (LZ30 sp p8 sb p10 p15) (WLZ p8 p10).
  Proof.
    intros p8 sb p10 p15 B8 B10.
    pose proof (x9_facts sp SA16b SLob SHib) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15).
    pose proof HI_A_val as VA. pose proof HI_N_val as VN. pose proof GAP_A_val as GA. pose proof GAP_N_val as GN. pose proof LO_N_val as LN.
    assert (LA : bv_unsigned LO_A = 0x7fff7000) by (vmeq_refl).
    assert (N8 : bv_unsigned (Z_to_bv 64 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE) = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE) by (vmeq_refl).
    assert (N10 : bv_unsigned (Z_to_bv 64 N_PA) = N_PA) by (vmeq_refl).
    pose proof (u64_range p8) as U8. pose proof (u64_range p10) as U10.
    (* [comment removed for export] *)
    assert (S16 : ivs_wf (LZ16 p8) /\ ivs_pos (LZ16 p8) /\ ivs_within (LZ16 p8) (WLZ p8 p10)).
    { unfold LZ16, LZ5. split; [|split].
      - repeat (apply ivs_wf_cons; [apply iv_wf_intro; rewrite ?N8, ?VA, ?VN, ?GA, ?GN, ?LA, ?LN; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE in *; lia|]). apply ivs_wf_nil.
      - repeat (apply ivs_pos_cons; [cbn [snd]; rewrite ?N8, ?VN, ?GN, ?LN; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE; lia|]). apply ivs_pos_nil.
      - apply ivs_within_cons; [exists (bv_unsigned p8, bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE); split; [unfold WLZ; right; left; reflexivity | cbn [fst snd]; rewrite N8; lia]|].
        repeat (apply ivs_within_cons; [exists (SHB_LO, SHB_HI); split; [unfold WLZ; left; reflexivity | cbn [fst snd]; rewrite ?VA, ?VN, ?GA, ?GN, ?LA, ?LN; unfold SHB_LO, SHB_HI; lia]|]).
        apply ivs_within_nil. }
    destruct S16 as (W16 & P16 & I16).
    assert (S17 : ivs_wf (LZ17 p8 sb) /\ ivs_pos (LZ17 p8 sb) /\ ivs_within (LZ17 p8 sb) (WLZ p8 p10)).
    { unfold LZ17. split; [apply maps_subtract_wf; [exact W16 | lia] | split; [apply maps_subtract_pos; assumption | apply maps_subtract_within; assumption]]. }
    destruct S17 as (W17 & P17 & I17).
    assert (S18 : ivs_wf (LZ18 p8 sb p10) /\ ivs_pos (LZ18 p8 sb p10) /\ ivs_within (LZ18 p8 sb p10) (WLZ p8 p10)).
    { unfold LZ18. split; [apply ivs_wf_cons; [apply iv_wf_intro; rewrite N10; unfold N_PA in *; lia | exact W17] | split].
      - apply ivs_pos_cons; [cbn [snd]; rewrite N10; unfold N_PA; lia | exact P17].
      - apply ivs_within_cons; [exists (bv_unsigned p10, bv_unsigned p10 + N_PA); split; [unfold WLZ; do 2 right; left; reflexivity | cbn [fst snd]; rewrite N10; lia] | exact I17]. }
    destruct S18 as (W18 & P18 & I18).
    assert (S24 : ivs_wf (LZ24 p8 sb p10 p15) /\ ivs_pos (LZ24 p8 sb p10 p15) /\ ivs_within (LZ24 p8 sb p10 p15) (WLZ p8 p10)).
    { unfold LZ24. split; [apply maps_subtract_wf; [exact W18 | lia] | split; [apply maps_subtract_pos; assumption | apply maps_subtract_within; assumption]]. }
    destruct S24 as (W24 & P24 & I24).
    (* [comment removed for export] *)
    unfold LZ30. exact (conj W24 (conj P24 I24)).
  Qed.

  #[using="Type"] Lemma L30_maps : l_maps L30 = [(EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096); (EVar 38, 65536); (EVar 37, 4096); (EVar 36, 8388608);
     (EVar 28, 137439023104); (EVar 27, 3727360); (EVar 26, 65536); (ELit 2201439137792, 15392894357504); (ELit 2415882240, 2199023255552);
     (ELit 2147446784, 268435456)].
  Proof. reflexivity. Qed.

  #[using="VI VE usp"] Lemma LZ30_guard_id : forall H A a tid c pl js sr kn hc lz R M mdl p8 sb p10 p15,
    bootS' H A a tid c pl js sr kn (lbrk L30 101 8192) hc lz R M mdl ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 101 = brk ->
    maps_subtract (LZ30 sp p8 sb p10 p15) (bv_unsigned brk) (bv_unsigned brk + 4096) = LZ30 sp p8 sb p10 p15.
  Proof.
    intros H A a tid c pl js sr kn hc lz R M mdl p8 sb p10 p15 HB E28 E36 E101.
    pose proof SLob as SLo. pose proof SHib as SHi.
    destruct HB as [_ _ _ _ _ _ F HMO _ _ _ _].
    assert (EV28 : edenot (EB' a tid c pl js) (EVar 28) = p8) by exact E28.
    assert (EV36 : edenot (EB' a tid c pl js) (EVar 36) = p10) by exact E36.
    assert (EV101 : edenot (EB' a tid c pl js) (EVar 101) = brk) by exact E101.
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. clear F.
    change (l_maps (lbrk L30 101 8192)) with ((EVar 101, 8192) :: l_maps L30) in AP. rewrite L30_maps in AP.
    cbn [dl List.map fst snd ivs_apart] in AP. destruct AP as [AP _]. rewrite EV101, EV28, EV36 in AP.
    repeat (apply Forall_cons_iff in AP as [?X AP]); cbn [fst snd edenot] in *. clear AP.
    clear X X0 X1 X2 X3 X6 X7.
    change (bv_unsigned (Z_to_bv 64 8192)) with 8192 in *. change (bv_unsigned (Z_to_bv 64 8388608)) with 8388608 in *.
    change (bv_unsigned (Z_to_bv 64 137439023104)) with 137439023104 in *.
    change (bv_unsigned (Z_to_bv 64 2201439137792)) with 2201439137792 in *. change (bv_unsigned (Z_to_bv 64 15392894357504)) with 15392894357504 in *.
    change (bv_unsigned (Z_to_bv 64 2415882240)) with 2415882240 in *. change (bv_unsigned (Z_to_bv 64 2199023255552)) with 2199023255552 in *.
    change (bv_unsigned (Z_to_bv 64 2147446784)) with 2147446784 in *. change (bv_unsigned (Z_to_bv 64 268435456)) with 268435456 in *.
    (* [comment removed for export] *)
    pose proof HMO as MO. unfold maps_ok in MO. change (l_maps (lbrk L30 101 8192)) with ((EVar 101, 8192) :: l_maps L30) in MO. rewrite L30_maps in MO.
    assert (M36 : map_ok sp (EB' a tid c pl js) (EVar 36, 8388608)) by (apply (proj1 (Forall_forall _ _) MO); cbn [In]; do 6 right; left; reflexivity).
    assert (M28 : map_ok sp (EB' a tid c pl js) (EVar 28, 137439023104)) by (apply (proj1 (Forall_forall _ _) MO); cbn [In]; do 7 right; left; reflexivity).
    clear MO HMO. unfold map_ok in M36, M28. cbn [fst snd edenot] in M36, M28. rewrite EV36 in M36. rewrite EV28 in M28.
    destruct M36 as (_ & _ & _ & T36 & _). destruct M28 as (_ & _ & _ & T28 & _). unfold stack_max_size in *.
    destruct (LZ30_shape p8 sb p10 p15 ltac:(unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, usp in *; lia) ltac:(unfold N_PA, usp in *; lia)) as (_ & POS & WIN).
    pose proof (u64_range brk) as UB.
    apply (maps_subtract_id_within _ _ _ (WLZ p8 p10)); [lia | exact POS | exact WIN |].
    intros w Hw. unfold WLZ in Hw. cbn [In] in Hw. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold SHB_LO, SHB_HI, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, N_PA; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="usp"] Lemma brk_misses_shadow : forall H A a tid c pl js sr kn hc lz R M mdl,
    bootS' H A a tid c pl js sr kn (lbrk L30 101 8192) hc lz R M mdl ->
    ev (EB' a tid c pl js) 101 = brk ->
    bv_unsigned brk + 8192 <= SHB_LO \/ SHB_HI <= bv_unsigned brk.
  Proof.
    intros H A a tid c pl js sr kn hc lz R M mdl HB E101.
    destruct HB as [_ _ _ _ _ _ F _ _ _ _ _].
    assert (EV101 : edenot (EB' a tid c pl js) (EVar 101) = brk) by exact E101.
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. clear F.
    change (l_maps (lbrk L30 101 8192)) with ((EVar 101, 8192) :: l_maps L30) in AP. rewrite L30_maps in AP.
    cbn [dl List.map fst snd ivs_apart] in AP. destruct AP as [AP _]. rewrite EV101 in AP.
    repeat (apply Forall_cons_iff in AP as [?X AP]); cbn [fst snd edenot] in *. clear AP.
    clear X X0 X1 X2 X3 X4 X5 X6 X7.
    change (bv_unsigned (Z_to_bv 64 8192)) with 8192 in *.
    change (bv_unsigned (Z_to_bv 64 2201439137792)) with 2201439137792 in *. change (bv_unsigned (Z_to_bv 64 15392894357504)) with 15392894357504 in *.
    change (bv_unsigned (Z_to_bv 64 2415882240)) with 2415882240 in *. change (bv_unsigned (Z_to_bv 64 2199023255552)) with 2199023255552 in *.
    change (bv_unsigned (Z_to_bv 64 2147446784)) with 2147446784 in *. change (bv_unsigned (Z_to_bv 64 268435456)) with 268435456 in *.
    unfold SHB_LO, SHB_HI. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation Lg := (lbrk L30 101 8192).
  #[using="VI VE"] Theorem s10_bG1 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRg0 KNg0 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG1 KNG1 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_brk_ecall1 + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_brk_ecall1 with PC_E20. change A_musl_mmap_ecall with PCG1 in HK. rg_block VI VE HB HK runG1_eq carG1_eq. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s10_guard : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), length js = 86%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 101 = brk ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG1 KNG1 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall x : word, bv_unsigned brk <= bv_unsigned x < bv_unsigned brk + 8192 -> H10' p8 sb p10 p12 a W x = false) ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl (js ++ [brk]) SRG1 KNG1u Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hjs E28 E36 E101 HB Hvis HK.
    assert (LEN : length (VB' a tid c pl js) = 102%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (LZ30_guard_id _ _ _ _ _ _ _ _ _ _ _ _ _ _ p8 sb p10 p15 HB E28 E36 E101) as LZID.
    pose proof (bs_mmap_fixed_none_guard sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG1 KNG1 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15)
                  101%nat 4096 8192 A_musl_mmap_ecall (l_maps L30) ECALLW R M mdl K HB fetch_musl_mmap_ecall is_ecall_ECALLW) as X.
    cbv zeta in X. change (ev (EB sp draw inp a tid c pl js) 101) with (ev (EB' a tid c pl js) 101) in X. rewrite E101 in X. apply X; clear X.
    - unfold A_musl_mmap_ecall; clear; lia.
    - unfold A_musl_mmap_ecall; clear; lia.
    - vmeq_refl.
    - replace (sr_get SRG1 10%bv) with (EVar 101) by (vmeq_refl). exact E101.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - reflexivity.
    - reflexivity.
    - clear; lia.
    - exact Hvis.
    - destruct (brk_misses_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB E101) as [B|B]; [left | right]; clear - B; lia.
    - intros R' mdl' HB'. rewrite KNG1u_eq, LZID in HB'.
      pose proof (bs_fresh2 sp brk mbase draw lim inp _ _ a tid c pl js SRG1 KNG1u Lg _ _ R' _ mdl' [brk] SRG1 [] HB') as Y.
      cbv zeta in Y. rewrite LEN in Y. apply (HK R' _ mdl'). apply Y; clear Y.
      + vmeq_refl.
      + vmeq_refl.
      + vmeq_refl.
      + auto.
      + constructor.
  Qed.

  #[using="VI VE"] Theorem s10_bG2 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG1 KNG1u Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG2 KNG2 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_musl_mmap_ecall with PCG1 at 1. change A_musl_mmap_ecall with PCG2 in HK. rg_block VI VE HB HK runG2_eq carG2_eq. Qed.

  #[using="Type"] Lemma DS_E22g_std : DS_std Lg = DS_E22g. Proof. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s10_e22G : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), 2 ^ 25 <= lim -> length js = 87%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG2 KNG2 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall p R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl (js ++ [p]) SRG2g KNG2g (lgrant Lg 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 103%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget10 a tid c pl js p8 sb p10 p12 p15 W _ _ Lg [(EVar 101, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] R M mdl Hlim eq_refl HB E28 E38) as BUD.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG2 KNG2 Lg (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) 4096 A_musl_mmap_ecall ECALLW
              R M mdl K HB fetch_musl_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_musl_mmap_ecall; lia).
    - change (page_round_up_Z 4096) with 4096. change (l_eager Lg) with (15450112 + 8192). clear - BUD. lia.
    - change (page_round_up_Z 4096) with 4096. rewrite (eq_refl : l_maps Lg = (EVar 101, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. apply (HK p). unfold SRG2g.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_E22g_std, KNG2g_eq in HB'. exact HB'.
  Qed.

  #[using="VI VE"] Theorem s10_bG3 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG2g KNG2g (lgrant Lg 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG3 KNG3 (lgrant Lg 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC_T0) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_musl_mmap_ecall with PCG2. change PC_T0 with PCG3 in HK. rg_block VI VE HB HK runG3_eq carG3_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s10_bK1 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRk0 KN_E20 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK1 KNK1 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_brk_ecall1 + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_brk_ecall1 with PC_E20. change A_musl_mmap_ecall with PCK1 in HK. rg_block VI VE HB HK runK1_eq carK1_eq. Qed.

  #[local] Notation Lk1 := (lgrant_nr L30 102 8192).
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s10_e21K : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), length js = 86%nat ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK1 KNK1 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall q R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl (js ++ [q]) SRK1g KNK1g Lk1 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       In (q, Z_to_bv 64 8192) (vm_noaccess (m_vmmaps mdl')) ->
       (forall x : word, bv_unsigned q <= bv_unsigned x < bv_unsigned q + 8192 -> H10' p8 sb p10 p12 a W x = false) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hjs HB HK.
    assert (LEN : length (VB' a tid c pl js) = 102%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (bs_mmap_none_anon sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK1 KNK1 L30 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15)
                  8192 A_musl_mmap_ecall ECALLW R M mdl K HB fetch_musl_mmap_ecall is_ecall_ECALLW) as X.
    cbv zeta in X. rewrite LEN in X. change (page_round_up_Z 8192) with 8192 in X. apply X; clear X.
    - unfold A_musl_mmap_ecall; clear; lia.
    - unfold A_musl_mmap_ecall; clear; lia.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - clear; lia.
    - rewrite L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros q R' mdl' HB' Hna Hvis. apply (HK q R' _ mdl'); [| exact Hna | exact Hvis].
      unfold kn_grant_none in HB'. rewrite DS_E20_std, KNK1g_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  Ltac rg_block_na VI VE HB HK RUN CAR Hna :=
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
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ =>
        let body := eval unfold m in m in
        lazymatch body with munrestrict ?H ?M (mem_denot (EB _ _ _ ?a ?tid ?c ?pl ?js) _ ?lg) =>
          lazymatch type of F with mfacts _ _ _ _ _ _ _ ?L _ =>
            lazymatch type of HZ with hf_ok _ _ ?hc =>
              destruct (frame_blockS sp brk mbase draw inp VI VE H a tid c pl js M lg hc (lows_of L) ltac:(vmeq_refl)
                          (lows_of_ok sp _ L HMO) (rg_above _ _ _ _ _ _ _ RG) HA HZ) as [HA0 HZ0];
              subst m
            end end end end;
      apply HK;
        [ constructor; try assumption;
          [ erewrite sbm_lazy by eassumption; exact HLZ | eapply mfacts_sbm; eassumption | eapply regime_ok_sbm; eassumption]
        | erewrite sbm_vmmaps by eassumption; exact Hna ]
    end.

  #[using="VI VE"] Theorem s10_bK2 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z) (q : word),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK1g KNK1g Lk1 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    In (q, Z_to_bv 64 8192) (vm_noaccess (m_vmmaps mdl)) ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK2 KNK2 Lk1 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       In (q, Z_to_bv 64 8192) (vm_noaccess (m_vmmaps mdl')) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_mprotect_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W q HB Hna HK. change A_musl_mmap_ecall with PCK1. change A_musl_mprotect_ecall with PCK2 in HK. rg_block_na VI VE HB HK runK2_eq carK2_eq Hna. Qed.

  #[local] Notation Lk2 := (lcommit Lk1 4096).
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s10_mprot : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z) (q : word), 2 ^ 25 <= lim ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> ev (EB' a tid c pl js) 102 = q ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK2 KNK2 Lk1 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    In (q, Z_to_bv 64 8192) (vm_noaccess (m_vmmaps mdl)) ->
    (forall x : word, bv_unsigned q <= bv_unsigned x < bv_unsigned q + 8192 -> H10' p8 sb p10 p12 a W x = false) ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK2m KNK2m Lk2 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_musl_mprotect_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_mprotect_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W q Hlim E28 E38 E102 HB Hna Hvis HK.
    pose proof (budget10 a tid c pl js p8 sb p10 p12 p15 W _ _ Lk1 [(EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] R M mdl Hlim eq_refl HB E28 E38) as BUD.
    pose proof (bs_mprotect_rw sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK2 KNK2 Lk1 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15)
                  102%nat 8192 4096 4096 A_musl_mprotect_ecall ECALLW R M mdl K HB fetch_musl_mprotect_ecall is_ecall_ECALLW) as X.
    cbv zeta in X. change (ev (EB sp draw inp a tid c pl js) 102) with (ev (EB' a tid c pl js) 102) in X. rewrite E102 in X. apply X; clear X.
    - unfold A_musl_mprotect_ecall; clear; lia.
    - unfold A_musl_mprotect_ecall; clear; lia.
    - vmeq_refl.
    - replace (sr_get SRK2 10%bv) with (EAlu ALU_ADD (EVar 102) (ELit 4096)) by (vmeq_refl).
      cbn [edenot]. change (ev (EB sp draw inp a tid c pl js) 102) with (ev (EB' a tid c pl js) 102). rewrite E102.
      apply bv_eq. rewrite u_add64. reflexivity.
    - vmeq_refl.
    - vmeq_refl.
    - left. reflexivity.
    - exact Hna.
    - exact Hvis.
    - clear; lia.
    - clear; lia.
    - reflexivity.
    - reflexivity.
    - clear; lia.
    - change (l_eager Lk1) with 15450112. clear - BUD. lia.
    - intros R' mdl' HB'. apply (HK R' _ mdl'). unfold kn_mprotect in HB'. rewrite KNK2m_eq in HB'. exact HB'.
  Qed.

  #[using="VI VE"] Theorem s10_bK3 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK2m KNK2m Lk2 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK3 KNK3 Lk2 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_musl_mprotect_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_musl_mprotect_ecall with PCK2. change A_musl_mmap_ecall with PCK3 in HK. rg_block VI VE HB HK runK3_eq carK3_eq. Qed.

  #[using="Type"] Lemma DS_E22k_std : DS_std Lk2 = DS_E22k. Proof. vmeq_refl. Qed.

  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s10_e22K : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z), 2 ^ 25 <= lim -> length js = 87%nat ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK3 KNK3 Lk2 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall p R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl (js ++ [p]) SRK3g KNK3g (lgrant Lk2 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hlim Hjs E28 E38 HB HK.
    assert (LEN : length (VB' a tid c pl js) = 103%nat) by (rewrite length_VB, Hjs; reflexivity).
    pose proof (budget10 a tid c pl js p8 sb p10 p12 p15 W _ _ Lk2 [(EVar 102, 8192); (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096)] R M mdl Hlim eq_refl HB E28 E38) as BUD.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK3 KNK3 Lk2 (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) 4096 A_musl_mmap_ecall ECALLW
              R M mdl K HB fetch_musl_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_musl_mmap_ecall; lia).
    - change (page_round_up_Z 4096) with 4096. change (l_eager Lk2) with (15450112 + 4096). clear - BUD. lia.
    - change (page_round_up_Z 4096) with 4096. rewrite (eq_refl : l_maps Lk2 = (EVar 102, 8192) :: l_maps L30), L30_maps. cbn [gws]. unfold IMG_HI, stack_max_size. clear. lia.
    - intros p R' M' mdl' HB'. apply (HK p). unfold SRK3g.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_E22k_std, KNK3g_eq in HB'. exact HB'.
  Qed.

  #[using="VI VE"] Theorem s10_bK4 : forall a tid c pl js p8 sb p10 p12 p15 R M mdl K (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK3g KNK3g (lgrant Lk2 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    (forall R' M' mdl', bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK4 KNK4 (lgrant Lk2 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC_T0) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (A_musl_mmap_ecall + 4)) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 p15 R M mdl K W HB HK. change A_musl_mmap_ecall with PCK3. change PC_T0 with PCK4 in HK. rg_block VI VE HB HK runK4_eq carK4_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Theorem s10_joinG : forall a tid c pl js p8 sb p10 p12 p15 R M mdl (W : Z),
    ev (EB' a tid c pl js) 101 = brk -> ev (EB' a tid c pl js) 102 = brk ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRG3 KNG3 (lgrant Lg 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_T0 KN_T0 (L_T0 8192) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl W E101 E102 HB.
    assert (HB1 : bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_T0 KN_T0 (lgrant Lg 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl).
    { eapply bootS_reknow; [exact HB | auto |]. apply know_ok_sub_b. exact (proj1 T0_join). }
    apply (bs_reledger sp brk mbase draw lim inp _ _ a tid c pl js SR_T0 KN_T0 (lgrant Lg 103 4096) (L_T0 8192) _ _ R M mdl HB1).
    - unfold sivden, L_T0, lgrant, lbrk. cbn [l_maps List.map fst snd edenot].
      change (ev (EB sp draw inp a tid c pl js) 102) with (ev (EB' a tid c pl js) 102). change (ev (EB sp draw inp a tid c pl js) 101) with (ev (EB' a tid c pl js) 101).
      rewrite E101, E102. reflexivity.
    - reflexivity.
    - unfold L_T0, lgrant, lbrk. cbn [l_eager]. clear. lia.
  Qed.

  #[using="Type"] Theorem s10_joinK : forall a tid c pl js p8 sb p10 p12 p15 R M mdl (W : Z),
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SRK4 KNK4 (lgrant Lk2 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl ->
    bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_T0 KN_T0 (L_T0 0) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 p15 R M mdl W HB.
    assert (HB1 : bootS' (H10' p8 sb p10 p12 a W) (A10' sb p12 a W) a tid c pl js SR_T0 KN_T0 (lgrant Lk2 103 4096) (hc6 p8 p10) (LZ30 sp p8 sb p10 p15) R M mdl).
    { rewrite <- SRK4_eq. eapply bootS_reknow; [exact HB | auto |]. apply know_ok_sub_b. exact (proj2 T0_join). }
    apply (bs_reledger sp brk mbase draw lim inp _ _ a tid c pl js SR_T0 KN_T0 (lgrant Lk2 103 4096) (L_T0 0) _ _ R M mdl HB1).
    - reflexivity.
    - reflexivity.
    - unfold L_T0, lgrant, lcommit, lgrant_nr. cbn [l_eager]. clear. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="usp"] Lemma ev_last : forall a tid c pl js (w : word) (k : nat), length js = k ->
    ev (EB' a tid c pl (js ++ [w])) (16 + k) = w.
  Proof.
    intros a tid c pl js w k Hk. rewrite (ev_EB_js sp draw inp a tid c pl _ k), app_nth2 by lia. rewrite Hk, Nat.sub_diag. reflexivity.
  Qed.

  #[using="VI VE usp"] Theorem boot_s10b : forall a tid c pl p8 sb p10 p12 p15 (W : Z) js R M mdl K, 2 ^ 25 <= lim -> length js = 86%nat ->
    at_E20' a tid c pl p8 sb p10 p12 p15 W js R M mdl ->
    (forall (lb : Z) ks R' M' mdl', length ks = 2%nat ->
       at_T0 sp brk mbase draw lim inp a tid c pl p8 sb p10 p12 p15 W lb (js ++ ks) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC_T0) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_brk_ecall1) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 p15 W js R M mdl K Hlim Hjs HE HK.
    destruct HE as (HB0 & Hsb & E28 & E29 & E36 & E38 & AP15 & E62 & E63 & E64 & E84 & E85 & WL & WH & E101).
    (* [comment removed for export] *)
    assert (CARRY : forall ks, ev (EB' a tid c pl (js ++ ks)) 28 = p8 /\ ev (EB' a tid c pl (js ++ ks)) 29 = sb /\ ev (EB' a tid c pl (js ++ ks)) 36 = p10
                     /\ ev (EB' a tid c pl (js ++ ks)) 38 = p12 /\ ev (EB' a tid c pl (js ++ ks)) 62 = Z_to_bv 64 (STv sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl (js ++ ks)) 64 = Z_to_bv 64 (PBv sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl (js ++ ks)) 85 = Z_to_bv 64 (Wdst sp)
                     /\ ev (EB' a tid c pl (js ++ ks)) 101 = brk).
    { intros ks. rewrite !ev_EB_app by (rewrite Hjs; lia). repeat split; assumption. }
    apply (s10_e20 a tid c pl js p8 sb p10 p12 p15 R M mdl K W Hlim Hjs HB0 E28 E38 E101).
    - (* [comment removed for export] *)
      intros R1 m1 H1.
      apply (s10_bK1 a tid c pl js p8 sb p10 p12 p15 R1 M m1 K W H1). intros R2 M2 m2 H2.
      apply (s10_e21K a tid c pl js p8 sb p10 p12 p15 R2 M2 m2 K W Hjs H2). intros q R3 M3 m3 H3 Hna Hvis.
      set (js1 := js ++ [q]) in *.
      assert (L1 : length js1 = 87%nat) by (unfold js1; rewrite length_app, Hjs; reflexivity).
      destruct (CARRY [q]) as (F28 & _ & _ & F38 & _). fold js1 in F28, F38.
      assert (F102 : ev (EB' a tid c pl js1) 102 = q) by (unfold js1; exact (ev_last a tid c pl js q 86 Hjs)).
      apply (s10_bK2 a tid c pl js1 p8 sb p10 p12 p15 R3 M3 m3 K W q H3 Hna). intros R4 M4 m4 H4 Hna4.
      apply (s10_mprot a tid c pl js1 p8 sb p10 p12 p15 R4 M4 m4 K W q Hlim F28 F38 F102 H4 Hna4 Hvis). intros R5 M5 m5 H5.
      apply (s10_bK3 a tid c pl js1 p8 sb p10 p12 p15 R5 M5 m5 K W H5). intros R6 M6 m6 H6.
      apply (s10_e22K a tid c pl js1 p8 sb p10 p12 p15 R6 M6 m6 K W Hlim L1 F28 F38 H6). intros p R7 M7 m7 H7.
      apply (s10_bK4 a tid c pl (js1 ++ [p]) p8 sb p10 p12 p15 R7 M7 m7 K W H7). intros R8 M8 m8 H8.
      pose proof (s10_joinK a tid c pl (js1 ++ [p]) p8 sb p10 p12 p15 R8 M8 m8 W H8) as H9.
      apply (HK 0 ([q] ++ [p]) R8 M8 m8); [reflexivity|].
      unfold at_T0. cbv zeta. rewrite app_assoc. fold js1. split; [exact H9|]. split; [left; reflexivity|]. split; [exact Hsb|].
      unfold js1. rewrite <- app_assoc. destruct (CARRY ([q] ++ [p])) as (G28 & G29 & G36 & G38 & G62 & G63 & G64 & G84 & G85 & G101).
      repeat split; assumption.
    - (* [comment removed for export] *)
      intros R1 m1 H1 Hvis.
      apply (s10_bG1 a tid c pl js p8 sb p10 p12 p15 R1 _ m1 K W H1). intros R2 M2 m2 H2.
      apply (s10_guard a tid c pl js p8 sb p10 p12 p15 R2 M2 m2 K W Hjs E28 E36 E101 H2 Hvis). intros R3 M3 m3 H3.
      set (js1 := js ++ [brk]) in *.
      assert (L1 : length js1 = 87%nat) by (unfold js1; rewrite length_app, Hjs; reflexivity).
      destruct (CARRY [brk]) as (F28 & _ & _ & F38 & _). fold js1 in F28, F38.
      apply (s10_bG2 a tid c pl js1 p8 sb p10 p12 p15 R3 M3 m3 K W H3). intros R4 M4 m4 H4.
      apply (s10_e22G a tid c pl js1 p8 sb p10 p12 p15 R4 M4 m4 K W Hlim L1 F28 F38 H4). intros p R5 M5 m5 H5.
      apply (s10_bG3 a tid c pl (js1 ++ [p]) p8 sb p10 p12 p15 R5 M5 m5 K W H5). intros R6 M6 m6 H6.
      destruct (CARRY ([brk] ++ [p])) as (G28 & G29 & G36 & G38 & G62 & G63 & G64 & G84 & G85 & G101).
      assert (G102 : ev (EB' a tid c pl (js1 ++ [p])) 102 = brk).
      { rewrite ev_EB_app by (rewrite L1; lia). unfold js1. exact (ev_last a tid c pl js brk 86 Hjs). }
      assert (G101' : ev (EB' a tid c pl (js1 ++ [p])) 101 = brk) by (unfold js1; rewrite <- app_assoc; exact G101).
      pose proof (s10_joinG a tid c pl (js1 ++ [p]) p8 sb p10 p12 p15 R6 M6 m6 W G101' G102 H6) as H7.
      apply (HK 8192 ([brk] ++ [p]) R6 M6 m6); [reflexivity|].
      unfold at_T0. cbv zeta. rewrite app_assoc. fold js1. split; [exact H7|]. split; [right; reflexivity|]. split; [exact Hsb|].
      unfold js1. rewrite <- app_assoc. repeat split; assumption.
  Qed.

End Theorems.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
