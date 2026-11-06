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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanKnow. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodesDrive AsanHeapKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanMemIsZero. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanMemIsZero.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKn2__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootArith__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKn2__Lib.AsanBootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4f__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn7a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS3 BootS4 BootS5 BootS6 BootS7 BootS8. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS9 BootNodes5. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4a__A3.BootKn4a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn6a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn7a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn8a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS8 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn9b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS9 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes5.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes6. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS10a. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn10a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10a.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn8a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootT0 BootS10b BootToT0. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn10b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootT0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootToT0.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS11w1 BootS11w2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import BootToMain.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootexport_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Definition L_MAIN (lb : Z) : ledger := lgrant (lgrant (lgrant_nr (lgrant (L_T0 lb) 104 1048576) 105 8388608) 106 4096) 107 4096.
Definition LZ_MAIN (sp p8 sb p10 p15 p24 : word) : list (word * word) := (p24, Z_to_bv 64 8388608) :: LZ30 sp p8 sb p10 p15.
(* [comment removed for export] *)
Definition A_MAIN (sp sb p12 a : word) (W : Z) (p24 : word) : list (Z * Z) :=
  (0x7fffa000, 0x7fffa000 + 782336) :: (bv_unsigned p24, bv_unsigned p24 + 4096) :: A10 sp sp sb p12 a W.
Definition H_MAIN (sp p8 sb p10 p12 a : word) (W : Z) (p24 : word) : word -> bool :=
  hcut (hcut (hjoin (H10 sp sp p8 sb p10 p12 a W) p24 8388608) (bv_unsigned p24) 4096) 0x7fffa000 779776.
Definition HC_MAIN (p8 p10 p24 : word) : hfacts := (bv_unsigned p24, bv_unsigned p24 + 8388608, Some (Z_to_bv 8 0)) :: hc6 p8 p10.

Lemma L_MAIN_maps : forall lb, l_maps (L_MAIN lb) =
  [(EVar 107, 4096); (EVar 106, 4096); (EVar 105, 8388608); (EVar 104, 1048576); (EVar 103, 4096); (EVar 102, 8192);
   (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096); (EVar 38, 65536); (EVar 37, 4096); (EVar 36, 8388608);
   (EVar 28, 137439023104); (EVar 27, 3727360); (EVar 26, 65536); (ELit 2201439137792, 15392894357504); (ELit 2415882240, 2199023255552);
   (ELit 2147446784, 268435456)].
Proof. reflexivity. Qed.
Lemma L_MAIN_eager : forall lb, l_eager (L_MAIN lb) = 16519168. Proof. reflexivity. Qed.
Lemma L_MAIN_brk : forall lb, l_brk (L_MAIN lb) = lb. Proof. reflexivity. Qed.

Section Export.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).

  (* [comment removed for export] *)
  Definition world1 : Prop := STv sp <= bv_unsigned sp - 96.

  (* [comment removed for export] *)
  Definition at_mainW (w1 : bool) (a tid c : word) (pl : placements) (p8 sb p10 p12 p15 p24 : word) (W lb : Z) (js : list word)
      (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) : Prop :=
    bootS' (H_MAIN sp p8 sb p10 p12 a W p24) (A_MAIN sp sb p12 a W p24) a tid c pl js
           (if w1 then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.SR_MAIN else A3.BootKn11w2.SR_MAIN) (if w1 then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn8a__A3.BootKn11w1.KN_MAIN else A3.BootKn11w2.KN_MAIN)
           (L_MAIN lb) (HC_MAIN p8 p10 p24) (LZ_MAIN sp p8 sb p10 p15 p24) R M mdl
    /\ (if w1 then world1 else ~ world1) /\ (lb = 0 \/ lb = 8192)
    /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12
    /\ (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15)
    /\ ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js) 64 = Z_to_bv 64 (PBv sp)
    /\ ev (EB' a tid c pl js) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl js) 85 = Z_to_bv 64 (Wdst sp) /\ bv_unsigned sp / 8 + CSH <= W /\ W + 8 <= SHB_HI
    /\ ev (EB' a tid c pl js) 101 = brk
    /\ ev (EB' a tid c pl js) 105 = p24 /\ (bv_unsigned p24 + 8388608 <= SHB_LO \/ SHB_HI <= bv_unsigned p24).

  #[using="Type"] Lemma at_mainW_1 : forall a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    BootS11w1.at_main sp brk mbase draw lim inp a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    at_mainW true a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl.
  Proof. intros. exact H. Qed.
  #[using="Type"] Lemma at_mainW_2 : forall a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    BootS11w2.at_main sp brk mbase draw lim inp a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    at_mainW false a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl.
  Proof.
    intros a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl (HB & HW & REST). split; [exact HB|]. split; [| exact REST].
    unfold BootS11w2.WORLD_OK in HW. unfold world1. lia.
  Qed.

  (* [comment removed for export] *)
  Definition AtMain (ms : machine_state) (mdl : Model) : Prop :=
    exists (w1 : bool) (a tid c : word) (pl : placements) (p8 sb p10 p12 p15 p24 : word) (W lb : Z) (js : list word) R M,
      length js = 92%nat /\ ms = mkst R (Z_to_bv 64 A_main) M ROM
      /\ at_mainW w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem boot_main_cps : forall (K : TSet), 2 ^ 25 <= lim ->
    (forall ms mdl, AtMain ms mdl -> srealizes SEGS (mkCfg ms mdl) K) ->
    srealizes SEGS (init_config SEGS PC0 PH sp brk mbase draw lim inp) K.
  Proof.
    intros K Hlim HK.
    apply (boot_to_main sp brk mbase draw lim inp VI VE (mkPL sp sp sp sp sp sp MV_refused_nometa []) K Hlim).
    - intros a tid c p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM. apply HK.
      exists true, a, tid, c, (mkPL sp sp sp sp sp sp MV_refused_nometa []), p8, sb, p10, p12, p15, p24, W, lb, js, R, M.
      split; [exact Hjs|]. split; [reflexivity|]. apply at_mainW_1. exact HM.
    - intros a tid c p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM. apply HK.
      exists false, a, tid, c, (mkPL sp sp sp sp sp sp MV_refused_nometa []), p8, sb, p10, p12, p15, p24, W, lb, js, R, M.
      split; [exact Hjs|]. split; [reflexivity|]. apply at_mainW_2. exact HM.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem at_main_model : forall ms mdl, AtMain ms mdl ->
    m_halted mdl = None
    /\ m_fds mdl = FDS0 /\ m_fs mdl = in_fs inp
    /\ (exists tid, m_tid mdl = Some tid /\ 0 < bv_unsigned tid < 4194304)
    /\ vm_reserved (m_vmmaps mdl) = segments_reserved SEGS
    /\ vm_init_sp (m_vmmaps mdl) = sp /\ vm_limit (m_vmmaps mdl) = lim /\ vm_start_brk (m_vmmaps mdl) = brk /\ vm_mmap_base (m_vmmaps mdl) = mbase
    /\ (vm_brk (m_vmmaps mdl) = brk \/ vm_brk (m_vmmaps mdl) = Z_to_bv 64 (bv_unsigned brk + 8192))
    /\ model_ivs_wf mdl
    /\ eager_used mdl <= 16519168
    /\ In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000) (vm_maps (m_vmmaps mdl))
    /\ In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) (vm_maps (m_vmmaps mdl))
    /\ region_free (vm_noaccess (m_vmmaps mdl)) (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000) = true
    /\ region_free (vm_noaccess (m_vmmaps mdl)) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000) = true
    /\ region_free (vm_reserved (m_vmmaps mdl)) (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000) = true
    /\ region_free (vm_reserved (m_vmmaps mdl)) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000) = true.
  Proof.
    intros ms mdl (w1 & a & tid & c & pl & p8 & sb & p10 & p12 & p15 & p24 & W & lb & js & R & M & Hjs & -> & (HB & _ & Hlb & _)).
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (ELO : LO_N = Z_to_bv 64 0x10000000) by (apply bv_eq; rewrite LO_N_val; reflexivity).
    assert (EHI : HI_N = Z_to_bv 64 0xdfff0001000) by (apply bv_eq; rewrite HI_N_val; reflexivity).
    pose proof (mf_na _ _ _ _ _ _ _ _ _ F) as [NA1 NA2]. unfold LO_A, HI_A in NA1, NA2. rewrite ELO in NA1. rewrite EHI in NA2.
    split; [exact (mf_halted _ _ _ _ _ _ _ _ _ F)|].
    split; [exact (mf_fds _ _ _ _ _ _ _ _ _ F)|]. split; [exact (mf_fs _ _ _ _ _ _ _ _ _ F)|].
    split; [exists tid; split; [exact (mf_tid _ _ _ _ _ _ _ _ _ F) | exact Ht]|].
    split; [exact (mf_res _ _ _ _ _ _ _ _ _ F)|].
    split; [exact (mf_isp _ _ _ _ _ _ _ _ _ F)|]. split; [exact (mf_lim _ _ _ _ _ _ _ _ _ F)|].
    split; [exact (mf_sbrk _ _ _ _ _ _ _ _ _ F)|]. split; [exact (mf_mb _ _ _ _ _ _ _ _ _ F)|].
    split.
    { rewrite (mf_brk _ _ _ _ _ _ _ _ _ F), L_MAIN_brk. destruct Hlb as [-> | ->]; [left; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned | right; reflexivity]. }
    split; [exact (mf_wf _ _ _ _ _ _ _ _ _ F)|].
    split; [pose proof (mf_eager _ _ _ _ _ _ _ _ _ F) as EG; rewrite L_MAIN_eager in EG; exact EG|].
    split; [rewrite (mf_maps _ _ _ _ _ _ _ _ _ F), L_MAIN_maps; cbn [dl List.map fst snd]; do 17 right; left; reflexivity|].
    split; [rewrite (mf_maps _ _ _ _ _ _ _ _ _ F), L_MAIN_maps; cbn [dl List.map fst snd]; do 15 right; left; reflexivity|].
    split; [exact NA1|]. split; [exact NA2|].
    rewrite (mf_res _ _ _ _ _ _ _ _ _ F). split; vm_compute; reflexivity.
  Qed.
End Export.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn10b. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootT0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS10b.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootToT0.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootToMain.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootexport_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Definition L_MAIN (lb : Z) : ledger := lgrant (lgrant (lgrant_nr (lgrant (L_T0 lb) 104 1048576) 105 8388608) 106 4096) 107 4096.
Definition LZ_MAIN (sp p8 sb p10 p15 p24 : word) : list (word * word) := (p24, Z_to_bv 64 8388608) :: LZ30 sp p8 sb p10 p15.
(* [comment removed for export] *)
Definition A_MAIN (sp sb p12 a : word) (W : Z) (p24 : word) : list (Z * Z) :=
  (0x7fffa000, 0x7fffa000 + 782336) :: (bv_unsigned p24, bv_unsigned p24 + 4096) :: A10 sp sp sb p12 a W.
Definition H_MAIN (sp p8 sb p10 p12 a : word) (W : Z) (p24 : word) : word -> bool :=
  hcut (hcut (hjoin (H10 sp sp p8 sb p10 p12 a W) p24 8388608) (bv_unsigned p24) 4096) 0x7fffa000 780288.
Definition HC_MAIN (p8 p10 p24 : word) : hfacts := (bv_unsigned p24, bv_unsigned p24 + 8388608, Some (Z_to_bv 8 0)) :: hc6 p8 p10.

Lemma L_MAIN_maps : forall lb, l_maps (L_MAIN lb) =
  [(EVar 107, 4096); (EVar 106, 4096); (EVar 105, 8388608); (EVar 104, 1048576); (EVar 103, 4096); (EVar 102, 8192);
   (EVar 83, 11571200); (EVar 60, 4096); (EVar 46, 4096); (EVar 38, 65536); (EVar 37, 4096); (EVar 36, 8388608);
   (EVar 28, 137439023104); (EVar 27, 3727360); (EVar 26, 65536); (ELit 2201439137792, 15392894357504); (ELit 2415882240, 2199023255552);
   (ELit 2147446784, 268435456)].
Proof. reflexivity. Qed.
Lemma L_MAIN_eager : forall lb, l_eager (L_MAIN lb) = 16519168. Proof. reflexivity. Qed.
Lemma L_MAIN_brk : forall lb, l_brk (L_MAIN lb) = lb. Proof. reflexivity. Qed.

Section Export.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).

  (* [comment removed for export] *)
  Definition world1 : Prop := STv sp <= bv_unsigned sp - 96.

  (* [comment removed for export] *)
  Definition at_mainW (w1 : bool) (a tid c : word) (pl : placements) (p8 sb p10 p12 p15 p24 : word) (W lb : Z) (js : list word)
      (R : bvmap 5 word) (M : word -> option byte) (mdl : Model) : Prop :=
    bootS' (H_MAIN sp p8 sb p10 p12 a W p24) (A_MAIN sp sb p12 a W p24) a tid c pl js
           (if w1 then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.SR_MAIN else OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w2.SR_MAIN) (if w1 then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w1.KN_MAIN else OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn10b__B3.BootKn11w2.KN_MAIN)
           (L_MAIN lb) (HC_MAIN p8 p10 p24) (LZ_MAIN sp p8 sb p10 p15 p24) R M mdl
    /\ (if w1 then world1 else ~ world1) /\ (lb = 0 \/ lb = 8192)
    /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12
    /\ (bv_unsigned p15 + 4096 <= 0x2008fff7000 \/ SHB_HI <= bv_unsigned p15)
    /\ ev (EB' a tid c pl js) 62 = Z_to_bv 64 (STv sp) /\ ev (EB' a tid c pl js) 63 = Z_to_bv 64 (XQv sp) /\ ev (EB' a tid c pl js) 64 = Z_to_bv 64 (PBv sp)
    /\ ev (EB' a tid c pl js) 84 = Z_to_bv 64 W /\ ev (EB' a tid c pl js) 85 = Z_to_bv 64 (Wdst sp) /\ bv_unsigned sp / 8 + CSH <= W /\ W + 8 <= SHB_HI
    /\ ev (EB' a tid c pl js) 101 = brk
    /\ ev (EB' a tid c pl js) 105 = p24 /\ (bv_unsigned p24 + 8388608 <= SHB_LO \/ SHB_HI <= bv_unsigned p24).

  #[using="Type"] Lemma at_mainW_1 : forall a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    A3.BootS11w1.TwB.at_main sp brk mbase draw lim inp a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    at_mainW true a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl.
  Proof. intros. exact H. Qed.
  #[using="Type"] Lemma at_mainW_2 : forall a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl,
    A3.BootS11w2.TwB.at_main sp brk mbase draw lim inp a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl ->
    at_mainW false a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl.
  Proof.
    intros a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl (HB & HW & REST). split; [exact HB|]. split; [| exact REST].
    unfold A3.BootS11w2.TwB.WORLD_OK in HW. unfold world1. lia.
  Qed.

  (* [comment removed for export] *)
  Definition AtMain (ms : machine_state) (mdl : Model) : Prop :=
    exists (w1 : bool) (a tid c : word) (pl : placements) (p8 sb p10 p12 p15 p24 : word) (W lb : Z) (js : list word) R M,
      length js = 92%nat /\ ms = mkst R (Z_to_bv 64 A_main) M ROM
      /\ at_mainW w1 a tid c pl p8 sb p10 p12 p15 p24 W lb js R M mdl.

  (* [comment removed for export] *)
  #[using="VI VE"] Theorem boot_main_cps : forall (K : TSet), 2 ^ 25 <= lim ->
    (forall ms mdl, AtMain ms mdl -> srealizes SEGS (mkCfg ms mdl) K) ->
    srealizes SEGS (init_config SEGS PC0 PH sp brk mbase draw lim inp) K.
  Proof.
    intros K Hlim HK.
    apply (boot_to_main sp brk mbase draw lim inp VI VE (mkPL sp sp sp sp sp sp MV_refused_nometa []) K Hlim).
    - intros a tid c p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM. apply HK.
      exists true, a, tid, c, (mkPL sp sp sp sp sp sp MV_refused_nometa []), p8, sb, p10, p12, p15, p24, W, lb, js, R, M.
      split; [exact Hjs|]. split; [reflexivity|]. apply at_mainW_1. exact HM.
    - intros a tid c p8 sb p10 p12 p15 p24 W lb js R M mdl Hjs HM. apply HK.
      exists false, a, tid, c, (mkPL sp sp sp sp sp sp MV_refused_nometa []), p8, sb, p10, p12, p15, p24, W, lb, js, R, M.
      split; [exact Hjs|]. split; [reflexivity|]. apply at_mainW_2. exact HM.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem at_main_model : forall ms mdl, AtMain ms mdl ->
    m_halted mdl = None
    /\ m_fds mdl = FDS0 /\ m_fs mdl = in_fs inp
    /\ (exists tid, m_tid mdl = Some tid /\ 0 < bv_unsigned tid < 4194304)
    /\ vm_reserved (m_vmmaps mdl) = segments_reserved SEGS
    /\ vm_init_sp (m_vmmaps mdl) = sp /\ vm_limit (m_vmmaps mdl) = lim /\ vm_start_brk (m_vmmaps mdl) = brk /\ vm_mmap_base (m_vmmaps mdl) = mbase
    /\ (vm_brk (m_vmmaps mdl) = brk \/ vm_brk (m_vmmaps mdl) = Z_to_bv 64 (bv_unsigned brk + 8192))
    /\ model_ivs_wf mdl
    /\ eager_used mdl <= 16519168
    /\ In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000) (vm_maps (m_vmmaps mdl))
    /\ In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) (vm_maps (m_vmmaps mdl))
    /\ region_free (vm_noaccess (m_vmmaps mdl)) (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000) = true
    /\ region_free (vm_noaccess (m_vmmaps mdl)) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000) = true
    /\ region_free (vm_reserved (m_vmmaps mdl)) (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000) = true
    /\ region_free (vm_reserved (m_vmmaps mdl)) (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000) = true.
  Proof.
    intros ms mdl (w1 & a & tid & c & pl & p8 & sb & p10 & p12 & p15 & p24 & W & lb & js & R & M & Hjs & -> & (HB & _ & Hlb & _)).
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (ELO : LO_N = Z_to_bv 64 0x10000000) by (apply bv_eq; rewrite LO_N_val; reflexivity).
    assert (EHI : HI_N = Z_to_bv 64 0xdfff0001000) by (apply bv_eq; rewrite HI_N_val; reflexivity).
    pose proof (mf_na _ _ _ _ _ _ _ _ _ F) as [NA1 NA2]. unfold LO_A, HI_A in NA1, NA2. rewrite ELO in NA1. rewrite EHI in NA2.
    split; [exact (mf_halted _ _ _ _ _ _ _ _ _ F)|].
    split; [exact (mf_fds _ _ _ _ _ _ _ _ _ F)|]. split; [exact (mf_fs _ _ _ _ _ _ _ _ _ F)|].
    split; [exists tid; split; [exact (mf_tid _ _ _ _ _ _ _ _ _ F) | exact Ht]|].
    split; [exact (mf_res _ _ _ _ _ _ _ _ _ F)|].
    split; [exact (mf_isp _ _ _ _ _ _ _ _ _ F)|]. split; [exact (mf_lim _ _ _ _ _ _ _ _ _ F)|].
    split; [exact (mf_sbrk _ _ _ _ _ _ _ _ _ F)|]. split; [exact (mf_mb _ _ _ _ _ _ _ _ _ F)|].
    split.
    { rewrite (mf_brk _ _ _ _ _ _ _ _ _ F), L_MAIN_brk. destruct Hlb as [-> | ->]; [left; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned | right; reflexivity]. }
    split; [exact (mf_wf _ _ _ _ _ _ _ _ _ F)|].
    split; [pose proof (mf_eager _ _ _ _ _ _ _ _ _ F) as EG; rewrite L_MAIN_eager in EG; exact EG|].
    split; [rewrite (mf_maps _ _ _ _ _ _ _ _ _ F), L_MAIN_maps; cbn [dl List.map fst snd]; do 17 right; left; reflexivity|].
    split; [rewrite (mf_maps _ _ _ _ _ _ _ _ _ F), L_MAIN_maps; cbn [dl List.map fst snd]; do 15 right; left; reflexivity|].
    split; [exact NA1|]. split; [exact NA2|].
    rewrite (mf_res _ _ _ _ _ _ _ _ _ F). split; vm_compute; reflexivity.
  Qed.
End Export.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
