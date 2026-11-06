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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes7_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition sivden (E : env) (l : sivs) : list (word * Z) := List.map (fun p => (edenot E (fst p), snd p)) l.

Lemma sivden_dl : forall E l l', sivden E l' = sivden E l -> dl E l' = dl E l.
Proof.
  intros E l l' H. unfold dl.
  assert (G : forall m, List.map (fun p : expr * Z => (edenot E (fst p), Z_to_bv 64 (snd p))) m
                        = List.map (fun q : word * Z => (fst q, Z_to_bv 64 (snd q))) (sivden E m)).
  { intros m. unfold sivden. rewrite map_map. reflexivity. }
  rewrite (G l), (G l'), H. reflexivity.
Qed.

Lemma sivden_In : forall E l l' p, sivden E l' = sivden E l -> In p l ->
  exists p', In p' l' /\ edenot E (fst p') = edenot E (fst p) /\ snd p' = snd p.
Proof.
  intros E l l' p H Hin.
  assert (Hi : In (edenot E (fst p), snd p) (sivden E l')).
  { rewrite H. unfold sivden. apply in_map_iff. exists p. split; [reflexivity | exact Hin]. }
  unfold sivden in Hi. apply in_map_iff in Hi as (p' & Hp' & Hin'). exists p'. split; [exact Hin'|].
  injection Hp' as H1 H2. split; assumption.
Qed.

Section Theorems16.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="usp"] Theorem bs_reledger : forall H A a tid c pl js sr kn L L' hc lz R M mdl,
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    sivden (EB' a tid c pl js) (l_maps L') = sivden (EB' a tid c pl js) (l_maps L) ->
    l_brk L' = l_brk L -> l_eager L <= l_eager L' ->
    bootS' H A a tid c pl js sr kn L' hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L L' hc lz R M mdl HB HD Hb He.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    pose proof (sivden_dl _ _ _ HD) as DL.
    assert (HD' : sivden (EB' a tid c pl js) (l_maps L) = sivden (EB' a tid c pl js) (l_maps L')) by (symmetry; exact HD).
    constructor; try assumption.
    - destruct F as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15].
      constructor; try assumption.
      + rewrite Hb. exact F6.
      + rewrite DL. exact F8.
      + rewrite DL. exact F9.
      + lia.
    - unfold maps_ok in *. apply Forall_forall. intros p' Hp'.
      destruct (sivden_In _ _ _ p' HD' Hp') as (p & Hp & E1 & E2).
      pose proof (proj1 (Forall_forall _ _) HMO p Hp) as MO. unfold map_ok in *. rewrite <- E1, <- E2. exact MO.
    - destruct RG as [G1 G2 G3 G4 G5 G6 G7 G8]. constructor; try assumption.
      + intros x Hx. destruct (G4 x Hx) as (p & Hp & Hr). destruct (sivden_In _ _ _ p HD Hp) as (p' & Hp' & E1 & E2).
        exists p'. split; [exact Hp'|]. rewrite E1, E2. exact Hr.
      + unfold hf_inmaps in *. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) G5 r Hr0) as (p & Hp & Hr).
        destruct (sivden_In _ _ _ p HD Hp) as (p' & Hp' & E1 & E2). exists p'. split; [exact Hp'|]. rewrite E1, E2. exact Hr.
      + intros x Hx. destruct (G8 x Hx) as (p & Hp & Hr). destruct (sivden_In _ _ _ p HD Hp) as (p' & Hp' & E1 & E2).
        exists p'. split; [exact Hp'|]. rewrite E1, E2. exact Hr.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Theorem bs_forget_regs : forall H A a tid c pl js sr kn L hc lz R M mdl (clob : list reg),
    let v := length (VB' a tid c pl js) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true ->
    ~ In (0%bv : reg) clob -> List.NoDup clob ->
    bootS' H A a tid c pl (js ++ junk_c R clob) (sr_after_call_c sr clob v) kn L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl clob v HB Hsr Hkn HL H0 Hnd.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    constructor; try assumption.
    - rewrite EB_app. unfold v. apply (regs_after_clob clob (VB' a tid c pl js) _ sr R R Hsr HR); [reflexivity | exact H0 | exact Hnd].
    - rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN].
    - apply mfacts_env; assumption.
    - apply maps_ok_env; assumption.
    - apply regime_ok_env; assumption.
  Qed.
End Theorems16.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes7_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition sivden (E : env) (l : sivs) : list (word * Z) := List.map (fun p => (edenot E (fst p), snd p)) l.

Lemma sivden_dl : forall E l l', sivden E l' = sivden E l -> dl E l' = dl E l.
Proof.
  intros E l l' H. unfold dl.
  assert (G : forall m, List.map (fun p : expr * Z => (edenot E (fst p), Z_to_bv 64 (snd p))) m
                        = List.map (fun q : word * Z => (fst q, Z_to_bv 64 (snd q))) (sivden E m)).
  { intros m. unfold sivden. rewrite map_map. reflexivity. }
  rewrite (G l), (G l'), H. reflexivity.
Qed.

Lemma sivden_In : forall E l l' p, sivden E l' = sivden E l -> In p l ->
  exists p', In p' l' /\ edenot E (fst p') = edenot E (fst p) /\ snd p' = snd p.
Proof.
  intros E l l' p H Hin.
  assert (Hi : In (edenot E (fst p), snd p) (sivden E l')).
  { rewrite H. unfold sivden. apply in_map_iff. exists p. split; [reflexivity | exact Hin]. }
  unfold sivden in Hi. apply in_map_iff in Hi as (p' & Hp' & Hin'). exists p'. split; [exact Hin'|].
  injection Hp' as H1 H2. split; assumption.
Qed.

Section Theorems16.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="usp"] Theorem bs_reledger : forall H A a tid c pl js sr kn L L' hc lz R M mdl,
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    sivden (EB' a tid c pl js) (l_maps L') = sivden (EB' a tid c pl js) (l_maps L) ->
    l_brk L' = l_brk L -> l_eager L <= l_eager L' ->
    bootS' H A a tid c pl js sr kn L' hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L L' hc lz R M mdl HB HD Hb He.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    pose proof (sivden_dl _ _ _ HD) as DL.
    assert (HD' : sivden (EB' a tid c pl js) (l_maps L) = sivden (EB' a tid c pl js) (l_maps L')) by (symmetry; exact HD).
    constructor; try assumption.
    - destruct F as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15].
      constructor; try assumption.
      + rewrite Hb. exact F6.
      + rewrite DL. exact F8.
      + rewrite DL. exact F9.
      + lia.
    - unfold maps_ok in *. apply Forall_forall. intros p' Hp'.
      destruct (sivden_In _ _ _ p' HD' Hp') as (p & Hp & E1 & E2).
      pose proof (proj1 (Forall_forall _ _) HMO p Hp) as MO. unfold map_ok in *. rewrite <- E1, <- E2. exact MO.
    - destruct RG as [G1 G2 G3 G4 G5 G6 G7 G8]. constructor; try assumption.
      + intros x Hx. destruct (G4 x Hx) as (p & Hp & Hr). destruct (sivden_In _ _ _ p HD Hp) as (p' & Hp' & E1 & E2).
        exists p'. split; [exact Hp'|]. rewrite E1, E2. exact Hr.
      + unfold hf_inmaps in *. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) G5 r Hr0) as (p & Hp & Hr).
        destruct (sivden_In _ _ _ p HD Hp) as (p' & Hp' & E1 & E2). exists p'. split; [exact Hp'|]. rewrite E1, E2. exact Hr.
      + intros x Hx. destruct (G8 x Hx) as (p & Hp & Hr). destruct (sivden_In _ _ _ p HD Hp) as (p' & Hp' & E1 & E2).
        exists p'. split; [exact Hp'|]. rewrite E1, E2. exact Hr.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Theorem bs_forget_regs : forall H A a tid c pl js sr kn L hc lz R M mdl (clob : list reg),
    let v := length (VB' a tid c pl js) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true ->
    ~ In (0%bv : reg) clob -> List.NoDup clob ->
    bootS' H A a tid c pl (js ++ junk_c R clob) (sr_after_call_c sr clob v) kn L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl clob v HB Hsr Hkn HL H0 Hnd.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    constructor; try assumption.
    - rewrite EB_app. unfold v. apply (regs_after_clob clob (VB' a tid c pl js) _ sr R R Hsr HR); [reflexivity | exact H0 | exact Hnd].
    - rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN].
    - apply mfacts_env; assumption.
    - apply maps_ok_env; assumption.
    - apply regime_ok_env; assumption.
  Qed.
End Theorems16.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
