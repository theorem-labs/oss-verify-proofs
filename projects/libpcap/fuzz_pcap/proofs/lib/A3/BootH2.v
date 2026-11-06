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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance booth2_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma fetch_spin_mmapordie : fetch_word SEGS (Z_to_bv 64 A_spin_mmapordie) = Some JSELF. Proof. vm_refl_bv. Qed.
Lemma fetch_spin_noreserve : fetch_word SEGS (Z_to_bv 64 A_spin_noreserve) = Some JSELF. Proof. vm_refl_bv. Qed.
Lemma fetch_internal_mmap_ret_prev : A_internal_mmap_ret = A_internal_mmap_ecall + 4. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition L_E6 : ledger :=
  Ledger [(ELit 0x2008fff7000, 0xdfff0001000); (ELit 0x8fff7000, 2 ^ 41); (ELit 0x7fff7000, 2 ^ 28)] 0 0.
(* [comment removed for export] *)
Definition LAZY_E6 : sivs := [(ELit 0x2008fff7000, 0xdfff0001000); (ELit 0x8fff7000, 2 ^ 41); (ELit 0x7fff7000, 2 ^ 28)].

(* [comment removed for export] *)
Lemma H2_in_maps_L : forall E L, incl (l_maps L_E6) (l_maps L) -> H_in_maps H2 E L.
Proof.
  intros E L HI x Hx. unfold H2 in Hx. apply andb_prop in Hx as [H1 H3]. apply Z.leb_le in H1. apply Z.ltb_lt in H3.
  unfold SHB_LO, SHB_HI in *.
  destruct (Z.lt_ge_cases (bv_unsigned x) 0x8fff7000).
  - exists (ELit 0x7fff7000, 2 ^ 28). split; [apply HI; cbn; tauto|]. cbn [fst snd edenot]. rewrite u_small by lia. lia.
  - destruct (Z.lt_ge_cases (bv_unsigned x) 0x2008fff7000).
    + exists (ELit 0x8fff7000, 2 ^ 41). split; [apply HI; cbn; tauto|]. cbn [fst snd edenot]. rewrite u_small by lia. lia.
    + exists (ELit 0x2008fff7000, 0xdfff0001000). split; [apply HI; cbn; tauto|]. cbn [fst snd edenot]. rewrite u_small by lia. lia.
Qed.

Lemma H2_cover_L : forall E (l : list (word * word)), l = dl E LAZY_E6 -> lazy_cover H2 l A2.
Proof.
  intros E l HL w Hp Hh. exfalso. rewrite HL in Hp. unfold LAZY_E6 in Hp. cbn [dl List.map fst snd edenot] in Hp.
  assert (PB : bv_unsigned (page_base w) <= bv_unsigned w < bv_unsigned (page_base w) + page_size).
  { unfold page_base, page_base_of, page_size. pose proof (u64_range w) as W.
    pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
    rewrite u_small by lia. lia. }
  apply page_in_ranges_true in Hp as (iv & Hin & P1 & P2).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in P1, P2; rewrite !u_small in P1 by lia; rewrite !u_small in P2 by lia;
    (rewrite (H2_in w) in Hh; [discriminate|]); unfold page_size, SHB_LO, SHB_HI in *; lia.
Qed.

Lemma H2_above : forall sp : word, 0x7fff80000000 <= bv_unsigned sp -> forall x : word, bv_unsigned sp <= bv_unsigned x -> H2 x = false.
Proof. intros sp Hsp x Hx. apply H2_out. right. unfold SHB_HI. lia. Qed.

(* [comment removed for export] *)
Definition HC5 : hfacts := [(0x2008fff7000, SHB_HI, Some (Z_to_bv 8 0)); (SHB_LO, SHB_LO + 2 ^ 28, Some (Z_to_bv 8 0))].
Lemma HC5_of_ZR5 : forall H M,
  Forall (fun r => forall x : word, fst r <= bv_unsigned x < snd r -> M x = Some (Z_to_bv 8 0)) (ZR5 ) -> hf_ok H M HC5.
Proof.
  intros H M HZ. unfold hf_ok, HC5. unfold ZR5 in HZ.
  apply Forall_cons_iff in HZ as [Z1 HZ]. apply Forall_cons_iff in HZ as [Z2 _].
  repeat constructor; cbn [fst snd] in *; intros; auto.
Qed.

(* [comment removed for export] *)
Lemma HC5_inmaps : forall E L, incl (l_maps L_E6) (l_maps L) -> hf_inmaps E L HC5.
Proof.
  intros E L HI. unfold hf_inmaps, HC5. unfold SHB_LO, SHB_HI.
  constructor; [| constructor; [| constructor]]; cbn [fst snd].
  - exists (ELit 0x2008fff7000, 0xdfff0001000). split; [apply HI; cbn; tauto|]. cbn [fst snd edenot]. rewrite u_small by lia. lia.
  - exists (ELit 0x7fff7000, 2 ^ 28). split; [apply HI; cbn; tauto|]. cbn [fst snd edenot]. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma regime_H2 : forall sp brk mbase draw inp, valid_input inp -> valid_entry IMG (mkEntry sp brk mbase draw) inp ->
  forall E L mdl, m_vm_lazy mdl = dl E LAZY_E6 -> incl (l_maps L_E6) (l_maps L) -> regime_ok sp H2 A2 HC5 E L mdl.
Proof.
  intros sp brk mbase draw inp VI VE E L mdl HL HI. constructor.
  - apply H2_off.
  - apply A2_wf.
  - apply (H2_cover_L E). exact HL.
  - apply H2_in_maps_L. exact HI.
  - apply HC5_inmaps. exact HI.
  - apply H2_above. apply (SL' sp brk mbase draw inp VI VE).
  - (* [comment removed for export] *)
    intros x Hx. rewrite HL. unfold H2 in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    pose proof (u64_range x) as Xr. unfold SHB_LO, SHB_HI in *.
    assert (PB : bv_unsigned (page_base x) = bv_unsigned x / 4096 * 4096).
    { unfold page_base, page_base_of, page_size. apply u_small.
      pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)). lia. }
    pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
    unfold LAZY_E6, page_in_ranges. cbn [dl List.map fst snd edenot existsb]. rewrite PB, !u_small by lia. unfold page_size.
    destruct (Z.lt_ge_cases (bv_unsigned x) 0x8fff7000);
      [| destruct (Z.lt_ge_cases (bv_unsigned x) 0x2008fff7000)];
      repeat (apply orb_true_intro; first [left; apply andb_true_intro; split; apply Z.leb_le; lia | right]).
  - apply H2_in_maps_L. exact HI.
Qed.

(* [comment removed for export] *)
Ltac h2_block VI VE HB HK RUN CAR := rg_block VI VE HB HK RUN CAR.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance booth2_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma fetch_spin_mmapordie : fetch_word SEGS (Z_to_bv 64 A_spin_mmapordie) = Some JSELF. Proof. vm_refl_bv. Qed.
Lemma fetch_spin_noreserve : fetch_word SEGS (Z_to_bv 64 A_spin_noreserve) = Some JSELF. Proof. vm_refl_bv. Qed.
Lemma fetch_internal_mmap_ret_prev : A_internal_mmap_ret = A_internal_mmap_ecall + 4. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition L_E6 : ledger :=
  Ledger [(ELit 0x2008fff7000, 0xdfff0001000); (ELit 0x8fff7000, 2 ^ 41); (ELit 0x7fff7000, 2 ^ 28)] 0 0.
(* [comment removed for export] *)
Definition LAZY_E6 : sivs := [(ELit 0x2008fff7000, 0xdfff0001000); (ELit 0x8fff7000, 2 ^ 41); (ELit 0x7fff7000, 2 ^ 28)].

(* [comment removed for export] *)
Lemma H2_in_maps_L : forall E L, incl (l_maps L_E6) (l_maps L) -> H_in_maps H2 E L.
Proof.
  intros E L HI x Hx. unfold H2 in Hx. apply andb_prop in Hx as [H1 H3]. apply Z.leb_le in H1. apply Z.ltb_lt in H3.
  unfold SHB_LO, SHB_HI in *.
  destruct (Z.lt_ge_cases (bv_unsigned x) 0x8fff7000).
  - exists (ELit 0x7fff7000, 2 ^ 28). split; [apply HI; cbn; tauto|]. cbn [fst snd edenot]. rewrite u_small by lia. lia.
  - destruct (Z.lt_ge_cases (bv_unsigned x) 0x2008fff7000).
    + exists (ELit 0x8fff7000, 2 ^ 41). split; [apply HI; cbn; tauto|]. cbn [fst snd edenot]. rewrite u_small by lia. lia.
    + exists (ELit 0x2008fff7000, 0xdfff0001000). split; [apply HI; cbn; tauto|]. cbn [fst snd edenot]. rewrite u_small by lia. lia.
Qed.

Lemma H2_cover_L : forall E (l : list (word * word)), l = dl E LAZY_E6 -> lazy_cover H2 l A2.
Proof.
  intros E l HL w Hp Hh. exfalso. rewrite HL in Hp. unfold LAZY_E6 in Hp. cbn [dl List.map fst snd edenot] in Hp.
  assert (PB : bv_unsigned (page_base w) <= bv_unsigned w < bv_unsigned (page_base w) + page_size).
  { unfold page_base, page_base_of, page_size. pose proof (u64_range w) as W.
    pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
    rewrite u_small by lia. lia. }
  apply page_in_ranges_true in Hp as (iv & Hin & P1 & P2).
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in P1, P2; rewrite !u_small in P1 by lia; rewrite !u_small in P2 by lia;
    (rewrite (H2_in w) in Hh; [discriminate|]); unfold page_size, SHB_LO, SHB_HI in *; lia.
Qed.

Lemma H2_above : forall sp : word, 0x7fff80000000 <= bv_unsigned sp -> forall x : word, bv_unsigned sp <= bv_unsigned x -> H2 x = false.
Proof. intros sp Hsp x Hx. apply H2_out. right. unfold SHB_HI. lia. Qed.

(* [comment removed for export] *)
Definition HC5 : hfacts := [(0x2008fff7000, SHB_HI, Some (Z_to_bv 8 0)); (SHB_LO, SHB_LO + 2 ^ 28, Some (Z_to_bv 8 0))].
Lemma HC5_of_ZR5 : forall H M,
  Forall (fun r => forall x : word, fst r <= bv_unsigned x < snd r -> M x = Some (Z_to_bv 8 0)) (ZR5 ) -> hf_ok H M HC5.
Proof.
  intros H M HZ. unfold hf_ok, HC5. unfold ZR5 in HZ.
  apply Forall_cons_iff in HZ as [Z1 HZ]. apply Forall_cons_iff in HZ as [Z2 _].
  repeat constructor; cbn [fst snd] in *; intros; auto.
Qed.

(* [comment removed for export] *)
Lemma HC5_inmaps : forall E L, incl (l_maps L_E6) (l_maps L) -> hf_inmaps E L HC5.
Proof.
  intros E L HI. unfold hf_inmaps, HC5. unfold SHB_LO, SHB_HI.
  constructor; [| constructor; [| constructor]]; cbn [fst snd].
  - exists (ELit 0x2008fff7000, 0xdfff0001000). split; [apply HI; cbn; tauto|]. cbn [fst snd edenot]. rewrite u_small by lia. lia.
  - exists (ELit 0x7fff7000, 2 ^ 28). split; [apply HI; cbn; tauto|]. cbn [fst snd edenot]. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma regime_H2 : forall sp brk mbase draw inp, valid_input inp -> valid_entry IMG (mkEntry sp brk mbase draw) inp ->
  forall E L mdl, m_vm_lazy mdl = dl E LAZY_E6 -> incl (l_maps L_E6) (l_maps L) -> regime_ok sp H2 A2 HC5 E L mdl.
Proof.
  intros sp brk mbase draw inp VI VE E L mdl HL HI. constructor.
  - apply H2_off.
  - apply A2_wf.
  - apply (H2_cover_L E). exact HL.
  - apply H2_in_maps_L. exact HI.
  - apply HC5_inmaps. exact HI.
  - apply H2_above. apply (SL' sp brk mbase draw inp VI VE).
  - (* [comment removed for export] *)
    intros x Hx. rewrite HL. unfold H2 in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    pose proof (u64_range x) as Xr. unfold SHB_LO, SHB_HI in *.
    assert (PB : bv_unsigned (page_base x) = bv_unsigned x / 4096 * 4096).
    { unfold page_base, page_base_of, page_size. apply u_small.
      pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)). lia. }
    pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
    unfold LAZY_E6, page_in_ranges. cbn [dl List.map fst snd edenot existsb]. rewrite PB, !u_small by lia. unfold page_size.
    destruct (Z.lt_ge_cases (bv_unsigned x) 0x8fff7000);
      [| destruct (Z.lt_ge_cases (bv_unsigned x) 0x2008fff7000)];
      repeat (apply orb_true_intro; first [left; apply andb_true_intro; split; apply Z.leb_le; lia | right]).
  - apply H2_in_maps_L. exact HI.
Qed.

(* [comment removed for export] *)
Ltac h2_block VI VE HB HK RUN CAR := rg_block VI VE HB HK RUN CAR.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
