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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootArith__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootArith__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootKn3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require Import BootS2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootState BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn3c__B3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn4a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4f__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn7a BootS3 BootS4. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn6a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn7a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS4.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require Import BootS5 BootS6.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots7_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



(* [comment removed for export] *)
Definition L21 : ledger := lgrant L20 46 4096.
Lemma DS_E13_eq : DS_std L20 = DS_E13. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition SHK (sp : word) : Z := (bv_unsigned sp - 800) / 8 + 0x7fff8000.
Definition PLOK (sp : word) : Z := SHK sp / 4096 * 4096.
Definition PHIK (sp : word) : Z := (SHK sp + 39 + 4095) / 4096 * 4096.
Definition H8 (sp p8 sb p10 p12 : word) : word -> bool := hcut (H7 p8 sb p10 p12) (SHK sp) 39.
Definition A8 (sp sb p12 : word) : list (Z * Z) := (PLOK sp, PHIK sp) :: A7 sb p12.

Lemma shk_facts : forall sp : word, bv_unsigned sp mod 16 = 0 -> 0x7fff80000000 <= bv_unsigned sp -> bv_unsigned sp <= 2 ^ 47 ->
  0x10006fff0000 <= PLOK sp /\ PLOK sp <= SHK sp /\ SHK sp + 39 <= PHIK sp /\ PHIK sp <= SHB_HI
  /\ SHK sp mod 2 = 0 /\ PLOK sp mod 4096 = 0 /\ PHIK sp mod 4096 = 0 /\ PHIK sp <= PLOK sp + 8192
  /\ (bv_unsigned sp - 497) / 8 = SHK sp - 0x7fff8000 + 37 /\ (bv_unsigned sp - 496) / 8 = SHK sp - 0x7fff8000 + 38
  /\ (bv_unsigned sp - stack_max_size) / 8 + 0x7fff8000 + 2 ^ 16 <= SHK sp.
Proof.
  intros sp Hal Hlo Hhi. unfold PLOK, PHIK, SHK, SHB_HI, stack_max_size in *.
  pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as D. set (k := bv_unsigned sp / 16) in *.
  replace ((bv_unsigned sp - 800) / 8) with (2 * k - 100) by (replace (bv_unsigned sp - 800) with ((2 * k - 100) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  replace ((bv_unsigned sp - 497) / 8) with (2 * k - 63) by (apply Z.div_unique with (r := 7); lia).
  replace ((bv_unsigned sp - 496) / 8) with (2 * k - 62) by (replace (bv_unsigned sp - 496) with ((2 * k - 62) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  replace ((bv_unsigned sp - 8 * 1024 * 1024) / 8) with (2 * k - 1048576) by (replace (bv_unsigned sp - 8 * 1024 * 1024) with ((2 * k - 1048576) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  pose proof (rdown_facts (2 * k - 100 + 2147450880) ltac:(lia)) as [R1 R2].
  pose proof (rup_facts (2 * k - 100 + 2147450880 + 39) ltac:(lia)) as [R3 R4].
  pose proof (rdown_ge (2 * k - 100 + 2147450880) 0x10006fff0000 eq_refl ltac:(lia)).
  pose proof (rup_le (2 * k - 100 + 2147450880 + 39) 17594333495296 eq_refl ltac:(lia)).
  repeat split; try lia. replace (2 * k - 100 + 2147450880) with ((k + 1073725390) * 2) by lia. apply Z_mod_mult.
Qed.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let usp := bv_unsigned sp.

  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).
  #[local] Notation at_E13' := (at_E13 sp brk mbase draw lim inp).

  #[using="brk mbase draw inp VI VE"] Lemma SA16 : usp mod 16 = 0. Proof. destruct (Hsp sp brk mbase draw inp VI VE) as (_ & _ & H). exact H. Qed.

  #[using="Type"] Lemma ivs_apart_app_r : forall pre l, ivs_apart (pre ++ l) -> ivs_apart l.
  Proof. intros pre l. induction pre as [|[b n] pre IH]; cbn [ivs_apart app]; intros Hx; [exact Hx | apply IH; exact (proj2 Hx)]. Qed.

  (* [comment removed for export] *)
  #[using="usp"] Lemma p8_factsG : forall L pre H A a tid c pl js sr kn hc lz R M mdl p8,
    l_maps L = pre ++ l_maps L20 ->
    bootS' H A a tid c pl js sr kn L hc lz R M mdl -> ev (EB' a tid c pl js) 28 = p8 ->
    bv_unsigned p8 mod 4096 = 0 /\ SHB_HI <= bv_unsigned p8 /\ bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE <= bv_unsigned sp - stack_max_size.
  Proof.
    intros L pre H A a tid c pl js sr kn hc lz R M mdl p8 HL HB E28.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (EV28 : edenot (EB' a tid c pl js) (EVar 28) = p8) by exact E28.
    pose proof HMO as MO. unfold maps_ok in MO. rewrite HL in MO. apply Forall_app in MO as [_ MO].
    unfold L20, L19, L18, L17, L16, lgrant, lgrant_nr, lcommit in MO. cbn [l_maps] in MO.
    do 3 (apply Forall_cons_iff in MO as [_ MO]). apply Forall_cons_iff in MO as [M28 _]. unfold map_ok in M28. cbn [fst snd] in M28. rewrite EV28 in M28.
    destruct M28 as (Mal & M4k & Mn & Mtop & Mimg).
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. rewrite HL in AP. unfold dl in AP. rewrite List.map_app in AP. apply ivs_apart_app_r in AP.
    fold (dl (EB' a tid c pl js) (l_maps L20)) in AP.
    unfold L20, L19, L18, L17, L16, L15, L13, L_E6, lgrant, lgrant_nr, lcommit in AP.
    cbn [l_maps dl List.map fst snd ivs_apart] in AP. rewrite EV28 in AP. destruct AP as (_ & _ & _ & AP & _).
    repeat (apply Forall_cons_iff in AP as [?X AP]); cbn [fst snd edenot] in *.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_HI in *. rewrite !u_small in X1, X2, X3 by lia. unfold stack_max_size in *. lia.
  Qed.

  #[using="usp"] Lemma p12_factsG : forall L pre H A a tid c pl js sr kn hc lz R M mdl p8 p12,
    l_maps L = pre ++ l_maps L20 ->
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bv_unsigned p12 mod 4096 = 0 /\ IMG_HI <= bv_unsigned p12 /\ bv_unsigned p12 + 65536 <= bv_unsigned sp - stack_max_size
    /\ (bv_unsigned p12 + 65536 <= SHB_LO \/ SHB_HI <= bv_unsigned p12)
    /\ (bv_unsigned p12 + 65536 <= bv_unsigned p8 \/ bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE <= bv_unsigned p12).
  Proof.
    intros L pre H A a tid c pl js sr kn hc lz R M mdl p8 p12 HL HB E28 E38.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (EV38 : edenot (EB' a tid c pl js) (EVar 38) = p12) by exact E38.
    assert (EV28 : edenot (EB' a tid c pl js) (EVar 28) = p8) by exact E28.
    pose proof HMO as MO. unfold maps_ok in MO. rewrite HL in MO. apply Forall_app in MO as [_ MO]. unfold L20, lgrant in MO. cbn [l_maps] in MO.
    apply Forall_cons_iff in MO as [M38 _]. unfold map_ok in M38. cbn [fst snd] in M38. rewrite EV38 in M38.
    destruct M38 as (Mal & M4k & Mn & Mtop & Mimg).
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. rewrite HL in AP. unfold dl in AP. rewrite List.map_app in AP. apply ivs_apart_app_r in AP.
    fold (dl (EB' a tid c pl js) (l_maps L20)) in AP.
    unfold L20, L19, L18, L17, L16, L15, L13, L_E6, lgrant, lgrant_nr, lcommit in AP.
    cbn [l_maps dl List.map fst snd ivs_apart] in AP. rewrite EV38, EV28 in AP. destruct AP as [AP _].
    repeat (apply Forall_cons_iff in AP as [?X AP]); cbn [fst snd edenot] in *.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_LO, SHB_HI, IMG_HI, A_img_lo, A_img_hi in *.
    rewrite !u_small in X1 by lia. rewrite !u_small in X4, X5, X6 by lia. unfold stack_max_size in *. lia.
  Qed.
  #[using="Type"] Lemma L21_ext : l_maps L21 = [(EVar 46, 4096)] ++ l_maps L20. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s7_e13 : forall a tid c pl p8 sb p10 p12 js R M mdl K, 2 ^ 25 <= lim -> length js = 30%nat ->
    at_E13' a tid c pl p8 sb p10 p12 js R M mdl ->
    (forall p13 R' M' mdl', bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl (js ++ [p13]) SR21 KN21 L21 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 js R M mdl K Hlim Hjs (HB & Hsb & E28 & E29 & E36 & E38) HK.
    assert (LEN : length (VB' a tid c pl js) = 46%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    pose proof (p12_facts sp brk mbase draw lim inp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR_E13 KN_E13 L20 (hc6 p8 p10) (LZ18 p8 sb p10) 4096 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - cbn [l_eager L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit A_bytes A7 A5 fst snd]. change (page_round_up_Z 4096) with 4096.
      destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia.
    - cbn [l_maps L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit gws]. change (page_round_up_Z 4096) with 4096. unfold N_PA, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, IMG_HI, stack_max_size. lia.
    - (* [comment removed for export] *)
      intros p R' M' mdl' HB'. rewrite <- fetch_internal_mmap_ret_prev. apply (HK p). unfold SR21, L21.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_E13_eq, KN21_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s7_expose : forall a tid c pl js p8 sb p10 p12 R M mdl, 2 ^ 25 <= lim -> bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR21 KN21 L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21 KN21y L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl Hlim Hsb E28 E38 HB.
    pose proof (p12_factsG L21 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L21_ext HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (p8_factsG L21 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L21_ext HB E28) as (P1 & P2 & P3).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (shk_facts sp SA16 SLo SHi) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11).
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    unfold SBV in Hsb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_HI, stack_max_size in P2, P3, Q3, Q5. unfold SHB_HI, stack_max_size in Y4, Y11.
    assert (SHv : bv_unsigned (edenot (EB sp draw inp a tid c pl js) EBK) + EOK = SHK sp).
    { unfold EBK, ESB, EOK, SHK. rewrite (shx_val_gen _ 0 (-800)) by (rewrite ev_EB_sp; lia). rewrite ev_EB_sp. reflexivity. }
    assert (HX : bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21 KN21x L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl).
    { unfold H8, A8. rewrite <- KN21x_eq. unfold xpose21.
      pose proof (bs_expose2 sp brk mbase draw lim inp VI VE (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR21 KN21 L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl
                    EBK EOK 39 (PLOK sp) (PHIK sp - PLOK sp) 0x2008fff7000 SHB_HI) as X.
      cbv zeta in X. rewrite SHv in X. replace (PLOK sp + (PHIK sp - PLOK sp)) with (PHIK sp) in X by lia.
      apply X; clear X; try assumption; try reflexivity; try (unfold SHB_HI, stack_max_size in *; lia).
      - rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, Y6, Y7. reflexivity.
      - intros x Hx. unfold H7, H6, H5, H4, H3.
        apply (proj2 (hcut_true _ _ _ _)). split.
        2:{ right. unfold SH12. pose proof (Z.div_mod (bv_unsigned p12) 4096 ltac:(lia)) as D12. set (k := bv_unsigned p12 / 4096) in D12.
            assert (E8a : bv_unsigned p12 / 8 = 512 * k) by (replace (bv_unsigned p12) with (512 * k * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
            assert (E8 : (bv_unsigned p12 + 65536) / 8 = 512 * k + 8192).
            { replace (bv_unsigned p12 + 65536) with ((512 * k + 8192) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
            pose proof (Z.div_le_mono (bv_unsigned p12 + 65536) (bv_unsigned sp - 8 * 1024 * 1024) 8 ltac:(lia) ltac:(lia)) as DL. lia. }
        apply hjoin_old. apply (proj2 (hcut_true _ _ _ _)). split.
        2:{ right. unfold SHRI, RI. pose proof (Z.div_mod (bv_unsigned p8) 65536 ltac:(lia)) as D8. set (q := bv_unsigned p8 / 65536) in *.
            assert (E8 : (bv_unsigned sb + 2 ^ 37) / 8 = 8192 * (q + 1) + 2 ^ 34).
            { replace (bv_unsigned sb + 2 ^ 37) with ((8192 * (q + 1) + 2 ^ 34) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
            assert (E9 : (bv_unsigned sb + 2 ^ 37 + 4096) / 8 = 8192 * (q + 1) + 2 ^ 34 + 512).
            { replace (bv_unsigned sb + 2 ^ 37 + 4096) with ((8192 * (q + 1) + 2 ^ 34 + 512) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
            pose proof (Z.div_le_mono (bv_unsigned sb + 2 ^ 37 + 4096) (bv_unsigned sp - 8 * 1024 * 1024) 8 ltac:(lia) ltac:(lia)) as DL. lia. }
        apply (proj2 (hcut_true _ _ _ _)). split; [| left; unfold RI; lia].
        apply hjoin_old. apply H2_in. unfold SHB_LO, SHB_HI in *. lia.
      - cbn. do 2 right. left. reflexivity.
      - cbn [l_eager L21 L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit A_bytes A7 A5 fst snd].
        destruct Q4 as [HL|HH]; [pose proof (sh12_L p12 Q1 Q2 HL) | pose proof (sh12_H p12 Q1 HH ltac:(unfold stack_max_size in *; lia))]; lia. }
    (* [comment removed for export] *)
    eapply bootS_reknow; [exact HX | auto |]. intros HKN. constructor; [| exact HKN].
    apply Forall_inv in HKN. cbn [kentry_ok] in HKN. destruct HKN as [_ Z39]. unfold estart, elenZ in Z39. cbn [a_base a_off] in Z39.
    fold (EB sp draw inp a tid c pl js) in Z39. unfold EBK, ESB, EOK in SHv. rewrite SHv in Z39. change (edenot _ (ELit 39)) with (Z_to_bv 64 39) in Z39. rewrite u_small in Z39 by lia.
    unfold KZ21e. cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off]. unfold ESB, EOK.
    rewrite (shx_val_gen _ 0 (-497)) by (rewrite ev_EB_sp; lia). rewrite ev_EB_sp. replace (bv_unsigned sp + -497) with (bv_unsigned sp - 497) by lia. rewrite Y9.
    change (edenot _ (ELit 1)) with (Z_to_bv 64 1). rewrite !u_small by lia.
    split; [lia|]. intros i Hi. replace (SHK sp - 2147450880 + 37 + 2147450880 + i) with (SHK sp + (37 + i)) by lia. apply Z39. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s7_b21a : forall a tid c pl js p8 sb p10 p12 R M mdl K,
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21 KN21y L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21a KN21a L21 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_mem_is_zero) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 R M mdl K HB HK. rg_block VI VE HB HK run21a_eq car21a_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s7_miz : forall a tid c pl js p8 sb p10 p12 R M mdl K, length js = 31%nat ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21a KN21a L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl (js ++ junk_c R' memisz_clob) SR21m KN21m L21 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 RET21) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_mem_is_zero) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hjs HB HK.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (shk_facts sp SA16 SLo SHi) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11).
    assert (LEN : length (VB' a tid c pl js) = 47%nat) by (rewrite length_VB, Hjs; reflexivity).
    assert (SHv : bv_unsigned (edenot (EB sp draw inp a tid c pl js) EBK) + EOK = SHK sp).
    { unfold EBK, ESB, EOK, SHK. rewrite (shx_val_gen _ 0 (-800)) by (rewrite ev_EB_sp; lia). rewrite ev_EB_sp. reflexivity. }
    assert (SPv : bv_unsigned (edenot (EB sp draw inp a tid c pl js) (EVar 0)) + SO21 = usp - 3088).
    { change (edenot _ (EVar 0)) with (ev (EB sp draw inp a tid c pl js) 0). rewrite ev_EB_sp. reflexivity. }
    (* [comment removed for export] *)
    assert (HBw : bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21a KN21w L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl).
    { rewrite <- KN21w_eq. eapply bootS_reknow; [exact HB | auto |]. apply kz_deep_sound. }
    pose proof (cross_mem_is_zero sp brk mbase draw lim inp VI VE memisz_clob (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21a KN21w L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl
                  EBK EOK (EVar 0) SO21 IZ21a IW21a EOK 39 (- 0x800000) 0x800000 38 RET21 K HBw) as X.
    cbv zeta in X. rewrite LEN, SHv, SPv in X. unfold SO21 in X. apply X; clear X.
    - intros r Hr. exact Hr.
    - cbn. intros Hx. repeat (destruct Hx as [Hx|Hx]; [discriminate|]). exact Hx.
    - unfold memisz_clob. repeat (constructor; [cbn; intros Hx; repeat (destruct Hx as [Hx|Hx]; [discriminate|]); exact Hx|]). constructor.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - reflexivity.
    - exact E21_split10.
    - replace (sr_get SR21a 11%bv) with
        (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 0) (ELit (-800))) (ELit 3)))
                      (EAlu ALU_SRL (EAlu ALU_ADD (EVar 0) (ELit (-496))) (ELit 3)))
        by (vmeq_refl).
      apply bv_eq. rewrite (shsub_val _ 0 (-800) (-496)); rewrite ?ev_EB_sp; try lia.
      replace (bv_unsigned sp + -496) with (bv_unsigned sp - 496) by lia. replace (bv_unsigned sp + -800) with (bv_unsigned sp - 800) by lia.
      rewrite Y10. unfold SHK. rewrite u_small by lia. lia.
    - lia.
    - rewrite E21_split2. reflexivity.
    - vmeq_refl.
    - apply bv_eq. vmeq_refl.
    - exact KN21a_iZ.
    - lia.
    - lia.
    - lia.
    - exact KN21a_iW.
    - lia.
    - lia.
    - lia.
    - lia.
    - unfold SHB_HI, stack_max_size in *. lia.
    - lia.
    - lia.
    - unfold SHB_HI, stack_max_size in *. lia.
    - intros R' M' mdl' HB'. apply HK. rewrite <- SR21m_eq, <- KN21m_eq. unfold miz21. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s7_b21b : forall a tid c pl js p8 sb p10 p12 R M mdl K,
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21m KN21m L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21b KN21b L21 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_memset) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 RET21) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 p12 R M mdl K HB HK. rg_block VI VE HB HK run21b_eq car21b_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s7_memset : forall a tid c pl js p8 sb p10 p12 R M mdl K, length js = 38%nat ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21b KN21b L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl (js ++ junk_c R' memset_clob) SR21n KN21n L21 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 RET21c) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hjs HB HK.
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (LEN : length (VB' a tid c pl js) = 54%nat) by (rewrite length_VB, Hjs; reflexivity).
    assert (SPv : bv_unsigned (edenot (EB sp draw inp a tid c pl js) (EVar 0)) + EO21c = usp - 800).
    { change (edenot _ (EVar 0)) with (ev (EB sp draw inp a tid c pl js) 0). rewrite ev_EB_sp. reflexivity. }
    pose proof (cross_musl_memset_c sp brk mbase draw lim inp VI VE memset_clob (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21b KN21b L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl
                  (EVar 0) EO21c IW21b (- 0x800000) 0x800000 0 304 RET21c K HB) as X.
    cbv zeta in X. rewrite LEN, SPv in X. unfold EO21c in X. apply X; clear X.
    - intros r Hr. exact Hr.
    - cbn. intros Hx. repeat (destruct Hx as [Hx|Hx]; [discriminate|]). exact Hx.
    - unfold memset_clob. repeat (constructor; [cbn; intros Hx; repeat (destruct Hx as [Hx|Hx]; [discriminate|]); exact Hx|]). constructor.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - reflexivity.
    - rewrite E21c_split. reflexivity.
    - vmeq_refl.
    - lia.
    - replace (sr_get SR21b 12%bv) with (ELit 304) by (vmeq_refl). reflexivity.
    - lia.
    - vmeq_refl.
    - apply bv_eq. vmeq_refl.
    - exact KN21b_iW.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - intros R' M' mdl' HB'. apply HK. rewrite <- SR21n_eq, <- KN21n_eq. unfold mset21. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition at_E14 (a tid c : word) (pl : placements) (p8 sb p10 p12 : word) (js : list word) R M mdl : Prop :=
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E14 KN_E14 L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12.

  #[using="VI VE"] Theorem s7_b21c : forall a tid c pl js p8 sb p10 p12 R M mdl K, bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 29 = sb -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR21n KN21n L21 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', at_E14 a tid c pl p8 sb p10 p12 js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 RET21c) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hsb E28 E29 E36 E38 HB HK.
    assert (HK' : forall R' M' mdl', bootS' (H8 sp p8 sb p10 p12) (A8 sp sb p12) a tid c pl js SR_E14 KN_E14 L21 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K).
    { intros R' M' mdl' HB'. apply HK. split; [exact HB' | repeat split; assumption]. }
    clear HK. rg_block VI VE HB HK' run21c_eq car21c_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem boot_s7 : forall a tid c pl p8 sb p10 p12 js R M mdl K, 2 ^ 25 <= lim -> length js = 30%nat ->
    at_E13' a tid c pl p8 sb p10 p12 js R M mdl ->
    (forall p13 ks R' M' mdl', length ks = 13%nat ->
       at_E14 a tid c pl p8 sb p10 p12 ((js ++ [p13]) ++ ks) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb p10 p12 js R M mdl K Hlim Hjs HE HK. pose proof HE as (_ & Hsb & E28 & E29 & E36 & E38).
    apply (s7_e13 a tid c pl p8 sb p10 p12 js R M mdl K Hlim Hjs HE). intros p13 R0 M0 m0 H0.
    set (js1 := js ++ [p13]) in *.
    assert (L1 : length js1 = 31%nat) by (unfold js1; rewrite length_app, Hjs; reflexivity).
    assert (FX : forall ks, ev (EB' a tid c pl (js1 ++ ks)) 28 = p8 /\ ev (EB' a tid c pl (js1 ++ ks)) 29 = sb
                            /\ ev (EB' a tid c pl (js1 ++ ks)) 36 = p10 /\ ev (EB' a tid c pl (js1 ++ ks)) 38 = p12).
    { intros ks. unfold js1. rewrite <- app_assoc, !ev_EB_app by (rewrite Hjs; lia). repeat split; assumption. }
    destruct (FX []) as (F28 & F29 & F36 & F38). rewrite app_nil_r in F28, F29, F36, F38.
    pose proof (s7_expose a tid c pl js1 p8 sb p10 p12 R0 M0 m0 Hlim Hsb F28 F38 H0) as H1.
    apply (s7_b21a _ _ _ _ _ _ _ _ _ _ _ _ K H1). intros R2 M2 m2 H2'.
    apply (s7_miz a tid c pl js1 p8 sb p10 p12 R2 M2 m2 K L1 H2'). intros R3 M3 m3 H3'.
    apply (s7_b21b _ _ _ _ _ _ _ _ _ _ _ _ K H3'). intros R4 M4 m4 H4'.
    assert (L2 : length (js1 ++ junk_c R3 memisz_clob) = 38%nat) by (rewrite length_app, L1; reflexivity).
    apply (s7_memset a tid c pl _ p8 sb p10 p12 R4 M4 m4 K L2 H4'). intros R5 M5 m5 H5'.
    rewrite <- app_assoc in H5'.
    destruct (FX (junk_c R3 memisz_clob ++ junk_c R5 memset_clob)) as (G28 & G29 & G36 & G38).
    apply (s7_b21c _ _ _ _ _ _ _ _ _ _ _ _ K Hsb G28 G29 G36 G38 H5'). intros R6 M6 m6 H6'.
    exact (HK p13 (junk_c R3 memisz_clob ++ junk_c R5 memset_clob) R6 M6 m6 eq_refl H6').
  Qed.
End Theorems.
