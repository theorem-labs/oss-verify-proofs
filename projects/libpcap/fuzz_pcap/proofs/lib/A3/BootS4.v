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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState BootH2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4a__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4e. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4f__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4a__A3.BootKn4a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4a__A3.BootKn4b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4a__A3.BootKn4c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4a__A3.BootKn4d OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4e OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots4_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition L15 : ledger := lgrant L13 27 0x38e000.
Lemma DS_E7_eq : DS_std L13 = DS_E7. Proof. reflexivity. Qed.
Lemma L15_incl : incl (l_maps L_E6) (l_maps L15). Proof. unfold L15, lgrant. cbn [l_maps]. apply incl_tl, L13_incl. Qed.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let envp := in_envp inp.
  Let uid := in_uid inp.
  Let hw := in_hwcap inp.
  Let usp := bv_unsigned sp.

  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation at_E7' := (at_E7 sp brk mbase draw lim inp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s4_e7 : forall a tid c pl js R M mdl K, 2 ^ 25 <= lim -> length js = 11%nat ->
    at_E7' a tid c pl js R M mdl ->
    (forall p R' M' mdl', bootS' H2 A2 a tid c pl (js ++ [p]) SR15 KN15 L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K Hlim Hjs HB HK. unfold at_E7 in HB.
    assert (LEN : length (VB sp draw inp a tid c pl js) = 27%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE H2 A2 a tid c pl js SR_E7 KN_E7 L13 HC5 LZ5 0x38e000 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - cbn [l_eager L13 L_E6 lgrant A_bytes A2]. change (page_round_up_Z 0x38e000) with 0x38e000. lia.
    - vm_compute. intros X; discriminate X.
    - (* [comment removed for export] *)
      intros p R' M' mdl' HB'. apply (HK p). unfold SR15, L15. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s4_b15a : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15 KN15 L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15a KN15a L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15a) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15a_eq car15a_eq. Qed.

  #[using="VI VE"] Theorem s4_b15b : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15a KN15a L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15b KN15b L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15b) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15a) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15b_eq car15b_eq. Qed.

  #[using="VI VE"] Theorem s4_b15c : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15b KN15b L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15c KN15c L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15c) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15b) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15c_eq car15c_eq. Qed.

  #[using="VI VE"] Theorem s4_b15d : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15c KN15c L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15d KN15d L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15d) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15c) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15d_eq car15d_eq. Qed.

  #[using="VI VE"] Theorem s4_b15e : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15d KN15d L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15e KN15e L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15e) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15d) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15e_eq car15e_eq. Qed.

  #[using="VI VE"] Theorem s4_b15f : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15e KN15e L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15f KN15f L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15f) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15e) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15f_eq car15f_eq. Qed.

  #[using="VI VE"] Theorem s4_b15g : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15f KN15f L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15g KN15g L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15g) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15f) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15g_eq car15g_eq. Qed.

  #[using="VI VE"] Theorem s4_b15h : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15g KN15g L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15h KN15h L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15h) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15g) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15h_eq car15h_eq. Qed.

  #[using="VI VE"] Theorem s4_b15i : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15h KN15h L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15i KN15i L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15i) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15h) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15i_eq car15i_eq. Qed.

  #[using="VI VE"] Theorem s4_b15j : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15i KN15i L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15j KN15j L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15j) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15i) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15j_eq car15j_eq. Qed.

  (* [comment removed for export] *)
  Definition at_E8 (a tid c : word) (pl : placements) (js : list word) := bootS' H2 A2 a tid c pl js SR_E8 KN_E8 L15 HC5 LZ5.

  #[using="VI VE"] Theorem s4_b15k : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15j KN15j L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', at_E8 a tid c pl js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15j) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K HB HK. unfold at_E8 in HK.
    assert (HK' : forall R' M' mdl', bootS' H2 A2 a tid c pl js SR_E8 KN15k L15 HC5 LZ5 R' M' mdl' ->
              srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K).
    { intros R' M' mdl' HB'. apply HK. rewrite <- KN_E8_eq. apply bootS_gc. exact HB'. }
    clear HK. h2_block VI VE HB HK' run15k_eq car15k_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem boot_s4 : forall a tid c pl js R M mdl K, 2 ^ 25 <= lim -> length js = 11%nat ->
    at_E7' a tid c pl js R M mdl ->
    (forall p R' M' mdl', at_E8 a tid c pl (js ++ [p]) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K Hlim Hjs HE HK.
    apply (s4_e7 a tid c pl js R M mdl K Hlim Hjs HE). intros p R0 M0 m0 H0.
    apply (s4_b15a _ _ _ _ _ _ _ _ K H0). intros R1 M1 m1 H1.
    apply (s4_b15b _ _ _ _ _ _ _ _ K H1). intros R2 M2 m2 H2.
    apply (s4_b15c _ _ _ _ _ _ _ _ K H2). intros R3 M3 m3 H3.
    apply (s4_b15d _ _ _ _ _ _ _ _ K H3). intros R4 M4 m4 H4.
    apply (s4_b15e _ _ _ _ _ _ _ _ K H4). intros R5 M5 m5 H5.
    apply (s4_b15f _ _ _ _ _ _ _ _ K H5). intros R6 M6 m6 H6.
    apply (s4_b15g _ _ _ _ _ _ _ _ K H6). intros R7 M7 m7 H7.
    apply (s4_b15h _ _ _ _ _ _ _ _ K H7). intros R8 M8 m8 H8.
    apply (s4_b15i _ _ _ _ _ _ _ _ K H8). intros R9 M9 m9 H9.
    apply (s4_b15j _ _ _ _ _ _ _ _ K H9). intros R10 M10 m10 H10.
    apply (s4_b15k _ _ _ _ _ _ _ _ K H10). intros R11 M11 m11 H11.
    exact (HK p R11 M11 m11 H11).
  Qed.
End Theorems.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn3c__B3.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn4a. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4a__A3.BootKn4b.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4a__A3.BootKn4c.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4a__A3.BootKn4d.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4e.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots4_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition L15 : ledger := lgrant L13 27 0x38e000.
Lemma DS_E7_eq : DS_std L13 = DS_E7. Proof. reflexivity. Qed.
Lemma L15_incl : incl (l_maps L_E6) (l_maps L15). Proof. unfold L15, lgrant. cbn [l_maps]. apply incl_tl, L13_incl. Qed.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let envp := in_envp inp.
  Let uid := in_uid inp.
  Let hw := in_hwcap inp.
  Let usp := bv_unsigned sp.

  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation at_E7' := (at_E7 sp brk mbase draw lim inp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s4_e7 : forall a tid c pl js R M mdl K, 2 ^ 25 <= lim -> length js = 11%nat ->
    at_E7' a tid c pl js R M mdl ->
    (forall p R' M' mdl', bootS' H2 A2 a tid c pl (js ++ [p]) SR15 KN15 L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K Hlim Hjs HB HK. unfold at_E7 in HB.
    assert (LEN : length (VB sp draw inp a tid c pl js) = 27%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE H2 A2 a tid c pl js SR_E7 KN_E7 L13 HC5 LZ5 0x38e000 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - cbn [l_eager L13 L_E6 lgrant A_bytes A2]. change (page_round_up_Z 0x38e000) with 0x38e000. lia.
    - vm_compute. intros X; discriminate X.
    - (* [comment removed for export] *)
      intros p R' M' mdl' HB'. apply (HK p). unfold SR15, L15. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s4_b15a : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15 KN15 L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15a KN15a L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15a) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15a_eq car15a_eq. Qed.

  #[using="VI VE"] Theorem s4_b15b : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15a KN15a L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15b KN15b L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15b) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15a) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15b_eq car15b_eq. Qed.

  #[using="VI VE"] Theorem s4_b15c : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15b KN15b L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15c KN15c L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15c) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15b) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15c_eq car15c_eq. Qed.

  #[using="VI VE"] Theorem s4_b15d : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15c KN15c L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15d KN15d L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15d) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15c) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15d_eq car15d_eq. Qed.

  #[using="VI VE"] Theorem s4_b15e : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15d KN15d L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15e KN15e L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15e) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15d) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15e_eq car15e_eq. Qed.

  #[using="VI VE"] Theorem s4_b15f : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15e KN15e L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15f KN15f L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15f) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15e) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15f_eq car15f_eq. Qed.

  #[using="VI VE"] Theorem s4_b15g : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15f KN15f L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15g KN15g L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15g) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15f) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15g_eq car15g_eq. Qed.

  #[using="VI VE"] Theorem s4_b15h : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15g KN15g L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15h KN15h L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15h) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15g) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15h_eq car15h_eq. Qed.

  #[using="VI VE"] Theorem s4_b15i : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15h KN15h L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15i KN15i L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15i) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15h) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15i_eq car15i_eq. Qed.

  #[using="VI VE"] Theorem s4_b15j : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15i KN15i L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR15j KN15j L15 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC15j) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15i) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run15j_eq car15j_eq. Qed.

  (* [comment removed for export] *)
  Definition at_E8 (a tid c : word) (pl : placements) (js : list word) := bootS' H2 A2 a tid c pl js SR_E8 KN_E8 L15 HC5 LZ5.

  #[using="VI VE"] Theorem s4_b15k : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR15j KN15j L15 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', at_E8 a tid c pl js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC15j) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K HB HK. unfold at_E8 in HK.
    assert (HK' : forall R' M' mdl', bootS' H2 A2 a tid c pl js SR_E8 KN15k L15 HC5 LZ5 R' M' mdl' ->
              srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K).
    { intros R' M' mdl' HB'. apply HK. rewrite <- KN_E8_eq. apply bootS_gc. exact HB'. }
    clear HK. h2_block VI VE HB HK' run15k_eq car15k_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem boot_s4 : forall a tid c pl js R M mdl K, 2 ^ 25 <= lim -> length js = 11%nat ->
    at_E7' a tid c pl js R M mdl ->
    (forall p R' M' mdl', at_E8 a tid c pl (js ++ [p]) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K Hlim Hjs HE HK.
    apply (s4_e7 a tid c pl js R M mdl K Hlim Hjs HE). intros p R0 M0 m0 H0.
    apply (s4_b15a _ _ _ _ _ _ _ _ K H0). intros R1 M1 m1 H1.
    apply (s4_b15b _ _ _ _ _ _ _ _ K H1). intros R2 M2 m2 H2.
    apply (s4_b15c _ _ _ _ _ _ _ _ K H2). intros R3 M3 m3 H3.
    apply (s4_b15d _ _ _ _ _ _ _ _ K H3). intros R4 M4 m4 H4.
    apply (s4_b15e _ _ _ _ _ _ _ _ K H4). intros R5 M5 m5 H5.
    apply (s4_b15f _ _ _ _ _ _ _ _ K H5). intros R6 M6 m6 H6.
    apply (s4_b15g _ _ _ _ _ _ _ _ K H6). intros R7 M7 m7 H7.
    apply (s4_b15h _ _ _ _ _ _ _ _ K H7). intros R8 M8 m8 H8.
    apply (s4_b15i _ _ _ _ _ _ _ _ K H8). intros R9 M9 m9 H9.
    apply (s4_b15j _ _ _ _ _ _ _ _ K H9). intros R10 M10 m10 H10.
    apply (s4_b15k _ _ _ _ _ _ _ _ K H10). intros R11 M11 m11 H11.
    exact (HK p R11 M11 m11 H11).
  Qed.
End Theorems.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
