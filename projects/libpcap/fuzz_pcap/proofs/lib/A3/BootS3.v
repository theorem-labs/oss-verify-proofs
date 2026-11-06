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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState BootH2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3c.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots3_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition L13 : ledger := lgrant L_E6 26 65536.
Lemma DS_E6_eq : DS_std L_E6 = DS_E6. Proof. reflexivity. Qed.
Lemma L13_incl : incl (l_maps L_E6) (l_maps L13). Proof. unfold L13, lgrant. cbn [l_maps]. apply incl_tl, incl_refl. Qed.

(* [comment removed for export] *)
Definition LZ5 : list (word * word) := [(HI_A, HI_N); (GAP_A, GAP_N); (LO_A, LO_N)].

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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma M_E3_fs : forall a tid, m_fs (M_E3 sp brk mbase lim inp a tid) = in_fs inp.
  Proof. intros. unfold M_E3. rewrite m_fs_with_tid. apply m_fs_init_model. Qed.
  #[using="Type"] Lemma M_E3_fds : forall a tid, m_fds (M_E3 sp brk mbase lim inp a tid) = FDS0.
  Proof. intros. unfold M_E3. rewrite m_fds_with_tid, m_fds_init_model. reflexivity. Qed.
  #[using="Type"] Lemma M_E3_tid : forall a tid, m_tid (M_E3 sp brk mbase lim inp a tid) = Some tid.
  Proof. intros. unfold M_E3. rewrite m_tid_with_tid. reflexivity. Qed.

  #[using="VI VE usp"] Lemma at_E6_bootS : forall a tid c pl js R M mdl,
    at_E6 sp brk mbase draw lim inp a tid c pl js R M mdl ->
    bootS' H2 A2 a tid c pl js SR_E6 KN_E6 L_E6 HC5 LZ5 R M mdl.
  Proof.
    intros a tid c pl js R M mdl [G1 G2 G3 G4 G5 G6 G7 G8 G9].
    pose proof (SL' sp brk mbase draw inp VI VE) as SL. pose proof (SH' sp brk mbase draw inp VI VE) as SH.
    pose proof G7 as (T1 & T2 & T3 & T4).
    pose proof (same_but_materialized_frame _ _ G6) as (_ & Svm & Slz & _ & _ & _ & _ & _ & Sfds & _ & _ & Sfs & Sh & Stid & _ & _ & Se).
    assert (ULO : bv_unsigned LO_A = SHB_LO) by (vm_compute; reflexivity).
    assert (EHI : HI_N = Z_to_bv 64 0xdfff0001000) by (apply bv_eq; rewrite HI_N_val; reflexivity).
    assert (EGAP : GAP_N = Z_to_bv 64 (2 ^ 41)) by (apply bv_eq; rewrite GAP_N_val; reflexivity).
    assert (ELO : LO_N = Z_to_bv 64 (2 ^ 28)) by (apply bv_eq; rewrite LO_N_val; reflexivity).
    pose proof (M_E5g_post sp brk mbase lim inp a tid) as P5. pose proof (M_E4g_post sp brk mbase lim inp a tid) as P4.
    pose proof (M_E3g_post sp brk mbase lim inp a tid) as P3. pose proof (M_E3_vm sp brk mbase lim inp a tid) as V3.
    constructor; try assumption.   (* [comment removed for export] *)
    - (* [comment removed for export] *) apply HC5_of_ZR5. exact G4.
    - (* [comment removed for export] *)
      constructor; rewrite ?Svm, ?Slz, ?Sfds, ?Sfs, ?Sh, ?Stid, ?Se.
      + apply M_E5g_halted.
      + rewrite (gp_res _ _ _ _ _ P5), (gp_res _ _ _ _ _ P4), (gp_res _ _ _ _ _ P3), V3. reflexivity.
      + rewrite (gp_isp _ _ _ _ _ P5), (gp_isp _ _ _ _ _ P4), (gp_isp _ _ _ _ _ P3), V3. reflexivity.
      + rewrite (gp_limit _ _ _ _ _ P5), (gp_limit _ _ _ _ _ P4), (gp_limit _ _ _ _ _ P3), V3. reflexivity.
      + rewrite (gp_sbrk _ _ _ _ _ P5), (gp_sbrk _ _ _ _ _ P4), (gp_sbrk _ _ _ _ _ P3), V3. reflexivity.
      + rewrite (gp_brk _ _ _ _ _ P5), (gp_brk _ _ _ _ _ P4), (gp_brk _ _ _ _ _ P3), V3. cbn [vm_brk L_E6 l_brk].
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + rewrite (gp_mbase _ _ _ _ _ P5), (gp_mbase _ _ _ _ _ P4), (gp_mbase _ _ _ _ _ P3), V3. reflexivity.
      + rewrite (gp_maps _ _ _ _ _ P5), (gp_maps _ _ _ _ _ P4), (gp_maps _ _ _ _ _ P3), V3.
        cbn [vm_maps L_E6 l_maps dl List.map fst snd edenot]. rewrite EHI, EGAP, ELO. reflexivity.
      + (* [comment removed for export] *)
        cbn [L_E6 l_maps dl List.map fst snd edenot ivs_apart]. rewrite !u_small by lia.
        repeat split; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; rewrite ?u_small by lia; lia.
      + rewrite (M_E5g_eager sp brk mbase draw lim inp VI VE a tid). cbn. lia.
      + rewrite (gp_fs _ _ _ _ _ P5), (gp_fs _ _ _ _ _ P4), (gp_fs _ _ _ _ _ P3). apply M_E3_fs.
      + rewrite (gp_fds _ _ _ _ _ P5), (gp_fds _ _ _ _ _ P4), (gp_fds _ _ _ _ _ P3). apply M_E3_fds.
      + rewrite (gp_tid _ _ _ _ _ P5), (gp_tid _ _ _ _ _ P4), (gp_tid _ _ _ _ _ P3). apply M_E3_tid.
      + pose proof (M_E5g_wf sp brk mbase draw lim inp VI VE a tid) as W. unfold model_ivs_wf in *. rewrite Svm, Slz. exact W.
      + (* [comment removed for export] *)
        unfold na_clear. rewrite Svm, (gp_noacc _ _ _ _ _ P5), (gp_noacc _ _ _ _ _ P4), (gp_noacc _ _ _ _ _ P3), V3.
        cbn [kind_none vm_noaccess]. split; vm_compute; reflexivity.
    - (* [comment removed for export] *)
      pose proof img_hull as IH.
      unfold maps_ok, L_E6. cbn [l_maps]. unfold A_img_lo, A_img_hi, stack_max_size in *.
      repeat apply Forall_cons; try apply Forall_nil; unfold map_ok; cbn [fst snd edenot]; rewrite ?ev_EB_tls; rewrite ?u_small by lia;
        unfold A_img_lo, A_img_hi, stack_max_size; unfold usp in *; (split; [first [assumption | reflexivity] | lia]).
    - (* [comment removed for export] *)
      apply (regime_H2 sp brk mbase draw inp VI VE); [| apply incl_refl].
      rewrite Slz, M_E5g_lazy. cbn [LAZY_E6 dl List.map fst snd edenot]. rewrite EHI, EGAP, ELO. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s3_e6 : forall a tid c pl js R M mdl K, 2 ^ 25 <= lim -> length js = 10%nat ->
    at_E6 sp brk mbase draw lim inp a tid c pl js R M mdl ->
    (forall p R' M' mdl', bootS' H2 A2 a tid c pl (js ++ [p]) SR13 KN13 L13 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K Hlim Hjs HE HK.
    pose proof (at_E6_bootS _ _ _ _ _ _ _ _ HE) as HB.
    assert (LEN : length (VB sp draw inp a tid c pl js) = 26%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE H2 A2 a tid c pl js SR_E6 KN_E6 L_E6 HC5 LZ5 65536 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - cbn [l_eager L_E6 A_bytes A2]. change (page_round_up_Z 65536) with 65536. lia.
    - vm_compute. intros X; discriminate X.
    - (* [comment removed for export] *)
      intros p R' M' mdl' HB'. apply (HK p). unfold SR13, L13. exact HB'.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s3_b13a : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR13 KN13 L13 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR13a KN13a L13 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC13a) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run13a_eq car13a_eq. Qed.

  #[using="VI VE"] Theorem s3_b13b : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR13a KN13a L13 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR13b KN13b L13 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC13b) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC13a) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run13b_eq car13b_eq. Qed.

  #[using="VI VE"] Theorem s3_b13c : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR13b KN13b L13 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR13c KN13c L13 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC13c) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC13b) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run13c_eq car13c_eq. Qed.

  #[using="VI VE"] Theorem s3_b13d : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR13c KN13c L13 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR13d KN13d L13 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_maxva_smeared) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC13c) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run13d_eq car13d_eq. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma sr13d_a0 : sr_get SR13d 10%bv = smear_reg (EAlu ALU_ADD (EVar 0) (ELit (-160))).
  Proof. pose proof itinerary3c_ok as IT. decompose [and] IT. assumption. Qed.

  #[using="VI VE usp"] Theorem s3_smear : forall a tid c pl js R M mdl,
    bootS' H2 A2 a tid c pl js SR13d KN13d L13 HC5 LZ5 R M mdl -> bootS' H2 A2 a tid c pl js SR14 KN13d L13 HC5 LZ5 R M mdl.
  Proof.
    intros a tid c pl js R M mdl HB. eapply bootS_reknow; [exact HB | | auto].
    intros HR. unfold SR14. apply (regs_ok_upd1 _ SR13d R R 10%bv); [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate X | | intros; reflexivity].
    rewrite (HR 10%bv), sr13d_a0. change (edenot _ (ELit (2 ^ 47 - 1))) with (Z_to_bv 64 (2 ^ 47 - 1)).
    apply smear_reg_val. cbn [edenot]. rewrite ev_EB_sp.
    pose proof (SL' sp brk mbase draw inp VI VE) as SL. pose proof (SH' sp brk mbase draw inp VI VE) as SH.
    rewrite u_add64. change (bv_unsigned (Z_to_bv 64 (-160))) with (2 ^ 64 - 160).
    replace (bv_unsigned sp + (2 ^ 64 - 160)) with ((bv_unsigned sp - 160) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition at_E7 (a tid c : word) (pl : placements) (js : list word) := bootS' H2 A2 a tid c pl js SR_E7 KN_E7 L13 HC5 LZ5.

  #[using="VI VE"] Theorem s3_b14 : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR14 KN13d L13 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', at_E7 a tid c pl js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_maxva_smeared) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K HB HK. unfold at_E7 in HK.
    assert (HK' : forall R' M' mdl', bootS' H2 A2 a tid c pl js SR_E7 KN14 L13 HC5 LZ5 R' M' mdl' ->
              srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K).
    { intros R' M' mdl' HB'. apply HK. rewrite <- KN_E7_eq. apply bootS_gc. exact HB'. }
    clear HK. h2_block VI VE HB HK' run14_eq car14_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem boot_s3 : forall a tid c pl js R M mdl K, 2 ^ 25 <= lim -> length js = 10%nat ->
    at_E6 sp brk mbase draw lim inp a tid c pl js R M mdl ->
    (forall p R' M' mdl', at_E7 a tid c pl (js ++ [p]) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K Hlim Hjs HE HK.
    apply (s3_e6 a tid c pl js R M mdl K Hlim Hjs HE). intros p R1 M1 m1 H1.
    apply (s3_b13a _ _ _ _ _ _ _ _ K H1). intros R2 M2 m2 H2'.
    apply (s3_b13b _ _ _ _ _ _ _ _ K H2'). intros R3 M3 m3 H3.
    apply (s3_b13c _ _ _ _ _ _ _ _ K H3). intros R4 M4 m4 H4.
    apply (s3_b13d _ _ _ _ _ _ _ _ K H4). intros R5 M5 m5 H5.
    apply (s3_b14 _ _ _ _ _ _ _ _ K (s3_smear _ _ _ _ _ _ _ _ H5)). intros R6 M6 m6 H6.
    exact (HK p R6 M6 m6 H6).
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3b.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn3c.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots3_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition L13 : ledger := lgrant L_E6 26 65536.
Lemma DS_E6_eq : DS_std L_E6 = DS_E6. Proof. reflexivity. Qed.
Lemma L13_incl : incl (l_maps L_E6) (l_maps L13). Proof. unfold L13, lgrant. cbn [l_maps]. apply incl_tl, incl_refl. Qed.

(* [comment removed for export] *)
Definition LZ5 : list (word * word) := [(HI_A, HI_N); (GAP_A, GAP_N); (LO_A, LO_N)].

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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma M_E3_fs : forall a tid, m_fs (M_E3 sp brk mbase lim inp a tid) = in_fs inp.
  Proof. intros. unfold M_E3. rewrite m_fs_with_tid. apply m_fs_init_model. Qed.
  #[using="Type"] Lemma M_E3_fds : forall a tid, m_fds (M_E3 sp brk mbase lim inp a tid) = FDS0.
  Proof. intros. unfold M_E3. rewrite m_fds_with_tid, m_fds_init_model. reflexivity. Qed.
  #[using="Type"] Lemma M_E3_tid : forall a tid, m_tid (M_E3 sp brk mbase lim inp a tid) = Some tid.
  Proof. intros. unfold M_E3. rewrite m_tid_with_tid. reflexivity. Qed.

  #[using="VI VE usp"] Lemma at_E6_bootS : forall a tid c pl js R M mdl,
    at_E6 sp brk mbase draw lim inp a tid c pl js R M mdl ->
    bootS' H2 A2 a tid c pl js SR_E6 KN_E6 L_E6 HC5 LZ5 R M mdl.
  Proof.
    intros a tid c pl js R M mdl [G1 G2 G3 G4 G5 G6 G7 G8 G9].
    pose proof (SL' sp brk mbase draw inp VI VE) as SL. pose proof (SH' sp brk mbase draw inp VI VE) as SH.
    pose proof G7 as (T1 & T2 & T3 & T4).
    pose proof (same_but_materialized_frame _ _ G6) as (_ & Svm & Slz & _ & _ & _ & _ & _ & Sfds & _ & _ & Sfs & Sh & Stid & _ & _ & Se).
    assert (ULO : bv_unsigned LO_A = SHB_LO) by (vm_compute; reflexivity).
    assert (EHI : HI_N = Z_to_bv 64 0xdfff0001000) by (apply bv_eq; rewrite HI_N_val; reflexivity).
    assert (EGAP : GAP_N = Z_to_bv 64 (2 ^ 41)) by (apply bv_eq; rewrite GAP_N_val; reflexivity).
    assert (ELO : LO_N = Z_to_bv 64 (2 ^ 28)) by (apply bv_eq; rewrite LO_N_val; reflexivity).
    pose proof (M_E5g_post sp brk mbase lim inp a tid) as P5. pose proof (M_E4g_post sp brk mbase lim inp a tid) as P4.
    pose proof (M_E3g_post sp brk mbase lim inp a tid) as P3. pose proof (M_E3_vm sp brk mbase lim inp a tid) as V3.
    constructor; try assumption.   (* [comment removed for export] *)
    - (* [comment removed for export] *) apply HC5_of_ZR5. exact G4.
    - (* [comment removed for export] *)
      constructor; rewrite ?Svm, ?Slz, ?Sfds, ?Sfs, ?Sh, ?Stid, ?Se.
      + apply M_E5g_halted.
      + rewrite (gp_res _ _ _ _ _ P5), (gp_res _ _ _ _ _ P4), (gp_res _ _ _ _ _ P3), V3. reflexivity.
      + rewrite (gp_isp _ _ _ _ _ P5), (gp_isp _ _ _ _ _ P4), (gp_isp _ _ _ _ _ P3), V3. reflexivity.
      + rewrite (gp_limit _ _ _ _ _ P5), (gp_limit _ _ _ _ _ P4), (gp_limit _ _ _ _ _ P3), V3. reflexivity.
      + rewrite (gp_sbrk _ _ _ _ _ P5), (gp_sbrk _ _ _ _ _ P4), (gp_sbrk _ _ _ _ _ P3), V3. reflexivity.
      + rewrite (gp_brk _ _ _ _ _ P5), (gp_brk _ _ _ _ _ P4), (gp_brk _ _ _ _ _ P3), V3. cbn [vm_brk L_E6 l_brk].
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + rewrite (gp_mbase _ _ _ _ _ P5), (gp_mbase _ _ _ _ _ P4), (gp_mbase _ _ _ _ _ P3), V3. reflexivity.
      + rewrite (gp_maps _ _ _ _ _ P5), (gp_maps _ _ _ _ _ P4), (gp_maps _ _ _ _ _ P3), V3.
        cbn [vm_maps L_E6 l_maps dl List.map fst snd edenot]. rewrite EHI, EGAP, ELO. reflexivity.
      + (* [comment removed for export] *)
        cbn [L_E6 l_maps dl List.map fst snd edenot ivs_apart]. rewrite !u_small by lia.
        repeat split; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; rewrite ?u_small by lia; lia.
      + rewrite (M_E5g_eager sp brk mbase draw lim inp VI VE a tid). cbn. lia.
      + rewrite (gp_fs _ _ _ _ _ P5), (gp_fs _ _ _ _ _ P4), (gp_fs _ _ _ _ _ P3). apply M_E3_fs.
      + rewrite (gp_fds _ _ _ _ _ P5), (gp_fds _ _ _ _ _ P4), (gp_fds _ _ _ _ _ P3). apply M_E3_fds.
      + rewrite (gp_tid _ _ _ _ _ P5), (gp_tid _ _ _ _ _ P4), (gp_tid _ _ _ _ _ P3). apply M_E3_tid.
      + pose proof (M_E5g_wf sp brk mbase draw lim inp VI VE a tid) as W. unfold model_ivs_wf in *. rewrite Svm, Slz. exact W.
      + (* [comment removed for export] *)
        unfold na_clear. rewrite Svm, (gp_noacc _ _ _ _ _ P5), (gp_noacc _ _ _ _ _ P4), (gp_noacc _ _ _ _ _ P3), V3.
        cbn [kind_none vm_noaccess]. split; vm_compute; reflexivity.
    - (* [comment removed for export] *)
      pose proof img_hull as IH.
      unfold maps_ok, L_E6. cbn [l_maps]. unfold A_img_lo, A_img_hi, stack_max_size in *.
      repeat apply Forall_cons; try apply Forall_nil; unfold map_ok; cbn [fst snd edenot]; rewrite ?ev_EB_tls; rewrite ?u_small by lia;
        unfold A_img_lo, A_img_hi, stack_max_size; unfold usp in *; (split; [first [assumption | reflexivity] | lia]).
    - (* [comment removed for export] *)
      apply (regime_H2 sp brk mbase draw inp VI VE); [| apply incl_refl].
      rewrite Slz, M_E5g_lazy. cbn [LAZY_E6 dl List.map fst snd edenot]. rewrite EHI, EGAP, ELO. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s3_e6 : forall a tid c pl js R M mdl K, 2 ^ 25 <= lim -> length js = 10%nat ->
    at_E6 sp brk mbase draw lim inp a tid c pl js R M mdl ->
    (forall p R' M' mdl', bootS' H2 A2 a tid c pl (js ++ [p]) SR13 KN13 L13 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K Hlim Hjs HE HK.
    pose proof (at_E6_bootS _ _ _ _ _ _ _ _ HE) as HB.
    assert (LEN : length (VB sp draw inp a tid c pl js) = 26%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE H2 A2 a tid c pl js SR_E6 KN_E6 L_E6 HC5 LZ5 65536 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - cbn [l_eager L_E6 A_bytes A2]. change (page_round_up_Z 65536) with 65536. lia.
    - vm_compute. intros X; discriminate X.
    - (* [comment removed for export] *)
      intros p R' M' mdl' HB'. apply (HK p). unfold SR13, L13. exact HB'.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s3_b13a : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR13 KN13 L13 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR13a KN13a L13 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC13a) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run13a_eq car13a_eq. Qed.

  #[using="VI VE"] Theorem s3_b13b : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR13a KN13a L13 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR13b KN13b L13 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC13b) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC13a) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run13b_eq car13b_eq. Qed.

  #[using="VI VE"] Theorem s3_b13c : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR13b KN13b L13 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR13c KN13c L13 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC13c) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC13b) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run13c_eq car13c_eq. Qed.

  #[using="VI VE"] Theorem s3_b13d : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR13c KN13c L13 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', bootS' H2 A2 a tid c pl js SR13d KN13d L13 HC5 LZ5 R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_maxva_smeared) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 PC13c) M ROM) mdl) K.
  Proof. intros a tid c pl js R M mdl K HB HK. h2_block VI VE HB HK run13d_eq car13d_eq. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma sr13d_a0 : sr_get SR13d 10%bv = smear_reg (EAlu ALU_ADD (EVar 0) (ELit (-160))).
  Proof. pose proof itinerary3c_ok as IT. decompose [and] IT. assumption. Qed.

  #[using="VI VE usp"] Theorem s3_smear : forall a tid c pl js R M mdl,
    bootS' H2 A2 a tid c pl js SR13d KN13d L13 HC5 LZ5 R M mdl -> bootS' H2 A2 a tid c pl js SR14 KN13d L13 HC5 LZ5 R M mdl.
  Proof.
    intros a tid c pl js R M mdl HB. eapply bootS_reknow; [exact HB | | auto].
    intros HR. unfold SR14. apply (regs_ok_upd1 _ SR13d R R 10%bv); [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate X | | intros; reflexivity].
    rewrite (HR 10%bv), sr13d_a0. change (edenot _ (ELit (2 ^ 47 - 1))) with (Z_to_bv 64 (2 ^ 47 - 1)).
    apply smear_reg_val. cbn [edenot]. rewrite ev_EB_sp.
    pose proof (SL' sp brk mbase draw inp VI VE) as SL. pose proof (SH' sp brk mbase draw inp VI VE) as SH.
    rewrite u_add64. change (bv_unsigned (Z_to_bv 64 (-160))) with (2 ^ 64 - 160).
    replace (bv_unsigned sp + (2 ^ 64 - 160)) with ((bv_unsigned sp - 160) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition at_E7 (a tid c : word) (pl : placements) (js : list word) := bootS' H2 A2 a tid c pl js SR_E7 KN_E7 L13 HC5 LZ5.

  #[using="VI VE"] Theorem s3_b14 : forall a tid c pl js R M mdl K,
    bootS' H2 A2 a tid c pl js SR14 KN13d L13 HC5 LZ5 R M mdl ->
    (forall R' M' mdl', at_E7 a tid c pl js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_maxva_smeared) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K HB HK. unfold at_E7 in HK.
    assert (HK' : forall R' M' mdl', bootS' H2 A2 a tid c pl js SR_E7 KN14 L13 HC5 LZ5 R' M' mdl' ->
              srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K).
    { intros R' M' mdl' HB'. apply HK. rewrite <- KN_E7_eq. apply bootS_gc. exact HB'. }
    clear HK. h2_block VI VE HB HK' run14_eq car14_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem boot_s3 : forall a tid c pl js R M mdl K, 2 ^ 25 <= lim -> length js = 10%nat ->
    at_E6 sp brk mbase draw lim inp a tid c pl js R M mdl ->
    (forall p R' M' mdl', at_E7 a tid c pl (js ++ [p]) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K Hlim Hjs HE HK.
    apply (s3_e6 a tid c pl js R M mdl K Hlim Hjs HE). intros p R1 M1 m1 H1.
    apply (s3_b13a _ _ _ _ _ _ _ _ K H1). intros R2 M2 m2 H2'.
    apply (s3_b13b _ _ _ _ _ _ _ _ K H2'). intros R3 M3 m3 H3.
    apply (s3_b13c _ _ _ _ _ _ _ _ K H3). intros R4 M4 m4 H4.
    apply (s3_b13d _ _ _ _ _ _ _ _ K H4). intros R5 M5 m5 H5.
    apply (s3_b14 _ _ _ _ _ _ _ _ K (s3_smear _ _ _ _ _ _ _ _ H5)). intros R6 M6 m6 H6.
    exact (HK p R6 M6 m6 H6).
  Qed.
End Theorems.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
