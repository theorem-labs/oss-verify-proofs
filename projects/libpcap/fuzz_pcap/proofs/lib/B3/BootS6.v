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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootArith__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBootTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require Import BootS2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootState BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn3c__B3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn4a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4f__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS3 BootS4. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn6a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS4.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require Import BootS5.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots6_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Definition N_PA : Z := 0x800000.
Definition L18 : ledger := lgrant_nr L17 36 N_PA.
Definition L19 : ledger := lgrant L18 37 4096.
Definition L20 : ledger := lgrant L19 38 65536.
Lemma DS_E10_eq : DS_std L17 = DS_E10. Proof. reflexivity. Qed.
Lemma DS_E11_eq : DS_std L18 = DS_E11. Proof. reflexivity. Qed.
Lemma DS_E12_eq : DS_std L19 = DS_E12. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition H6 (p8 sb p10 : word) : word -> bool := hjoin (H5 p8 sb) p10 N_PA.
Definition hc6 (p8 p10 : word) : hfacts := (bv_unsigned p10, bv_unsigned p10 + N_PA, None) :: hc3 p8.
Definition LZ18 (p8 sb p10 : word) : list (word * word) := (p10, Z_to_bv 64 N_PA) :: LZ17 p8 sb.
Definition SH12 (p12 : word) : Z := bv_unsigned p12 / 8 + 0x7fff8000.
Definition PLO12 (p12 : word) : Z := SH12 p12 / 4096 * 4096.
Definition PHI12 (p12 : word) : Z := (SH12 p12 + 8192 + 4095) / 4096 * 4096.
Definition H7 (p8 sb p10 p12 : word) : word -> bool := hcut (H6 p8 sb p10) (SH12 p12) 8192.
Definition A7 (sb p12 : word) : list (Z * Z) := (PLO12 p12, PHI12 p12) :: A5 sb.

Lemma rdown_facts : forall x, 0 <= x -> x - 4096 < x / 4096 * 4096 <= x /\ (x / 4096 * 4096) mod 4096 = 0.
Proof. intros x Hx. pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)). split; [lia|]. rewrite Z.mul_comm. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
Lemma rup_facts : forall x, 0 <= x -> x <= (x + 4095) / 4096 * 4096 < x + 4096 /\ ((x + 4095) / 4096 * 4096) mod 4096 = 0.
Proof. intros x Hx. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)). split; [lia|]. apply Z_mod_mult. Qed.
Lemma rdown_ge : forall x B, B mod 4096 = 0 -> B <= x -> B <= x / 4096 * 4096.
Proof. intros x B HB Hx. pose proof (Z.div_le_mono B x 4096 ltac:(lia) Hx). pose proof (Z.div_mod B 4096 ltac:(lia)). lia. Qed.
Lemma rup_le : forall x B, B mod 4096 = 0 -> x <= B -> (x + 4095) / 4096 * 4096 <= B.
Proof. intros x B HB Hx. pose proof (Z.div_mod B 4096 ltac:(lia)) as D.
  assert (E : (B + 4095) / 4096 = B / 4096).
  { replace (B + 4095) with (4095 + (B / 4096) * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  pose proof (Z.div_le_mono (x + 4095) (B + 4095) 4096 ltac:(lia) ltac:(lia)). rewrite E in H. lia.
Qed.
Lemma sh12_L : forall p12 : word, bv_unsigned p12 mod 4096 = 0 -> IMG_HI <= bv_unsigned p12 -> bv_unsigned p12 + 65536 <= SHB_LO ->
  SHB_LO + 512 <= PLO12 p12 /\ PLO12 p12 <= SH12 p12 /\ SH12 p12 + 8192 <= PHI12 p12 /\ PHI12 p12 <= SHB_LO + 2 ^ 28
  /\ SH12 p12 mod 512 = 0 /\ PLO12 p12 mod 4096 = 0 /\ PHI12 p12 mod 4096 = 0 /\ PHI12 p12 <= PLO12 p12 + 12288.
Proof.
  intros p12 Hal Hlo Hhi. unfold PLO12, PHI12, SH12, SHB_LO, IMG_HI in *.
  pose proof (Z.div_mod (bv_unsigned p12) 4096 ltac:(lia)) as D. set (k := bv_unsigned p12 / 4096) in *.
  replace (bv_unsigned p12 / 8) with (512 * k) by (replace (bv_unsigned p12) with (512 * k * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  pose proof (rdown_facts (512 * k + 2147450880) ltac:(lia)) as [R1 R2].
  pose proof (rup_facts (512 * k + 2147450880 + 8192) ltac:(lia)) as [R3 R4].
  pose proof (rdown_ge (512 * k + 2147450880) (2147446784 + 4096) eq_refl ltac:(lia)).
  pose proof (rup_le (512 * k + 2147450880 + 8192) (2147446784 + 2 ^ 28) eq_refl ltac:(lia)).
  repeat split; try lia. replace (512 * k + 2147450880) with ((k + 4194240) * 512) by lia. apply Z_mod_mult.
Qed.
Lemma sh12_H : forall p12 : word, bv_unsigned p12 mod 4096 = 0 -> SHB_HI <= bv_unsigned p12 -> bv_unsigned p12 + 65536 <= 2 ^ 47 - stack_max_size ->
  0x2008fff7000 <= PLO12 p12 /\ PLO12 p12 <= SH12 p12 /\ SH12 p12 + 8192 <= PHI12 p12 /\ PHI12 p12 <= SHB_HI - 2 ^ 20
  /\ SH12 p12 mod 512 = 0 /\ PLO12 p12 mod 4096 = 0 /\ PHI12 p12 mod 4096 = 0 /\ PHI12 p12 <= PLO12 p12 + 12288.
Proof.
  intros p12 Hal Hlo Hhi. unfold PLO12, PHI12, SH12, SHB_HI, stack_max_size in *.
  pose proof (Z.div_mod (bv_unsigned p12) 4096 ltac:(lia)) as D. set (k := bv_unsigned p12 / 4096) in *.
  replace (bv_unsigned p12 / 8) with (512 * k) by (replace (bv_unsigned p12) with (512 * k * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  pose proof (rdown_facts (512 * k + 2147450880) ltac:(lia)) as [R1 R2].
  pose proof (rup_facts (512 * k + 2147450880 + 8192) ltac:(lia)) as [R3 R4].
  pose proof (rdown_ge (512 * k + 2147450880) 0x2008fff7000 eq_refl ltac:(lia)).
  pose proof (rup_le (512 * k + 2147450880 + 8192) (17594333495296 - 2 ^ 20) eq_refl ltac:(lia)).
  repeat split; try lia. replace (512 * k + 2147450880) with ((k + 4194240) * 512) by lia. apply Z_mod_mult.
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
  #[local] Notation at_E10' := (at_E10 sp brk mbase draw lim inp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s6_e10 : forall a tid c pl p8 sb js R M mdl K, 2 ^ 25 <= lim -> length js = 20%nat ->
    at_E10' a tid c pl p8 sb js R M mdl ->
    (forall p10 R' M' mdl', bootS' (H6 p8 sb p10) (A5 sb) a tid c pl (js ++ [p10]) SR18 KN18 L18 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb js R M mdl K Hlim Hjs (HB & Hsb & E28 & E29) HK.
    assert (LEN : length (VB' a tid c pl js) = 36%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    eapply (bs_mmap_none_nr_spin sp brk mbase draw lim inp VI VE (H5 p8 sb) (A5 sb) a tid c pl js SR_E10 KN_E10 L17 (hc3 p8) (LZ17 p8 sb) N_PA A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - change (page_round_up_Z N_PA) with N_PA. unfold N_PA. lia.
    - change (page_round_up_Z N_PA) with N_PA. cbn [l_maps L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit gws]. unfold N_PA, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, IMG_HI, stack_max_size. lia.
    - (* [comment removed for export] *)
      change (page_round_up_Z N_PA) with N_PA.
      intros p R2 M2 mdl2 HB2. rewrite <- fetch_internal_mmap_ret_prev. apply (HK p). unfold SR18, L18, H6, hc6, LZ18.
      unfold kn_grant_none, KN_E10, SR_E10 in HB2. rewrite DS_E10_eq in HB2. unfold N_PA in HB2 |- *. rewrite KN18_eq in HB2. exact HB2.
  Qed.

  #[using="VI VE"] Theorem s6_b18a : forall a tid c pl js p8 sb p10 R M mdl K,
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR18 KN18 L18 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR18a KN18a L18 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 R M mdl K HB HK. rg_block VI VE HB HK run18a_eq car18a_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s6_e11 : forall a tid c pl js p8 sb p10 R M mdl K, 2 ^ 25 <= lim -> length js = 21%nat ->
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR18a KN18a L18 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall p11 R' M' mdl', bootS' (H6 p8 sb p10) (A5 sb) a tid c pl (js ++ [p11]) SR19 KN19 L19 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 R M mdl K Hlim Hjs HB HK.
    assert (LEN : length (VB' a tid c pl js) = 37%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H6 p8 sb p10) (A5 sb) a tid c pl js SR18a KN18a L18 (hc6 p8 p10) (LZ18 p8 sb p10) 4096 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - cbn [l_eager L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit A_bytes A5 fst snd]. change (page_round_up_Z 4096) with 4096. lia.
    - cbn [l_maps L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit gws]. change (page_round_up_Z 4096) with 4096. unfold N_PA, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, IMG_HI, stack_max_size. lia.
    - (* [comment removed for export] *)
      intros p R' M' mdl' HB'. rewrite <- fetch_internal_mmap_ret_prev. apply (HK p). unfold SR19, L19.
      unfold kn_grant in HB'. change (page_round_up_Z 4096) with 4096 in HB'. rewrite DS_E11_eq, KN19_eq in HB'. exact HB'.
  Qed.

  #[using="VI VE"] Theorem s6_b19a : forall a tid c pl js p8 sb p10 R M mdl K,
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR19 KN19 L19 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR19a KN19a L19 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 R M mdl K HB HK. rg_block VI VE HB HK run19a_eq car19a_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s6_e12 : forall a tid c pl js p8 sb p10 R M mdl K, 2 ^ 25 <= lim -> length js = 22%nat ->
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR19a KN19a L19 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall p12 R' M' mdl', bootS' (H6 p8 sb p10) (A5 sb) a tid c pl (js ++ [p12]) SR20 KN20 L20 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 R M mdl K Hlim Hjs HB HK.
    assert (LEN : length (VB' a tid c pl js) = 38%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    eapply (bs_mmap_rw_spin sp brk mbase draw lim inp VI VE (H6 p8 sb p10) (A5 sb) a tid c pl js SR19a KN19a L19 (hc6 p8 p10) (LZ18 p8 sb p10) 65536 A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - cbn [l_eager L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit A_bytes A5 fst snd]. change (page_round_up_Z 65536) with 65536. lia.
    - cbn [l_maps L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit gws]. change (page_round_up_Z 65536) with 65536. unfold N_PA, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, IMG_HI, stack_max_size. lia.
    - (* [comment removed for export] *)
      intros p R' M' mdl' HB'. rewrite <- fetch_internal_mmap_ret_prev. apply (HK p). unfold SR20, L20.
      unfold kn_grant in HB'. change (page_round_up_Z 65536) with 65536 in HB'. rewrite DS_E12_eq, KN20_eq in HB'. exact HB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="usp"] Lemma p12_facts : forall H A a tid c pl js sr kn hc lz R M mdl p8 p12,
    bootS' H A a tid c pl js sr kn L20 hc lz R M mdl ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 ->
    bv_unsigned p12 mod 4096 = 0 /\ IMG_HI <= bv_unsigned p12 /\ bv_unsigned p12 + 65536 <= bv_unsigned sp - stack_max_size
    /\ (bv_unsigned p12 + 65536 <= SHB_LO \/ SHB_HI <= bv_unsigned p12)
    /\ (bv_unsigned p12 + 65536 <= bv_unsigned p8 \/ bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE <= bv_unsigned p12).
  Proof.
    intros H A a tid c pl js sr kn hc lz R M mdl p8 p12 HB E28 E38.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (EV38 : edenot (EB' a tid c pl js) (EVar 38) = p12) by exact E38.
    assert (EV28 : edenot (EB' a tid c pl js) (EVar 28) = p8) by exact E28.
    pose proof HMO as MO. unfold maps_ok, L20, lgrant in MO. cbn [l_maps] in MO.
    apply Forall_cons_iff in MO as [M38 _]. unfold map_ok in M38. cbn [fst snd] in M38. rewrite EV38 in M38.
    destruct M38 as (Mal & M4k & Mn & Mtop & Mimg).
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. unfold L20, L19, L18, L17, L16, L15, L13, L_E6, lgrant, lgrant_nr, lcommit in AP.
    cbn [l_maps dl List.map fst snd ivs_apart] in AP. rewrite EV38, EV28 in AP. destruct AP as [AP _].
    repeat (apply Forall_cons_iff in AP as [?X AP]); cbn [fst snd edenot] in *.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_LO, SHB_HI, IMG_HI, A_img_lo, A_img_hi in *.
    rewrite !u_small in X1 by lia. rewrite !u_small in X4, X5, X6 by lia. unfold stack_max_size in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="usp"] Theorem s6_krL : forall a tid c pl js p8 sb p10 p12 R M mdl,
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> bv_unsigned p12 + 65536 <= SHB_LO ->
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR20 KN20 L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR20 KN20L L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl E28 E38 HL HB.
    pose proof (p12_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    eapply bootS_reknow; [exact HB | auto |]. intros HKN. constructor; [| exact HKN].
    unfold KR38L. cbn [kentry_ok]. change (edenot (EB sp draw inp a tid c pl js) (EVar 38)) with (ev (EB sp draw inp a tid c pl js) 38). rewrite E38.
    unfold SHB_LO, IMG_HI in *. lia.
  Qed.

  #[using="VI VE usp"] Theorem s6_krH : forall a tid c pl js p8 sb p10 p12 R M mdl,
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> SHB_HI <= bv_unsigned p12 ->
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR20 KN20 L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR20 KN20H L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl E28 E38 HL HB.
    pose proof (p12_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    eapply bootS_reknow; [exact HB | auto |]. intros HKN. constructor; [| exact HKN].
    unfold KR38H. cbn [kentry_ok]. change (edenot (EB sp draw inp a tid c pl js) (EVar 38)) with (ev (EB sp draw inp a tid c pl js) 38). rewrite E38.
    unfold SHB_HI, IMG_HI, stack_max_size in *. lia.
  Qed.

  #[using="VI VE"] Theorem s6_b20aL : forall a tid c pl js p8 sb p10 R M mdl K,
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR20 KN20L L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR20aL KN20aL L20 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_memset) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 R M mdl K HB HK. rg_block VI VE HB HK run20aL_eq car20aL_eq. Qed.

  #[using="VI VE"] Theorem s6_b20aH : forall a tid c pl js p8 sb p10 R M mdl K,
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR20 KN20H L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR20aH KN20aH L20 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_memset) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb p10 R M mdl K HB HK. rg_block VI VE HB HK run20aH_eq car20aH_eq. Qed.

  #[using="usp"] Lemma p8_facts6 : forall H A a tid c pl js sr kn hc lz R M mdl p8,
    bootS' H A a tid c pl js sr kn L20 hc lz R M mdl -> ev (EB' a tid c pl js) 28 = p8 ->
    bv_unsigned p8 mod 4096 = 0 /\ SHB_HI <= bv_unsigned p8 /\ bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE <= bv_unsigned sp - stack_max_size.
  Proof.
    intros H A a tid c pl js sr kn hc lz R M mdl p8 HB E28.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (EV28 : edenot (EB' a tid c pl js) (EVar 28) = p8) by exact E28.
    pose proof HMO as MO. unfold maps_ok, L20, L19, L18, L17, L16, lgrant, lgrant_nr, lcommit in MO. cbn [l_maps] in MO.
    do 3 (apply Forall_cons_iff in MO as [_ MO]). apply Forall_cons_iff in MO as [M28 _]. unfold map_ok in M28. cbn [fst snd] in M28. rewrite EV28 in M28.
    destruct M28 as (Mal & M4k & Mn & Mtop & Mimg).
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. unfold L20, L19, L18, L17, L16, L15, L13, L_E6, lgrant, lgrant_nr, lcommit in AP.
    cbn [l_maps dl List.map fst snd ivs_apart] in AP. rewrite EV28 in AP. destruct AP as (_ & _ & _ & AP & _).
    repeat (apply Forall_cons_iff in AP as [?X AP]); cbn [fst snd edenot] in *.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_HI in *. rewrite !u_small in X1, X2, X3 by lia. unfold stack_max_size in *. lia.
  Qed.

  #[using="VI VE usp"] Theorem s6_exposeL : forall a tid c pl js p8 sb p10 p12 R M mdl, 2 ^ 25 <= lim -> bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> bv_unsigned p12 + 65536 <= SHB_LO ->
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR20aL KN20aL L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR20aL KN20xL L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl Hlim Hsb E28 E38 HL HB.
    pose proof (p12_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (p8_facts6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB E28) as (P1 & P2 & P3).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (sh12_L p12 Q1 Q2 HL) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    unfold SBV in Hsb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_HI, stack_max_size in P2, P3.
    assert (SHv : bv_unsigned (edenot (EB sp draw inp a tid c pl js) EB12) + EO12 = SH12 p12).
    { unfold EB12, EO12, SH12. rewrite (shx_val0 _ 38). change (ev (EB sp draw inp a tid c pl js) 38) with (ev (EB' a tid c pl js) 38). rewrite E38. reflexivity. }
    unfold H7, A7. rewrite <- KN20xL_eq. unfold xpose12.
    pose proof (bs_expose2 sp brk mbase draw lim inp VI VE (H6 p8 sb p10) (A5 sb) a tid c pl js SR20aL KN20aL L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl
                  EB12 EO12 8192 (PLO12 p12) (PHI12 p12 - PLO12 p12) SHB_LO (SHB_LO + 2 ^ 28)) as X.
    cbv zeta in X. rewrite SHv in X. replace (PLO12 p12 + (PHI12 p12 - PLO12 p12)) with (PHI12 p12) in X by lia.
    apply X; clear X; try assumption; try reflexivity; try lia.
    - rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, Y6, Y7. reflexivity.
    - unfold SHB_LO in *. lia.
    - unfold SHB_LO, stack_max_size in *. lia.
    - intros x Hx. unfold H6, H5, H4, H3. apply hjoin_old.
      apply (proj2 (hcut_true _ _ _ _)). split; [| unfold SHRI, RI, SHB_LO in *; left; pose proof (Z.div_le_mono (2 ^ 37) (bv_unsigned sb + 2 ^ 37) 8 ltac:(lia) ltac:(lia)); change (2 ^ 37 / 8) with 17179869184 in *; lia].
      apply (proj2 (hcut_true _ _ _ _)). split; [| unfold RI, SHB_LO in *; lia].
      apply hjoin_old. apply H2_in. unfold SHB_LO, SHB_HI in *. lia.
    - cbn. do 2 right. right. left. reflexivity.
    - cbn [l_eager L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit A_bytes A5 fst snd]. lia.
  Qed.

  #[using="VI VE usp"] Theorem s6_exposeH : forall a tid c pl js p8 sb p10 p12 R M mdl, 2 ^ 25 <= lim -> bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> SHB_HI <= bv_unsigned p12 ->
    bootS' (H6 p8 sb p10) (A5 sb) a tid c pl js SR20aH KN20aH L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR20aH KN20xH L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl Hlim Hsb E28 E38 HL HB.
    pose proof (p12_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (p8_facts6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB E28) as (P1 & P2 & P3).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_HI, stack_max_size in P2, P3, Q3, Q5.
    pose proof (sh12_H p12 Q1 HL ltac:(unfold stack_max_size; lia)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    unfold SBV in Hsb.
    assert (SHv : bv_unsigned (edenot (EB sp draw inp a tid c pl js) EB12) + EO12 = SH12 p12).
    { unfold EB12, EO12, SH12. rewrite (shx_val0 _ 38). change (ev (EB sp draw inp a tid c pl js) 38) with (ev (EB' a tid c pl js) 38). rewrite E38. reflexivity. }
    (* [comment removed for export] *)
    assert (APART : SH12 p12 + 8192 <= SHRI sb \/ SHRI sb + 512 <= SH12 p12).
    { unfold SHRI, RI, SH12. pose proof (Z.div_mod (bv_unsigned p12) 4096 ltac:(lia)) as D12.
      pose proof (Z.div_mod (bv_unsigned p8) 65536 ltac:(lia)) as D8.
      set (k := bv_unsigned p12 / 4096) in *. set (q := bv_unsigned p8 / 65536) in *.
      replace (bv_unsigned p12 / 8) with (512 * k) by (replace (bv_unsigned p12) with (512 * k * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
      replace ((bv_unsigned sb + 2 ^ 37) / 8) with (8192 * (q + 1) + 2 ^ 34)
        by (replace (bv_unsigned sb + 2 ^ 37) with ((8192 * (q + 1) + 2 ^ 34) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
      destruct Q5; [left | right]; lia. }
    unfold H7, A7. rewrite <- KN20xH_eq. unfold xpose12.
    pose proof (bs_expose2 sp brk mbase draw lim inp VI VE (H6 p8 sb p10) (A5 sb) a tid c pl js SR20aH KN20aH L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl
                  EB12 EO12 8192 (PLO12 p12) (PHI12 p12 - PLO12 p12) 0x2008fff7000 SHB_HI) as X.
    cbv zeta in X. rewrite SHv in X. replace (PLO12 p12 + (PHI12 p12 - PLO12 p12)) with (PHI12 p12) in X by lia.
    apply X; clear X; try assumption; try reflexivity; try lia.
    - rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, Y6, Y7. reflexivity.
    - unfold SHB_HI, stack_max_size in *. lia.
    - intros x Hx. unfold H6, H5, H4, H3. apply hjoin_old.
      apply (proj2 (hcut_true _ _ _ _)). split; [| lia].
      apply (proj2 (hcut_true _ _ _ _)). split; [| unfold RI, SHB_HI in *; lia].
      apply hjoin_old. apply H2_in. unfold SHB_LO, SHB_HI in *. lia.
    - cbn. do 2 right. left. reflexivity.
    - cbn [l_eager L20 L19 L18 L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit A_bytes A5 fst snd]. lia.
  Qed.

  #[using="VI VE usp"] Theorem s6_memsetL : forall a tid c pl js p8 sb p10 p12 R M mdl K, length js = 23%nat -> bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> bv_unsigned p12 + 65536 <= SHB_LO ->
    bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR20aL KN20xL L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl (js ++ junk_c R' memset_clob7) SR20m KN20mL L20 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 RET20) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hjs Hsb E28 E38 HL HB HK.
    pose proof (p12_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (sh12_L p12 Q1 Q2 HL) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
    assert (LEN : length (VB' a tid c pl js) = 39%nat) by (rewrite length_VB, Hjs; reflexivity).
    assert (SHv : bv_unsigned (edenot (EB sp draw inp a tid c pl js) EB12) + EO12 = SH12 p12).
    { unfold EB12, EO12, SH12. rewrite (shx_val0 _ 38). change (ev (EB sp draw inp a tid c pl js) 38) with (ev (EB' a tid c pl js) 38). rewrite E38. reflexivity. }
    pose proof (cross_musl_memset_c sp brk mbase draw lim inp VI VE memset_clob7 (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR20aL KN20xL L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl
                  EB12 EO12 1%nat EO12 8192 254 8192 RET20 K HB) as X.
    cbv zeta in X. rewrite LEN, SHv in X. apply X; clear X.
    - unfold memset_clob, memset_clob7. intros r Hr. cbn in Hr |- *. clear - Hr. tauto. (* [comment removed for export] *)
    - cbn. intros Hx. repeat (destruct Hx as [Hx|Hx]; [discriminate|]). exact Hx.
    - unfold memset_clob7. repeat (constructor; [cbn; intros Hx; repeat (destruct Hx as [Hx|Hx]; [discriminate|]); exact Hx|]). constructor.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - reflexivity.
    - vmeq_refl.
    - vmeq_refl.
    - lia.
    - replace (sr_get SR20aL 12%bv) with
        (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EVar 38) (ELit 3)))
                                (EAlu ALU_SRL (EAlu ALU_ADD (EVar 38) (ELit 65528)) (ELit 3))) (ELit 1))
        by (vmeq_refl).
      apply bv_eq. replace 65528 with (65536 - 8) by reflexivity.
      rewrite (shdiff_val0 _ 38 65536); change (ev (EB sp draw inp a tid c pl js) 38) with (ev (EB' a tid c pl js) 38); rewrite ?E38; try lia.
      + reflexivity.
      + pose proof (Z.div_mod (bv_unsigned p12) 4096 ltac:(lia)). replace (bv_unsigned p12) with (512 * (bv_unsigned p12 / 4096) * 8) by lia. apply Z_mod_mult.
      + reflexivity.
      + unfold SHB_LO in *. lia.
    - lia.
    - vmeq_refl.
    - apply bv_eq. vmeq_refl.
    - vmeq_refl.
    - lia.
    - lia.
    - lia.
    - unfold SHB_LO in *. lia.
    - unfold SHB_LO, stack_max_size in *. lia.
    - intros R' M' mdl' HB'. apply HK. rewrite <- (proj1 SR20a_join), <- KN20mL_eq. exact HB'.
  Qed.

  #[using="VI VE usp"] Theorem s6_memsetH : forall a tid c pl js p8 sb p10 p12 R M mdl K, length js = 23%nat -> bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 38 = p12 -> SHB_HI <= bv_unsigned p12 ->
    bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR20aH KN20xH L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl (js ++ junk_c R' memset_clob7) SR20m KN20mH L20 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 RET20) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hjs Hsb E28 E38 HL HB HK.
    pose proof (p12_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB E28 E38) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    pose proof (sh12_H p12 Q1 HL ltac:(unfold stack_max_size in *; lia)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
    assert (LEN : length (VB' a tid c pl js) = 39%nat) by (rewrite length_VB, Hjs; reflexivity).
    assert (SHv : bv_unsigned (edenot (EB sp draw inp a tid c pl js) EB12) + EO12 = SH12 p12).
    { unfold EB12, EO12, SH12. rewrite (shx_val0 _ 38). change (ev (EB sp draw inp a tid c pl js) 38) with (ev (EB' a tid c pl js) 38). rewrite E38. reflexivity. }
    pose proof (cross_musl_memset_c sp brk mbase draw lim inp VI VE memset_clob7 (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR20aH KN20xH L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl
                  EB12 EO12 1%nat EO12 8192 254 8192 RET20 K HB) as X.
    cbv zeta in X. rewrite LEN, SHv in X. apply X; clear X.
    - unfold memset_clob, memset_clob7. intros r Hr. cbn in Hr |- *. clear - Hr. tauto. (* [comment removed for export] *)
    - cbn. intros Hx. repeat (destruct Hx as [Hx|Hx]; [discriminate|]). exact Hx.
    - unfold memset_clob7. repeat (constructor; [cbn; intros Hx; repeat (destruct Hx as [Hx|Hx]; [discriminate|]); exact Hx|]). constructor.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - reflexivity.
    - vmeq_refl.
    - vmeq_refl.
    - lia.
    - replace (sr_get SR20aH 12%bv) with
        (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EVar 38) (ELit 3)))
                                (EAlu ALU_SRL (EAlu ALU_ADD (EVar 38) (ELit 65528)) (ELit 3))) (ELit 1))
        by (vmeq_refl).
      apply bv_eq. replace 65528 with (65536 - 8) by reflexivity.
      rewrite (shdiff_val0 _ 38 65536); change (ev (EB sp draw inp a tid c pl js) 38) with (ev (EB' a tid c pl js) 38); rewrite ?E38; try lia.
      + reflexivity.
      + pose proof (Z.div_mod (bv_unsigned p12) 4096 ltac:(lia)). replace (bv_unsigned p12) with (512 * (bv_unsigned p12 / 4096) * 8) by lia. apply Z_mod_mult.
      + reflexivity.
      + unfold SHB_HI, stack_max_size in *. lia.
    - lia.
    - vmeq_refl.
    - apply bv_eq. vmeq_refl.
    - vmeq_refl.
    - lia.
    - lia.
    - lia.
    - unfold SHB_HI, stack_max_size in *. lia.
    - unfold SHB_HI, stack_max_size in *. lia.
    - intros R' M' mdl' HB'. apply HK. rewrite <- (proj1 (proj2 SR20a_join)), <- KN20mH_eq. exact HB'.
  Qed.

  #[using="Type"] Lemma ev_EB_app : forall a tid c pl js ks k, (k < 16 + length js)%nat ->
    ev (EB' a tid c pl (js ++ ks)) k = ev (EB' a tid c pl js) k.
  Proof.
    intros a tid c pl js ks k Hk. rewrite EB_app. cbn [ev]. unfold EB. cbn [ev]. apply vals_ev_app_l. rewrite length_VB. exact Hk.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition at_E13 (a tid c : word) (pl : placements) (p8 sb p10 p12 : word) (js : list word) R M mdl : Prop :=
    bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR_E13 KN_E13 L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb /\ ev (EB' a tid c pl js) 36 = p10 /\ ev (EB' a tid c pl js) 38 = p12.

  #[using="VI VE usp"] Theorem s6_b20bL : forall a tid c pl js p8 sb p10 p12 R M mdl K, bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 29 = sb -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR20m KN20mL L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', at_E13 a tid c pl p8 sb p10 p12 js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 RET20) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hsb E28 E29 E36 E38 HB HK.
    assert (HK' : forall R' M' mdl', bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR20bL KN20bL L20 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K).
    { intros R' M' mdl' HB'. apply HK. split; [| repeat split; assumption].
      pose proof (p12_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB' E28 E38) as (_ & Q2 & Q3 & _).
      rewrite <- (proj1 (proj2 (proj2 E13_join))). eapply bootS_reknow; [exact HB' | auto |]. intros HKN'. unfold KN_E13. constructor.
      - unfold KR38W. cbn [kentry_ok]. change (edenot (EB sp draw inp a tid c pl js) (EVar 38)) with (ev (EB sp draw inp a tid c pl js) 38). rewrite E38.
        pose proof (SH sp brk mbase draw inp VI VE). unfold IMG_HI, stack_max_size in *. lia.
      - apply (know_ok_sub_b _ _ _ _ _ (proj1 E13_join)). exact HKN'. }
    clear HK. rg_block VI VE HB HK' run20bL_eq car20bL_eq.
  Qed.

  #[using="VI VE usp"] Theorem s6_b20bH : forall a tid c pl js p8 sb p10 p12 R M mdl K, bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 29 = sb -> ev (EB' a tid c pl js) 36 = p10 -> ev (EB' a tid c pl js) 38 = p12 ->
    bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR20m KN20mH L20 (hc6 p8 p10) (LZ18 p8 sb p10) R M mdl ->
    (forall R' M' mdl', at_E13 a tid c pl p8 sb p10 p12 js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 RET20) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb p10 p12 R M mdl K Hsb E28 E29 E36 E38 HB HK.
    assert (HK' : forall R' M' mdl', bootS' (H7 p8 sb p10 p12) (A7 sb p12) a tid c pl js SR20bH KN20bH L20 (hc6 p8 p10) (LZ18 p8 sb p10) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K).
    { intros R' M' mdl' HB'. apply HK. split; [| repeat split; assumption].
      pose proof (p12_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB' E28 E38) as (_ & Q2 & Q3 & _).
      unfold SR_E13. eapply bootS_reknow; [exact HB' | auto |]. intros HKN'. unfold KN_E13. constructor.
      - unfold KR38W. cbn [kentry_ok]. change (edenot (EB sp draw inp a tid c pl js) (EVar 38)) with (ev (EB sp draw inp a tid c pl js) 38). rewrite E38.
        pose proof (SH sp brk mbase draw inp VI VE). unfold IMG_HI, stack_max_size in *. lia.
      - apply (know_ok_sub_b _ _ _ _ _ (proj1 (proj2 E13_join))). exact HKN'. }
    clear HK. pose proof (proj2 (proj2 (proj2 E13_join))) as PCe. rg_block VI VE HB HK' run20bH_eq car20bH_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem boot_s6 : forall a tid c pl p8 sb js R M mdl K, 2 ^ 25 <= lim -> length js = 20%nat ->
    at_E10' a tid c pl p8 sb js R M mdl ->
    (forall p10 p11 p12 ks R' M' mdl', length ks = 7%nat ->
       at_E13 a tid c pl p8 sb p10 p12 ((((js ++ [p10]) ++ [p11]) ++ [p12]) ++ ks) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl p8 sb js R M mdl K Hlim Hjs HE HK. pose proof HE as (_ & Hsb & E28 & E29).
    apply (s6_e10 a tid c pl p8 sb js R M mdl K Hlim Hjs HE). intros p10 R0 M0 m0 H0.
    apply (s6_b18a _ _ _ _ _ _ _ _ _ _ _ K H0). intros R1 M1 m1 H1.
    assert (L1 : length (js ++ [p10]) = 21%nat) by (rewrite length_app, Hjs; reflexivity).
    apply (s6_e11 a tid c pl _ p8 sb p10 R1 M1 m1 K Hlim L1 H1). intros p11 R2 M2 m2 H2'.
    apply (s6_b19a _ _ _ _ _ _ _ _ _ _ _ K H2'). intros R3 M3 m3 H3'.
    assert (L2 : length ((js ++ [p10]) ++ [p11]) = 22%nat) by (rewrite length_app, L1; reflexivity).
    apply (s6_e12 a tid c pl _ p8 sb p10 R3 M3 m3 K Hlim L2 H3'). intros p12 R4 M4 m4 H4'.
    set (js3 := ((js ++ [p10]) ++ [p11]) ++ [p12]) in *.
    assert (L3 : length js3 = 23%nat) by (unfold js3; rewrite length_app, L2; reflexivity).
    assert (F28 : ev (EB' a tid c pl js3) 28 = p8) by (unfold js3; rewrite !ev_EB_app by (rewrite ?length_app, ?Hjs; cbn; lia); exact E28).
    assert (F29 : ev (EB' a tid c pl js3) 29 = sb) by (unfold js3; rewrite !ev_EB_app by (rewrite ?length_app, ?Hjs; cbn; lia); exact E29).
    assert (F36 : ev (EB' a tid c pl js3) 36 = p10).
    { unfold js3. rewrite 2!ev_EB_app by (rewrite ?length_app, ?Hjs; cbn; lia).
      replace 36%nat with (16 + 20)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 20), app_nth2, Hjs by lia. reflexivity. }
    assert (F38 : ev (EB' a tid c pl js3) 38 = p12).
    { unfold js3. replace 38%nat with (16 + 22)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 22), app_nth2, L2 by lia. reflexivity. }
    assert (FX : forall ks, ev (EB' a tid c pl (js3 ++ ks)) 28 = p8 /\ ev (EB' a tid c pl (js3 ++ ks)) 29 = sb
                            /\ ev (EB' a tid c pl (js3 ++ ks)) 36 = p10 /\ ev (EB' a tid c pl (js3 ++ ks)) 38 = p12).
    { intros ks. rewrite !ev_EB_app by (rewrite L3; lia). repeat split; assumption. }
    destruct (p12_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4' F28 F38) as (_ & _ & _ & [HL | HH] & _).
    - (* [comment removed for export] *)
      pose proof (s6_krL a tid c pl js3 p8 sb p10 p12 R4 M4 m4 F28 F38 HL H4') as H5'.
      apply (s6_b20aL _ _ _ _ _ _ _ _ _ _ _ K H5'). intros R6 M6 m6 H6'.
      pose proof (s6_exposeL a tid c pl js3 p8 sb p10 p12 R6 M6 m6 Hlim Hsb F28 F38 HL H6') as H7'.
      apply (s6_memsetL a tid c pl js3 p8 sb p10 p12 R6 M6 m6 K L3 Hsb F28 F38 HL H7'). intros R8 M8 m8 H8.
      destruct (FX (junk_c R8 memset_clob7)) as (G28 & G29 & G36 & G38).
      apply (s6_b20bL _ _ _ _ _ _ _ _ _ _ _ _ K Hsb G28 G29 G36 G38 H8). intros R9 M9 m9 H9.
      exact (HK p10 p11 p12 (junk_c R8 memset_clob7) R9 M9 m9 eq_refl H9).
    - (* [comment removed for export] *)
      pose proof (s6_krH a tid c pl js3 p8 sb p10 p12 R4 M4 m4 F28 F38 HH H4') as H5'.
      apply (s6_b20aH _ _ _ _ _ _ _ _ _ _ _ K H5'). intros R6 M6 m6 H6'.
      pose proof (s6_exposeH a tid c pl js3 p8 sb p10 p12 R6 M6 m6 Hlim Hsb F28 F38 HH H6') as H7'.
      apply (s6_memsetH a tid c pl js3 p8 sb p10 p12 R6 M6 m6 K L3 Hsb F28 F38 HH H7'). intros R8 M8 m8 H8.
      destruct (FX (junk_c R8 memset_clob7)) as (G28 & G29 & G36 & G38).
      apply (s6_b20bH _ _ _ _ _ _ _ _ _ _ _ _ K Hsb G28 G29 G36 G38 H8). intros R9 M9 m9 H9.
      exact (HK p10 p11 p12 (junk_c R8 memset_clob7) R9 M9 m9 eq_refl H9).
  Qed.
End Theorems.
