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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require Import BootS2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootState BootH2 BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootH2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn3a.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootKn3c__B3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn3c OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootKn3c__B3.BootKn4a. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn4f__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS3 BootS4. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn4f.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS4.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots5_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition L16 : ledger := lgrant_nr L15 28 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE.
Definition L17 : ledger := lcommit L16 4096.
Lemma DS_E8_eq : DS_std L15 = DS_E8. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition RI (sb : word) : Z := bv_unsigned sb + 2 ^ 37.
Definition SHRI (sb : word) : Z := RI sb / 8 + 0x7fff8000.
Definition H3 (p8 : word) : word -> bool := hjoin H2 p8 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE.
Definition hc3 (p8 : word) : hfacts := (bv_unsigned p8, bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, None) :: HC5.
Definition H4 (p8 sb : word) : word -> bool := hcut (H3 p8) (RI sb) 4096.
Definition H5 (p8 sb : word) : word -> bool := hcut (H4 p8 sb) (SHRI sb) 512.   (* [comment removed for export] *)
Definition A5 (sb : word) : list (Z * Z) := [(SHRI sb, SHRI sb + 4096)].
(* [comment removed for export] *)
Definition LZ16 (p8 : word) : list (word * word) := (p8, Z_to_bv 64 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE) :: LZ5.
Definition LZ17 (p8 sb : word) : list (word * word) := maps_subtract (LZ16 p8) (RI sb) (RI sb + 4096).

(* [comment removed for export] *)
Definition SBV (p8 : word) : Z := bv_unsigned p8 + 65536 - bv_unsigned p8 mod 65536.

(* [comment removed for export] *)
Ltac in_lit := first [left; reflexivity | right; in_lit].
Ltac lia3 := split; [lia | split; [lia | reflexivity]].

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let usp := bv_unsigned sp.

  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="usp"] Lemma p8_facts : forall H A a tid c pl js p8 ks sr kn L hc lz R M mdl,
    bootS' H A a tid c pl (js ++ p8 :: ks) sr kn L hc lz R M mdl -> length js = 12%nat -> l_maps L = l_maps L16 ->
    bv_unsigned p8 mod 4096 = 0 /\ SHB_HI <= bv_unsigned p8 /\ bv_unsigned p8 + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE <= bv_unsigned sp - stack_max_size.
  Proof.
    intros H A a tid c pl js p8 ks sr kn L hc lz R M mdl HB Hjs HL.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (EV : edenot (EB sp draw inp a tid c pl (js ++ p8 :: ks)) (EVar 28) = p8).
    { cbn [edenot]. replace 28%nat with (16 + 12)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl (js ++ p8 :: ks) 12).
      rewrite app_nth2 by lia. rewrite Hjs. reflexivity. }
    pose proof HMO as MO. unfold maps_ok in MO. rewrite HL in MO. unfold L16, lgrant_nr in MO. cbn [l_maps] in MO.
    apply Forall_cons_iff in MO as [M28 MO]. unfold map_ok in M28. cbn [fst snd] in M28. rewrite EV in M28.
    destruct M28 as (Mal & M4k & Mn & Mtop & Mimg).
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as AP. rewrite HL in AP. unfold L16, lgrant_nr, L15, lgrant, L13, L_E6 in AP.
    cbn [l_maps dl List.map fst snd ivs_apart] in AP. rewrite EV in AP. destruct AP as [AP _].
    repeat (apply Forall_cons_iff in AP as [?X AP]); cbn [fst snd edenot] in *.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_HI in *. rewrite !u_small in X1, X2, X3 by lia. unfold stack_max_size in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s5_e8 : forall a tid c pl js R M mdl K, 2 ^ 25 <= lim -> length js = 12%nat ->
    at_E8 sp brk mbase draw lim inp a tid c pl js R M mdl ->
    (forall p8 R' M' mdl', bootS' (H3 p8) A2 a tid c pl (js ++ [p8]) SR16 KN16 L16 (hc3 p8) (LZ16 p8) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K Hlim Hjs HB HK. unfold at_E8 in HB.
    assert (LEN : length (VB' a tid c pl js) = 28%nat) by (rewrite length_VB, Hjs; reflexivity).
    rewrite fetch_internal_mmap_ret_prev in HK.
    eapply (bs_mmap_none_nr_spin sp brk mbase draw lim inp VI VE H2 A2 a tid c pl js SR_E8 KN_E8 L15 HC5 LZ5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE A_internal_mmap_ecall ECALLW
              R M mdl K HB fetch_internal_mmap_ecall is_ecall_ECALLW);
      rewrite ?LEN; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - change (page_round_up_Z OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE) with OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE. lia.
    - change (page_round_up_Z OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE) with OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE. cbn [l_maps L15 L13 L_E6 lgrant gws]. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, IMG_HI, stack_max_size. lia.
    - (* [comment removed for export] *)
      change (page_round_up_Z OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE) with OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE.
      intros p R2 M2 mdl2 HB2. rewrite <- fetch_internal_mmap_ret_prev. apply (HK p). unfold SR16, L16, H3, hc3.
      unfold kn_grant_none in HB2. rewrite DS_E8_eq, KN16_eq in HB2. exact HB2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s5_b16a : forall a tid c pl js p8 R M mdl K,
    bootS' (H3 p8) A2 a tid c pl js SR16 KN16 L16 (hc3 p8) (LZ16 p8) R M mdl ->
    (forall R' M' mdl', bootS' (H3 p8) A2 a tid c pl js SR16a KN16a L16 (hc3 p8) (LZ16 p8) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 PC16a) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 R M mdl K HB HK. rg_block VI VE HB HK run16a_eq car16a_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s5_fresh : forall a tid c pl js p8 R M mdl,
    length js = 12%nat ->
    bootS' (H3 p8) A2 a tid c pl (js ++ [p8]) SR16a KN16a L16 (hc3 p8) (LZ16 p8) R M mdl ->
    exists sb : word, bv_unsigned sb = SBV p8 /\
      bootS' (H3 p8) A2 a tid c pl ((js ++ [p8]) ++ [sb]) SR16f KN16f L16 (hc3 p8) (LZ16 p8) R M mdl.
  Proof.
    intros a tid c pl js p8 R M mdl Hjs HB.
    pose proof (p8_facts _ _ _ _ _ _ js p8 [] _ _ _ _ _ _ _ _ HB Hjs eq_refl) as (P1 & P2 & P3).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (LEN : length (VB' a tid c pl (js ++ [p8])) = 29%nat) by (rewrite length_VB, length_app, Hjs; reflexivity).
    assert (EV : ev (EB sp draw inp a tid c pl (js ++ [p8])) 28 = p8).
    { replace 28%nat with (16 + 12)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl (js ++ [p8]) 12), app_nth2 by lia. rewrite Hjs. reflexivity. }
    pose proof HB as HB0. destruct HB0 as [HR HKN _ _ _ _ _ _ _ _ _ _].
    set (sb := getr R 10%bv).
    assert (Usb : bv_unsigned sb = SBV p8).
    { unfold sb. rewrite (HR 10%bv), SBX_eq. change SBX with (sbx 28 (2 ^ 16)).
      rewrite (sbx_val _ 28 16) by (rewrite ?EV; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, stack_max_size in *; lia).
      rewrite EV. unfold SBV. reflexivity. }
    exists sb. split; [exact Usb|].
    unfold SR16f. rewrite <- KN16f_eq. change 10%nat with (ridx 10%bv).
    pose proof (bs_fresh sp brk mbase draw lim inp (H3 p8) A2 a tid c pl (js ++ [p8]) SR16a KN16a L16 (hc3 p8) (LZ16 p8) R M mdl 10%bv sb KF29 HB eq_refl) as BF.
    rewrite LEN in BF. apply BF; [vmeq_refl | vmeq_refl | reflexivity |]. clear BF.
    unfold KF29. unfold SBV, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_HI, stack_max_size in Usb, P1, P2, P3, SLo, SHi.
    assert (EV' : edenot (EB sp draw inp a tid c pl ((js ++ [p8]) ++ [sb])) (EVar 29) = sb).
    { cbn [edenot]. rewrite EB_app. cbn [ev]. rewrite <- LEN, <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MB.
    assert (EV28' : edenot (EB sp draw inp a tid c pl ((js ++ [p8]) ++ [sb])) (EVar 28) = p8).
    { cbn [edenot]. replace 28%nat with (16 + 12)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 12), <- app_assoc, app_nth2, Hjs by lia. reflexivity. }
    apply (proj2 (know_ok_app SEGS _ _ _ _)). split; [constructor; [| constructor; [| constructor; [| constructor]]]|].
    - cbn [kentry_ok]. rewrite EV', Usb. split; [lia|]. pose proof (Z.div_mod (bv_unsigned p8) 65536 ltac:(lia)).
      replace (bv_unsigned p8 + 65536 - bv_unsigned p8 mod 65536) with (65536 * (bv_unsigned p8 / 65536) + 1 * 65536) by lia.
      rewrite Z_mod_plus_full, Z.mul_comm. apply Z_mod_mult.
    - cbn [kentry_ok]. rewrite EV', Usb. unfold N_RI, stack_max_size. lia.
    - (* [comment removed for export] *)
      cbn [kentry_ok]. change (edenot ?E (EAlu ALU_SUB (EVar 29) (EVar 28))) with ((edenot E (EVar 29) - edenot E (EVar 28))%bv).
      rewrite EV', EV28', bv_sub_unsigned, Usb. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
      rewrite Z.mod_small by lia. lia.
    - pose proof (dsj_entries_sub sp draw inp a tid c pl (js ++ [p8]) 28 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE N_RI DS_E8 sb (mrestrict (H3 p8) M)) as DS.
      cbv zeta in DS. rewrite EV, LEN in DS. apply DS; try (unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, N_RI; lia).
      + rewrite <- KN16a_dsj28. apply know_ok_filter. exact HKN.
      + unfold DS_E8. repeat apply Forall_cons; try apply Forall_nil; split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s5_b16b : forall a tid c pl js p8 R M mdl K,
    bootS' (H3 p8) A2 a tid c pl js SR16f KN16f L16 (hc3 p8) (LZ16 p8) R M mdl ->
    (forall R' M' mdl', bootS' (H3 p8) A2 a tid c pl js SR16b KN16b L16 (hc3 p8) (LZ16 p8) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_init_aligned_sb) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 R M mdl K HB HK. rg_block VI VE HB HK run16b_eq car16b_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s5_e9 : forall a tid c pl js p8 sb R M mdl K, 2 ^ 25 <= lim -> length js = 12%nat -> bv_unsigned sb = SBV p8 ->
    bootS' (H3 p8) A2 a tid c pl ((js ++ [p8]) ++ [sb]) SR16b KN16b L16 (hc3 p8) (LZ16 p8) R M mdl ->
    (forall R' mdl', bootS' (H4 p8 sb) A2 a tid c pl ((js ++ [p8]) ++ [sb]) SR16b KN17 L17 (hc3 p8) (LZ17 p8 sb) R'
                        (zfill (Z_to_bv 64 (RI sb)) (Z_to_bv 64 4096) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ret) (zfill (Z_to_bv 64 (RI sb)) (Z_to_bv 64 4096) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb R M mdl K Hlim Hjs Hsb HB HK.
    pose proof (p8_facts _ _ _ _ _ _ js p8 [sb] _ _ _ _ _ _ _ _ ltac:(rewrite <- app_assoc in HB; exact HB) Hjs eq_refl) as (P1 & P2 & P3).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (LEN : length (VB' a tid c pl ((js ++ [p8]) ++ [sb])) = 30%nat) by (rewrite length_VB, !length_app, Hjs; reflexivity).
    assert (EV28 : ev (EB sp draw inp a tid c pl ((js ++ [p8]) ++ [sb])) 28 = p8).
    { replace 28%nat with (16 + 12)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 12), <- app_assoc, app_nth2, Hjs by lia. reflexivity. }
    assert (EV29 : ev (EB sp draw inp a tid c pl ((js ++ [p8]) ++ [sb])) 29 = sb).
    { replace 29%nat with (16 + 13)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 13), app_nth2 by (rewrite length_app, Hjs; cbn; lia).
      rewrite length_app, Hjs. reflexivity. }
    pose proof (mod_pos:=Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)).
    unfold SBV, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_HI, stack_max_size in Hsb, P1, P2, P3.
    rewrite fetch_internal_mmap_ret_prev in HK.
    pose proof (bs_mmap_fixedin_rw sp brk mbase draw lim inp VI VE (H3 p8) A2 a tid c pl ((js ++ [p8]) ++ [sb]) SR16b KN16b L16 (hc3 p8) (LZ16 p8) R M mdl
                  EB9 EO9 4096 A_internal_mmap_ecall (EVar 28) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE ECALLW K HB fetch_internal_mmap_ecall is_ecall_ECALLW) as NODE.
    cbv zeta in NODE. unfold EB9, EO9 in NODE. cbn [edenot] in NODE. rewrite EV28, EV29 in NODE.
    change (page_round_up_Z 4096) with 4096 in NODE.
    apply NODE; clear NODE; try reflexivity; try (unfold A_internal_mmap_ecall; lia).
    - unfold L16, lgrant_nr. cbn [l_maps]. left. reflexivity.
    - unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE. lia.
    - pose proof (Z.div_mod (bv_unsigned p8) 65536 ltac:(lia)). rewrite Hsb.
      replace (bv_unsigned p8 + 65536 - bv_unsigned p8 mod 65536 + 137438953472) with (4096 * (16 * (bv_unsigned p8 / 65536) + 16 + 33554432)) by lia.
      rewrite Z.mul_comm. apply Z_mod_mult.
    - intros x Hx. unfold H3. apply hjoin_new. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE. lia.
    - constructor.
    - cbn [l_eager L16 L15 L13 L_E6 lgrant lgrant_nr A_bytes A2]. lia.
    - intros R' mdl' HB'. rewrite <- fetch_internal_mmap_ret_prev. apply HK. unfold H4, RI, L17. rewrite <- KN17_eq.
      (* [comment removed for export] *)
      eapply bootS_reknow; [exact HB' | auto |]. intros HKN'.
      apply (proj1 (know_ok_app SEGS _ _ [_; _] _)) in HKN' as [HK2 HKr]. apply (proj2 (know_ok_app SEGS _ _ [_; _] _)). split; [| exact HKr].
      assert (EQB : edenot (EB sp draw inp a tid c pl ((js ++ [p8]) ++ [sb])) RIB = edenot (EB sp draw inp a tid c pl ((js ++ [p8]) ++ [sb])) EB9).
      { unfold RIB, EB9. cbn [edenot]. rewrite EV28. change (alu64 ALU_ADD ?x (alu64 ALU_SUB ?y ?x)) with (x + (y - x))%bv.
        apply bv_eq. rewrite bv_add_unsigned, bv_sub_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r.
        replace (bv_unsigned p8 + (bv_unsigned (ev (EB sp draw inp a tid c pl ((js ++ [p8]) ++ [sb])) 29) - bv_unsigned p8)) with (bv_unsigned (ev (EB sp draw inp a tid c pl ((js ++ [p8]) ++ [sb])) 29)) by lia.
        apply Z.mod_small. apply u64_range. }
      inversion HK2 as [|k1 l1 K1 HK3]; subst. inversion HK3 as [|k2 l2 K2 _]; subst.
      constructor; [| constructor; [| constructor]].
      + unfold kentry_ok, flat, estart, adenot in K1 |- *. cbn [a_base a_off] in K1 |- *. rewrite EQB. exact K1.
      + unfold kentry_ok, flat, estart, adenot in K2 |- *. cbn [a_base a_off] in K2 |- *. rewrite EQB. exact K2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE"] Theorem s5_b17a : forall a tid c pl js p8 sb R M mdl K,
    bootS' (H4 p8 sb) A2 a tid c pl js SR16b KN17 L17 (hc3 p8) (LZ17 p8 sb) R M mdl ->
    (forall R' M' mdl', bootS' (H4 p8 sb) A2 a tid c pl js SR17a KN17a L17 (hc3 p8) (LZ17 p8 sb) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_musl_memset) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ret) M ROM) mdl) K.
  Proof. intros a tid c pl js p8 sb R M mdl K HB HK. rg_block VI VE HB HK run17a_eq car17a_eq. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s5_expose : forall a tid c pl js p8 sb R M mdl, 2 ^ 25 <= lim -> length js = 12%nat -> bv_unsigned sb = SBV p8 ->
    bootS' (H4 p8 sb) A2 a tid c pl ((js ++ [p8]) ++ [sb]) SR17a KN17a L17 (hc3 p8) (LZ17 p8 sb) R M mdl ->
    bootS' (H5 p8 sb) (A5 sb) a tid c pl ((js ++ [p8]) ++ [sb]) SR17a KN17x L17 (hc3 p8) (LZ17 p8 sb) R M mdl.
  Proof.
    intros a tid c pl js p8 sb R M mdl Hlim Hjs Hsb HB.
    pose proof (p8_facts _ _ _ _ _ _ js p8 [sb] _ _ _ _ _ _ _ _ ltac:(rewrite <- app_assoc in HB; exact HB) Hjs eq_refl) as (P1 & P2 & P3).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (EV29 : ev (EB sp draw inp a tid c pl ((js ++ [p8]) ++ [sb])) 29 = sb).
    { replace 29%nat with (16 + 13)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 13), app_nth2 by (rewrite length_app, Hjs; cbn; lia).
      rewrite length_app, Hjs. reflexivity. }
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    unfold SBV, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_HI, stack_max_size in Hsb, P1, P2, P3.
    assert (SHv : bv_unsigned (edenot (EB sp draw inp a tid c pl ((js ++ [p8]) ++ [sb])) EBS) + EOS = SHRI sb).
    { unfold EBS, EOS, SHRI, RI. rewrite (shx_val _ 29 (2 ^ 37)) by (rewrite ?EV29; lia). rewrite EV29. reflexivity. }
    assert (SHlo : 0x2008fff7000 + 2 ^ 34 <= SHRI sb /\ SHRI sb + 4096 + 2 ^ 20 <= SHB_HI /\ SHRI sb mod 4096 = 0).
    { unfold SHRI, RI, SHB_HI. pose proof (Z.div_mod (bv_unsigned p8) 65536 ltac:(lia)).
      set (q := bv_unsigned p8 / 65536) in *.
      replace (bv_unsigned sb + 2 ^ 37) with (8 * (8192 * (q + 1 + 2097152))) by lia.
      rewrite (Z.mul_comm 8), Z.div_mul by lia. split; [lia|]. split; [lia|].
      replace (8192 * (q + 1 + 2097152) + 2147450880) with (4096 * (2 * (q + 1 + 2097152) + 524280)) by lia.
      rewrite Z.mul_comm. apply Z_mod_mult. }
    destruct SHlo as (S1 & S2 & S3). unfold SHB_HI in S2.
    unfold H5, A5. rewrite <- KN17x_eq.
    pose proof (bs_expose2 sp brk mbase draw lim inp VI VE (H4 p8 sb) A2 a tid c pl ((js ++ [p8]) ++ [sb]) SR17a KN17a L17 (hc3 p8) (LZ17 p8 sb) R M mdl
                  EBS EOS 512 (SHRI sb) 4096 0x2008fff7000 SHB_HI) as X.
    cbv zeta in X. rewrite SHv in X. apply X; clear X; try assumption; try reflexivity; try lia.
    - unfold stack_max_size. lia.
    - intros x Hx. unfold H4, H3. apply (proj2 (hcut_true _ _ _ _)). split; [| unfold RI; lia].
      apply hjoin_old. apply H2_in. unfold SHB_LO, SHB_HI. lia.
    - cbn. right. left. reflexivity.
    - unfold SHB_HI. lia.
    - cbn [l_eager L17 L16 L15 L13 L_E6 lgrant lgrant_nr lcommit A_bytes A2]. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem s5_memset : forall a tid c pl js p8 sb R M mdl K, length js = 12%nat -> bv_unsigned sb = SBV p8 ->
    bootS' (H5 p8 sb) (A5 sb) a tid c pl ((js ++ [p8]) ++ [sb]) SR17a KN17x L17 (hc3 p8) (LZ17 p8 sb) R M mdl ->
    (forall R' M' mdl', bootS' (H5 p8 sb) (A5 sb) a tid c pl (((js ++ [p8]) ++ [sb]) ++ junk_c R' memset_clob) SR17m KN17m L17 (hc3 p8) (LZ17 p8 sb) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 RET17) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_musl_memset) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb R M mdl K Hjs Hsb HB HK.
    pose proof (p8_facts _ _ _ _ _ _ js p8 [sb] _ _ _ _ _ _ _ _ ltac:(rewrite <- app_assoc in HB; exact HB) Hjs eq_refl) as (P1 & P2 & P3).
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (LEN : length (VB' a tid c pl ((js ++ [p8]) ++ [sb])) = 30%nat) by (rewrite length_VB, !length_app, Hjs; reflexivity).
    assert (EV29 : ev (EB sp draw inp a tid c pl ((js ++ [p8]) ++ [sb])) 29 = sb).
    { replace 29%nat with (16 + 13)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 13), app_nth2 by (rewrite length_app, Hjs; cbn; lia).
      rewrite length_app, Hjs. reflexivity. }
    pose proof (Z.mod_pos_bound (bv_unsigned p8) 65536 ltac:(lia)) as MP.
    unfold SBV, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn4f__A3.BootKn5a.TwB.N_SPACE, SHB_HI, stack_max_size in Hsb, P1, P2, P3.
    pose proof (Z.div_mod (bv_unsigned p8) 65536 ltac:(lia)) as DM. set (q := bv_unsigned p8 / 65536) in *.
    pose proof (cross_musl_memset sp brk mbase draw lim inp VI VE (H5 p8 sb) (A5 sb) a tid c pl ((js ++ [p8]) ++ [sb]) SR17a KN17x L17 (hc3 p8) (LZ17 p8 sb) R M mdl
                  EBS EOS 1%nat 512 MSV MSN RET17 K HB) as X.
    cbv zeta in X. rewrite LEN in X. apply X; clear X.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - vmeq_refl.
    - exact ES_split.
    - vmeq_refl.
    - unfold MSV. lia.
    - replace (sr_get SR17a 12%bv) with
        (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 29) (ELit (2 ^ 37))) (ELit 3)))
                                (EAlu ALU_SRL (EAlu ALU_ADD (EVar 29) (ELit (2 ^ 37 + 4096 - 8))) (ELit 3))) (ELit 1))
        by (vmeq_refl).
      apply bv_eq. rewrite (shdiff_val _ 29 (2 ^ 37) 4096); rewrite ?EV29; try lia.
      + unfold MSN. reflexivity.
      + replace (bv_unsigned sb + 2 ^ 37) with (8 * (8192 * (q + 1 + 2097152))) by lia. rewrite Z.mul_comm. apply Z_mod_mult.
      + reflexivity.
    - unfold MSN. lia.
    - vmeq_refl.
    - apply bv_eq. vmeq_refl.
    - vmeq_refl.
    - unfold MSN. lia.
    - lia.
    - unfold EBS, EOS. rewrite (shx_val _ 29 (2 ^ 37)) by (rewrite ?EV29; lia). rewrite EV29. pose proof (Z.div_pos (bv_unsigned sb + 2 ^ 37) 8). lia.
    - unfold EBS, EOS, MSN. rewrite (shx_val _ 29 (2 ^ 37)) by (rewrite ?EV29; lia). rewrite EV29.
      replace (bv_unsigned sb + 2 ^ 37) with (8 * (8192 * (q + 1 + 2097152))) by lia. rewrite (Z.mul_comm 8), Z.div_mul by lia. unfold stack_max_size. lia.
    - rewrite ?KN17m_eq, ?SR17m_eq. exact HK.   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SR_E10 : list expr := SR17b.
  Definition KN_E10 : list kentry := KN17b.
  (* [comment removed for export] *)
  Definition at_E10 (a tid c : word) (pl : placements) (p8 sb : word) (js : list word) R M mdl : Prop :=
    bootS' (H5 p8 sb) (A5 sb) a tid c pl js SR_E10 KN_E10 L17 (hc3 p8) (LZ17 p8 sb) R M mdl /\ bv_unsigned sb = SBV p8
    /\ ev (EB' a tid c pl js) 28 = p8 /\ ev (EB' a tid c pl js) 29 = sb.

  #[using="VI VE"] Theorem s5_b17b : forall a tid c pl js p8 sb R M mdl K, bv_unsigned sb = SBV p8 ->
    ev (EB' a tid c pl js) 28 = p8 -> ev (EB' a tid c pl js) 29 = sb ->
    bootS' (H5 p8 sb) (A5 sb) a tid c pl js SR17m KN17m L17 (hc3 p8) (LZ17 p8 sb) R M mdl ->
    (forall R' M' mdl', at_E10 a tid c pl p8 sb js R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 RET17) M ROM) mdl) K.
  Proof.
    intros a tid c pl js p8 sb R M mdl K Hsb E28 E29 HB HK.
    assert (HK' : forall R' M' mdl', bootS' (H5 p8 sb) (A5 sb) a tid c pl js SR17b KN17b L17 (hc3 p8) (LZ17 p8 sb) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K).
    { intros R' M' mdl' HB'. apply HK. split; [exact HB' | split; [exact Hsb | split; [exact E28 | exact E29]]]. }
    clear HK. rg_block VI VE HB HK' run17b_eq car17b_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem boot_s5 : forall a tid c pl js R M mdl K, 2 ^ 25 <= lim -> length js = 12%nat ->
    at_E8 sp brk mbase draw lim inp a tid c pl js R M mdl ->
    (forall p8 sb ks R' M' mdl', length ks = 6%nat -> at_E10 a tid c pl p8 sb (((js ++ [p8]) ++ [sb]) ++ ks) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) mdl) K.
  Proof.
    intros a tid c pl js R M mdl K Hlim Hjs HE HK.
    apply (s5_e8 a tid c pl js R M mdl K Hlim Hjs HE). intros p8 R0 M0 m0 H0.
    apply (s5_b16a _ _ _ _ _ _ _ _ _ K H0). intros R1 M1 m1 H1.
    destruct (s5_fresh a tid c pl js p8 R1 M1 m1 Hjs H1) as (sb & Hsb & H2).
    apply (s5_b16b _ _ _ _ _ _ _ _ _ K H2). intros R3 M3 m3 H3'.
    apply (s5_e9 a tid c pl js p8 sb R3 M3 m3 K Hlim Hjs Hsb H3'). intros R4 m4 H4'.
    apply (s5_b17a _ _ _ _ _ _ _ _ _ _ K H4'). intros R5 M5 m5 H5'.
    pose proof (s5_expose a tid c pl js p8 sb R5 M5 m5 Hlim Hjs Hsb H5') as H6.
    apply (s5_memset a tid c pl js p8 sb R5 M5 m5 K Hjs Hsb H6). intros R7 M7 m7 H7.
    assert (E28 : ev (EB' a tid c pl (((js ++ [p8]) ++ [sb]) ++ junk_c R7 memset_clob)) 28 = p8).
    { replace 28%nat with (16 + 12)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 12), <- !app_assoc, app_nth2, Hjs by lia. reflexivity. }
    assert (E29 : ev (EB' a tid c pl (((js ++ [p8]) ++ [sb]) ++ junk_c R7 memset_clob)) 29 = sb).
    { replace 29%nat with (16 + 13)%nat by reflexivity. rewrite (ev_EB_js sp draw inp a tid c pl _ 13), <- !app_assoc, app_nth2 by (rewrite Hjs; lia).
      rewrite Hjs. reflexivity. }
    apply (s5_b17b _ _ _ _ _ _ _ _ _ _ K Hsb E28 E29 H7). intros R8 M8 m8 H8.
    exact (HK p8 sb (junk_c R7 memset_clob) R8 M8 m8 eq_refl H8).
  Qed.
End Theorems.
