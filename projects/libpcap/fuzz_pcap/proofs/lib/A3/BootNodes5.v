(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesLibE AsanNodesMmB BackingAlgebra. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore AsanPlan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanKnow. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodesDrive AsanHeapKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesMmDrive__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBootMm3__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanNodesBrk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3 BootS1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootS2 BootState BootNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootNodes2__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes5_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KB_brk (v : nat) (off : Z) : list kentry :=
  [KAlign (EVar v) 4096; KRange (EVar v) (IMG_HI + off) (IMG_HI + brk_aslr_max + off)].

(* [comment removed for export] *)
Definition lbrk (L : ledger) (v : nat) (d : Z) : ledger :=
  Ledger ((EVar v, d) :: l_maps L) (l_brk L + d) (l_eager L + d).

(* [comment removed for export] *)
Definition kn_brk_grant (L : ledger) (v : nat) (gl d : Z) (kn : list kentry) : list kentry :=
  [KZero (SA (EVar v) 0) (ELit gl); KWr (SA (EVar v) 0) (ELit gl);
   KZero (SA (EVar v) gl) (ELit (d - gl)); KWr (SA (EVar v) gl) (ELit (d - gl))]
  ++ dsj_entries v d (DS_std L)
  ++ kn_keep MGrow (dsj_entries v d (DS_std L) ++ kn) kn (EVar v) 0 (ELit d).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_mprotect (eb : expr) (eo n : Z) (kn : list kentry) : list kentry :=
  [KZero (SA eb eo) (ELit n); KWr (SA eb eo) (ELit n)] ++ kn_keep MGrow kn kn eb eo (ELit n).

Section Theorems10.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let usp := bv_unsigned sp.

  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="sp usp"] Lemma dsj_entries_ok_var : forall E M P nZ ds (v : nat) (a : word),
    0 <= nZ -> bv_unsigned a + nZ < 2 ^ 64 -> ev E v = a ->
    dsj_claims E P nZ ds -> P a ->
    know_ok SEGS E M (dsj_entries v nZ ds).
  Proof.
    intros E M P nZ ds v a HnZ Hnw Hev Hds Ha.
    unfold dsj_entries. unfold dsj_claims in Hds.
    induction ds as [|[r l] ds IH]; [constructor|].
    apply Forall_cons_iff in Hds as [Hd Hds].
    cbn [map fst snd] in *. constructor; [|apply IH; assumption].
    specialize (Hd a Ha).
    cbn [kentry_ok]. unfold estart, elenZ in *. cbn [a_base a_off edenot] in *. rewrite Hev.
    rewrite u_small by (pose proof (u64_range a); lia). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_brk_query : forall H A a tid c pl js sr kn L hc lz (pc : Z) w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let b := Z_to_bv 64 (bv_unsigned brk + l_brk L) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true ->
    sr_get sr 17%bv = ELit 214 -> sr_get sr 10%bv = ELit 0 ->
    0 <= l_brk L < 2 ^ 32 -> l_brk L mod 4096 = 0 ->
    (forall R',
       bootS' H A a tid c pl (js ++ [b]) (sr_upd sr (ridx 10%bv) (EVar v)) (KB_brk v (l_brk L) ++ kn) L hc lz R' M mdl ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) M ROM) mdl) K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz pc w R M mdl K E v b HB HF HE Hpc0 Hpc4 Hsr Hkn HL S17 S10 Hb0 Hbal HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    destruct (VE48 sp brk mbase draw inp VI VE) as (_ & VB48 & _ & _). destruct VB48 as (Vb1 & Vb2 & Vb3).
    rewrite reserved_top_val in Vb1, Vb2. unfold page_size in Vb3.
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    eapply (srz_brk_query_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17) (G _ _ S10)).
    rewrite pc_lit_add4 by lia. rewrite (mf_brk _ _ _ _ _ _ _ _ _ F). fold b.
    assert (Hub : bv_unsigned b = bv_unsigned brk + l_brk L).
    { unfold b. apply u_small. unfold brk_aslr_max, IMG_HI in *. pose proof (u64_range brk). lia. }
    assert (Hev : edenot (EB sp draw inp a tid c pl (js ++ [b])) (EVar v) = b).
    { rewrite EB_app. cbn [edenot ev]. unfold v. rewrite <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
    apply HK. constructor.
    - apply regs_ok_set; [| intros X; apply (f_equal bv_unsigned) in X; discriminate X | exact Hev].
      rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
    - apply (proj2 (know_ok_app SEGS _ _ _ _)). split.
      + unfold KB_brk. constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; rewrite Hev.
        * split; [lia|]. rewrite Hub, Z.add_mod, Vb3, Hbal by lia. reflexivity.
        * rewrite Hub. unfold brk_aslr_max, IMG_HI in *. lia.
      + rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN].
    - exact HA.
    - exact HZ.
    - exact HLZ.
    - exact HM.
    - apply mfacts_env; [exact HL | exact F].
    - apply maps_ok_env; [exact HL | exact HMO].
    - apply regime_ok_env; [exact HL | exact RG].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_brk_grow : forall H A a tid c pl js sr kn L hc lz (v : nat) (gl d pc : Z) w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let b := Z_to_bv 64 (bv_unsigned brk + l_brk L) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 214 -> ev E v = b -> (v < length (VB' a tid c pl js))%nat ->
    edenot E (sr_get sr 10%bv) = Z_to_bv 64 (bv_unsigned b + d) ->
    0 <= l_brk L < 2 ^ 32 -> l_brk L mod 4096 = 0 -> d mod 4096 = 0 -> gl mod 4096 = 0 -> 0 < gl < d -> d <= 2 ^ 32 ->
    sivs_sizes_ok (l_maps L) = true ->
    l_eager L + d + A_bytes A <= lim ->
    (* [comment removed for export] *)
    (forall R' mdl', brk_grow_adm d mdl = false ->
       bootS' H A a tid c pl js (sr_upd sr (ridx 10%bv) (EVar v)) kn L hc lz R' M mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) M ROM) mdl') K) ->
    (* [comment removed for export] *)
    (forall R' mdl', brk_grow_adm d mdl = true ->
       bootS' H A a tid c pl js (sr_upd sr (ridx 10%bv) (EAlu ALU_ADD (EVar v) (ELit d))) (kn_brk_grant L v gl d kn) (lbrk L v d) hc lz
              R' (zfill b (Z_to_bv 64 d) M) mdl' ->
       (forall x : word, bv_unsigned b <= bv_unsigned x < bv_unsigned b + d -> H x = false) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (zfill b (Z_to_bv 64 d) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz v gl d pc w R M mdl K E b HB HF HE Hpc0 Hpc4 S17 Hev Hvlt H10 Hb0 Hbal Hdal Hgal Hgl Hd32 Hs Hbud HKA HKB.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    destruct (VE48 sp brk mbase draw inp VI VE) as (_ & VB48 & _ & _). destruct VB48 as (Vb1 & Vb2 & Vb3).
    rewrite reserved_top_val in Vb1, Vb2. unfold page_size in Vb3.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    pose proof (u64_range brk) as Ubrk.
    assert (Hub : bv_unsigned b = bv_unsigned brk + l_brk L).
    { unfold b. apply u_small. unfold brk_aslr_max, IMG_HI in *. lia. }
    assert (Hb : vm_brk (m_vmmaps mdl) = b) by exact (mf_brk _ _ _ _ _ _ _ _ _ F).
    assert (Hsb : vm_start_brk (m_vmmaps mdl) = brk) by exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
    assert (G17 : getr R 17 = Z_to_bv 64 214) by (rewrite (HR 17%bv), S17; reflexivity).
    assert (G10 : getr R 10 = Z_to_bv 64 (bv_unsigned b + d)) by (rewrite (HR 10%bv); exact H10).
    assert (Hbal' : bv_unsigned b mod page_size = 0).
    { unfold page_size. rewrite Hub, Z.add_mod, Vb3, Hbal by lia. reflexivity. }
    assert (Htop : alloc_top (m_vmmaps mdl) = bv_unsigned sp - stack_max_size) by exact (mfacts_alloc_top _ _ _ _ _ _ _ _ _ F).
    destruct (brk_grow_adm d mdl) eqn:Hadm.
    - (* [comment removed for export] *)
      eapply (srz_brk_grow_grant_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w d K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F) G17);
        rewrite ?Hb, ?Hsb; try assumption.
      1-4: rewrite ?Hub; unfold brk_aslr_max, IMG_HI in *; lia.
      rewrite pc_lit_add4 by lia.
      pose proof (brk_grow_adm_unpack d mdl) as U. cbv zeta in U. rewrite Hb in U.
      specialize (U Hbal' Hdal ltac:(lia) ltac:(unfold IMG_HI in *; lia) ltac:(unfold brk_aslr_max, IMG_HI in *; lia) Hadm).
      destruct U as (Htop' & Hrf & Hlive). rewrite Htop in Htop'.
      assert (Hpin : grant_ok_na_pin mdl b d = true).
      { unfold grant_ok_na_pin. rewrite Htop.
        rewrite (proj2 (Z.eqb_eq _ _) Hbal'), (proj2 (Z.leb_le _ _) Htop').
        rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned b))) by (unfold IMG_HI in *; lia). cbn [andb].
        apply (region_free_shrink _ b (d + page_size) d); [unfold page_size; lia | unfold page_size, brk_aslr_max, IMG_HI, stack_max_size in *; lia | exact Hrf]. }
      assert (Hvis : range_visible H b d) by (apply (grant_visible_L sp brk mbase lim inp H E tid L mdl b d F HIN Hs ltac:(lia) Hpin)).
      set (n := Z_to_bv 64 d). assert (Hun : bv_unsigned n = d) by (unfold n; apply u_small; lia).
      destruct (grant_ok_na_pin_unpack _ _ _ Hpin) as (_ & _ & _ & Hrf'). fold n in Hrf'.
      apply HKB; [reflexivity | | exact Hvis].
      constructor.
      + (* [comment removed for export] *)
        apply regs_ok_set; [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate X |].
        cbn [edenot]. fold E. rewrite Hev. fold b. apply bv_eq. rewrite u_add64, !u_small by (unfold brk_aslr_max, IMG_HI, stack_max_size in *; lia).
        apply Z.mod_small. unfold brk_aslr_max, IMG_HI, stack_max_size in *; lia.
      + (* [comment removed for export] *)
        fold n. fold E. rewrite (mrestrict_zfill H b n M) by (rewrite Hun; exact Hvis).
        assert (KD : forall V, know_ok SEGS E V (dsj_entries v d (DS_std L))).
        { intros V. apply (dsj_entries_ok_var E V _ d (DS_std L) v b ltac:(lia) ltac:(unfold brk_aslr_max, IMG_HI, stack_max_size in *; lia) Hev
                           (DS_std_claims sp brk mbase draw lim inp VI VE E tid L mdl d F Hshd (ev_EB_sp sp draw inp a tid c pl js) Hs ltac:(lia)) Hpin). }
        assert (KZ : kentry_ok SEGS E (zfill b n (mrestrict H M)) (KZero (SA (EVar v) 0) (ELit d))).
        { unfold n. apply EntryGlue.kzero_zfill; [cbn [edenot]; exact Hev | lia | unfold brk_aslr_max, IMG_HI, stack_max_size in *; lia]. }
        assert (KW : kentry_ok SEGS E (zfill b n (mrestrict H M)) (KWr (SA (EVar v) 0) (ELit d))).
        { unfold n. apply EntryGlue.kwr_zfill; [cbn [edenot]; exact Hev | lia | unfold brk_aslr_max, IMG_HI, stack_max_size in *; lia]. }
        unfold kn_brk_grant. apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [|apply (proj2 (know_ok_app SEGS _ _ _ _)); split].
        * constructor; [apply (kzero_sub SEGS E _ (EVar v) 0 d 0 gl KZ); lia|].
          constructor; [apply (kwr_sub SEGS E _ (EVar v) 0 d 0 gl KW); lia|].
          constructor; [apply (kzero_sub SEGS E _ (EVar v) 0 d gl (d - gl) KZ); lia|].
          constructor; [apply (kwr_sub SEGS E _ (EVar v) 0 d gl (d - gl) KW); lia|].
          constructor.
        * apply KD.
        * apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill b n (mrestrict H M)) MGrow).
          -- apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KD | exact HKN].
          -- exact HKN.
          -- unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hev. fold n. rewrite Hun, Z.add_0_r, <- Hun. apply mem_change_zfill.
      + (* [comment removed for export] *)
        intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. fold n. rewrite Hun. unfold stack_max_size, usp in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *.
        apply Forall_forall. intros r Hr x Hx Hhx. rewrite zfill_out; [exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|].
        fold n. rewrite Hun.
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned b)); [left; assumption|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned b + d)); [|right; assumption].
        exfalso. rewrite (Hvis x ltac:(lia)) in Hhx. discriminate.
      + (* [comment removed for export] *) rewrite brk_grown_model_lazy. exact HLZ.
      + (* [comment removed for export] *)
        pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as (W1 & W2 & W3 & W4).
        eapply MInv_transport; [exact HM | reflexivity | reflexivity |].
        pose proof (AsanNodesMmB.eager_used_cons_le mdl (vm_brk (m_vmmaps mdl)) n (m_vmmaps (brk_grown_model d mdl)) W1
                      ltac:(apply iv_wf_intro; rewrite Hb, Hun; unfold stack_max_size in *; lia) eq_refl eq_refl) as Hle.
        change (with_vmmaps (m_vmmaps (brk_grown_model d mdl)) mdl) with (brk_grown_model d mdl) in Hle.
        change (vm_limit (m_vmmaps (brk_grown_model d mdl))) with (vm_limit (m_vmmaps mdl)).
        rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). rewrite Hun in Hle. pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
      + (* [comment removed for export] *)
        pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as (W1 & W2 & W3 & W4).
        constructor; rewrite ?brk_grown_model_vm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
        * rewrite brk_grown_model_halted. exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * exact Hsb.
        * rewrite Hb, Hub. cbn [lbrk l_brk]. f_equal. lia.
        * exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * cbn [lbrk l_maps dl List.map fst snd]. cbn [edenot]. fold E. rewrite Hb, Hev, (mf_maps _ _ _ _ _ _ _ _ _ F). reflexivity.
        * cbn [lbrk l_maps ivs_apart dl List.map fst snd]. cbn [edenot]. fold E. rewrite Hev. fold n. unfold E. fold (dl (EB' a tid c pl js) (l_maps L)).
          rewrite <- (mf_maps _ _ _ _ _ _ _ _ _ F).
          rewrite region_free_app in Hrf'. apply andb_prop in Hrf' as [_ Hrf2].
          split; [| rewrite (mf_maps _ _ _ _ _ _ _ _ _ F); exact (mf_apart _ _ _ _ _ _ _ _ _ F)].
          apply Forall_forall. intros [qb qn] Hq. cbn [fst snd].
          pose proof (region_free_In _ b n qb qn Hrf2 Hq) as Hov. rewrite Hun in Hov. rewrite Hun. lia.
        * cbn [lbrk l_eager].
          pose proof (AsanNodesMmB.eager_used_cons_le mdl (vm_brk (m_vmmaps mdl)) n (m_vmmaps (brk_grown_model d mdl)) W1
                        ltac:(apply iv_wf_intro; rewrite Hb, Hun; unfold stack_max_size in *; lia) eq_refl eq_refl) as Hle.
          change (with_vmmaps (m_vmmaps (brk_grown_model d mdl)) mdl) with (brk_grown_model d mdl) in Hle.
          rewrite Hun in Hle. pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
        * rewrite brk_grown_model_fs. exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite brk_grown_model_fds. exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite brk_grown_model_tid. exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * unfold model_ivs_wf. rewrite brk_grown_model_vm, brk_grown_model_lazy. cbn [vm_maps vm_noaccess vm_init_sp].
          fold n. split; [apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hb, Hun; unfold stack_max_size in *; lia | exact W1]|].
          split; [exact W2|]. split; [exact W3|]. exact W4.
        * (* [comment removed for export] *) unfold na_clear. rewrite brk_grown_model_vm. cbn [vm_noaccess]. exact (mf_na _ _ _ _ _ _ _ _ _ F).
      + (* [comment removed for export] *)
        unfold maps_ok, lbrk. cbn [l_maps]. constructor.
        * unfold map_ok. cbn [fst snd edenot]. fold E. rewrite Hev. unfold page_size in Hbal'. unfold stack_max_size, A_img_hi, IMG_HI in *.
          split; [exact Hbal'|]. split; [lia|]. split; [lia|]. split; [unfold usp in *; lia | right; lia].
        * exact HMO.
      + (* [comment removed for export] *)
        constructor; try assumption; try (rewrite brk_grown_model_lazy; assumption).
        -- intros x Hx. destruct (HIN x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lbrk. cbn [l_maps]. right. exact Hq.
        -- unfold hf_inmaps in *. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) Hhin r Hr0) as (q & Hq & Hr).
           exists q. split; [| exact Hr]. unfold lbrk. cbn [l_maps]. right. exact Hq.
        -- intros x Hx. destruct (Hshd x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lbrk. cbn [l_maps]. right. exact Hq.
      + exact HT.
      + exact Hcl.
      + exact Ht.
    - (* [comment removed for export] *)
      eapply (srz_brk_grow_blocked_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w (Z_to_bv 64 (bv_unsigned b + d)) K HF HE
                (mf_halted _ _ _ _ _ _ _ _ _ F) G17 G10).
      + rewrite u_small; unfold brk_aslr_max, IMG_HI in *; lia.
      + rewrite Hsb, u_small; unfold brk_aslr_max, IMG_HI in *; lia.
      + rewrite Hb, u_small; unfold brk_aslr_max, IMG_HI in *; lia.
      + unfold brk_grow_adm in Hadm. rewrite Hb in Hadm. exact Hadm.
      + rewrite pc_lit_add4 by lia. rewrite Hb. apply HKA; [reflexivity|].
        constructor; try assumption.
        apply regs_ok_set; [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate X | cbn [edenot]; exact Hev].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_mmap_fixed_none_guard : forall H A a tid c pl js sr kn L hc lz (v : nat) (gl d pc : Z) rest w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let b := ev E v in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 222 -> edenot E (sr_get sr 10%bv) = b -> sr_get sr 11%bv = ELit gl -> sr_get sr 12%bv = ELit 0 ->
    sr_get sr 13%bv = ELit 50 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    l_maps L = (EVar v, d) :: rest -> gl mod 4096 = 0 -> 0 < gl <= d ->
    (forall x : word, bv_unsigned b <= bv_unsigned x < bv_unsigned b + d -> H x = false) ->
    (bv_unsigned b + gl <= SHB_LO \/ SHB_HI <= bv_unsigned b) ->   (* [comment removed for export] *)
    (forall R' mdl',
       bootS' H A a tid c pl js sr (kn_keep MUnmap kn kn (EVar v) 0 (ELit gl)) L hc
              (maps_subtract lz (bv_unsigned b) (bv_unsigned b + gl)) R' (unfill b (Z_to_bv 64 gl) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (unfill b (Z_to_bv 64 gl) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz v gl d pc rest w R M mdl K E b HB HF HE Hpc0 Hpc4 S17 S10 S11 S12 S13 S14 S15 HL Hgal Hgl Hvis Hshb HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (Eb : edenot (EB sp draw inp a tid c pl js) (EVar v) = b) by reflexivity.
    (* [comment removed for export] *)
    pose proof HMO as MO. unfold maps_ok in MO. rewrite HL in MO. apply Forall_cons_iff in MO as [MOK MOR].
    unfold map_ok in MOK. cbn [fst snd] in MOK. rewrite Eb in MOK. destruct MOK as (Mal & M4k & Md & Mtop & Mimg).
    set (n := Z_to_bv 64 gl).
    assert (Hun : bv_unsigned n = gl) by (unfold n; apply u_small; unfold stack_max_size in *; lia).
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    assert (Hpr : page_round_up_Z gl = gl).
    { unfold page_round_up_Z, page_size. pose proof (Z.div_mod gl 4096 ltac:(lia)). rewrite Z.mul_comm.
      replace ((gl + 4096 - 1) / 4096) with (gl / 4096); [lia|].
      replace (gl + 4096 - 1) with (4095 + (gl / 4096) * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
    assert (HMAPS : vm_maps (m_vmmaps mdl) = (b, Z_to_bv 64 d) :: dl (EB sp draw inp a tid c pl js) rest).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F), HL. reflexivity. }
    eapply (srz_mmap_fixed_noaccess_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w b gl K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17)).
    - rewrite (HR 10%bv). exact S10.
    - unfold page_size. exact Mal.
    - lia.
    - exact (G _ _ S11).
    - lia.
    - rewrite Hpr, (mfacts_alloc_top sp brk mbase lim inp _ _ _ _ F). unfold stack_max_size in *. lia.
    - exact (G _ _ S12).
    - exact (G _ _ S13).
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - rewrite Hpr, (mf_res _ _ _ _ _ _ _ _ _ F). fold n. apply reserved_free_of_apart. rewrite Hun. lia.
    - rewrite Hpr, HMAPS. fold n. unfold map_contains. cbn [existsb fst snd]. rewrite Hun, (u_small d) by (unfold stack_max_size in *; lia).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le (bv_unsigned b + gl) _)) by lia. reflexivity.
    - rewrite Hpr, pc_lit_add4 by lia. fold n.
      set (mdl' := fixed_noaccess_model b n mdl).
      assert (Hend : bv_unsigned b + bv_unsigned n <= 2 ^ 64) by (rewrite Hun; unfold stack_max_size in *; lia).
      assert (Hnl : bv_unsigned n mod page_size = 0) by (rewrite Hun; unfold page_size; exact Hgal).
      assert (Hpos : 0 < bv_unsigned n) by (rewrite Hun; lia).
      apply (HK (regupd R 10%bv b) mdl'). constructor.
      + intros r. destruct (bv_eqb r 10%bv) eqn:Er.
        * apply bv_eqb_eq in Er. subst r. rewrite getr_same by (intros X; apply (f_equal bv_unsigned) in X; discriminate X). symmetry. exact S10.
        * assert (Hne : r <> 10%bv) by (intros X; rewrite X, bv_eqb_refl in Er; discriminate Er).
          rewrite getr_other by exact Hne. apply HR.
      + (* [comment removed for export] *)
        rewrite mrestrict_unfill.
        apply (kn_keep_sound SEGS _ (mrestrict H M) (unfill b n (mrestrict H M)) MUnmap); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). fold b. fold n. rewrite Z.add_0_r.
        apply mem_change_unfill.
      + intros x Hx. rewrite unfill_out; [apply HA; exact Hx|]. fold n. rewrite Hun. unfold stack_max_size in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        rewrite unfill_out; [exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|]. fold n. rewrite Hun.
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned b)); [left; assumption|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned b + gl)); [|right; assumption].
        exfalso. rewrite (Hvis x ltac:(lia)) in Hhx. discriminate.
      + unfold mdl'. rewrite (fxn_lazy b n mdl), HLZ, Hun. reflexivity.
      + unfold mdl'. exact (MInv_fxn A b n mdl WF ltac:(unfold page_size; exact Mal) Hnl Hpos Hend HM).
      + (* [comment removed for export] *)
        pose proof (model_ivs_wf_fxn b n mdl WF Hpos Hend) as WF'.
        pose proof (eager_used_fxn_le b n mdl WF Hpos Hend) as EGL.
        unfold mdl'. constructor.
        * rewrite (fxn_halted b n mdl). exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_reserved b n mdl). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_init_sp b n mdl). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_limit b n mdl). exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_start_brk b n mdl). exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_brk b n mdl). exact (mf_brk _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_mmap_base b n mdl). exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_maps b n mdl). exact (mf_maps _ _ _ _ _ _ _ _ _ F).
        * exact (mf_apart _ _ _ _ _ _ _ _ _ F).
        * pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
        * rewrite (fxn_fs b n mdl). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_fds b n mdl). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_tid b n mdl). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (fxn_noaccess b n mdl).
          apply na_clear_l_cons; [rewrite Hun; exact Hshb | apply na_clear_l_sub; [exact W2 | exact (mf_na _ _ _ _ _ _ _ _ _ F)]].
      + exact HMO.
      + (* [comment removed for export] *)
        constructor.
        * exact HH.
        * exact HAW.
        * unfold mdl'. apply (lazy_cover_fxn A b n mdl WF Hpos). exact HCOV.
        * exact HIN.
        * exact Hhin.
        * exact Habv.
        * intros x Hx. unfold mdl'. rewrite (fxn_lazy b n mdl), Hun.
          assert (Hout : ~ (bv_unsigned b <= bv_unsigned x < bv_unsigned b + d)) by (intros X; rewrite (Hvis x X) in Hx; discriminate).
          rewrite page_in_ranges_subtract_out; [exact (Hhl x Hx) | exact W3 | lia |].
          pose proof (u64_range x) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod (bv_unsigned b) 4096 ltac:(lia)). pose proof (Z.div_mod gl 4096 ltac:(lia)). nia.
        * exact Hshd.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_mmap_none_anon : forall H A a tid c pl js sr kn L hc lz (len pc : Z) w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let nZ := page_round_up_Z len in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> sivs_sizes_ok (l_maps L) = true ->
    sr_get sr 17%bv = ELit 222 -> sr_get sr 10%bv = ELit 0 -> sr_get sr 11%bv = ELit len -> sr_get sr 12%bv = ELit 0 ->
    sr_get sr 13%bv = ELit 34 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len ->
    IMG_HI + nZ + gws nZ (l_maps L) <= 0x7fff80000000 - stack_max_size ->
    (forall p R' mdl',
       bootS' H A a tid c pl (js ++ [p]) (sr_upd sr (ridx 10%bv) (EVar v)) (kn_grant_none L v nZ kn) (lgrant_nr L v nZ) hc lz
              R' (unfill p (Z_to_bv 64 nZ) M) mdl' ->
       In (p, Z_to_bv 64 nZ) (vm_noaccess (m_vmmaps mdl')) ->
       (forall x : word, bv_unsigned p <= bv_unsigned x < bv_unsigned p + nZ -> H x = false) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (unfill p (Z_to_bv 64 nZ) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz len pc w R M mdl K E v nZ HB HF HE Hpc0 Hpc4
           Hsr Hkn HL Hs S17 S10 S11 S12 S13 S14 S15 Hlen Hroom HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
    assert (Hlen64 : len < 2 ^ 64).
    { unfold stack_max_size, IMG_HI in Hroom. pose proof (gap_weight_nonneg nZ (dl E (l_maps L)) ltac:(lia)) as W.
      rewrite (gap_weight_dl sp E nZ _ Hs) in W. lia. }
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    eapply (srz_mmap_none_pin_spin SEGS R (Z_to_bv 64 pc) M ROM mdl w len (Z_to_bv 64 34) K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F)
              (G _ _ S17) (G _ _ S11) ltac:(lia) (G _ _ S12) (G _ _ S13) eq_refl).
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - exact (grant_exists_L sp brk mbase draw lim inp VI VE E tid L mdl nZ F ltac:(lia) Hs Hroom).
    - (* [comment removed for export] *)
      intros p Hp. rewrite pc_lit_add4 by lia. fold nZ. fold nZ in Hp.
      destruct (grant_ok_na_pin_unpack _ _ _ Hp) as (Hal & Hpos & Htop & Hrf).
      rewrite (mfacts_alloc_top sp brk mbase lim inp _ _ _ _ F) in Htop.
      pose proof (u64_range p) as Hpr.
      assert (Hvis : range_visible H p nZ) by (apply (grant_visible_L sp brk mbase lim inp H E tid L mdl p nZ F HIN Hs ltac:(lia) Hp)).
      assert (Hev : edenot (EB sp draw inp a tid c pl (js ++ [p])) (EVar v) = p).
      { rewrite EB_app. cbn [edenot ev]. unfold v. rewrite <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
      set (n := Z_to_bv 64 nZ) in *.
      assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in Htop; lia).
      assert (Himg : bv_unsigned p + nZ <= A_img_lo \/ A_img_hi <= bv_unsigned p).
      { pose proof Hrf as Hrf0. rewrite (mf_res _ _ _ _ _ _ _ _ _ F), (mf_maps _ _ _ _ _ _ _ _ _ F), region_free_app in Hrf0. apply andb_prop in Hrf0 as [Hrf0 _].
        apply (reserved_apart p nZ); [lia | unfold stack_max_size in *; lia | exact Hrf0]. }
      pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
      assert (EWB : with_mmap_backing (Z_to_bv 64 34) p n (noaccess_model p n mdl) = noaccess_model p n mdl).
      { unfold with_mmap_backing. rewrite mmap_noreserve_b_22. reflexivity. }
      rewrite EWB.
      pose proof HL as HL0. pose proof HL as HL1. unfold ledger_vars_lt in HL1.
      apply (HK p); [| rewrite noaccess_model_vm; cbn [vm_noaccess]; left; reflexivity | exact Hvis].
      constructor.
      + (* [comment removed for export] *)
        apply regs_ok_set; [| intros X; apply (f_equal bv_unsigned) in X; discriminate X | exact Hev].
        rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
      + (* [comment removed for export] *)
        rewrite mrestrict_unfill.
        assert (KO' : know_ok SEGS (EB sp draw inp a tid c pl (js ++ [p])) (mrestrict H M) kn).
        { rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN]. }
        assert (KF : forall V, know_ok SEGS (EB sp draw inp a tid c pl (js ++ [p])) V (GF_none v nZ)).
        { intros V. rewrite EB_app. unfold v, GF_none. apply kfacts_grant; try assumption; unfold stack_max_size in *; lia. }
        assert (KD : forall V, know_ok SEGS (EB sp draw inp a tid c pl (js ++ [p])) V (dsj_entries v nZ (DS_std L))).
        { intros V. rewrite EB_app. unfold v.
          apply (dsj_entries_ok SEGS (VB sp draw inp a tid c pl js) (blobs0 draw (in_argv inp)) V _ nZ (DS_std L) p ltac:(lia)
                   ltac:(unfold stack_max_size in *; lia) (DS_std_claims sp brk mbase draw lim inp VI VE E tid L mdl nZ F Hshd (ev_EB_sp sp draw inp a tid c pl js) Hs ltac:(lia)) Hp).
          unfold DS_std, DS_maps. apply Forall_app. split.
          - constructor; [cbn; split; reflexivity|]. constructor; [cbn; split; reflexivity|]. constructor; [cbn; split; reflexivity|]. constructor.
          - apply Forall_forall. intros d Hd. apply in_map_iff in Hd as ([e en] & <- & Hin). cbn [fst snd]. split; [|reflexivity].
            cbn [saddr_vars_lt a_base]. exact (proj1 (forallb_forall _ _) HL1 _ Hin). }
        unfold kn_grant_none, kn_grant_none_d. apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KF|].
        apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KD|].
        apply (kn_keep_sound SEGS _ (mrestrict H M) (unfill p n (mrestrict H M)) MUnmap).
        * apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KF|].
          apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KD | exact KO'].
        * exact KO'.
        * unfold estart, elenZ. cbn [a_base a_off]. rewrite Hev. cbn [edenot]. fold n. rewrite Hun.
          rewrite Z.add_0_r, <- Hun. apply mem_change_unfill.
      + (* [comment removed for export] *)
        intros x Hx. rewrite unfill_out; [apply HA; exact Hx|]. rewrite Hun. unfold stack_max_size in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        assert (Hout : bv_unsigned x < bv_unsigned p \/ bv_unsigned p + bv_unsigned n <= bv_unsigned x).
        { rewrite Hun. destruct (proj1 (Forall_forall _ _) Hhin r Hr) as ([qe qn] & Hq & Q1 & Q2). cbn [fst snd] in Q1, Q2.
          pose proof Hrf as Hrf'. rewrite (mf_res _ _ _ _ _ _ _ _ _ F), (mf_maps _ _ _ _ _ _ _ _ _ F), region_free_app in Hrf'.
          apply andb_prop in Hrf' as [_ Hrf'].
          pose proof (region_free_In _ p n (edenot E qe) (Z_to_bv 64 qn) Hrf'
                        ltac:(unfold dl; apply in_map_iff; exists (qe, qn); split; [reflexivity | exact Hq])) as Hap.
          pose proof (proj1 (forallb_forall _ _) Hs _ Hq) as Hqn. cbn [snd] in Hqn. apply andb_prop in Hqn as [N0 N1].
          apply Z.leb_le in N0. apply Z.ltb_lt in N1. rewrite Hun, (u_small qn) in Hap by lia. unfold E in Hap. lia. }
        rewrite unfill_out by exact Hout. exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx).
      + (* [comment removed for export] *) rewrite noaccess_model_lazy. exact HLZ.
      + (* [comment removed for export] *)
        eapply MInv_transport; [exact HM | reflexivity | reflexivity |].
        pose proof (eager_used_none_nr_le (Z_to_bv 64 34) p n mdl WF Hal
                      ltac:(rewrite Hun; unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult)
                      ltac:(rewrite Hun; lia) ltac:(rewrite Hun; unfold stack_max_size in *; lia)) as HEA.
        rewrite EWB in HEA. change (vm_limit (m_vmmaps (noaccess_model p n mdl))) with (vm_limit (m_vmmaps mdl)).
        destruct HM as [_ _ _ _ N5]. lia.
      + (* [comment removed for export] *)
        constructor; rewrite ?noaccess_model_vm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
        * exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
        * cbn [lgrant_nr l_brk]. exact (mf_brk _ _ _ _ _ _ _ _ _ F).
        * exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * cbn [lgrant_nr l_maps dl List.map fst snd]. rewrite Hev, (mf_maps _ _ _ _ _ _ _ _ _ F). fold (dl (EB sp draw inp a tid c pl (js ++ [p])) (l_maps L)).
          rewrite EB_app. unfold E, EB. rewrite (dl_app_env _ [p] _ _ HL1). reflexivity.
        * (* [comment removed for export] *)
          cbn [lgrant_nr l_maps ivs_apart dl List.map fst snd]. fold (dl (EB sp draw inp a tid c pl (js ++ [p])) (l_maps L)). rewrite Hev.
          rewrite EB_app. unfold E, EB in F |- *. rewrite (dl_app_env _ [p] _ _ HL1). rewrite <- (mf_maps _ _ _ _ _ _ _ _ _ F).
          pose proof Hrf as Hrf0. rewrite region_free_app in Hrf0. apply andb_prop in Hrf0 as [_ Hrf2].
          split; [| rewrite (mf_maps _ _ _ _ _ _ _ _ _ F); exact (mf_apart _ _ _ _ _ _ _ _ _ F)].
          apply Forall_forall. intros [qb qn] Hq. cbn [fst snd].
          pose proof (region_free_In _ p n qb qn Hrf2 Hq) as Hov. rewrite Hun in Hov. fold n. rewrite Hun. lia.
        * cbn [lgrant_nr l_eager].
          pose proof (eager_used_none_nr_le (Z_to_bv 64 34) p n mdl WF Hal
                        ltac:(rewrite Hun; unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult)
                        ltac:(rewrite Hun; lia) ltac:(rewrite Hun; unfold stack_max_size in *; lia)) as HEA.
          rewrite EWB in HEA. pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
        * exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * apply model_ivs_wf_with_vmmaps; cbn [vm_maps vm_noaccess vm_init_sp];
            [exact WF | apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hun; lia | exact W1]
            | apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hun; lia | exact W2] | reflexivity].
        * (* [comment removed for export] *) unfold na_clear. rewrite noaccess_model_vm. cbn [vm_noaccess]. apply na_clear_l_cons; [| exact (mf_na _ _ _ _ _ _ _ _ _ F)]. rewrite Hun.
          exact (grant_misses_shadow sp brk mbase draw lim inp VI VE E tid L mdl p nZ F Hshd (ev_EB_sp sp draw inp a tid c pl js) Hs ltac:(lia) Hp).
      + (* [comment removed for export] *)
        unfold maps_ok, lgrant_nr. cbn [l_maps]. constructor.
        * unfold map_ok. cbn [fst snd]. rewrite Hev. unfold stack_max_size, page_size in *.
          split; [exact Hal|]. split; [|split; [lia | split; [lia | exact Himg]]].
          pose proof (Z.mod_pos_bound (bv_unsigned p) 4096 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). nia.
        * exact (maps_ok_env sp draw inp a tid c pl js [p] L HL0 HMO).
      + (* [comment removed for export] *)
        pose proof (regime_ok_env sp draw inp H A hc a tid c pl js [p] L mdl HL0 RG) as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8].
        constructor; try assumption; try (rewrite noaccess_model_lazy; assumption).
        * intros x Hx. destruct (Q4 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
        * unfold hf_inmaps in Q5 |- *. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) Q5 r Hr0) as (q & Hq & Hr).
          exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
        * intros x Hx. destruct (Q8 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_mprotect_rw : forall H A a tid c pl js sr kn L hc lz (vp : nat) (nm eo n pc : Z) w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let p := ev E vp in
    let lo := Z_to_bv 64 (bv_unsigned p + eo) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 226 -> edenot E (sr_get sr 10%bv) = lo -> sr_get sr 11%bv = ELit n -> sr_get sr 12%bv = ELit 3 ->
    In (EVar vp, nm) (l_maps L) -> In (p, Z_to_bv 64 nm) (vm_noaccess (m_vmmaps mdl)) ->
    (forall x : word, bv_unsigned p <= bv_unsigned x < bv_unsigned p + nm -> H x = false) ->
    0 <= eo -> eo + n <= nm -> eo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n ->
    l_eager L + n + A_bytes A <= lim ->
    (forall R' mdl',
       bootS' H A a tid c pl js (sr_upd sr (ridx 10%bv) (ELit 0)) (kn_mprotect (EVar vp) eo n kn) (lcommit L n) hc lz
              R' (zfill lo (Z_to_bv 64 n) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (zfill lo (Z_to_bv 64 n) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz vp nm eo n pc w R M mdl K E p lo HB HF HE Hpc0 Hpc4 S17 S10 S11 S12 Hin Hna Hvis
           Heo Heon Heal Hnal Hn Hbud HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (Ep : edenot (EB sp draw inp a tid c pl js) (EVar vp) = p) by reflexivity.
    (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MOK.
    unfold map_ok in MOK. cbn [fst snd] in MOK. rewrite Ep in MOK. destruct MOK as (Mal & M4k & Mnm & Mtop & Mimg).
    assert (Ulo : bv_unsigned lo = bv_unsigned p + eo) by (unfold lo; apply u_small; unfold stack_max_size in *; lia).
    set (nw := Z_to_bv 64 n).
    assert (Hun : bv_unsigned nw = n) by (unfold nw; apply u_small; unfold stack_max_size in *; lia).
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    assert (Hpr : page_round_up_Z n = n).
    { unfold page_round_up_Z, page_size. pose proof (Z.div_mod n 4096 ltac:(lia)). rewrite Z.mul_comm.
      replace ((n + 4096 - 1) / 4096) with (n / 4096); [lia|].
      replace (n + 4096 - 1) with (4095 + (n / 4096) * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
    assert (HinM : In (p, Z_to_bv 64 nm) (vm_maps (m_vmmaps mdl))).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). unfold dl. apply in_map_iff. exists (EVar vp, nm). split; [reflexivity | exact Hin]. }
    assert (Hmc : map_contains (vm_maps (m_vmmaps mdl)) lo nw = true).
    { unfold map_contains. apply existsb_exists. exists (p, Z_to_bv 64 nm). split; [exact HinM|].
      cbn [fst snd]. rewrite Ulo, Hun, (u_small nm) by (unfold stack_max_size in *; lia). apply andb_true_intro. split; apply Z.leb_le; lia. }
    assert (Hnc : map_contains (vm_noaccess (m_vmmaps mdl)) lo nw = true).
    { unfold map_contains. apply existsb_exists. exists (p, Z_to_bv 64 nm). split; [exact Hna|].
      cbn [fst snd]. rewrite Ulo, Hun, (u_small nm) by (unfold stack_max_size in *; lia). apply andb_true_intro. split; apply Z.leb_le; lia. }
    (* [comment removed for export] *)
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as APM0.
    assert (APM : ivs_apart (vm_maps (m_vmmaps mdl))) by (rewrite (mf_maps _ _ _ _ _ _ _ _ _ F); exact APM0).
    destruct (ivs_apart_split _ _ _ lo nw APM HinM
                ltac:(rewrite Ulo; lia) ltac:(rewrite Ulo, Hun, (u_small nm) by (unfold stack_max_size in *; lia); lia) ltac:(rewrite Hun; lia))
      as (l1 & l2 & EQM & Hrf12).
    pose proof (overlap_sum_one l1 (p, Z_to_bv 64 nm) l2 lo nw Hrf12) as OV. rewrite <- EQM, Hun in OV.
    (* [comment removed for export] *)
    destruct HM as [N1' N2' N3' N4' N5'].
    pose proof (allowed_pages_bound A (m_vm_materialized mdl) HAW N1' N2' N3') as PB. unfold page_size in PB.
    pose proof (mf_eager _ _ _ _ _ _ _ _ _ F) as EG. pose proof (mf_lim _ _ _ _ _ _ _ _ _ F) as LIM.
    assert (Hbud' : mprotect_budget_ok mdl lo nw = true).
    { apply (mprotect_budget_ok_intro_gen mdl lo nw WF). rewrite vm_backing_used_split, Hun, LIM. unfold page_size. lia. }
    eapply (srz_mprotect_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w lo n K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17)).
    - rewrite (HR 10%bv). exact S10.
    - rewrite Ulo. unfold page_size. rewrite Z.add_mod, Mal, Heal by lia. reflexivity.
    - exact (G _ _ S11).
    - exact Hn.
    - rewrite Hpr, Ulo. unfold two_pow_64, stack_max_size in *. lia.
    - exact (G _ _ S12).
    - rewrite Hpr. exact Hnc.
    - rewrite Hpr. exact Hmc.
    - rewrite Hpr. exact Hbud'.
    - rewrite Hpr, pc_lit_add4 by lia. fold nw.
      set (mdl' := mprotect_model lo nw mdl).
      assert (HvisR : range_visible H lo n) by (intros x Hx; apply Hvis; rewrite Ulo in Hx; lia).
      apply (HK (regupd R 10%bv (Z_to_bv 64 0)) mdl'). constructor.
      + apply regs_ok_set; [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate X | reflexivity].
      + (* [comment removed for export] *)
        fold nw. rewrite (mrestrict_zfill H lo nw M) by (rewrite Hun; exact HvisR).
        assert (KZ : kentry_ok SEGS (EB sp draw inp a tid c pl js) (zfill lo nw (mrestrict H M)) (KZero (SA (EVar vp) eo) (ELit n))).
        { rewrite <- Hun. apply kzero_zfill_off; [rewrite Ep, Ulo; reflexivity | rewrite Hun; lia | rewrite Ulo, Hun; unfold stack_max_size in *; lia]. }
        assert (KW : kentry_ok SEGS (EB sp draw inp a tid c pl js) (zfill lo nw (mrestrict H M)) (KWr (SA (EVar vp) eo) (ELit n))).
        { rewrite <- Hun. apply kwr_zfill_off; [rewrite Ep, Ulo; reflexivity | rewrite Hun; lia | rewrite Ulo, Hun; unfold stack_max_size in *; lia]. }
        unfold kn_mprotect. constructor; [exact KZ|]. constructor; [exact KW|].
        apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill lo nw (mrestrict H M)) MGrow); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off]. rewrite Ep. cbn [edenot]. fold nw. rewrite <- Ulo. apply mem_change_zfill.
      + intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. fold nw. rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        rewrite zfill_out; [exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|]. fold nw. rewrite Hun.
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned lo)); [left; assumption|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned lo + n)); [|right; assumption].
        exfalso. rewrite (HvisR x ltac:(lia)) in Hhx. discriminate.
      + unfold mdl'. rewrite (mp_lazy lo nw mdl). exact HLZ.
      + unfold mdl'. apply (MInv_mp A lo nw mdl WF (mkMInv _ _ N1' N2' N3' N4' N5')). rewrite Hun, LIM. lia.
      + (* [comment removed for export] *)
        pose proof (model_ivs_wf_mp lo nw mdl WF) as WF'.
        pose proof (eager_used_mp_le lo nw mdl WF) as EGL. rewrite Hun in EGL.
        unfold mdl'. constructor; cbn [lcommit l_maps l_brk l_eager].
        * rewrite (mp_halted lo nw mdl). exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_reserved lo nw mdl). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_init_sp lo nw mdl). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_limit lo nw mdl). exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_start_brk lo nw mdl). exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_brk lo nw mdl). exact (mf_brk _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_mmap_base lo nw mdl). exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_maps lo nw mdl). exact (mf_maps _ _ _ _ _ _ _ _ _ F).
        * exact APM0.
        * lia.
        * rewrite (mp_fs lo nw mdl). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_fds lo nw mdl). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_tid lo nw mdl). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (mp_noaccess lo nw mdl). apply na_clear_l_sub; [exact (proj1 (proj2 WF)) | exact (mf_na _ _ _ _ _ _ _ _ _ F)].
      + exact HMO.
      + (* [comment removed for export] *)
        constructor; cbn [lcommit l_maps]; try assumption; unfold mdl'; rewrite (mp_lazy lo nw mdl); assumption.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems10.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require BootS2.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.NodesMmDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanKnow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodesDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanHeapKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesMmDrive__Lib.AsanBootKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanLedger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanNodesBrk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootMm3__Lib.AsanBootMm2.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBootW.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootS1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.BootLedgerA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.BootS2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootState.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootNodes2__A3.BootNodes2.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance bootnodes5_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KB_brk (v : nat) (off : Z) : list kentry :=
  [KAlign (EVar v) 4096; KRange (EVar v) (IMG_HI + off) (IMG_HI + brk_aslr_max + off)].

(* [comment removed for export] *)
Definition lbrk (L : ledger) (v : nat) (d : Z) : ledger :=
  Ledger ((EVar v, d) :: l_maps L) (l_brk L + d) (l_eager L + d).

(* [comment removed for export] *)
Definition kn_brk_grant (L : ledger) (v : nat) (gl d : Z) (kn : list kentry) : list kentry :=
  [KZero (SA (EVar v) 0) (ELit gl); KWr (SA (EVar v) 0) (ELit gl);
   KZero (SA (EVar v) gl) (ELit (d - gl)); KWr (SA (EVar v) gl) (ELit (d - gl))]
  ++ dsj_entries v d (DS_std L)
  ++ kn_keep MGrow (dsj_entries v d (DS_std L) ++ kn) kn (EVar v) 0 (ELit d).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_mprotect (eb : expr) (eo n : Z) (kn : list kentry) : list kentry :=
  [KZero (SA eb eo) (ELit n); KWr (SA eb eo) (ELit n)] ++ kn_keep MGrow kn kn eb eo (ELit n).

Section Theorems10.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let usp := bv_unsigned sp.

  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  (* [comment removed for export] *)
  #[using="sp usp"] Lemma dsj_entries_ok_var : forall E M P nZ ds (v : nat) (a : word),
    0 <= nZ -> bv_unsigned a + nZ < 2 ^ 64 -> ev E v = a ->
    dsj_claims E P nZ ds -> P a ->
    know_ok SEGS E M (dsj_entries v nZ ds).
  Proof.
    intros E M P nZ ds v a HnZ Hnw Hev Hds Ha.
    unfold dsj_entries. unfold dsj_claims in Hds.
    induction ds as [|[r l] ds IH]; [constructor|].
    apply Forall_cons_iff in Hds as [Hd Hds].
    cbn [map fst snd] in *. constructor; [|apply IH; assumption].
    specialize (Hd a Ha).
    cbn [kentry_ok]. unfold estart, elenZ in *. cbn [a_base a_off edenot] in *. rewrite Hev.
    rewrite u_small by (pose proof (u64_range a); lia). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_brk_query : forall H A a tid c pl js sr kn L hc lz (pc : Z) w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let b := Z_to_bv 64 (bv_unsigned brk + l_brk L) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true ->
    sr_get sr 17%bv = ELit 214 -> sr_get sr 10%bv = ELit 0 ->
    0 <= l_brk L < 2 ^ 32 -> l_brk L mod 4096 = 0 ->
    (forall R',
       bootS' H A a tid c pl (js ++ [b]) (sr_upd sr (ridx 10%bv) (EVar v)) (KB_brk v (l_brk L) ++ kn) L hc lz R' M mdl ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) M ROM) mdl) K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz pc w R M mdl K E v b HB HF HE Hpc0 Hpc4 Hsr Hkn HL S17 S10 Hb0 Hbal HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    destruct (VE48 sp brk mbase draw inp VI VE) as (_ & VB48 & _ & _). destruct VB48 as (Vb1 & Vb2 & Vb3).
    rewrite reserved_top_val in Vb1, Vb2. unfold page_size in Vb3.
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    eapply (srz_brk_query_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17) (G _ _ S10)).
    rewrite pc_lit_add4 by lia. rewrite (mf_brk _ _ _ _ _ _ _ _ _ F). fold b.
    assert (Hub : bv_unsigned b = bv_unsigned brk + l_brk L).
    { unfold b. apply u_small. unfold brk_aslr_max, IMG_HI in *. pose proof (u64_range brk). lia. }
    assert (Hev : edenot (EB sp draw inp a tid c pl (js ++ [b])) (EVar v) = b).
    { rewrite EB_app. cbn [edenot ev]. unfold v. rewrite <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
    apply HK. constructor.
    - apply regs_ok_set; [| intros X; apply (f_equal bv_unsigned) in X; discriminate X | exact Hev].
      rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
    - apply (proj2 (know_ok_app SEGS _ _ _ _)). split.
      + unfold KB_brk. constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; rewrite Hev.
        * split; [lia|]. rewrite Hub, Z.add_mod, Vb3, Hbal by lia. reflexivity.
        * rewrite Hub. unfold brk_aslr_max, IMG_HI in *. lia.
      + rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN].
    - exact HA.
    - exact HZ.
    - exact HLZ.
    - exact HM.
    - apply mfacts_env; [exact HL | exact F].
    - apply maps_ok_env; [exact HL | exact HMO].
    - apply regime_ok_env; [exact HL | exact RG].
    - exact HT.
    - exact Hcl.
    - exact Ht.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_brk_grow : forall H A a tid c pl js sr kn L hc lz (v : nat) (gl d pc : Z) w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let b := Z_to_bv 64 (bv_unsigned brk + l_brk L) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 214 -> ev E v = b -> (v < length (VB' a tid c pl js))%nat ->
    edenot E (sr_get sr 10%bv) = Z_to_bv 64 (bv_unsigned b + d) ->
    0 <= l_brk L < 2 ^ 32 -> l_brk L mod 4096 = 0 -> d mod 4096 = 0 -> gl mod 4096 = 0 -> 0 < gl < d -> d <= 2 ^ 32 ->
    sivs_sizes_ok (l_maps L) = true ->
    l_eager L + d + A_bytes A <= lim ->
    (* [comment removed for export] *)
    (forall R' mdl', brk_grow_adm d mdl = false ->
       bootS' H A a tid c pl js (sr_upd sr (ridx 10%bv) (EVar v)) kn L hc lz R' M mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) M ROM) mdl') K) ->
    (* [comment removed for export] *)
    (forall R' mdl', brk_grow_adm d mdl = true ->
       bootS' H A a tid c pl js (sr_upd sr (ridx 10%bv) (EAlu ALU_ADD (EVar v) (ELit d))) (kn_brk_grant L v gl d kn) (lbrk L v d) hc lz
              R' (zfill b (Z_to_bv 64 d) M) mdl' ->
       (forall x : word, bv_unsigned b <= bv_unsigned x < bv_unsigned b + d -> H x = false) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (zfill b (Z_to_bv 64 d) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz v gl d pc w R M mdl K E b HB HF HE Hpc0 Hpc4 S17 Hev Hvlt H10 Hb0 Hbal Hdal Hgal Hgl Hd32 Hs Hbud HKA HKB.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    destruct (VE48 sp brk mbase draw inp VI VE) as (_ & VB48 & _ & _). destruct VB48 as (Vb1 & Vb2 & Vb3).
    rewrite reserved_top_val in Vb1, Vb2. unfold page_size in Vb3.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    pose proof (u64_range brk) as Ubrk.
    assert (Hub : bv_unsigned b = bv_unsigned brk + l_brk L).
    { unfold b. apply u_small. unfold brk_aslr_max, IMG_HI in *. lia. }
    assert (Hb : vm_brk (m_vmmaps mdl) = b) by exact (mf_brk _ _ _ _ _ _ _ _ _ F).
    assert (Hsb : vm_start_brk (m_vmmaps mdl) = brk) by exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
    assert (G17 : getr R 17 = Z_to_bv 64 214) by (rewrite (HR 17%bv), S17; reflexivity).
    assert (G10 : getr R 10 = Z_to_bv 64 (bv_unsigned b + d)) by (rewrite (HR 10%bv); exact H10).
    assert (Hbal' : bv_unsigned b mod page_size = 0).
    { unfold page_size. rewrite Hub, Z.add_mod, Vb3, Hbal by lia. reflexivity. }
    assert (Htop : alloc_top (m_vmmaps mdl) = bv_unsigned sp - stack_max_size) by exact (mfacts_alloc_top _ _ _ _ _ _ _ _ _ F).
    destruct (brk_grow_adm d mdl) eqn:Hadm.
    - (* [comment removed for export] *)
      eapply (srz_brk_grow_grant_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w d K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F) G17);
        rewrite ?Hb, ?Hsb; try assumption.
      1-4: rewrite ?Hub; unfold brk_aslr_max, IMG_HI in *; lia.
      rewrite pc_lit_add4 by lia.
      pose proof (brk_grow_adm_unpack d mdl) as U. cbv zeta in U. rewrite Hb in U.
      specialize (U Hbal' Hdal ltac:(lia) ltac:(unfold IMG_HI in *; lia) ltac:(unfold brk_aslr_max, IMG_HI in *; lia) Hadm).
      destruct U as (Htop' & Hrf & Hlive). rewrite Htop in Htop'.
      assert (Hpin : grant_ok_na_pin mdl b d = true).
      { unfold grant_ok_na_pin. rewrite Htop.
        rewrite (proj2 (Z.eqb_eq _ _) Hbal'), (proj2 (Z.leb_le _ _) Htop').
        rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned b))) by (unfold IMG_HI in *; lia). cbn [andb].
        apply (region_free_shrink _ b (d + page_size) d); [unfold page_size; lia | unfold page_size, brk_aslr_max, IMG_HI, stack_max_size in *; lia | exact Hrf]. }
      assert (Hvis : range_visible H b d) by (apply (grant_visible_L sp brk mbase lim inp H E tid L mdl b d F HIN Hs ltac:(lia) Hpin)).
      set (n := Z_to_bv 64 d). assert (Hun : bv_unsigned n = d) by (unfold n; apply u_small; lia).
      destruct (grant_ok_na_pin_unpack _ _ _ Hpin) as (_ & _ & _ & Hrf'). fold n in Hrf'.
      apply HKB; [reflexivity | | exact Hvis].
      constructor.
      + (* [comment removed for export] *)
        apply regs_ok_set; [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate X |].
        cbn [edenot]. fold E. rewrite Hev. fold b. apply bv_eq. rewrite u_add64, !u_small by (unfold brk_aslr_max, IMG_HI, stack_max_size in *; lia).
        apply Z.mod_small. unfold brk_aslr_max, IMG_HI, stack_max_size in *; lia.
      + (* [comment removed for export] *)
        fold n. fold E. rewrite (mrestrict_zfill H b n M) by (rewrite Hun; exact Hvis).
        assert (KD : forall V, know_ok SEGS E V (dsj_entries v d (DS_std L))).
        { intros V. apply (dsj_entries_ok_var E V _ d (DS_std L) v b ltac:(lia) ltac:(unfold brk_aslr_max, IMG_HI, stack_max_size in *; lia) Hev
                           (DS_std_claims sp brk mbase draw lim inp VI VE E tid L mdl d F Hshd (ev_EB_sp sp draw inp a tid c pl js) Hs ltac:(lia)) Hpin). }
        assert (KZ : kentry_ok SEGS E (zfill b n (mrestrict H M)) (KZero (SA (EVar v) 0) (ELit d))).
        { unfold n. apply EntryGlue.kzero_zfill; [cbn [edenot]; exact Hev | lia | unfold brk_aslr_max, IMG_HI, stack_max_size in *; lia]. }
        assert (KW : kentry_ok SEGS E (zfill b n (mrestrict H M)) (KWr (SA (EVar v) 0) (ELit d))).
        { unfold n. apply EntryGlue.kwr_zfill; [cbn [edenot]; exact Hev | lia | unfold brk_aslr_max, IMG_HI, stack_max_size in *; lia]. }
        unfold kn_brk_grant. apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [|apply (proj2 (know_ok_app SEGS _ _ _ _)); split].
        * constructor; [apply (kzero_sub SEGS E _ (EVar v) 0 d 0 gl KZ); lia|].
          constructor; [apply (kwr_sub SEGS E _ (EVar v) 0 d 0 gl KW); lia|].
          constructor; [apply (kzero_sub SEGS E _ (EVar v) 0 d gl (d - gl) KZ); lia|].
          constructor; [apply (kwr_sub SEGS E _ (EVar v) 0 d gl (d - gl) KW); lia|].
          constructor.
        * apply KD.
        * apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill b n (mrestrict H M)) MGrow).
          -- apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KD | exact HKN].
          -- exact HKN.
          -- unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hev. fold n. rewrite Hun, Z.add_0_r, <- Hun. apply mem_change_zfill.
      + (* [comment removed for export] *)
        intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. fold n. rewrite Hun. unfold stack_max_size, usp in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *.
        apply Forall_forall. intros r Hr x Hx Hhx. rewrite zfill_out; [exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|].
        fold n. rewrite Hun.
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned b)); [left; assumption|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned b + d)); [|right; assumption].
        exfalso. rewrite (Hvis x ltac:(lia)) in Hhx. discriminate.
      + (* [comment removed for export] *) rewrite brk_grown_model_lazy. exact HLZ.
      + (* [comment removed for export] *)
        pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as (W1 & W2 & W3 & W4).
        eapply MInv_transport; [exact HM | reflexivity | reflexivity |].
        pose proof (AsanNodesMmB.eager_used_cons_le mdl (vm_brk (m_vmmaps mdl)) n (m_vmmaps (brk_grown_model d mdl)) W1
                      ltac:(apply iv_wf_intro; rewrite Hb, Hun; unfold stack_max_size in *; lia) eq_refl eq_refl) as Hle.
        change (with_vmmaps (m_vmmaps (brk_grown_model d mdl)) mdl) with (brk_grown_model d mdl) in Hle.
        change (vm_limit (m_vmmaps (brk_grown_model d mdl))) with (vm_limit (m_vmmaps mdl)).
        rewrite (mf_lim _ _ _ _ _ _ _ _ _ F). rewrite Hun in Hle. pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
      + (* [comment removed for export] *)
        pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as (W1 & W2 & W3 & W4).
        constructor; rewrite ?brk_grown_model_vm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
        * rewrite brk_grown_model_halted. exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * exact Hsb.
        * rewrite Hb, Hub. cbn [lbrk l_brk]. f_equal. lia.
        * exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * cbn [lbrk l_maps dl List.map fst snd]. cbn [edenot]. fold E. rewrite Hb, Hev, (mf_maps _ _ _ _ _ _ _ _ _ F). reflexivity.
        * cbn [lbrk l_maps ivs_apart dl List.map fst snd]. cbn [edenot]. fold E. rewrite Hev. fold n. unfold E. fold (dl (EB' a tid c pl js) (l_maps L)).
          rewrite <- (mf_maps _ _ _ _ _ _ _ _ _ F).
          rewrite region_free_app in Hrf'. apply andb_prop in Hrf' as [_ Hrf2].
          split; [| rewrite (mf_maps _ _ _ _ _ _ _ _ _ F); exact (mf_apart _ _ _ _ _ _ _ _ _ F)].
          apply Forall_forall. intros [qb qn] Hq. cbn [fst snd].
          pose proof (region_free_In _ b n qb qn Hrf2 Hq) as Hov. rewrite Hun in Hov. rewrite Hun. lia.
        * cbn [lbrk l_eager].
          pose proof (AsanNodesMmB.eager_used_cons_le mdl (vm_brk (m_vmmaps mdl)) n (m_vmmaps (brk_grown_model d mdl)) W1
                        ltac:(apply iv_wf_intro; rewrite Hb, Hun; unfold stack_max_size in *; lia) eq_refl eq_refl) as Hle.
          change (with_vmmaps (m_vmmaps (brk_grown_model d mdl)) mdl) with (brk_grown_model d mdl) in Hle.
          rewrite Hun in Hle. pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
        * rewrite brk_grown_model_fs. exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite brk_grown_model_fds. exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite brk_grown_model_tid. exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * unfold model_ivs_wf. rewrite brk_grown_model_vm, brk_grown_model_lazy. cbn [vm_maps vm_noaccess vm_init_sp].
          fold n. split; [apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hb, Hun; unfold stack_max_size in *; lia | exact W1]|].
          split; [exact W2|]. split; [exact W3|]. exact W4.
        * (* [comment removed for export] *) unfold na_clear. rewrite brk_grown_model_vm. cbn [vm_noaccess]. exact (mf_na _ _ _ _ _ _ _ _ _ F).
      + (* [comment removed for export] *)
        unfold maps_ok, lbrk. cbn [l_maps]. constructor.
        * unfold map_ok. cbn [fst snd edenot]. fold E. rewrite Hev. unfold page_size in Hbal'. unfold stack_max_size, A_img_hi, IMG_HI in *.
          split; [exact Hbal'|]. split; [lia|]. split; [lia|]. split; [unfold usp in *; lia | right; lia].
        * exact HMO.
      + (* [comment removed for export] *)
        constructor; try assumption; try (rewrite brk_grown_model_lazy; assumption).
        -- intros x Hx. destruct (HIN x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lbrk. cbn [l_maps]. right. exact Hq.
        -- unfold hf_inmaps in *. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) Hhin r Hr0) as (q & Hq & Hr).
           exists q. split; [| exact Hr]. unfold lbrk. cbn [l_maps]. right. exact Hq.
        -- intros x Hx. destruct (Hshd x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lbrk. cbn [l_maps]. right. exact Hq.
      + exact HT.
      + exact Hcl.
      + exact Ht.
    - (* [comment removed for export] *)
      eapply (srz_brk_grow_blocked_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w (Z_to_bv 64 (bv_unsigned b + d)) K HF HE
                (mf_halted _ _ _ _ _ _ _ _ _ F) G17 G10).
      + rewrite u_small; unfold brk_aslr_max, IMG_HI in *; lia.
      + rewrite Hsb, u_small; unfold brk_aslr_max, IMG_HI in *; lia.
      + rewrite Hb, u_small; unfold brk_aslr_max, IMG_HI in *; lia.
      + unfold brk_grow_adm in Hadm. rewrite Hb in Hadm. exact Hadm.
      + rewrite pc_lit_add4 by lia. rewrite Hb. apply HKA; [reflexivity|].
        constructor; try assumption.
        apply regs_ok_set; [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate X | cbn [edenot]; exact Hev].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_mmap_fixed_none_guard : forall H A a tid c pl js sr kn L hc lz (v : nat) (gl d pc : Z) rest w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let b := ev E v in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 222 -> edenot E (sr_get sr 10%bv) = b -> sr_get sr 11%bv = ELit gl -> sr_get sr 12%bv = ELit 0 ->
    sr_get sr 13%bv = ELit 50 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    l_maps L = (EVar v, d) :: rest -> gl mod 4096 = 0 -> 0 < gl <= d ->
    (forall x : word, bv_unsigned b <= bv_unsigned x < bv_unsigned b + d -> H x = false) ->
    (bv_unsigned b + gl <= SHB_LO \/ SHB_HI <= bv_unsigned b) ->   (* [comment removed for export] *)
    (forall R' mdl',
       bootS' H A a tid c pl js sr (kn_keep MUnmap kn kn (EVar v) 0 (ELit gl)) L hc
              (maps_subtract lz (bv_unsigned b) (bv_unsigned b + gl)) R' (unfill b (Z_to_bv 64 gl) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (unfill b (Z_to_bv 64 gl) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz v gl d pc rest w R M mdl K E b HB HF HE Hpc0 Hpc4 S17 S10 S11 S12 S13 S14 S15 HL Hgal Hgl Hvis Hshb HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (Eb : edenot (EB sp draw inp a tid c pl js) (EVar v) = b) by reflexivity.
    (* [comment removed for export] *)
    pose proof HMO as MO. unfold maps_ok in MO. rewrite HL in MO. apply Forall_cons_iff in MO as [MOK MOR].
    unfold map_ok in MOK. cbn [fst snd] in MOK. rewrite Eb in MOK. destruct MOK as (Mal & M4k & Md & Mtop & Mimg).
    set (n := Z_to_bv 64 gl).
    assert (Hun : bv_unsigned n = gl) by (unfold n; apply u_small; unfold stack_max_size in *; lia).
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    assert (Hpr : page_round_up_Z gl = gl).
    { unfold page_round_up_Z, page_size. pose proof (Z.div_mod gl 4096 ltac:(lia)). rewrite Z.mul_comm.
      replace ((gl + 4096 - 1) / 4096) with (gl / 4096); [lia|].
      replace (gl + 4096 - 1) with (4095 + (gl / 4096) * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
    assert (HMAPS : vm_maps (m_vmmaps mdl) = (b, Z_to_bv 64 d) :: dl (EB sp draw inp a tid c pl js) rest).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F), HL. reflexivity. }
    eapply (srz_mmap_fixed_noaccess_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w b gl K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17)).
    - rewrite (HR 10%bv). exact S10.
    - unfold page_size. exact Mal.
    - lia.
    - exact (G _ _ S11).
    - lia.
    - rewrite Hpr, (mfacts_alloc_top sp brk mbase lim inp _ _ _ _ F). unfold stack_max_size in *. lia.
    - exact (G _ _ S12).
    - exact (G _ _ S13).
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - rewrite Hpr, (mf_res _ _ _ _ _ _ _ _ _ F). fold n. apply reserved_free_of_apart. rewrite Hun. lia.
    - rewrite Hpr, HMAPS. fold n. unfold map_contains. cbn [existsb fst snd]. rewrite Hun, (u_small d) by (unfold stack_max_size in *; lia).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le (bv_unsigned b + gl) _)) by lia. reflexivity.
    - rewrite Hpr, pc_lit_add4 by lia. fold n.
      set (mdl' := fixed_noaccess_model b n mdl).
      assert (Hend : bv_unsigned b + bv_unsigned n <= 2 ^ 64) by (rewrite Hun; unfold stack_max_size in *; lia).
      assert (Hnl : bv_unsigned n mod page_size = 0) by (rewrite Hun; unfold page_size; exact Hgal).
      assert (Hpos : 0 < bv_unsigned n) by (rewrite Hun; lia).
      apply (HK (regupd R 10%bv b) mdl'). constructor.
      + intros r. destruct (bv_eqb r 10%bv) eqn:Er.
        * apply bv_eqb_eq in Er. subst r. rewrite getr_same by (intros X; apply (f_equal bv_unsigned) in X; discriminate X). symmetry. exact S10.
        * assert (Hne : r <> 10%bv) by (intros X; rewrite X, bv_eqb_refl in Er; discriminate Er).
          rewrite getr_other by exact Hne. apply HR.
      + (* [comment removed for export] *)
        rewrite mrestrict_unfill.
        apply (kn_keep_sound SEGS _ (mrestrict H M) (unfill b n (mrestrict H M)) MUnmap); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off edenot]. fold (EB sp draw inp a tid c pl js). fold b. fold n. rewrite Z.add_0_r.
        apply mem_change_unfill.
      + intros x Hx. rewrite unfill_out; [apply HA; exact Hx|]. fold n. rewrite Hun. unfold stack_max_size in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        rewrite unfill_out; [exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|]. fold n. rewrite Hun.
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned b)); [left; assumption|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned b + gl)); [|right; assumption].
        exfalso. rewrite (Hvis x ltac:(lia)) in Hhx. discriminate.
      + unfold mdl'. rewrite (fxn_lazy b n mdl), HLZ, Hun. reflexivity.
      + unfold mdl'. exact (MInv_fxn A b n mdl WF ltac:(unfold page_size; exact Mal) Hnl Hpos Hend HM).
      + (* [comment removed for export] *)
        pose proof (model_ivs_wf_fxn b n mdl WF Hpos Hend) as WF'.
        pose proof (eager_used_fxn_le b n mdl WF Hpos Hend) as EGL.
        unfold mdl'. constructor.
        * rewrite (fxn_halted b n mdl). exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_reserved b n mdl). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_init_sp b n mdl). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_limit b n mdl). exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_start_brk b n mdl). exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_brk b n mdl). exact (mf_brk _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_mmap_base b n mdl). exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_maps b n mdl). exact (mf_maps _ _ _ _ _ _ _ _ _ F).
        * exact (mf_apart _ _ _ _ _ _ _ _ _ F).
        * pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
        * rewrite (fxn_fs b n mdl). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_fds b n mdl). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (fxn_tid b n mdl). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (fxn_noaccess b n mdl).
          apply na_clear_l_cons; [rewrite Hun; exact Hshb | apply na_clear_l_sub; [exact W2 | exact (mf_na _ _ _ _ _ _ _ _ _ F)]].
      + exact HMO.
      + (* [comment removed for export] *)
        constructor.
        * exact HH.
        * exact HAW.
        * unfold mdl'. apply (lazy_cover_fxn A b n mdl WF Hpos). exact HCOV.
        * exact HIN.
        * exact Hhin.
        * exact Habv.
        * intros x Hx. unfold mdl'. rewrite (fxn_lazy b n mdl), Hun.
          assert (Hout : ~ (bv_unsigned b <= bv_unsigned x < bv_unsigned b + d)) by (intros X; rewrite (Hvis x X) in Hx; discriminate).
          rewrite page_in_ranges_subtract_out; [exact (Hhl x Hx) | exact W3 | lia |].
          pose proof (u64_range x) as Xr. unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small by lia.
          pose proof (Z.div_mod (bv_unsigned b) 4096 ltac:(lia)). pose proof (Z.div_mod gl 4096 ltac:(lia)). nia.
        * exact Hshd.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_mmap_none_anon : forall H A a tid c pl js sr kn L hc lz (len pc : Z) w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let nZ := page_round_up_Z len in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> sivs_sizes_ok (l_maps L) = true ->
    sr_get sr 17%bv = ELit 222 -> sr_get sr 10%bv = ELit 0 -> sr_get sr 11%bv = ELit len -> sr_get sr 12%bv = ELit 0 ->
    sr_get sr 13%bv = ELit 34 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len ->
    IMG_HI + nZ + gws nZ (l_maps L) <= 0x7fff80000000 - stack_max_size ->
    (forall p R' mdl',
       bootS' H A a tid c pl (js ++ [p]) (sr_upd sr (ridx 10%bv) (EVar v)) (kn_grant_none L v nZ kn) (lgrant_nr L v nZ) hc lz
              R' (unfill p (Z_to_bv 64 nZ) M) mdl' ->
       In (p, Z_to_bv 64 nZ) (vm_noaccess (m_vmmaps mdl')) ->
       (forall x : word, bv_unsigned p <= bv_unsigned x < bv_unsigned p + nZ -> H x = false) ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (unfill p (Z_to_bv 64 nZ) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz len pc w R M mdl K E v nZ HB HF HE Hpc0 Hpc4
           Hsr Hkn HL Hs S17 S10 S11 S12 S13 S14 S15 Hlen Hroom HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
    assert (Hlen64 : len < 2 ^ 64).
    { unfold stack_max_size, IMG_HI in Hroom. pose proof (gap_weight_nonneg nZ (dl E (l_maps L)) ltac:(lia)) as W.
      rewrite (gap_weight_dl sp E nZ _ Hs) in W. lia. }
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    eapply (srz_mmap_none_pin_spin SEGS R (Z_to_bv 64 pc) M ROM mdl w len (Z_to_bv 64 34) K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F)
              (G _ _ S17) (G _ _ S11) ltac:(lia) (G _ _ S12) (G _ _ S13) eq_refl).
    - rewrite (G _ _ S14). apply bv_eq. reflexivity.
    - exact (G _ _ S15).
    - exact (grant_exists_L sp brk mbase draw lim inp VI VE E tid L mdl nZ F ltac:(lia) Hs Hroom).
    - (* [comment removed for export] *)
      intros p Hp. rewrite pc_lit_add4 by lia. fold nZ. fold nZ in Hp.
      destruct (grant_ok_na_pin_unpack _ _ _ Hp) as (Hal & Hpos & Htop & Hrf).
      rewrite (mfacts_alloc_top sp brk mbase lim inp _ _ _ _ F) in Htop.
      pose proof (u64_range p) as Hpr.
      assert (Hvis : range_visible H p nZ) by (apply (grant_visible_L sp brk mbase lim inp H E tid L mdl p nZ F HIN Hs ltac:(lia) Hp)).
      assert (Hev : edenot (EB sp draw inp a tid c pl (js ++ [p])) (EVar v) = p).
      { rewrite EB_app. cbn [edenot ev]. unfold v. rewrite <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
      set (n := Z_to_bv 64 nZ) in *.
      assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in Htop; lia).
      assert (Himg : bv_unsigned p + nZ <= A_img_lo \/ A_img_hi <= bv_unsigned p).
      { pose proof Hrf as Hrf0. rewrite (mf_res _ _ _ _ _ _ _ _ _ F), (mf_maps _ _ _ _ _ _ _ _ _ F), region_free_app in Hrf0. apply andb_prop in Hrf0 as [Hrf0 _].
        apply (reserved_apart p nZ); [lia | unfold stack_max_size in *; lia | exact Hrf0]. }
      pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
      assert (EWB : with_mmap_backing (Z_to_bv 64 34) p n (noaccess_model p n mdl) = noaccess_model p n mdl).
      { unfold with_mmap_backing. rewrite mmap_noreserve_b_22. reflexivity. }
      rewrite EWB.
      pose proof HL as HL0. pose proof HL as HL1. unfold ledger_vars_lt in HL1.
      apply (HK p); [| rewrite noaccess_model_vm; cbn [vm_noaccess]; left; reflexivity | exact Hvis].
      constructor.
      + (* [comment removed for export] *)
        apply regs_ok_set; [| intros X; apply (f_equal bv_unsigned) in X; discriminate X | exact Hev].
        rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
      + (* [comment removed for export] *)
        rewrite mrestrict_unfill.
        assert (KO' : know_ok SEGS (EB sp draw inp a tid c pl (js ++ [p])) (mrestrict H M) kn).
        { rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN]. }
        assert (KF : forall V, know_ok SEGS (EB sp draw inp a tid c pl (js ++ [p])) V (GF_none v nZ)).
        { intros V. rewrite EB_app. unfold v, GF_none. apply kfacts_grant; try assumption; unfold stack_max_size in *; lia. }
        assert (KD : forall V, know_ok SEGS (EB sp draw inp a tid c pl (js ++ [p])) V (dsj_entries v nZ (DS_std L))).
        { intros V. rewrite EB_app. unfold v.
          apply (dsj_entries_ok SEGS (VB sp draw inp a tid c pl js) (blobs0 draw (in_argv inp)) V _ nZ (DS_std L) p ltac:(lia)
                   ltac:(unfold stack_max_size in *; lia) (DS_std_claims sp brk mbase draw lim inp VI VE E tid L mdl nZ F Hshd (ev_EB_sp sp draw inp a tid c pl js) Hs ltac:(lia)) Hp).
          unfold DS_std, DS_maps. apply Forall_app. split.
          - constructor; [cbn; split; reflexivity|]. constructor; [cbn; split; reflexivity|]. constructor; [cbn; split; reflexivity|]. constructor.
          - apply Forall_forall. intros d Hd. apply in_map_iff in Hd as ([e en] & <- & Hin). cbn [fst snd]. split; [|reflexivity].
            cbn [saddr_vars_lt a_base]. exact (proj1 (forallb_forall _ _) HL1 _ Hin). }
        unfold kn_grant_none, kn_grant_none_d. apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KF|].
        apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KD|].
        apply (kn_keep_sound SEGS _ (mrestrict H M) (unfill p n (mrestrict H M)) MUnmap).
        * apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KF|].
          apply (proj2 (know_ok_app SEGS _ _ _ _)); split; [apply KD | exact KO'].
        * exact KO'.
        * unfold estart, elenZ. cbn [a_base a_off]. rewrite Hev. cbn [edenot]. fold n. rewrite Hun.
          rewrite Z.add_0_r, <- Hun. apply mem_change_unfill.
      + (* [comment removed for export] *)
        intros x Hx. rewrite unfill_out; [apply HA; exact Hx|]. rewrite Hun. unfold stack_max_size in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        assert (Hout : bv_unsigned x < bv_unsigned p \/ bv_unsigned p + bv_unsigned n <= bv_unsigned x).
        { rewrite Hun. destruct (proj1 (Forall_forall _ _) Hhin r Hr) as ([qe qn] & Hq & Q1 & Q2). cbn [fst snd] in Q1, Q2.
          pose proof Hrf as Hrf'. rewrite (mf_res _ _ _ _ _ _ _ _ _ F), (mf_maps _ _ _ _ _ _ _ _ _ F), region_free_app in Hrf'.
          apply andb_prop in Hrf' as [_ Hrf'].
          pose proof (region_free_In _ p n (edenot E qe) (Z_to_bv 64 qn) Hrf'
                        ltac:(unfold dl; apply in_map_iff; exists (qe, qn); split; [reflexivity | exact Hq])) as Hap.
          pose proof (proj1 (forallb_forall _ _) Hs _ Hq) as Hqn. cbn [snd] in Hqn. apply andb_prop in Hqn as [N0 N1].
          apply Z.leb_le in N0. apply Z.ltb_lt in N1. rewrite Hun, (u_small qn) in Hap by lia. unfold E in Hap. lia. }
        rewrite unfill_out by exact Hout. exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx).
      + (* [comment removed for export] *) rewrite noaccess_model_lazy. exact HLZ.
      + (* [comment removed for export] *)
        eapply MInv_transport; [exact HM | reflexivity | reflexivity |].
        pose proof (eager_used_none_nr_le (Z_to_bv 64 34) p n mdl WF Hal
                      ltac:(rewrite Hun; unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult)
                      ltac:(rewrite Hun; lia) ltac:(rewrite Hun; unfold stack_max_size in *; lia)) as HEA.
        rewrite EWB in HEA. change (vm_limit (m_vmmaps (noaccess_model p n mdl))) with (vm_limit (m_vmmaps mdl)).
        destruct HM as [_ _ _ _ N5]. lia.
      + (* [comment removed for export] *)
        constructor; rewrite ?noaccess_model_vm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
        * exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
        * cbn [lgrant_nr l_brk]. exact (mf_brk _ _ _ _ _ _ _ _ _ F).
        * exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * cbn [lgrant_nr l_maps dl List.map fst snd]. rewrite Hev, (mf_maps _ _ _ _ _ _ _ _ _ F). fold (dl (EB sp draw inp a tid c pl (js ++ [p])) (l_maps L)).
          rewrite EB_app. unfold E, EB. rewrite (dl_app_env _ [p] _ _ HL1). reflexivity.
        * (* [comment removed for export] *)
          cbn [lgrant_nr l_maps ivs_apart dl List.map fst snd]. fold (dl (EB sp draw inp a tid c pl (js ++ [p])) (l_maps L)). rewrite Hev.
          rewrite EB_app. unfold E, EB in F |- *. rewrite (dl_app_env _ [p] _ _ HL1). rewrite <- (mf_maps _ _ _ _ _ _ _ _ _ F).
          pose proof Hrf as Hrf0. rewrite region_free_app in Hrf0. apply andb_prop in Hrf0 as [_ Hrf2].
          split; [| rewrite (mf_maps _ _ _ _ _ _ _ _ _ F); exact (mf_apart _ _ _ _ _ _ _ _ _ F)].
          apply Forall_forall. intros [qb qn] Hq. cbn [fst snd].
          pose proof (region_free_In _ p n qb qn Hrf2 Hq) as Hov. rewrite Hun in Hov. fold n. rewrite Hun. lia.
        * cbn [lgrant_nr l_eager].
          pose proof (eager_used_none_nr_le (Z_to_bv 64 34) p n mdl WF Hal
                        ltac:(rewrite Hun; unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult)
                        ltac:(rewrite Hun; lia) ltac:(rewrite Hun; unfold stack_max_size in *; lia)) as HEA.
          rewrite EWB in HEA. pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
        * exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * apply model_ivs_wf_with_vmmaps; cbn [vm_maps vm_noaccess vm_init_sp];
            [exact WF | apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hun; lia | exact W1]
            | apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hun; lia | exact W2] | reflexivity].
        * (* [comment removed for export] *) unfold na_clear. rewrite noaccess_model_vm. cbn [vm_noaccess]. apply na_clear_l_cons; [| exact (mf_na _ _ _ _ _ _ _ _ _ F)]. rewrite Hun.
          exact (grant_misses_shadow sp brk mbase draw lim inp VI VE E tid L mdl p nZ F Hshd (ev_EB_sp sp draw inp a tid c pl js) Hs ltac:(lia) Hp).
      + (* [comment removed for export] *)
        unfold maps_ok, lgrant_nr. cbn [l_maps]. constructor.
        * unfold map_ok. cbn [fst snd]. rewrite Hev. unfold stack_max_size, page_size in *.
          split; [exact Hal|]. split; [|split; [lia | split; [lia | exact Himg]]].
          pose proof (Z.mod_pos_bound (bv_unsigned p) 4096 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). nia.
        * exact (maps_ok_env sp draw inp a tid c pl js [p] L HL0 HMO).
      + (* [comment removed for export] *)
        pose proof (regime_ok_env sp draw inp H A hc a tid c pl js [p] L mdl HL0 RG) as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8].
        constructor; try assumption; try (rewrite noaccess_model_lazy; assumption).
        * intros x Hx. destruct (Q4 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
        * unfold hf_inmaps in Q5 |- *. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) Q5 r Hr0) as (q & Hq & Hr).
          exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
        * intros x Hx. destruct (Q8 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="VI VE usp"] Theorem bs_mprotect_rw : forall H A a tid c pl js sr kn L hc lz (vp : nat) (nm eo n pc : Z) w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let p := ev E vp in
    let lo := Z_to_bv 64 (bv_unsigned p + eo) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_get sr 17%bv = ELit 226 -> edenot E (sr_get sr 10%bv) = lo -> sr_get sr 11%bv = ELit n -> sr_get sr 12%bv = ELit 3 ->
    In (EVar vp, nm) (l_maps L) -> In (p, Z_to_bv 64 nm) (vm_noaccess (m_vmmaps mdl)) ->
    (forall x : word, bv_unsigned p <= bv_unsigned x < bv_unsigned p + nm -> H x = false) ->
    0 <= eo -> eo + n <= nm -> eo mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n ->
    l_eager L + n + A_bytes A <= lim ->
    (forall R' mdl',
       bootS' H A a tid c pl js (sr_upd sr (ridx 10%bv) (ELit 0)) (kn_mprotect (EVar vp) eo n kn) (lcommit L n) hc lz
              R' (zfill lo (Z_to_bv 64 n) M) mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) (zfill lo (Z_to_bv 64 n) M) ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L hc lz vp nm eo n pc w R M mdl K E p lo HB HF HE Hpc0 Hpc4 S17 S10 S11 S12 Hin Hna Hvis
           Heo Heon Heal Hnal Hn Hbud HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL sp brk mbase draw inp VI VE) as SLo. pose proof (SH sp brk mbase draw inp VI VE) as SHi.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (Ep : edenot (EB sp draw inp a tid c pl js) (EVar vp) = p) by reflexivity.
    (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) HMO _ Hin) as MOK.
    unfold map_ok in MOK. cbn [fst snd] in MOK. rewrite Ep in MOK. destruct MOK as (Mal & M4k & Mnm & Mtop & Mimg).
    assert (Ulo : bv_unsigned lo = bv_unsigned p + eo) by (unfold lo; apply u_small; unfold stack_max_size in *; lia).
    set (nw := Z_to_bv 64 n).
    assert (Hun : bv_unsigned nw = n) by (unfold nw; apply u_small; unfold stack_max_size in *; lia).
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    assert (Hpr : page_round_up_Z n = n).
    { unfold page_round_up_Z, page_size. pose proof (Z.div_mod n 4096 ltac:(lia)). rewrite Z.mul_comm.
      replace ((n + 4096 - 1) / 4096) with (n / 4096); [lia|].
      replace (n + 4096 - 1) with (4095 + (n / 4096) * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
    pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as WF. pose proof WF as (W1 & W2 & W3 & W4).
    assert (HinM : In (p, Z_to_bv 64 nm) (vm_maps (m_vmmaps mdl))).
    { rewrite (mf_maps _ _ _ _ _ _ _ _ _ F). unfold dl. apply in_map_iff. exists (EVar vp, nm). split; [reflexivity | exact Hin]. }
    assert (Hmc : map_contains (vm_maps (m_vmmaps mdl)) lo nw = true).
    { unfold map_contains. apply existsb_exists. exists (p, Z_to_bv 64 nm). split; [exact HinM|].
      cbn [fst snd]. rewrite Ulo, Hun, (u_small nm) by (unfold stack_max_size in *; lia). apply andb_true_intro. split; apply Z.leb_le; lia. }
    assert (Hnc : map_contains (vm_noaccess (m_vmmaps mdl)) lo nw = true).
    { unfold map_contains. apply existsb_exists. exists (p, Z_to_bv 64 nm). split; [exact Hna|].
      cbn [fst snd]. rewrite Ulo, Hun, (u_small nm) by (unfold stack_max_size in *; lia). apply andb_true_intro. split; apply Z.leb_le; lia. }
    (* [comment removed for export] *)
    pose proof (mf_apart _ _ _ _ _ _ _ _ _ F) as APM0.
    assert (APM : ivs_apart (vm_maps (m_vmmaps mdl))) by (rewrite (mf_maps _ _ _ _ _ _ _ _ _ F); exact APM0).
    destruct (ivs_apart_split _ _ _ lo nw APM HinM
                ltac:(rewrite Ulo; lia) ltac:(rewrite Ulo, Hun, (u_small nm) by (unfold stack_max_size in *; lia); lia) ltac:(rewrite Hun; lia))
      as (l1 & l2 & EQM & Hrf12).
    pose proof (overlap_sum_one l1 (p, Z_to_bv 64 nm) l2 lo nw Hrf12) as OV. rewrite <- EQM, Hun in OV.
    (* [comment removed for export] *)
    destruct HM as [N1' N2' N3' N4' N5'].
    pose proof (allowed_pages_bound A (m_vm_materialized mdl) HAW N1' N2' N3') as PB. unfold page_size in PB.
    pose proof (mf_eager _ _ _ _ _ _ _ _ _ F) as EG. pose proof (mf_lim _ _ _ _ _ _ _ _ _ F) as LIM.
    assert (Hbud' : mprotect_budget_ok mdl lo nw = true).
    { apply (mprotect_budget_ok_intro_gen mdl lo nw WF). rewrite vm_backing_used_split, Hun, LIM. unfold page_size. lia. }
    eapply (srz_mprotect_lazy SEGS R (Z_to_bv 64 pc) M ROM mdl w lo n K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F) (G _ _ S17)).
    - rewrite (HR 10%bv). exact S10.
    - rewrite Ulo. unfold page_size. rewrite Z.add_mod, Mal, Heal by lia. reflexivity.
    - exact (G _ _ S11).
    - exact Hn.
    - rewrite Hpr, Ulo. unfold two_pow_64, stack_max_size in *. lia.
    - exact (G _ _ S12).
    - rewrite Hpr. exact Hnc.
    - rewrite Hpr. exact Hmc.
    - rewrite Hpr. exact Hbud'.
    - rewrite Hpr, pc_lit_add4 by lia. fold nw.
      set (mdl' := mprotect_model lo nw mdl).
      assert (HvisR : range_visible H lo n) by (intros x Hx; apply Hvis; rewrite Ulo in Hx; lia).
      apply (HK (regupd R 10%bv (Z_to_bv 64 0)) mdl'). constructor.
      + apply regs_ok_set; [exact HR | intros X; apply (f_equal bv_unsigned) in X; discriminate X | reflexivity].
      + (* [comment removed for export] *)
        fold nw. rewrite (mrestrict_zfill H lo nw M) by (rewrite Hun; exact HvisR).
        assert (KZ : kentry_ok SEGS (EB sp draw inp a tid c pl js) (zfill lo nw (mrestrict H M)) (KZero (SA (EVar vp) eo) (ELit n))).
        { rewrite <- Hun. apply kzero_zfill_off; [rewrite Ep, Ulo; reflexivity | rewrite Hun; lia | rewrite Ulo, Hun; unfold stack_max_size in *; lia]. }
        assert (KW : kentry_ok SEGS (EB sp draw inp a tid c pl js) (zfill lo nw (mrestrict H M)) (KWr (SA (EVar vp) eo) (ELit n))).
        { rewrite <- Hun. apply kwr_zfill_off; [rewrite Ep, Ulo; reflexivity | rewrite Hun; lia | rewrite Ulo, Hun; unfold stack_max_size in *; lia]. }
        unfold kn_mprotect. constructor; [exact KZ|]. constructor; [exact KW|].
        apply (kn_keep_sound SEGS _ (mrestrict H M) (zfill lo nw (mrestrict H M)) MGrow); [exact HKN | exact HKN|].
        unfold estart, elenZ. cbn [a_base a_off]. rewrite Ep. cbn [edenot]. fold nw. rewrite <- Ulo. apply mem_change_zfill.
      + intros x Hx. rewrite zfill_out; [apply HA; exact Hx|]. fold nw. rewrite Ulo, Hun. unfold stack_max_size in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *. apply Forall_forall. intros r Hr x Hx Hhx.
        rewrite zfill_out; [exact (proj1 (Forall_forall _ _) HZ r Hr x Hx Hhx)|]. fold nw. rewrite Hun.
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned lo)); [left; assumption|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned lo + n)); [|right; assumption].
        exfalso. rewrite (HvisR x ltac:(lia)) in Hhx. discriminate.
      + unfold mdl'. rewrite (mp_lazy lo nw mdl). exact HLZ.
      + unfold mdl'. apply (MInv_mp A lo nw mdl WF (mkMInv _ _ N1' N2' N3' N4' N5')). rewrite Hun, LIM. lia.
      + (* [comment removed for export] *)
        pose proof (model_ivs_wf_mp lo nw mdl WF) as WF'.
        pose proof (eager_used_mp_le lo nw mdl WF) as EGL. rewrite Hun in EGL.
        unfold mdl'. constructor; cbn [lcommit l_maps l_brk l_eager].
        * rewrite (mp_halted lo nw mdl). exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_reserved lo nw mdl). exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_init_sp lo nw mdl). exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_limit lo nw mdl). exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_start_brk lo nw mdl). exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_brk lo nw mdl). exact (mf_brk _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_mmap_base lo nw mdl). exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_maps lo nw mdl). exact (mf_maps _ _ _ _ _ _ _ _ _ F).
        * exact APM0.
        * lia.
        * rewrite (mp_fs lo nw mdl). exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_fds lo nw mdl). exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * rewrite (mp_tid lo nw mdl). exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * exact WF'.
        * (* [comment removed for export] *) unfold na_clear. rewrite (mp_noaccess lo nw mdl). apply na_clear_l_sub; [exact (proj1 (proj2 WF)) | exact (mf_na _ _ _ _ _ _ _ _ _ F)].
      + exact HMO.
      + (* [comment removed for export] *)
        constructor; cbn [lcommit l_maps]; try assumption; unfold mdl'; rewrite (mp_lazy lo nw mdl); assumption.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems10.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
