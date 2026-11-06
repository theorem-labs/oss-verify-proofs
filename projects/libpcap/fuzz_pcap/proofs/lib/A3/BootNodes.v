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
#[local] Instance bootnodes_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma eager_used_none_nr_le : forall (flags a n : word) m,
  model_ivs_wf m -> bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 -> 0 < bv_unsigned n ->
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  eager_used (with_mmap_backing flags a n (noaccess_model a n m)) <= eager_used m.
Proof.
  intros flags a n m Hwf Hal Hnl Hpos Hend.
  assert (Hwf' : model_ivs_wf (with_mmap_backing flags a n (noaccess_model a n m))).
  { apply model_ivs_wf_with_mmap_backing; [lia |]. unfold noaccess_model.
    pose proof Hwf as (W1 & W2 & W3 & W4).
    apply model_ivs_wf_with_vmmaps; cbn [vm_maps vm_noaccess vm_init_sp];
      [exact Hwf | apply ivs_wf_cons; [exact Hend | exact W1] | apply ivs_wf_cons; [exact Hend | exact W2] | reflexivity]. }
  rewrite (eager_used_sem _ Hwf'), (eager_used_sem _ Hwf).
  assert (EM : vm_maps (m_vmmaps (with_mmap_backing flags a n (noaccess_model a n m))) = (a, n) :: vm_maps (m_vmmaps m)).
  { unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. }
  assert (EN : vm_noaccess (m_vmmaps (with_mmap_backing flags a n (noaccess_model a n m))) = (a, n) :: vm_noaccess (m_vmmaps m)).
  { unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. }
  assert (EL : exists l, m_vm_lazy (with_mmap_backing flags a n (noaccess_model a n m)) = l ++ m_vm_lazy m).
  { unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [exists (lazy_interior a n) | exists []]; reflexivity. }
  destruct EL as (l & EL). rewrite EM, EN, EL. cbn [sum_count].
  set (C' := ((a, n) :: vm_noaccess (m_vmmaps m)) ++ l ++ m_vm_lazy m).
  assert (Z0 : iv_count (fun x => negb (covered C' x)) (a, n) = 0).
  { unfold iv_count, B, S. cbn [fst snd]. apply zcount_false. intros x Hx. rewrite Z2Nat.id in Hx by lia.
    apply negb_false_iff. unfold C', covered. cbn [existsb app]. unfold in_iv, in_rng, B, S. cbn [fst snd].
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Z0, Z.add_0_l.
  apply sum_count_negb_covered_mono. intros x Hx. unfold C'.
  unfold covered in *. rewrite existsb_app. cbn [existsb]. rewrite existsb_app.
  apply existsb_exists in Hx as (c & Hc & Hcx). apply in_app_iff in Hc as [Hc|Hc].
  - rewrite (proj2 (existsb_exists _ _) (ex_intro _ c (conj Hc Hcx))). cbn [orb]. rewrite orb_true_r. reflexivity.
  - rewrite (proj2 (existsb_exists _ (m_vm_lazy m)) (ex_intro _ c (conj Hc Hcx))). rewrite !orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hjoin (H : word -> bool) (p : word) (nZ : Z) : word -> bool :=
  fun x => H x || ((bv_unsigned p <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned p + nZ)).

Lemma hjoin_old : forall H p nZ x, H x = true -> hjoin H p nZ x = true.
Proof. intros H p nZ x Hx. unfold hjoin. rewrite Hx. reflexivity. Qed.
Lemma hjoin_new : forall H p nZ x, bv_unsigned p <= bv_unsigned x < bv_unsigned p + nZ -> hjoin H p nZ x = true.
Proof.
  intros H p nZ x Hx. unfold hjoin. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  apply orb_true_r.
Qed.
Lemma hjoin_false : forall H p nZ x, hjoin H p nZ x = false <-> H x = false /\ (bv_unsigned x < bv_unsigned p \/ bv_unsigned p + nZ <= bv_unsigned x).
Proof.
  intros H p nZ x. unfold hjoin. rewrite orb_false_iff, andb_false_iff, Z.leb_gt, Z.ltb_ge. tauto.
Qed.

(* [comment removed for export] *)
Definition lgrant_nr (L : ledger) (v : nat) (nZ : Z) : ledger :=
  Ledger ((EVar v, nZ) :: l_maps L) (l_brk L) (l_eager L).

(* [comment removed for export] *)

Section Theorems2.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let argv := in_argv inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).
  #[local] Notation mfacts' := (mfacts sp brk mbase lim inp).
  #[local] Notation maps_ok' := (maps_ok sp).
  Definition kn_grant_none (L : ledger) (v : nat) (nZ : Z) (kn : list kentry) : list kentry :=
    kn_grant_none_d (DS_std L) v nZ kn.

  Ltac vmp := unfold noaccess_model; rewrite m_vmmaps_with_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].

  #[using="VI VE argv usp"] Theorem bs_mmap_none_nr_spin : forall H A a tid c pl js sr kn L zr lz (len pc : Z) w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let nZ := page_round_up_Z len in
    bootS' H A a tid c pl js sr kn L zr lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> sivs_sizes_ok (l_maps L) = true ->
    sr_get sr 17%bv = ELit 222 -> sr_get sr 10%bv = ELit 0 -> sr_get sr 11%bv = ELit len -> sr_get sr 12%bv = ELit 0 ->
    sr_get sr 13%bv = ELit 16418 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len -> 0x10000 <= nZ ->
    IMG_HI + nZ + gws nZ (l_maps L) <= 0x7fff80000000 - stack_max_size ->
    (forall p R' M' mdl',
       bootS' (hjoin H p nZ) A a tid c pl (js ++ [p]) (sr_upd sr 10 (EVar v)) (kn_grant_none L v nZ kn) (lgrant_nr L v nZ)
              ((bv_unsigned p, bv_unsigned p + nZ, None) :: zr) ((p, Z_to_bv 64 nZ) :: lz) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L zr lz len pc w R M mdl K E v nZ HB HF HE Hpc0 Hpc4
           Hsr Hkn HL Hs S17 S10 S11 S12 S13 S14 S15 Hlen HnZ64K Hroom HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL' sp brk mbase draw inp VI VE) as SL. pose proof (SH' sp brk mbase draw inp VI VE) as SH.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (USP : usp = bv_unsigned sp) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
    assert (Hlen64 : len < 2 ^ 64).
    { unfold stack_max_size, IMG_HI in Hroom. pose proof (gap_weight_nonneg nZ (dl E (l_maps L)) ltac:(lia)) as W.
      rewrite (gap_weight_dl sp E nZ _ Hs) in W. lia. }
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    eapply (srz_mmap_none_pin_spin SEGS R (Z_to_bv 64 pc) M ROM mdl w len (Z_to_bv 64 16418) K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F)
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
      assert (Hev : edenot (EB' a tid c pl (js ++ [p])) (EVar v) = p).
      { rewrite EB_app. cbn [edenot ev]. unfold v. rewrite <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
      set (n := Z_to_bv 64 nZ) in *.
      assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in Htop; unfold usp in *; lia).
      assert (Himg : bv_unsigned p + nZ <= A_img_lo \/ A_img_hi <= bv_unsigned p).
      { rewrite (mf_res _ _ _ _ _ _ _ _ _ F), (mf_maps _ _ _ _ _ _ _ _ _ F), region_free_app in Hrf. apply andb_prop in Hrf as [Hrf _].
        apply (reserved_apart p nZ); [lia | unfold stack_max_size, usp in *; lia | exact Hrf]. }
      assert (Habove : A_img_hi <= bv_unsigned p) by (pose proof img_hull; unfold A_img_lo in *; lia).
      pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as (W1 & W2 & W3 & W4).
      assert (Hli : lazy_interior p n = [(p, n)]).
      { apply lazy_interior_aligned; rewrite ?Hun; [exact Hal | | lia | unfold stack_max_size, usp in *; lia].
        unfold nZ, page_round_up_Z, page_size. apply Z_mod_mult. }
      pose proof HL as HL0. pose proof HL as HL1. unfold ledger_vars_lt in HL1.
      apply (HK p). constructor.
      + (* [comment removed for export] *)
        apply regs_ok_set; [| intros X; apply (f_equal bv_unsigned) in X; discriminate X | exact Hev].
        rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
      + (* [comment removed for export] *)
        assert (EQM : mrestrict (hjoin H p nZ) (unfill p n M) = unfill p n (mrestrict H M)).
        { extensionality x. rewrite <- mrestrict_unfill. unfold mrestrict, hjoin.
          destruct (H x); [reflexivity|]. cbn [orb].
          destruct (Z.leb_spec (bv_unsigned p) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned p + nZ)); cbn [andb]; try reflexivity.
          unfold unfill. rewrite Hun. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
        rewrite EQM.
        assert (KO' : know_ok SEGS (EB' a tid c pl (js ++ [p])) (mrestrict H M) kn).
        { rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN]. }
        assert (KF : forall V, know_ok SEGS (EB' a tid c pl (js ++ [p])) V (GF_none v nZ)).
        { intros V. rewrite EB_app. unfold v, GF_none. apply kfacts_grant; try assumption; unfold stack_max_size, usp in *; lia. }
        assert (KD : forall V, know_ok SEGS (EB' a tid c pl (js ++ [p])) V (dsj_entries v nZ (DS_std L))).
        { intros V. rewrite EB_app. unfold v.
          apply (dsj_entries_ok SEGS (VB' a tid c pl js) (blobs0 draw argv) V _ nZ (DS_std L) p ltac:(lia)
                   ltac:(unfold stack_max_size, usp in *; lia) (DS_std_claims sp brk mbase draw lim inp VI VE E tid L mdl nZ F Hshd (ev_EB_sp sp draw inp a tid c pl js) Hs ltac:(lia)) Hp).
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
        intros x Hx. rewrite unfill_out; [apply HA; exact Hx|]. rewrite Hun. unfold stack_max_size, usp in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *. constructor.
        { cbn [fst snd]. intros x Hx _. unfold unfill. rewrite Hun. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
        apply Forall_forall. intros r Hr x Hx Hhx.
        assert (Hout : bv_unsigned x < bv_unsigned p \/ bv_unsigned p + bv_unsigned n <= bv_unsigned x).
        { rewrite Hun. destruct (proj1 (Forall_forall _ _) Hhin r Hr) as ([qe qn] & Hq & Q1 & Q2). cbn [fst snd] in Q1, Q2.
          pose proof Hrf as Hrf'. rewrite (mf_res _ _ _ _ _ _ _ _ _ F), (mf_maps _ _ _ _ _ _ _ _ _ F), region_free_app in Hrf'.
          apply andb_prop in Hrf' as [_ Hrf'].
          pose proof (region_free_In _ p n (edenot E qe) (Z_to_bv 64 qn) Hrf'
                        ltac:(unfold dl; apply in_map_iff; exists (qe, qn); split; [reflexivity | exact Hq])) as Hap.
          pose proof (proj1 (forallb_forall _ _) Hs _ Hq) as Hqn. cbn [snd] in Hqn. apply andb_prop in Hqn as [N0 N1].
          apply Z.leb_le in N0. apply Z.ltb_lt in N1. rewrite Hun, (u_small qn) in Hap by lia. unfold E in Hap. lia. }
        rewrite unfill_out by exact Hout.
        apply (proj1 (Forall_forall _ _) HZ r Hr x Hx). unfold hjoin in Hhx. rewrite Hun in Hout.
        apply orb_prop in Hhx as [Hhx|Hhx]; [exact Hhx|]. exfalso.
        apply andb_prop in Hhx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
      + (* [comment removed for export] *)
        change (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) with (vm_add_lazy p n (noaccess_model p n mdl)).
        rewrite m_vm_lazy_vm_add_lazy, Hli. unfold noaccess_model. rewrite m_vm_lazy_with_vmmaps, HLZ. reflexivity.
      + (* [comment removed for export] *)
        destruct HM as [N1 N2 N3 N4 N5].
        assert (EMAT : m_vm_materialized (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) = m_vm_materialized mdl) by reflexivity.
        assert (ELZ : m_vm_lazy (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) = (p, n) :: m_vm_lazy mdl).
        { change (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) with (vm_add_lazy p n (noaccess_model p n mdl)).
          rewrite m_vm_lazy_vm_add_lazy, Hli. reflexivity. }
        constructor; rewrite ?EMAT, ?ELZ.
        * exact N1.
        * exact N2.
        * exact N3.
        * intros q Hq. unfold page_in_ranges in *. cbn [existsb]. rewrite (N4 q Hq). apply orb_true_r.
        * pose proof (eager_used_none_nr_le (Z_to_bv 64 16418) p n mdl (mf_wf _ _ _ _ _ _ _ _ _ F) Hal
                        ltac:(rewrite Hun; unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult)
                        ltac:(rewrite Hun; lia) ltac:(rewrite Hun; unfold stack_max_size, usp in *; lia)) as HEA.
          replace (vm_limit (m_vmmaps (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)))) with (vm_limit (m_vmmaps mdl)) by reflexivity.
          lia.
      + (* [comment removed for export] *)
        assert (EVM : m_vmmaps (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) = m_vmmaps (noaccess_model p n mdl)) by reflexivity.
        constructor; rewrite ?EVM.
        * exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * vmp. exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * vmp. exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * vmp. exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * vmp. exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
        * vmp. cbn [lgrant_nr l_brk]. exact (mf_brk _ _ _ _ _ _ _ _ _ F).
        * vmp. exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * vmp. cbn [lgrant_nr l_maps dl List.map fst snd]. rewrite Hev, (mf_maps _ _ _ _ _ _ _ _ _ F). fold (dl (EB' a tid c pl (js ++ [p])) (l_maps L)).
          rewrite EB_app. unfold E, EB. rewrite (dl_app_env _ [p] _ _ HL1). reflexivity.
        * (* [comment removed for export] *)
          cbn [lgrant_nr l_maps ivs_apart dl List.map fst snd]. fold (dl (EB' a tid c pl (js ++ [p])) (l_maps L)). rewrite Hev.
          rewrite EB_app. unfold E, EB in F |- *. rewrite (dl_app_env _ [p] _ _ HL1). rewrite <- (mf_maps _ _ _ _ _ _ _ _ _ F).
          pose proof Hrf as Hrf0. rewrite region_free_app in Hrf0. apply andb_prop in Hrf0 as [_ Hrf2].
          split; [| rewrite (mf_maps _ _ _ _ _ _ _ _ _ F); exact (mf_apart _ _ _ _ _ _ _ _ _ F)].
          apply Forall_forall. intros [qb qn] Hq. cbn [fst snd].
          pose proof (region_free_In _ p n qb qn Hrf2 Hq) as Hov. rewrite Hun in Hov. fold n. rewrite Hun. lia.
        * cbn [lgrant_nr l_eager].
          pose proof (eager_used_none_nr_le (Z_to_bv 64 16418) p n mdl (mf_wf _ _ _ _ _ _ _ _ _ F) Hal
                        ltac:(rewrite Hun; unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult)
                        ltac:(rewrite Hun; lia) ltac:(rewrite Hun; unfold stack_max_size, usp in *; lia)) as HEA.
          pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
        * exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * apply model_ivs_wf_with_mmap_backing; [rewrite Hun; unfold stack_max_size, usp in *; lia|].
          apply model_ivs_wf_with_vmmaps; cbn [vm_maps vm_noaccess vm_init_sp];
            [exact (mf_wf _ _ _ _ _ _ _ _ _ F) | apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hun; lia | exact W1]
            | apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hun; lia | exact W2] | reflexivity].
        * (* [comment removed for export] *)
          unfold na_clear. rewrite EVM. vmp. apply na_clear_l_cons; [| exact (mf_na _ _ _ _ _ _ _ _ _ F)]. rewrite Hun.
          exact (grant_misses_shadow sp brk mbase draw lim inp VI VE E tid L mdl p nZ F Hshd (ev_EB_sp sp draw inp a tid c pl js) Hs ltac:(lia) Hp).
      + (* [comment removed for export] *)
        unfold maps_ok, lgrant_nr. cbn [l_maps]. constructor.
        * unfold map_ok. cbn [fst snd]. rewrite Hev. unfold stack_max_size, page_size in *.
          split; [exact Hal|]. split; [|split; [lia | split; [lia | exact Himg]]].
          pose proof (Z.mod_pos_bound (bv_unsigned p) 4096 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). nia.
        * exact (maps_ok_env sp draw inp a tid c pl js [p] L HL0 HMO).
      + (* [comment removed for export] *)
        pose proof (regime_ok_env sp draw inp H A zr a tid c pl js [p] L mdl HL0 RG) as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8].
        constructor.
        * intros x Hx. unfold hjoin in Hx. apply orb_prop in Hx as [Hx|Hx]; [exact (HH x Hx)|].
          apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          apply (H_off_segments_above SEGS (fun y : word => IMG_HI <=? bv_unsigned y) IMG_HI segs_below
                   ltac:(intros y Hy; apply Z.leb_le in Hy; exact Hy)).
          apply Z.leb_le. pose proof img_hull. unfold IMG_HI, A_img_hi in *. lia.
        * exact HAW.
        * intros x Hpx Hhx. apply hjoin_false in Hhx as [Hhx Hout]. apply (Q3 x); [| exact Hhx].
          change (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) with (vm_add_lazy p n (noaccess_model p n mdl)) in Hpx.
          rewrite m_vm_lazy_vm_add_lazy, Hli in Hpx. unfold noaccess_model in Hpx. rewrite m_vm_lazy_with_vmmaps in Hpx.
          change ([(p, n)] ++ m_vm_lazy mdl) with ((p, n) :: m_vm_lazy mdl) in Hpx.
          rewrite page_in_ranges_cons in Hpx. cbn [fst snd] in Hpx.
          rewrite Hun in Hpx. apply orb_prop in Hpx as [Hpx|Hpx]; [| exact Hpx]. exfalso.
          apply andb_prop in Hpx as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
          pose proof (u64_range x) as Xr. unfold page_base, page_base_of, page_size in X1, X2.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small in X1, X2 by lia.
          unfold page_size in Hal. pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). nia.
        * intros x Hx. unfold hjoin in Hx. apply orb_prop in Hx as [Hx|Hx].
          -- destruct (Q4 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
          -- apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
             exists (EVar v, nZ). split; [unfold lgrant_nr; cbn [l_maps]; left; reflexivity|]. cbn [fst snd]. rewrite Hev. lia.
        * (* [comment removed for export] *)
          unfold hf_inmaps. constructor.
          -- exists (EVar v, nZ). split; [unfold lgrant_nr; cbn [l_maps]; left; reflexivity|]. cbn [fst snd]. rewrite Hev. lia.
          -- unfold hf_inmaps in Q5. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) Q5 r Hr0) as (q & Hq & Hr).
             exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
        * intros x Hx. apply (proj2 (hjoin_false H p nZ x)). split; [exact (Habv x Hx)|]. unfold stack_max_size, usp in *. lia.
        * (* [comment removed for export] *)
          intros x Hx. change (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) with (vm_add_lazy p n (noaccess_model p n mdl)).
          rewrite m_vm_lazy_vm_add_lazy, Hli. unfold noaccess_model. rewrite m_vm_lazy_with_vmmaps.
          change ([(p, n)] ++ m_vm_lazy mdl) with ((p, n) :: m_vm_lazy mdl). rewrite page_in_ranges_cons. cbn [fst snd].
          unfold hjoin in Hx. apply orb_prop in Hx as [Hx|Hx]; [rewrite (Q7 x Hx); apply orb_true_r|].
          apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          apply orb_true_intro. left. rewrite Hun. pose proof (u64_range x) as Xr.
          unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small by lia. unfold page_size in Hal. pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)).
          assert (nZ mod 4096 = 0) by (unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult).
          pose proof (Z.div_mod nZ 4096 ltac:(lia)).
          apply andb_true_intro; split; apply Z.leb_le; nia.
        * intros x Hx. destruct (Q8 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Theorems3.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  #[using="Type"] Theorem bs_fresh : forall H A a tid c pl js sr kn L hc lz R M mdl (r : reg) (w : word) (kf : list kentry),
    let v := length (VB' a tid c pl js) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    getr R r = w ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true ->
    know_ok SEGS (EB' a tid c pl (js ++ [w])) (mrestrict H M) kf ->
    bootS' H A a tid c pl (js ++ [w]) (sr_upd sr (ridx r) (EVar v)) (kf ++ kn) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl r w kf v HB Hw Hsr Hkn HL HKF.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (Hev : edenot (EB' a tid c pl (js ++ [w])) (EVar v) = w).
    { rewrite EB_app. cbn [edenot ev]. unfold v. rewrite <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
    constructor; try assumption.
    - apply regs_ok_pin; [| rewrite Hev; exact Hw]. rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
    - apply (proj2 (know_ok_app SEGS _ _ _ _)). split; [exact HKF|]. rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN].
    - apply mfacts_env; assumption.
    - apply maps_ok_env; assumption.
    - apply regime_ok_env; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma dsj_entries_sub : forall a tid c pl js (ia : nat) (nZ n1 : Z) ds (w : word) V,
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    know_ok SEGS E V (dsj_entries ia nZ ds) ->
    Forall (fun d => saddr_vars_lt v (fst d) = true /\ expr_vars_lt v (snd d) = true) ds ->
    0 <= n1 -> 0 <= nZ -> bv_unsigned (ev E ia) + nZ < 2 ^ 64 ->
    bv_unsigned (ev E ia) <= bv_unsigned w -> bv_unsigned w + n1 <= bv_unsigned (ev E ia) + nZ ->
    know_ok SEGS (EB' a tid c pl (js ++ [w])) V (dsj_entries v n1 ds).
  Proof.
    intros a tid c pl js ia nZ n1 ds w V E v HK Hlt Hn1 HnZ Hnw Hlo Hhi.
    rewrite EB_app. unfold v.
    apply (dsj_entries_ok SEGS (VB' a tid c pl js) (blobs0 draw (in_argv inp)) V (fun q => q = w) n1 ds w Hn1).
    - lia.
    - unfold dsj_claims. unfold dsj_entries in HK. apply Forall_forall. intros d Hd q Hq. subst q.
      pose proof (proj1 (Forall_forall _ _) HK (KDisj (SA (EVar ia) 0) (ELit nZ) (fst d) (snd d))
                    ltac:(apply in_map_iff; exists d; split; [reflexivity | exact Hd])) as HKd.
      cbn [kentry_ok] in HKd. unfold estart, elenZ in HKd |- *. cbn [a_base a_off edenot] in HKd |- *.
      fold E in HKd. change ({| ev := vals_ev (VB' a tid c pl js); eb := blobs0 draw (in_argv inp) |}) with E.
      pose proof (u64_range (ev E ia)). rewrite (u_small nZ) in HKd by lia.
      destruct HKd as [HKd|HKd]; [left; lia | right; lia].
    - reflexivity.
    - exact Hlt.
  Qed.
End Theorems3.

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
#[local] Instance bootnodes_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma eager_used_none_nr_le : forall (flags a n : word) m,
  model_ivs_wf m -> bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 -> 0 < bv_unsigned n ->
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  eager_used (with_mmap_backing flags a n (noaccess_model a n m)) <= eager_used m.
Proof.
  intros flags a n m Hwf Hal Hnl Hpos Hend.
  assert (Hwf' : model_ivs_wf (with_mmap_backing flags a n (noaccess_model a n m))).
  { apply model_ivs_wf_with_mmap_backing; [lia |]. unfold noaccess_model.
    pose proof Hwf as (W1 & W2 & W3 & W4).
    apply model_ivs_wf_with_vmmaps; cbn [vm_maps vm_noaccess vm_init_sp];
      [exact Hwf | apply ivs_wf_cons; [exact Hend | exact W1] | apply ivs_wf_cons; [exact Hend | exact W2] | reflexivity]. }
  rewrite (eager_used_sem _ Hwf'), (eager_used_sem _ Hwf).
  assert (EM : vm_maps (m_vmmaps (with_mmap_backing flags a n (noaccess_model a n m))) = (a, n) :: vm_maps (m_vmmaps m)).
  { unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. }
  assert (EN : vm_noaccess (m_vmmaps (with_mmap_backing flags a n (noaccess_model a n m))) = (a, n) :: vm_noaccess (m_vmmaps m)).
  { unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. }
  assert (EL : exists l, m_vm_lazy (with_mmap_backing flags a n (noaccess_model a n m)) = l ++ m_vm_lazy m).
  { unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [exists (lazy_interior a n) | exists []]; reflexivity. }
  destruct EL as (l & EL). rewrite EM, EN, EL. cbn [sum_count].
  set (C' := ((a, n) :: vm_noaccess (m_vmmaps m)) ++ l ++ m_vm_lazy m).
  assert (Z0 : iv_count (fun x => negb (covered C' x)) (a, n) = 0).
  { unfold iv_count, B, S. cbn [fst snd]. apply zcount_false. intros x Hx. rewrite Z2Nat.id in Hx by lia.
    apply negb_false_iff. unfold C', covered. cbn [existsb app]. unfold in_iv, in_rng, B, S. cbn [fst snd].
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Z0, Z.add_0_l.
  apply sum_count_negb_covered_mono. intros x Hx. unfold C'.
  unfold covered in *. rewrite existsb_app. cbn [existsb]. rewrite existsb_app.
  apply existsb_exists in Hx as (c & Hc & Hcx). apply in_app_iff in Hc as [Hc|Hc].
  - rewrite (proj2 (existsb_exists _ _) (ex_intro _ c (conj Hc Hcx))). cbn [orb]. rewrite orb_true_r. reflexivity.
  - rewrite (proj2 (existsb_exists _ (m_vm_lazy m)) (ex_intro _ c (conj Hc Hcx))). rewrite !orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hjoin (H : word -> bool) (p : word) (nZ : Z) : word -> bool :=
  fun x => H x || ((bv_unsigned p <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned p + nZ)).

Lemma hjoin_old : forall H p nZ x, H x = true -> hjoin H p nZ x = true.
Proof. intros H p nZ x Hx. unfold hjoin. rewrite Hx. reflexivity. Qed.
Lemma hjoin_new : forall H p nZ x, bv_unsigned p <= bv_unsigned x < bv_unsigned p + nZ -> hjoin H p nZ x = true.
Proof.
  intros H p nZ x Hx. unfold hjoin. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  apply orb_true_r.
Qed.
Lemma hjoin_false : forall H p nZ x, hjoin H p nZ x = false <-> H x = false /\ (bv_unsigned x < bv_unsigned p \/ bv_unsigned p + nZ <= bv_unsigned x).
Proof.
  intros H p nZ x. unfold hjoin. rewrite orb_false_iff, andb_false_iff, Z.leb_gt, Z.ltb_ge. tauto.
Qed.

(* [comment removed for export] *)
Definition lgrant_nr (L : ledger) (v : nat) (nZ : Z) : ledger :=
  Ledger ((EVar v, nZ) :: l_maps L) (l_brk L) (l_eager L).

(* [comment removed for export] *)

Section Theorems2.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  Let argv := in_argv inp.
  Let usp := bv_unsigned sp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).
  #[local] Notation mfacts' := (mfacts sp brk mbase lim inp).
  #[local] Notation maps_ok' := (maps_ok sp).
  Definition kn_grant_none (L : ledger) (v : nat) (nZ : Z) (kn : list kentry) : list kentry :=
    kn_grant_none_d (DS_std L) v nZ kn.

  Ltac vmp := unfold noaccess_model; rewrite m_vmmaps_with_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].

  #[using="VI VE argv usp"] Theorem bs_mmap_none_nr_spin : forall H A a tid c pl js sr kn L zr lz (len pc : Z) w R M mdl (K : TSet),
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    let nZ := page_round_up_Z len in
    bootS' H A a tid c pl js sr kn L zr lz R M mdl ->
    fetch_word SEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true -> sivs_sizes_ok (l_maps L) = true ->
    sr_get sr 17%bv = ELit 222 -> sr_get sr 10%bv = ELit 0 -> sr_get sr 11%bv = ELit len -> sr_get sr 12%bv = ELit 0 ->
    sr_get sr 13%bv = ELit 16418 -> sr_get sr 14%bv = ELit (2 ^ 64 - 1) -> sr_get sr 15%bv = ELit 0 ->
    0 < len -> 0x10000 <= nZ ->
    IMG_HI + nZ + gws nZ (l_maps L) <= 0x7fff80000000 - stack_max_size ->
    (forall p R' M' mdl',
       bootS' (hjoin H p nZ) A a tid c pl (js ++ [p]) (sr_upd sr 10 (EVar v)) (kn_grant_none L v nZ kn) (lgrant_nr L v nZ)
              ((bv_unsigned p, bv_unsigned p + nZ, None) :: zr) ((p, Z_to_bv 64 nZ) :: lz) R' M' mdl' ->
       srealizes SEGS (mkCfg (mkst R' (Z_to_bv 64 (pc + 4)) M' ROM) mdl') K) ->
    srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 pc) M ROM) mdl) K.
  Proof.
    intros H A a tid c pl js sr kn L zr lz len pc w R M mdl K E v nZ HB HF HE Hpc0 Hpc4
           Hsr Hkn HL Hs S17 S10 S11 S12 S13 S14 S15 Hlen HnZ64K Hroom HK.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht]. pose proof RG as [HH HAW HCOV HIN Hhin Habv Hhl Hshd].
    pose proof (SL' sp brk mbase draw inp VI VE) as SL. pose proof (SH' sp brk mbase draw inp VI VE) as SH.
    assert (SMS : stack_max_size = 8388608) by reflexivity.
    assert (USP : usp = bv_unsigned sp) by reflexivity.
    assert (HnZ : len <= nZ /\ nZ < len + 4096) by (unfold nZ; pose proof (page_round_up_Z_bounds len ltac:(lia)); unfold page_size in *; lia).
    assert (Hlen64 : len < 2 ^ 64).
    { unfold stack_max_size, IMG_HI in Hroom. pose proof (gap_weight_nonneg nZ (dl E (l_maps L)) ltac:(lia)) as W.
      rewrite (gap_weight_dl sp E nZ _ Hs) in W. lia. }
    assert (G : forall r z, sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z).
    { intros r z Hz. rewrite (HR r), Hz. reflexivity. }
    eapply (srz_mmap_none_pin_spin SEGS R (Z_to_bv 64 pc) M ROM mdl w len (Z_to_bv 64 16418) K HF HE (mf_halted _ _ _ _ _ _ _ _ _ F)
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
      assert (Hev : edenot (EB' a tid c pl (js ++ [p])) (EVar v) = p).
      { rewrite EB_app. cbn [edenot ev]. unfold v. rewrite <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
      set (n := Z_to_bv 64 nZ) in *.
      assert (Hun : bv_unsigned n = nZ) by (unfold n; apply u_small; unfold stack_max_size in Htop; unfold usp in *; lia).
      assert (Himg : bv_unsigned p + nZ <= A_img_lo \/ A_img_hi <= bv_unsigned p).
      { rewrite (mf_res _ _ _ _ _ _ _ _ _ F), (mf_maps _ _ _ _ _ _ _ _ _ F), region_free_app in Hrf. apply andb_prop in Hrf as [Hrf _].
        apply (reserved_apart p nZ); [lia | unfold stack_max_size, usp in *; lia | exact Hrf]. }
      assert (Habove : A_img_hi <= bv_unsigned p) by (pose proof img_hull; unfold A_img_lo in *; lia).
      pose proof (mf_wf _ _ _ _ _ _ _ _ _ F) as (W1 & W2 & W3 & W4).
      assert (Hli : lazy_interior p n = [(p, n)]).
      { apply lazy_interior_aligned; rewrite ?Hun; [exact Hal | | lia | unfold stack_max_size, usp in *; lia].
        unfold nZ, page_round_up_Z, page_size. apply Z_mod_mult. }
      pose proof HL as HL0. pose proof HL as HL1. unfold ledger_vars_lt in HL1.
      apply (HK p). constructor.
      + (* [comment removed for export] *)
        apply regs_ok_set; [| intros X; apply (f_equal bv_unsigned) in X; discriminate X | exact Hev].
        rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
      + (* [comment removed for export] *)
        assert (EQM : mrestrict (hjoin H p nZ) (unfill p n M) = unfill p n (mrestrict H M)).
        { extensionality x. rewrite <- mrestrict_unfill. unfold mrestrict, hjoin.
          destruct (H x); [reflexivity|]. cbn [orb].
          destruct (Z.leb_spec (bv_unsigned p) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned p + nZ)); cbn [andb]; try reflexivity.
          unfold unfill. rewrite Hun. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
        rewrite EQM.
        assert (KO' : know_ok SEGS (EB' a tid c pl (js ++ [p])) (mrestrict H M) kn).
        { rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN]. }
        assert (KF : forall V, know_ok SEGS (EB' a tid c pl (js ++ [p])) V (GF_none v nZ)).
        { intros V. rewrite EB_app. unfold v, GF_none. apply kfacts_grant; try assumption; unfold stack_max_size, usp in *; lia. }
        assert (KD : forall V, know_ok SEGS (EB' a tid c pl (js ++ [p])) V (dsj_entries v nZ (DS_std L))).
        { intros V. rewrite EB_app. unfold v.
          apply (dsj_entries_ok SEGS (VB' a tid c pl js) (blobs0 draw argv) V _ nZ (DS_std L) p ltac:(lia)
                   ltac:(unfold stack_max_size, usp in *; lia) (DS_std_claims sp brk mbase draw lim inp VI VE E tid L mdl nZ F Hshd (ev_EB_sp sp draw inp a tid c pl js) Hs ltac:(lia)) Hp).
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
        intros x Hx. rewrite unfill_out; [apply HA; exact Hx|]. rewrite Hun. unfold stack_max_size, usp in *. lia.
      + (* [comment removed for export] *)
        unfold hf_ok in HZ |- *. constructor.
        { cbn [fst snd]. intros x Hx _. unfold unfill. rewrite Hun. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
        apply Forall_forall. intros r Hr x Hx Hhx.
        assert (Hout : bv_unsigned x < bv_unsigned p \/ bv_unsigned p + bv_unsigned n <= bv_unsigned x).
        { rewrite Hun. destruct (proj1 (Forall_forall _ _) Hhin r Hr) as ([qe qn] & Hq & Q1 & Q2). cbn [fst snd] in Q1, Q2.
          pose proof Hrf as Hrf'. rewrite (mf_res _ _ _ _ _ _ _ _ _ F), (mf_maps _ _ _ _ _ _ _ _ _ F), region_free_app in Hrf'.
          apply andb_prop in Hrf' as [_ Hrf'].
          pose proof (region_free_In _ p n (edenot E qe) (Z_to_bv 64 qn) Hrf'
                        ltac:(unfold dl; apply in_map_iff; exists (qe, qn); split; [reflexivity | exact Hq])) as Hap.
          pose proof (proj1 (forallb_forall _ _) Hs _ Hq) as Hqn. cbn [snd] in Hqn. apply andb_prop in Hqn as [N0 N1].
          apply Z.leb_le in N0. apply Z.ltb_lt in N1. rewrite Hun, (u_small qn) in Hap by lia. unfold E in Hap. lia. }
        rewrite unfill_out by exact Hout.
        apply (proj1 (Forall_forall _ _) HZ r Hr x Hx). unfold hjoin in Hhx. rewrite Hun in Hout.
        apply orb_prop in Hhx as [Hhx|Hhx]; [exact Hhx|]. exfalso.
        apply andb_prop in Hhx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
      + (* [comment removed for export] *)
        change (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) with (vm_add_lazy p n (noaccess_model p n mdl)).
        rewrite m_vm_lazy_vm_add_lazy, Hli. unfold noaccess_model. rewrite m_vm_lazy_with_vmmaps, HLZ. reflexivity.
      + (* [comment removed for export] *)
        destruct HM as [N1 N2 N3 N4 N5].
        assert (EMAT : m_vm_materialized (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) = m_vm_materialized mdl) by reflexivity.
        assert (ELZ : m_vm_lazy (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) = (p, n) :: m_vm_lazy mdl).
        { change (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) with (vm_add_lazy p n (noaccess_model p n mdl)).
          rewrite m_vm_lazy_vm_add_lazy, Hli. reflexivity. }
        constructor; rewrite ?EMAT, ?ELZ.
        * exact N1.
        * exact N2.
        * exact N3.
        * intros q Hq. unfold page_in_ranges in *. cbn [existsb]. rewrite (N4 q Hq). apply orb_true_r.
        * pose proof (eager_used_none_nr_le (Z_to_bv 64 16418) p n mdl (mf_wf _ _ _ _ _ _ _ _ _ F) Hal
                        ltac:(rewrite Hun; unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult)
                        ltac:(rewrite Hun; lia) ltac:(rewrite Hun; unfold stack_max_size, usp in *; lia)) as HEA.
          replace (vm_limit (m_vmmaps (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)))) with (vm_limit (m_vmmaps mdl)) by reflexivity.
          lia.
      + (* [comment removed for export] *)
        assert (EVM : m_vmmaps (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) = m_vmmaps (noaccess_model p n mdl)) by reflexivity.
        constructor; rewrite ?EVM.
        * exact (mf_halted _ _ _ _ _ _ _ _ _ F).
        * vmp. exact (mf_res _ _ _ _ _ _ _ _ _ F).
        * vmp. exact (mf_isp _ _ _ _ _ _ _ _ _ F).
        * vmp. exact (mf_lim _ _ _ _ _ _ _ _ _ F).
        * vmp. exact (mf_sbrk _ _ _ _ _ _ _ _ _ F).
        * vmp. cbn [lgrant_nr l_brk]. exact (mf_brk _ _ _ _ _ _ _ _ _ F).
        * vmp. exact (mf_mb _ _ _ _ _ _ _ _ _ F).
        * vmp. cbn [lgrant_nr l_maps dl List.map fst snd]. rewrite Hev, (mf_maps _ _ _ _ _ _ _ _ _ F). fold (dl (EB' a tid c pl (js ++ [p])) (l_maps L)).
          rewrite EB_app. unfold E, EB. rewrite (dl_app_env _ [p] _ _ HL1). reflexivity.
        * (* [comment removed for export] *)
          cbn [lgrant_nr l_maps ivs_apart dl List.map fst snd]. fold (dl (EB' a tid c pl (js ++ [p])) (l_maps L)). rewrite Hev.
          rewrite EB_app. unfold E, EB in F |- *. rewrite (dl_app_env _ [p] _ _ HL1). rewrite <- (mf_maps _ _ _ _ _ _ _ _ _ F).
          pose proof Hrf as Hrf0. rewrite region_free_app in Hrf0. apply andb_prop in Hrf0 as [_ Hrf2].
          split; [| rewrite (mf_maps _ _ _ _ _ _ _ _ _ F); exact (mf_apart _ _ _ _ _ _ _ _ _ F)].
          apply Forall_forall. intros [qb qn] Hq. cbn [fst snd].
          pose proof (region_free_In _ p n qb qn Hrf2 Hq) as Hov. rewrite Hun in Hov. fold n. rewrite Hun. lia.
        * cbn [lgrant_nr l_eager].
          pose proof (eager_used_none_nr_le (Z_to_bv 64 16418) p n mdl (mf_wf _ _ _ _ _ _ _ _ _ F) Hal
                        ltac:(rewrite Hun; unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult)
                        ltac:(rewrite Hun; lia) ltac:(rewrite Hun; unfold stack_max_size, usp in *; lia)) as HEA.
          pose proof (mf_eager _ _ _ _ _ _ _ _ _ F). lia.
        * exact (mf_fs _ _ _ _ _ _ _ _ _ F).
        * exact (mf_fds _ _ _ _ _ _ _ _ _ F).
        * exact (mf_tid _ _ _ _ _ _ _ _ _ F).
        * apply model_ivs_wf_with_mmap_backing; [rewrite Hun; unfold stack_max_size, usp in *; lia|].
          apply model_ivs_wf_with_vmmaps; cbn [vm_maps vm_noaccess vm_init_sp];
            [exact (mf_wf _ _ _ _ _ _ _ _ _ F) | apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hun; lia | exact W1]
            | apply ivs_wf_cons; [apply iv_wf_intro; rewrite Hun; lia | exact W2] | reflexivity].
        * (* [comment removed for export] *)
          unfold na_clear. rewrite EVM. vmp. apply na_clear_l_cons; [| exact (mf_na _ _ _ _ _ _ _ _ _ F)]. rewrite Hun.
          exact (grant_misses_shadow sp brk mbase draw lim inp VI VE E tid L mdl p nZ F Hshd (ev_EB_sp sp draw inp a tid c pl js) Hs ltac:(lia) Hp).
      + (* [comment removed for export] *)
        unfold maps_ok, lgrant_nr. cbn [l_maps]. constructor.
        * unfold map_ok. cbn [fst snd]. rewrite Hev. unfold stack_max_size, page_size in *.
          split; [exact Hal|]. split; [|split; [lia | split; [lia | exact Himg]]].
          pose proof (Z.mod_pos_bound (bv_unsigned p) 4096 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). nia.
        * exact (maps_ok_env sp draw inp a tid c pl js [p] L HL0 HMO).
      + (* [comment removed for export] *)
        pose proof (regime_ok_env sp draw inp H A zr a tid c pl js [p] L mdl HL0 RG) as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8].
        constructor.
        * intros x Hx. unfold hjoin in Hx. apply orb_prop in Hx as [Hx|Hx]; [exact (HH x Hx)|].
          apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          apply (H_off_segments_above SEGS (fun y : word => IMG_HI <=? bv_unsigned y) IMG_HI segs_below
                   ltac:(intros y Hy; apply Z.leb_le in Hy; exact Hy)).
          apply Z.leb_le. pose proof img_hull. unfold IMG_HI, A_img_hi in *. lia.
        * exact HAW.
        * intros x Hpx Hhx. apply hjoin_false in Hhx as [Hhx Hout]. apply (Q3 x); [| exact Hhx].
          change (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) with (vm_add_lazy p n (noaccess_model p n mdl)) in Hpx.
          rewrite m_vm_lazy_vm_add_lazy, Hli in Hpx. unfold noaccess_model in Hpx. rewrite m_vm_lazy_with_vmmaps in Hpx.
          change ([(p, n)] ++ m_vm_lazy mdl) with ((p, n) :: m_vm_lazy mdl) in Hpx.
          rewrite page_in_ranges_cons in Hpx. cbn [fst snd] in Hpx.
          rewrite Hun in Hpx. apply orb_prop in Hpx as [Hpx|Hpx]; [| exact Hpx]. exfalso.
          apply andb_prop in Hpx as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
          pose proof (u64_range x) as Xr. unfold page_base, page_base_of, page_size in X1, X2.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small in X1, X2 by lia.
          unfold page_size in Hal. pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). nia.
        * intros x Hx. unfold hjoin in Hx. apply orb_prop in Hx as [Hx|Hx].
          -- destruct (Q4 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
          -- apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
             exists (EVar v, nZ). split; [unfold lgrant_nr; cbn [l_maps]; left; reflexivity|]. cbn [fst snd]. rewrite Hev. lia.
        * (* [comment removed for export] *)
          unfold hf_inmaps. constructor.
          -- exists (EVar v, nZ). split; [unfold lgrant_nr; cbn [l_maps]; left; reflexivity|]. cbn [fst snd]. rewrite Hev. lia.
          -- unfold hf_inmaps in Q5. apply Forall_forall. intros r Hr0. destruct (proj1 (Forall_forall _ _) Q5 r Hr0) as (q & Hq & Hr).
             exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
        * intros x Hx. apply (proj2 (hjoin_false H p nZ x)). split; [exact (Habv x Hx)|]. unfold stack_max_size, usp in *. lia.
        * (* [comment removed for export] *)
          intros x Hx. change (with_mmap_backing (Z_to_bv 64 16418) p n (noaccess_model p n mdl)) with (vm_add_lazy p n (noaccess_model p n mdl)).
          rewrite m_vm_lazy_vm_add_lazy, Hli. unfold noaccess_model. rewrite m_vm_lazy_with_vmmaps.
          change ([(p, n)] ++ m_vm_lazy mdl) with ((p, n) :: m_vm_lazy mdl). rewrite page_in_ranges_cons. cbn [fst snd].
          unfold hjoin in Hx. apply orb_prop in Hx as [Hx|Hx]; [rewrite (Q7 x Hx); apply orb_true_r|].
          apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          apply orb_true_intro. left. rewrite Hun. pose proof (u64_range x) as Xr.
          unfold page_base, page_base_of, page_size.
          pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
          rewrite u_small by lia. unfold page_size in Hal. pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)).
          assert (nZ mod 4096 = 0) by (unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult).
          pose proof (Z.div_mod nZ 4096 ltac:(lia)).
          apply andb_true_intro; split; apply Z.leb_le; nia.
        * intros x Hx. destruct (Q8 x Hx) as (q & Hq & Hr). exists q. split; [| exact Hr]. unfold lgrant_nr. cbn [l_maps]. right. exact Hq.
      + exact HT.
      + exact Hcl.
      + exact Ht.
  Qed.
End Theorems2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Theorems3.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.
  #[local] Notation bootS' := (bootS sp brk mbase draw lim inp).
  #[local] Notation EB' := (EB sp draw inp).
  #[local] Notation VB' := (VB sp draw inp).

  #[using="Type"] Theorem bs_fresh : forall H A a tid c pl js sr kn L hc lz R M mdl (r : reg) (w : word) (kf : list kentry),
    let v := length (VB' a tid c pl js) in
    bootS' H A a tid c pl js sr kn L hc lz R M mdl ->
    getr R r = w ->
    sr_vars_lt v sr = true -> kn_vars_lt v kn = true -> ledger_vars_lt v L = true ->
    know_ok SEGS (EB' a tid c pl (js ++ [w])) (mrestrict H M) kf ->
    bootS' H A a tid c pl (js ++ [w]) (sr_upd sr (ridx r) (EVar v)) (kf ++ kn) L hc lz R M mdl.
  Proof.
    intros H A a tid c pl js sr kn L hc lz R M mdl r w kf v HB Hw Hsr Hkn HL HKF.
    destruct HB as [HR HKN HA HZ HLZ HM F HMO RG HT Hcl Ht].
    assert (Hev : edenot (EB' a tid c pl (js ++ [w])) (EVar v) = w).
    { rewrite EB_app. cbn [edenot ev]. unfold v. rewrite <- (Nat.add_0_r (length _)), vals_ev_app_r. reflexivity. }
    constructor; try assumption.
    - apply regs_ok_pin; [| rewrite Hev; exact Hw]. rewrite EB_app. apply env_app_regs; [exact Hsr | exact HR].
    - apply (proj2 (know_ok_app SEGS _ _ _ _)). split; [exact HKF|]. rewrite EB_app. apply env_app_know; [exact Hkn | exact HKN].
    - apply mfacts_env; assumption.
    - apply maps_ok_env; assumption.
    - apply regime_ok_env; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma dsj_entries_sub : forall a tid c pl js (ia : nat) (nZ n1 : Z) ds (w : word) V,
    let E := EB' a tid c pl js in
    let v := length (VB' a tid c pl js) in
    know_ok SEGS E V (dsj_entries ia nZ ds) ->
    Forall (fun d => saddr_vars_lt v (fst d) = true /\ expr_vars_lt v (snd d) = true) ds ->
    0 <= n1 -> 0 <= nZ -> bv_unsigned (ev E ia) + nZ < 2 ^ 64 ->
    bv_unsigned (ev E ia) <= bv_unsigned w -> bv_unsigned w + n1 <= bv_unsigned (ev E ia) + nZ ->
    know_ok SEGS (EB' a tid c pl (js ++ [w])) V (dsj_entries v n1 ds).
  Proof.
    intros a tid c pl js ia nZ n1 ds w V E v HK Hlt Hn1 HnZ Hnw Hlo Hhi.
    rewrite EB_app. unfold v.
    apply (dsj_entries_ok SEGS (VB' a tid c pl js) (blobs0 draw (in_argv inp)) V (fun q => q = w) n1 ds w Hn1).
    - lia.
    - unfold dsj_claims. unfold dsj_entries in HK. apply Forall_forall. intros d Hd q Hq. subst q.
      pose proof (proj1 (Forall_forall _ _) HK (KDisj (SA (EVar ia) 0) (ELit nZ) (fst d) (snd d))
                    ltac:(apply in_map_iff; exists d; split; [reflexivity | exact Hd])) as HKd.
      cbn [kentry_ok] in HKd. unfold estart, elenZ in HKd |- *. cbn [a_base a_off edenot] in HKd |- *.
      fold E in HKd. change ({| ev := vals_ev (VB' a tid c pl js); eb := blobs0 draw (in_argv inp) |}) with E.
      pose proof (u64_range (ev E ia)). rewrite (u_small nZ) in HKd by lia.
      destruct HKd as [HKd|HKd]; [left; lia | right; lia].
    - reflexivity.
    - exact Hlt.
  Qed.
End Theorems3.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
