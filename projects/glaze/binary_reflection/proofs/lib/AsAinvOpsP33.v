(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CfgStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsKSys3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanPlacement OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

#[local] Notation kclosedD := (kclosedD segs).
#[local] Notation katD := (katD segs).
#[local] Notation katwD := (katwD segs).
#[local] Notation katsD := (katsD segs).
#[local] Notation doomed := (doomed segs).

Lemma mmap_fixed_rw_free_check_top : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  (alloc_top (m_vmmaps model) < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = flags -> mmap_flags_core flags = 50%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mmap_errnos r   (* [comment removed for export] *)
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
        then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Htop Htop64 H2 H3 Hcore H4 H5 nZ n Hrf.
  pose proof (u64_range addr) as Har. unfold two_pow_64 in Htop64.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as HB. pose proof (page_round_up_Z_pos' len Hlen) as HP.
  assert (Hlen' : (len < 2 ^ 64)%Z) by lia.
  destruct (mmap_gates_core50 flags (Z_to_bv 64 3) Hcore) as (Gm & Gn & _ & Gfn & Gfr).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { (lazymatch goal with |- ?G => let G' := eval unfold w_is0 in G in change_no_check G' end). apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). (lazymatch goal with |- ?G => let G' := eval unfold check_mmap in G in change_no_check G' end).
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn, Gfr. (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end). cbv beta iota zeta.
  rewrite (proj2 (Z.leb_gt _ _)) by ((lazymatch goal with |- ?G => let G' := eval unfold two_pow_64 in G in change_no_check G' end); lia).
  rewrite (proj2 (Z.leb_le _ _) Htop). (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end).
  rewrite (proj2 (Z.eqb_eq _ _) Hal). (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end).
  rewrite (proj2 (Z.ltb_lt _ _) Hpos). (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end). fold nZ. fold n.
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = false).
  { apply region_free_not_contains; [(lazymatch goal with |- ?G => let G' := eval unfold n in G in change_no_check G' end); rewrite u64_lit by lia; lia|].
    rewrite RefNodes.region_free_app in Hrf. apply andb_true_iff in Hrf. tauto. }
  rewrite Hmc, andb_false_r, Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [|try (match goal with |- context [errno_ret_in ?es r] => destruct (errno_ret_in es r) end; [destruct zs|]); reflexivity].
  destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
  (lazymatch goal with |- ?G => let G' := eval unfold mmap_model in G in change_no_check G' end). reflexivity.
Qed.

Section Fixfree.
  Variables (ms : machine_state) (model : Model) (x8 : word) (flags addr : word) (len : Z).
  Hypotheses (Hh : m_halted model = None) (Hsvc : ms_svc_pending ms = Some x8) (Hno : bv_unsigned x8 = 222%Z)
             (H0 : ms_gpr ms 0 = addr) (Hal : (bv_unsigned addr mod page_size = 0)%Z) (Hpos : (0 < bv_unsigned addr)%Z)
             (H1 : ms_gpr ms 1 = Z_to_bv 64 len) (Hlen : (0 < len)%Z)
             (Htop : (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z)
             (Htop64 : (alloc_top (m_vmmaps model) < two_pow_64)%Z)
             (H2 : ms_gpr ms 2 = Z_to_bv 64 3) (H3 : ms_gpr ms 3 = flags) (Hcore : mmap_flags_core flags = 50%Z)
             (H4 : ms_gpr ms 4 = Z_to_bv 64 (-1)) (H5 : ms_gpr ms 5 = Z_to_bv 64 0).
  Let nZ : Z := page_round_up_Z len.
  Let n : word := Z_to_bv 64 nZ.
  Hypotheses (Hrf : region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true)
             (Hbk : mmap_noreserve_backed_ok flags model nZ = true).

  Definition fxfr_effs (i : unit + unit) : SyscallEffect :=
    match i with inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] [] | inr _ => mkEffectU addr [] [(addr, n)] [] [] [] end.
  Definition fxfr_ms' (i : unit + unit) : Model :=
    match i with inl _ => model | inr _ => with_mmap_backing flags addr n (mmap_model addr n model) end.
  Definition fxfr_nx (i : unit + unit) : config := mkCfg (advance_past_svc (apply_effect ms (fxfr_effs i))) (fxfr_ms' i).

  (* [comment removed for export] *)
  Lemma node_mmap_fixfree1 : node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => fxfr_nx (inr tt)).
  Proof.
    pose proof (fun eff => mmap_fixed_rw_free_check_top ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Htop Htop64
                             H2 H3 Hcore H4 H5 Hrf) as Hchk.
    cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk.
    rewrite Hbk in Hchk.
    assert (Ea : errno_ret_in mmap_errnos addr = false).
    { apply errno_ret_in_below; [reflexivity|]. pose proof (alloc_top_room (m_vmmaps model)).
      pose proof (page_round_up_Z_bounds len ltac:(lia)).
      unfold stack_max_size, two_pow_64 in *. lia. }
    assert (Hrb : forall r, refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r)
      by (intros r; exact (CfgStep.refusal_b_mmap (sys_input segs ms x8) model r Hno)).
    (lazymatch goal with |- ?G => let G' := eval unfold fxfr_nx in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fxfr_effs fxfr_ms'] in G in change_no_check G' end).
    apply (node_chk_noacc segs ms model x8 unit (fun _ => mkEffectU addr [] [(addr, n)] [] [] [])
             (fun _ => with_mmap_backing flags addr n (mmap_model addr n model)) Hh Hsvc).
    - intros []. cbv beta. rewrite Hchk. cbv beta iota.
      rewrite Ea, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    - intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      + right. cbn [eff_ret]. rewrite Hrb. split; [exact Er |].
        destruct zs; [|discriminate]. injection Hc as <- <-. split; [exact Hh |]. split.
        { rewrite (CfgStep.injected_family_off_alloc_only CfgStep.kit_cfg _ CfgStep.kit_cfg_alloc_only).
          cbn [sys_input in_sysno]. rewrite Hno. reflexivity. }
        exists tt. rewrite Hrb. exact Ea.
      + left. destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate]. cbn [andb] in Hc.
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
        exists tt. repeat split; reflexivity.
    - left. intros []. rewrite Hrb. exact Ea.
    - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate |].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)])%bool; discriminate.
    - intros []. (lazymatch goal with |- ?G => let G' := eval unfold with_mmap_backing in G in change_no_check G' end). destruct (mmap_noreserve_b flags).
      + rewrite vm_add_lazy_halted, mmap_model_halted. exact Hh.
      + rewrite mmap_model_halted. exact Hh.
    - intros []; reflexivity.
  Qed.





End Fixfree.

End WithSegs.
End AsKSys3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsAinvLedger2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.
#[local] Notation u := bv_unsigned.

Section Famap.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.
  Ltac uilia := unfold IB, DEPOT_TAB, DEPOT_NIDS, DEPOT_MAP1, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.
  Ltac fzri A B Cc D E AGc H := eapply (cellZ_frame _ _ _ _ _ _ H);
    [clear -A B; lia | clear -Cc D E; lia | let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply AGc; clear -Hi; cbn in Hi; lia].

  Theorem OPS_REP_famap_pf : OPS_REP_famap bt.
  Proof using.
    intros st Lc FF M M' mdl mdl' c W R Hc FR lo AGR C24 W128 WSL FSH VMK VMP NA NP' LZ FL' E1 E2 E3 E4 E5 E6 MI EAG.
    pose proof (fa_holes_ok_of_WF bt st Lc FF W) as FHO.
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & WQ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM' & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & YC).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (clear -SP7 SPH; lia). box SP4. box SP5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    assert (Elo : lo = fa_beg SBEG c + r_mapped_fa (a_reg st c)) by reflexivity.
    assert (SL : lo mod 8 = 0 /\ SBEG <= lo /\ fa_beg SBEG c <= lo /\ lo + KFAMAP <= fa_beg SBEG c + 2 ^ 29 /\ fa_beg SBEG c + 2 ^ 29 <= SBEG + KSPACE
                 /\ bt_resv6 bt <= lo /\ lo + KFAMAP <= bt_resv6 bt + bt_resv6_len bt /\ 0 <= lo /\ lo + KFAMAP < 2 ^ 64 /\ AS_HEAPLO <= lo /\ lo + KFAMAP <= CEIL
                 /\ region_beg SBEG c + r_mapped_user (a_reg st c) <= fa_beg SBEG c /\ lo mod 2 ^ 16 = 0).
    { rewrite Elo. unfold fa_beg, region_beg, KFAOFF, KREGION, KREGION_EXHAUST, KFAMAP, KUSERMAP in *. clear -Y2 Y3 Y5 Y6 FR Q1 Q2 Q5 Q8 X14 X15 X16 Hc SP7 SP8 SPH.
      Z.div_mod_to_equations. ulia. }
    destruct SL as (SL1 & SL2 & SL3 & SL4 & SL5 & SL6 & SL7 & SL8 & SL9 & SL10 & SL11 & SL12 & SL13).
    (* [comment removed for export] *)
    set (Mmid := fun a : word => if decide (reginfo bt c + 24 <= u a < reginfo bt c + 32) then M a else M' a).
    assert (P : Rep bt st Lc FF Mmid mdl).
    { apply (Rep_frame_q bt st Lc FF M Mmid mdl W R). intros a NE. unfold Mmid in NE |- *.
      destruct (decide (reginfo bt c + 24 <= u a < reginfo bt c + 32)) as [IN|NI]; [exfalso; exact (NE eq_refl)|].
      destruct (AGR a NE) as [Hf Hd]. split; [| exact Hd].
      intros HC. unfold foot_famap in Hf.
      destruct Hf as [Hf|[Hf|[Hf|[Hf|[Hf|Hf]]]]].
      - exact (NI Hf).
      - exact (rijunk_not_cells bt st Lc FF W c (u a) Hc Hf HC).
      - exact (fshadow_not_cells bt st Lc FF c W Hc FR (u a) Hf HC).
      - exact (fslot_not_supp bt st Lc FF c _ _ W Hc FR (u a) (or_introl HC) Hf).
      - apply (stats_not_cells bt st Lc FF W (u a)); [unfold T_UNW in Hf; exact Hf | exact HC].
      - exact (ceil_not_cells bt st Lc FF W (u a) Hf HC). }
    clearbody lo.
    (* [comment removed for export] *)
    assert (AG : forall i, ~ (reginfo bt c + 24 <= i < reginfo bt c + 32) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mmid in G in change_no_check G' end). rewrite (u64_lit i) by lia.
      destruct (decide (reginfo bt c + 24 <= i < reginfo bt c + 32)) as [IN|NI]; [exfalso; exact (Hi IN) | reflexivity]. }
    assert (DEF : DEFK Mmid M').
    { intros a NE. unfold Mmid in NE. destruct (decide (reginfo bt c + 24 <= u a < reginfo bt c + 32)) as [IN|NI]; [| exfalso; exact (NE eq_refl)].
      destruct (W128 (u a) ltac:(lia)) as [D _]. rewrite Z_to_bv_bv_unsigned in D. exact D. }
    assert (AGP : forall i, ~ (SBEG + KSPACE <= i < SBEG + KSPACE + PG) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply AG; [| exact Hr]. clear -Hi Q9 Q10. intros X. apply Hi. lia. }
    assert (IMGR : forall i, ia_img_lo IA <= i < ia_img_hi IA -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi. apply AGP; [clear -Hi I2 SBH; ulia | clear -Hi I1 I2; ulia]. }
    assert (FIXR : forall lo' hi', In (lo', hi') (bt_fixed bt) -> hi' - lo' < KSPACE -> forall i, lo' <= i < hi' -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo' hi' Hin Hlen i Hi Hr. apply AGP; [| exact Hr]. destruct (space_vs_fixed bt st Lc FF W lo' hi' Hin Hlen); clear -H Hi; ulia. }
    assert (DYNR : forall lo' hi', In (lo', hi') (dyn_ranges st) -> forall i, lo' <= i < hi' -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo' hi' Hin i Hi Hr. apply AGP; [| exact Hr]. destruct (space_vs_dyn bt st Lc FF W lo' hi' Hin); clear -H Hi; ulia. }
    assert (SPCR : forall i, SBEG <= i < SBEG + KSPACE -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply AGP; [clear -Hi; lia | exact Hr]. }
    assert (BANDR : forall i, SB <= i < AS_HEAPLO -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply AGP; [clear -Hi SBH; ulia | exact Hr]. }
    assert (RIR : forall c0, 1 <= c0 <= 30 -> c0 <> c -> forall i, reginfo bt c0 <= i < reginfo bt c0 + 128 -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros c0 Hc0 NE i Hi Hr. apply AG; [| exact Hr]. unfold reginfo in *. clear -Hi Hc0 Hc NE. lia. }
    (* [comment removed for export] *)
    set (r' := REG (r_mapped_user (a_reg st c)) (r_alloc_user (a_reg st c)) (r_mapped_fa (a_reg st c) + KFAMAP) (r_free (a_reg st c)) (r_uhole (a_reg st c)) false).
    set (st' := add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + KFAMAP / 8)] 0).
    assert (ER : a_reg st' = fupdZ (a_reg st) c r') by reflexivity.
    assert (FLD : forall c0, r_mapped_user (a_reg st' c0) = r_mapped_user (a_reg st c0)
                        /\ r_alloc_user (a_reg st' c0) = r_alloc_user (a_reg st c0)
                        /\ r_mapped_fa (a_reg st' c0) = (if c0 =? c then r_mapped_fa (a_reg st c0) + KFAMAP else r_mapped_fa (a_reg st c0))
                        /\ r_free (a_reg st' c0) = r_free (a_reg st c0)
                        /\ r_uhole (a_reg st' c0) = r_uhole (a_reg st c0) /\ r_fhole (a_reg st' c0) = (if c0 =? c then false else r_fhole (a_reg st c0)))
      by (intros c0; exact (famap_fields st c c0)).
    pose proof P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact P1 | exact YC |]. intros c0 i Hc0 Hi.
             destruct (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) as [LT _]. exact (IMGR i LT). }
    (* [comment removed for export] *)
    split. { change (rep_instance bt st' M') with (rep_instance bt st M'). eapply rep_instance_frame; [exact DEF | exact P2 | uilia | uilia | ulia | ulia | exact S1 |].
             intros i Hi Hr. destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
             - apply (FIXR _ _ IN8); [ulia | clear -IN S1 S3; lia | exact Hr].
             - destruct (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact Hi | exact NI])) as [LT _]. exact (IMGR i LT). }
    (* [comment removed for export] *)
    split. { change (rep_thread bt st' M') with (rep_thread bt st M'). eapply rep_thread_frame; [exact DEF | exact P3 | ulia | ulia | ulia | ulia | exact (cache_len bt st Lc FF W) |].
             intros i Hi Hr. destruct (thread_cells_where bt i Hi) as [A|A].
             - apply (FIXR _ _ INT); [ulia | clear -A; unfold T_UNW, PG in *; lia | exact Hr].
             - apply (FIXR _ _ INC); [ulia | clear -A; lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. rewrite ER. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c0 c) as [-> | NE].
             - destruct (P4 c Hc) as [G0 F0]. destruct G0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). destruct F0 as (F1 & F2 & F3). (lazymatch goal with |- ?G => let G' := eval unfold r' in G in change_no_check G' end).
               assert (AGc : forall i, reginfo bt c <= i < reginfo bt c + 128 -> ~ (reginfo bt c + 24 <= i < reginfo bt c + 32) -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
               { intros i Hi Hn. apply AG; [exact Hn | clear -Hi Q9 Q10 X14 X15; ulia]. }
               unfold KSPACE, PG in Q9, Q10, X15. pose proof ceil_rng as CR.
               split.
               + unfold rep_reginfo in *. (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_mapped_fa r_alloc_user r_mapped_user] in G in change_no_check G' end).
                 split; [fzri Q9 X14 Q10 X15 CR AGc G1|]. split; [fzri Q9 X14 Q10 X15 CR AGc G2|]. split; [fzri Q9 X14 Q10 X15 CR AGc G3|].
                 split; [exact C24|]. split; [fzri Q9 X14 Q10 X15 CR AGc G5|]. split; [fzri Q9 X14 Q10 X15 CR AGc G6|].
                 split; [fzri Q9 X14 Q10 X15 CR AGc G7|]. split; [fzri Q9 X14 Q10 X15 CR AGc G8|]. destruct G9 as [G9a G9b].
                 split; [eapply (byteZ_frame _ _ _ _ _ G9a); [clear -Q9 X14; lia | clear -Q10 X15 CR; lia | apply AGc; clear; lia] | exact W128].
               + unfold rep_freearray in *. (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_mapped_fa r_mapped_user] in G in change_no_check G' end). split; [| split; [| frW DEF F3]].
                 * intros i k Hk. pose proof (nth_error_lt _ _ _ Hk) as Hl. pose proof (F1 i k Hk) as C.
                   eapply (cellZ_frame _ _ _ _ _ _ C); [clear -Q1 Q2 Q8 X14; ulia | clear -Hl Q5 Q6 Q7 X15 CR; ulia |].
                   intros i0 Hi0. apply SPCR; [clear -Hi0 Hl Q1 Q2 Q5 Q6 Q7 Q8; ulia | clear -Hi0 Hl Q1 Q2 Q5 Q6 Q7 Q8 X14 X15 CR; ulia].
                 * pose proof (writableZ_keep _ _ _ _ _ DEF F2) as F2'. intros i Hi.
                   destruct (Z.lt_ge_cases i lo) as [LT|GE]; [apply F2'; clear -Hi LT Elo; lia | apply WSL; clear -Hi GE Elo; lia].
             - destruct (P4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
               destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & _).
               eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | clear -D9 X14; ulia | clear -D10 X15; ulia | clear -D1 D2 D8 X14; ulia | clear -D2 D5 D6 D8 X15; ulia | exact D7 |].
               intros i Hi Hr. unfold foot_region in Hi. destruct Hi as [[Hi _] | Hi]; [apply (RIR c0 Hc0 NE); [clear -Hi; lia | exact Hr] | apply SPCR; [clear -Hi D1 D2 D3 D4 D5 D6 D7; ulia | exact Hr]]. }
    (* [comment removed for export] *)
    assert (BAfree : forall q, rep_batches bt Mmid q -> (forall b, In b q -> In b (a_tq st ++ a_gq st)) -> rep_batches bt M' q).
    { intros q RB SUB. eapply rep_batches_frame; [exact DEF | exact RB | |].
      - intros b Hb. destruct (batch_facts bt st Lc FF W b (SUB b Hb)) as (_ & BL & BB1 & BB2). clear -BL BB1 BB2 X14 X15. ulia.
      - intros b i Hb Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b (SUB b Hb)) as (_ & BL & BB1 & BB2).
        apply SPCR; [clear -Hi BL BB1 BB2; ulia | exact Hr]. }
    split; [change (a_tq st') with (a_tq st); apply (BAfree _ P5); intros b Hb; apply in_app_iff; left; exact Hb|].
    split; [change (a_gq st') with (a_gq st); apply (BAfree _ P6); intros b Hb; apply in_app_iff; right; exact Hb|].
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st' M') with (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact P7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A5 A6 A7. ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (DYNR _ _ (sec_dyn st sc Hs)); [| exact Hr]. pose proof (rz_range (sc_n sc)). clear -Hi A5 A6 A7 H. ulia. }
    (* [comment removed for export] *)
    split. { change (rep_headers bt st' Lc M') with (rep_headers bt st Lc M'). destruct P8 as [HLh HQh].
             assert (HDRfree : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
             { intros p' n' i Hown Hf Hr. pose proof (rz_range n') as RZ'.
               destruct (hdr_zone bt st Lc FF W p' n' i Hown Hf) as [(HP' & W1 & W2 & W3 & CV' & HC' & N1' & W4) | (HP' & sc' & Hs' & Eu' & En' & W1 & N1')].
               - apply SPCR; [clear -W1 W2 W3 W4 N1'; lia | exact Hr].
               - apply (DYNR _ _ (sec_dyn st sc' Hs')); [| exact Hr]. destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
                 rewrite Eu', En' in *. clear -W1 A5 A6 N1'. ulia. }
             split.
             - intros p' n' Hin'. destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n') as RZ'.
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | clear -A1 A3 RZ'; ulia | clear -A2 A3; ulia |]. intros i Hi Hr. exact (HDRfree p' n' i (or_introl Hin') Hi Hr).
             - intros m0 n' Hq. destruct (HQh m0 n' Hq) as [Hh HW]. split; [| frW DEF HW].
               destruct (quar_item_range bt st Lc FF W m0 n' Hq) as (QB1 & QB2 & QB3). pose proof (rz_range n') as RZn.
               eapply rep_hdr_frame; [exact DEF | exact Hh | clear -QB1 QB2 QB3 RZn; ulia | clear -QB1 QB2 QB3 RZn; ulia |]. intros i Hi Hr.
               apply (HDRfree (m0 + 16) n' i); [right; replace (m0 + 16 - 16) with m0 by lia; exact Hq | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact P9 | uilia | uilia | uilia | uilia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). clear -A1 A2. ulia.
             - intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) as [LT _]. exact (IMGR i LT).
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXR _ _ INN); [clear; ulia | clear -Hi Hbk Eb; rewrite Eb; lia | exact Hr].
               + apply (DYNR _ _ (node_dyn st bb Hnb)); [clear -Hi Hbk; lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact P10 | ulia | ulia | uilia | uilia | clear -DT1; ulia | clear -DT2; ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). clear -A1 A2 A4 X5 X6. ulia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXR _ _ INFS); [clear; ulia | clear -Hi; ulia | exact Hr].
               + destruct (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact Hi)) as [LT _]. exact (IMGR i LT).
               + apply (FIXR _ _ (dtls_member bt st Lc FF W)); [clear; ulia | clear -Hi; ulia | exact Hr].
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXR _ _ INFS); [clear; ulia | clear -Hi A1 A2 A4; ulia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact P11 | uilia | uilia | uilia | uilia |].
             intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) as [LT _]. exact (IMGR i LT). }
    (* [comment removed for export] *)
    split. { destruct P12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end). change (a_sec st') with (a_sec st). change (quar st') with (quar st).
             assert (SHR : forall lo1 hi1 g, lo1 / 8 <= g < hi1 / 8 -> 0 <= lo1 -> hi1 <= CEIL + 8 -> SB <= SB + g < AS_HEAPLO /\ 0 <= SB + g /\ SB + g + 1 < 2 ^ 64).
             { intros lo1 hi1 g Hg Hg0 Hg1. clear -Hg Hg0 Hg1. Zlia. }
             split. { intros c0 g Hc0 Hg NL'. destruct (FLD c0) as (RMU & _). rewrite RMU in Hg. pose proof (SH1 c0 g Hc0 Hg NL') as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 X14; ulia) ltac:(clear -D2 D3 D4 D5 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros c0 g Hc0 Hg. destruct (FLD c0) as (_ & _ & RFA & _). rewrite RFA in Hg.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & _).
                      destruct (Z.eqb_spec c0 c) as [-> | NE].
                      - destruct (Z.lt_ge_cases g (lo / 8)) as [OLD | NEW].
                        + pose proof (SH2 c g Hc ltac:(rewrite Elo in OLD; clear -Hg OLD; lia)) as BY.
                          destruct (SHR (fa_beg SBEG c) lo g ltac:(clear -Hg OLD; lia) ltac:(clear -D1 D2 D3 D4 X14; ulia) ltac:(clear -SL11; unfold KFAMAP in SL11; lia)) as (QQ1 & QQ2 & QQ3).
                          eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]].
                        + apply FSH. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). rewrite Elo in NEW |- *. clear -NEW Hg SL1 Elo. unfold KFAMAP in *. Z.div_mod_to_equations. lia.
                      - pose proof (SH2 c0 g Hc0 Hg) as BY.
                        destruct (SHR _ _ g Hg ltac:(clear -D1 D2 D3 D4 X14; ulia) ltac:(clear -D5 D6 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                        eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros sc g Hs Hg NUG. pose proof (SH3 sc g Hs Hg NUG) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -A1; ulia) ltac:(clear -A2; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros sc g Hs HQ HU. pose proof (SH4 sc g Hs HQ HU) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
                      unfold user_granule in HU.
                      destruct (SHR (sc_user sc) (sc_user sc + sc_n sc + 7) g ltac:(clear -HU; lia) ltac:(clear -A1 A5; ulia) ltac:(clear -A2 A6; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros c0 g Hc0 Hg. destruct (FLD c0) as (RMU & _). rewrite RMU in Hg. exact (def_keep Mmid M' _ DEF (SH5 c0 g Hc0 Hg)). }
             intros sc g Hs Hg. exact (def_keep Mmid M' _ DEF (SH6 sc g Hs Hg)). }
    (* [comment removed for export] *)
    split. { destruct P13 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12). (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end).
             change (dyn_maps st') with (dyn_maps st). change (a_dep st') with (a_dep st).
             assert (COM : forall a, committed bt st' a <-> committed bt st a \/ lo <= a < lo + KFAMAP).
             { intros a. (lazymatch goal with |- ?G => let G' := eval unfold committed in G in change_no_check G' end). change (a_nres st') with (a_nres st). split.
               - intros [(c0 & Hc0 & X) | X]; [| left; right; exact X]. destruct (FLD c0) as (RMU & _ & RFA & _). rewrite RMU, RFA in X.
                 destruct (Z.eqb_spec c0 c) as [-> | NE]; [| left; left; exists c0; exact (conj Hc0 X)].
                 destruct X as [X | X]; [left; left; exists c; split; [exact Hc | left; exact X]|].
                 destruct (Z.lt_ge_cases a lo); [left; left; exists c; split; [exact Hc | right; rewrite Elo in *; clear -X H; lia] | right; rewrite Elo in *; clear -X H; unfold KFAMAP in *; lia].
               - intros [[(c0 & Hc0 & X) | X] | X].
                 + left. exists c0. destruct (FLD c0) as (RMU & _ & RFA & _). rewrite RMU, RFA. split; [exact Hc0|].
                   destruct (Z.eqb_spec c0 c) as [-> | NE]; [| exact X]. destruct X as [X | X]; [left; exact X | right; (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); clear -X; lia].
                 + right. exact X.
                 + left. exists c. destruct (FLD c) as (_ & _ & RFA & _). rewrite Z.eqb_refl in RFA. rewrite RFA. split; [exact Hc|]. right. rewrite Elo in X. clear -X Y5. lia. }
             assert (HOL1 : forall a, holes bt st' a -> holes bt st a).
             { intros a (c0 & Hc0 & X). exists c0. split; [exact Hc0|]. destruct (FLD c0) as (RMU & _ & RFA & _ & RUH & RFH). rewrite RMU, RFA, RUH, RFH in X.
               destruct (Z.eqb_spec c0 c) as [-> | NE]; [| exact X]. destruct X as [X | [F _]]; [left; exact X | discriminate F]. }
             assert (HOL2 : forall a, holes bt st a -> holes bt st' a \/ (r_fhole (a_reg st c) = true /\ lo <= a < lo + KFAMAP)).
             { intros a (c0 & Hc0 & X). destruct (FLD c0) as (RMU & _ & RFA & _ & RUH & RFH).
               destruct (Z.eqb_spec c0 c) as [E | NE].
               - subst c0. destruct X as [X | [HU X]]; [| right; split; [exact HU | rewrite Elo; exact X]].
                 left. exists c. rewrite RMU, RFA, RUH, RFH. split; [exact Hc|]. left. exact X.
               - left. exists c0. rewrite RMU, RFA, RUH, RFH. exact (conj Hc0 X). }
             (* [comment removed for export] *)
             assert (SLOTH : forall a, lo <= a < lo + KFAMAP -> holes bt st' a -> False).
             { intros a Ha (c0 & Hc0 & X). destruct (FLD c0) as (RMU & _ & RFA & _ & RUH & RFH). rewrite RMU, RFA, RUH, RFH in X.
               destruct (Z.eqb_spec c0 c) as [-> | NE].
               - destruct X as [[_ X] | [F _]]; [| discriminate F]. rewrite Elo in Ha. clear -Ha X Y3 Y5. unfold fa_beg, KFAOFF, KREGION_EXHAUST, KFAMAP, KUSERMAP in *. lia.
               - pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (PP1 & PP2 & PP3 & PP4 & PP5 & PP6 & PP7 & PP8 & _).
                 destruct (WR1 c0 Hc0) as (_ & _ & W3 & _). pose proof (FHO c0 Hc0) as FH0.
                 assert (XR : region_beg SBEG c0 <= a < region_beg SBEG c0 + KREGION).
                 { unfold fa_beg, KFAOFF, KREGION, KREGION_EXHAUST, KFAMAP, KUSERMAP in *. destruct X as [[_ X] | [HF X]]; [clear -X PP8 W3; lia | specialize (FH0 HF); clear -X PP6 FH0; lia]. }
                 pose proof (fslot_other bt st Lc FF c _ _ W Hc FR c0 a Hc0 NE) as FO. apply FO; [unfold KREGION in XR; exact XR|].
                 (lazymatch goal with |- ?G => let G' := eval unfold fslot in G in change_no_check G' end). rewrite <- Elo. exact Ha. }
             split. { destruct L1 as (F6 & PF & FOK & FPW & FH).
                      assert (WF6 : ivs_wf F6).
                      { intros q Hq. rewrite Forall_forall in FOK. destruct (FOK q Hq) as (A1 & A2 & A3 & _). (lazymatch goal with |- ?G => let G' := eval unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S in G in change_no_check G' end).
                        clear -A1 A2 A3 SP3. ulia. }
                      destruct (r_fhole (a_reg st c)) eqn:HU.
                      - (* [comment removed for export] *)
                        assert (FREE : forall a, lo <= a < lo + KFAMAP -> covered F6 a = false).
                        { intros a Ha. destruct (covered F6 a) eqn:CV; [| reflexivity]. exfalso.
                          apply (proj1 (FH a ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_resv6 in G in change_no_check G' end); clear -Ha SL6 SL7; lia)) ltac:(apply in_ivz_covered; exact CV)).
                          exists c. split; [exact Hc|]. right. split; [exact HU | rewrite <- Elo; exact Ha]. }
                        pose proof (frag_remapped bt ltac:(clear -SP3; ulia) F6 lo (Z_to_bv 64 lo) (Z_to_bv 64 KFAMAP) FOK (seps_of_split F6 FPW) WF6
                                      ltac:(subst lo; apply fa_slot_aligned; exact Y6) SL6 SL7
                                      ltac:(rewrite u64_lit; [reflexivity | clear -SL8 SL9; unfold KFAMAP in *; lia]) ltac:(rewrite u64_lit; [reflexivity | (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); lia]) FREE) as FRM.
                        cbn zeta in FRM. destruct FRM as (FOK' & FSP' & FWF' & FCV').
                        exists ((Z_to_bv 64 lo, Z_to_bv 64 KFAMAP) :: F6).
                        split. { eapply Permutation_trans; [exact (VMP eq_refl)|]. (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end). apply Permutation_cons; [reflexivity | exact PF]. }
                        split; [exact FOK'|]. split; [exact (split_of_seps _ FSP')|].
                        intros a Ha. rewrite !in_ivz_covered, (FCV' a). rewrite <- in_ivz_covered. split.
                        + intros [X | X]; [| intros H'; exact (SLOTH a X H')]. intros H'. exact (proj1 (FH a Ha) X (HOL1 a H')).
                        + intros NH. destruct (decide (lo <= a < lo + KFAMAP)) as [IN | NI]; [right; exact IN | left].
                          apply (proj2 (FH a Ha)). intros Hh. destruct (HOL2 a Hh) as [H' | [_ X]]; [exact (NH H') | exact (NI X)].
                      - (* [comment removed for export] *)
                        exists F6. rewrite (VMK eq_refl). split; [exact PF|]. split; [exact FOK|]. split; [exact FPW|].
                        intros a Ha. rewrite (FH a Ha). split.
                        + intros NH H'. exact (NH (HOL1 a H')).
                        + intros NH Hh. destruct (HOL2 a Hh) as [H' | [F _]]; [exact (NH H') | discriminate F]. }
             split. { intros a. rewrite (NA a), (L2 a), (COM a). split.
                      - intros [(A & B & Cn) D]. split; [exact A|]. split; [intros [X|X]; [exact (B X) | exact (D X)]|]. intros H'. exact (Cn (HOL1 a H')).
                      - intros (A & B & Cn). assert (NS : ~ (lo <= a < lo + KFAMAP)) by (intros X; apply B; right; exact X).
                        split; [| exact NS]. split; [exact A|]. split; [intros X; apply B; left; exact X|].
                        intros Hh. destruct (HOL2 a Hh) as [H' | [_ X]]; [exact (Cn H') | exact (NS X)]. }
             split. { intros a. rewrite (LZ a), (L3 a), (COM a). split.
                      - intros [[(A & B & Cn) | S] D]; [left | right; exact S]. split; [exact A|]. split; [intros [X|X]; [exact (B X) | exact (D X)]|].
                        intros H'. exact (Cn (HOL1 a H')).
                      - intros [(A & B & Cn) | S].
                        + assert (NS : ~ (lo <= a < lo + KFAMAP)) by (intros X; apply B; right; exact X).
                          split; [| exact NS]. left. split; [exact A|]. split; [intros X; apply B; left; exact X|].
                          intros Hh. destruct (HOL2 a Hh) as [H' | [_ X]]; [exact (Cn H') | exact (NS X)].
                        + split; [right; exact S|]. destruct S as (b & Hb & Rb). intros X.
                          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (store_dyn st b Hb)) as D. hnf in D. cbn in D. clear -Rb X D SL6 SL7. unfold KFAMAP in *. lia. }
             split; [exact FL'|]. unfold alloc_top in L10 |- *. rewrite E1, E2, E3, E4, E5, E6. repeat (split; [assumption|]). exact NP'. }
    (* [comment removed for export] *)
    split. { destruct P14 as (Bu1 & Bu2 & Bu3 & Bu4 & Bu5 & Bu6 & Bu7 & Bu8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
             change (a_aa st') with (a_aa st ++ [(sh_lo lo, sh_lo lo + KFAMAP / 8)]). change (a_sec st') with (a_sec st).
             change (a_dep st') with (a_dep st). change (a_shsec st') with (a_shsec st + 0). change (a_nres st') with (a_nres st).
             assert (SHLO : sh_lo lo = sh_lo (fa_beg SBEG c) + r_mapped_fa (a_reg st c) / 8 /\ sh_lo lo mod PG = 0 /\ (KFAMAP / 8) mod PG = 0 /\ 0 <= sh_lo lo /\ sh_lo lo + KFAMAP / 8 <= 2 ^ 64
                            /\ (r_mapped_fa (a_reg st c) + KFAMAP) / 8 = r_mapped_fa (a_reg st c) / 8 + KFAMAP / 8).
             { (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). rewrite Elo. clear -Y6 SL13 SL8 SL9 Elo X14 X16 Hc. unfold fa_beg, region_beg, KFAOFF, KREGION, KFAMAP, PG, SB in *. Z.div_mod_to_equations. lia. }
             destruct SHLO as (SH1' & SH2' & SH3' & SH4' & SH5' & SH6').
             split. { unfold A_wf in *. apply Forall_app. split; [exact Bu1|]. apply Forall_cons; [| apply Forall_nil]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end).
                      clear -SH2' SH3' SH4'. unfold PG, KFAMAP in *. Z.div_mod_to_equations. lia. }
             split; [exact MI|].
             split; [intros lo1 hi1 H; apply range_allowed_app; exact (Bu3 lo1 hi1 H)|].
             split; [intros p n H; apply range_allowed_app; exact (Bu4 p n H)|].
             split. { intros c0 Hc0. rewrite ER. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c0 c) as [-> | NE].
                      - destruct (Bu5 c Hc) as [X Y]. (lazymatch goal with |- ?G => let G' := eval unfold r' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_mapped_fa] in G in change_no_check G' end). split; [apply range_allowed_app; exact X|].
                        rewrite SH6'. intros a Ha. destruct (Z.lt_ge_cases a (sh_lo lo)) as [LT | GE].
                        + apply (range_allowed_app _ _ _ _ Y). clear -Ha LT SH1'. lia.
                        + apply (range_allowed_last (a_aa st) (sh_lo lo) (sh_lo lo + KFAMAP / 8) SH2' ltac:(clear -SH2' SH3'; unfold PG in *; Z.div_mod_to_equations; lia) SH4' SH5').
                          clear -Ha GE SH1'. lia.
                      - destruct (Bu5 c0 Hc0) as [X Y]. split; apply range_allowed_app; assumption. }
             split; [intros s Hs; apply range_allowed_app; exact (Bu6 s Hs)|].
             split; [intros b Hb; apply range_allowed_app; exact (Bu7 b Hb)|].
             rewrite A_bytes_app. (lazymatch goal with |- ?G => let G' := eval cbn [A_bytes fst snd] in G in change_no_check G' end).
             change (sec_charge st') with (sec_charge st). change (depot_charge st') with (depot_charge st).
             assert (PC : prim_charge st' = prim_charge st + (KFAMAP + KFAMAP / 8)).
             { (lazymatch goal with |- ?G => let G' := eval unfold prim_charge in G in change_no_check G' end). rewrite (sum_classes_upd (fun c0 : Z => r_mapped_user (a_reg st c0) + r_mapped_user (a_reg st c0) / 8 + r_mapped_fa (a_reg st c0) + r_mapped_fa (a_reg st c0) / 8)
                                           (fun c0 : Z => r_mapped_user (a_reg st' c0) + r_mapped_user (a_reg st' c0) / 8 + r_mapped_fa (a_reg st' c0) + r_mapped_fa (a_reg st' c0) / 8)
                                           c (KFAMAP + KFAMAP / 8) 30).
               - destruct (Z.leb_spec c (Z.of_nat 30)); [reflexivity | exfalso; lia].
               - intros c0 NE. destruct (FLD c0) as (RMU & _ & RFA & _). rewrite RMU, RFA. destruct (Z.eqb_spec c0 c) as [E | _]; [exfalso; exact (NE E) | reflexivity].
               - destruct (FLD c) as (RMU & _ & RFA & _). rewrite Z.eqb_refl in RFA. rewrite RMU, RFA, SH6'. lia.
               - lia. }
             rewrite PC. destruct Bu8 as [Bu8 Bu9]. split; [clear -Bu8 EAG; lia|].
             (* [comment removed for export] *)
             intros s0 Hs0. apply in_app_iff. left. exact (Bu9 s0 Hs0). }
    (* [comment removed for export] *)
    split. { intros p' n' Hin'. destruct (P15 p' n' Hin') as [V1 V2]. split; [frW DEF V1 | frW DEF V2]. }
    split. { intros f k0 Hf. frW DEF (P16 f k0 Hf). }
    split; [eapply (cellZ_frame _ _ _ _ _ _ P17); [ulia | ulia | intros i Hi; exact (IMGR i (proj1 (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia))))] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ P18); [ulia | ulia | intros i Hi; exact (IMGR i (proj1 (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia))))] |].
    exact (rep_last_keep bt _ _ Mmid M' DEF P19 (fun H => H)).
  Qed.
End Famap.
