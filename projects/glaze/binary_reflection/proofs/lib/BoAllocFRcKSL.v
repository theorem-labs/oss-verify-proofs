(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcGL.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRcS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcGS.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma rt_priv_sub : forall {RUN : run_ceil} IA (Lc Lc' FF : list (Z * Z)) a,
  (forall x, In x Lc' -> In x Lc) -> rt_priv IA Lc FF a -> rt_priv IA Lc' FF a.
Proof.
  intros RUN IA Lc Lc' FF a SUB (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros V. apply P3.
  destruct V as [(b & n & Hin & Hr) | [V | [(b & n & Hin & Hr) | V]]].
  - left. exists b, n. split; [exact (SUB _ Hin) | exact Hr].
  - right; left; exact V.
  - right; right; left. exists b, n. split; [exact (SUB _ Hin) | exact Hr].
  - right; right; right; exact V.
Qed.

Section RcGL.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, PTRHI in *; lia.

  Section W.
    Variables (st : ast) (Lc FF : list (Z * Z)).
    Context {qt qg : Z}.
    Hypothesis W : WFq bt st Lc FF qt qg.
    Hypothesis IMGLO : ia_img_lo IA <= 65536.

    Lemma sec_live_idx : forall p n, In (p, n) Lc -> is_primary n = false ->
      exists i s, nth_error (a_sec st) i = Some s /\ In s (a_sec st) /\ sc_user s = p /\ sc_n s = n.
    Proof using W qg qt FF bt RUN.
      intros p n Hin HP. destruct (live_sec bt st Lc FF W p n Hin HP) as (s & Hs & Eu & En).
      destruct (In_nth_error _ _ Hs) as (i & Hi). exists i, s. repeat split; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma post_lists : forall L1 L2 p n, Lc = L1 ++ (p, n) :: L2 -> forall x, In x (L1 ++ L2) -> In x Lc /\ x <> (p, n).
    Proof using W qg qt FF st bt RUN.
      intros L1 L2 p n HL x Hx. pose proof W as (_ & _ & _ & _ & (_ & ND & _) & _).
      assert (NDL : List.NoDup (L1 ++ (p, n) :: L2)) by (rewrite <- HL; exact ND).
      rewrite HL. exact (proj1 (in_remove_mid L1 L2 (p, n) x NDL) Hx).
    Qed.

    (* [comment removed for export] *)
    Lemma sec_live_private : forall L1 L2 p n s a, Lc = L1 ++ (p, n) :: L2 -> is_primary n = false -> In s (a_sec st) -> sc_user s = p -> sc_n s = n ->
      sc_map s <= a < sc_map s + sc_mapsz s -> rt_priv IA (L1 ++ L2) FF a.
    Proof using IMGLO W qg qt.
      intros L1 L2 p n s a HL HP Hs Eu En Ha.
      pose proof (post_lists L1 L2 p n HL) as INL.
      pose proof (sec_geom bt st Lc FF W IMGLO s Hs) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
      pose proof (img_lits bt st Lc FF W) as [I1 I2].
      pose proof (fs_vs_dyn bt st Lc FF W _ _ (sec_dyn st s Hs)) as DF.
      split; [clear - Ha G2; lia|]. split; [clear - Ha G9; lia|].
      destruct (heap_not_shadowish bt st Lc FF W (L1 ++ L2) a ltac:(intros p0 n0 H0; exact (proj1 (INL _ H0))) ltac:(clear - Ha G10; lia)) as (N1 & N2 & N3 & N4).
      intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
      - destruct V as (p' & n' & Hin & Hpa). destruct (INL _ Hin) as [Hin2 NE].
        destruct (live_ext bt st Lc FF W p' n' Hin2) as (lo' & hi' & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
        pose proof (up8_facts n' ltac:(lia)) as (U1 & _).
        destruct E as [(HP' & -> & -> & CV' & HC' & LIV' & S1 & S2) | (HP' & sc & Hsc & Eu' & En' & -> & ->)].
        + clear - G11 S1 S2 Ha Hpa Y1 Y2 U1 Y8. ulia.
        + destruct (sec_cases bt st Lc FF W s sc Hs Hsc) as [<- | D].
          * apply NE. rewrite <- Eu', <- En', Eu, En. reflexivity.
          * clear - D Ha Hpa Y1 Y2 U1 Y8. unfold PG in *. lia.
      - destruct V as (f & k & Hf & Hfa). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
        clear - DF Ha Hfa F1 F2 F3 F4. ulia.
    Qed.

    (* [comment removed for export] *)
    Lemma shadow_private_of_sub : forall Lc' lo L z, (forall x, In x Lc' -> In x Lc) -> lo mod 8 = 0 -> L mod 8 = 0 -> 0 <= lo -> lo + L <= CEIL ->
      (lo + L <= ia_img_lo IA \/ ia_img_hi IA <= lo) ->
      (forall a, lo <= a < lo + L -> ~ app_visible IA Lc' FF a) ->
      sh_lo lo <= z < sh_lo lo + L / 8 -> rt_priv IA Lc' FF z.
    Proof using IMGLO W qg qt st.
      intros Lc' lo L z SUB Hlo HL HLO HHI HIM NV Hz. pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof ceil_rng as CR.
      unfold sh_lo in Hz.
      pose proof (Z.div_mod lo 8 ltac:(lia)) as Dlo. rewrite Hlo in Dlo. pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite HL in DL.
      set (g := z - SB) in *. assert (Eg : z = SB + g) by ((lazymatch goal with |- ?G => let G' := eval unfold g in G in change_no_check G' end); lia).
      assert (G8 : lo <= 8 * g < lo + L) by lia.
      split; [ulia|]. split; [ulia|].
      intros [V | [V | [V | [V | [V | V]]]]].
      - destruct V as (p & n & Hin & Hr).
        pose proof W as (_ & _ & _ & _ & (WL & _) & _). destruct (WL p n (SUB _ Hin)) as (_ & _ & (B1 & B2 & B3 & B4) & _). ulia.
      - destruct V as (f & k & Hf & Hr). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & _).
        pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _ & _ & _ & _ & _ & INFS & _) & _).
        destruct (RNG _ _ (all_ranges_fixed bt st _ INFS)) as ((D1 & D2 & D3 & D4 & D5) & _). ulia.
      - destruct V as (p & n & Hin & Hr). unfold sh_lo, sh_hi in Hr.
        destruct (live_range bt st Lc FF W p n (SUB _ Hin)) as (L1 & L2 & L3 & L4).
        apply (NV (8 * g) G8). left. exists p, n. split; [exact Hin|].
        pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. assert (P8 : p mod 8 = 0) by (clear -L4; Z.div_mod_to_equations; lia). rewrite P8 in Dp.
        assert (g < (p + n + 7) / 8) by lia. assert (p / 8 <= g) by lia.
        assert (8 * g + 8 <= p + n + 7) by (clear -H; Z.div_mod_to_equations; lia). lia.
      - destruct V as (f & k & Hf & Hr). unfold sh_lo, sh_hi in Hr.
        destruct (frame_gran bt st Lc FF W f k Hf) as [F8 K8].
        apply (NV (8 * g) G8). right; left. exists f, k. split; [exact Hf|].
        pose proof (Z.div_mod f 8 ltac:(lia)) as Df. rewrite F8 in Df.
        assert (g < (f + FS k + 7) / 8) by lia. assert (f / 8 <= g) by lia.
        assert (8 * g + 8 <= f + FS k + 7) by (clear -H; Z.div_mod_to_equations; lia). lia.
      - unfold in_stack_shadow, sh_lo in V. pose proof ceil_pg as CP.
        assert (CEIL / 8 <= g) by lia. assert (CEIL <= 8 * g) by (clear -H CP; Z.div_mod_to_equations; lia). lia.
      - unfold in_image_shadow, sh_lo, sh_hi in V.
        assert (g < (ia_img_lo IA + (ia_img_hi IA - ia_img_lo IA) + 7) / 8) by lia.
        assert (ia_img_lo IA / 8 <= g) by lia.
        assert (8 * g + 8 <= ia_img_hi IA + 7) by (clear -H; Z.div_mod_to_equations; lia).
        assert (ia_img_lo IA <= 8 * g + 7) by (clear -H0; Z.div_mod_to_equations; lia).
        clear - H1 H2 G8 HIM Dlo DL. lia.
    Qed.

    Lemma sec_live_shadow_private : forall L1 L2 p n s z, Lc = L1 ++ (p, n) :: L2 -> is_primary n = false -> In s (a_sec st) -> sc_user s = p -> sc_n s = n ->
      sh_lo (sc_map s) <= z < sh_lo (sc_map s) + sc_mapsz s / 8 -> rt_priv IA (L1 ++ L2) FF z.
    Proof using IMGLO W qg qt.
      intros L1 L2 p n s z HL HP Hs Eu En Hz.
      pose proof (sec_geom bt st Lc FF W IMGLO s Hs) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
      apply (shadow_private_of_sub (L1 ++ L2) (sc_map s) (sc_mapsz s) z);
        [intros x Hx; exact (proj1 (post_lists L1 L2 p n HL x Hx)) | clear - G3; Z.div_mod_to_equations; lia | clear - G4; Z.div_mod_to_equations; lia | lia | exact G2 | right; exact G9 | | exact Hz].
      intros a Ha. exact (proj2 (proj2 (sec_live_private L1 L2 p n s a HL HP Hs Eu En Ha))).
    Qed.
  End W.
End RcGL.
End BoAllocFRcGL.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys8 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys8 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlushKI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS5. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlushKI.AsRtFlushK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlushKI.BoRtFlushI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlushKI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRcS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcS4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcS6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcSU OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcSN.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53.AsAinvRelease3.   (* [comment removed for export] *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc94 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc94.AsAinvOpsRc63 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcGS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc94.AsAinvOpsRc93 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc94 BoAllocFRcGL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI.   (* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section KSL.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation P8 := (bt_ptrarr bt).

  Ltac gl G := clear - G; unfold hideW in G; lia.

  (* [comment removed for export] *)
  Definition sec_live_post (qt qg : Z) (st : ast) (L1 L2 FF : list (Z * Z)) (M : mem) (mdl : Model) (R : bvmap 5 word) (S ret : word) (c' : config) : Prop :=
    exists fx' (i : nat) (M' : mem) mdl' (R' : bvmap 5 word),
      c' = mkCfg (@mkst fx' R' ret M' (seg_rom BSEGS)) mdl'
      /\ FXOK fx' /\ m_halted mdl' = None /\ BackingAlgebra.model_ivs_wf mdl'
      /\ WFq bt (op_sec_free st i) (L1 ++ L2) FF qt qg /\ Rep bt (op_sec_free st i) (L1 ++ L2) FF M' mdl'
      /\ (forall a : word, U S - 2400 <= U a -> M' a = M a)
      /\ (forall a : word, M' a <> M a -> rc_changed bt (L1 ++ L2) FF (U S) (U a) /\ (M' a <> None \/ rt_priv (bt_ia bt) (L1 ++ L2) FF (U a)))
      /\ lazy_kept (bt_ia bt) (L1 ++ L2) FF mdl mdl' /\ same_except_vm mdl mdl'
      /\ regs_kept R R'.

  (* [comment removed for export] *)
  Definition sec_live_stmt : Prop :=
    forall fx (X : Z -> Prop) qt qg st Lc L1 L2 FF (M : mem) mdl (R : bvmap 5 word) (S ret cbw : word) m n,
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WFq bt st Lc FF qt qg -> AsAinvOpsRc73.AsAinvRepX3.RepX bt X st Lc FF M mdl ->
      Lc = L1 ++ (m + 16, n) :: L2 -> is_primary n = false ->
      (forall z, X z -> z = m \/ m + 16 <= z < m + 24 \/ (bt_thread bt + 2768 <= z < bt_thread bt + 3168) \/ CEIL <= z) ->
      getr R 1 = ret -> ret_ok ret -> getr R 2 = at_ S (-2400) -> getr R 10 = cbw -> getr R 11 = Z_to_bv 64 m ->
      getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt)) ->
      U S mod 16 = 0 -> CEIL + 3584 <= U S -> U S + 16 <= PTRHI + 256 ->
      (forall a : word, U S - 3584 <= U a < U S - 2400 -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
      katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4e8a4) M (seg_rom BSEGS)) mdl)
           (sec_live_post qt qg st L1 L2 FF M mdl R S ret).

  Theorem sec_live_pf : sec_live_stmt.
  Proof using SHGATE BOOTG HTP SECC RCC CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold sec_live_stmt in G in change_no_check G' end).
    intros fx X qt qg st Lc La Lb FF M mdl R S ret cbw m n HFX HH MW W RX ELc HP XSHAPE
           R1 RET R2 R10 R11 R4 S16 Slo Shi SOK.
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    (* [comment removed for export] *)
    set (s0v := getr R 8) in *. set (s1v := getr R 9) in *. set (s2v := getr R 18) in *. set (s3v := getr R 19) in *. set (s4v := getr R 20) in *.
    set (x21 := getr R 21) in *. set (tpv := getr R 4) in *.
    assert (PC0 : (0x4e8a4%bv : word) = Z_to_bv 64 0x4e8a4) by (apply bv_eq; reflexivity).
    assert (PC1 : (0x4ef70%bv : word) = Z_to_bv 64 0x4ef70) by (apply bv_eq; reflexivity).
    assert (PC2 : v_addi (0x811b8%bv : word) 4 = Z_to_bv 64 0x811bc) by (apply bv_eq; reflexivity).
    assert (PC3 : (0x811bc%bv : word) = Z_to_bv 64 0x811bc) by (apply bv_eq; reflexivity).
    assert (PCF : (0x6ea68%bv : word) = ft_base both_flush_tab) by reflexivity.
    destruct RX as (M0 & RP & DX).
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M) by (intros a Ha; destruct (decide (M a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct RCC as (CELL_rib & CELL_magic & G_tsdp).
    destruct SECC as (CELL_spg & CELL_chk & CELL_gpgc & CELL_pgc & CELL_seal & CELL_lim & CELL_thr & G_tsdp2).
    unfold free_cells_nb in CELLNB.
    (* [comment removed for export] *)
    assert (Hin : In (m + 16, n) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    assert (IMGLO : ia_img_lo (bt_ia bt) <= 65536) by (rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
    destruct (sec_live_idx bt st Lc FF W (m + 16) n Hin HP) as (i & s & Hnth & Hs & Eus & Ens).
    pose proof (sec_geom bt st Lc FF W IMGLO s Hs) as G. cbv zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
    assert (Hlen : (i < length (a_sec st))%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
    destruct (nth_error (a_sec st) (length (a_sec st) - 1)) as [sl|] eqn:Hnl; [| exfalso; apply nth_error_None in Hnl; lia].
    assert (Hsl : In sl (a_sec st)) by exact (nth_error_In _ _ Hnl).
    pose proof (sec_geom bt st Lc FF W IMGLO sl Hsl) as GL. cbv zeta in GL.
    destruct GL as (L1 & L2 & L3 & L4 & L5 & _ & _ & _ & L9 & L10 & L11 & L12 & L13 & L14).
    pose proof (sec_cases bt st Lc FF W s sl Hs Hsl) as SCS.
    pose proof (ptrarr_geom bt st Lc FF W IMGLO) as (PG1 & PG2 & PG3 & PG4 & PG5 & PG6 & PG7 & PG8).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    rewrite BT_ia in GTI, GCI, G9, L9, PG1. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI, G9, L9, PG1.
    unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
    unfold KSPACE, PG, AS_HEAPLO, AS_LO, NMAX, PTRHI in *.
    remember (sc_map s) as h eqn:Eh. remember (sc_mapsz s) as msz eqn:Emsz. remember (sc_map sl) as last eqn:Elast. remember (sc_mapsz sl) as lsz eqn:Elsz.
    set (len := Z.of_nat (length (a_sec st))) in *. set (iz := Z.of_nat i) in *.
    assert (Em : sc_user s = m + 16) by exact Eus.
    rewrite Em in G6, G7. rewrite Ens in G7, G8.
    assert (T4 : 4096 <= T) by (clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    set (shlo := 0x7fff8000 + h / 8).
    destruct (sh_split h msz (pg_mod8 h G3) (pg_mod8 msz G4) ltac:(clear - G1; lia) ltac:(clear - G5; lia)) as (SHs & SH8h & SH8m).
    assert (P_GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 + 256) by (clear - Slo Shi CR; lia).       (* [comment removed for export] *)
    assert (P_GT : 4096 <= T /\ T + 4096 <= U S - 3584) by (clear - T4 GTC Slo; lia).
    assert (P_Gh8 : AIMGHI <= h /\ h mod 8 = 0 /\ msz mod 8 = 0 /\ 65536 <= msz /\ h + msz <= U S - 3584).
    { split; [exact G9|]. split; [exact (pg_mod8 h G3)|]. split; [exact (pg_mod8 msz G4)|]. clear - G5 G2 Slo. lia. }
    assert (P_Gi : 0 <= iz < len /\ len <= 2 ^ 20) by ((lazymatch goal with |- ?G => let G' := eval unfold iz, len in G in change_no_check G' end); clear - Hlen PG8; lia).
    assert (P_Gptr : AIMGHI <= P8 /\ P8 + 8 * len <= U S - 3584) by (clear - PG1 PG2 PG8 Slo; unfold len in *; lia).
    assert (P_Glast : AIMGHI <= last /\ last + 32 <= U S - 3584) by (clear - L9 L2 L5 Slo; lia).
    assert (P_GshS : shlo + msz / 8 <= U S - 3584) by ((lazymatch goal with |- ?G => let G' := eval unfold shlo in G in change_no_check G' end); clear - SH8h SH8m G2 Slo CR; lia).
    assert (P_GlastH : hideW (last = h \/ last + 32 <= h \/ h + msz <= last)).
    { (lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end). destruct SCS as [<- | [D | D]]; [left; rewrite Eh, Elast; reflexivity | right; right; clear - D; lia | right; left; clear - D L5; lia]. }
    assert (P_GptrL : hideW (P8 + 8 * len <= last \/ last + 32 <= P8)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - L14 L5 PG8; unfold len in *; lia).
    assert (P_GptrH : hideW (P8 + 8 * len <= h \/ h + msz <= P8)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - G14 PG8; unfold len in *; lia).
    assert (P_GTi : hideW (T + 4096 <= AIMGLO \/ AIMGHI <= T)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI; lia).
    assert (P_GptrT : hideW (P8 + 8 * len <= T \/ T + 4096 <= P8)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - PG6 PG8; unfold len in *; lia).
    assert (P_GlastT : hideW (last + 32 <= T \/ T + 4096 <= last)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - L12 L5; lia).
    assert (SHB : (0x7fff8000 <= shlo /\ shlo + msz / 8 <= 0x8fff7000) \/ (0x2008fff7000 <= shlo /\ shlo + msz / 8 <= 0x10007fff8000)).
    { (lazymatch goal with |- ?G => let G' := eval unfold shlo in G in change_no_check G' end). clear - G10 G1 G5 G2 CR SH8h SH8m. lia. }
    assert (P_Gsh : hideW (shlo + msz / 8 <= AIMGLO \/ AIMGHI <= shlo)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - SHB; lia).
    assert (P_GshP : hideW (shlo + msz / 8 <= P8 \/ P8 + 8 * len <= shlo)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - SHB PG4 PG8; unfold len in *; lia).
    assert (P_GshL : hideW (shlo + msz / 8 <= last \/ last + 32 <= shlo)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - SHB L10 L5; lia).
    (* [comment removed for export] *)
    pose proof RP as (Rc & Ri & Rt & _ & _ & _ & Rsec & Rh & _ & _ & _ & _ & R13 & R14 & _ & _ & Csb & _ & SHM0).
    first [pose proof (proj1 SHM0) as SHM | pose proof SHM0 as SHM]. clear SHM0.          (* [comment removed for export] *)
    rewrite BT_ia in Csb. cbn [ia_rtc_sb both_addrs] in Csb.
    destruct Ri as (_ & Inch & Ilock & _ & _ & _ & _ & Ichunks & Iptrw).
    destruct Rt as (_ & _ & _ & _ & _ & _ & _ & _ & TW & Tback & _).
    destruct (Rsec i s Hnth) as (Hmap & Hsz & _ & Hidx & Hwr).
    destruct (Rsec _ sl Hnl) as (_ & _ & _ & _ & Lwr).
    destruct Rh as [RHL _]. destruct (RHL (m + 16) n Hin) as (_ & _ & Hnhi & Hnlo & _).
    destruct R14 as (B1 & B2 & _ & _ & _ & BSS & _ & _ & B9).          (* [comment removed for export] *)
    rewrite BT_segs in *. unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
    unfold T_PC, PC_SZ, sh_lo, sh_hi, SB, PG in *.
    rewrite <- Eh in Hmap, Hsz, Hidx, Hwr. rewrite <- Emsz in Hsz, Hwr. rewrite <- Elast, <- Elsz in Lwr.
    replace (m + 16 - 14) with (m + 2) in Hnhi by lia. replace (m + 16 - 12) with (m + 4) in Hnlo by lia.
    (* [comment removed for export] *)
    pose proof (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _ & _ & INC).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as SPT.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as SPC.
    unfold KSPACE, PG in SPT, SPC.
    assert (XIMG : forall z, (AIMGLO <= z /\ z < 0x10ab58 + 888) \/ (0x10ab58 + 920 <= z /\ z < AIMGHI) -> ~ X z).
    { intros z Hz Hx. destruct (XSHAPE z Hx) as [Q | [Q | [Q | Q]]]; [clear - Hz Q G9 G6; lia | clear - Hz Q G9 G6; lia | clear - Hz Q GTI; lia | clear - Hz Q CR; lia]. }
    assert (XC : forall z, CTX <= z < CTX + 65536 -> ~ X z).
    { intros z Hz Hx. destruct (XSHAPE z Hx) as [Q | [Q | [Q | Q]]]; [clear - Hz Q G13 G6 G7 G8; lia | clear - Hz Q G13 G6 G7 G8; lia | clear - Hz Q GCT'; lia | clear - Hz Q GCC; lia]. }
    assert (XHP : forall z, h <= z < h + 4096 -> ~ X z).
    { intros z Hz Hx. destruct (XSHAPE z Hx) as [Q | [Q | [Q | Q]]]; [clear - Hz Q G6; lia | clear - Hz Q G6; lia | clear - Hz Q G12 G5; lia | clear - Hz Q G2 G5; lia]. }
    assert (XM : forall z, m + 1 <= z < m + 16 -> ~ X z).
    { intros z Hz Hx. destruct (XSHAPE z Hx) as [Q | [Q | [Q | Q]]]; [clear - Hz Q; lia | clear - Hz Q; lia | clear - Hz Q G12 G6 G7 G8; lia | clear - Hz Q G2 G7 G8; lia]. }
    assert (XP : forall z, P8 <= z < P8 + 2 ^ 23 -> ~ X z).
    { intros z Hz Hx. destruct (XSHAPE z Hx) as [Q | [Q | [Q | Q]]]; [clear - Hz Q G14 G6 G7 G8; lia | clear - Hz Q G14 G6 G7 G8; lia | clear - Hz Q PG6; lia | clear - Hz Q PG2; lia]. }
    assert (XSUBL : forall z, X z -> AsAinvOpsRc94.XL bt s z).
    { intros z Hx. (lazymatch goal with |- ?G => let G' := eval unfold AsAinvOpsRc94.XL in G in change_no_check G' end). rewrite <- Eh, <- Emsz. destruct (XSHAPE z Hx) as [Q | [Q | [Q | Q]]]; [left; clear - Q G6 G7 G8; lia | left; clear - Q G6 G7 G8; lia | right; left; exact Q | right; right; exact Q]. }
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (rep_nolazy_thread bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHC : forall z, CTX <= z < CTX + 65536 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GC0 GCC CR; lia|]. apply (rep_nolazy_tctx bt st Lc FF M0 mdl W RP). exact Hz. }
    assert (NHH : forall z, h <= z < h + msz -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz G1 G2 CR; lia|]. apply (rep_nolazy_sec bt st Lc FF M0 mdl W RP s z Hs). rewrite <- Eh, <- Emsz. exact Hz. }
    assert (NHL : forall z, last <= z < last + lsz -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz L1 L2 CR; lia|]. apply (rep_nolazy_sec bt st Lc FF M0 mdl W RP sl z Hsl). rewrite <- Elast, <- Elsz. exact Hz. }
    assert (NHP : forall z, P8 <= z < P8 + 8 * len -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz PG1 PG2 PG8 CR; unfold len in *; lia|]. apply (rep_nolazy_ptrarr bt st Lc FF M0 mdl W RP). clear - Hz PG8. unfold len in *. lia. }
    assert (NHSH : forall z, shlo <= z < shlo + msz / 8 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. apply (BSS s Hs). rewrite <- Eh, <- Emsz. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end). rewrite SHs. unfold shlo in Hz. clear - Hz. lia. }
    (* [comment removed for export] *)
    hidehypW G10. hidehypW G11. hidehypW G12. hidehypW G13. hidehypW G14. hidehypW L10. hidehypW L11. hidehypW L12. hidehypW L13. hidehypW L14.
    hidehypW PG4. hidehypW PG5. hidehypW PG6. hidehypW PG7. hidehypW GTI. hidehypW GTB. hidehypW GCI. hidehypW GCB. hidehypW GCT'. hidehypW SCS.
    hidehypW SPT. hidehypW SPC. hidehypW SHB. hidehypW G_tsdp. hidehypW G_tsdp2.
    Ltac ul := unfold hideW in *; lia.
    (* [comment removed for export] *)
    Ltac czl := first [ reflexivity | (vm_compute; discriminate) | (vm_compute; reflexivity) | lia ].
    Ltac cimgM M M0 X Rc EQ0 XIMG C := apply (cellM M M0 X _ _ _ (const_cell bt _ _ _ _ Rc C) EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply XIMG; clear - Hz; lia].
    assert (C_spb : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))) by cimgM M M0 X Rc EQ0 XIMG CELLNB.
    assert (C_pg : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096))) by cimgM M M0 X Rc EQ0 XIMG CELL_spg.
    assert (C_ptr : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 72)) 8 = Some (LE8 (Z_to_bv 64 P8))) by cimgM M M0 X Rc EQ0 XIMG CELL_chk.
    assert (C_gsh : rdn BSEGS M (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8))) by cimgM M M0 X Rc EQ0 XIMG CELL_gsh.
    assert (C_gmb : rdn BSEGS M (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8))) by cimgM M M0 X Rc EQ0 XIMG CELL_gmb.
    assert (C_mb : rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0))) by cimgM M M0 X Rc EQ0 XIMG CELL_mb.
    assert (C_gme : rdn BSEGS M (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0))) by cimgM M M0 X Rc EQ0 XIMG CELL_gme.
    assert (C_me : rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by cimgM M M0 X Rc EQ0 XIMG CELL_me.
    assert (C_ghe : rdn BSEGS M (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0))) by cimgM M M0 X Rc EQ0 XIMG CELL_ghe.
    assert (C_he : rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by cimgM M M0 X Rc EQ0 XIMG CELL_he.
    assert (C_grm : rdn BSEGS M (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58))) by cimgM M M0 X Rc EQ0 XIMG CELL_grm.
    assert (C_rm : rdn BSEGS M (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c))) by cimgM M M0 X Rc EQ0 XIMG CELL_rm.
    assert (C_gcf : rdn BSEGS M (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8))) by cimgM M M0 X Rc EQ0 XIMG CELL_gcf.
    assert (C_thr64 : rdn BSEGS M (Z_to_bv 64 (0x19fce8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615))) by cimgM M M0 X Rc EQ0 XIMG CELL_thr.
    assert (C_lim : rdn BSEGS M (Z_to_bv 64 (0x19fce8 + 144)) 8 = Some (LE8 (Z_to_bv 64 0))) by cimgM M M0 X Rc EQ0 XIMG CELL_lim.
    assert (C_gpgc : rdn BSEGS M (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 0x19dc60))) by cimgM M M0 X Rc EQ0 XIMG CELL_gpgc.
    assert (C_pgc : rdn BSEGS M (Z_to_bv 64 0x19dc60) 8 = Some (LE8 (Z_to_bv 64 4096))) by cimgM M M0 X Rc EQ0 XIMG CELL_pgc.
    assert (C_seal : rdn BSEGS M (Z_to_bv 64 0x105f58) 8 = Some (LE8 (Z_to_bv 64 1))) by cimgM M M0 X Rc EQ0 XIMG CELL_seal.
    assert (C_sh : rdn BSEGS M (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))).
    { apply (cellM M M0 X _ _ _ Csb EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply XIMG; clear - Hz; lia]. }
    assert (C_kif : rdn BSEGS M (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]).
    { rewrite <- w2b1 by (clear; lia). cimgM M M0 X Rc EQ0 XIMG CELL_kif. }
    assert (C_key : rdn BSEGS M (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24 : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). cimgM M M0 X Rc EQ0 XIMG CELL_key. }
    subst TP. cbn [ia_tp both_addrs] in CELL_tsdp, Gc9, Gc10.
    assert (Utp : U tpv = 0x641380) by (rewrite R4; vm_compute; reflexivity).
    assert (C_tsdp : rdn BSEGS M (at_ tpv (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { replace (at_ tpv (-88)) with (Z_to_bv 64 (0x641380 - 88) : word) by (clear - Utp; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Utp; unorm; reflexivity).
      cimgM M M0 X Rc EQ0 XIMG CELL_tsdp. }
    assert (C_tctx : rdn BSEGS M (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))).
    { apply (cellM M M0 X _ _ _ (const_cell bt _ _ _ _ Rc CELL_tctx) EQ0); [clear - Gc1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc2; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XIMG. clear - Hz G_tsdp Gc1 Gc2. ul. }
    assert (C_thr : rdn BSEGS M (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152) : word) by (clear - GC0 GCC CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply (cellM M M0 X _ _ _ Tback EQ0); [clear - GC0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GCC CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XC. clear - Hz. lia. }
    assert (Hrng : 0 <= h /\ h + msz < 2 ^ 64) by (clear - G1 G2 CR; lia).
    assert (C_mbh : rdn BSEGS M (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h))).
    { apply (cellM M M0 X _ _ _ Hmap EQ0); [clear - Hrng; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G5; lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XHP. clear - Hz G5. lia. }
    assert (C_msz : rdn BSEGS M (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz))).
    { apply (cellM M M0 X _ _ _ Hsz EQ0); [clear - Hrng; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G5; lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XHP. clear - Hz G5. lia. }
    assert (C_idx : rdn BSEGS M (Z_to_bv 64 (h + 24)) 8 = Some (LE8 (Z_to_bv 64 iz))).
    { apply (cellM M M0 X _ _ _ Hidx EQ0); [clear - Hrng; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G5; lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XHP. clear - Hz G5. lia. }
    assert (C_nhi : rdn BSEGS M (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)))).
    { apply (cellM M M0 X _ _ _ Hnhi EQ0); [clear - Hrng G6; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G6 G7 G8; lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XM. clear - Hz. lia. }
    assert (C_nlo : rdn BSEGS M (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32))).
    { apply (cellM M M0 X _ _ _ Hnlo EQ0); [clear - Hrng G6; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G6 G7 G8; lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XM. clear - Hz. lia. }
    assert (C_n : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 len))).
    { apply (cellM M M0 X _ _ _ Inch EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply XIMG; clear - Hz; lia]. }
    assert (C_hs : forall j x, nth_error (map sc_map (a_sec st)) j = Some x -> rdn BSEGS M (Z_to_bv 64 (P8 + 8 * Z.of_nat j)) 8 = Some (LE8 (Z_to_bv 64 x))).
    { intros j x Hj. rewrite nth_error_map in Hj. destruct (nth_error (a_sec st) j) as [sj|] eqn:Ej; [| discriminate Hj]. injection Hj as <-.
      assert (Lj : (j < length (a_sec st))%nat) by (apply nth_error_Some; rewrite Ej; discriminate).
      apply (cellM M M0 X _ _ _ (Ichunks j sj Ej) EQ0); [clear - PG1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - PG2 CR Lj PG8; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply XP. clear - Hz Lj PG8. lia. }
    (* [comment removed for export] *)
    pose (memD := mrestrict Hd M).
    assert (Utsdp : U (Z_to_bv 64 TSDP) = TSDP) by (clear - Gc1 Gc2; unorm; reflexivity).
    assert (Uctx152 : U (at_ (Z_to_bv 64 CTX) 152) = CTX + 152) by (clear - GC0 GCC CR; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
    assert (Utp88 : U (at_ tpv (-88)) = 0x641380 - 88) by (clear - Utp; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Utp; unorm; reflexivity).
    assert (Ukey : U (at_ (Z_to_bv 64 0x10da20) 4) = 0x10da24) by (clear; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity).
    Ltac toD_img Hd M NHs C := apply (rdRw Hd M M _ _ _ C); [unorm; czl | intros x _; reflexivity | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]].
    assert (K_spb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))) by toD_img Hd M NHs C_spb.
    assert (K_pg : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096))) by toD_img Hd M NHs C_pg.
    assert (K_ptr : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 72)) 8 = Some (LE8 (Z_to_bv 64 P8))) by toD_img Hd M NHs C_ptr.
    assert (K_n : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 len))) by toD_img Hd M NHs C_n.
    assert (K_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8))) by toD_img Hd M NHs C_gsh.
    assert (K_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))) by toD_img Hd M NHs C_sh.
    assert (K_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8))) by toD_img Hd M NHs C_gmb.
    assert (K_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0))) by toD_img Hd M NHs C_mb.
    assert (K_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0))) by toD_img Hd M NHs C_gme.
    assert (K_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by toD_img Hd M NHs C_me.
    assert (K_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0))) by toD_img Hd M NHs C_ghe.
    assert (K_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by toD_img Hd M NHs C_he.
    assert (K_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58))) by toD_img Hd M NHs C_grm.
    assert (K_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c))) by toD_img Hd M NHs C_rm.
    assert (K_gcf : rdn BSEGS memD (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8))) by toD_img Hd M NHs C_gcf.
    assert (K_thr64 : rdn BSEGS memD (Z_to_bv 64 (0x19fce8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615))) by toD_img Hd M NHs C_thr64.
    assert (K_kif : rdn BSEGS memD (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]) by toD_img Hd M NHs C_kif.
    assert (K_key : rdn BSEGS memD (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0)).
    { apply (rdRw Hd M M _ _ _ C_key); [rewrite Ukey; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x _; reflexivity | rewrite Ukey; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]. }
    assert (K_tsdp : rdn BSEGS memD (at_ tpv (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { apply (rdRw Hd M M _ _ _ C_tsdp); [rewrite Utp88; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x _; reflexivity | rewrite Utp88; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]. }
    assert (K_tctx : rdn BSEGS memD (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))).
    { apply (rdRw Hd M M _ _ _ C_tctx); [rewrite Utsdp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc2; lia | intros x _; reflexivity | rewrite Utsdp; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz Gc1 Gc2; lia | right; clear - Hz Gc1 Gc2; lia]]. }
    assert (K_thr : rdn BSEGS memD (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { apply (rdRw Hd M M _ _ _ C_thr); [rewrite Uctx152; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GCC CR; lia | intros x _; reflexivity | rewrite Uctx152; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHC; clear - Hz; lia]. }
    Ltac toD_h Hd M NHH G C := apply (rdRw Hd M M _ _ _ C); [clear - G; wd_ulia_c | intros x _; reflexivity | rewrite u_Z2bv by (clear - G; lia); (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHH; clear - Hz G; lia].
    pose proof (conj Hrng (conj G5 (conj G6 (conj G7 G8)))) as GH0.
    assert (K_mbh : rdn BSEGS memD (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h))) by toD_h Hd M NHH GH0 C_mbh.
    assert (K_msz : rdn BSEGS memD (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz))) by toD_h Hd M NHH GH0 C_msz.
    assert (K_idx : rdn BSEGS memD (Z_to_bv 64 (h + 24)) 8 = Some (LE8 (Z_to_bv 64 iz))) by toD_h Hd M NHH GH0 C_idx.
    assert (K_nhi : rdn BSEGS memD (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)))) by toD_h Hd M NHH GH0 C_nhi.
    assert (K_nlo : rdn BSEGS memD (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32))) by toD_h Hd M NHH GH0 C_nlo.
    assert (K_hs : forall j x, nth_error (map sc_map (a_sec st)) j = Some x -> rdn BSEGS memD (Z_to_bv 64 (P8 + 8 * Z.of_nat j)) 8 = Some (LE8 (Z_to_bv 64 x))).
    { intros j x Hj. pose proof (C_hs j x Hj) as CJ.
      assert (Lj : Z.of_nat j < len).
      { pose proof (nth_error_Some (map sc_map (a_sec st)) j) as NS. rewrite Hj in NS. rewrite length_map in NS. (lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end). assert (j < length (a_sec st))%nat by (apply NS; discriminate). lia. }
      pose proof (conj Lj (conj PG1 (conj PG2 (conj PG8 CR)))) as GJ.
      apply (rdRw Hd M M _ _ _ CJ); [clear - GJ; unfold len in *; wd_ulia_c | intros x0 _; reflexivity |].
      replace (U (Z_to_bv 64 (P8 + 8 * Z.of_nat j))) with (P8 + 8 * Z.of_nat j) by (clear - GJ; unfold len in *; unorm; reflexivity).
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply NHP. clear - Hz GJ. lia. }
    assert (Hnth_i : nth_error (map sc_map (a_sec st)) i = Some h) by (rewrite nth_error_map, Hnth, Eh; reflexivity).
    assert (Hnth_l : nth_error (map sc_map (a_sec st)) (length (a_sec st) - 1) = Some last) by (rewrite nth_error_map, Hnl, Elast; reflexivity).
    pose proof (K_hs i h Hnth_i) as K_slot. fold iz in K_slot.
    pose proof (K_hs _ last Hnth_l) as K_last. replace (Z.of_nat (length (a_sec st) - 1)) with (len - 1) in K_last by ((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); clear - Hlen; lia).
    (* [comment removed for export] *)
    destruct (rdn1_ex_10ae41 memD) as [b1 Hb1]. destruct (rdn1_ex_10ae42 memD) as [b2 Hb2]. destruct (rdn1_ex_10ae43 memD) as [b3 Hb3].
    assert (K_lock0 : rdn BSEGS memD (Z_to_bv 64 0x10ae00) 1 = Some [Z_to_bv 8 0]).
    { unfold byteZ, cellN in Ilock. rewrite w2b1 in Ilock by (clear; lia).
      assert (C_l0 : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 680)) 1 = Some [Z_to_bv 8 0]).
      { eapply rd_same; [| clear; wd_ulia_c | exact Ilock]. intros x Hx. apply EQ0. apply XIMG. revert Hx. clear. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia. }
      toD_img Hd M NHs C_l0. }
    assert (K_lock : rdn BSEGS memD (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; b1; b2; b3]).
    { apply rdn4_of_bytesS; [clear; wd_ulia | exact K_lock0 | | | ].
      - replace (at_ (Z_to_bv 64 0x10ae00) 1) with (Z_to_bv 64 0x10ae01 : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). exact Hb1.
      - replace (at_ (Z_to_bv 64 0x10ae00) 2) with (Z_to_bv 64 0x10ae02 : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). exact Hb2.
      - replace (at_ (Z_to_bv 64 0x10ae00) 3) with (Z_to_bv 64 0x10ae03 : word) by (clear; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). exact Hb3. }
    set (lkw := [Z_to_bv 8 0; b1; b2; b3]).
    pose proof (bytes_le_to_Z_bound lkw) as Blk. cbn [length lkw] in Blk. pose proof (bytes_le_to_Z_nonneg lkw) as Blk0.
    assert (P_hv : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U (Z_to_bv 64 (bytes_le_to_Z lkw))) by (clear - Blk Blk0; unorm; reflexivity).
    (* [comment removed for export] *)
    unfold PG in TW.
    assert (TDEF : forall z, T <= z < T + 4096 -> M (Z_to_bv 64 z) <> None).
    { intros z Hz. apply GR0. apply (writableZ_def M0 _ _ _ TW). exact Hz. }
    assert (TDEFD : forall z, T <= z < T + 4096 -> memD (Z_to_bv 64 z) <> None).
    { intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite mrestrict_off by (apply NHT; exact Hz). exact (TDEF z Hz). }
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2840)) 8) as (bf0 & Cf0 & Lf0);
      [intros z Hz; apply TDEFD; clear - Hz GT0 GTC CR; revert Hz; unorm; intros Hz; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2848)) 8) as (bf1 & Cf1 & Lf1);
      [intros z Hz; apply TDEFD; clear - Hz GT0 GTC CR; revert Hz; unorm; intros Hz; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn8_ex_10ac28 memD) as (bnf & Cnf & Lnf). destruct (rdn8_ex_10ac30 memD) as (bca & Cca & Lca).
    destruct (rdn8_ex_10ae58 memD) as (b16 & C16 & L16). destruct (rdn8_ex_10ae60 memD) as (b24 & C24 & L24).
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS memD (at_ S (-2512)) 112 = true).
    { replace (at_ S (-2512)) with (Z_to_bv 64 (U S - 2512) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz HSr Slo CR. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz. unorm. lia.
      - apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
    assert (SOKT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { apply (sokX Hd M M0 _ _ T _ TW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - GTC CR; lia | clear - GT0; lia |].
      intros z Hz. apply NHT. clear - Hz. cbn in Hz. lia. }
    assert (SOKslot : store_ok BSEGS memD (Z_to_bv 64 (P8 + 8 * iz)) 8 = true).
    { apply (sokX Hd M M0 _ _ (P8 + 8 * iz) 8 Iptrw GR0); [clear - P_Gi; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - P_Gi PG8; unfold len in *; lia | clear - PG2 PG8 CR; lia | clear - PG1 P_Gi; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply NHP. clear - Hz P_Gi. lia. }
    assert (SOKlast : store_ok BSEGS memD (Z_to_bv 64 (last + 24)) 8 = true).
    { apply (sokX Hd M M0 _ _ (last + 24) 8 Lwr GR0); [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - L5; lia | clear - L2 CR; lia | clear - L1; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply NHL. clear - Hz L5. lia. }
    assert (SHrng : 0x7fff8000 <= shlo /\ shlo + msz / 8 <= 0x10007fff8000 /\ 0 <= msz / 8) by (clear - SHB SH8m G5; ul).
    assert (SOKsh : store_ok BSEGS memD (Z_to_bv 64 (AsRtPoison.shad (Z_to_bv 64 h))) (Z.to_nat (msz / 8)) = true).
    { replace (AsRtPoison.shad (Z_to_bv 64 h)) with shlo by (clear - Hrng G5; (lazymatch goal with |- ?G => let G' := eval unfold AsRtPoison.shad, shlo in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - SHrng; lia | rewrite Z2Nat.id by (clear - SHrng; lia); clear - SHrng; lia |].
      rewrite Z2Nat.id by (clear - SHrng; lia). intros z Hz. split; [| apply NHSH; exact Hz].
      apply GR0. apply SHM. (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_GAPLO, AS_LO, AS_HEAPLO in G in change_no_check G' end). clear - Hz SHB. ul. }
    (* [comment removed for export] *)
    assert (P_Gspb : 0x10007fff8000 <= SBEG /\ SBEG + 2 ^ 37 < 2 ^ 47) by (clear - SBH SB1 CR; lia).
    assert (P_Gh : AIMGHI <= h /\ h mod 4096 = 0 /\ msz mod 4096 = 0 /\ 65536 <= msz /\ h + msz <= U S - 3584) by (clear - G9 G3 G4 G5 G2 Slo; lia).
    assert (P_Ghs : hideW (h + msz <= 0x7fff7000 \/ 0x10007fff8000 <= h)) by exact G10.
    assert (P_Ghp : hideW (h + msz <= SBEG \/ SBEG + 2 ^ 37 <= h)) by (clear - G11; ul).
    assert (P_Gm : h + 4096 <= m /\ m + 16 <= h + msz) by (clear - G6 G7 G8; lia).
    assert (P_Gn : 1 <= n <= 2 ^ 40) by (clear - G8; lia).
    assert (P_GTt : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact T4|]. split; [clear - GTI GTB; ul | clear - GTC Slo; lia]. }
    assert (P_GhT : hideW (h + msz <= T \/ T + 4096 <= h)) by exact G12.
    assert (P_Gctx : 1 <= CTX /\ CTX + 4096 <= U S - 3584) by (clear - GC0 GCC Slo; lia).
    assert (P_Gctxi : hideW (CTX + 4096 <= AIMGLO \/ AIMGHI <= CTX)) by (clear - GCI; ul).
    assert (P_Gtp : 0x10ae04 + 88 <= U tpv /\ U tpv + 8 <= AIMGHI) by (rewrite Utp; clear; lia).
    assert (P_Gtsdp : AIMGLO <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= 0x10ae00 \/ 0x10ae04 <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= AIMGHI).
    { rewrite Utsdp. clear - G_tsdp2 Gc1 Gc2. ul. }
    assert (P_Glen : 0 <= iz < len /\ len <= 2 ^ 20 /\ Z.of_nat (length (map sc_map (a_sec st))) = len) by (rewrite length_map; clear - P_Gi; unfold len in *; lia).
    assert (P_hs63 : Forall (fun x => 0 <= x < 2 ^ 63) (map sc_map (a_sec st))).
    { apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (sx & <- & Hsx). destruct (sec_facts bt st Lc FF W sx Hsx) as (A1 & A2 & _ & _ & A5 & A6 & A7 & _). clear - A1 A2 A5 A6 A7 CR. unfold PG in *. lia. }
    assert (P_scan : gbb_scan m (map sc_map (a_sec st)) 0 = h).
    { rewrite Eh. apply (sec_scan bt st Lc FF W s m Hs). rewrite <- Eh, <- Emsz. clear - P_Gm. lia. }
    (* [comment removed for export] *)
    destruct (run_sA memD (seg_rom BSEGS) R S ret s0v s1v s2v s3v s4v x21 cbw tpv (Z_to_bv 64 TSDP)
                (Z_to_bv 64 (bytes_le_to_Z lkw)) (Z_to_bv 64 MIDEND) b1 b2 b3 m n SBEG T CTX h msz iz len P8 last (map sc_map (a_sec st)) bf0 bf1 bnf bca b16 b24
                R1 R2 R10 R11 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                P_GS P_Gspb P_Gh P_Ghs P_Ghp P_Gm P_Gn P_GTt P_GhT P_Gctx P_Gctxi P_Gtp P_Gtsdp P_Glen P_Gptr P_GptrT P_GptrH P_Glast P_GlastH P_GptrL
                P_hs63 P_scan SOKstk SOKT SOKslot SOKlast SOKsh
                K_spb K_pg K_lock P_hv K_n K_ptr K_hs K_slot K_last K_mbh K_msz K_idx K_kif K_key K_tsdp K_tctx K_thr K_nhi K_nlo
                Cf0 Lf0 Cf1 Lf1 Cnf Lnf Cca Lca C16 L16 C24 L24 K_gsh K_sh K_gmb K_mb K_gme K_me K_ghe K_he K_grm K_rm K_gcf K_thr64)
      as (rA & RUNA & A1 & A2 & A10 & A11 & A8 & A9 & A18 & A19 & A20 & A21 & A3 & A4 & A22 & A23 & A24 & A25 & A26 & A27).
    set (j0 := at_ (Z_to_bv 64 (bytes_le_to_Z bf0)) 1) in *. set (j1 := v_add (Z_to_bv 64 n) (Z_to_bv 64 (bytes_le_to_Z bf1))) in *.
    set (wnf := at_ (Z_to_bv 64 (bytes_le_to_Z bnf)) 1) in *. set (wca := v_sub (Z_to_bv 64 (bytes_le_to_Z bca)) (Z_to_bv 64 msz)) in *.
    set (w16 := v_add (Z_to_bv 64 (bytes_le_to_Z b16)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 msz))) in *.
    set (w24 := v_add (Z_to_bv 64 (bytes_le_to_Z b24)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 msz))) in *.
    (* [comment removed for export] *)
    assert (HOstk : hid_off Hd (U S - 2512) 112).
    { apply hid_off_of. intros z Hz. split; [clear - Hz HSr Slo CR; lia | apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]]. }
    assert (HOinst : hid_off Hd 0x10ab98 656).
    { apply hid_off_of. intros z Hz. split; [clear - Hz; lia | apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]. }
    assert (HOT : hid_off Hd (T + 2840) 16).
    { apply hid_off_of. intros z Hz. split; [clear - Hz GT0 GTC CR; lia | apply NHT; clear - Hz; lia]. }
    assert (HOT2 : hid_off Hd (T + 2888) 16).
    { apply hid_off_of. intros z Hz. split; [clear - Hz GT0 GTC CR; lia | apply NHT; clear - Hz; lia]. }
    assert (HOslot : hid_off Hd (P8 + 8 * iz) 8).
    { apply hid_off_of. intros z Hz. split; [clear - Hz PG1 PG2 PG8 P_Gi CR; unfold len in *; lia | apply NHP; clear - Hz P_Gi; lia]. }
    assert (HOlast : hid_off Hd (last + 24) 8).
    { apply hid_off_of. intros z Hz. split; [clear - Hz L1 L2 L5 CR; lia | apply NHL; clear - Hz L5; lia]. }
    assert (HOsh : hid_off Hd shlo (msz / 8)).
    { apply hid_off_of. intros z Hz. split; [clear - Hz SHrng; lia | apply NHSH; exact Hz]. }
    (* [comment removed for export] *)
    set (st1 := op_sec_release st h (sc_n s)). set (Hd1 := HID st1 mdl).
    assert (RL1 : rep_ledger bt st1 mdl) by exact (rep_ledger_release bt st mdl h (sc_n s) R13).
    assert (NHs1 : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd1 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st1 mdl z RL1 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHT1 : forall z, T <= z < T + 4096 -> Hd1 (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (rep_nolazy_thread bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHC1 : forall z, CTX <= z < CTX + 65536 -> Hd1 (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GC0 GCC CR; lia|]. apply (rep_nolazy_tctx bt st Lc FF M0 mdl W RP). exact Hz. }
    assert (NHH1 : forall z, h <= z < h + msz -> Hd1 (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz G1 G2 CR; lia|]. apply (rep_nolazy_sec bt st Lc FF M0 mdl W RP s z Hs). rewrite <- Eh, <- Emsz. exact Hz. }
    assert (HOstk1 : hid_off Hd1 (U S - 2512) 112).
    { apply hid_off_of. intros z Hz. split; [clear - Hz HSr Slo CR; lia | apply NHs1; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]]. }
    assert (HOT21 : hid_off Hd1 (T + 2888) 16).
    { apply hid_off_of. intros z Hz. split; [clear - Hz GT0 GTC CR; lia | apply NHT1; clear - Hz; lia]. }
    assert (HOFF1 : H_off_segments BSEGS Hd1).
    { intros a Ha. unfold Hd1 in Ha. apply HID_lazy in Ha. pose proof (u64_range a) as Ra.
      destruct (lazy_zone bt st mdl (U a) R13 ltac:(clear - Ra; lia) Ha) as [Z1 Z2]. rewrite BT_ia in Z2. cbn [ia_img_lo ia_img_hi both_addrs] in Z2.
      destruct (find_segment BSEGS (U a) 1) eqn:E; [|reflexivity]. exfalso. apply Z2. apply asanF_segs_hull. rewrite E. discriminate. }
    assert (AW1 : A_wf (a_aa st1)) by (cbv delta [st1]; (lazymatch goal with |- ?G => let G' := eval cbn [a_aa op_sec_release] in G in change_no_check G' end); apply A_wf_release; [rewrite Ens; clear - G8; lia | exact B1]).
    (* [comment removed for export] *)
    rewrite PC0 in RUNA.
    eapply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) (@mkst fx R _ M (seg_rom BSEGS)) _ mdl);
      [ apply lazy_cover_HID | exact B1 | exact B2 | exact HH | rewrite restrict_mkstK; exact RUNA | ].
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    (lazymatch goal with |- ?G => let G' := eval cbn [ms_mem mkst] in G in change_no_check G' end).
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _).
    (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end).
    rewrite (fr_sA_mr Hd M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24
               P_GS P_GT P_Gh8 P_Gi P_Gptr P_Glast HOstk HOinst HOT HOslot HOlast HOsh).
    set (M1 := fr_sA M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24).
    assert (OUT1 : forall x : word, outA S T h msz P8 iz last x -> M1 x = M x).
    { intros x OA. exact (fr_sA_out M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24
                            P_GS P_GT P_Gh8 P_Gi P_Gptr P_Glast x OA). }
    assert (OUTH : forall x : word, Hd x = true -> outA S T h msz P8 iz last x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold outA in G in change_no_check G' end).
      pose proof (out_of_hidden Hd _ _ x HOstk Hx) as O1. pose proof (out_of_hidden Hd _ _ x HOinst Hx) as O2. pose proof (out_of_hidden Hd _ _ x HOT Hx) as O3.
      pose proof (out_of_hidden Hd _ _ x HOslot Hx) as O4. pose proof (out_of_hidden Hd _ _ x HOlast Hx) as O5. pose proof (out_of_hidden Hd _ _ x HOsh Hx) as O6.
      fold shlo. repeat split; [clear - O1; lia | clear - O2; lia | clear - O3; lia | clear - O4; lia | clear - O5; lia | clear - O6; lia]. }
    rewrite (munrestrict_same Hd M M1 (fun a Ha => OUT1 a (OUTH a Ha))).
    (* [comment removed for export] *)
    assert (HALT1 : m_halted mdl1 = None) by (rewrite Eh1; exact HH).
    assert (OUTimg : forall x : word, AIMGLO <= U x < AIMGHI -> (U x < 0x10ab98 + 56 \/ 0x10ab58 + 688 + 32 <= U x) -> outA S T h msz P8 iz last x).
    { intros x Hx Hx2. (lazymatch goal with |- ?G => let G' := eval unfold outA in G in change_no_check G' end). fold shlo.
      split; [left; clear - Hx Slo CR; lia|]. split; [exact Hx2|]. split; [clear - Hx GTI; ul|].
      split; [left; clear - Hx PG1 P_Gi; lia|]. split; [left; clear - Hx L9; lia|]. clear - Hx SHB. ul. }
    Ltac cM1 OUT1 OUTimg C := eapply rd_same; [ intros x Hx; apply OUT1; apply OUTimg; revert Hx; clear; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                              | clear; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact C ].
    assert (Uh : U (Z_to_bv 64 h) = h /\ U (Z_to_bv 64 msz) = msz) by (clear - Hrng G5; unorm; split; reflexivity).
    destruct Uh as (Uh & Umsz).
    assert (GR1 : mem_grows M M1) by (apply fr_sA_grows).
    assert (FLH : flushH BSEGS both_flush_tab M1 (Z_to_bv 64 h) (Z_to_bv 64 msz) (at_ S (-2432)) (Z_to_bv 64 MIDEND)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ft_mt ft_g_pgsz ft_p_pgsz ft_g_seal ft_sv both_flush_tab] in G in change_no_check G' end).
      - split; (lazymatch goal with |- ?G => let G' := eval cbn [AsRtM2S.mt_g_shoff AsRtM2S.mt_p_shoff AsRtM2S.mt_g_midbeg AsRtM2S.mt_p_midbeg AsRtM2S.mt_g_midend AsRtM2S.mt_p_midend AsRtM2S.mt_g_hiend AsRtM2S.mt_p_hiend BoRtXStrlenI.BoRtM2SI.both_m2s_tab_6dffc] in G in change_no_check G' end).
        + cM1 OUT1 OUTimg C_gsh. + cM1 OUT1 OUTimg C_sh. + cM1 OUT1 OUTimg C_gmb. + cM1 OUT1 OUTimg C_mb.
        + cM1 OUT1 OUTimg C_gme. + cM1 OUT1 OUTimg C_me. + cM1 OUT1 OUTimg C_ghe. + cM1 OUT1 OUTimg C_he.
        + (lazymatch goal with |- ?G => let G' := eval unfold AsRtM2S.m2s_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [AsRtM2S.mt_g_shoff AsRtM2S.mt_p_shoff AsRtM2S.mt_g_midbeg AsRtM2S.mt_p_midbeg AsRtM2S.mt_g_midend AsRtM2S.mt_p_midend AsRtM2S.mt_g_hiend AsRtM2S.mt_p_hiend BoRtXStrlenI.BoRtM2SI.both_m2s_tab_6dffc] in G in change_no_check G' end).
          repeat constructor; lia.
        + rewrite Uh. clear - G10 G5. ul.
        + rewrite Uh. clear - G2 G5 CR. lia.
      - rewrite Uh, Umsz. clear - G10 G2 G5 CR. ul.
      - cM1 OUT1 OUTimg C_gpgc.
      - cM1 OUT1 OUTimg C_pgc.
      - cM1 OUT1 OUTimg C_seal.
      - rewrite both_flush_cells. rewrite at_u by (clear - HSr Slo CR; lia). repeat constructor; clear - Slo CR; lia.
      - rewrite at_u by (clear - HSr Slo CR; lia). clear - Slo CR. lia.
      - rewrite at_at. change (-2432 + -32) with (-2464).
        eapply store_ok_mono; [exact GR1|].
        assert (SOKM : store_ok BSEGS M (at_ S (-2512)) 112 = true).
        { replace (at_ S (-2512)) with (Z_to_bv 64 (U S - 2512) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
          apply store_ok_bytes; [| clear - HSr Slo CR; wd_ulia_c]. intros x Hx. apply (proj2 (SOK x ltac:(clear - Hx HSr Slo CR; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia))). }
        eapply (store_ok_sub BSEGS M (at_ S (-2512)) _ 112); [clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact SOKM | clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | clear - HSr Slo CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    assert (RET_F : ret_ok (Z_to_bv 64 0x4ef70)) by (apply ret_ok_lit; [lia | reflexivity]).
    pose proof (fl_geom_t (Z_to_bv 64 h) (Z_to_bv 64 msz) (fh_end _ _ _ _ _ _ _ FLH)) as FG. unfold fl_sb, fl_se in FG. rewrite Uh, Umsz in FG.
    replace ((h + msz) / 8 + 2147450880) with (shlo + msz / 8) in FG by ((lazymatch goal with |- ?G => let G' := eval unfold shlo in G in change_no_check G' end); clear - SH8h SH8m; Z.div_mod_to_equations; lia).
    replace (h / 8 + 2147450880) with shlo in FG by ((lazymatch goal with |- ?G => let G' := eval unfold shlo in G in change_no_check G' end); clear; lia).
    set (pb := fl_pb (Z_to_bv 64 h)) in *. set (pe := fl_pe (Z_to_bv 64 h) (Z_to_bv 64 msz)) in *.
    destruct FG as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    assert (PBE : pb < pe /\ shlo <= pb /\ pe <= shlo + msz / 8 /\ 8192 <= msz / 8) by (clear - F4 F5 F6 F7 G5; Z.div_mod_to_equations; lia).
    destruct PBE as (PBE1 & PBE2 & PBE3 & PBE4).
    rewrite PCF.
    apply (both_flush_katD2 Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx Hd1 HOFF1 (a_aa st) (a_aa st1) rA M1 (seg_rom BSEGS) mdl1   (* [comment removed for export] *)
             (Z_to_bv 64 h) (Z_to_bv 64 msz) (Z_to_bv 64 0x4ef70) (at_ S (-2432)) (Z_to_bv 64 MIDEND) _ FLH RET_F A1 A2 A10 A11).
    { rewrite both_flush_cells. repeat constructor; apply hid_off_of; intros z Hz; (split; [clear - Hz; lia | apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]). }
    { rewrite at_u by (clear - HSr Slo CR; lia). eapply hid_off_sub; [exact HOstk | clear; lia | clear; lia]. }
    { exact HALT1. }
    { rewrite Elz1. apply lazy_cover_HID. }
    { exact B1. }
    { exact MI1. }
    { (* [comment removed for export] *)
      intros _ mdlm SBMm MIm. fold pb pe.
      apply (SHGATE st Lc FF M0 mdl mdlm qt qg pb (pe - pb) W RP (same_but_materialized_trans _ _ _ SBM1 SBMm) MIm
               (model_ivs_wf_sbm _ _ (same_but_materialized_trans _ _ _ SBM1 SBMm) MW)).
      - exact F8.
      - clear - F8 F9. Z.div_mod_to_equations. lia.
      - clear - PBE1. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold SB, AS_GAPLO, AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). clear - SHB PBE2 PBE3 PBE1. ul. }
    { (* [comment removed for export] *) exact AW1. }
    { (* [comment removed for export] *) rewrite Elz1. apply lazy_cover_HID. }
    { (* [comment removed for export] *)
      intros HLT mdlm SBMm MIm. fold pb pe. cbv delta [st1]. (lazymatch goal with |- ?G => let G' := eval cbn [a_aa op_sec_release] in G in change_no_check G' end).
      assert (Epb : pb = sec_inner_lo h).
      { (lazymatch goal with |- ?G => let G' := eval unfold sec_inner_lo, pgup, sh_lo, SB, PG in G in change_no_check G' end). unfold shlo in F4, F5. clear - F4 F5 F8. Z.div_mod_to_equations. lia. }
      assert (Epe : pe = sec_inner_hi h (sc_n s)).
      { (lazymatch goal with |- ?G => let G' := eval unfold sec_inner_hi, pgdn, sh_hi, SB, PG in G in change_no_check G' end). replace (sec_map_size (sc_n s)) with msz by (rewrite Emsz; reflexivity).
        rewrite SHs. unfold shlo in F6, F7. clear - F6 F7 F9. Z.div_mod_to_equations. lia. }
      assert (Rpb : 0 <= pb /\ pe < 2 ^ 64) by (unfold shlo in PBE2, PBE3; clear - PBE1 PBE2 PBE3 G1 G2 G5 CR SH8h SH8m; lia).
      apply (MInv_release_madvise (a_aa st) h (sc_n s) mdlm (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb))).
      - rewrite Ens. clear - G8. lia.
      - exact B1.
      - pose proof (B9 s Hs) as HIN. rewrite <- Eh in HIN. exact HIN.
      - exact MIm.
      - rewrite u_Z2bv by (clear - Rpb PBE1; lia). exact Epb.
      - rewrite !u_Z2bv by (clear - Rpb PBE1; lia). rewrite <- Epe. clear. lia. }
    2:{ (* [comment removed for export] *) intros HGE. exfalso. fold pb pe in HGE. clear - HGE PBE1. lia. }
    intros _ rF mdlm mdl4 SBMm MIm SBM4 MI4 E1F E2F E10F AGF. fold pb pe in SBM4 |- *.
    (* [comment removed for export] *)
    try clear OUTH. try clear HOsh. try clear NHSH. clear NHs NHT NHC NHH HOstk HOT2. try clear HOinst. try clear HOT. try clear HOslot. try clear HOlast. try clear NHL. try clear NHP.
    rename Hd into Hd0. rename Hd1 into Hd. rename NHs1 into NHs. rename NHT1 into NHT. rename NHC1 into NHC. rename NHH1 into NHH.
    rename HOstk1 into HOstk. rename HOT21 into HOT2.
    rewrite A8, A9, A18.
    change (zfill (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb)) (fl_frame M1 (at_ S (-2432)) (Z_to_bv 64 0x4ef70) (Z_to_bv 64 h) (Z_to_bv 64 h) (Z_to_bv 64 msz)))
      with (mz_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 pb (pe - pb)).
    set (MZ := mz_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 pb (pe - pb)).
    (* [comment removed for export] *)
    assert (SBMn : same_but_materialized mdlm (madvise_dontneed_next mdlm (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb)))) by ((lazymatch goal with |- ?G => let G' := eval unfold madvise_dontneed_next in G in change_no_check G' end); apply with_vm_backing_same).
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBMm) SBMn) SBM4) as SBM04.
    pose proof (same_but_materialized_frame mdl mdl4 SBM04) as SF4.
    destruct SF4 as (_ & Evm4 & Elz4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh4 & _).
    (* [comment removed for export] *)
    assert (P_Gpb : shlo <= pb /\ pb + (pe - pb) <= shlo + msz / 8 /\ 0 <= pe - pb) by (clear - PBE1 PBE2 PBE3; lia).
    Ltac feedK H := repeat (let T := type of H in lazymatch T with ?A -> _ => let a := fresh in assert (a : A) by assumption; specialize (H a); clear a end).
    assert (OUTZ : forall x : word, outA S T h msz P8 iz last x -> MZ x = M x).
    { pose proof (mz_out M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 pb (pe - pb)) as F. feedK F. exact F. }
    assert (GRZ : mem_grows M MZ) by (apply mz_grows).
    assert (OUTctx : forall x : word, CTX <= U x < CTX + 65536 -> outA S T h msz P8 iz last x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold outA in G in change_no_check G' end). fold shlo.
      split; [left; clear - Hx GCC Slo; lia|]. split; [clear - Hx GCI; ul|]. split; [clear - Hx GCT'; ul|].
      split; [clear - Hx PG7 P_Gi PG8; unfold len in *; ul|]. split; [clear - Hx L13 L5; ul|]. clear - Hx SHB GCB. ul. }
    assert (OUTh : forall x : word, h <= U x < h + 16 -> outA S T h msz P8 iz last x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold outA in G in change_no_check G' end). fold shlo.
      split; [left; clear - Hx G2 G5 Slo; lia|]. split; [right; clear - Hx G9; lia|]. split; [clear - Hx G12 G5; ul|].
      split; [clear - Hx P_GptrH P_Gi G5; ul|]. split; [clear - Hx P_GlastH G5; ul|]. clear - Hx SHB G10 G5. ul. }
    set (memZ := mrestrict Hd MZ).
    Ltac toZ_img Hd M MZ OUTZ OUTimg NHs C := apply (rdRw Hd M MZ _ _ _ C); [unorm; czl | intros x Hx; apply OUTZ; apply OUTimg; revert Hx; clear; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                            | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]].
    assert (Z_kif : rdn BSEGS memZ (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]) by toZ_img Hd M MZ OUTZ OUTimg NHs C_kif.
    assert (Z_key : rdn BSEGS memZ (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0)).
    { apply (rdRw Hd M MZ _ _ _ C_key); [rewrite Ukey; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply OUTZ; apply OUTimg; revert Hx; rewrite Ukey; clear; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                       | rewrite Ukey; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]. }
    assert (Z_tsdp : rdn BSEGS memZ (at_ tpv (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { apply (rdRw Hd M MZ _ _ _ C_tsdp); [rewrite Utp88; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply OUTZ; apply OUTimg; revert Hx; rewrite Utp88; clear; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                        | rewrite Utp88; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]]. }
    assert (Z_tctx : rdn BSEGS memZ (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))).
    { apply (rdRw Hd M MZ _ _ _ C_tctx); [rewrite Utsdp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc2; lia
        | intros x Hx; apply OUTZ; apply OUTimg; revert Hx; rewrite Utsdp; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; [clear - Hx Gc1 Gc2; lia | clear - Hx G_tsdp2; ul]
        | rewrite Utsdp; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz Gc1 Gc2; lia | right; clear - Hz Gc1 Gc2; lia]]. }
    assert (Z_thr : rdn BSEGS memZ (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { apply (rdRw Hd M MZ _ _ _ C_thr); [rewrite Uctx152; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GCC CR; lia | intros x Hx; apply OUTZ; apply OUTctx; revert Hx; rewrite Uctx152; clear; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                       | rewrite Uctx152; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHC; clear - Hz; lia]. }
    assert (Z_mbh : rdn BSEGS memZ (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h))).
    { apply (rdRw Hd M MZ _ _ _ C_mbh); [rewrite Uh; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G5; lia | intros x Hx; apply OUTZ; apply OUTh; revert Hx; rewrite Uh; clear; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                       | rewrite Uh; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHH; clear - Hz G5; lia]. }
    assert (Uh8 : U (Z_to_bv 64 (h + 8)) = h + 8) by (clear - Hrng G5; unorm; reflexivity).
    assert (Z_msz : rdn BSEGS memZ (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz))).
    { apply (rdRw Hd M MZ _ _ _ C_msz); [rewrite Uh8; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hrng G5; lia | intros x Hx; apply OUTZ; apply OUTh; revert Hx; rewrite Uh8; clear; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                       | rewrite Uh8; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHH; clear - Hz G5; lia]. }
    (* [comment removed for export] *)
    pose proof (mz_frame M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 pb (pe - pb)) as FRZ. feedK FRZ. destruct FRZ as (FZ_ra & FZ_s0 & FZ_s1 & FZ_s2).
    Ltac toZ_stk Hd MZ NHs G C := apply (rdRw Hd MZ MZ _ _ _ C); [clear - G; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x _; reflexivity
                                  | rewrite at_u by (clear - G; lia); (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz G; lia | left; clear - Hz G; lia]].
    pose proof (conj HSr (conj Slo (conj Shi CR))) as GSTK.
    assert (Z_ra : rdn BSEGS memZ (at_ S (-2408)) 8 = Some (LE8 ret)) by toZ_stk Hd MZ NHs GSTK FZ_ra.
    assert (Z_s0 : rdn BSEGS memZ (at_ S (-2416)) 8 = Some (LE8 s0v)) by toZ_stk Hd MZ NHs GSTK FZ_s0.
    assert (Z_s1 : rdn BSEGS memZ (at_ S (-2424)) 8 = Some (LE8 s1v)) by toZ_stk Hd MZ NHs GSTK FZ_s1.
    assert (Z_s2 : rdn BSEGS memZ (at_ S (-2432)) 8 = Some (LE8 s2v)) by toZ_stk Hd MZ NHs GSTK FZ_s2.
    assert (TDEFZ : forall z, T <= z < T + 4096 -> memZ (Z_to_bv 64 z) <> None).
    { intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold memZ in G in change_no_check G' end). rewrite mrestrict_off by (apply NHT; exact Hz). apply GRZ. exact (TDEF z Hz). }
    destruct (rdn_defined_ex BSEGS memZ (Z_to_bv 64 (T + 2888)) 8) as (bu0 & Cu0 & Lu0);
      [intros z Hz; apply TDEFZ; clear - Hz GT0 GTC CR; revert Hz; unorm; intros Hz; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memZ (Z_to_bv 64 (T + 2896)) 8) as (bu1 & Cu1 & Lu1);
      [intros z Hz; apply TDEFZ; clear - Hz GT0 GTC CR; revert Hz; unorm; intros Hz; lia | clear - GT0 GTC CR; wd_ulia |].
    assert (SOKM : store_ok BSEGS M (at_ S (-2512)) 112 = true).
    { replace (at_ S (-2512)) with (Z_to_bv 64 (U S - 2512) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply store_ok_bytes; [| clear - HSr Slo CR; wd_ulia_c]. intros x Hx. apply (proj2 (SOK x ltac:(clear - Hx HSr Slo CR; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia))). }
    assert (SOKstkZ : store_ok BSEGS memZ (at_ S (-2512)) 112 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold memZ in G in change_no_check G' end). rewrite store_ok_mrestrict; [eapply store_ok_mono; [exact GRZ | exact SOKM] | clear - GSTK; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by (clear - GSTK; lia); exact HOstk]. }
    assert (SOKTZ : store_ok BSEGS memZ (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { apply (sokX Hd MZ M0 _ _ T _ TW (mem_grows_trans _ _ _ GR0 GRZ)); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - GTC CR; lia | clear - GT0; lia |].
      intros z Hz. apply NHT. clear - Hz. cbn in Hz. lia. }
    assert (P_GhB : AIMGHI <= h /\ 4096 <= msz /\ h + msz <= U S - 3584) by (clear - P_Gh; lia).
    assert (P_GtpB : AIMGLO + 88 <= U tpv /\ U tpv + 8 <= AIMGHI) by (rewrite Utp; clear; lia).
    assert (P_GtsdpB : AIMGLO <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= AIMGHI) by (rewrite Utsdp; clear - Gc1 Gc2; lia).
    Ltac viaF AGF A := lazymatch type of A with getr _ ?k = _ => rewrite (AGF k) by ((lazymatch goal with |- ?G => let G' := eval unfold AsRtM2S.m2s_clob in G in change_no_check G' end); notin); exact A end.
    assert (F8r : getr rF _ = Z_to_bv 64 h) by viaF AGF A8.
    assert (F18r : getr rF _ = Z_to_bv 64 msz) by viaF AGF A18.
    assert (F4r : getr rF _ = tpv) by viaF AGF A4.
    destruct (run_sB memZ (seg_rom BSEGS) rF S ret s0v s1v s2v tpv (Z_to_bv 64 TSDP) T CTX h msz bu0 bu1
                E2F F8r F18r F4r P_GS P_GhB P_GTt P_Gctx P_GtpB P_GtsdpB SOKstkZ SOKTZ
                Z_kif Z_key Z_tsdp Z_tctx Z_thr Cu0 Lu0 Cu1 Lu1 Z_mbh Z_msz Z_ra Z_s0 Z_s1 Z_s2)
      as (rB & RUNB & UR & B4r).
    set (k0 := at_ (Z_to_bv 64 (bytes_le_to_Z bu0)) 1) in *. set (k1 := v_add (Z_to_bv 64 (bytes_le_to_Z bu1)) (Z_to_bv 64 msz)) in *.
    assert (HALT4 : m_halted mdl4 = None) by (rewrite Eh4; exact HH).
    rewrite PC1 in RUNB.
    eapply (katD_msteps_acct BSEGS Hd HOFF1 asanF_segs_wx (a_aa st1) (@mkst fx rF _ MZ (seg_rom BSEGS)) _ mdl4);
      [ rewrite Elz4; apply lazy_cover_HID | exact AW1 | exact MI4 | exact HALT4 | rewrite restrict_mkstK; exact RUNB | ].
    intros mdl5 MI5 SBM5 HC5. rewrite unrestrict_mkst.
    (lazymatch goal with |- ?G => let G' := eval cbn [ms_mem mkst] in G in change_no_check G' end).
    pose proof (same_but_materialized_trans _ _ _ SBM04 SBM5) as SBM05.
    pose proof (same_but_materialized_frame mdl mdl5 SBM05) as SF5.
    destruct SF5 as (_ & Evm5 & Elz5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh5 & _).
    (lazymatch goal with |- ?G => let G' := eval unfold memZ in G in change_no_check G' end). rewrite (fr_sB_mr Hd MZ S ret s0v s1v s2v T k0 k1 P_GS P_GT HOstk HOT2).
    set (M5 := fr_sB MZ S ret s0v s1v s2v T k0 k1).
    assert (OUT5H : forall x : word, Hd x = true -> M5 x = MZ x).
    { intros x Hx. pose proof (out_of_hidden Hd _ _ x HOstk Hx) as O1. pose proof (out_of_hidden Hd _ _ x HOT2 Hx) as O2.
      apply (fr_sB_out MZ S ret s0v s1v s2v T k0 k1 P_GS P_GT x); [clear - O1; lia | clear - O2; lia]. }
    rewrite (munrestrict_same Hd MZ M5 OUT5H).
    (* [comment removed for export] *)
    unfold um1_regs in UR. destruct UR as (U1 & U2 & U10 & U11 & U17 & U8 & U9 & U18 & U3 & U4 & U19 & U20 & U21 & U22 & U23 & U24 & U25 & U26 & U27).
    assert (HALT5 : m_halted mdl5 = None) by (rewrite Eh5; exact HH).
    pose proof (proj1 (proj2 BOOTG)) as NS.
    assert (MAPHAS : map_has (vm_maps (m_vmmaps mdl5)) (Z_to_bv 64 h) (Z_to_bv 64 msz) = true).
    { rewrite Evm5, Eh, Emsz. exact (AsKSys8.sec_map_has bt st Lc FF M0 mdl s W RP Hs). }
    apply (katD_ecall_munmap BSEGS rB _ M5 (seg_rom BSEGS) mdl5 _ (Z_to_bv 64 h) msz _ F_811b8 E_811b8 HALT5 U17 U10).
    { rewrite Uh. exact G3. } { exact U11. } { clear - G5; lia. } { exact G4. } { rewrite Uh. clear - G2 CR. lia. } { exact MAPHAS. }
    rewrite PC2.
    change (unfill (Z_to_bv 64 h) (Z_to_bv 64 msz) M5)
      with (mu_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)).
    set (MU := mu_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)).
    set (mdlU := munmap_model (Z_to_bv 64 h) (Z_to_bv 64 msz) mdl5).
    (* [comment removed for export] *)
    assert (EKV : m_vmmaps mdl5 = m_vmmaps mdl) by exact Evm5.
    assert (EKL : m_vm_lazy mdl5 = m_vm_lazy mdl) by exact Elz5.
    assert (MIU : MInv (a_aa st1) mdlU).
    { (lazymatch goal with |- ?G => let G' := eval unfold mdlU in G in change_no_check G' end). rewrite Eh, Emsz. exact (AsKSys8.child_MInv bt st Lc FF M0 mdl s W RP MW Hs NS (a_aa st1) mdl5 EKV EKL MI5). }
    assert (HALTU : m_halted mdlU = None) by ((lazymatch goal with |- ?G => let G' := eval unfold mdlU in G in change_no_check G' end); rewrite munmap_model_halted; exact HALT5).
    assert (LCU : lazy_cover Hd (m_vm_lazy mdlU) (a_aa st1)).
    { apply (lazy_cover_of_iff Hd (m_vm_lazy mdl) (m_vm_lazy mdlU)); [| apply lazy_cover_HID].
      pose proof (AsKSys8.secfree_ledger bt st Lc FF M0 mdl s W RP MW Hs NS mdl5 (munmap_model (Z_to_bv 64 (sc_map s)) (Z_to_bv 64 (sc_mapsz s)) mdl5) EKV EKL (same_but_materialized_refl _)) as LG.
      rewrite <- Eh, <- Emsz in LG. exact (proj1 (proj2 (proj2 LG))). }
    (* [comment removed for export] *)
    set (memU := mrestrict Hd MU).
    assert (OUTU : forall x : word, outA S T h msz P8 iz last x -> (U x < T + 2888 \/ T + 2904 <= U x) -> (U x < h \/ h + msz <= U x) -> MU x = M x).
    { pose proof (mu_out M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as F. feedK F. exact F. }
    Ltac toU_img Hd M MU OUTU OUTimg NHs GI C := apply (rdRw Hd M MU _ _ _ C); [unorm; czl
        | intros x Hx; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; apply OUTU; [apply OUTimg; clear - Hx; lia | clear - Hx GI; ul | clear - Hx GI; ul]
        | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros z Hz; apply NHs; [clear - Hz; lia | right; clear - Hz; lia]].
    pose proof (conj GTI G9) as GIU.
    assert (U_gcf : rdn BSEGS memU (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8))) by toU_img Hd M MU OUTU OUTimg NHs GIU C_gcf.
    assert (U_lim : rdn BSEGS memU (Z_to_bv 64 (0x19fce8 + 144)) 8 = Some (LE8 (Z_to_bv 64 0))) by toU_img Hd M MU OUTU OUTimg NHs GIU C_lim.
    pose proof (mu_frame M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FRU. feedK FRU. destruct FRU as (FU_ra & FU_s0 & FU_s1 & FU_s2).
    assert (U_ra : rdn BSEGS memU (at_ S (-2408)) 8 = Some (LE8 ret)) by toZ_stk Hd MU NHs GSTK FU_ra.
    assert (U_s0 : rdn BSEGS memU (at_ S (-2416)) 8 = Some (LE8 s0v)) by toZ_stk Hd MU NHs GSTK FU_s0.
    assert (U_s1 : rdn BSEGS memU (at_ S (-2424)) 8 = Some (LE8 s1v)) by toZ_stk Hd MU NHs GSTK FU_s1.
    assert (U_s2 : rdn BSEGS memU (at_ S (-2432)) 8 = Some (LE8 s2v)) by toZ_stk Hd MU NHs GSTK FU_s2.
    assert (SOKstkU : store_ok BSEGS memU (at_ S (-2448)) 48 = true).
    { pose proof (mu_stk M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as F. feedK F.
      (lazymatch goal with |- ?G => let G' := eval unfold memU in G in change_no_check G' end). rewrite store_ok_mrestrict; [| clear - GSTK; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by (clear - GSTK; lia); eapply hid_off_sub; [exact HOstk | clear; lia | clear; lia]].
      eapply (store_ok_sub BSEGS MU (at_ S (-2512)) _ 112); [clear - GSTK; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact F | clear - GSTK; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | clear - GSTK; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    assert (P_GS24 : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47 + 256) by (clear - P_GS; lia).
    match goal with |- context [regupd rB ?k ?v] => set (rU := regupd rB k v) end.
    destruct (um2_run memU (seg_rom BSEGS) S ret s0v s1v s2v msz rU) as (rC & RUNC & URC); try assumption.
    { (lazymatch goal with |- ?G => let G' := eval unfold rU in G in change_no_check G' end). rewrite getr_other by (intros E; discriminate E). exact U1. }
    { (lazymatch goal with |- ?G => let G' := eval unfold rU in G in change_no_check G' end). rewrite getr_other by (intros E; discriminate E). exact U2. }
    { (lazymatch goal with |- ?G => let G' := eval unfold rU in G in change_no_check G' end). rewrite getr_same by (intros E; discriminate E). reflexivity. }
    { (lazymatch goal with |- ?G => let G' := eval unfold rU in G in change_no_check G' end). rewrite getr_other by (intros E; discriminate E). exact U8. }
    rewrite PC3 in RUNC.
    eapply (katD_msteps_acct BSEGS Hd HOFF1 asanF_segs_wx (a_aa st1) (@mkst fx rU _ MU (seg_rom BSEGS)) _ mdlU);
      [ exact LCU | exact AW1 | exact MIU | exact HALTU | rewrite restrict_mkstK; exact RUNC | ].
    intros mdl6 MI6 SBM6 HC6. rewrite unrestrict_mkst.
    (lazymatch goal with |- ?G => let G' := eval cbn [ms_mem mkst] in G in change_no_check G' end).
    (lazymatch goal with |- ?G => let G' := eval unfold memU in G in change_no_check G' end). rewrite (fr_um2_mr Hd S P_GS HOstk MU).
    assert (OUT6H : forall x : word, Hd x = true -> fr_um2 MU S x = MU x).
    { intros x Hx. pose proof (out_of_hidden Hd _ _ x HOstk Hx) as O1. apply (fr_um2_out S P_GS MU x). clear - O1. lia. }
    rewrite (munrestrict_same Hd MU (fr_um2 MU S) OUT6H).
    change (fr_um2 MU S) with (fin_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)).
    set (MF := fin_mem M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)).
    (* [comment removed for export] *)
    pose proof (fin_out M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FOUT. feedK FOUT.
    pose proof (fin_def M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FDEF. feedK FDEF.
    pose proof (fin_foot M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FFOOT. feedK FFOOT.
    pose proof (fin_nch M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FNCH. feedK FNCH.
    pose proof (fin_lock M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FLOCK. feedK FLOCK.
    pose proof (fin_slot M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FSLOT. feedK FSLOT.
    pose proof (fin_idx M S ret s0v s1v s2v s3v s4v x21 cbw b1 b2 b3 m T h msz len P8 iz last j0 j1 wnf wca w16 w24 k0 k1 pb (pe - pb)) as FIDX. feedK FIDX.
    fold MF in FOUT, FDEF, FFOOT, FNCH, FLOCK, FSLOT, FIDX.
    assert (SBM6' : same_but_materialized (munmap_model (Z_to_bv 64 (sc_map s)) (Z_to_bv 64 (sc_mapsz s)) mdl5) mdl6) by (rewrite <- Eh, <- Emsz; exact SBM6).
    pose proof (AsKSys8.secfree_perm bt st Lc FF M0 mdl s W RP Hs mdl5 mdl6 EKV EKL SBM6') as PM.
    pose proof (AsKSys8.secfree_ledger bt st Lc FF M0 mdl s W RP MW Hs NS mdl5 mdl6 EKV EKL SBM6') as (LNA & LNP & LLZ & LFL & LE1 & LE2 & LE3 & LE4 & LE5 & LE6).
    pose proof (AsKSys8.secfree_eager bt st Lc FF M0 mdl s W RP MW Hs NS mdl5 mdl6 EKV EKL SBM6') as EAG.
    pose proof (AsKSys8.child_wf bt st Lc FF M0 mdl s W RP MW Hs NS mdl5 mdl6 EKV EKL SBM6') as MW6.
    pose proof (same_but_materialized_frame mdlU mdl6 SBM6) as SF6.
    destruct SF6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh6 & _).
    (* [comment removed for export] *)
    assert (FOOTLO : forall a : word, MF a <> M a -> U a < U S - 2400).
    { intros a NE. destruct (FFOOT a NE) as [F|[F|[F|[F|[F|[F|[F|F]]]]]]];
        [clear - F; lia | clear - F Slo CR; lia | clear - F GTC Slo; lia | clear - F GTC Slo; lia | clear - F P_Gptr P_Gi; lia | clear - F P_Glast; lia | clear - F P_GshS; lia | clear - F P_Gh; lia]. }
    pose proof W as WL. rewrite ELc in WL.
    assert (W' : WFq bt (op_sec_free st i) (La ++ Lb) FF qt qg) by exact (AsAinvOpsRc94.AsAinvOpsRc93.OPS_WFq_sec_free_live_pf bt st La Lb FF (m + 16) n i s qt qg WL HP Hnth Eus).
    assert (RXL : AsAinvOpsRc73.AsAinvRepX3.RepX bt X st (La ++ (m + 16, n) :: Lb) FF M mdl) by (rewrite <- ELc; exact (ex_intro _ M0 (conj RP DX))).
    assert (RP' : Rep bt (op_sec_free st i) (La ++ Lb) FF MF mdl6).
    { apply (AsAinvOpsRc94.OPS_REPX_sec_free_live_pf bt X st La Lb FF M MF mdl mdl6 (m + 16) n i s qt qg WL RXL XSUBL HP Hnth Eus).
      - intros a NE. split; [| rewrite <- Eh, <- Emsz; exact (FDEF a NE)]. (lazymatch goal with |- ?G => let G' := eval unfold foot_recycle_sec, idx_lo, idx_hi in G in change_no_check G' end). rewrite Hnl.
        (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). rewrite <- Eh, <- Emsz, <- Elast. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end). rewrite SHs. fold iz.
        destruct (FFOOT a NE) as [F|[F|[F|[F|[F|[F|[F|F]]]]]]].
        + do 6 right. clear - F Slo. lia.
        + left. clear - F. lia.
        + do 5 right. left. clear - F. lia.
        + do 5 right. left. clear - F. lia.
        + right. left. exact F.
        + right. right. left. clear - F. lia.
        + do 4 right. left. unfold shlo in F. clear - F. lia.
        + do 3 right. left. exact F.
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). fold len. exact FNCH.
      - (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). rewrite w2b1 by (clear; lia). exact FLOCK.
      - intros sl' Hlt Hnl'. rewrite Hnl in Hnl'. injection Hnl' as <-. rewrite <- Elast. fold iz. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs.
        split; [exact FSLOT|]. apply FIDX. intros E. subst last.
        assert (s = sl) by (apply (AsAinvFrame3.NoDup_map_inj sc_map (a_sec st) s sl); [destruct W as (_ & _ & _ & (_ & _ & _ & _ & ND & _) & _); exact ND | exact Hs | exact Hsl | rewrite <- Eh; symmetry; exact E]).
        subst sl. pose proof W as (_ & _ & _ & (_ & _ & _ & _ & ND & _) & _). apply NoDup_map_inv in ND.
        pose proof (proj1 (NoDup_nth_error (a_sec st)) ND i (length (a_sec st) - 1)%nat Hlen ltac:(rewrite Hnth, Hnl; reflexivity)) as EI.
        fold len in Hlt. unfold len in Hlt. clear - EI Hlt Hlen. lia.
      - exact PM. - exact LNA. - exact LNP. - exact LLZ. - exact LFL. - exact LE1. - exact LE2. - exact LE3. - exact LE4. - exact LE5. - exact LE6.
      - cbv delta [st1] in MI6. cbn [a_aa op_sec_release] in MI6. rewrite Eh in MI6. exact MI6.   (* [comment removed for export] *)
      - exact EAG. }
    (* [comment removed for export] *)
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold sec_live_post in G in change_no_check G' end). exists fx, i, MF, mdl6, rC.
    split; [reflexivity|]. split; [exact HFX|]. split; [rewrite Eh6; exact HALTU|]. split; [exact MW6|].
    split; [exact W'|]. split; [exact RP'|].
    split.
    { intros a Ha. destruct (decide (MF a = M a)) as [E|NE]; [exact E|]. exfalso. pose proof (FOOTLO a NE) as N2. clear - Ha N2. lia. }
    split.
    { intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold rc_changed in G in change_no_check G' end).
      assert (PRIVI : forall z, 0x10ab58 <= z < 0x10b9b8 -> in_wins (ia_priv (bt_ia bt)) z).
      { intros z Hz. rewrite BT_ia. exists 0x10ab58, 0x10b9b8. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | exact Hz]. }
      assert (IMGLO' : ia_img_lo (bt_ia bt) <= 65536) by (rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
      assert (SUBL : forall x, In x (La ++ Lb) -> In x Lc) by (intros x Hx; exact (proj1 (post_lists bt st Lc FF W La Lb (m + 16) n ELc x Hx))).
      destruct (FFOOT a NE) as [F|[F|[F|[F|[F|[F|[F|F]]]]]]].
      - split; [left; clear - F; lia | left; destruct (FDEF a NE) as [D|D]; [exact D | exfalso; clear - F D P_Gh; lia]].
      - split; [right; right; apply PRIVI; clear - F; lia | left; destruct (FDEF a NE) as [D|D]; [exact D | exfalso; clear - F D G9; lia]].
      - split; [right; left; apply (rt_priv_sub _ Lc _ FF _ SUBL); apply (OBL_rt_private_pf bt st Lc FF W (U a)); left; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); clear - F; lia | left; destruct (FDEF a NE) as [D|D]; [exact D | exfalso; clear - F D G12; ul]].
      - split; [right; left; apply (rt_priv_sub _ Lc _ FF _ SUBL); apply (OBL_rt_private_pf bt st Lc FF W (U a)); left; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); clear - F; lia | left; destruct (FDEF a NE) as [D|D]; [exact D | exfalso; clear - F D G12; ul]].
      - split; [right; left; apply (rt_priv_sub _ Lc _ FF _ SUBL); apply (ptrarr_private bt st Lc FF W (U a)); clear - F P_Gi PG8; unfold len in *; lia | left; destruct (FDEF a NE) as [D|D]; [exact D | exfalso; clear - F D P_GptrH P_Gi; ul]].
      - assert (PL : rt_priv (bt_ia bt) (La ++ Lb) FF (U a)) by (apply (rt_priv_sub _ Lc _ FF _ SUBL); apply (sec_hdr_private bt st Lc FF W IMGLO' sl (U a) Hsl); rewrite <- Elast; clear - F; lia).
        split; [right; left; exact PL | right; exact PL].
      - assert (PS : rt_priv (bt_ia bt) (La ++ Lb) FF (U a)).
        { apply (sec_live_shadow_private bt st Lc FF W IMGLO' La Lb (m + 16) n s (U a) ELc HP Hs Eus Ens). rewrite <- Eh, <- Emsz. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end). unfold shlo in F. exact F. }
        split; [right; left; exact PS | right; exact PS].
      - assert (PC : rt_priv (bt_ia bt) (La ++ Lb) FF (U a)) by (apply (sec_live_private bt st Lc FF W IMGLO' La Lb (m + 16) n s (U a) ELc HP Hs Eus Ens); rewrite <- Eh, <- Emsz; exact F).
        split; [right; left; exact PC | right; exact PC]. }
    split; [intros a _; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); exact (lzb_of_iff _ _ LLZ a)|].
    split.
    { apply (same_except_vm_trans mdl mdl5 mdl6); [apply same_but_materialized_except_vm; exact SBM05|].
      apply (same_except_vm_trans mdl5 mdlU mdl6); [apply munmap_except_vm | apply same_but_materialized_except_vm; exact SBM6]. }
    (* [comment removed for export] *)
    unfold um2_regs in URC. destruct URC as (V2 & V8 & V9 & V18 & V3 & V4 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27).
    Ltac viaR AGF U A := lazymatch type of U with getr _ ?k = _ => rewrite U; rewrite (AGF k) by ((lazymatch goal with |- ?G => let G' := eval unfold AsRtM2S.m2s_clob in G in change_no_check G' end); notin); exact A end.
    Ltac viaC r C := lazymatch type of C with getr _ ?k = _ => rewrite C; (lazymatch goal with |- ?G => let G' := eval unfold r in G in change_no_check G' end); rewrite getr_other by (intros E; discriminate E) end.
    apply regs_kept_intro.
    - rewrite V2. symmetry. exact R2.
    - viaC rU V3. viaR AGF U3 A3.
    - viaC rU V4. viaR AGF U4 A4.
    - exact V8. - exact V9. - exact V18.
    - viaC rU V19. viaR AGF U19 A19.
    - viaC rU V20. viaR AGF U20 A20.
    - viaC rU V21. viaR AGF U21 A21.
    - viaC rU V22. viaR AGF U22 A22.
    - viaC rU V23. viaR AGF U23 A23.
    - viaC rU V24. viaR AGF U24 A24.
    - viaC rU V25. viaR AGF U25 A25.
    - viaC rU V26. viaR AGF U26 A26.
    - viaC rU V27. viaR AGF U27 A27.
  Qed.
End KSL.
