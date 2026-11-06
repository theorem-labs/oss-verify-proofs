(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec StepTac RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VWord2 VState VLogic VGamma VStepMem VStepSound VStepMemSound VCert VContract VState2 VStepMem2 VGamma2 VStepMem2SoundA VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound1_both VContractASound2 VContractASound2_both VContractASound3_both VContractASoundI VContractASound6.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require BothRegionPoisoned BothMemchr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require CatSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VBothIcStrcmpWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac vm_refl := vm_refl_bv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_ISC : Z := 0x44228.            (* [comment removed for export] *)
Definition A_istrcmp : Z := 0x1437e2.       (* [comment removed for export] *)
Definition A_sstrict : Z := 0x1437dd.       (* [comment removed for export] *)

Lemma isc_clob_saved (r : reg) : VBothIcStrcmpWalk.isc_clob r = true -> In (bv_unsigned r) CALLER_SAVED.
Proof.
  unfold VBothIcStrcmpWalk.isc_clob. intros H.
  repeat (apply Bool.orb_prop in H; destruct H as [H|H]);
    unfold bv_eqb in H; apply Z.eqb_eq in H; rewrite H; unfold CALLER_SAVED; cbn; tauto.
Qed.

(* [comment removed for export] *)
Definition cmp_dlt (ua ub : Z) : Z := if ua <? ub then -1 else if ub <? ua then 1 else 0.
Lemma cmpx_dlt ua ub : bv_unsigned (Z_to_bv 64 (VBothIcStrcmpWalk.cmpx ua ub)) = zwrap 64 (cmp_dlt ua ub) /\ -1 <= cmp_dlt ua ub <= 1.
Proof.
  unfold VBothIcStrcmpWalk.cmpx, cmp_dlt. rewrite u_Z_to_bv64.
  destruct (ua <? ub); [|destruct (ub <? ua)]; (split; [vm_compute; reflexivity|lia]).
Qed.

(* [comment removed for export] *)
Section Contracts.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.
  Hypothesis PO2 : params_ok2 BSEGS P.
  Hypothesis SHOFF : vp_shoff P = SBz.
  Hypothesis FSLEN : forall len ssl, vp_fs P = Some (len, ssl) -> FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL < len.
  Hypothesis FS_SOME : vp_fs P <> None.
  Hypothesis FRAME40 : vp_frame (p1 P) < 2 ^ 40.
  (* [comment removed for export] *)
  Hypothesis PRI_GOT1 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_cflags /\ A_GOT_hend + 8 <= phi.
  (* [comment removed for export] *)
  Hypothesis K_shb : In (A_shb, (8, SBz)) (vp_kcells P).
  Hypothesis K_mid1 : In (A_mid1, (8, 0)) (vp_kcells P).
  Hypothesis K_mid2 : In (A_mid2, (8, 0)) (vp_kcells P).
  Hypothesis K_hend : In (A_hend, (8, 2 ^ 47 - 1)) (vp_kcells P).
  Hypothesis K_inited : In (0xb2898, (1, 1)) (vp_kcells P).   (* [comment removed for export] *)
  Hypothesis K_istrcmp : In (A_istrcmp, (1, 1)) (vp_kcells P).
  Hypothesis K_sstrict : In (A_sstrict, (1, 0)) (vp_kcells P).

  #[warnings="-notation-for-abbreviation"] Notation gamma2P := (gamma2 BSEGS P E mem0).

  (* [comment removed for export] *)
  Definition ISC_MCELLS (m : word -> option byte) : Prop := VBothIcStrcmpWalk.isc_cells m.

  Lemma ISC_MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> ISC_MCELLS mem.
  Proof.
    intros A nu regs mem HG2. unfold ISC_MCELLS, VBothIcStrcmpWalk.isc_cells, BothRegionPoisoned.cells, BothRegionPoisoned.cell.
    change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
    change BothRegionPoisoned.SB with SBz. change BothRegionPoisoned.kHighEnd with (2 ^ 47 - 1).
    fold (wordZ 0xa94b8) (wordZ 0xb1bb8) (wordZ 0xa94c0) (wordZ 0xb28a8) (wordZ 0xa94c8) (wordZ 0xb28b0)
         (wordZ 0xa94d0) (wordZ 0xb28a0) (wordZ 0xb2898) (wordZ 0xa94a8) (wordZ 0x1436e8)
         (wordZ 0x1437e2) (wordZ 0x1437dd) (wordZ SBz) (wordZ 0) (wordZ (2 ^ 47 - 1)).
    destruct PRI_GOT1 as (plo & phi & G1 & G2 & G3). unfold A_GOT_cflags, A_GOT_hend in G2, G3.
    repeat split.
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|unfold A_GOT_shb; lia]|exact GOT_shb_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_shb).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|unfold A_GOT_mid1; lia]|exact GOT_mid1_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_mid1).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|unfold A_GOT_mid2; lia]|exact GOT_mid2_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_mid2).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|unfold A_GOT_hend; lia]|exact GOT_hend_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_hend).
    - exact (kcellN P E mem0 A nu regs mem _ _ _ HG2 K_inited).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact GOT_cflags_bytes].
    - exact (kcellN P E mem0 A nu regs mem _ _ _ HG2 K_istrcmp).
    - exact (kcellN P E mem0 A nu regs mem _ _ _ HG2 K_sstrict).
  Qed.

  Lemma shfacts_of mem x K usp :
    (forall g, x / 8 <= g < (x + K) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0)) ->
    (exists b1 : byte, mem (wordZ (SBz + (x + K) / 8)) = Some b1 /\ (bv_unsigned b1 = 0 \/ (x + K) mod 8 < bv_unsigned b1 < 8)) ->
    (forall a, (SBz + x / 8) / 8 * 8 <= a -> a <= (SBz + (x + K) / 8) / 8 * 8 -> a mod 8 = 0 ->
          exists w : word, rdn BSEGS mem (wordZ a) 8 = Some (word_to_le_bytes 8 w)) ->
    SBz + (x + K) / 8 + 8 < usp - JUNK6 ->
    (x + K + 1 <= LOW_MEM_END \/ HIGH_MEM_BEG <= x /\ x + K + 1 <= HIGH_MEM_END - 1) ->
    (usp <= x \/ x + K + 1 <= usp - JUNK6) ->
    VBothIcStrcmpWalk.shfacts mem x K usp.
  Proof.
    intros ZG LG WRD SHD RNG SAP. unfold HIGH_MEM_BEG, HIGH_MEM_END, LOW_MEM_END, JUNK6, SBz in *.
    constructor; unfold VBothIcStrcmpWalk.ISC_FRAME, BothRegionPoisoned.SB, BothRegionPoisoned.kLowEnd,
        BothRegionPoisoned.kHighBeg, BothRegionPoisoned.kHighEnd; change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn;
        try exact ZG; try exact LG; try exact WRD; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma RUN_asan : RUN_spec6 BSEGS rom A_ISC ISC_MCELLS.
  Proof.
    unfold RUN_spec6. intros mem a b usp K bufa bufb regs ra MC FA FB ZK Husp Hstk Hret H1 H2 H10 H11.
    destruct FA as (Hbufa & La & Hnwa & Ha & HK & HK40 & RNGa & SAPa & SHDa & ZGa & LGa & WRDa).
    destruct FB as (Hbufb & Lb & Hnwb & Hb & _ & _ & RNGb & SAPb & SHDb & ZGb & LGb & WRDb).
    pose proof (shfacts_of mem a K usp ZGa LGa WRDa SHDa RNGa SAPa) as SFa.
    pose proof (shfacts_of mem b K usp ZGb LGb WRDb SHDb RNGb SAPb) as SFb.
    unfold JUNK6, SBz in *.
    assert (IH : VBothIcStrcmpWalk.iscH mem a b usp bufa bufb K).
    { constructor; unfold VBothIcStrcmpWalk.ISC_FRAME, BothRegionPoisoned.SB;
        change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn;
        try exact MC; try exact Hbufa; try exact Hbufb; try exact ZK; try exact SFa; try exact SFb; try exact Hstk; try lia. }
    destruct (VBothIcStrcmpWalk.isc_run mem rom a b usp bufa bufb K IH regs ra Hret H1 H2 H10 H11)
      as (regs' & I & m' & MS & HI & _ & _ & Q10 & Q2 & Q1 & QK & QM & QG & _).
    destruct (cmpx_dlt (bv_unsigned (nth (Z.to_nat I) bufa (Z_to_bv 8 0))) (bv_unsigned (nth (Z.to_nat I) bufb (Z_to_bv 8 0)))) as [CV CB].
    exists regs', (cmp_dlt (bv_unsigned (nth (Z.to_nat I) bufa (Z_to_bv 8 0))) (bv_unsigned (nth (Z.to_nat I) bufb (Z_to_bv 8 0)))), m'. split.
    { lazymatch type of MS with OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps _ (_ _ ?p _ _) _ =>
        replace (wordZ A_ISC) with p by bveq end.
      apply asan_msteps_bridge. exact MS. }
    split; [exact CB|]. split; [etransitivity; [|exact CV]; f_equal; exact Q10|].
    split; [exact Q2|]. split; [exact Q1|].
    split; [exact (asan_caller_saved _ regs regs' QK isc_clob_saved)|].
    split; [exact QM|exact QG].
  Qed.

  Theorem i_strcmp_post_asan : contract_post2 BSEGS P E mem0 rom CI C_i_strcmp A_ISC.
  Proof.
    exact (i_strcmp_post BSEGS P E mem0 rom CI PO2 SHOFF ROM_HI_asan FSLEN FS_SOME FRAME40 A_ISC ISC_MCELLS ISC_MCELLS_OK RUN_asan).
  Qed.

  Theorem i_strcmp_dead_asan : contract_dead2 BSEGS P E mem0 CI C_i_strcmp.
  Proof. exact (i_strcmp_dead BSEGS P E mem0 CI PO2). Qed.
End Contracts.
