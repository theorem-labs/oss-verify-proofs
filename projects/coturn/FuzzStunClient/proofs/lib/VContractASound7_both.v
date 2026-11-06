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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VWord2 VState VLogic VGamma VStepMem VStepSound VStepMemSound VCert VContract VState2 VStepMem2 VGamma2 VStepMem2SoundA VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound1_both VContractASound2 VContractASound2_both VContractASound3_both VContractASoundI VContractASound7.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require BothRegionPoisoned BothMemchr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require CatSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VBothIcBcmpWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac vm_refl := vm_refl_bv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_IBC : Z := 0x44234.            (* [comment removed for export] *)
Definition A_imemcmp : Z := 0x1437e6.       (* [comment removed for export] *)
Definition A_smemcmp : Z := 0x1437e7.       (* [comment removed for export] *)
Definition A_CELL_bcmp : Z := 0xab1e8.     (* [comment removed for export] *)
Definition A_CELL_memcmp : Z := 0xab1e0.   (* [comment removed for export] *)

Lemma CELL_bcmp_bytes : rdn BSEGS (fun _ => None) (wordZ A_CELL_bcmp) 8 = Some (word_to_le_bytes 8 (wordZ 0xa26e8)).
Proof. vm_refl_bv. Qed.
Lemma CELL_memcmp_bytes : rdn BSEGS (fun _ => None) (wordZ A_CELL_memcmp) 8 = Some (word_to_le_bytes 8 (wordZ 0xa27b8)).
Proof. vm_refl_bv. Qed.

Lemma ibc_clob_saved (r : reg) : VBothIcBcmpWalk.ibc_clob r = true -> In (bv_unsigned r) CALLER_SAVED.
Proof.
  unfold VBothIcBcmpWalk.ibc_clob. intros H.
  repeat (apply Bool.orb_prop in H; destruct H as [H|H]);
    unfold bv_eqb in H; apply Z.eqb_eq in H; rewrite H; unfold CALLER_SAVED; cbn; tauto.
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
  Hypothesis K_imemcmp : In (A_imemcmp, (1, 1)) (vp_kcells P).
  Hypothesis K_smemcmp : In (A_smemcmp, (1, 1)) (vp_kcells P).
  Hypothesis PRI_CELLS : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_CELL_memcmp /\ A_CELL_bcmp + 8 <= phi.

  #[warnings="-notation-for-abbreviation"] Notation gamma2P := (gamma2 BSEGS P E mem0).

  (* [comment removed for export] *)
  Definition IBC_MCELLS (m : word -> option byte) : Prop := VBothIcBcmpWalk.ibc_cells m.

  Lemma IBC_MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> IBC_MCELLS mem.
  Proof.
    intros A nu regs mem HG2. unfold IBC_MCELLS, VBothIcBcmpWalk.ibc_cells, BothRegionPoisoned.cells, BothRegionPoisoned.cell.
    change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
    change BothRegionPoisoned.SB with SBz. change BothRegionPoisoned.kHighEnd with (2 ^ 47 - 1).
    fold (wordZ 0xa94b8) (wordZ 0xb1bb8) (wordZ 0xa94c0) (wordZ 0xb28a8) (wordZ 0xa94c8) (wordZ 0xb28b0)
         (wordZ 0xa94d0) (wordZ 0xb28a0) (wordZ 0xb2898) (wordZ 0xa94a8) (wordZ 0x1436e8)
         (wordZ 0x1437e6) (wordZ 0x1437e7) (wordZ 0xab1e8) (wordZ 0xa26e8) (wordZ 0xab1e0) (wordZ 0xa27b8)
         (wordZ SBz) (wordZ 0) (wordZ (2 ^ 47 - 1)).
    destruct PRI_GOT1 as (plo & phi & G1 & G2 & G3). unfold A_GOT_cflags, A_GOT_hend in G2, G3.
    destruct PRI_CELLS as (qlo & qhi & Q1 & Q2 & Q3). unfold A_CELL_memcmp, A_CELL_bcmp in Q2, Q3.
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
    - exact (kcellN P E mem0 A nu regs mem _ _ _ HG2 K_imemcmp).
    - exact (kcellN P E mem0 A nu regs mem _ _ _ HG2 K_smemcmp).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists qlo, qhi; split; [exact Q1|lia]|exact CELL_bcmp_bytes].
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists qlo, qhi; split; [exact Q1|lia]|exact CELL_memcmp_bytes].
  Qed.

  Lemma accfacts_of mem usp x n buf : opnd_facts BSEGS mem usp x n buf -> 0 < n -> VBothIcBcmpWalk.accfacts mem x n usp.
  Proof.
    intros (_ & _ & _ & _ & F) Hn. destruct (F Hn) as (ZG & LG & W1 & W2 & SHD & RNG & SAP).
    unfold HIGH_MEM_BEG, HIGH_MEM_END, LOW_MEM_END, JUNK7, SBz in *.
    constructor; unfold VBothIcBcmpWalk.IBC_FRAME, BothRegionPoisoned.SB, BothRegionPoisoned.kLowEnd,
        BothRegionPoisoned.kHighBeg, BothRegionPoisoned.kHighEnd; change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn;
        try exact ZG; try exact LG; try exact W1; try exact W2; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma RUN_asan : RUN_spec7 BSEGS rom A_IBC IBC_MCELLS.
  Proof.
    unfold RUN_spec7. intros mem a b n usp bufa bufb regs ra MC Hn FA FB Husp Hstk Hret H1 H2 H10 H11 H12.
    pose proof FA as (Hbufa & La & Ha & Han & _). pose proof FB as (Hbufb & Lb & Hb & Hbn & _).
    unfold JUNK7, SBz in *.
    assert (IH : VBothIcBcmpWalk.ibcH mem a b n usp bufa bufb).
    { constructor; unfold VBothIcBcmpWalk.IBC_FRAME, BothRegionPoisoned.SB;
        change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn;
        try exact MC; try exact La; try exact Lb; try exact Hbufa; try exact Hbufb; try exact Hstk; try lia.
      - intros Hn0. exact (accfacts_of mem usp a n bufa FA Hn0).
      - intros Hn0. exact (accfacts_of mem usp b n bufb FB Hn0). }
    destruct (VBothIcBcmpWalk.ibc_run mem rom a b n usp bufa bufb IH regs ra Hret H1 H2 H10 H11 H12)
      as (regs' & d & m' & MS & Hd & Q10 & Q2 & Q1 & QK & QM & QG & _).
    exists regs', d, m'. split.
    { lazymatch type of MS with OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps _ (_ _ ?p _ _) _ =>
        replace (wordZ A_IBC) with p by bveq end.
      apply asan_msteps_bridge. exact MS. }
    split; [exact Hd|]. split; [etransitivity; [|apply u_Z_to_bv64]; f_equal; exact Q10|].
    split; [exact Q2|]. split; [exact Q1|].
    split; [exact (asan_caller_saved _ regs regs' QK ibc_clob_saved)|].
    split; [exact QM|exact QG].
  Qed.

  Theorem i_bcmp_post_asan : contract_post2 BSEGS P E mem0 rom CI C_i_bcmp A_IBC.
  Proof.
    exact (i_bcmp_post BSEGS P E mem0 rom CI PO2 SHOFF ROM_HI_asan FSLEN FS_SOME FRAME40 A_IBC IBC_MCELLS IBC_MCELLS_OK RUN_asan).
  Qed.

  Theorem i_bcmp_dead_asan : contract_dead2 BSEGS P E mem0 CI C_i_bcmp.
  Proof. exact (i_bcmp_dead BSEGS P E mem0 CI PO2). Qed.
End Contracts.
