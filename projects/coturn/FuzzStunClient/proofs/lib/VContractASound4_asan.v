(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec StepTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VCert VContract VState2 VStepMem2 VGamma2 VStepMem2SoundA VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound1_asan VContractASound2 VContractASound2_asan VContractASound3_asan VContractASound4.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require AsanRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require CatSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VAsanMemcpyWalk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac vm_refl := vm_refl_bv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_CELL_memcpy : Z := 0xacce8.   (* [comment removed for export] *)

Lemma CELL_memcpy_bytes : rdn ASEGS (fun _ => None) (wordZ A_CELL_memcpy) 8 = Some (word_to_le_bytes 8 (wordZ 0xa41ac)).
Proof. vm_refl_bv. Qed.

Lemma cp_clob_saved (r : reg) : VAsanMemcpyWalk.cp_clob r = true -> In (bv_unsigned r) CALLER_SAVED.
Proof.
  unfold VAsanMemcpyWalk.cp_clob. intros H.
  repeat (apply Bool.orb_prop in H; destruct H as [H|H]);
    unfold bv_eqb in H; apply Z.eqb_eq in H; rewrite H; unfold CALLER_SAVED; cbn; tauto.
Qed.

(* [comment removed for export] *)
Section Contracts.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.
  Hypothesis PO2 : params_ok2 ASEGS P.
  Hypothesis SHOFF : vp_shoff P = SBz.
  Hypothesis FSLEN : forall len ssl, vp_fs P = Some (len, ssl) -> FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL < len.
  Hypothesis DATAL : 8 <= vp_datal P.
  (* [comment removed for export] *)
  Hypothesis GOT1_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_shb /\ A_GOT_hend + 8 <= phi.
  Hypothesis GOT2_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_ri /\ A_GOT_ri + 8 <= phi.
  Hypothesis CELL_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_CELL_memcpy /\ A_CELL_memcpy + 8 <= phi.
  (* [comment removed for export] *)
  Hypothesis K_shb : In (A_shb, (8, SBz)) (vp_kcells P).
  Hypothesis K_mid1 : In (A_mid1, (8, 0)) (vp_kcells P).
  Hypothesis K_mid2 : In (A_mid2, (8, 0)) (vp_kcells P).
  Hypothesis K_hend : In (A_hend, (8, 2 ^ 47 - 1)) (vp_kcells P).
  Hypothesis K_ri : In (A_ri, (1, 1)) (vp_kcells P).

  #[warnings="-notation-for-abbreviation"] Notation gamma2P := (gamma2 ASEGS P E mem0).

  (* [comment removed for export] *)
  Definition CP_MCELLS (m : word -> option byte) : Prop := VAsanMemcpyWalk.cp_cells m.

  Lemma CP_MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> CP_MCELLS mem.
  Proof.
    intros A nu regs mem HG2. unfold CP_MCELLS, VAsanMemcpyWalk.cp_cells, AsanRegionPoisoned.cells, AsanRegionPoisoned.cell.
    change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
    change AsanRegionPoisoned.SB with SBz. change AsanRegionPoisoned.kHighEnd with (2 ^ 47 - 1).
    fold (wordZ 0xaae80) (wordZ 0xb35f8) (wordZ 0xaae88) (wordZ 0xb42e8) (wordZ 0xaae90) (wordZ 0xb42f0)
         (wordZ 0xaae98) (wordZ 0xb42e0) (wordZ 0xab9e8) (wordZ 0xb42d9) (wordZ 0xacce8) (wordZ 0xa41ac)
         (wordZ SBz) (wordZ 0) (wordZ (2 ^ 47 - 1)).
    destruct GOT1_PRISTINE as (plo & phi & G1 & G2 & G3). unfold A_GOT_shb, A_GOT_hend in G2, G3.
    repeat split.
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact GOT_shb_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_shb).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact GOT_mid1_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_mid1).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact GOT_mid2_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_mid2).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact GOT_hend_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_hend).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exact GOT2_PRISTINE|exact GOT_ri_bytes].
    - exact (kcellN P E mem0 A nu regs mem _ _ _ HG2 K_ri).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exact CELL_PRISTINE|exact CELL_memcpy_bytes].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma RUN_asan : RUN_spec4 ASEGS rom 0x53e30 CP_MCELLS.
  Proof.
    unfold RUN_spec4. intros mem d s n usp bs regs ra MC Hn Hd Hs Hdn Hsn Hdisj Hlen Hsrc Hrngd Hrngs Husp Hapd Haps Hshd Hshs ACCd ACCs Hdok Hstk
           Hret H1 H2 H10 H11 H12.
    unfold acc_facts, band_ok, LOW_MEM_TOP, HIGH_MEM_BEG, HIGH_MEM_END, JUNK4, SBz in *.
    assert (CH : VAsanMemcpyWalk.cpH mem d s n usp bs).
    { constructor; unfold VAsanMemcpyWalk.CP_FRAME, AsanRegionPoisoned.SB, AsanRegionPoisoned.kLowEnd,
        AsanRegionPoisoned.kHighBeg, AsanRegionPoisoned.kHighEnd; change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn;
        try exact MC; try exact Hlen; try exact Hsrc; try exact Hdok; try exact Hstk; try (intros; (ltac2:(LK.k [@Hn; @Hlen; @Hd; @Hs; @Hdn; @Hsn; @Hdisj; @Hrngd; @H; @Hrngs; @Husp; @Hapd; @Haps; @Hshd; @Hshs]); lia)); try (ltac2:(LK.k [@Hn; @Hlen; @Hd; @Hs; @Hdn; @Hsn; @Hdisj; @Hrngd; @H; @Hrngs; @Husp; @Hapd; @Haps; @Hshd; @Hshs]); lia).
      - intros g Hn0 Hg. exact (proj1 (ACCd Hn0) g Hg).
      - intros Hn0. exact (proj1 (proj2 (ACCd Hn0))).
      - intros g Hn0 Hg. exact (proj1 (ACCs Hn0) g Hg).
      - intros Hn0. exact (proj1 (proj2 (ACCs Hn0))).
      - intros Hn0. exact (proj1 (proj2 (proj2 (ACCd Hn0)))).
      - intros Hn0. exact (proj2 (proj2 (proj2 (ACCd Hn0)))).
      - intros Hn0. exact (proj1 (proj2 (proj2 (ACCs Hn0)))).
      - intros Hn0. exact (proj2 (proj2 (proj2 (ACCs Hn0)))). }
    destruct (VAsanMemcpyWalk.asan_memcpy_run mem rom d s n usp bs CH regs ra Hret H1 H2 H10 H11 H12)
      as (regs' & m' & MS & Q10 & Q2 & Q1 & QK & QM & QG).
    exists regs', m'. split.
    { lazymatch type of MS with OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps _ (_ _ ?p _ _) _ =>
        replace (wordZ 0x53e30) with p by bveq end.
      apply asan_msteps_bridge. exact MS. }
    split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|].
    split; [exact (asan_caller_saved _ regs regs' QK cp_clob_saved)|].
    split; [exact QM|exact QG].
  Qed.

  Theorem asan_memcpy_post_asan : contract_post2 ASEGS P E mem0 rom CI C_asan_memcpy 0x53e30.
  Proof.
    exact (asan_memcpy_post ASEGS P E mem0 rom CI PO2 SHOFF ROM_HI_asan FSLEN DATAL 0x53e30 CP_MCELLS CP_MCELLS_OK RUN_asan).
  Qed.

  Theorem asan_memcpy_dead_asan : contract_dead2 ASEGS P E mem0 CI C_asan_memcpy.
  Proof. exact (asan_memcpy_dead ASEGS P E mem0 CI PO2). Qed.
End Contracts.
