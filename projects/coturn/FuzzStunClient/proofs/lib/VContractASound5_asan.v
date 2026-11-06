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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec StepTac RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VCert VContract VState2 VStepMem2 VGamma2 VStepMem2SoundA VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound1_asan VContractASound2 VContractASound2_asan VContractASound3_asan VContractASoundI VContractASound5.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require AsanRegionPoisoned AsanMemchr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require CatSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VAsanMuslStrlen VAsanIcStrlenWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac vm_refl := vm_refl_bv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_ISL : Z := 0x44230.            (* [comment removed for export] *)
Definition A_CELL_strlen : Z := 0xacb88.   (* [comment removed for export] *)
Definition A_istrlen : Z := 0x145223.       (* [comment removed for export] *)
Definition A_inited : Z := 0xb42d8.        (* [comment removed for export] *)
Definition RC_LO : Z := 0x10360.            (* [comment removed for export] *)
Definition RC_HI : Z := 0x10388.

Lemma CELL_strlen_bytes : rdn ASEGS (fun _ => None) (wordZ A_CELL_strlen) 8 = Some (word_to_le_bytes 8 (wordZ 0xa47fc)).
Proof. vm_refl_bv. Qed.

Lemma isl_clob_saved (r : reg) : VAsanIcStrlenWalk.isl_clob r = true -> In (bv_unsigned r) CALLER_SAVED.
Proof.
  unfold VAsanIcStrlenWalk.isl_clob. intros H.
  repeat (apply Bool.orb_prop in H; destruct H as [H|H]);
    unfold bv_eqb in H; apply Z.eqb_eq in H; rewrite H; unfold CALLER_SAVED; cbn; tauto.
Qed.

(* [comment removed for export] *)
Lemma strlen_span_wend (s K : Z) : 0 <= s -> 0 <= K -> VAsanMuslStrlen.strlen_span s K <= wend s K - s.
Proof.
  intros Hs HK. unfold VAsanMuslStrlen.strlen_span, VAsanMuslStrlen.hd, wend.
  pose proof (Z.div_mod (s + K) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)).
  pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)).
  destruct (Z.ltb_spec K ((8 - s mod 8) mod 8)); [|lia].
  pose proof (Z.mod_pos_bound (8 - s mod 8) 8 ltac:(lia)). lia.
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
  Hypothesis FS_SOME : vp_fs P <> None.
  Hypothesis FRAME40 : vp_frame (p1 P) < 2 ^ 40.
  (* [comment removed for export] *)
  Hypothesis PRI_GOT1 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_cflags /\ A_GOT_hend + 8 <= phi.
  Hypothesis PRI_CELL : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_CELL_strlen /\ A_CELL_strlen + 8 <= phi.
  Hypothesis PRI_RC : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= RC_LO /\ RC_HI <= phi.
  (* [comment removed for export] *)
  Hypothesis K_shb : In (A_shb, (8, SBz)) (vp_kcells P).
  Hypothesis K_mid1 : In (A_mid1, (8, 0)) (vp_kcells P).
  Hypothesis K_mid2 : In (A_mid2, (8, 0)) (vp_kcells P).
  Hypothesis K_hend : In (A_hend, (8, 2 ^ 47 - 1)) (vp_kcells P).
  Hypothesis K_inited : In (A_inited, (1, 1)) (vp_kcells P).
  Hypothesis K_istrlen : In (A_istrlen, (1, 1)) (vp_kcells P).

  #[warnings="-notation-for-abbreviation"] Notation gamma2P := (gamma2 ASEGS P E mem0).

  (* [comment removed for export] *)
  Definition ISL_MCELLS (m : word -> option byte) : Prop := VAsanIcStrlenWalk.isl_cells m.

  Lemma ISL_MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> ISL_MCELLS mem.
  Proof.
    intros A nu regs mem HG2. unfold ISL_MCELLS, VAsanIcStrlenWalk.isl_cells, AsanRegionPoisoned.cells, AsanRegionPoisoned.cell.
    change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
    change AsanRegionPoisoned.SB with SBz. change AsanRegionPoisoned.kHighEnd with (2 ^ 47 - 1).
    fold (wordZ 0xaae80) (wordZ 0xb35f8) (wordZ 0xaae88) (wordZ 0xb42e8) (wordZ 0xaae90) (wordZ 0xb42f0)
         (wordZ 0xaae98) (wordZ 0xb42e0) (wordZ 0xb42d8) (wordZ 0xacb88) (wordZ 0xa47fc) (wordZ 0xaae70) (wordZ 0x145128)
         (wordZ 0x145223) (wordZ SBz) (wordZ 0) (wordZ (2 ^ 47 - 1)).
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
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exact PRI_CELL|exact CELL_strlen_bytes].
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact GOT_cflags_bytes].
    - exact (kcellN P E mem0 A nu regs mem _ _ _ HG2 K_istrlen).
    - (* [comment removed for export] *)
      intros i Hi. pose proof HG2 as ((_ & (_ & _ & MP & _) & _) & _).
      destruct PRI_RC as (qlo & qhi & Q1 & Q2 & Q3). unfold RC_LO, RC_HI in Q2, Q3.
      exact (MP qlo qhi i Q1 ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma RUN_asan : RUN_spec5 ASEGS rom A_ISL ISL_MCELLS.
  Proof.
    unfold RUN_spec5. intros mem s usp K buf regs ra MC SF Husp Hstk Hret H1 H2 H10.
    unfold str_facts, HIGH_MEM_BEG, HIGH_MEM_END, LOW_MEM_END, JUNK5, SBz in *.
    destruct SF as (Hbuf & Hwin & Hnw & Hs & HK & HK40 & Hz & Hrng & Hsap & Hshd & ZG & LG & WRD).
    assert (IH : VAsanIcStrlenWalk.islH mem s usp buf K).
    { constructor; unfold VAsanIcStrlenWalk.ISL_FRAME, AsanRegionPoisoned.SB, AsanRegionPoisoned.kLowEnd,
        AsanRegionPoisoned.kHighBeg, AsanRegionPoisoned.kHighEnd; change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn;
        try exact MC; try exact Hbuf; try exact Hz; try exact ZG; try exact LG; try exact WRD; try exact Hstk; try lia.
      pose proof (strlen_span_wend s K Hs HK). lia. }
    destruct (VAsanIcStrlenWalk.isl_run mem rom s usp buf K IH regs ra Hret H1 H2 H10)
      as (regs' & i & m' & MS & Hi & Zi & NZi & Q10 & Q2 & Q1 & QK & QM & QG & _).
    exists regs', i, m'. split.
    { lazymatch type of MS with OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps _ (_ _ ?p _ _) _ =>
        replace (wordZ A_ISL) with p by bveq end.
      apply asan_msteps_bridge. exact MS. }
    split; [exact Hi|]. split; [exact Zi|]. split; [exact NZi|].
    split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|].
    split; [exact (asan_caller_saved _ regs regs' QK isl_clob_saved)|].
    split; [exact QM|exact QG].
  Qed.

  Theorem i_strlen_post_asan : contract_post2 ASEGS P E mem0 rom CI C_i_strlen A_ISL.
  Proof.
    exact (i_strlen_post ASEGS P E mem0 rom CI PO2 SHOFF ROM_HI_asan FSLEN FS_SOME FRAME40 A_ISL ISL_MCELLS ISL_MCELLS_OK RUN_asan).
  Qed.

  Theorem i_strlen_dead_asan : contract_dead2 ASEGS P E mem0 CI C_i_strlen.
  Proof. exact (i_strlen_dead ASEGS P E mem0 CI PO2). Qed.
End Contracts.
