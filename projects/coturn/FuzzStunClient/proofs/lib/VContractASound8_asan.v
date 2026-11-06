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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec StepTac RefMemcpyLib ZStores.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VCert VContract VState2 VStepMem2 VGamma2 VStepMem2SoundA VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound1_asan VContractASound2 VContractASound2_asan VContractASound3_asan VContractASoundI VContractASound5_asan VContractASound8.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require AsanRegionPoisoned AsanMemchr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require CatSim ZStores.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VAsanMuslStrLib VAsanMuslStrlen VAsanIcMemchrWalk VAsanIcStrncpyWalk.
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
Definition A_ISN : Z := 0x442c0.            (* [comment removed for export] *)
Definition A_GOT_flags : Z := 0xaae78.     (* [comment removed for export] *)
Definition A_rstr : Z := 0xb0e15.          (* [comment removed for export] *)
Definition A_CELL_strnlen : Z := 0xacc98.  (* [comment removed for export] *)
Definition A_CELL_strncpy : Z := 0xaccb8.  (* [comment removed for export] *)
Definition A_CELL_memchr : Z := 0xacbb0.   (* [comment removed for export] *)

Lemma GOT_flags_bytes : rdn ASEGS (fun _ => None) (wordZ A_GOT_flags) 8 = Some (word_to_le_bytes 8 (wordZ 0xb0df8)).
Proof. vm_refl_bv. Qed.
Lemma CELL_strnlen_bytes : rdn ASEGS (fun _ => None) (wordZ A_CELL_strnlen) 8 = Some (word_to_le_bytes 8 (wordZ 0xa4a38)).
Proof. vm_refl_bv. Qed.
Lemma CELL_strncpy_bytes : rdn ASEGS (fun _ => None) (wordZ A_CELL_strncpy) 8 = Some (word_to_le_bytes 8 (wordZ 0xa4900)).
Proof. vm_refl_bv. Qed.
Lemma CELL_memchr_bytes : rdn ASEGS (fun _ => None) (wordZ A_CELL_memchr) 8 = Some (word_to_le_bytes 8 (wordZ 0xa40b0)).
Proof. vm_refl_bv. Qed.

Lemma isn_clob_saved (r : reg) : VAsanIcStrncpyWalk.isn_clob r = true -> In (bv_unsigned r) CALLER_SAVED.
Proof.
  unfold VAsanIcStrncpyWalk.isn_clob. intros H.
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
  Hypothesis FS_SOME : vp_fs P <> None.
  Hypothesis FRAME40 : vp_frame (p1 P) < 2 ^ 40.
  Hypothesis SEG_IMG : forall lo hi, In (lo, hi) (vp_segs (p1 P)) -> hi <= vp_imgend P.   (* [comment removed for export] *)
  Hypothesis VIMG : 0x608000 <= vp_imgend P.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis PRI_GOT1 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_cflags /\ A_GOT_hend + 8 <= phi.
  Hypothesis PRI_GOT2 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_ri /\ A_GOT_ri + 8 <= phi.
  Hypothesis PRI_CELLS : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_CELL_memchr /\ A_CELL_memset + 8 <= phi.
  Hypothesis PRI_RC : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= RC_LO /\ RC_HI <= phi.
  (* [comment removed for export] *)
  Hypothesis K_shb : In (A_shb, (8, SBz)) (vp_kcells P).
  Hypothesis K_mid1 : In (A_mid1, (8, 0)) (vp_kcells P).
  Hypothesis K_mid2 : In (A_mid2, (8, 0)) (vp_kcells P).
  Hypothesis K_hend : In (A_hend, (8, 2 ^ 47 - 1)) (vp_kcells P).
  Hypothesis K_inited : In (A_inited, (1, 1)) (vp_kcells P).
  Hypothesis K_ri : In (A_ri, (1, 1)) (vp_kcells P).
  Hypothesis K_rstr : In (A_rstr, (1, 1)) (vp_kcells P).

  #[warnings="-notation-for-abbreviation"] Notation gamma2P := (gamma2 ASEGS P E mem0).

  (* [comment removed for export] *)
  Definition ISN_MCELLS (m : word -> option byte) : Prop := VAsanIcStrncpyWalk.isn_cells m.

  Lemma kbyte1 A nu regs mem a : gamma2P A nu regs mem -> In (a, (1, 1)) (vp_kcells P) ->
    rdn ASEGS mem (wordZ a) 1 = Some [Z_to_bv 8 1].
  Proof.
    intros HG2 HK. pose proof HG2 as (_ & _ & (KC & _) & _).
    destruct (KC _ _ _ HK) as (_ & _ & _ & bs & R & V). change (Z.to_nat 1) with 1%nat in R.
    pose proof (rdn_length _ _ _ _ _ R) as L. destruct bs as [|b [|]]; try discriminate.
    rewrite R. do 2 f_equal. apply bv_eq. cbn [bytes_le_to_Z] in V. rewrite Z.shiftl_0_l, Z.lor_0_r in V.
    rewrite V. reflexivity.
  Qed.

  Lemma ISN_MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> ISN_MCELLS mem.
  Proof.
    intros A nu regs mem HG2. unfold ISN_MCELLS, VAsanIcStrncpyWalk.isn_cells, AsanRegionPoisoned.cells, AsanRegionPoisoned.cell.
    change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
    change AsanRegionPoisoned.SB with SBz. change AsanRegionPoisoned.kHighEnd with (2 ^ 47 - 1).
    fold (wordZ 0xaae80) (wordZ 0xb35f8) (wordZ 0xaae88) (wordZ 0xb42e8) (wordZ 0xaae90) (wordZ 0xb42f0)
         (wordZ 0xaae98) (wordZ 0xb42e0) (wordZ 0xb42d8) (wordZ 0xaae78) (wordZ 0xb0df8) (wordZ 0xb0e15)
         (wordZ 0xacc98) (wordZ 0xa4a38) (wordZ 0xaccb8) (wordZ 0xa4900) (wordZ 0xacbb0) (wordZ 0xa40b0)
         (wordZ 0xab9e8) (wordZ 0xb42d9) (wordZ 0xaccf0) (wordZ 0xa45b0)
         (wordZ SBz) (wordZ 0) (wordZ (2 ^ 47 - 1)).
    destruct PRI_GOT1 as (plo & phi & G1 & G2 & G3). unfold A_GOT_cflags, A_GOT_hend in G2, G3.
    destruct PRI_CELLS as (clo & chi & CC1 & CC2 & CC3). unfold A_CELL_memchr, A_CELL_memset in CC2, CC3.
    repeat split.
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|unfold A_GOT_shb; lia]|exact GOT_shb_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_shb).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|unfold A_GOT_mid1; lia]|exact GOT_mid1_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_mid1).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|unfold A_GOT_mid2; lia]|exact GOT_mid2_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_mid2).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|unfold A_GOT_hend; lia]|exact GOT_hend_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_hend).
    - exact (kbyte1 A nu regs mem _ HG2 K_inited).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|unfold A_GOT_flags; lia]|exact GOT_flags_bytes].
    - exact (kbyte1 A nu regs mem _ HG2 K_rstr).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists clo, chi; split; [exact CC1|unfold A_CELL_strnlen; lia]|exact CELL_strnlen_bytes].
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists clo, chi; split; [exact CC1|unfold A_CELL_strncpy; lia]|exact CELL_strncpy_bytes].
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists clo, chi; split; [exact CC1|unfold A_CELL_memchr; lia]|exact CELL_memchr_bytes].
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exact PRI_GOT2|exact GOT_ri_bytes].
    - exact (kbyte1 A nu regs mem _ HG2 K_ri).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists clo, chi; split; [exact CC1|unfold A_CELL_memset; lia]|exact CELL_BYTES_asan].
    - (* [comment removed for export] *)
      intros i Hi. pose proof HG2 as ((_ & (_ & _ & MP & _) & _) & _).
      destruct PRI_RC as (qlo & qhi & Q1 & Q2 & Q3). unfold RC_LO, RC_HI in Q2, Q3.
      exact (MP qlo qhi i Q1 ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  #[using="VIMG"] Lemma RUN_asan : RUN_spec8 ASEGS P rom A_ISN ISN_MCELLS.
  Proof.
    unfold RUN_spec8.
    intros mem d s n usp K buf regs ra MC Hn Hd Hdn SF Hs0 HK8 DISJ DR DIMG Husp Hdst Hshd ZGd LGd WRDd DOK Hstk Hret H1 H2 H10 H11 H12.
    pose proof VIMG as VIMG'.
    unfold str_facts, band_ok, LOW_MEM_TOP, HIGH_MEM_BEG, HIGH_MEM_END, LOW_MEM_END, JUNK8, SBz in *.
    destruct SF as (Hbuf & Hwin & Hnw & Hs & HK & HK40 & Hz & Hrng & Hsap & Hshs & ZG & LG & WRD).
    assert (HKL : K < Z.of_nat (length buf)).
    { destruct (Z_lt_le_dec K (Z.of_nat (length buf))) as [X|X]; [exact X|exfalso].
      rewrite nth_overflow in Hz by (ltac2:(LK.k [@HK; @Hrng; @Hsap; @Hshs; @Hs0; @HK8; @DISJ; @DR; @DIMG; @Husp; @Hdst; @Hshd; @VIMG'; @X]); lia). cbn in Hz. pose proof (rdn_length _ _ _ _ _ Hbuf). unfold wend in Hwin.
      pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)). lia. }
    assert (IH : VAsanIcStrncpyWalk.isnH mem d s n usp buf K).
    { constructor; unfold VAsanIcStrncpyWalk.ISN_FRAME, AsanRegionPoisoned.SB, AsanRegionPoisoned.kLowEnd,
        AsanRegionPoisoned.kHighBeg, AsanRegionPoisoned.kHighEnd; change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn;
        try exact MC; try exact Hbuf; try exact Hz; try exact ZG; try exact LG; try exact WRD; try exact ZGd; try exact LGd; try exact WRDd;
        try exact DOK; try exact Hstk; try exact DISJ; try lia.
      unfold wend in Hwin. pose proof (Z.div_mod (s + K) 8 ltac:(lia)). (ltac2:(LK.k [@Hwin; @HK; @Hrng; @Hsap; @Hshs; @Hs0; @HK8; @DISJ; @DR; @DIMG; @Husp; @Hdst; @Hshd; @VIMG'; @HKL; @H]); lia). }
    destruct (VAsanIcStrncpyWalk.isn_run mem rom d s n usp buf K IH regs ra Hret H1 H2 H10 H11 H12)
      as (regs' & m' & MS & Q10 & Q2 & Q1 & QK & QM & QG & HI & ZI & NZI).
    exists regs', m', (firstn (Z.to_nat (Z.of_nat (VAsanIcMemchrWalk.fz buf))) buf ++ ZStores.zeros (Z.to_nat (n - Z.of_nat (VAsanIcMemchrWalk.fz buf))))%list.
    split.
    { rewrite length_app, length_firstn, ZStores.length_zeros. (ltac2:(LK.k [@Hn; @HK; @Hrng; @Hsap; @Hshs; @Hs0; @HK8; @DISJ; @DR; @DIMG; @Husp; @Hdst; @Hshd; @VIMG'; @HKL; @HI]); lia). }
    split.
    { lazymatch type of MS with OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps _ (_ _ ?p _ _) _ =>
        replace (wordZ A_ISN) with p by bveq end.
      apply asan_msteps_bridge. exact MS. }
    split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|].
    split; [exact (asan_caller_saved _ regs regs' QK isn_clob_saved)|].
    split; [exact QM|exact QG].
  Qed.

  Theorem i_strncpy_post_asan : contract_post2 ASEGS P E mem0 rom CI C_i_strncpy A_ISN.
  Proof.
    exact (i_strncpy_post ASEGS P E mem0 rom CI PO2 SHOFF ROM_HI_asan FSLEN FS_SOME FRAME40 SEG_IMG A_ISN ISN_MCELLS ISN_MCELLS_OK RUN_asan).
  Qed.

  Theorem i_strncpy_dead_asan : contract_dead2 ASEGS P E mem0 CI C_i_strncpy.
  Proof. exact (i_strncpy_dead ASEGS P E mem0 CI PO2). Qed.
End Contracts.
