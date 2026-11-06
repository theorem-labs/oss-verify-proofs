(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec Hoare StepTac ZStores RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import TolowerDefs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VCert VContract VContractSound VContractSound2 VContractSound5 VState2 VStepMem2 VCert2 VContract2 VGamma2 VStepMem2SoundA VContract2Iface VContractASound1_asan VContractASoundV1.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VAsanMuslTolower VAsanMuslStrtoul.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition A_TOLOWER_asan : Z := 0x99ed0.
Definition A_STRTOUL_asan : Z := 0xa3f44.
Definition A_GOT_asan : Z := 0xabb08.       (* [comment removed for export] *)
Definition A_GUARD_asan : Z := 0x606630.     (* [comment removed for export] *)
Definition RO1_LO_asan : Z := 0x10330.  Definition RO1_HI_asan : Z := 0x10508.     (* [comment removed for export] *)
Definition RO2_LO_asan : Z := 0x237c0.  Definition RO2_HI_asan : Z := 0x238c1.     (* [comment removed for export] *)
Definition RO_MIN_asan : Z := 0x27468.

(* [comment removed for export] *)
Lemma stopper_of_contA b : strtoul_cont b = false -> VAsanMuslStrtoul.stopper b.
Proof.
  unfold strtoul_cont, VAsanMuslStrtoul.stopper, VAsanMuslStrtoul.isdig, VAsanMuslStrtoul.issp, VAsanMuslStrtoul.issign. intros H.
  apply Bool.orb_false_elim in H as [H H5]. apply Bool.orb_false_elim in H as [H H4].
  apply Bool.orb_false_elim in H as [H H3]. apply Bool.orb_false_elim in H as [H1 H2].
  rewrite H1, H2, H3, H4, H5. repeat split; reflexivity.
Qed.

Lemma strtoul_clobA_CS : forallb (fun r : reg => existsb (Z.eqb (bv_unsigned r)) CALLER_SAVED) VAsanMuslStrtoul.strtoul_clob = true.
Proof. reflexivity. Qed.
Lemma strtoul_clobA_ra : existsb (fun r : reg => Z.eqb (bv_unsigned r) 1) VAsanMuslStrtoul.strtoul_clob = false.
Proof. reflexivity. Qed.

Lemma wordZ_litA (x : word) z : bv_unsigned x = z -> wordZ z = x.
Proof. intros <-. apply wordZ_u. Qed.

Lemma bytes_eq_of_unsignedA : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|a t IH]; intros [|b u] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hab Htu. f_equal; [apply bv_eq; exact Hab|apply IH; exact Htu].
Qed.

(* [comment removed for export] *)
Lemma GOT_BYTES_asan :
  rdn ASEGS (fun _ => None) (wordZ A_GOT_asan) 8 = Some (word_to_le_bytes 8 (wordZ A_GUARD_asan)).
Proof.
  assert (H : option_map (map bv_unsigned) (rdn ASEGS (fun _ => None) (wordZ A_GOT_asan) 8)
              = option_map (map bv_unsigned) (Some (word_to_le_bytes 8 (wordZ A_GUARD_asan)))) by (vm_compute; reflexivity).
  destruct (rdn _ _ _ _) as [bs|]; [|discriminate]. cbn [option_map] in H. injection H as H'.
  f_equal. apply bytes_eq_of_unsignedA. exact H'.
Qed.

Section Asan.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma TOLOWER_asan : forall regs mem (c : Z) (ret : word),
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = Z_to_bv 64 c -> 0 <= c <= 255 ->
    exists regs',
      msteps ASEGS (mkst regs (wordZ A_TOLOWER_asan) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10%bv = Z_to_bv 64 (tolower_Z c)
      /\ regs_agree (fun r => In r tolower_clob) regs regs'.
  Proof.
    intros. rewrite (wordZ_litA (0x99ed0 : word)) by reflexivity.
    change tolower_Z with VAsanMuslTolower.tolower_Z. change tolower_clob with VAsanMuslTolower.tolower_clob.
    destruct (VAsanMuslTolower.ref_tolower_byte regs mem rom c ret H H0 H1 H2) as (r & RUN & V & AG).
    exists r. split; [apply asan_msteps_bridge; exact RUN|]. split; [exact V|exact AG].
  Qed.

  Lemma STRTOUL_asan : forall mem (s sp tp CAN : word) (str : list byte) (A : Z) regs (ret : word),
    rdn ASEGS mem s (length str) = Some str ->
    0 <= A < Z.of_nat (length str) ->
    strtoul_cont (bv_unsigned (nth (Z.to_nat A) str (Z_to_bv 8 0))) = false ->
    bv_unsigned s + Z.of_nat (length str) < 2 ^ 64 - 8 ->
    store_ok ASEGS mem (Z_to_bv 64 (bv_unsigned sp - 368)) 368 = true ->
    368 <= bv_unsigned sp < 2 ^ 64 ->
    RO_MIN_asan <= bv_unsigned sp - 368 ->
    (bv_unsigned sp <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length str) <= bv_unsigned sp - 368) ->
    store_ok ASEGS mem (Z_to_bv 64 (bv_unsigned tp - 164)) 4 = true ->
    RO_MIN_asan + 164 <= bv_unsigned tp ->
    (bv_unsigned tp - 164 + 4 <= bv_unsigned sp - 368 \/ bv_unsigned sp <= bv_unsigned tp - 164) ->
    (bv_unsigned tp - 164 + 4 <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length str) <= bv_unsigned tp - 164) ->
    rdn ASEGS mem (Z_to_bv 64 A_GOT_asan) 8 = Some (word_to_le_bytes 8 (wordZ A_GUARD_asan)) ->
    A_GOT_asan + 8 <= bv_unsigned sp - 368 ->
    rdn ASEGS mem (wordZ A_GUARD_asan) 8 = Some (word_to_le_bytes 8 CAN) ->
    (A_GUARD_asan + 8 <= bv_unsigned sp - 368 \/ bv_unsigned sp <= A_GUARD_asan) ->
    (A_GUARD_asan + 8 <= bv_unsigned tp - 164 \/ bv_unsigned tp - 164 + 4 <= A_GUARD_asan) ->
    A_GUARD_asan + 8 < 2 ^ 64 ->
    (forall x, (RO1_LO_asan <= x < RO1_HI_asan \/ RO2_LO_asan <= x < RO2_HI_asan) -> mem (Z_to_bv 64 x) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp -> getr regs 4%bv = tp ->
    getr regs 10%bv = s -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 10 ->
    exists regs' mem',
      msteps ASEGS (mkst regs (wordZ A_STRTOUL_asan) mem rom) (mkst regs' ret mem' rom)
      /\ (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x)
      /\ getr regs' 1%bv = getr regs 1%bv
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 368), 368); (Z_to_bv 64 (bv_unsigned tp - 164), 4)].
  Proof.
    intros mem s sp tp CAN str A regs ret Hstr HA Hstop Hnws Hstk Hsp Hspro Hspstr Herr Htp Herrstk Herrstr
           Hgot Hgotstk Hcan HGstk HGerr HGnw Hro Hret H1 H2 H4 H10 H11 H12.
    assert (UG : bv_unsigned (wordZ A_GUARD_asan) = A_GUARD_asan) by (apply u_wordZ; unfold A_GUARD_asan; lia).
    assert (HOK : VAsanMuslStrtoul.stH mem s sp tp (wordZ A_GUARD_asan) CAN str A).
    { constructor; try assumption; try (rewrite UG); unfold RO_MIN_asan, A_GOT_asan, A_GUARD_asan,
        RO1_LO_asan, RO1_HI_asan, RO2_LO_asan, RO2_HI_asan, VAsanMuslStrtoul.TABA, VAsanMuslStrtoul.C10A, VAsanMuslStrtoul.GOTA in *; try lia.
      all: try (apply stopper_of_contA; exact Hstop).
      all: try exact Hgot.
      all: intros x Hx; apply Hro; lia. }
    destruct (VAsanMuslStrtoul.ref_strtoul mem s sp tp (wordZ A_GUARD_asan) CAN str A rom regs ret HOK Hret H1 H2 H4 H10 H11 H12)
      as (regs' & mem' & RUN & AG & FM).
    exists regs', mem'. rewrite (wordZ_litA (0xa3f44 : word)) by reflexivity.
    split; [apply asan_msteps_bridge; exact RUN|]. split; [exact (regs_agree_CS VAsanMuslStrtoul.strtoul_clob regs regs' strtoul_clobA_CS AG)|].
    split; [exact (regs_agree_ra VAsanMuslStrtoul.strtoul_clob regs regs' strtoul_clobA_ra AG)|exact FM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable P : vparams2.
  Variable E : venv2.
  Variable mem0 : word -> option byte.
  Variable CI : cimg.
  Hypothesis PO2 : params_ok2 ASEGS P.
  Let P1 := p1 P.
  Let E1 := ev1 E.
  Let PO : params_ok ASEGS P1 := PO1 ASEGS P PO2.

  Theorem tolower_post_asan : contract_post2 ASEGS P E mem0 rom CI (CV1 C_tolower) A_TOLOWER_asan.
  Proof.
    apply (contract_post2_of_v1 ASEGS P E mem0 rom CI PO2).
    - intros m0. exact (tolower_post ASEGS P1 E1 m0 rom CI PO A_TOLOWER_asan TOLOWER_asan).
    - apply globs_kept_tolower.
  Qed.

  Theorem tolower_dead_asan : contract_dead2 ASEGS P E mem0 CI (CV1 C_tolower).
  Proof.
    apply (contract_dead2_of_v1 ASEGS P E mem0 CI). intros m0. exact (tolower_dead ASEGS P1 E1 m0 CI).
  Qed.

  (* [comment removed for export] *)
  Hypothesis PRI_GOT : exists plo phi, In (plo, phi) (vp_pristine P1) /\ plo <= A_GOT_asan /\ A_GOT_asan + 8 <= phi.
  Hypothesis SEG_GUARD : exists lo hi, In (lo, hi) (vp_segs P1) /\ lo <= A_GUARD_asan /\ A_GUARD_asan + 8 <= hi.
  Hypothesis PRI_RO1 : exists plo phi, In (plo, phi) (vp_pristine P1) /\ plo <= RO1_LO_asan /\ RO1_HI_asan <= phi.
  Hypothesis PRI_RO2 : exists plo phi, In (plo, phi) (vp_pristine P1) /\ plo <= RO2_LO_asan /\ RO2_HI_asan <= phi.
  Hypothesis CI_ERRNO : ci_errno CI = ci_tp CI - 164.
  Hypothesis CI_TP : RO_MIN_asan + 164 <= ci_tp CI < 2 ^ 64.
  Hypothesis RO_MIN : 0 <= RO_MIN_asan <= vp_splo P1 - vp_frame P1.
  Hypothesis GUARD_ERR : A_GUARD_asan + 8 <= ci_errno CI \/ ci_errno CI + 4 <= A_GUARD_asan.
  Hypothesis SPHI8 : vp_sphi P1 + 8 < 2 ^ 64.

  Theorem strtoul_post_asan : contract_post2 ASEGS P E mem0 rom CI (CV1 C_strtoul) A_STRTOUL_asan.
  Proof.
    apply (contract_post2_of_v1 ASEGS P E mem0 rom CI PO2).
    - intros m0.
      exact (strtoul_post ASEGS P1 E1 m0 rom CI PO A_STRTOUL_asan A_GOT_asan A_GUARD_asan RO1_LO_asan RO1_HI_asan RO2_LO_asan RO2_HI_asan RO_MIN_asan
               PRI_GOT GOT_BYTES_asan SEG_GUARD PRI_RO1 PRI_RO2 CI_ERRNO CI_TP RO_MIN GUARD_ERR SPHI8 STRTOUL_asan).
    - apply globs_kept_strtoul.
  Qed.

  Theorem strtoul_dead_asan : contract_dead2 ASEGS P E mem0 CI (CV1 C_strtoul).
  Proof.
    apply (contract_dead2_of_v1 ASEGS P E mem0 CI). intros m0. exact (strtoul_dead ASEGS P1 E1 m0 CI).
  Qed.
End Asan.
