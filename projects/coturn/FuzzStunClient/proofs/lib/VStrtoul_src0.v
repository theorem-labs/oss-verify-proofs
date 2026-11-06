(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec Hoare StepTac ZStores RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefStrtoul.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VCert VContract VContractSound VContractSound_src0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Abbreviation SEGS0 := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition A_STRTOUL_src0 : Z := 0x23490.
Definition A_GOT_src0 : Z := 0x252f8.
Definition A_GUARD_src0 : Z := 0x567f0.
Definition RO1_LO_src0 : Z := 0x10578.  Definition RO1_HI_src0 : Z := 0x10580.
Definition RO2_LO_src0 : Z := 0x11464.  Definition RO2_HI_src0 : Z := 0x11565.
Definition RO_MIN_src0 : Z := 0x1156c.

(* [comment removed for export] *)
Lemma stopper_of_cont b : strtoul_cont b = false -> stopper b.
Proof.
  unfold strtoul_cont, stopper, isdig, issp, issign. intros H.
  apply Bool.orb_false_elim in H as [H H5]. apply Bool.orb_false_elim in H as [H H4].
  apply Bool.orb_false_elim in H as [H H3]. apply Bool.orb_false_elim in H as [H1 H2].
  rewrite H1, H2, H3, H4, H5. repeat split; reflexivity.
Qed.

Lemma strtoul_clob_CS : forallb (fun r : reg => existsb (Z.eqb (bv_unsigned r)) CALLER_SAVED) strtoul_clob = true.
Proof. reflexivity. Qed.
Lemma strtoul_clob_ra : existsb (fun r : reg => Z.eqb (bv_unsigned r) 1) strtoul_clob = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|a t IH]; intros [|b u] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hab Htu. f_equal; [apply bv_eq; exact Hab|apply IH; exact Htu].
Qed.

(* [comment removed for export] *)
Lemma GOT_BYTES_src0 :
  rdn SEGS0 (fun _ => None) (wordZ A_GOT_src0) 8 = Some (word_to_le_bytes 8 (wordZ A_GUARD_src0)).
Proof.
  assert (H : option_map (map bv_unsigned) (rdn SEGS0 (fun _ => None) (wordZ A_GOT_src0) 8)
              = option_map (map bv_unsigned) (Some (word_to_le_bytes 8 (wordZ A_GUARD_src0)))) by (vm_compute; reflexivity).
  destruct (rdn _ _ _ _) as [bs|]; [|discriminate]. cbn [option_map] in H. injection H as H'.
  f_equal. apply bytes_eq_of_unsigned. exact H'.
Qed.

Section Src0.
  Variable rom : word -> option byte.

  Lemma STRTOUL_src0 : forall mem (s sp tp CAN : word) (str : list byte) (A : Z) regs (ret : word),
    rdn SEGS0 mem s (length str) = Some str ->
    0 <= A < Z.of_nat (length str) ->
    strtoul_cont (bv_unsigned (nth (Z.to_nat A) str (Z_to_bv 8 0))) = false ->
    bv_unsigned s + Z.of_nat (length str) < 2 ^ 64 - 8 ->
    store_ok SEGS0 mem (Z_to_bv 64 (bv_unsigned sp - 368)) 368 = true ->
    368 <= bv_unsigned sp < 2 ^ 64 ->
    RO_MIN_src0 <= bv_unsigned sp - 368 ->
    (bv_unsigned sp <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length str) <= bv_unsigned sp - 368) ->
    store_ok SEGS0 mem (Z_to_bv 64 (bv_unsigned tp - 164)) 4 = true ->
    RO_MIN_src0 + 164 <= bv_unsigned tp ->
    (bv_unsigned tp - 164 + 4 <= bv_unsigned sp - 368 \/ bv_unsigned sp <= bv_unsigned tp - 164) ->
    (bv_unsigned tp - 164 + 4 <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length str) <= bv_unsigned tp - 164) ->
    rdn SEGS0 mem (Z_to_bv 64 A_GOT_src0) 8 = Some (word_to_le_bytes 8 (wordZ A_GUARD_src0)) ->
    A_GOT_src0 + 8 <= bv_unsigned sp - 368 ->
    rdn SEGS0 mem (wordZ A_GUARD_src0) 8 = Some (word_to_le_bytes 8 CAN) ->
    (A_GUARD_src0 + 8 <= bv_unsigned sp - 368 \/ bv_unsigned sp <= A_GUARD_src0) ->
    (A_GUARD_src0 + 8 <= bv_unsigned tp - 164 \/ bv_unsigned tp - 164 + 4 <= A_GUARD_src0) ->
    A_GUARD_src0 + 8 < 2 ^ 64 ->
    (forall x, (RO1_LO_src0 <= x < RO1_HI_src0 \/ RO2_LO_src0 <= x < RO2_HI_src0) -> mem (Z_to_bv 64 x) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp -> getr regs 4%bv = tp ->
    getr regs 10%bv = s -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 10 ->
    exists regs' mem',
      msteps SEGS0 (mkst regs (wordZ A_STRTOUL_src0) mem rom) (mkst regs' ret mem' rom)
      /\ (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x)
      /\ getr regs' 1%bv = getr regs 1%bv
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 368), 368); (Z_to_bv 64 (bv_unsigned tp - 164), 4)].
  Proof.
    intros mem s sp tp CAN str A regs ret Hstr HA Hstop Hnws Hstk Hsp Hspro Hspstr Herr Htp Herrstk Herrstr
           Hgot Hgotstk Hcan HGstk HGerr HGnw Hro Hret H1 H2 H4 H10 H11 H12.
    assert (UG : bv_unsigned (wordZ A_GUARD_src0) = A_GUARD_src0) by (apply u_wordZ; unfold A_GUARD_src0; lia).
    assert (HOK : stH mem s sp tp (wordZ A_GUARD_src0) CAN str A).
    { constructor; try assumption; try (rewrite UG); unfold RO_MIN_src0, A_GOT_src0, A_GUARD_src0,
        RO1_LO_src0, RO1_HI_src0, RO2_LO_src0, RO2_HI_src0, TABA, C10A, GOTA in *; try lia.
      all: try (apply stopper_of_cont; exact Hstop).
      all: try exact Hgot.
      all: intros x Hx; apply Hro; lia. }
    destruct (ref_strtoul mem s sp tp (wordZ A_GUARD_src0) CAN str A rom regs ret HOK Hret H1 H2 H4 H10 H11 H12)
      as (regs' & mem' & RUN & AG & FM).
    exists regs', mem'. rewrite (wordZ_lit (0x23490 : word)) by reflexivity.
    split; [exact RUN|]. split; [exact (regs_agree_CS strtoul_clob regs regs' strtoul_clob_CS AG)|].
    split; [exact (regs_agree_ra strtoul_clob regs regs' strtoul_clob_ra AG)|exact FM].
  Qed.
End Src0.
