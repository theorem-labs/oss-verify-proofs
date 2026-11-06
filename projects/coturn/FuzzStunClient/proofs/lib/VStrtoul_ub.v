(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec Hoare StepTac ZStores RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbStrtoul.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VCert VContract VContractSound VContractSound_src0 VStrtoul_src0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Abbreviation SEGSU := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition A_STRTOUL_ub : Z := 0x23938.
Definition A_GOT_ub : Z := 0x257a0.
Definition A_GUARD_ub : Z := 0x56ca0.
Definition RO1_LO_ub : Z := 0x10570.  Definition RO1_HI_ub : Z := 0x10578.
Definition RO2_LO_ub : Z := 0x1146c.  Definition RO2_HI_ub : Z := 0x1156d.
Definition RO_MIN_ub : Z := 0x11574.

(* [comment removed for export] *)
Lemma stopper_of_contU b : strtoul_cont b = false -> UbStrtoul.stopper b.
Proof.
  unfold strtoul_cont, UbStrtoul.stopper, UbStrtoul.isdig, UbStrtoul.issp, UbStrtoul.issign. intros H.
  apply Bool.orb_false_elim in H as [H H5]. apply Bool.orb_false_elim in H as [H H4].
  apply Bool.orb_false_elim in H as [H H3]. apply Bool.orb_false_elim in H as [H1 H2].
  rewrite H1, H2, H3, H4, H5. repeat split; reflexivity.
Qed.

Lemma strtoul_clobU_CS : forallb (fun r : reg => existsb (Z.eqb (bv_unsigned r)) CALLER_SAVED) UbStrtoul.strtoul_clob = true.
Proof. reflexivity. Qed.
Lemma strtoul_clobU_ra : existsb (fun r : reg => Z.eqb (bv_unsigned r) 1) UbStrtoul.strtoul_clob = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma GOT_BYTES_ub :
  rdn SEGSU (fun _ => None) (wordZ A_GOT_ub) 8 = Some (word_to_le_bytes 8 (wordZ A_GUARD_ub)).
Proof.
  assert (H : option_map (map bv_unsigned) (rdn SEGSU (fun _ => None) (wordZ A_GOT_ub) 8)
              = option_map (map bv_unsigned) (Some (word_to_le_bytes 8 (wordZ A_GUARD_ub)))) by (vm_compute; reflexivity).
  destruct (rdn _ _ _ _) as [bs|]; [|discriminate]. cbn [option_map] in H. injection H as H'.
  f_equal. apply bytes_eq_of_unsigned. exact H'.
Qed.

Section Ub.
  Variable rom : word -> option byte.

  Lemma STRTOUL_ub : forall mem (s sp tp CAN : word) (str : list byte) (A : Z) regs (ret : word),
    rdn SEGSU mem s (length str) = Some str ->
    0 <= A < Z.of_nat (length str) ->
    strtoul_cont (bv_unsigned (nth (Z.to_nat A) str (Z_to_bv 8 0))) = false ->
    bv_unsigned s + Z.of_nat (length str) < 2 ^ 64 - 8 ->
    store_ok SEGSU mem (Z_to_bv 64 (bv_unsigned sp - 368)) 368 = true ->
    368 <= bv_unsigned sp < 2 ^ 64 ->
    RO_MIN_ub <= bv_unsigned sp - 368 ->
    (bv_unsigned sp <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length str) <= bv_unsigned sp - 368) ->
    store_ok SEGSU mem (Z_to_bv 64 (bv_unsigned tp - 164)) 4 = true ->
    RO_MIN_ub + 164 <= bv_unsigned tp ->
    (bv_unsigned tp - 164 + 4 <= bv_unsigned sp - 368 \/ bv_unsigned sp <= bv_unsigned tp - 164) ->
    (bv_unsigned tp - 164 + 4 <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length str) <= bv_unsigned tp - 164) ->
    rdn SEGSU mem (Z_to_bv 64 A_GOT_ub) 8 = Some (word_to_le_bytes 8 (wordZ A_GUARD_ub)) ->
    A_GOT_ub + 8 <= bv_unsigned sp - 368 ->
    rdn SEGSU mem (wordZ A_GUARD_ub) 8 = Some (word_to_le_bytes 8 CAN) ->
    (A_GUARD_ub + 8 <= bv_unsigned sp - 368 \/ bv_unsigned sp <= A_GUARD_ub) ->
    (A_GUARD_ub + 8 <= bv_unsigned tp - 164 \/ bv_unsigned tp - 164 + 4 <= A_GUARD_ub) ->
    A_GUARD_ub + 8 < 2 ^ 64 ->
    (forall x, (RO1_LO_ub <= x < RO1_HI_ub \/ RO2_LO_ub <= x < RO2_HI_ub) -> mem (Z_to_bv 64 x) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp -> getr regs 4%bv = tp ->
    getr regs 10%bv = s -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 10 ->
    exists regs' mem',
      msteps SEGSU (mkst regs (wordZ A_STRTOUL_ub) mem rom) (mkst regs' ret mem' rom)
      /\ (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x)
      /\ getr regs' 1%bv = getr regs 1%bv
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 368), 368); (Z_to_bv 64 (bv_unsigned tp - 164), 4)].
  Proof.
    intros mem s sp tp CAN str A regs ret Hstr HA Hstop Hnws Hstk Hsp Hspro Hspstr Herr Htp Herrstk Herrstr
           Hgot Hgotstk Hcan HGstk HGerr HGnw Hro Hret H1 H2 H4 H10 H11 H12.
    assert (UG : bv_unsigned (wordZ A_GUARD_ub) = A_GUARD_ub) by (apply u_wordZ; unfold A_GUARD_ub; lia).
    assert (HOK : UbStrtoul.stH mem s sp tp (wordZ A_GUARD_ub) CAN str A).
    { constructor; try assumption; try (rewrite UG); unfold RO_MIN_ub, A_GOT_ub, A_GUARD_ub,
        RO1_LO_ub, RO1_HI_ub, RO2_LO_ub, RO2_HI_ub, UbStrtoul.TABA, UbStrtoul.C10A, UbStrtoul.GOTA in *; try lia.
      all: try (apply stopper_of_contU; exact Hstop).
      all: try exact Hgot.
      all: intros x Hx; apply Hro; lia. }
    destruct (UbStrtoul.ref_strtoul mem s sp tp (wordZ A_GUARD_ub) CAN str A rom regs ret HOK Hret H1 H2 H4 H10 H11 H12)
      as (regs' & mem' & RUN & AG & FM).
    exists regs', mem'. rewrite (wordZ_lit (0x23938 : word)) by reflexivity.
    split; [exact RUN|]. split; [exact (regs_agree_CS UbStrtoul.strtoul_clob regs regs' strtoul_clobU_CS AG)|].
    split; [exact (regs_agree_ra UbStrtoul.strtoul_clob regs regs' strtoul_clobU_ra AG)|exact FM].
  Qed.
End Ub.
