(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState Mem Cells Step Frame.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AUnw () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "WithSegs.uwc"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Lib.Frame.munch"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Frame.outside"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.Step.ro_cells"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"].


Section WithSegs.
  Variable segs : list Segment.

  Inductive uwc (m : mem) (LO TOP : Z) : Z -> Z -> Z -> Prop :=
  | uwc_stop : forall v F d, 0 <= d -> (v < LO \/ TOP - 16 <= v \/ v mod 8 <> 0) -> uwc m LO TOP v F d
  | uwc_link : forall v F d v', F + 16 <= v -> v < TOP - 16 -> v mod 8 = 0 -> 0 <= v' < 2^64 -> 0 <= d ->
      ro_cells segs m (v - 16) [C8 (Z_to_bv 64 v')] -> uwc m LO TOP v' v d -> uwc m LO TOP v F (d + 1)
  | uwc_cap : forall v F d, 28 <= d -> uwc m LO TOP v F d.

  #[using="Type"] Lemma uwc_nonneg : forall m LO TOP v F d, uwc m LO TOP v F d -> 0 <= d.
  Proof. intros m LO TOP v F d H. induction H; lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma uwc_mono : forall m LO TOP v F d d', uwc m LO TOP v F d -> d <= d' -> uwc m LO TOP v F d'.
  Proof.
    intros m LO TOP v F d d' H. revert d'. induction H; intros d' Hd.
    - apply uwc_stop; [lia| assumption].
    - replace d' with ((d' - 1) + 1) by lia. eapply uwc_link; eauto; try lia. apply IHuwc. lia.
    - apply uwc_cap. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma uwc_floor : forall m LO TOP v F F' d, uwc m LO TOP v F d -> F' <= F -> uwc m LO TOP v F' d.
  Proof.
    intros m LO TOP v F F' d H. revert F'. induction H; intros F' HF.
    - apply uwc_stop; assumption.
    - eapply uwc_link; eauto; try lia. 
    - apply uwc_cap. assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma uwc_transport : ltac2:(CDefT.buildp (gd_tbl_AUnw ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',Px,(0.&40.)(1.(0.&8.))PLO,$2.PTOP,$2.Pv,$2.PF,$2.Pd,$2.P,(3.R7.R5.R4.R3.R2.R1.)P,Pa,$2.P,(4.(5.R4.R1.)(6.R1.R6.))(7.(1.(0.&8.))A1.R9.(8.R2.)A1.R:.(8.R2.))(3.R8.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros m m' LO TOP v F d H. induction H; intros AG.
    - apply uwc_stop; assumption.
    - eapply uwc_link; eauto.
      + eapply (ro_cells_transport segs [(0, v - 16); (v - 8, 2^64)]); [eassumption| | cbn; repeat split; lia].
        intros x OUT. cbn [outside] in OUT. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR.
        rewrite <- (Z_to_bv_bv_unsigned x). apply AG. cbn [Z.pow Z.of_N Pos.pow N.of_nat] in XR. lia.
      + apply IHuwc. intros a Ha. apply AG. lia.
    - apply uwc_cap. assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma uwc_munch : ltac2:(CDefT.buildp (gd_tbl_AUnw ()) "PW,(9.$:.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PLO,$2.PTOP,$2.Pv,$2.PF,$2.Pd,$2.P,(3.R7.R5.R4.R3.R2.R1.)P,(;.R9.R8.R7.)P,(5.=R4.)P,(5.R7.(<.+2.+40.))P,Pa,$2.P,(4.(5.R7.R1.)(6.R1.R9.))(=.R>.R2.)(3.R;.R:.R9.R8.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros W m m' LO TOP v F d H MU F0 T64 OW. eapply uwc_transport; [exact H|].
    intros a Ha. apply MU. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    cbn [Z.pow Z.of_N Pos.pow N.of_nat Z.pow_pos Pos.iter Z.mul]. rewrite Z.mod_small by lia. apply OW. exact Ha.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma uwc_data : forall m LO TOP v F d, 0 <= d -> v < LO -> uwc m LO TOP v F d.
  Proof. intros. apply uwc_stop; [assumption| left; assumption]. Qed.

  #[using="Type"] Lemma uwc_high : forall m LO TOP v F d, 0 <= d -> TOP - 16 <= v -> uwc m LO TOP v F d.
  Proof. intros. apply uwc_stop; [assumption| right; left; assumption]. Qed.

  #[using="Type"] Lemma uwc_odd : forall m LO TOP v F d, 0 <= d -> v mod 8 <> 0 -> uwc m LO TOP v F d.
  Proof. intros. apply uwc_stop; [assumption| right; right; assumption]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma uwc_frame : ltac2:(CDefT.buildp (gd_tbl_AUnw ()) "Pm,P,(0.&40.)(1.(0.&8.))PLO,$2.PTOP,$2.Pu,$2.PF,$2.Pv',$2.Pd,$2.P,(5.(>.R3.+10.)R4.)P,(7.$2.(?.R5.+8.)=)P,(4.(5.=R4.)(6.R4.(<.+2.+40.)))P,(5.=R4.)P,(10.Vsegs,R;.(11.R8.+10.)(12.$13.(14.(15.&40.R6.))(16.$13.)))P,(3.R<.R;.R:.R7.R9.R6.)(3.R=.R<.R;.R:.R9.(>.R7.+1.))")
(* [comment removed for export] *).
  Proof.
    intros m LO TOP u F v' d HF AL RV Hd RO CH.
    destruct (Z_lt_le_dec u (TOP - 16)) as [LT|GE].
    - eapply uwc_link; eauto.
    - apply uwc_stop; [lia| right; left; lia].
  Qed.
End WithSegs.
