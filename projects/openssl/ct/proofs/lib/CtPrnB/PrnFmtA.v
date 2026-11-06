(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS Arr FP Frame Cells Step Mem. 
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApLogic ApErr PrintfModel PrintfModelX.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Printf_sn.
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit FX_lib F_pop_arg F_printf_iface I_vsnstmt.
From OSSVerify.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OSSVerify.Proofs.openssl.ct.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require Import RT_iface2 LibKitA ARun BnHeapA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA.
From OSSVerify.Proofs.openssl.ct.lib.CtFrameB Require Import AFrameKit AFrameCall AFrameTac.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApUTacB.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_bio_write Fr_BIO_vprintf Fr_BIO_printf W_bio_printf W_bio_printf2 W_bio_vprintfG.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import W_bio_printf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition A_C12_A : Z := 0x715e0.      (* [comment removed for export] *)
Definition A_EMPTYH_A : Z := 0x71580.   (* [comment removed for export] *)
Definition A_C13_A : Z := 0x71600.      (* [comment removed for export] *)
Definition A_C14_A : Z := 0x71620.      (* [comment removed for export] *)
Definition A_C15_A : Z := 0x71640.      (* [comment removed for export] *)

Lemma fmt_C12_roA : ro_bytes ctbsegs A_C12_A (zb FMT_C12). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C13_roA : ro_bytes ctbsegs A_C13_A (zb FMT_C13). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C14_roA : ro_bytes ctbsegs A_C14_A (zb FMT_C14). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C15_roA : ro_bytes ctbsegs A_C15_A (zb FMT_C15). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma emptyh_lit_roA : ro_bytes ctbsegs A_EMPTYH_A (zb [] ++ Z_to_bv 8 0 :: zb [0; 0; 0; 0; 0; 0; 0]). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Local Ltac accg A g := intros AR' Σ' OW' LB' m' H; eapply (af_lib_acc_lit _ (@ar_AF AR') Σ' m' g); [exact (@AH_art AR' _ _ _ _ H)| vm_compute; reflexivity| unfold A; cbn; clear; lia| unfold A; cbn; clear; lia].

Lemma vfmtA_C12 : vfmtA_ok A_C12_A FMT_C12 [PA_i 20; PA_s []] (zrepeat 32 20).
Proof.
  pose proof printf_piecesx_C12 as P.
  split; [exact fmt_C12_roA|]. split; [exact fmt_bytes_C12|].
  split; [unfold A_C12_A; clear; lia|]. split; [unfold A_C12_A; change (zlength FMT_C12) with 4; cbv; discriminate|].
  split. { change (zlength FMT_C12) with 4. accg A_C12_A (0x715e0, 4, 32). }
  split; [exact pass1x_ok_C12|].
  split. { change (zlength (zrepeat 32 20)) with 20. replace (zrepeat 32 20) with (concat [[]; zrepeat 32 20; []; []]) by (cbn [concat app]; rewrite app_nil_r; reflexivity).
           apply (printf_modelx_sn _ _ _ _ P). unfold OSSVerify.Proofs.openssl.ct.lib.P.F_printf_iface.SN_CAP. cbn [concat app]. rewrite app_nil_r, zlength_zrepeat by lia. clear; lia. }
  split; [apply fp_callsx_is0|]. split; reflexivity.
Qed.

Lemma vfmtA_C14 : vfmtA_ok A_C14_A FMT_C14 [] [10].
Proof.
  pose proof printf_piecesx_C14 as P.
  split; [exact fmt_C14_roA|]. split; [exact fmt_bytes_C14|].
  split; [unfold A_C14_A; clear; lia|]. split; [unfold A_C14_A; change (zlength FMT_C14) with 2; cbv; discriminate|].
  split. { change (zlength FMT_C14) with 2. accg A_C14_A (0x71620, 2, 32). }
  split; [exact pass1x_ok_C14|].
  split. { change [10] with (concat [[10]]). change (zlength (concat [[10]])) with 1. apply (printf_modelx_sn _ _ _ _ P). unfold OSSVerify.Proofs.openssl.ct.lib.P.F_printf_iface.SN_CAP. change (zlength (concat [[10]])) with 1. clear; lia. }
  split; [apply fp_callsx_nil|]. split; reflexivity.
Qed.

Lemma vfmtA_C13 : forall b, 0 <= b < 256 -> vfmtA_ok A_C13_A FMT_C13 [PA_u b] (hex2 b ++ [58]).
Proof.
  intros b Hb. destruct (printf_piecesx_C13 b Hb) as (ps & P & CC). pose proof (printf_piecesx_count _ _ _ _ P) as L.
  split; [exact fmt_C13_roA|]. split; [exact fmt_bytes_C13|].
  split; [unfold A_C13_A; clear; lia|]. split; [unfold A_C13_A; change (zlength FMT_C13) with 6; cbv; discriminate|].
  split. { change (zlength FMT_C13) with 6. accg A_C13_A (0x71600, 6, 32). }
  split; [exact pass1x_ok_C13|].
  split. { rewrite <- CC, L. apply (printf_modelx_sn _ _ _ _ P). rewrite L. unfold OSSVerify.Proofs.openssl.ct.lib.P.F_printf_iface.SN_CAP. clear; lia. }
  split; [apply fp_callsx_u|]. split; reflexivity.
Qed.

Lemma vfmtA_C15 : forall b, 0 <= b < 256 -> vfmtA_ok A_C15_A FMT_C15 [PA_u b] (hex2 b).
Proof.
  intros b Hb. destruct (printf_piecesx_C15 b Hb) as (ps & P & CC). pose proof (printf_piecesx_count _ _ _ _ P) as L.
  split; [exact fmt_C15_roA|]. split; [exact fmt_bytes_C15|].
  split; [unfold A_C15_A; clear; lia|]. split; [unfold A_C15_A; change (zlength FMT_C15) with 5; cbv; discriminate|].
  split. { change (zlength FMT_C15) with 5. accg A_C15_A (0x71640, 5, 32). }
  split; [exact pass1x_ok_C15|].
  split. { rewrite <- CC, L. apply (printf_modelx_sn _ _ _ _ P). rewrite L. unfold OSSVerify.Proofs.openssl.ct.lib.P.F_printf_iface.SN_CAP. clear; lia. }
  split; [apply fp_callsx_u|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma emptyh_vargA : forall OW LB m, vargA_ok OW LB m (Z_to_bv 64 A_EMPTYH_A) (PA_s []).
Proof.
  intros OW LB m. unfold vargA_ok, A_EMPTYH_A. rewrite (unsigned_lit 464256) by (clear; lia).
  exists (zb [0; 0; 0; 0; 0; 0; 0]). change (zlength (@nil Z)) with 0. change (zlength (zb [0; 0; 0; 0; 0; 0; 0])) with 7.
  split; [constructor|]. split; [clear; lia|]. split; [clear; cbn; lia|].
  right. split; [clear; lia|]. split; [cbv; discriminate|]. split; [exact emptyh_lit_roA|].
  intros AR' Σ' m' H'. eapply (af_lib_acc_lit _ (@ar_AF AR') Σ' m' (0x71580, 1, 32)); [exact (@AH_art AR' _ _ _ _ H')| vm_compute; reflexivity| cbn; clear; lia| cbn; clear; lia].
Qed.
