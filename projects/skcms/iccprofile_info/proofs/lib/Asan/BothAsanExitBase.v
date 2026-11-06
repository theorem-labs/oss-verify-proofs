(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanAcct BothAsanAcctImages.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Export SumWalkTac.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Export AsanAcctNoLazy.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Section WithFP1. Context {FP : PropExec.FPState}.
Definition Asan_wx_nowrap' : wx_segs_nowrap ASEGS := Asan_wx_nowrap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma asan_wseg_wd1 : wseg_ok ASEGS (0xa3ed0 : word) 760%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_wseg_wd2 : wseg_ok ASEGS (0x5da8c8 : word) 133040%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma store_ok_data1 : forall m (a : word) n,
  (0xa3ed0 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0xa41c8)%Z ->
  store_ok ASEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window ASEGS m (0xa3ed0 : word) a 760%nat n 0xa3ed0 0xa41c8);
    [reflexivity | reflexivity | lia | exact asan_wseg_wd1 | exact Hlo | exact Hhi].
Qed.

Lemma store_ok_data2 : forall m (a : word) n,
  (0x5da8c8 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x5fb078)%Z ->
  store_ok ASEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window ASEGS m (0x5da8c8 : word) a 133040%nat n 0x5da8c8 0x5fb078);
    [reflexivity | reflexivity | lia | exact asan_wseg_wd2 | exact Hlo | exact Hhi].
Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac sok_data := store_ok_peel;
  first [ apply store_ok_data1; zsimp; lia | apply store_ok_data2; zsimp; lia ].

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFP2. Context {FP : PropExec.FPState}.
Lemma asan_window_data : window_in_seg_b ASEGS 0xa1000 0x5fd000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_window_got : window_in_seg_b ASEGS 0x9f000 0xa1000 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma data_avoids : forall H (a : Z) n,
  H_off_segments ASEGS H ->
  (0xa1000 <= a)%Z -> (a + Z.of_nat n <= 0x5fd000)%Z ->
  range_avoids H (Z_to_bv 64 a) n.
Proof.
  intros H a n HH Hlo Hhi.
  apply (range_avoids_in_window ASEGS H 0xa1000 0x5fd000 a n HH asan_window_data); lia.
Qed.

(* [comment removed for export] *)
Lemma got_avoids : forall H (a : Z) n,
  H_off_segments ASEGS H ->
  (0x9f000 <= a)%Z -> (a + Z.of_nat n <= 0xa1000)%Z ->
  range_avoids H (Z_to_bv 64 a) n.
Proof.
  intros H a n HH Hlo Hhi.
  apply (range_avoids_in_window ASEGS H 0x9f000 0xa1000 a n HH asan_window_got); lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_mrestrict_data : forall H mem (a : Z) n bs,
  H_off_segments ASEGS H ->
  (0xa1000 <= a)%Z -> (a + Z.of_nat n <= 0x5fd000)%Z ->
  rdn ASEGS mem (Z_to_bv 64 a) n = Some bs ->
  rdn ASEGS (mrestrict H mem) (Z_to_bv 64 a) n = Some bs.
Proof.
  intros H mem a n bs HH Hlo Hhi Hr. rewrite (rdn_mrestrict_eq ASEGS H); [exact Hr|].
  apply data_avoids; assumption.
Qed.

Lemma rdn_mrestrict_got : forall H mem (a : Z) n bs,
  H_off_segments ASEGS H ->
  (0x9f000 <= a)%Z -> (a + Z.of_nat n <= 0xa1000)%Z ->
  rdn ASEGS mem (Z_to_bv 64 a) n = Some bs ->
  rdn ASEGS (mrestrict H mem) (Z_to_bv 64 a) n = Some bs.
Proof.
  intros H mem a n bs HH Hlo Hhi Hr. rewrite (rdn_mrestrict_eq ASEGS H); [exact Hr|].
  apply got_avoids; assumption.
Qed.

(* [comment removed for export] *)
Lemma rdn_mrestrict_av : forall H mem (a : word) n bs,
  range_avoids H a n ->
  rdn ASEGS mem a n = Some bs ->
  rdn ASEGS (mrestrict H mem) a n = Some bs.
Proof. intros H mem a n bs Hav Hr. rewrite (rdn_mrestrict_eq ASEGS H); assumption. Qed.

Lemma store_ok_mrestrict_av : forall H mem (a : word) n,
  range_avoids H a n ->
  store_ok ASEGS mem a n = true ->
  store_ok ASEGS (mrestrict H mem) a n = true.
Proof. intros H mem a n Hav Hs. rewrite (store_ok_mrestrict_eq ASEGS H); assumption. Qed.

(* [comment removed for export] *)
Lemma range_avoids_subZ : forall H (z : Z) n (b : Z) k,
  range_avoids H (Z_to_bv 64 z) n ->
  (0 <= z < 2 ^ 64)%Z ->
  (z <= b)%Z -> (b + Z.of_nat k <= z + Z.of_nat n)%Z ->
  range_avoids H (Z_to_bv 64 b) k.
Proof.
  intros H z n b k Hr Hz Hlo Hhi.
  apply (range_avoids_sub H (Z_to_bv 64 z) n b k Hr); rewrite u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop :=
  rdn ASEGS mem (Z_to_bv 64 (f + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn ASEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn ASEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn ASEGS mem (Z_to_bv 64 (f + 8)) 8%nat = Some (word_to_le_bytes 8 rp)
  /\ rdn ASEGS mem (Z_to_bv 64 (f + 16)) 8%nat = Some (word_to_le_bytes 8 rp).

(* [comment removed for export] *)
Definition stdio_globals (mem : word -> option byte) : Prop :=
  rdn ASEGS mem (Z_to_bv 64 0x5fac03) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn ASEGS mem (Z_to_bv 64 0x5fb068) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn ASEGS mem (Z_to_bv 64 0xa4198) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa40b0)) (* [comment removed for export] *)
  /\ rdn ASEGS mem (Z_to_bv 64 0xa40a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa3fc0)) (* [comment removed for export] *)
  /\ rdn ASEGS mem (Z_to_bv 64 0xa3fb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa3ed0)). (* [comment removed for export] *)

Lemma file_clean_mrestrict : forall H mem f wp rp,
  H_off_segments ASEGS H -> (0xa1000 <= f)%Z -> (f + 232 <= 0x5fd000)%Z ->
  file_clean mem f wp rp -> file_clean (mrestrict H mem) f wp rp.
Proof.
  intros H mem f wp rp HH Flo Fhi (A & B & C & D & E).
  repeat split; (eapply rdn_mrestrict_data; [exact HH | | | eassumption]); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma stdio_globals_mrestrict : forall H mem,
  H_off_segments ASEGS H -> stdio_globals mem -> stdio_globals (mrestrict H mem).
Proof.
  intros H mem HH (A & B & C & D & E).
  repeat split; (eapply rdn_mrestrict_data; [exact HH | | | eassumption]); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.
End WithFP2.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
