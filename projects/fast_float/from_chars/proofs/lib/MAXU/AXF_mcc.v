(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngWb.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb.AxZ2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits AxMalloc AXF_maz AXG_mfmem.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition Env0 (v : Z) : env := let w := wa v in Env (fun _ => w) (fun _ => []).
Definition YX : expr :=
  EAlu ALU_OR (EAluw ALU_SRL (EAlu ALU_OR (EAlu ALU_OR (EAluw ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 1)) (ELit 2)) (EAlu ALU_ADD (EVar 32) (ELit 1)))
                                          (EAluw ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 1)) (ELit 1))) (ELit 2))
              (EAluw ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 1)) (ELit 1)).
Definition SX : expr :=
  EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 8589934592) (EAlu ALU_OR (EAlu ALU_SRL (EAlu ALU_OR (EAlu ALU_SRL (EVar 32) (ELit 4)) (EVar 32)) (ELit 8))
                                                                     (EAlu ALU_OR (EAlu ALU_SRL (EVar 32) (ELit 4)) (EVar 32)))) (ELit 49))
              (EAlu ALU_OR (EAlu ALU_SRL (EAlu ALU_OR (EAlu ALU_SRL (EVar 32) (ELit 4)) (EVar 32)) (ELit 8)) (EAlu ALU_OR (EAlu ALU_SRL (EVar 32) (ELit 4)) (EVar 32))).
Definition cY (u : Z) : Z := m64 (zeval2 (Env0 u) YX).
Definition cS (y : Z) : Z := m64 (zeval2 (Env0 y) SX).
Definition dbx (s : Z) : Z := m64 (zeval2 (Env0 s) OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.DBX).

Definition mc_keep : list nat := [1;2;3;4;8;9;18;19;21;22;23;24;25;26;27]%nat.
Definition mc_keep20 : list nat := [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat.

Lemma m64_range : forall a, 0 <= m64 a < 2^64.
Proof. intros a. rewrite m64_ok. apply Z.mod_pos_bound. lia. Qed.

Ltac srg' HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

Lemma xor124 : forall d, 0 <= d <= 31 -> Z.lxor (4 * d) 124 = 124 - 4 * d.
Proof.
  intros d Hd.
  assert (C : forallb (fun d => Z.lxor (4 * d) 124 =? 124 - 4 * d) (zseq 0 32) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. apply Z.eqb_eq. apply C. apply In_zseq. lia.
Qed.

(* [comment removed for export] *)
Fixpoint forall_from (f : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S n' => f lo && forall_from f (lo + 1) n' end.

Lemma forall_from_ok : forall f n lo, forall_from f lo n = true -> forall x, lo <= x < lo + Z.of_nat n -> f x = true.
Proof.
  intros f n. induction n as [|n IH]; intros lo H x Hx; [cbn [Z.of_nat] in Hx; lia|].
  cbn [forall_from] in H. apply andb_true_iff in H as [H1 H2].
  destruct (Z.eq_dec x lo) as [->|Hne]; [exact H1|]. apply (IH (lo + 1) H2). lia.
Qed.

(* [comment removed for export] *)
Definition smear_chk (u : Z) : bool := let y := cY u in (y <=? 4294967295) && (cS y =? Z.ones (Z.log2 (u + 1))).
Lemma smear_chk_all : forall_from smear_chk 10 8181%nat = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition dbx_chk (L : Z) : bool := let ix := dbx (Z.ones L) in (0 <=? ix) && (ix <=? 31) && (znth ix debruijn =? L).
Lemma dbx_chk_all : forall_from dbx_chk 3 10%nat = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition rest_chk (u : Z) : bool :=
  let d := Z.log2 (u + 1) in let x := 124 - 4 * d in
  (3 <=? d) && (d <=? 12) && (0 <=? 121 - x) && (121 - x <=? 47) &&
  (let t1 := znth (121 - x) size_classes in let i2 := (if u <? t1 then 120 else 122) - x in
   (0 <=? i2) && (i2 <=? 47) && (let t2 := znth i2 size_classes in Z.lor i2 (if u <? t2 then 0 else 1) =? class_of_units u)).
Lemma rest_chk_all : forall_from rest_chk 10 8181%nat = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cY_eq : forall u, cY u = m64 (zeval2 (Env0 u) YX). Proof. reflexivity. Qed.
Lemma cS_eq : forall y, cS y = m64 (zeval2 (Env0 y) SX). Proof. reflexivity. Qed.
Lemma dbx_eq : forall s, dbx s = m64 (zeval2 (Env0 s) OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mc1.DBX). Proof. reflexivity. Qed.
Lemma cY_range : forall u, 0 <= cY u < 2^64. Proof. intros u. rewrite cY_eq. apply m64_range. Qed.

Strategy expand [smear_chk dbx_chk rest_chk].
Strategy opaque [cY cS dbx].

Lemma cls_facts : forall u, 10 <= u <= 8190 ->
  let y := cY u in let s := cS y in let ix := dbx s in let d := znth ix debruijn in let x := 124 - 4 * d in
  let t1 := znth (121 - x) size_classes in let i2 := (if u <? t1 then 120 else 122) - x in let t2 := znth i2 size_classes in
  (0 <= y <= 4294967295 /\ 0 <= s <= 4294967295 /\ 0 <= ix <= 31 /\ 0 <= d <= 31 /\ 0 <= 121 - x <= 47 /\ 0 <= i2 <= 47) /\
  Z.lor i2 (if u <? t2 then 0 else 1) = class_of_units u.
Proof.
  intros u Hu. cbv zeta.
  assert (N8181 : Z.of_nat 8181%nat = 8181) by (vm_compute; reflexivity).
  assert (N10 : Z.of_nat 10%nat = 10) by (vm_compute; reflexivity).
  pose proof (forall_from_ok _ _ _ smear_chk_all u ltac:(rewrite N8181; lia)) as SM. unfold smear_chk in SM. cbv zeta in SM.
  apply andb_true_iff in SM as [SM1 SM2]. apply Z.leb_le in SM1. apply Z.eqb_eq in SM2.
  pose proof (cY_range u) as R1.
  assert (LR : 3 <= Z.log2 (u + 1) <= 12).
  { split; [replace 3 with (Z.log2 8) by reflexivity | replace 12 with (Z.log2 8191) by reflexivity]; apply Z.log2_le_mono; lia. }
  pose proof (forall_from_ok _ _ _ dbx_chk_all (Z.log2 (u + 1)) ltac:(rewrite N10; lia)) as DB. unfold dbx_chk in DB. cbv zeta in DB.
  apply andb_true_iff in DB as [DB1 DB2]. apply andb_true_iff in DB1 as [DB0 DB1].
  apply Z.leb_le in DB0, DB1. apply Z.eqb_eq in DB2.
  pose proof (forall_from_ok _ _ _ rest_chk_all u ltac:(rewrite N8181; lia)) as RC. unfold rest_chk in RC. cbv zeta in RC.
  rewrite SM2, DB2.
  repeat rewrite andb_true_iff in RC. repeat rewrite Z.leb_le in RC. rewrite Z.eqb_eq in RC.
  destruct RC as ((((C1 & C2) & C3) & C4) & (C5 & C6) & C7).
  assert (ONES : 0 <= Z.ones (Z.log2 (u + 1)) <= 4294967295).
  { rewrite Z.ones_equiv. assert (2 ^ Z.log2 (u + 1) <= 2^12) by (apply Z.pow_le_mono_r; lia). pose proof (Z.pow_pos_nonneg 2 (Z.log2 (u+1)) ltac:(lia) ltac:(lia)). lia. }
  split; [repeat split; lia | exact C7].
Qed.

