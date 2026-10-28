(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep CidBits AW_AllocBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition hb1Al_of (o : Z) : Z := Z.lor (Z.land (Z.lor (o - o mod 2 ^ 2) 1) 143) 64.
Lemma hb1Al_facts : forall o, 0 <= o < 256 -> 0 <= hb1Al_of o < 256 /\ b1_ok (Z.land (hb1Al_of o) 243).
Proof.
  intros o Ho.
  pose proof (forall_rangeZ_spec (fun o => let v := hb1Al_of o in
       (0 <=? v) && (v <? 256) && (0 <=? Z.land v 243) && (Z.land v 243 <? 256) && (Z.land v 243 mod 128 =? 0x41)) 0 256 o) as C.
  cbn beta in C. specialize (C ltac:(hci; vm_compute; reflexivity) ltac:(hci; lia) ltac:(hci; lia)).
  cbn zeta in C. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt, Z.eqb_eq in C. unfold b1_ok. lia.
Qed.

Section HCW3.
  Context {HCEIL : HeapCeil}.
(* [comment removed for export] *)
Definition aframeAl (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m1 : mem) (j8 : list byte) : Prop :=
  rw_cells asegs m1 (bv_unsigned sp + -128)
    [CB 8 j8; C8 (wz 1); C8 (wz 64); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
End HCW3.
