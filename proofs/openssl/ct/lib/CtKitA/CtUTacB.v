(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnTacX BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnBoth Require Import UbKit AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Export ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUbTabB ApATac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import CtUbTabB ARun BnHeapA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma ablock_range_ub {AR : ARun.ARun} : forall A n, ablock_range A n -> al16 A /\ al8 A /\ 0 < A /\ A + n <= BnHeapA.ACEIL /\ 0 <= n.
Proof.
  intros A n (P & M & N & H & _). unfold al16, al8. refine (conj M (conj _ (conj P (conj H N)))).
  clear - M. Z.div_mod_to_equations. lia.
Qed.
Ltac ub_facts :=
  repeat match goal with
         | H : ablock_range ?A ?n |- _ =>
             lazymatch goal with
             | _ : al8 A |- _ => fail
             | |- _ => let X := fresh "UBF" in pose proof (ablock_range_ub A n H) as X;
                       destruct X as (?UBal16 & ?UBal8 & ?UBpos & ?UBhi & ?UBn)
             end
         end.

(* [comment removed for export] *)
Definition ub_kindx (pc : Z) : Z :=
  match CtUbTabB.ub_kind2 pc with
  | 0 => ApUbTabB.ub_kind pc
  | k => k
  end.

(* [comment removed for export] *)
Ltac ub1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let k := eval vm_compute in (ub_kindx pc) in
      lazymatch k with
      | 1%Z => zstep
      | 2%Z => ub_facts; first [ uchk | fail 100 "ub(ctB): cannot refute the UBSan trap condition at pc" pc ]
      | 3%Z => first [ uchk_inv | fail 100 "ub(ctB): cannot establish the branch over the UBSan trap jump at pc" pc ]
      end
  end.
Ltac ub := repeat ub1.

(* [comment removed for export] *)
Ltac upre := ual; ub; try (udecide; ub).
Ltac apre := ual; ab; repeat (progress ub; ab).

(* [comment removed for export] *)
Ltac show_ub := lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let k := eval vm_compute in (ub_kindx pc) in idtac "pc =" pc "ub_kindx =" k
  | |- _ => idtac "(no literal pc)" end.
