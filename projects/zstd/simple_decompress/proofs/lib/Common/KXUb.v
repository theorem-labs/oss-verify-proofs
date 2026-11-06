(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto.
Import ListNotations. Import KXS.
Open Scope Z_scope.

Lemma kxub_sltu : forall zs E a b, atoms_ok zs E ->
  bv_unsigned (edenot E (EAlu ALU_SLTU a b)) = Z.b2z (uz E zs a <? uz E zs b).
Proof.
  intros zs E a b HA. cbn [edenot]. rewrite u_sltu64, (uz_sound zs E a HA), (uz_sound zs E b HA).
  destruct (uz E zs a <? uz E zs b); reflexivity.
Qed.

Lemma kxub_lxor_pos : forall a b, 0 <= a -> 0 <= b -> (0 <? Z.lxor a b) = negb (a =? b).
Proof.
  intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|NE]; cbn [negb].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.ltb_lt. assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; tauto).
    assert (Z.lxor a b <> 0) by (intro X; apply Z.lxor_eq in X; contradiction). lia.
Qed.
Lemma kxub_lxor_lt1 : forall a b, 0 <= a -> 0 <= b -> (Z.lxor a b <? 1) = (a =? b).
Proof.
  intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.ltb_ge. assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; tauto).
    assert (Z.lxor a b <> 0) by (intro X; apply Z.lxor_eq in X; contradiction). lia.
Qed.

(* [comment removed for export] *)
Ltac kx_sltu_in H :=
  lazymatch goal with
  | KXA : atoms_ok ?zs ?E |- _ =>
      let nz := eval cbv in (length zs) in
      repeat match type of H with
             | context [bv_unsigned (edenot E (EAlu ALU_SLTU ?a ?b))] =>
                 let ua := kx_uz E zs nz a in
                 let ub := kx_uz E zs nz b in
                 let EQ := fresh "EQ" in
                 assert (EQ : bv_unsigned (edenot E (EAlu ALU_SLTU a b)) = Z.b2z (ua <? ub)) by exact (kxub_sltu zs E a b KXA);
                 rewrite EQ in H; clear EQ
             end
  end.

(* [comment removed for export] *)
Ltac kx_ub_norm H :=
  repeat match type of H with
         | context [?z mod 2^64] =>
             let HR := fresh "HR" in
             assert (HR : 0 <= z < 2^64) by (clear H; kx_lia);
             rewrite (Z.mod_small z (2^64) HR) in H; clear HR
         end;
  repeat match type of H with
         | context [0 <? Z.lxor ?a ?b] => rewrite (kxub_lxor_pos a b) in H by (clear H; kx_lia)
         | context [Z.lxor ?a ?b <? 1] => rewrite (kxub_lxor_lt1 a b) in H by (clear H; kx_lia)
         end.

(* [comment removed for export] *)
Ltac kx_ub_decide H :=
  repeat match type of H with
         | context [Z.ltb ?a ?b] =>
             first [ replace (Z.ltb a b) with true in H by (symmetry; apply Z.ltb_lt; clear H; kx_lia)
                   | replace (Z.ltb a b) with false in H by (symmetry; apply Z.ltb_ge; clear H; kx_lia) ]
         | context [Z.eqb ?a ?b] =>
             first [ replace (Z.eqb a b) with true in H by (symmetry; apply Z.eqb_eq; clear H; kx_lia)
                   | replace (Z.eqb a b) with false in H by (symmetry; apply Z.eqb_neq; clear H; kx_lia) ]
         end;
  cbn [Z.b2z negb Z.lxor Pos.lxor] in H.

(* [comment removed for export] *)
Ltac kx_ub H := kx_sltu_in H; kx_ub_norm H; kx_ub_decide H; first [ exfalso; apply H; reflexivity | discriminate H | exfalso; lia | exfalso; congruence ].

(* [comment removed for export] *)
Ltac kx_trap :=
  first [ solve [exfalso; kx_lia]
        | match goal with H : ?T |- _ => lazymatch T with context [edenot] => idtac end; lazymatch type of T with Prop => idtac end; solve [kx_ub H] end ].
