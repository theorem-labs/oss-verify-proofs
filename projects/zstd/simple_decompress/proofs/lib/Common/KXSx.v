(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
Import ListNotations.
Import KXS.
Open Scope Z_scope.

Fixpoint ez2 (E : env) (zs : list Z) (e : expr) {struct e} : Z :=
  match e with
  | EExt true O 4 a => ez2 E zs a
  | EAluw ALU_ADD a b => ez2 E zs a + ez2 E zs b
  | EAlu ALU_ADD a b => ez2 E zs a + ez2 E zs b
  | _ => ez E zs e
  end.

Fixpoint sxc (E : env) (zs : list Z) (e : expr) {struct e} : Prop :=
  match e with
  | EExt true O 4 a => sxc E zs a /\ 0 <= ez2 E zs a < 2^31
  | EAluw ALU_ADD a b => sxc E zs a /\ sxc E zs b /\ 0 <= ez2 E zs a + ez2 E zs b < 2^31
  | EAlu ALU_ADD a b => sxc E zs a /\ sxc E zs b
  | _ => True
  end.

Lemma ez2_sound : forall zs E e, atoms_ok zs E -> sxc E zs e -> edenot E e = Z_to_bv 64 (ez2 E zs e).
Proof.
  intros zs E e HA.
  induction e as [z|j|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros HS;
    try exact (ez_sound zs E _ HA).
  - (* [comment removed for export] *)
    destruct op; try exact (ez_sound zs E _ HA).
    cbn [sxc] in HS. destruct HS as [Sa Sb]. cbn [ez2 edenot]. rewrite (IHa Sa), (IHb Sb).
    apply word_eq_Z. rewrite u_add64, !Z_to_bv_unsigned, !AS.PropExec.bv_wrap64_mod, <- Zplus_mod. reflexivity.
  - (* [comment removed for export] *)
    destruct op; try exact (ez_sound zs E _ HA).
    cbn [sxc] in HS. destruct HS as (Sa & Sb & R). cbn [ez2 edenot]. rewrite (IHa Sa), (IHb Sb).
    apply word_eq_Z.
    rewrite (u_addw_small _ _ (ez2 E zs a + ez2 E zs b) R).
    + symmetry. apply Z.mod_small. lia.
    + rewrite !Z_to_bv_unsigned, !AS.PropExec.bv_wrap64_mod.
      exists (- (ez2 E zs a / 2^64) * 2^32 - (ez2 E zs b / 2^64) * 2^32).
      pose proof (Z.div_mod (ez2 E zs a) (2^64) ltac:(lia)). pose proof (Z.div_mod (ez2 E zs b) (2^64) ltac:(lia)). lia.
  - (* [comment removed for export] *)
    destruct sx; try exact (ez_sound zs E _ HA).
    destruct lo; try exact (ez_sound zs E _ HA).
    do 4 (destruct n as [|n]; try exact (ez_sound zs E _ HA)).
    destruct n; try exact (ez_sound zs E _ HA).
    cbn [sxc] in HS. destruct HS as [Sa R]. cbn [ez2 edenot]. rewrite (IHa Sa).
    unfold ext_val, ext_Z. rewrite Z_to_bv_unsigned, AS.PropExec.bv_wrap64_mod.
    change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
    change (2 ^ (8 * Z.of_nat 4)) with (2^32). change (8 * N.of_nat 4)%N with 32%N.
    rewrite (Z.mod_small (ez2 E zs a) (2^64)) by lia. rewrite (Z.mod_small (ez2 E zs a) (2^32)) by lia.
    rewrite swrap32_small by lia. reflexivity.
Qed.

Lemma ez2_sound_u : forall zs E e, atoms_ok zs E -> sxc E zs e -> 0 <= ez2 E zs e < 2^64 -> bv_unsigned (edenot E e) = ez2 E zs e.
Proof.
  intros zs E e HA HS HR. rewrite (ez2_sound zs E e HA HS), Z_to_bv_unsigned, AS.PropExec.bv_wrap64_mod. apply Z.mod_small. exact HR.
Qed.

(* [comment removed for export] *)
Ltac kx_ez2 E zs nz e :=
  lazymatch e with
  | EExt true O 4 ?a => kx_ez2 E zs nz a
  | EAluw ALU_ADD ?a ?b => let x := kx_ez2 E zs nz a in let y := kx_ez2 E zs nz b in constr:(x + y)
  | EAlu ALU_ADD ?a ?b => let x := kx_ez2 E zs nz a in let y := kx_ez2 E zs nz b in constr:(x + y)
  | _ => kx_ez E zs nz e
  end.

Ltac kx_sx_has e :=
  lazymatch e with
  | context [EExt true] => idtac
  | context [EAluw] => idtac
  end.

(* [comment removed for export] *)
Ltac kx_sxc E zs nz e :=
  lazymatch e with
  | EExt true O 4 ?a => let p := kx_sxc E zs nz a in let x := kx_ez2 E zs nz a in constr:(p /\ 0 <= x < 2^31)
  | EAluw ALU_ADD ?a ?b =>
      let p := kx_sxc E zs nz a in let q := kx_sxc E zs nz b in let x := kx_ez2 E zs nz a in let y := kx_ez2 E zs nz b in
      constr:(p /\ q /\ 0 <= x + y < 2^31)
  | EAlu ALU_ADD ?a ?b => let p := kx_sxc E zs nz a in let q := kx_sxc E zs nz b in constr:(p /\ q)
  | _ => constr:(True)
  end.

(* [comment removed for export] *)
Ltac kx_sx1 :=
  match goal with
  | KXA : atoms_ok ?zs ?E |- context [bv_unsigned (edenot ?E ?e)] =>
      kx_sx_has e;
      let nz := kx_len zs in
      let z := kx_ez2 E zs nz e in
      let P := kx_sxc E zs nz e in
      let H := fresh "KXSX" in
      assert (H : bv_unsigned (edenot E e) = z);
      [ refine (ez2_sound_u zs E e KXA (_ : P) (_ : 0 <= z < 2^64)); [ repeat split; Lia.lia | Lia.lia ]
      | rewrite !H in *; clear H ]
  end.
Ltac kx_sx :=
  lazymatch goal with
  | |- context [EExt true] => kx_read_ranges; repeat kx_sx1
  | |- context [EAluw] => kx_read_ranges; repeat kx_sx1
  | _ => idtac
  end.
