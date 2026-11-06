(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXSx.
Import ListNotations.
Import KXS.
Open Scope Z_scope.

Fixpoint ez3 (E : env) (zs : list Z) (e : expr) {struct e} : Z :=
  match e with
  | EExt true O 4 a => ez3 E zs a
  | EExt false O 4 a => ez3 E zs a
  | EAluw ALU_ADD a b => ez3 E zs a + ez3 E zs b
  | EAlu ALU_ADD a b => ez3 E zs a + ez3 E zs b
  | _ => ez E zs e
  end.

Fixpoint sxc3 (E : env) (zs : list Z) (e : expr) {struct e} : Prop :=
  match e with
  | EExt true O 4 a => sxc3 E zs a /\ 0 <= ez3 E zs a < 2^31
  | EExt false O 4 a => sxc3 E zs a /\ 0 <= ez3 E zs a < 2^32
  | EAluw ALU_ADD a b => sxc3 E zs a /\ sxc3 E zs b /\ 0 <= ez3 E zs a + ez3 E zs b < 2^31
  | EAlu ALU_ADD a b => sxc3 E zs a /\ sxc3 E zs b
  | _ => True
  end.

Lemma ez3_sound : forall zs E e, atoms_ok zs E -> sxc3 E zs e -> edenot E e = Z_to_bv 64 (ez3 E zs e).
Proof.
  intros zs E e HA.
  induction e as [z|j|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros HS;
    try exact (ez_sound zs E _ HA).
  - (* [comment removed for export] *)
    destruct op; try exact (ez_sound zs E _ HA).
    cbn [sxc3] in HS. destruct HS as [Sa Sb]. cbn [ez3 edenot]. rewrite (IHa Sa), (IHb Sb).
    apply word_eq_Z. rewrite u_add64, !Z_to_bv_unsigned, !AS.PropExec.bv_wrap64_mod, <- Zplus_mod. reflexivity.
  - (* [comment removed for export] *)
    destruct op; try exact (ez_sound zs E _ HA).
    cbn [sxc3] in HS. destruct HS as (Sa & Sb & R). cbn [ez3 edenot]. rewrite (IHa Sa), (IHb Sb).
    apply word_eq_Z.
    rewrite (u_addw_small _ _ (ez3 E zs a + ez3 E zs b) R).
    + symmetry. apply Z.mod_small. lia.
    + rewrite !Z_to_bv_unsigned, !AS.PropExec.bv_wrap64_mod.
      exists (- (ez3 E zs a / 2^64) * 2^32 - (ez3 E zs b / 2^64) * 2^32).
      pose proof (Z.div_mod (ez3 E zs a) (2^64) ltac:(lia)). pose proof (Z.div_mod (ez3 E zs b) (2^64) ltac:(lia)). lia.
  - (* [comment removed for export] *)
    destruct lo; [|destruct sx; exact (ez_sound zs E _ HA)].
    do 4 (destruct n as [|n]; [destruct sx; exact (ez_sound zs E _ HA)|]).
    destruct n; [|destruct sx; exact (ez_sound zs E _ HA)].
    destruct sx.
    + cbn [sxc3] in HS. destruct HS as [Sa R]. cbn [ez3 edenot]. rewrite (IHa Sa).
      unfold ext_val, ext_Z. rewrite Z_to_bv_unsigned, AS.PropExec.bv_wrap64_mod.
      change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
      change (2 ^ (8 * Z.of_nat 4)) with (2^32). change (8 * N.of_nat 4)%N with 32%N.
      rewrite (Z.mod_small (ez3 E zs a) (2^64)) by lia. rewrite (Z.mod_small (ez3 E zs a) (2^32)) by lia.
      rewrite swrap32_small by lia. reflexivity.
    + cbn [sxc3] in HS. destruct HS as [Sa R]. cbn [ez3 edenot]. rewrite (IHa Sa).
      unfold ext_val, ext_Z. rewrite Z_to_bv_unsigned, AS.PropExec.bv_wrap64_mod.
      change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
      change (2 ^ (8 * Z.of_nat 4)) with (2^32).
      rewrite (Z.mod_small (ez3 E zs a) (2^64)) by lia. rewrite (Z.mod_small (ez3 E zs a) (2^32)) by lia.
      reflexivity.
Qed.

Lemma ez3_sound_u : forall zs E e, atoms_ok zs E -> sxc3 E zs e -> 0 <= ez3 E zs e < 2^64 -> bv_unsigned (edenot E e) = ez3 E zs e.
Proof.
  intros zs E e HA HS HR. rewrite (ez3_sound zs E e HA HS), Z_to_bv_unsigned, AS.PropExec.bv_wrap64_mod. apply Z.mod_small. exact HR.
Qed.

(* [comment removed for export] *)
Ltac kx_ez3 E zs nz e :=
  lazymatch e with
  | EExt true O 4 ?a => kx_ez3 E zs nz a
  | EExt false O 4 ?a => kx_ez3 E zs nz a
  | EAluw ALU_ADD ?a ?b => let x := kx_ez3 E zs nz a in let y := kx_ez3 E zs nz b in constr:(x + y)
  | EAlu ALU_ADD ?a ?b => let x := kx_ez3 E zs nz a in let y := kx_ez3 E zs nz b in constr:(x + y)
  | _ => kx_ez E zs nz e
  end.

Ltac kx_sxc3 E zs nz e :=
  lazymatch e with
  | EExt true O 4 ?a => let p := kx_sxc3 E zs nz a in let x := kx_ez3 E zs nz a in constr:(p /\ 0 <= x < 2^31)
  | EExt false O 4 ?a => let p := kx_sxc3 E zs nz a in let x := kx_ez3 E zs nz a in constr:(p /\ 0 <= x < 2^32)
  | EAluw ALU_ADD ?a ?b =>
      let p := kx_sxc3 E zs nz a in let q := kx_sxc3 E zs nz b in let x := kx_ez3 E zs nz a in let y := kx_ez3 E zs nz b in
      constr:(p /\ q /\ 0 <= x + y < 2^31)
  | EAlu ALU_ADD ?a ?b => let p := kx_sxc3 E zs nz a in let q := kx_sxc3 E zs nz b in constr:(p /\ q)
  | _ => constr:(True)
  end.

Ltac kx_sx3_has e :=
  lazymatch e with
  | context [EExt true O 4] => idtac
  | context [EExt false O 4] => idtac
  | context [EAluw ALU_ADD] => idtac
  end.

(* [comment removed for export] *)
Ltac kx_sx3_1 :=
  match goal with
  | KXA : atoms_ok ?zs ?E |- context [bv_unsigned (edenot ?E ?e)] =>
      kx_sx3_has e;
      let nz := kx_len zs in
      let z := kx_ez3 E zs nz e in
      let P := kx_sxc3 E zs nz e in
      let H := fresh "KXSX" in
      assert (H : bv_unsigned (edenot E e) = z);
      [ refine (ez3_sound_u zs E e KXA (_ : P) (_ : 0 <= z < 2^64)); [ repeat split; Lia.lia | Lia.lia ]
      | rewrite !H in *; clear H ]
  | KXA : atoms_ok ?zs ?E, HH : context [bv_unsigned (edenot ?E ?e)] |- _ =>
      kx_sx3_has e;
      let nz := kx_len zs in
      let z := kx_ez3 E zs nz e in
      let P := kx_sxc3 E zs nz e in
      let H := fresh "KXSX" in
      assert (H : bv_unsigned (edenot E e) = z);
      [ refine (ez3_sound_u zs E e KXA (_ : P) (_ : 0 <= z < 2^64)); [ repeat split; Lia.lia | Lia.lia ]
      | rewrite !H in *; clear H ]
  | KXA : atoms_ok ?zs ?E |- context [edenot ?E ?e] =>
      kx_sx3_has e;
      let nz := kx_len zs in
      let z := kx_ez3 E zs nz e in
      let P := kx_sxc3 E zs nz e in
      let H := fresh "KXSX" in
      assert (H : edenot E e = Z_to_bv 64 z);
      [ refine (ez3_sound zs E e KXA (_ : P)); repeat split; Lia.lia
      | rewrite !H in *; clear H ]
  | KXA : atoms_ok ?zs ?E, HH : context [edenot ?E ?e] |- _ =>
      kx_sx3_has e;
      let nz := kx_len zs in
      let z := kx_ez3 E zs nz e in
      let P := kx_sxc3 E zs nz e in
      let H := fresh "KXSX" in
      assert (H : edenot E e = Z_to_bv 64 z);
      [ refine (ez3_sound zs E e KXA (_ : P)); repeat split; Lia.lia
      | rewrite !H in *; clear H ]
  end.
Ltac kx_sx3 := kx_read_ranges; repeat kx_sx3_1.
