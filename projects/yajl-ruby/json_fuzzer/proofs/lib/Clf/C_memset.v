(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import STRW_memset.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Clf Require Import CImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition memset_entry := 0x11f64%Z.

(* [comment removed for export] *)
Ltac brute256 c Rc :=
  first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
  repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
  revert c Rc; apply brute256_ok; vm_compute; reflexivity.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
  intros x Hx H4.
  transitivity (Z.land (x mod 8) 4).
  { change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
    rewrite <- Z.land_assoc. reflexivity. }
  assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
  destruct R as [R|R]; rewrite R; reflexivity.
Qed.
