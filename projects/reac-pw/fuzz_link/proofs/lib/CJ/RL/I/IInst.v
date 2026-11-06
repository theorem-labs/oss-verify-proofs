(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import Tac.
Import ListNotations.
Open Scope Z_scope.

Fixpoint zlookup (k : Z) (t : list (Z * Z)) : option Z :=
  match t with [] => None | (a, v) :: t' => if Z.eqb k a then Some v else zlookup k t' end.
Fixpoint ivlookup (k : Z) (t : list (Z * Z * Z)) : option Z :=
  match t with [] => None | (lo, hi, d) :: t' => if (lo <=? k) && (k <? hi) then Some (k + d) else ivlookup k t' end.
Definition tsym (ex : list (Z * Z)) (iv : list (Z * Z * Z)) (k : Z) : Z :=
  match zlookup k ex with Some v => v | None => match ivlookup k iv with Some v => v | None => k end end.

(* [comment removed for export] *)
Ltac sym_lits := repeat match goal with |- context [@sym ?I ?k] => let v := eval vm_compute in (@sym I k) in change (@sym I k) with v end.
Ltac rel_ok := unfold rel_code, rel_sym, rel_near; sym_lits; lia.
Ltac inst := lazymatch goal with
  | |- code_at _ _ _ => apply code_checkb_ok; vm_compute; reflexivity
  | |- CodeAt _ _ _ => apply code_checkb_ok; vm_compute; reflexivity
  | |- CodeAtT _ _ _ => apply code_checkb_t_ok; vm_compute; reflexivity
  | |- ro_bytes_b _ _ _ = true => vm_compute; reflexivity
  | |- RoB _ _ _ => unfold RoB; vm_compute; reflexivity
  | |- rel_code _ _ => rel_ok | |- rel_sym _ => rel_ok | |- rel_near _ _ => rel_ok
  | |- RelCode _ _ => unfold RelCode; rel_ok | |- RelSym _ => unfold RelSym; rel_ok | |- RelNear _ _ => unfold RelNear; rel_ok
  | |- ZFact _ => unfold ZFact; sym_lits; lia
  | |- (_ <= _)%Z => sym_lits; lia
  | |- _ => solve [ typeclasses eauto ]       (* [comment removed for export] *)
  end.
