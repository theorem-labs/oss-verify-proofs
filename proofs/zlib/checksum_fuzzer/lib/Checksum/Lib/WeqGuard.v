(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From Stdlib Require Import Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Mem ZBridge.

Ltac2 rec wg_is_pos (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args => if Bool.or (Constr.equal h 'xI) (Constr.equal h 'xO) then wg_is_pos (Array.get args 0) else false
  | _ => Constr.equal t 'xH
  end.
Ltac2 wg_is_lit (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args => if Bool.or (Constr.equal h 'Zpos) (Constr.equal h 'Zneg) then wg_is_pos (Array.get args 0) else false
  | _ => Constr.equal t 'Z0
  end.
Ltac2 wg_mem (t : constr) (l : constr list) : bool := List.exist (fun u => Constr.equal t u) l.
Ltac2 rec wg_atoms (t : constr) (acc : constr list) : constr list :=
  if wg_is_lit t then acc else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Bool.or (Constr.equal h '@Z.add) (Constr.equal h '@Z.sub) then wg_atoms (Array.get args 1) (wg_atoms (Array.get args 0) acc)
      else if Constr.equal h '@Z.opp then wg_atoms (Array.get args 0) acc
      else if Constr.equal h '@Z.mul then
        (if wg_is_lit (Array.get args 0) then wg_atoms (Array.get args 1) acc
         else if wg_is_lit (Array.get args 1) then wg_atoms (Array.get args 0) acc
         else if wg_mem t acc then acc else t :: acc)
      else if wg_mem t acc then acc else t :: acc
  | _ => if wg_mem t acc then acc else t :: acc
  end.
(* [comment removed for export] *)
Ltac2 wg_expr (w : constr) : constr option :=
  lazy_match! w with
  | Z_to_bv _ ?e => Some e
  | wa ?e => Some e
  | _ => None
  end.
Ltac2 wg_guard () : unit :=
  lazy_match! goal with
  | [ |- @eq _ ?x ?y ] =>
      match wg_expr x with
      | Some e1 =>
          match wg_expr y with
          | Some e2 =>
              let a1 := wg_atoms e1 [] in let a2 := wg_atoms e2 [] in
              if Bool.and (List.for_all (fun u => wg_mem u a2) a1) (List.for_all (fun u => wg_mem u a1) a2) then ()
              else Control.zero (Tactic_failure (Some (Message.of_string "WeqGuard: the two addresses have different atoms")))
          | None => ()
          end
      | None => ()
      end
  | [ |- _ ] => ()
  end.
Ltac weq_guard := ltac2:(Control.enter wg_guard).

(* [comment removed for export] *)
Ltac word_eq_guarded :=
  first [ exact eq_refl
        | weq_guard; first [ f_equal; lia
                           | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
                           | apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ] ].
