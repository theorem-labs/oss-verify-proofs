(* SPDX-License-Identifier: MIT *)
(* LPS c0dd863a: the end state of a transfer FX hole ([BrTrans.tr_check]) read back from the hole's own run.
   The recorded end state [ER0] (renumbered) gives the hole's end registers and facts in the numbering of
   the recorded start state [CSr]; the hole now starts from a state [CS] computed in the build, whose
   registers can name other variables and which can have more of them.  [rb_end] first moves the variables
   the hole made fresh ([CSr]'s next variable and up) above [CS]'s next variable, so that none of them
   names a variable of [CS]; then it keeps each recorded register whose expression the run's end value
   matches ([val_match]) and puts in each other one a fresh variable, which [gen_vt] binds to the run's
   value; it keeps each recorded fact the run's end state gives ([tr_entry_chk]), and in the place of each
   other one it puts the start state's fact on the same place ([PlanRegen.same_key]) when the run's end
   state gives that, else, for a word, the same place known readable only ([rb_unk]) when the run's end state
   gives that, else a pure fact of the start state, so that the facts keep their places.  Nothing here is
   trusted: the hole's [tr_check] runs on the state this gives. *)
From Stdlib Require Import ZArith NArith List Bool Uint63.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxImage FxHandoff.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require PlanRegen.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cx Require Import CxPlan.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrRev BrClass BrRevS BrDress BrTrans BrGen BrRa.
Import ListNotations.
Open Scope Z_scope.

Section Readback.
Variable IM : fimage.
Variable A : CAP.atable.
Variable TT : ttab_e.
Variable CS : CAP.acs.     (* the hole's start state, computed *)
Variable d : sdesc.        (* its FX descriptor *)
Variable F' : fstate.      (* the FX run's end *)
Variable ER0 : CAP.acs.    (* the recorded end state, renumbered *)
Variable CSr : CAP.acs.    (* the recorded start state, renumbered *)

(* the hole's own fresh variables, moved above the computed start state's *)
Definition rb_ER : CAP.acs :=
  PlanRegen.ash (PlanRegen.vshift (CAP.nxt CSr) (Nat.max (CAP.nxt CS) (CAP.nxt CSr) - CAP.nxt CSr)) ER0.

(* fresh variables start above every variable of the start state and of the moved end state *)
Definition rb_nx : nat := Nat.max (CAP.nxt CS) (CAP.nxt rb_ER).

Definition rb_regs : list AX2.expr :=
  let regs := AX2.s_regs (CAP.a_ss rb_ER) in
  let vt0 := gen_vt (CAP.nxt CS) regs F' in
  map (fun i => let e := nth i regs (AX2.ELit 0) in
                if Nat.eqb i 0 then e
                else if val_match vt0 [] (xt_of TT) [] e (FxState.rget F' (of_Z (Z.of_nat i))) then e
                else AX2.EVar (rb_nx + i)) (seq 0 (List.length regs)).

Definition rb_fill : AX2.kentry :=
  match List.find is_pure (CAP.kn CS) with Some K => K | None => AX2.KRange (AX2.ELit 0) 0 0 end.

(* a recorded word whose value names a variable of the recorded start: its place, readable, value unknown *)
Definition rb_unk (K : AX2.kentry) : option AX2.kentry :=
  match K with AX2.KWord a w _ => Some (AX2.KUnk a (AX2.ELit (Z.of_nat w))) | _ => None end.

Definition rb_kn : list AX2.kentry :=
  let XTv := xt_of TT in
  let M0v := f_mem (state_of d) in
  let chk := tr_entry_chk IM A TT (CAP.kn CS) d (f_mem F') (gen_vt (CAP.nxt CS) rb_regs F') (ra_fast (CAP.kn CS))
                          (CAP.kset_mem (CAP.kset_of (CAP.kn CS))) XTv M0v
                          (root_cov (CAP.kn CS) M0v XTv) (root_ovcov (CAP.kn CS) M0v XTv) in
  map (fun K => if chk K then K
                else match List.find (fun K0 => PlanRegen.same_key K K0 && chk K0) (CAP.kn CS) with
                     | Some K0 => K0     (* the start state's fact on the same place, which the run kept *)
                     | None => match rb_unk K with
                               | Some K1 => if chk K1 then K1 else rb_fill
                               | None => rb_fill
                               end
                     end) (CAP.kn rb_ER).

Definition rb_end : CAP.acs := tr_state CS (to_Z (f_pc F')) rb_regs rb_kn (rb_nx + 32).
End Readback.
