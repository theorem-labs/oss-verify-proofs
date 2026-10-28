(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxImage FxHandoff FxHoBuild
  FxSys FxDrive FxDrive3 FxDrive3N FxDrive3S FxDrive3C FxDrive3D FxDrive3H FxDrive3T FxDrive3O.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CxPlan HBPlanImage HBAtable.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrRev BrClass BrRevS BrDress BrTrans BrGen Br3Aux.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require Import BFIPcs BFI8DataK1B3 BFI8EndK1B3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition page_var (e : AX2.expr) : list nat :=
  match e with AX2.EMd Instr.M_MUL (AX2.ELit 4096) (AX2.EVar v) => [v] | _ => [] end.
Definition pair_vars (tags : list int) (es : list AX2.expr) : list (int * nat) :=
  flat_map (fun p => map (fun v => (fst p, v)) (page_var (snd p))) (combine tags es).

(* [comment removed for export] *)
Definition aux (F' : fstate) (L' : fledger3) (n' : int) : LeafAux :=
  let nfresh := (List.length (fl_all L') - List.length (fl_all L3))%nat in
  let live := pair_vars (map fent_tag (firstn nfresh (fl_all L'))) (map CAP.am_base (firstn nfresh (CAP.a_maps END))) in
  let cuts := rev (flat_map (fun o : vop => match fst o with OpCut => [fent_tag (snd o)] | _ => [] end) (fl_ops L')) in
  let nghost := (List.length (CAP.a_ghost END) - List.length (CAP.a_ghost START))%nat in
  let dead := pair_vars cuts (map fst (firstn nghost (CAP.a_ghost END))) in
  let xtn := live ++ dead in
  LA (map (fun p : int * nat => (snd p, VDiv (fst p) 0 4096 0)) xtn ++ gen_vt (CAP.nxt START) (AX2.s_regs (CAP.a_ss END)) F')
     [] xtn
     (flat_map (fun o : vop => match fst o with OpShadow => [(fent_tag (snd o), (fent_tag (snd o) - 1)%uint63)] | _ => [] end) (fl_ops L')).
