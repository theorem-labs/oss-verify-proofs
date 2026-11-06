(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutOpsD CutAutoD.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FAS.
Definition P48 : Z := 281474976710656.
Definition MAXU : Z := 18446744073709551615.
Definition KMAX : Z := 70000.
Definition NZ (a b : expr) : kentry := KRange (EAlu ALU_SLTU (ELit 0) (EAlu ALU_OR a b)) 1 1.
Definition vs (l : list expr) : list nat := nodup Nat.eq_dec (flat_map CAD.expr_vars l).

Definition rel (kn : list kentry) (v : list nat) : list kentry :=
  List.filter (fun K => match K with KRange e _ _ => forallb (fun x => existsb (Nat.eqb x) v) (CAD.expr_vars e) | _ => false end) kn.
Definition hask (kn : list kentry) (K : kentry) : bool := existsb (APC.kentry_eqb K) kn.
Definition r (regs : list expr) (n : nat) : expr := nth n regs (ELit 0).
Definition m1 (v : nat) : expr := EAlu ALU_ADD (EVar v) (ELit (-1)).

Definition inv_t (XL T : nat) : kentry := KRange (EAlu ALU_SRL (EVar XL) (APC.esub (ELit 64) (EVar T))) 1 MAXU.
Definition inv_b (XL T : nat) (xl t : expr) : kentry := CC.ksubstL 32 [(XL, xl); (T, t)] (inv_t XL T).

Definition a_nz : list expr -> list kentry -> list (list kentry * kentry) := fun regs kn =>
  let a0 := r regs 10 in let a1 := r regs 11 in let s3 := r regs 19 in
  [(rel kn (vs [a0]), KRange a0 P48 (2 * P48 - 1)); (rel kn (vs [a0; a1; s3; r regs 18]), NZ a1 s3)].

Definition a_j1 (S7 S8 : nat) : list expr -> list kentry -> list (list kentry * kentry) := fun regs kn =>
  let e7 := r regs 23 in let e8 := r regs 24 in
  [(rel kn (vs [e7]), CC.ksubstL 32 [(S7, e7)] (KRange (EAlu ALU_ADD (EVar S7) (ELit 120)) 0 65535));
   (rel kn (vs [e8]), CC.ksubstL 32 [(S8, e8)] (KRange (EAlu ALU_ADD (EVar S8) (ELit 120)) 0 65535))].

Definition a_f1 (K : nat) : list expr -> list kentry -> list (list kentry * kentry) := fun regs kn =>
  let e7 := r regs 23 in let e8 := r regs 24 in
  let pk := rel kn (vs [e7; e8]) in

  (if hask kn (KRange (EAlu ALU_SLT e8 e7) 1 1) then
     if hask kn (KRange (EVar K) 1 KMAX) then [(pk, KRange (m1 K) 1 KMAX)]
     else [(pk, KRange (APC.esub e7 e8) 1 KMAX); (pk, KRange (EAlu ALU_ADD (APC.esub e8 e7) (ELit (KMAX + 1))) 1 KMAX)]
   else []) ++ a_nz regs kn.

Definition a_ent : list expr -> list kentry -> list (list kentry * kentry) := fun regs kn =>
  let a0 := r regs 10 in let s3 := r regs 19 in [(rel kn (vs [a0; s3]), NZ a0 s3); ([], KRange a0 0 MAXU)].

Definition a_f2 (XL T : nat) : list expr -> list kentry -> list (list kentry * kentry) := fun regs kn =>
  let a0 := r regs 10 in let s3 := r regs 19 in
  let pa := rel kn (vs [a0; s3]) in
  let pb := rel kn (T :: vs [a0; s3]) in

  let from_b := (hask kn (KRange (EVar T) 1 64) && match s3 with EMd M_MUL (ELit 2) (EVar _) => true | _ => false end)%bool in
  match erange kn a0 with
  | Some (l, hh) =>
      if Z.eqb hh 0 then [(pa, KRange s3 1 MAXU)] ++ (if from_b then [(pb, KRange (m1 T) 1 64); (pb, inv_b XL T s3 (m1 T))] else [(pa, inv_b XL T s3 (ELit 64))])
      else if Z.leb 1 l then [(pa, KRange a0 1 (P48 - 1))]
      else []
  | None => []
  end
  ++ match a0 with
     | EAlu ALU_OR (EMd M_MUL (ELit 2) (EVar h)) (EAlu ALU_SRL _ (ELit 63)) => [(pa, KRange a0 1 (P48 - 1)); (pa, KRange (APC.esub a0 (EVar h)) 1 P48)]
     | _ => []
     end.
End FAS.
