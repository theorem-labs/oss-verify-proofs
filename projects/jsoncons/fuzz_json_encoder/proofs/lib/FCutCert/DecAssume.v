(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutAutoD.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DAS.
Definition lemc : Type := list expr -> list kentry -> list (list kentry * kentry).
Definition rg (regs : list expr) (r : nat) : expr := nth r regs (ELit 0).
(* [comment removed for export] *)
Definition probe0 (e : expr) : expr := EAlu ALU_SLTU (EAlu ALU_SUB e (ELit 0)) (ELit 1).
Fixpoint find_fact (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' l h :: r => if expr_eqb e e' then Some (l, h) else find_fact r e
  | _ :: r => find_fact r e
  end.
Definition lo_of (kn : list kentry) (e : expr) : Z := match erange kn e with Some (l, _) => l | None => 0 end.
Definition all_lo1 (l : list kentry) : bool :=
  (negb (Nat.eqb (length l) 0) && forallb (fun K => match K with KRange _ lo _ => Z.leb 1 lo | _ => false end) l)%bool.
Definition U64 : Z := 18446744073709551615.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_l5_t3 : lemc := fun regs kn =>
  if (expr_eqb (rg regs 13) (rg regs 19) && Z.leb 1 (lo_of kn (rg regs 14)))%bool
  then [(CAD.vranges kn (rg regs 28), KRange (rg regs 28) 1 2147483647)] else [].
(* [comment removed for export] *)
Definition A_l5_or : lemc := fun regs kn =>
  match rg regs 14 with
  | EAlu ALU_OR (EAlu ALU_XOR k (ELit a)) _ =>
      match find_fact kn k with
      | Some (l, h) => if (Z.leb 0 a && Z.ltb a l)%bool then [([KRange k l h], KRange (rg regs 14) 1 U64)] else []
      | None => []
      end
  | _ => []
  end.
(* [comment removed for export] *)
Definition A_l5_join : lemc := fun regs kn =>
  let e := rg regs 14 in
  if CX.has_k kn (KRange (probe0 e) 1 1) then [([KRange (probe0 e) 1 1], KRange e 0 0)]
  else if CX.has_k kn (KRange (probe0 e) 0 0) then [(KRange (probe0 e) 0 0 :: CAD.vranges kn e, KRange e 1 2147483647)] else [].
(* [comment removed for export] *)
Definition A_l5_cy : lemc := fun regs kn =>
  match rg regs 17 with
  | ELit c7 =>
      let e := rg regs 14 in
      (CAD.vranges kn e, KRange e 0 (1000000000 - c7)) ::
      match rg regs 28, e with
      | EAluw ALU_ADD (EMdw M_DIVU x _) (ELit 0), EMdw M_MUL (EAluw ALU_SUB x' _) _ =>
          if (expr_eqb x x' && all_lo1 (CAD.vranges kn x) && CX.has_k kn (KRange (rg regs 28) 0 0))%bool
          then [(KRange (rg regs 28) 0 0 :: CAD.vranges kn x, KRange e c7 (1000000000 - c7))] else []
      | _, _ => []
      end
  | _ => []
  end.
(* [comment removed for export] *)
Definition A_l5_rp (wv : nat) : lemc := fun regs kn =>
  match rg regs 23, rg regs 19 with
  | EAlu ALU_ADD (EAluw ALU_SUB _ (ELit _)) (ELit 9), ELit a =>
      let e := APC.esub (rg regs 23) (APC.eaddz (APC.escale 9 (EVar wv)) (-1305 - 9 * a)) in [(CAD.vranges kn e, KRange e 0 0)]
  | _, _ => []
  end.
(* [comment removed for export] *)
Definition sra4_of (e : expr) : option expr :=
  match e with EAlu ALU_SRA (EMd M_MUL (ELit 4294967296) z) (ELit 30) => Some (APC.escale 4 z) | _ => None end.
Definition A_sra4 (r : nat) : lemc := fun regs kn =>
  match sra4_of (rg regs r) with Some e4 => let e := APC.esub (rg regs r) e4 in [(CAD.vranges kn e, KRange e 0 0)] | None => [] end.
Definition R_sra4 (r : nat) : list expr -> list kentry -> list (nat * expr) := fun regs _ =>
  match sra4_of (rg regs r) with Some e4 => [(r, e4)] | None => [] end.
(* [comment removed for export] *)
Definition when_r1300 (f : lemc) : lemc := fun regs kn =>
  match rg regs 23 with EAlu ALU_ADD (EVar _) (ELit z) => if Z.eqb z (-1300) then f regs kn else [] | _ => [] end.
(* [comment removed for export] *)
Definition sgn64 (c : Z) : Z := let c' := c mod 18446744073709551616 in if Z.ltb c' 9223372036854775808 then c' else c' - 18446744073709551616.
Definition mask_lin (kn : list kentry) (e : expr) : option expr :=
  match e with
  | EAlu ALU_AND (EAlu ALU_ADD v (ELit c0)) (ELit 2047) =>
      let c := sgn64 c0 in
      match erange kn v with
      | Some (l, h) => if (Z.eqb ((l + c) / 2048) ((h + c) / 2048) && Z.leb (h - l) 4096)%bool then Some (APC.eaddz v (c - 2048 * ((l + c) / 2048))) else None
      | None => None
      end
  | _ => None
  end.
Definition A_mask (r : nat) : lemc := fun regs kn =>
  match mask_lin kn (rg regs r) with Some e' => let e := APC.esub (rg regs r) e' in [(CAD.vranges kn e, KRange e 0 0)] | None => [] end.
Definition R_mask (r : nat) : list expr -> list kentry -> list (nat * expr) := fun regs kn =>
  match mask_lin kn (rg regs r) with Some e' => [(r, e')] | None => [] end.
(* [comment removed for export] *)
Definition probe_eq (x y : expr) : expr := EAlu ALU_SLTU (EAlu ALU_SUB x y) (ELit 1).
Definition A_probe_eq (r1 r2 : nat) : lemc := fun regs kn =>
  let x := rg regs r1 in let y := rg regs r2 in
  if CX.has_k kn (KRange (probe_eq x y) 1 1) then [([KRange (probe_eq x y) 1 1], KRange (APC.esub x y) 0 0)] else [].
(* [comment removed for export] *)
Definition A_var (v : nat) (lo hi : Z) : lemc := fun regs kn =>
  match erange kn (EVar v) with      (* [comment removed for export] *)
  | Some (l, h) => [(CAD.prems kn (EVar v), KRange (EVar v) (Z.max lo l) (Z.min hi h))]
  | None => [(CAD.prems kn (EVar v), KRange (EVar v) lo hi)]
  end.
(* [comment removed for export] *)
Definition zx4 (e : expr) : expr := EExt false 0 4 e.
(* [comment removed for export] *)
Definition A_sext_ge (r : nat) (c : Z) : lemc := fun regs kn =>
  match rg regs r with
  | EExt true O 4 x => let p := EAlu ALU_SLTU (EExt true 0 4 x) (ELit c) in
                       if CX.has_k kn (KRange p 0 0) then [([KRange p 0 0], KRange (zx4 x) c 4294967295)] else []
  | _ => []
  end.
(* [comment removed for export] *)
Definition A_ds_t6 : lemc := fun regs kn =>
  if negb (expr_eqb (rg regs 28) (rg regs 19)) then [] else
  match rg regs 31, rg regs 5 with
  | EAluw ALU_ADD (EAluw ALU_SRL (EExt true O 4 xa) (ELit sh)) (ELit 0), ELit sh' =>
      match find_fact kn (zx4 xa) with
      | Some (l, h) =>
          (if Z.leb 1 l then [([KRange (zx4 xa) l h], KRange (APC.esub (zx4 xa) (zx4 (rg regs 31))) 1 4294967295)] else [])
          ++ (if Z.leb (2 ^ sh) l then [([KRange (zx4 xa) l h], KRange (rg regs 31) 1 2147483647)] else [])
      | None => []
      end
  | EAluw ALU_ADD (EAluw ALU_SRL _ (ELit sh)) cy, _ =>
      match erange kn cy with
      | Some (l, h) => if (Z.leb 1 l && Z.leb h 999999999)%bool
                       then [([KRange cy l h], KRange (rg regs 31) 1 U64); ([KRange cy l h], KRange (zx4 (rg regs 31)) 1 4294967295)] else []
      | None => []
      end
  | _, _ => []
  end.
(* [comment removed for export] *)
Definition A_ds_or : lemc := fun regs kn =>
  match rg regs 6 with
  | EAlu ALU_OR (EAlu ALU_XOR k a) _ =>
      match find_fact kn (APC.esub k a), find_fact kn (APC.esub a k) with
      | Some (l, h), _ => if Z.leb 1 l then [([KRange (APC.esub k a) l h], KRange (rg regs 6) 1 U64)] else []
      | None, Some (l, h) => if Z.leb 1 l then [([KRange (APC.esub a k) l h], KRange (rg regs 6) 1 U64)] else []
      | None, None => []
      end
  | _ => []
  end.
(* [comment removed for export] *)
Definition A_ds_join : lemc := fun regs kn =>
  let e := rg regs 6 in
  if CX.has_k kn (KRange (probe0 e) 1 1) then [([KRange (probe0 e) 1 1], KRange e 0 0)]
  else if CX.has_k kn (KRange (probe0 e) 0 0)
       then ([KRange (probe0 e) 0 0], KRange e 1 U64) ::
            match e with EAluw _ _ _ => [([KRange (probe0 e) 0 0], KRange (zx4 e) 1 4294967295)] | _ => [] end      (* [comment removed for export] *)
       else [].
(* [comment removed for export] *)
Definition A_ds_cy : lemc := fun regs kn =>
  match rg regs 6, rg regs 31 with
  | EMdw M_MUL (EAlu ALU_AND x (ELit m)) (ELit c), t6 =>
      ([], KRange (rg regs 6) 0 (m * c)) ::
      match x, t6 with
      | EExt true O 4 xa, EAluw ALU_ADD (EAluw ALU_SRL (EExt true O 4 xa') (ELit sh)) (ELit 0) =>
          match find_fact kn (zx4 xa) with
          | Some (l, h) => if (expr_eqb xa xa' && Z.leb 1 l && CX.has_k kn (KRange t6 0 0))%bool
                           then [([KRange t6 0 0; KRange (zx4 xa) l h], KRange (rg regs 6) c (m * c))] else []
          | None => []
          end
      | _, _ => []
      end
  | _, _ => []
  end.
(* [comment removed for export] *)
Definition A_rp_ne36 (wv : nat) : lemc := fun regs kn =>
  let p := probe_eq (rg regs 23) (ELit 36) in
  if CX.has_k kn (KRange p 0 0) then [(CAD.vranges kn (EVar wv) ++ [KRange p 0 0], KRange (EVar wv) 150 400)] else [].
(* [comment removed for export] *)
Definition R_s3_z : list expr -> list kentry -> list (nat * expr) := fun regs _ =>
  if expr_eqb (rg regs 19) (rg regs 28) then [(19%nat, rg regs 18)] else [].
Definition both (a b : lemc) : lemc := fun regs kn => a regs kn ++ b regs kn.

(* [comment removed for export] *)
Definition nd_of (c : expr) : expr := mkAlu ALU_SLTU (mkAlu ALU_ADD c (ELit (-48))) (ELit 10).
Definition np_of (c : expr) : expr := mkAlu ALU_SLTU (mkAlu ALU_SUB c (ELit 46)) (ELit 1).
Definition ne_of (c : expr) : expr := mkAlu ALU_SLTU (mkAlu ALU_SUB (mkAlu ALU_AND c (ELit (-33))) (ELit 69)) (ELit 1).
Definition nmin_of (e : expr) : expr := EAlu ALU_SLTU (EAlu ALU_SUB e (ELit 9223372036854775808)) (ELit 1).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_cls (fs : list (expr -> expr)) : lemc := fun regs kn =>
  match rg regs 10 with
  | ELit _ => []
  | c => map (fun f : expr -> expr => (CAD.prems kn c, KRange (f c) 0 0)) fs
  end.

(* [comment removed for export] *)
Definition ret_scx (F2 : list (expr * Z * expr)) (lmin : bool) (src : CC.cutpoint) (BL : CAD.blocks) (nxsrc : nat) (ps : SR.post_spec) : option (CC.cutpoint * CAD.blocks) :=
  let regs := CAD.ps_reglist ps in
  let nx := Nat.max nxsrc (CAD.ps_bound ps) in
  match nth 1 regs (ELit 1) with
  | ELit ra =>
      let regs1 := APC.sr_fresh regs APC.caller_saved nx in
      let a0v := nth 10 regs1 (ELit 0) in
      let regs2 := if lmin then sr_upd regs1 10 (ELit 9223372036854775808) else regs1 in
      let '(spb, spo) := split_lit (nth 2 regs (ELit 0)) in
      let '(fb, fo) := split_lit (nth 10 regs (ELit 0)) in
      let kn1 := APC.kn_havoc (APC.kn_havoc (SR.ps_cells ps) fb (fo + 8) (ELit 8)) spb (spo - 80) (ELit 80) in
      let kn := KWord (SA fb (fo + 8)) 8 (EVar (nx + APC.NCS)) :: KUnk (SA spb (spo - 80)) (ELit 80) :: kn1 in
      Some (CC.CP ra regs2 (if lmin then kn else KRange (nmin_of a0v) 0 0 :: kn) (nx + APC.NCS + 1) (if lmin then CC.cp_F src else F2) [] (APC.esub (CC.cp_meas src) (ELit 1)), BL)
  | _ => None
  end.
End DAS.
