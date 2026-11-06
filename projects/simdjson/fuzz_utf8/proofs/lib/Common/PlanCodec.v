(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Corelib Require Import PrimInt63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Module PKC.

(* [comment removed for export] *)
Fixpoint enc_ugo (fuel : nat) (u : Z) (acc : list Z) : list Z :=
  match fuel with O => acc | S f => if Z.eqb u 0 then acc else enc_ugo f (u / 32) ((u mod 32 + 32) :: acc) end.
Definition enc_u (u : Z) (k : list Z) : list Z := enc_ugo 40%nat (u / 32) ((u mod 32) :: k).
Definition zig (z : Z) : Z := if Z.leb 0 z then 2 * z else (-2) * z - 1.
Definition unzig (u : Z) : Z := if Z.even u then u / 2 else - ((u + 1) / 2).
Definition enc_Z (z : Z) (k : list Z) : list Z := enc_u (zig z) k.
Definition enc_nat (n : nat) (k : list Z) : list Z := enc_u (Z.of_nat n) k.
Definition enc_bool (b : bool) (k : list Z) : list Z := (if b then 1 else 0) :: k.
Definition enc_list {T} (e : T -> list Z -> list Z) (l : list T) (k : list Z) : list Z :=
  enc_u (Z.of_nat (List.length l)) (fold_right e k l).
Definition enc_opt {T} (e : T -> list Z -> list Z) (o : option T) (k : list Z) : list Z :=
  match o with None => 0 :: k | Some x => 1 :: e x k end.
Definition enc_pair {T U} (e1 : T -> list Z -> list Z) (e2 : U -> list Z -> list Z) (p : T * U) (k : list Z) : list Z :=
  e1 (fst p) (e2 (snd p) k).

(* [comment removed for export] *)
Section Str.
Variable s : string.
Definition zbit (c m : int) (v : Z) : Z := if PrimInt63.eqb (PrimInt63.land c m) 0%int63 then 0 else v.
(* [comment removed for export] *)
Definition rd (i : int) : Z :=
  let c := PrimInt63.sub (PrimString.get s i) 63%int63 in
  zbit c 1%int63 1 + zbit c 2%int63 2 + zbit c 4%int63 4 + zbit c 8%int63 8 + zbit c 16%int63 16 + zbit c 32%int63 32.
Definition nx (i : int) : int := PrimInt63.add i 1%int63.
Fixpoint dec_ugo (fuel : nat) (i : int) (acc : Z) : option (Z * int) :=
  match fuel with O => None | S f =>
    let d := rd i in if Z.leb 32 d then dec_ugo f (nx i) (acc * 32 + (d - 32)) else Some (acc * 32 + d, nx i) end.
Definition dec_u (fuel : nat) (i : int) : option (Z * int) := dec_ugo 41%nat i 0.
Definition dec_Z (fuel : nat) (i : int) : option (Z * int) := match dec_u fuel i with Some (u, j) => Some (unzig u, j) | None => None end.
Definition dec_nat (fuel : nat) (i : int) : option (nat * int) := match dec_u fuel i with Some (u, j) => Some (Z.to_nat u, j) | None => None end.
Definition dec_bool (fuel : nat) (i : int) : option (bool * int) := let d := rd i in if Z.eqb d 0 then Some (false, nx i) else if Z.eqb d 1 then Some (true, nx i) else None.
Fixpoint dec_listn {T} (dx : int -> option (T * int)) (n : nat) (i : int) : option (list T * int) :=
  match n with
  | O => Some ([], i)
  | S m => match dx i with Some (x, j) => match dec_listn dx m j with Some (r, j') => Some (x :: r, j') | None => None end | None => None end
  end.
Definition dec_list {T} (dx : int -> option (T * int)) (fuel : nat) (i : int) : option (list T * int) :=
  match dec_u fuel i with Some (n, j) => if Z.ltb n 0 then None else dec_listn dx (Z.to_nat n) j | None => None end.
Definition dec_opt {T} (dx : int -> option (T * int)) (fuel : nat) (i : int) : option (option T * int) :=
  let d := rd i in if Z.eqb d 0 then Some (None, nx i) else if Z.eqb d 1 then match dx (nx i) with Some (x, j) => Some (Some x, j) | None => None end else None.
Definition dec_pair {T U} (d1 : int -> option (T * int)) (d2 : int -> option (U * int)) (i : int) : option ((T * U) * int) :=
  match d1 i with Some (x, j) => match d2 j with Some (y, j') => Some ((x, y), j') | None => None end | None => None end.

Definition enc_aluop (x : Instr.aluop) (k : list Z) : list Z := (match x with Instr.ALU_ADD => 0 | Instr.ALU_SUB => 1 | Instr.ALU_SLL => 2 | Instr.ALU_SLT => 3 | Instr.ALU_SLTU => 4 | Instr.ALU_XOR => 5 | Instr.ALU_SRL => 6 | Instr.ALU_SRA => 7 | Instr.ALU_OR => 8 | Instr.ALU_AND => 9 end) :: k.
Definition dec_aluop (fuel : nat) (i : int) : option (Instr.aluop * int) := let d := rd i in if Z.eqb d 0 then Some (Instr.ALU_ADD, nx i) else if Z.eqb d 1 then Some (Instr.ALU_SUB, nx i) else if Z.eqb d 2 then Some (Instr.ALU_SLL, nx i) else if Z.eqb d 3 then Some (Instr.ALU_SLT, nx i) else if Z.eqb d 4 then Some (Instr.ALU_SLTU, nx i) else if Z.eqb d 5 then Some (Instr.ALU_XOR, nx i) else if Z.eqb d 6 then Some (Instr.ALU_SRL, nx i) else if Z.eqb d 7 then Some (Instr.ALU_SRA, nx i) else if Z.eqb d 8 then Some (Instr.ALU_OR, nx i) else if Z.eqb d 9 then Some (Instr.ALU_AND, nx i) else None.
Definition enc_mulop (x : Instr.mulop) (k : list Z) : list Z := (match x with Instr.M_MUL => 0 | Instr.M_MULH => 1 | Instr.M_MULHSU => 2 | Instr.M_MULHU => 3 | Instr.M_DIV => 4 | Instr.M_DIVU => 5 | Instr.M_REM => 6 | Instr.M_REMU => 7 end) :: k.
Definition dec_mulop (fuel : nat) (i : int) : option (Instr.mulop * int) := let d := rd i in if Z.eqb d 0 then Some (Instr.M_MUL, nx i) else if Z.eqb d 1 then Some (Instr.M_MULH, nx i) else if Z.eqb d 2 then Some (Instr.M_MULHSU, nx i) else if Z.eqb d 3 then Some (Instr.M_MULHU, nx i) else if Z.eqb d 4 then Some (Instr.M_DIV, nx i) else if Z.eqb d 5 then Some (Instr.M_DIVU, nx i) else if Z.eqb d 6 then Some (Instr.M_REM, nx i) else if Z.eqb d 7 then Some (Instr.M_REMU, nx i) else None.
Definition enc_xnode (x : xnode) (k : list Z) : list Z := (match x with XIMemset => 0 | XIMemcpy => 1 | XMemset => 2 | XMemcpy => 3 | XMemIsZero => 4 | XEnvScan => 5 | XPnScan => 6 | XLayout => 7 | XIStrncpy => 8 | XPopFree => 9 | XSniff => 10 end) :: k.
Definition dec_xnode (fuel : nat) (i : int) : option (xnode * int) := let d := rd i in if Z.eqb d 0 then Some (XIMemset, nx i) else if Z.eqb d 1 then Some (XIMemcpy, nx i) else if Z.eqb d 2 then Some (XMemset, nx i) else if Z.eqb d 3 then Some (XMemcpy, nx i) else if Z.eqb d 4 then Some (XMemIsZero, nx i) else if Z.eqb d 5 then Some (XEnvScan, nx i) else if Z.eqb d 6 then Some (XPnScan, nx i) else if Z.eqb d 7 then Some (XLayout, nx i) else if Z.eqb d 8 then Some (XIStrncpy, nx i) else if Z.eqb d 9 then Some (XPopFree, nx i) else if Z.eqb d 10 then Some (XSniff, nx i) else None.
Definition enc_snode (x : snode) (k : list Z) : list Z := (match x with YMunmap => 0 | YBrk => 1 | YSetTid => 2 end) :: k.
Definition dec_snode (fuel : nat) (i : int) : option (snode * int) := let d := rd i in if Z.eqb d 0 then Some (YMunmap, nx i) else if Z.eqb d 1 then Some (YBrk, nx i) else if Z.eqb d 2 then Some (YSetTid, nx i) else None.
Definition enc_mkind (x : mkind) (k : list Z) : list Z := (match x with KRW => 0 | KRWLAZY => 1 | KNONE => 2 | KNONELAZY => 3 | KFOG => 4 | KHOLE => 5 end) :: k.
Definition dec_mkind (fuel : nat) (i : int) : option (mkind * int) := let d := rd i in if Z.eqb d 0 then Some (KRW, nx i) else if Z.eqb d 1 then Some (KRWLAZY, nx i) else if Z.eqb d 2 then Some (KNONE, nx i) else if Z.eqb d 3 then Some (KNONELAZY, nx i) else if Z.eqb d 4 then Some (KFOG, nx i) else if Z.eqb d 5 then Some (KHOLE, nx i) else None.
Fixpoint enc_expr (v : expr) (k : list Z) : list Z :=
  match v with
  | ELit x0 => 0 :: enc_Z x0 (k)
  | EVar x0 => 1 :: enc_nat x0 (k)
  | EAlu x0 x1 x2 => 2 :: enc_aluop x0 (enc_expr x1 (enc_expr x2 (k)))
  | EAluw x0 x1 x2 => 3 :: enc_aluop x0 (enc_expr x1 (enc_expr x2 (k)))
  | EMd x0 x1 x2 => 4 :: enc_mulop x0 (enc_expr x1 (enc_expr x2 (k)))
  | EMdw x0 x1 x2 => 5 :: enc_mulop x0 (enc_expr x1 (enc_expr x2 (k)))
  | EExt x0 x1 x2 x3 => 6 :: enc_bool x0 (enc_nat x1 (enc_nat x2 (enc_expr x3 (k))))
  | EBlob x0 x1 x2 x3 => 7 :: enc_bool x0 (enc_nat x1 (enc_Z x2 (enc_nat x3 (k))))
  end.
Fixpoint dec_expr (fuel : nat) (i : int) : option (expr * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in match (dec_Z f) j0 with Some (y0, j1) => Some (ELit y0, j1) | None => None end) else
  if Z.eqb d 1 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => Some (EVar y0, j1) | None => None end) else
  if Z.eqb d 2 then (let j0 := nx i in match (dec_aluop f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_expr f) j2 with Some (y2, j3) => Some (EAlu y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 3 then (let j0 := nx i in match (dec_aluop f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_expr f) j2 with Some (y2, j3) => Some (EAluw y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 4 then (let j0 := nx i in match (dec_mulop f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_expr f) j2 with Some (y2, j3) => Some (EMd y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 5 then (let j0 := nx i in match (dec_mulop f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_expr f) j2 with Some (y2, j3) => Some (EMdw y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 6 then (let j0 := nx i in match (dec_bool f) j0 with Some (y0, j1) => match (dec_nat f) j1 with Some (y1, j2) => match (dec_nat f) j2 with Some (y2, j3) => match (dec_expr f) j3 with Some (y3, j4) => Some (EExt y0 y1 y2 y3, j4) | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 7 then (let j0 := nx i in match (dec_bool f) j0 with Some (y0, j1) => match (dec_nat f) j1 with Some (y1, j2) => match (dec_Z f) j2 with Some (y2, j3) => match (dec_nat f) j3 with Some (y3, j4) => Some (EBlob y0 y1 y2 y3, j4) | None => None end | None => None end | None => None end | None => None end) else None end.
Definition enc_saddr (v : saddr) (k : list Z) : list Z :=
  match v with
  | SA x0 x1 => 0 :: enc_expr x0 (enc_Z x1 (k))
  end.
Fixpoint dec_saddr (fuel : nat) (i : int) : option (saddr * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => Some (SA y0 y1, j2) | None => None end | None => None end) else None end.
Definition enc_kentry (v : kentry) (k : list Z) : list Z :=
  match v with
  | KWord x0 x1 x2 => 0 :: enc_saddr x0 (enc_nat x1 (enc_expr x2 (k)))
  | KZero x0 x1 => 1 :: enc_saddr x0 (enc_expr x1 (k))
  | KBlob x0 x1 x2 => 2 :: enc_saddr x0 (enc_expr x1 (enc_nat x2 (k)))
  | KImg x0 x1 => 3 :: enc_Z x0 (enc_Z x1 (k))
  | KAlign x0 x1 => 4 :: enc_expr x0 (enc_Z x1 (k))
  | KRange x0 x1 x2 => 5 :: enc_expr x0 (enc_Z x1 (enc_Z x2 (k)))
  | KWr x0 x1 => 6 :: enc_saddr x0 (enc_expr x1 (k))
  | KDisj x0 x1 x2 x3 => 7 :: enc_saddr x0 (enc_expr x1 (enc_saddr x2 (enc_expr x3 (k))))
  | KFill x0 x1 x2 => 8 :: enc_saddr x0 (enc_expr x1 (enc_Z x2 (k)))
  | KUnk x0 x1 => 9 :: enc_saddr x0 (enc_expr x1 (k))
  end.
Fixpoint dec_kentry (fuel : nat) (i : int) : option (kentry * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in match (dec_saddr f) j0 with Some (y0, j1) => match (dec_nat f) j1 with Some (y1, j2) => match (dec_expr f) j2 with Some (y2, j3) => Some (KWord y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 1 then (let j0 := nx i in match (dec_saddr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => Some (KZero y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 2 then (let j0 := nx i in match (dec_saddr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_nat f) j2 with Some (y2, j3) => Some (KBlob y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 3 then (let j0 := nx i in match (dec_Z f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => Some (KImg y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 4 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => Some (KAlign y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 5 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => match (dec_Z f) j2 with Some (y2, j3) => Some (KRange y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 6 then (let j0 := nx i in match (dec_saddr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => Some (KWr y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 7 then (let j0 := nx i in match (dec_saddr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_saddr f) j2 with Some (y2, j3) => match (dec_expr f) j3 with Some (y3, j4) => Some (KDisj y0 y1 y2 y3, j4) | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 8 then (let j0 := nx i in match (dec_saddr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_Z f) j2 with Some (y2, j3) => Some (KFill y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 9 then (let j0 := nx i in match (dec_saddr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => Some (KUnk y0 y1, j2) | None => None end | None => None end) else None end.
Definition enc_sentry (v : sentry) (k : list Z) : list Z :=
  match v with
  | SE x0 x1 x2 => 0 :: enc_saddr x0 (enc_nat x1 (enc_expr x2 (k)))
  end.
Fixpoint dec_sentry (fuel : nat) (i : int) : option (sentry * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in match (dec_saddr f) j0 with Some (y0, j1) => match (dec_nat f) j1 with Some (y1, j2) => match (dec_expr f) j2 with Some (y2, j3) => Some (SE y0 y1 y2, j3) | None => None end | None => None end | None => None end) else None end.
Definition enc_sym_state (v : sym_state) (k : list Z) : list Z :=
  match v with
  | SSR x0 x1 x2 x3 x4 x5 => 0 :: enc_Z x0 (enc_list (fun x k0 => enc_expr x (k0)) x1 (enc_list (fun x k0 => enc_sentry x (k0)) x2 (enc_list (fun x k0 => enc_kentry x (k0)) x3 (enc_nat x4 (enc_opt (fun x k0 => enc_saddr x (k0)) x5 (k))))))
  end.
Fixpoint dec_sym_state (fuel : nat) (i : int) : option (sym_state * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in match (dec_Z f) j0 with Some (y0, j1) => match (dec_list (dec_expr f) f) j1 with Some (y1, j2) => match (dec_list (dec_sentry f) f) j2 with Some (y2, j3) => match (dec_list (dec_kentry f) f) j3 with Some (y3, j4) => match (dec_nat f) j4 with Some (y4, j5) => match (dec_opt (dec_saddr f) f) j5 with Some (y5, j6) => Some (SSR y0 y1 y2 y3 y4 y5, j6) | None => None end | None => None end | None => None end | None => None end | None => None end | None => None end) else None end.
Definition enc_amap (v : amap) (k : list Z) : list Z :=
  match v with
  | AM x0 x1 x2 => 0 :: enc_expr x0 (enc_expr x1 (enc_mkind x2 (k)))
  end.
Fixpoint dec_amap (fuel : nat) (i : int) : option (amap * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_mkind f) j2 with Some (y2, j3) => Some (AM y0 y1 y2, j3) | None => None end | None => None end | None => None end) else None end.
Definition enc_afd (v : afd) (k : list Z) : list Z :=
  match v with
  | FdStd  => 0 :: k
  | FdFile x0 x1 x2 => 1 :: enc_nat x0 (enc_expr x1 (enc_expr x2 (k)))
  | FdDir  => 2 :: k
  end.
Fixpoint dec_afd (fuel : nat) (i : int) : option (afd * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in Some (FdStd , j0)) else
  if Z.eqb d 1 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_expr f) j2 with Some (y2, j3) => Some (FdFile y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 2 then (let j0 := nx i in Some (FdDir , j0)) else None end.
Definition enc_gatom (v : gatom) (k : list Z) : list Z :=
  match v with
  | GA x0 x1 => 0 :: enc_nat x0 (enc_list (fun x k0 => enc_expr x (k0)) x1 (k))
  end.
Fixpoint dec_gatom (fuel : nat) (i : int) : option (gatom * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_list (dec_expr f) f) j1 with Some (y1, j2) => Some (GA y0 y1, j2) | None => None end | None => None end) else None end.
Definition enc_acs (v : acs) (k : list Z) : list Z :=
  match v with
  | ACSG x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => 0 :: enc_sym_state x0 (enc_list (fun x k0 => enc_amap x (k0)) x1 (enc_Z x2 (enc_Z x3 (enc_Z x4 (enc_list (fun x k0 => enc_pair (fun x k0 => enc_expr x (k0)) (fun x k0 => enc_expr x (k0)) x (k0)) x5 (enc_list (fun x k0 => enc_pair (fun x k0 => enc_expr x (k0)) (fun x k0 => enc_expr x (k0)) x (k0)) x6 (enc_Z x7 (enc_expr x8 (enc_afd x9 (enc_bool x10 (enc_list (fun x k0 => enc_gatom x (k0)) x11 (k))))))))))))
  end.
Fixpoint dec_acs (fuel : nat) (i : int) : option (acs * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in match (dec_sym_state f) j0 with Some (y0, j1) => match (dec_list (dec_amap f) f) j1 with Some (y1, j2) => match (dec_Z f) j2 with Some (y2, j3) => match (dec_Z f) j3 with Some (y3, j4) => match (dec_Z f) j4 with Some (y4, j5) => match (dec_list (dec_pair (dec_expr f) (dec_expr f)) f) j5 with Some (y5, j6) => match (dec_list (dec_pair (dec_expr f) (dec_expr f)) f) j6 with Some (y6, j7) => match (dec_Z f) j7 with Some (y7, j8) => match (dec_expr f) j8 with Some (y8, j9) => match (dec_afd f) j9 with Some (y9, j10) => match (dec_bool f) j10 with Some (y10, j11) => match (dec_list (dec_gatom f) f) j11 with Some (y11, j12) => Some (ACSG y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11, j12) | None => None end | None => None end | None => None end | None => None end | None => None end | None => None end | None => None end | None => None end | None => None end | None => None end | None => None end | None => None end) else None end.
Definition enc_spiece (v : spiece) (k : list Z) : list Z :=
  match v with
  | SPLit x0 => 0 :: enc_list (fun x k0 => enc_Z x (k0)) x0 (k)
  | SPBlob x0 => 1 :: enc_nat x0 (k)
  end.
Fixpoint dec_spiece (fuel : nat) (i : int) : option (spiece * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in match (dec_list (dec_Z f) f) j0 with Some (y0, j1) => Some (SPLit y0, j1) | None => None end) else
  if Z.eqb d 1 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => Some (SPBlob y0, j1) | None => None end) else None end.
Fixpoint enc_shape (v : shape) (k : list Z) : list Z :=
  match v with
  | SNil  => 0 :: k
  | SExit x0 => 1 :: enc_Z x0 (k)
  | SEmitP x0 x1 x2 => 2 :: enc_Z x0 (enc_list (fun x k0 => enc_spiece x (k0)) x1 (enc_shape x2 (k)))
  | SAlt2 x0 x1 => 3 :: enc_shape x0 (enc_shape x1 (k))
  | SCase x0 x1 x2 x3 => 4 :: enc_expr x0 (enc_Z x1 (enc_shape x2 (enc_shape x3 (k))))
  | SHole x0 => 5 :: enc_nat x0 (k)
  | SNext  => 6 :: k
  end.
Fixpoint dec_shape (fuel : nat) (i : int) : option (shape * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in Some (SNil , j0)) else
  if Z.eqb d 1 then (let j0 := nx i in match (dec_Z f) j0 with Some (y0, j1) => Some (SExit y0, j1) | None => None end) else
  if Z.eqb d 2 then (let j0 := nx i in match (dec_Z f) j0 with Some (y0, j1) => match (dec_list (dec_spiece f) f) j1 with Some (y1, j2) => match (dec_shape f) j2 with Some (y2, j3) => Some (SEmitP y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 3 then (let j0 := nx i in match (dec_shape f) j0 with Some (y0, j1) => match (dec_shape f) j1 with Some (y1, j2) => Some (SAlt2 y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 4 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => match (dec_shape f) j2 with Some (y2, j3) => match (dec_shape f) j3 with Some (y3, j4) => Some (SCase y0 y1 y2 y3, j4) | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 5 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => Some (SHole y0, j1) | None => None end) else
  if Z.eqb d 6 then (let j0 := nx i in Some (SNext , j0)) else None end.
Fixpoint enc_plan (v : plan) (k : list Z) : list Z :=
  match v with
  | PRun x0 x1 => 0 :: enc_list (fun x k0 => enc_Z x (k0)) x0 (enc_plan x1 (k))
  | PSplit x0 x1 x2 x3 => 1 :: enc_expr x0 (enc_Z x1 (enc_plan x2 (enc_plan x3 (k))))
  | PCase2 x0 x1 x2 x3 => 2 :: enc_expr x0 (enc_Z x1 (enc_plan x2 (enc_plan x3 (k))))
  | PCaseDisj x0 x1 x2 x3 => 3 :: enc_expr x0 (enc_expr x1 (enc_plan x2 (enc_plan x3 (k))))
  | PShDisj x0 x1 x2 x3 x4 => 4 :: enc_expr x0 (enc_expr x1 (enc_expr x2 (enc_expr x3 (enc_plan x4 (k)))))
  | PContra  => 5 :: k
  | PFact x0 x1 => 6 :: enc_kentry x0 (enc_plan x1 (k))
  | PJoin x0 x1 x2 x3 => 7 :: enc_expr x0 (enc_Z x1 (enc_nat x2 (enc_plan x3 (k))))
  | PForget x0 x1 => 8 :: enc_list (fun x k0 => enc_nat x (k0)) x0 (enc_plan x1 (k))
  | PDropRange x0 x1 x2 => 9 :: enc_expr x0 (enc_expr x1 (enc_plan x2 (k)))
  | PGcKeep x0 x1 => 10 :: enc_list (fun x k0 => enc_pair (fun x k0 => enc_expr x (k0)) (fun x k0 => enc_expr x (k0)) x (k0)) x0 (enc_plan x1 (k))
  | PBump x0 x1 => 11 :: enc_nat x0 (enc_plan x1 (k))
  | PHavoc x0 x1 => 12 :: enc_list (fun x k0 => enc_nat x (k0)) x0 (enc_plan x1 (k))
  | PHavocBig x0 x1 => 13 :: enc_nat x0 (enc_plan x1 (k))
  | PFresh x0 x1 x2 x3 => 14 :: enc_nat x0 (enc_Z x1 (enc_opt (fun x k0 => enc_expr x (k0)) x2 (enc_plan x3 (k))))
  | PSys x0 x1 => 15 :: enc_snode x0 (enc_plan x1 (k))
  | PMmap x0 => 16 :: enc_plan x0 (k)
  | PMmapIn x0 => 17 :: enc_plan x0 (k)
  | PMprotect x0 => 18 :: enc_plan x0 (k)
  | PBrk x0 => 19 :: enc_plan x0 (k)
  | PX x0 x1 x2 => 20 :: enc_xnode x0 (enc_list (fun x k0 => enc_expr x (k0)) x1 (enc_plan x2 (k)))
  | PExt x0 x1 x2 => 21 :: enc_nat x0 (enc_list (fun x k0 => enc_expr x (k0)) x1 (enc_plan x2 (k)))
  | PEmit x0 x1 x2 => 22 :: enc_nat x0 (enc_list (fun x k0 => enc_expr x (k0)) x1 (enc_plan x2 (k)))
  | PExt2 x0 x1 x2 x3 => 23 :: enc_nat x0 (enc_list (fun x k0 => enc_expr x (k0)) x1 (enc_plan x2 (enc_plan x3 (k))))
  | PLoop x0 x1 x2 x3 x4 => 24 :: enc_nat x0 (enc_expr x1 (enc_acs x2 (enc_plan x3 (enc_plan x4 (k)))))
  | PNext  => 25 :: k
  | PHandoff x0 => 26 :: enc_nat x0 (k)
  | PExit  => 27 :: k
  | PSpin  => 28 :: k
  | PFog x0 x1 x2 => 29 :: enc_nat x0 (enc_Z x1 (enc_plan x2 (k)))
  | PFogNew x0 x1 x2 => 30 :: enc_nat x0 (enc_Z x1 (enc_plan x2 (k)))
  | PGhost x0 x1 x2 => 31 :: enc_expr x0 (enc_expr x1 (enc_plan x2 (k)))
  | PUnvis x0 x1 x2 => 32 :: enc_expr x0 (enc_expr x1 (enc_plan x2 (k)))
  | PHavocBrk x0 x1 x2 => 33 :: enc_Z x0 (enc_Z x1 (enc_plan x2 (k)))
  | PIntro x0 x1 x2 => 34 :: enc_Z x0 (enc_Z x1 (enc_plan x2 (k)))
  | PDiamond x0 x1 x2 => 35 :: enc_Z x0 (enc_list (fun x k0 => enc_nat x (k0)) x1 (enc_plan x2 (k)))
  | PRename x0 x1 => 36 :: enc_list (fun x k0 => enc_pair (fun x k0 => enc_nat x (k0)) (fun x k0 => enc_nat x (k0)) x (k0)) x0 (enc_plan x1 (k))
  | PCompact x0 => 37 :: enc_plan x0 (k)
  | PVia x0 x1 x2 x3 x4 => 38 :: enc_nat x0 (enc_acs x1 (enc_nat x2 (enc_plan x3 (enc_plan x4 (k)))))
  | PMerge x0 => 39 :: enc_nat x0 (k)
  | PAbstractCell x0 x1 x2 => 40 :: enc_expr x0 (enc_Z x1 (enc_plan x2 (k)))
  | PHavocWords x0 x1 => 41 :: enc_list (fun x k0 => enc_expr x (k0)) x0 (enc_plan x1 (k))
  | PRespell x0 x1 x2 => 42 :: enc_nat x0 (enc_expr x1 (enc_plan x2 (k)))
  | PWhileN x0 x1 x2 x3 x4 => 43 :: enc_nat x0 (enc_list (fun x k0 => enc_pair (fun x k0 => enc_acs x (k0)) (fun x k0 => enc_plan x (k0)) x (k0)) x1 (enc_expr x2 (enc_shape x3 (enc_list (fun x k0 => enc_pair (fun x k0 => enc_acs x (k0)) (fun x k0 => enc_plan x (k0)) x (k0)) x4 (k)))))
  | PNextN x0 x1 => 44 :: enc_nat x0 (enc_list (fun x k0 => enc_pair (fun x k0 => enc_nat x (k0)) (fun x k0 => enc_expr x (k0)) x (k0)) x1 (k))
  | PBreak x0 x1 => 45 :: enc_nat x0 (enc_list (fun x k0 => enc_pair (fun x k0 => enc_nat x (k0)) (fun x k0 => enc_expr x (k0)) x (k0)) x1 (k))
  | PUse x0 x1 x2 => 46 :: enc_nat x0 (enc_list (fun x k0 => enc_pair (fun x k0 => enc_nat x (k0)) (fun x k0 => enc_expr x (k0)) x (k0)) x1 (enc_list (fun x k0 => enc_plan x (k0)) x2 (k)))
  | PGIntro x0 x1 => 47 :: enc_gatom x0 (enc_plan x1 (k))
  | PGDrop x0 x1 => 48 :: enc_nat x0 (enc_plan x1 (k))
  | PGFact x0 x1 => 49 :: enc_kentry x0 (enc_plan x1 (k))
  | PGFactT x0 x1 x2 x3 => 50 :: enc_bool x0 (enc_nat x1 (enc_kentry x2 (enc_plan x3 (k))))
  | PHandoffS x0 x1 x2 => 51 :: enc_nat x0 (enc_nat x1 (enc_list (fun x k0 => enc_pair (fun x k0 => enc_nat x (k0)) (fun x k0 => enc_expr x (k0)) x (k0)) x2 (k)))
  | PBrk2 x0 x1 => 52 :: enc_plan x0 (enc_plan x1 (k))
  | PCaseDisjJ x0 x1 x2 x3 x4 => 53 :: enc_expr x0 (enc_expr x1 (enc_Z x2 (enc_list (fun x k0 => enc_nat x (k0)) x3 (enc_plan x4 (k)))))
  end.
Fixpoint dec_plan (fuel : nat) (i : int) : option (plan * int) :=
  match fuel with O => None | S f =>
  let d := rd i in
  if Z.eqb d 0 then (let j0 := nx i in match (dec_list (dec_Z f) f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PRun y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 1 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => match (dec_plan f) j3 with Some (y3, j4) => Some (PSplit y0 y1 y2 y3, j4) | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 2 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => match (dec_plan f) j3 with Some (y3, j4) => Some (PCase2 y0 y1 y2 y3, j4) | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 3 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => match (dec_plan f) j3 with Some (y3, j4) => Some (PCaseDisj y0 y1 y2 y3, j4) | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 4 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_expr f) j2 with Some (y2, j3) => match (dec_expr f) j3 with Some (y3, j4) => match (dec_plan f) j4 with Some (y4, j5) => Some (PShDisj y0 y1 y2 y3 y4, j5) | None => None end | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 5 then (let j0 := nx i in Some (PContra , j0)) else
  if Z.eqb d 6 then (let j0 := nx i in match (dec_kentry f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PFact y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 7 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => match (dec_nat f) j2 with Some (y2, j3) => match (dec_plan f) j3 with Some (y3, j4) => Some (PJoin y0 y1 y2 y3, j4) | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 8 then (let j0 := nx i in match (dec_list (dec_nat f) f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PForget y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 9 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PDropRange y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 10 then (let j0 := nx i in match (dec_list (dec_pair (dec_expr f) (dec_expr f)) f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PGcKeep y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 11 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PBump y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 12 then (let j0 := nx i in match (dec_list (dec_nat f) f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PHavoc y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 13 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PHavocBig y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 14 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => match (dec_opt (dec_expr f) f) j2 with Some (y2, j3) => match (dec_plan f) j3 with Some (y3, j4) => Some (PFresh y0 y1 y2 y3, j4) | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 15 then (let j0 := nx i in match (dec_snode f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PSys y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 16 then (let j0 := nx i in match (dec_plan f) j0 with Some (y0, j1) => Some (PMmap y0, j1) | None => None end) else
  if Z.eqb d 17 then (let j0 := nx i in match (dec_plan f) j0 with Some (y0, j1) => Some (PMmapIn y0, j1) | None => None end) else
  if Z.eqb d 18 then (let j0 := nx i in match (dec_plan f) j0 with Some (y0, j1) => Some (PMprotect y0, j1) | None => None end) else
  if Z.eqb d 19 then (let j0 := nx i in match (dec_plan f) j0 with Some (y0, j1) => Some (PBrk y0, j1) | None => None end) else
  if Z.eqb d 20 then (let j0 := nx i in match (dec_xnode f) j0 with Some (y0, j1) => match (dec_list (dec_expr f) f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PX y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 21 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_list (dec_expr f) f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PExt y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 22 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_list (dec_expr f) f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PEmit y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 23 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_list (dec_expr f) f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => match (dec_plan f) j3 with Some (y3, j4) => Some (PExt2 y0 y1 y2 y3, j4) | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 24 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_acs f) j2 with Some (y2, j3) => match (dec_plan f) j3 with Some (y3, j4) => match (dec_plan f) j4 with Some (y4, j5) => Some (PLoop y0 y1 y2 y3 y4, j5) | None => None end | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 25 then (let j0 := nx i in Some (PNext , j0)) else
  if Z.eqb d 26 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => Some (PHandoff y0, j1) | None => None end) else
  if Z.eqb d 27 then (let j0 := nx i in Some (PExit , j0)) else
  if Z.eqb d 28 then (let j0 := nx i in Some (PSpin , j0)) else
  if Z.eqb d 29 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PFog y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 30 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PFogNew y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 31 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PGhost y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 32 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PUnvis y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 33 then (let j0 := nx i in match (dec_Z f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PHavocBrk y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 34 then (let j0 := nx i in match (dec_Z f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PIntro y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 35 then (let j0 := nx i in match (dec_Z f) j0 with Some (y0, j1) => match (dec_list (dec_nat f) f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PDiamond y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 36 then (let j0 := nx i in match (dec_list (dec_pair (dec_nat f) (dec_nat f)) f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PRename y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 37 then (let j0 := nx i in match (dec_plan f) j0 with Some (y0, j1) => Some (PCompact y0, j1) | None => None end) else
  if Z.eqb d 38 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_acs f) j1 with Some (y1, j2) => match (dec_nat f) j2 with Some (y2, j3) => match (dec_plan f) j3 with Some (y3, j4) => match (dec_plan f) j4 with Some (y4, j5) => Some (PVia y0 y1 y2 y3 y4, j5) | None => None end | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 39 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => Some (PMerge y0, j1) | None => None end) else
  if Z.eqb d 40 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_Z f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PAbstractCell y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 41 then (let j0 := nx i in match (dec_list (dec_expr f) f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PHavocWords y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 42 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_plan f) j2 with Some (y2, j3) => Some (PRespell y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 43 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_list (dec_pair (dec_acs f) (dec_plan f)) f) j1 with Some (y1, j2) => match (dec_expr f) j2 with Some (y2, j3) => match (dec_shape f) j3 with Some (y3, j4) => match (dec_list (dec_pair (dec_acs f) (dec_plan f)) f) j4 with Some (y4, j5) => Some (PWhileN y0 y1 y2 y3 y4, j5) | None => None end | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 44 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_list (dec_pair (dec_nat f) (dec_expr f)) f) j1 with Some (y1, j2) => Some (PNextN y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 45 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_list (dec_pair (dec_nat f) (dec_expr f)) f) j1 with Some (y1, j2) => Some (PBreak y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 46 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_list (dec_pair (dec_nat f) (dec_expr f)) f) j1 with Some (y1, j2) => match (dec_list (dec_plan f) f) j2 with Some (y2, j3) => Some (PUse y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 47 then (let j0 := nx i in match (dec_gatom f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PGIntro y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 48 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PGDrop y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 49 then (let j0 := nx i in match (dec_kentry f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PGFact y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 50 then (let j0 := nx i in match (dec_bool f) j0 with Some (y0, j1) => match (dec_nat f) j1 with Some (y1, j2) => match (dec_kentry f) j2 with Some (y2, j3) => match (dec_plan f) j3 with Some (y3, j4) => Some (PGFactT y0 y1 y2 y3, j4) | None => None end | None => None end | None => None end | None => None end) else
  if Z.eqb d 51 then (let j0 := nx i in match (dec_nat f) j0 with Some (y0, j1) => match (dec_nat f) j1 with Some (y1, j2) => match (dec_list (dec_pair (dec_nat f) (dec_expr f)) f) j2 with Some (y2, j3) => Some (PHandoffS y0 y1 y2, j3) | None => None end | None => None end | None => None end) else
  if Z.eqb d 52 then (let j0 := nx i in match (dec_plan f) j0 with Some (y0, j1) => match (dec_plan f) j1 with Some (y1, j2) => Some (PBrk2 y0 y1, j2) | None => None end | None => None end) else
  if Z.eqb d 53 then (let j0 := nx i in match (dec_expr f) j0 with Some (y0, j1) => match (dec_expr f) j1 with Some (y1, j2) => match (dec_Z f) j2 with Some (y2, j3) => match (dec_list (dec_nat f) f) j3 with Some (y3, j4) => match (dec_plan f) j4 with Some (y4, j5) => Some (PCaseDisjJ y0 y1 y2 y3 y4, j5) | None => None end | None => None end | None => None end | None => None end | None => None end) else None end.
End Str.

(* [comment removed for export] *)
Definition ch (d : Z) : string :=
  match d with
  | 0 => PrimString.make 1%int63 63%int63
  | 1 => PrimString.make 1%int63 64%int63
  | 2 => PrimString.make 1%int63 65%int63
  | 3 => PrimString.make 1%int63 66%int63
  | 4 => PrimString.make 1%int63 67%int63
  | 5 => PrimString.make 1%int63 68%int63
  | 6 => PrimString.make 1%int63 69%int63
  | 7 => PrimString.make 1%int63 70%int63
  | 8 => PrimString.make 1%int63 71%int63
  | 9 => PrimString.make 1%int63 72%int63
  | 10 => PrimString.make 1%int63 73%int63
  | 11 => PrimString.make 1%int63 74%int63
  | 12 => PrimString.make 1%int63 75%int63
  | 13 => PrimString.make 1%int63 76%int63
  | 14 => PrimString.make 1%int63 77%int63
  | 15 => PrimString.make 1%int63 78%int63
  | 16 => PrimString.make 1%int63 79%int63
  | 17 => PrimString.make 1%int63 80%int63
  | 18 => PrimString.make 1%int63 81%int63
  | 19 => PrimString.make 1%int63 82%int63
  | 20 => PrimString.make 1%int63 83%int63
  | 21 => PrimString.make 1%int63 84%int63
  | 22 => PrimString.make 1%int63 85%int63
  | 23 => PrimString.make 1%int63 86%int63
  | 24 => PrimString.make 1%int63 87%int63
  | 25 => PrimString.make 1%int63 88%int63
  | 26 => PrimString.make 1%int63 89%int63
  | 27 => PrimString.make 1%int63 90%int63
  | 28 => PrimString.make 1%int63 91%int63
  | 29 => PrimString.make 1%int63 92%int63
  | 30 => PrimString.make 1%int63 93%int63
  | 31 => PrimString.make 1%int63 94%int63
  | 32 => PrimString.make 1%int63 95%int63
  | 33 => PrimString.make 1%int63 96%int63
  | 34 => PrimString.make 1%int63 97%int63
  | 35 => PrimString.make 1%int63 98%int63
  | 36 => PrimString.make 1%int63 99%int63
  | 37 => PrimString.make 1%int63 100%int63
  | 38 => PrimString.make 1%int63 101%int63
  | 39 => PrimString.make 1%int63 102%int63
  | 40 => PrimString.make 1%int63 103%int63
  | 41 => PrimString.make 1%int63 104%int63
  | 42 => PrimString.make 1%int63 105%int63
  | 43 => PrimString.make 1%int63 106%int63
  | 44 => PrimString.make 1%int63 107%int63
  | 45 => PrimString.make 1%int63 108%int63
  | 46 => PrimString.make 1%int63 109%int63
  | 47 => PrimString.make 1%int63 110%int63
  | 48 => PrimString.make 1%int63 111%int63
  | 49 => PrimString.make 1%int63 112%int63
  | 50 => PrimString.make 1%int63 113%int63
  | 51 => PrimString.make 1%int63 114%int63
  | 52 => PrimString.make 1%int63 115%int63
  | 53 => PrimString.make 1%int63 116%int63
  | 54 => PrimString.make 1%int63 117%int63
  | 55 => PrimString.make 1%int63 118%int63
  | 56 => PrimString.make 1%int63 119%int63
  | 57 => PrimString.make 1%int63 120%int63
  | 58 => PrimString.make 1%int63 121%int63
  | 59 => PrimString.make 1%int63 122%int63
  | 60 => PrimString.make 1%int63 123%int63
  | 61 => PrimString.make 1%int63 124%int63
  | 62 => PrimString.make 1%int63 125%int63
  | 63 => PrimString.make 1%int63 126%int63
  | _ => PrimString.make 1%int63 63%int63
  end.
Fixpoint pairup (l : list string) : list string :=
  match l with a :: b :: r => PrimString.cat a b :: pairup r | _ => l end.
Fixpoint catall (fuel : nat) (l : list string) : string :=
  match fuel with O => PrimString.make 0%int63 63%int63 | S f =>
    match l with [] => PrimString.make 0%int63 63%int63 | [x] => x | _ => catall f (pairup l) end end.
Definition to_str (ds : list Z) : string := catall 64%nat (List.map ch ds).

(* [comment removed for export] *)
Fixpoint int_to_Z_go (n : nat) (x m : int) (v acc : Z) : Z :=
  match n with O => acc | S n' => int_to_Z_go n' x (PrimInt63.lsl m 1%int63) (2 * v) (acc + zbit x m v) end.
Definition int_to_Z (x : int) : Z := int_to_Z_go 63%nat x 1%int63 1 0.

Definition pack (p : plan) : string := to_str (enc_plan p []).
Definition pack_acs (c : acs) : string := to_str (enc_acs c []).
Definition fuel_of (s : string) : nat := Z.to_nat (int_to_Z (PrimString.length s) + 2).
Definition decode_plan (s : string) : plan :=
  match dec_plan s (fuel_of s) 0%int63 with Some (p, _) => p | None => PContra end.
Definition decode_acs (s : string) : option acs :=
  match dec_acs s (fuel_of s) 0%int63 with Some (c, _) => Some c | None => None end.
End PKC.
