(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Module KB.
Import AX2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition M64 : Z := Z.ones 64.

Record kbits : Type := KB { km : Z; kv : Z }.

(* [comment removed for export] *)
Definition full (z : Z) : kbits := KB M64 (Z.land z M64).
Definition is_full (b : kbits) : bool := Z.eqb (Z.land (km b) M64) M64.
(* [comment removed for export] *)
Definition lit (b : kbits) : Z := Z.land (kv b) M64.

(* [comment removed for export] *)
Definition k1 (b : kbits) : Z := Z.land (km b) (kv b).
Definition k0 (b : kbits) : Z := Z.ldiff (km b) (kv b).

Definition kb_or (a b : kbits) : kbits :=
  let o := Z.lor (k1 a) (k1 b) in KB (Z.lor o (Z.land (k0 a) (k0 b))) o.
Definition kb_and (a b : kbits) : kbits :=
  let o := Z.land (k1 a) (k1 b) in KB (Z.lor o (Z.lor (k0 a) (k0 b))) o.
Definition kb_xor (a b : kbits) : kbits :=
  let m := Z.land (km a) (km b) in KB m (Z.land (Z.lxor (kv a) (kv b)) m).
(* [comment removed for export] *)
Definition kb_srl (a : kbits) (s : Z) : kbits :=
  KB (Z.lor (Z.shiftr (km a) s) (Z.ldiff M64 (Z.ones (64 - s)))) (Z.shiftr (Z.land (kv a) M64) s).
(* [comment removed for export] *)
Definition kb_sll (a : kbits) (s : Z) : kbits :=
  KB (Z.lor (Z.shiftl (km a) s) (Z.ones s)) (Z.shiftl (kv a) s).
(* [comment removed for export] *)
Definition kb_ext (lo n : nat) (a : kbits) : kbits :=
  let l := 8 * Z.of_nat lo in let w := 8 * Z.of_nat n in
  KB (Z.lor (Z.shiftr (km a) l) (Z.ldiff M64 (Z.ones w))) (Z.land (Z.shiftr (Z.land (kv a) M64) l) (Z.ones w)).

(* [comment removed for export] *)
Definition prefix_len (lo hi : Z) : Z := if Z.eqb lo hi then 0 else Z.log2 (Z.lxor lo hi) + 1.
Definition kb_range (lo hi : Z) : option kbits :=
  if (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi two64)%bool then
    let p := prefix_len lo hi in
    if (Z.leb 0 p && Z.leb p 64 && Z.eqb (Z.shiftr lo p) (Z.shiftr hi p))%bool then
      let m := Z.ldiff M64 (Z.ones p) in Some (KB m (Z.land lo m))
    else None
  else None.

Definition leaf (k : list kentry) (e : expr) : option kbits :=
  match xlo k e, xhi k e with
  | Some lo, Some hi => kb_range lo hi
  | _, _ => None
  end.

Definition orelse (r l : option kbits) : option kbits := match r with Some x => Some x | None => l end.

(* [comment removed for export] *)
Definition shamt (b : kbits) : Z := Z.land (lit b) (Z.ones 6).

Definition kb_alu (op : aluop) (ka kb : kbits) : option kbits :=
  if (is_full ka && is_full kb)%bool then Some (full (zalu op (lit ka) (lit kb)))
  else match op with
       | ALU_OR => Some (kb_or ka kb)
       | ALU_AND => Some (kb_and ka kb)
       | ALU_XOR => Some (kb_xor ka kb)
       | ALU_SRL => if is_full kb then Some (kb_srl ka (shamt kb)) else None
       | ALU_SLL => if is_full kb then Some (kb_sll ka (shamt kb)) else None
       | _ => None
       end.

Definition kb_extop (sx : bool) (lo n : nat) (ka : kbits) : option kbits :=
  if is_full ka then Some (full (zext_lit sx lo n (lit ka)))
  else if sx then None else Some (kb_ext lo n ka).

Fixpoint kb_eval (fuel : nat) (k : list kentry) (e : expr) : option kbits :=
  match fuel with
  | O => None
  | S f =>
      match e with
      | ELit z => Some (full z)
      | EAlu op a b =>
          orelse (match kb_eval f k a, kb_eval f k b with
                  | Some ka, Some kb => kb_alu op ka kb
                  | _, _ => None
                  end) (leaf k e)
      | EAluw op a b =>
          orelse (match kb_eval f k a, kb_eval f k b with
                  | Some ka, Some kb => if (is_full ka && is_full kb)%bool then Some (full (zaluw op (lit ka) (lit kb))) else None
                  | _, _ => None
                  end) (leaf k e)
      | EMd op a b =>
          orelse (match kb_eval f k a, kb_eval f k b with
                  | Some ka, Some kb => if (is_full ka && is_full kb)%bool then Some (full (zmd op (lit ka) (lit kb))) else None
                  | _, _ => None
                  end) (leaf k e)
      | EMdw op a b =>
          orelse (match kb_eval f k a, kb_eval f k b with
                  | Some ka, Some kb => if (is_full ka && is_full kb)%bool then Some (full (zmdw op (lit ka) (lit kb))) else None
                  | _, _ => None
                  end) (leaf k e)
      | EExt sx lo n a =>
          orelse (match kb_eval f k a with
                  | Some ka => kb_extop sx lo n ka
                  | None => None
                  end) (leaf k e)
      | _ => leaf k e
      end
  end.

(* [comment removed for export] *)
Definition KB_FUEL : nat := 512.

(* [comment removed for export] *)
Definition kb_lit_eq (k : list kentry) (a e : expr) : bool :=
  match e with
  | ELit v => match kb_eval KB_FUEL k a with
              | Some b => (is_full b && Z.eqb (lit b) (zlit64 v))%bool
              | None => false
              end
  | _ => false
  end.

End KB.
