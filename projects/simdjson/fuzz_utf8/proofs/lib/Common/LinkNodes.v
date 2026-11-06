(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.
(* [comment removed for export] *)

Module LNK.

Definition LINK_ID : nat := 110.

Section Node.
  Context {fx : FPState}.

  (* [comment removed for export] *)
  Definition mhi_pos (j : Z) : Z := two64 - 2 ^ j.
  Definition mhi_neg (j : Z) : Z := - 2 ^ j.

  Definition lin_eq0 (k : list kentry) (a b : expr) : bool :=
    lin_ge0 k [(a, 0)] [(b, 0)] && lin_ge0 k [(b, 0)] [(a, 0)].

  (* [comment removed for export] *)
  Definition block_linked (k : list kentry) (x : expr) (j : Z) (ne : expr) : bool :=
    match xlo k x, xhi k x, erange k ne with
    | Some l, Some h, Some (nl, nh) =>
        let c := (l / 2 ^ j) * 2 ^ j in
        (Z.leb 0 l && Z.eqb (l / 2 ^ j) (h / 2 ^ j) && Z.eqb nl c && Z.eqb nh c)%bool
    | _, _, _ => false
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition srl_form (x : expr) (j : Z) : expr := EMd M_MUL (ELit (2 ^ j)) (EAlu ALU_SRL x (ELit j)).
  Definition high_linked (k : list kentry) (x : expr) (j : Z) (ne : expr) : bool :=
    lin_eq0 k (EAlu ALU_AND x (ELit (mhi_pos j))) ne || lin_eq0 k (EAlu ALU_AND x (ELit (mhi_neg j))) ne || block_linked k x j ne
    || lin_eq0 k (srl_form x j) ne.

  Definition xn (args : list expr) (cs : acs) : option acs :=
    match args with
    | [x; ELit j; ne] =>
        if (Z.leb 1 j && Z.leb j 63 && high_linked (kn cs) x j ne)%bool then
          match erange (kn cs) (EAlu ALU_AND x (ELit (2 ^ j - 1))) with
          | Some (lo, hi) => Some (set_kn cs (KRange (esub x ne) lo hi :: kn cs))
          | None => None
          end
        else None
    | _ => None
    end.
End Node.

End LNK.
