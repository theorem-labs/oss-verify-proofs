(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxStep HxHook.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tag_even (t : int) : bool := (t land 1 =? 0)%uint63.

(* [comment removed for export] *)
Definition sh_tag (t : int) : int := (t + 1)%uint63.

Section Shadow.
(* [comment removed for export] *)
Variable shb : w64.

Definition sh_rule (M : mem) (a : hval) : option hval :=
  match a with
  | VP t o =>
      if tag_even t && inb (ctx_of M) t o then
        match ctx_of M t, mget M (sh_tag t) with
        | Some (al, _), Some rgs =>
            match rg_abs rgs with
            | None => if (3 <=? al)%uint63 then Some (VP (sh_tag t) (w_sub (W false (wl o >> 3)%uint63) shb)) else None
            | Some _ => None
            end
        | _, _ => None
        end
      else None
  | _ => None
  end.

Definition is_three (w : w64) : bool := negb (wh w) && (wl w =? 3)%uint63.

(* [comment removed for export] *)
Definition al_rule (M : mem) (t : int) (o m : w64) : option hval :=
  match ctx_of M t with
  | Some (al, _) =>
      let c := w_xor m w_ones in
      if inb (ctx_of M) t o && negb (wh c) && (wl c <? (1 << al))%uint63 then Some (VP t (w_sub o (w_and o c))) else None
  | None => None
  end.

(* [comment removed for export] *)
Definition xalu (M : mem) (op : aluop) (a b : hval) : option hval :=
  match op, a, b with
  | ALU_SRL, VP _ _, VC sh => if is_three sh then sh_rule M a else None
  | ALU_AND, VP t o, VC m => al_rule M t o m
  | _, _, _ => None
  end.

Variable segs : list Segment.

Definition hxs_exec (d : dinstr) (S : sstate) : sres :=
  let npc := w_add (s_pc S) w_four in
  match d with
  | DOpImm op rd rs1 imm =>
      match xalu (s_mem S) op (rget S rs1) (VC imm) with Some v => SNext (with_reg_pc S rd v npc) | None => hx_exec segs d S end
  | DShiftImm op rd rs1 sh =>
      match xalu (s_mem S) op (rget S rs1) (VC sh) with Some v => SNext (with_reg_pc S rd v npc) | None => hx_exec segs d S end
  | DOp op rd rs1 rs2 =>
      match xalu (s_mem S) op (rget S rs1) (rget S rs2) with Some v => SNext (with_reg_pc S rd v npc) | None => hx_exec segs d S end
  | _ => hx_exec segs d S
  end.

Definition hxs_step (ic : icache) (S : sstate) : icache * sres :=
  match hx_fetch segs ic (s_pc S) with
  | Some (d, ic') => (ic', hxs_exec d S)
  | None => (ic, SStuck 1 S)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Run.
Variable stop : w64 -> bool.

Definition hxs_step1 (ic : icache) (S : sstate) : icache * rres :=
  if stop (s_pc S) then (ic, RStop S) else
  match hxs_step ic S with
  | (ic', SNext S') => (ic', RRun S')
  | (ic', SStuck c S') => (ic', RStuck c S')
  end.

Fixpoint hxs_run (n : nat) (ic : icache) (S : sstate) : icache * rres :=
  match n with
  | O => hxs_step1 ic S
  | Datatypes.S n' =>
      match hxs_run n' ic S with
      | (ic', RRun S') => hxs_run n' ic' S'
      | r => r
      end
  end.

End Run.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Drive.
Context {CD : Type}.
Definition hook := CD -> sstate -> option (CD * sstate).
(* [comment removed for export] *)
Variable hookix : itrie nat.
Variable hooks : list hook.
Variable final : w64 -> bool.

Definition hook_at (pc : w64) : option hook :=
  if pc_ok pc then match iget ICD hookix (ic_key pc) with Some i => nth_error hooks i | None => None end else None.

Definition xstop_pc (pc : w64) : bool := final pc || match hook_at pc with Some _ => true | None => false end.

Inductive xres : Type :=
| XDone (cd : CD) (S : sstate)
| XStuck (code : int) (cd : CD) (S : sstate)
| XFuel (cd : CD) (S : sstate).

(* [comment removed for export] *)
Fixpoint hxs_drive (k : nat) (n : nat) (ic : icache) (cd : CD) (S : sstate) : icache * xres :=
  match hxs_run xstop_pc n ic S with
  | (ic', RStop S') =>
      if final (s_pc S') then (ic', XDone cd S') else
      match hook_at (s_pc S') with
      | Some h =>
          match h cd S' with
          | Some (cd', S'') =>
              if (s_next S' <=? s_next S'')%uint63 then
                match k with O => (ic', XFuel cd' S'') | Datatypes.S k' => hxs_drive k' n ic' cd' S'' end
              else (ic', XStuck 102 cd S')     (* [comment removed for export] *)
          | None => (ic', XStuck 100 cd S')
          end
      | None => (ic', XStuck 101 cd S')
      end
  | (ic', RStuck c S') => (ic', XStuck c cd S')
  | (ic', RRun S') => (ic', XFuel cd S')
  end.

End Drive.

End Shadow.
