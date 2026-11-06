(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxSys AxOcc AxSysDisp.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Export AxSys2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

Definition is_zero_form (f : lin) : bool := (fst f =? 0) &&& match snd f with [] => true | _ => false end.

(* [comment removed for export] *)
Definition brk_grow_guard (A : AST) (b : lin) (d : Z) : bool :=
  let am := a_model A in
  let s := a_facts A in
  (0 <? d) &&& (d <? 1099511627776) &&& (d mod 4096 =? 0) &&& lin_al 4096 b &&& (0 <=? fst b) &&& (fst b <? 9223372036854775808)
  &&& match lrange s b, lrange s (lsub b (am_brk0 am)) with
      | Some (blo, bhi), Some (dlo, _) => (0 <? blo) &&& (bhi + d + 4096 <? 140737488355328) &&& (0 <=? dlo)
      | _, _ => false
      end
  &&& am_shadow am &&& eb_above s (am_atop am) (a_mem A) &&& ss_wit s (a_mem A) &&& lforall (fun R => (0 <? to_Z (rg_n R))) (a_mem A).

Definition sys_brk2 (A : AST) : option (list AST) :=
  let am := a_model A in
  let s := a_facts A in
  let r := a_regs A in
  let b := am_brk am in
  match xform s (aget r 10%uint63) with
  | Some f =>
      if is_zero_form f then
        match lrange s b with
        | Some (blo, bhi) =>
            if (0 <=? blo) &&& (bhi <? 18446744073709551616)
            then Some [with_model A (npc A) (aset r reg_a0 (of_form b)) (a_mem A) s am (a_budget A)] else None
        | None => None
        end
      else
        let dl := lsub f b in
        match snd dl with
        | [] =>
            let d := fst dl in
            if brk_grow_guard A b d then
              Some [ with_model A (npc A) (aset r reg_a0 (of_form f))
                       (zero_rg (snd b) (wofZ (fst b)) d :: comp_rg (snd b) (wofZ (fst b)) d :: a_mem A) s
                       (am_brk_grow am (AE b d false) f (am_next am)) (a_budget A + d);
                     with_model A (npc A) (aset r reg_a0 (of_form b)) (a_mem A) s am (a_budget A) ]
            else None
        | _ => None
        end
  | None => None
  end.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition sys_disp2 (LIM : Z) (A : AST) : option (list AST) :=
  match sys_disp segs LIM A with
  | Some l => Some l
  | None =>
      if pc_ok (npc A) then
        match xlit (aget (a_regs A) 17%uint63) with
        | Some 222 =>
            match sys_fix_rw LIM A with
            | Some l => Some l
            | None => match sys_fix_sh LIM A with Some l => Some l | None => sys_fix_none A end
            end
        | Some 215 => sys_munmap2 A
        | Some 226 => sys_mprotect2 LIM A
        | Some 214 => sys_brk2 A
        | _ => None
        end
      else None
  end.

End WithSegs.
