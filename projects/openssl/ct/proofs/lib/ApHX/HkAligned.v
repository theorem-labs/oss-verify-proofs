(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import FastWord.
From OSSVerify.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxMem HxStep HxHook.
Import ListNotations.
Local Open Scope uint63_scope.

(* [comment removed for export] *)
Definition hk_posix_memalign (stk : int) (cd : acd) (S : sstate) : option (acd * sstate) :=
  match a_ops cd, rget S X10, zval (rget S X11), zval (rget S X12), rget S X2 with
  | (3%Z, n, al) :: rest, VP ts o, Some al', Some n', VP ts2 osp =>
      if (ts =? stk) && (ts2 =? stk) && (n =? n')%Z && (al =? al')%Z && (al =? 64)%Z && (0 <? n)%Z && (n <? 2147483648)%Z
         && negb (wh o) && negb (wh osp) && (wl o land 7 =? 0) && (wl osp <=? wl o) then
        match mget (s_mem S) stk with
        | Some rg =>
            if (wl o <=? rg_size rg) && (wl o + 8 <=? rg_size rg) && rg_wr rg then
              let t := s_next S in
              let M' := mset (s_mem S) stk (wr_cell rg (wl o >> 3) (CP t w_zero)) in
              match hk_return S (VC w_zero) (new_region M' t (of_Z n) 6 DUnk) (t + 1) with
              | Some S' => Some (ACD rest (t :: a_tags cd) (a_n cd + 1)%Z, S')
              | None => None
              end
            else None
        | None => None
        end
      else None
  | _, _, _, _, _ => None
  end.

Definition hk_posix_memalign_v (t_errno errno_int : int) (tpv : w64) (stk : int) (cd : acd) (S : sstate) : option (acd * sstate) :=
  if tp_ok tpv S && sp_ok stk S then
    match reset_errno t_errno errno_int (s_mem S) with
    | Some M1 => hk_posix_memalign stk cd (SS (s_pc S) (s_regs S) (s_resv S) M1 (s_abs S) (s_next S))
    | None => None
    end
  else None.
