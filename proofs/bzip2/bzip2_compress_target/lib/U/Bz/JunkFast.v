(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From Ltac2 Require Ltac2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.

Module JF.
  Import Ltac2.
  Ltac2 name_is_junk (id : ident) : bool :=
    let s := Ident.to_string id in
    let pre (p : string) : bool :=
      if Int.lt (String.length s) (String.length p) then false else String.equal (String.sub s 0 (String.length p)) p in
    if pre "junk" then true else pre "jbk".
  (* [comment removed for export] *)
  Ltac2 rec over_junk (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Var id => name_is_junk id
    | _ => lazy_match! c with
           | List.firstn _ ?x => over_junk x
           | List.skipn _ ?x => over_junk x
           | _ => false
           end
    end.
  Ltac2 check (c : constr) : unit := if over_junk c then () else Control.zero (Tactic_failure None).
End JF.
Ltac jf_check j := let f := ltac2:(j |- JF.check (Option.get (Ltac1.to_constr j))) in f j.
Ltac forget_junk :=
  repeat match goal with
  | FR : rw_cells _ _ _ ?cs |- _ =>
      match cs with
      | context [CB _ (@List.firstn byte ?k ?x)] =>
          jf_check x; let j := constr:(@List.firstn byte k x) in
          let jv := fresh "jbk" in let E := fresh "Ejbk" in remember j as jv eqn:E in FR; clear E
      | context [CB _ (@List.skipn byte ?k ?x)] =>
          jf_check x; let j := constr:(@List.skipn byte k x) in
          let jv := fresh "jbk" in let E := fresh "Ejbk" in remember j as jv eqn:E in FR; clear E
      end
  end.

(* [comment removed for export] *)
Ltac bz32_old :=
  strip_mod64_in_swrap;
  repeat match goal with
  | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
  | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
  | |- context [bv_wrap 32 ?e] => change (bv_wrap 32 e) with (Z.modulo e 4294967296)
  | |- context [Z.modulo ?e 4294967296] => rewrite (Z.mod_small e 4294967296) by mlia
  | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by mlia
  | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by mlia
  | |- context [Z.lxor ?e 9223372036854775808] => rewrite (lxor_sign_small e) by mlia
  | |- context [Z.lxor ?e 18446744073709551615] => rewrite (zb_lxor_ones e) by mlia
  | |- context [bv_signed (Z_to_bv 64 ?e)] => rewrite (signed_lit_small e) by mlia
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by mlia
  | |- context [sx32 (Z_to_bv 64 ?e)] => rewrite (sx32_of_Z e) by mlia
  | |- context [zx32 (Z_to_bv 64 ?e)] => rewrite (zx32_of_Z e) by mlia
  end; zb_fold_lits.
Ltac bz32l_old :=
  strip_mod64_in_swrap;
  repeat match goal with
  | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
  | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
  | |- context [bv_wrap 32 ?e] => change (bv_wrap 32 e) with (Z.modulo e 4294967296)
  | |- context [Z.modulo ?e 4294967296] => rewrite (Z.mod_small e 4294967296) by lia
  | |- context [bv_swrap 32 ?e] => rewrite (swrap32_small e) by lia
  | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
  | |- context [Z.lxor ?e 9223372036854775808] => rewrite (lxor_sign_small e) by lia
  | |- context [Z.lxor ?e 18446744073709551615] => rewrite (zb_lxor_ones e) by lia
  | |- context [bv_signed (Z_to_bv 64 ?e)] => rewrite (signed_lit_small e) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  | |- context [sx32 (Z_to_bv 64 ?e)] => rewrite (sx32_of_Z e) by lia
  | |- context [zx32 (Z_to_bv 64 ?e)] => rewrite (zx32_of_Z e) by lia
  end; zb_fold_lits.
Ltac bz32_j := forget_junk; bz32_old.
Ltac bz32l_j := forget_junk; bz32l_old.
