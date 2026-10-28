(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib LiaTuning.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs BzTac BzTac2 BzContracts DecCut JunkFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From Ltac2 Require Ltac2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.

(* [comment removed for export] *)
Inductive nf_failed (h : Z) (G : Prop) : Prop := NfFail.

Module NF.
  Import Ltac2.
  Ltac2 mix (a : int) (b : int) : int := Int.land (Int.add (Int.mul a 1000003) b) 1152921504606846975.
  Ltac2 hash_string (s : string) : int :=
    let n := String.length s in
    let rec go (i : int) (acc : int) : int :=
      if Int.ge i n then acc else go (Int.add i 1) (mix acc (Char.to_int (String.get s i))) in
    go 0 7.
  (* [comment removed for export] *)
  Ltac2 rec hc (acc : int) (c : constr) : int :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Rel n => mix acc (Int.add 3 n)
    | Constr.Unsafe.Var id => mix acc (hash_string (Ident.to_string id))
    | Constr.Unsafe.App f args => Array.fold_left hc (hc (mix acc 5) f) args
    | Constr.Unsafe.Constant _ _ => mix acc 11
    | Constr.Unsafe.Ind _ _ => mix acc 13
    | Constr.Unsafe.Constructor k _ => mix (mix acc 17) (Constructor.index k)
    | Constr.Unsafe.Prod b t => hc (hc (mix acc 19) (Constr.Binder.type b)) t
    | Constr.Unsafe.Lambda b t => hc (hc (mix acc 23) (Constr.Binder.type b)) t
    | Constr.Unsafe.LetIn b v t => hc (hc (hc (mix acc 29) (Constr.Binder.type b)) v) t
    | Constr.Unsafe.Cast x _ t => hc (hc (mix acc 31) x) t
    | _ => mix acc 37
    end.
  Ltac2 mk1 (f : constr) (x : constr) : constr := Constr.Unsafe.make (Constr.Unsafe.App f (Array.make 1 x)).
  Ltac2 rec pos_of_int (n : int) : constr :=
    if Int.le n 1 then 'xH
    else let r := pos_of_int (Int.div n 2) in
         if Int.equal (Int.mod n 2) 0 then mk1 'xO r else mk1 'xI r.
  Ltac2 z_of_int (n : int) : constr := if Int.le n 0 then 'Z0 else mk1 'Zpos (pos_of_int n).
  Ltac2 hash_z (g : constr) : constr := z_of_int (hc 1 g).

  (* [comment removed for export] *)
  Ltac2 marker_parts (ty : constr) : (constr * constr) option :=
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 2 then
          (if Constr.equal f '@nf_failed then Some (Array.get args 0, Array.get args 1) else None)
        else None
    | _ => None
    end.
  (* [comment removed for export] *)
  Ltac2 inert_head (h : constr) : bool :=
    if Constr.equal h '@rw_cells then true else if Constr.equal h '@u8arr then true
    else if Constr.equal h '@u32arr then true else if Constr.equal h '@bytes_at then true
    else if Constr.equal h '@stk then true else if Constr.equal h '@munch then true
    else if Constr.equal h '@wmono then true else if Constr.equal h '@mem_inv then true
    else if Constr.equal h '@hidden then true else if Constr.equal h '@drest_at then true
    else if Constr.equal h '@blk_at then true else if Constr.equal h '@nf_failed then true
    else if Constr.equal h '@zify_done then true else Constr.equal h '@zify_done_qr.
  Ltac2 relevant (body : constr option) (ty : constr) : bool :=
    match body with
    | Some _ => true
    | None => if zt_is_prop ty then (if inert_head (zt_head ty) then false else true) else false
    end.
  Ltac2 rec has_marker (hs : (ident * constr option * constr) list) : bool :=
    match hs with
    | [] => false
    | h :: r => let (_, _, ty) := h in match marker_parts ty with Some _ => true | None => has_marker r end
    end.
  (* [comment removed for export] *)
  Ltac2 rec stale_ids (hs : (ident * constr option * constr) list) (seen : bool) (acc : ident list) : ident list :=
    match hs with
    | [] => acc
    | h :: r =>
        let (id, body, ty) := h in
        match marker_parts ty with
        | Some p => let (hz, g) := p in
                    if seen then stale_ids r seen (id :: acc)
                    else (if Constr.equal hz (hash_z g) then stale_ids r seen acc else stale_ids r seen (id :: acc))
        | None => stale_ids r (if seen then true else relevant body ty) acc
        end
    end.
  Ltac2 prune () : unit :=
    let hs := Control.hyps () in
    if has_marker hs then
      (match stale_ids (List.rev hs) false [] with
       | [] => ()
       | ids => Std.clear ids
       end)
    else ().
  Ltac2 clear_markers () : unit :=
    let ids := List.map_filter (fun h => let (id, _, ty) := h in
                 match marker_parts ty with Some _ => Some id | None => None end) (Control.hyps ()) in
    match ids with [] => () | _ => Std.clear ids end.
  Ltac2 mark (g : constr) : unit :=
    let hz := hash_z g in
    ltac1:(hz g |- pose proof (@NfFail hz g)) (Ltac1.of_constr hz) (Ltac1.of_constr g).
End NF.
Ltac nf_prune := ltac2:(Control.enter NF.prune).
(* [comment removed for export] *)
Ltac nf_pre := ltac2:(Control.enter NF.clear_markers).
Ltac nf_pre_natlen := nf_pre; NatLit.natlen_ctx.
Ltac nf_mlia := nf_pre; mlia.
Ltac nf_mark G := let f := ltac2:(g |- NF.mark (Option.get (Ltac1.to_constr g))) in f G.

(* [comment removed for export] *)
Ltac nf_rw lem solver :=
  let T := type of lem in
  lazymatch T with
  | ?G -> _ =>
      lazymatch goal with
      | _ : nf_failed _ G |- _ => fail
      | _ => first [ rewrite lem by solver | nf_mark G ]
      end
  end.

(* [comment removed for export] *)
Ltac bz32_m :=
  nf_prune;
  strip_mod64_in_swrap;
  repeat match goal with
  | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
  | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
  | |- context [bv_wrap 32 ?e] => change (bv_wrap 32 e) with (Z.modulo e 4294967296)
  | |- context [Z.modulo ?e 4294967296] => nf_rw (Z.mod_small e 4294967296) ltac:(nf_mlia)
  | |- context [bv_swrap 32 ?e] => nf_rw (swrap32_id e) ltac:(nf_mlia)
  | |- context [Z.modulo ?e 18446744073709551616] => nf_rw (Z.mod_small e 18446744073709551616) ltac:(nf_mlia)
  | |- context [Z.lxor ?e 9223372036854775808] => nf_rw (lxor_sign_small e) ltac:(nf_mlia)
  | |- context [Z.lxor ?e 18446744073709551615] => nf_rw (zb_lxor_ones e) ltac:(nf_mlia)
  | |- context [bv_signed (Z_to_bv 64 ?e)] => nf_rw (signed_lit_small e) ltac:(nf_mlia)
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => nf_rw (unsigned_lit e) ltac:(nf_mlia)
  | |- context [sx32 (Z_to_bv 64 ?e)] => nf_rw (sx32_of_Z e) ltac:(nf_mlia)
  | |- context [zx32 (Z_to_bv 64 ?e)] => nf_rw (zx32_of_Z e) ltac:(nf_mlia)
  end; zb_fold_lits.
Ltac bz32l_m :=
  nf_prune;
  strip_mod64_in_swrap;
  repeat match goal with
  | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
  | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
  | |- context [bv_wrap 32 ?e] => change (bv_wrap 32 e) with (Z.modulo e 4294967296)
  | |- context [Z.modulo ?e 4294967296] => nf_rw (Z.mod_small e 4294967296) ltac:(lia)
  | |- context [bv_swrap 32 ?e] => nf_rw (swrap32_small e) ltac:(lia)
  | |- context [Z.modulo ?e 18446744073709551616] => nf_rw (Z.mod_small e 18446744073709551616) ltac:(lia)
  | |- context [Z.lxor ?e 9223372036854775808] => nf_rw (lxor_sign_small e) ltac:(lia)
  | |- context [Z.lxor ?e 18446744073709551615] => nf_rw (zb_lxor_ones e) ltac:(lia)
  | |- context [bv_signed (Z_to_bv 64 ?e)] => nf_rw (signed_lit_small e) ltac:(lia)
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => nf_rw (unsigned_lit e) ltac:(lia)
  | |- context [sx32 (Z_to_bv 64 ?e)] => nf_rw (sx32_of_Z e) ltac:(lia)
  | |- context [zx32 (Z_to_bv 64 ?e)] => nf_rw (zx32_of_Z e) ltac:(lia)
  end; zb_fold_lits.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac unset_Z_subst := repeat match goal with v := _ : Z |- _ => subst v end.
