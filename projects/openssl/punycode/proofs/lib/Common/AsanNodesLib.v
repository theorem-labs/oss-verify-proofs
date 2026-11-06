(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module LBN.

Record libtab : Type := LTX {
  lt_dec : Z;                 (* [comment removed for export] *)
  lt_loop : Z;                (* [comment removed for export] *)
  lt_loop_exit : Z;           (* [comment removed for export] *)
  lt_rodata : list (Z * Z);   (* [comment removed for export] *)
  lt_imgend : Z;              (* [comment removed for export] *)
  (* [comment removed for export] *)
  lt_dframe : Z;              (* [comment removed for export] *)
  lt_ldepth : Z;              (* [comment removed for export] *)
  lt_strict : bool }.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition LT (dec loop loop_exit : Z) (rodata : list (Z * Z)) (imgend : Z) : libtab := LTX dec loop loop_exit rodata imgend 144 2384 false.

(* [comment removed for export] *)
Definition loop_havoc : list nat :=
  [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition NLH : nat := 27.

Section WithSegs.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable T : libtab.

(* [comment removed for export] *)
Definition addr_in (k : list kentry) (e : expr) (n : Z) (lo hi : Z) : bool :=
  match xlo k e, xhi k e with
  | Some l, Some h => Z.leb lo l && Z.leb (h + n) hi
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition stk_ok (k : list kentry) (e : expr) (off n : Z) : bool :=
  let '(b, o) := split_lit e in
  kwritable_x k k b (o + off) (ELit n) && addr_in k e 0 (lt_imgend T - off) (2 ^ 63 - 1 - off - n).

(* [comment removed for export] *)
Definition ovl_ok (k : list kentry) (e : expr) (n : expr) : bool :=
  let '(b, o) := split_lit e in
  kwritable_x k k b o n && off_image_x A k b o n.

(* [comment removed for export] *)
Definition hav (k : list kentry) (e : expr) (off n : Z) : list kentry :=
  let '(b, o) := split_lit e in kn_havoc k b (o + off) (ELit n).

(* [comment removed for export] *)
Definition node_decode (cs : acs) : option acs :=
  let k := kn cs in
  if (negb (Z.eqb (pc cs) (lt_dec T)) || Z.eqb (lt_dec T) 0)%bool then None else
  match ret_lit cs with
  | Some ret =>
      let sp := reg cs 2 in let p := reg cs 10 in let n := reg cs 11 in let out := reg cs 12 in let q := reg cs 13 in
      let '(qb, qo) := split_lit q in
      match kreadZ segs k qb qo 4, xlo k n, xhi k n, xhi k p with
      | Some mx, Some nlo, Some nhi, Some phi =>
          if (Z.leb 1 mx && Z.leb mx 512 && Z.leb 0 nlo && Z.ltb nhi (2 ^ 31) && Z.ltb (phi + nhi) (2 ^ 63)
              && (Z.eqb nhi 0 || (Z.leb 1 nlo && ovl_ok k p n))
              && (Z.ltb 0 (lt_dframe T) && Z.ltb (lt_dframe T) 65536)
              && (negb (lt_strict T)
                  || ((Z.eqb nhi 0 || match xlo k p with Some l => Z.leb 1 l | None => false end)
                      && Z.leb 2 (ealign k out) && Z.leb 2 (ealign k q)))
              && stk_ok k sp (- lt_dframe T) (lt_dframe T)
              && stk_ok k out 0 (4 * mx) && stk_ok k q 0 4
              && lin_ge0 k [(out, 0)] [(sp, 0)] && lin_ge0 k [(q, 0)] [(sp, 0)])%bool
          then
            let k1 := hav k sp (- lt_dframe T) (lt_dframe T) in
            let k2 := hav k1 out 0 (4 * mx) in
            let k3 := hav k2 q 0 4 in
            after_call nx0 cs ret None k3
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition cell8 (k : list kentry) (e : expr) (off : Z) : option expr :=
  let '(b, o) := split_lit e in kread8e segs k b (o + off).
Definition cell8_is (k : list kentry) (e : expr) (off : Z) (z : Z) : bool :=
  match cell8 k e off with Some (ELit v) => Z.eqb (v mod two64) z | _ => false end.

(* [comment removed for export] *)
Definition cell1 (k : list kentry) (b : expr) (o : Z) : option expr :=
  match know_lookup segs k b o 1 false [] [] with LHit v [] _ => Some v | _ => None end.
Fixpoint even_expr (e : expr) : bool :=
  match e with
  | ELit z => Z.even z
  | EAlu ALU_AND a b => even_expr a || even_expr b
  | EExt false O (S _) a => even_expr a
  | _ => false
  end.

(* [comment removed for export] *)
Definition str_window (k : list kentry) (b len : expr) : option expr :=
  let '(bb, bo) := split_lit b in
  match List.find (fun K => match K with
                            | KWr (SA wb wk) wl => xinside k bb bo (eaddz len 1) wb wk wl && Z.leb 3 (ealign k (eadd (eaddz wb wk) wl))
                            | _ => false
                            end) k with
  | Some (KWr (SA wb wk) wl) => Some (esub (eadd (eaddz wb wk) wl) b)
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_a2uloop (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in
  match args with
  | [len] =>
      if (negb (Z.eqb (pc cs) (lt_loop T)) || Z.eqb (lt_loop T) 0)%bool then None else
      let S := reg cs 8 in let b := reg cs 19 in
      let '(Sb, So) := split_lit S in let '(bb, bo) := split_lit b in
      let '(nb, no) := split_lit (eadd b len) in
      match cell8 k S (-2216 + 8), cell8 k S (-2216 + 40), cell1 k Sb (So - 2216 + 48),
            kreadZ segs k nb no 1, str_window k b len, xlo k len, xhi k len with
      | Some out, Some sb, Some fl, Some 0, Some N, Some llo, Some lhi =>
          let '(ob, oo) := split_lit out in
          if (expr_eqb (reg cs 2) (eaddz S (-2240))
              && cell8_is k S (-2216) 0 && cell8_is k S (-2216 + 16) 0 && cell8_is k S (-2216 + 24) 0 && cell8_is k S (-2216 + 32) 16
              && even_expr fl
              && match xlo k sb with Some l => Z.leb 1 l | None => false end
              && Z.leb 0 llo && Z.ltb lhi (2 ^ 31)
              && expr_vars_lt (nxt cs) len
              && ovl_ok k b N
              && match xlo k b, xhi k b, xhi k N with Some l, Some h, Some hn => Z.leb 1 l && Z.ltb (h + hn) (2 ^ 63) | _, _, _ => false end
              && flat_x k nb no (ELit 1)
              && forallb (fun r => img_cov k (fst r) (snd r)) (lt_rodata T)
              && (Z.ltb 2240 (lt_ldepth T) && Z.ltb (lt_ldepth T) 65536) && (negb (lt_strict T) || Z.leb 3 (ealign k S))
              && stk_ok k S (- lt_ldepth T) (lt_ldepth T - 2216) && stk_ok k S (-2200) 16 && stk_ok k S (-2160) 2048
              && addr_in k S 0 0 (2 ^ 63 - 1)
              && stk_ok k out 0 16
              && lin_ge0 k [(out, 0)] [(S, 0)]
              && ranges_apart_x k bb bo N Sb (So - lt_ldepth T) (ELit (lt_ldepth T))
              && ranges_apart_x k bb bo N ob oo (ELit 16)
              && fresh_ok nx0 cs)%bool
          then
            let k1 := hav k S (- lt_ldepth T) (lt_ldepth T - 2216) in
            let k2 := hav k1 S (-2200) 16 in
            let k3 := hav k2 S (-2160) 2048 in
            let k4 := hav k3 out 0 16 in
            let nx := nxt cs in
            let sr2 := sr_fresh (s_regs (a_ss cs)) loop_havoc nx in
            if kn_vars_lt nx k4 then Some (with_ss cs (mk_ss (lt_loop_exit T) sr2 k4 (nx + NLH))) else None
          else None
      | _, _, _, _, _, _, _ => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_unkintro (cs : acs) (args : list expr) : option acs :=
  match args with
  | [e; ELit n] =>
      let k := kn cs in
      let '(b, o) := split_lit e in
      if (Z.ltb 0 n && Z.leb n 4096 && expr_vars_lt (nxt cs) e && kwritable_x k k b o (ELit n) && off_image_x A k b o (ELit n))%bool
      then Some (add_kn cs [KUnk (SA b o) (ELit n)]) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 40%nat => node_decode cs
  | 41%nat => node_a2uloop cs args
  | 42%nat => node_unkintro cs args
  | _ => None
  end.

End WithSegs.
End LBN.
