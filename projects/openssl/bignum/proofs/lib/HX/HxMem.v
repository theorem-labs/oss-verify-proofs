(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie AxFetchFast.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxVal HxBytes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Inductive cell : Type :=
| CW (w : w64) (km : int)
| CP (t : int) (o : w64).

Inductive rdflt : Type :=
| DUnk
| DZero
| DImage (i : nat) (d : int).

Record region : Type := RG {
  rg_abs : option int;
  rg_size : int;
  rg_al : int;
  rg_wr : bool;
  rg_dflt : rdflt;
  rg_d : nat;
  rg_cells : itrie cell
}.

Definition TAGD : nat := 20.
Definition TAGLIM : int := 1048576.

Definition mem := itrie region.

Definition mget (M : mem) (t : int) : option region :=
  if (t <? TAGLIM)%uint63 then iget TAGD M t else None.

Definition mset (M : mem) (t : int) (rg : region) : mem := iset TAGD M t rg.

Definition ctx_of (M : mem) : vctx := fun t =>
  match mget M t with
  | Some rg => match rg_abs rg with
               | None => if (rg_al rg =? 0)%uint63 then None else Some (rg_al rg, rg_size rg)
               | Some _ => None
               end
  | None => None
  end.

Definition byte_mask (n : int) : int := ((1 << n) - 1)%uint63.

Definition known (km j n : int) : bool := let m := byte_mask n in (((km >> j) land m) =? m)%uint63.

Definition img_byte (segs : list Segment) (i : nat) (x : int) : option int :=
  match nth_error segs i with
  | Some sg => match seg_bytes sg with [c] => hbyte c (x << 1)%uint63 | _ => None end
  | None => None
  end.

Definition img_cell (segs : list Segment) (i : nat) (x : int) : cell :=
  match img_byte segs i x, img_byte segs i (x + 1)%uint63, img_byte segs i (x + 2)%uint63, img_byte segs i (x + 3)%uint63,
        img_byte segs i (x + 4)%uint63, img_byte segs i (x + 5)%uint63, img_byte segs i (x + 6)%uint63, img_byte segs i (x + 7)%uint63 with
  | Some b0, Some b1, Some b2, Some b3, Some b4, Some b5, Some b6, Some b7 =>
      CW (W (128 <=? b7)%uint63
            (b0 lor (b1 << 8) lor (b2 << 16) lor (b3 << 24) lor (b4 << 32) lor (b5 << 40) lor (b6 << 48) lor ((b7 land 127) << 56))%uint63)
         255
  | _, _, _, _, _, _, _, _ => CW w_zero 0
  end.

Definition dflt_cell (segs : list Segment) (d : rdflt) (k : int) : cell :=
  match d with
  | DUnk => CW w_zero 0
  | DZero => CW w_zero 255
  | DImage i dl => img_cell segs i (dl + (k << 3))%uint63
  end.

Definition rd_cell (segs : list Segment) (rg : region) (k : int) : cell :=
  match iget (rg_d rg) (rg_cells rg) k with
  | Some c => c
  | None => dflt_cell segs (rg_dflt rg) k
  end.

Definition wr_cell (rg : region) (k : int) (c : cell) : region :=
  RG (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) (rg_dflt rg) (rg_d rg) (iset (rg_d rg) (rg_cells rg) k c).

Definition forget (c : cell) (j n : int) : cell :=
  match c with
  | CW w km => CW w (km land (255 lxor (byte_mask n << j)))%uint63
  | CP _ _ => CW w_zero 0
  end.

Definition abstab := list (int * int * int).

Fixpoint abs_find (l : abstab) (a n : int) : option (int * int) :=
  match l with
  | [] => None
  | (lo, hi, t) :: r =>
      if ((lo <=? a) && (a <=? hi) && (a + n <=? hi))%uint63 then Some (t, (a - lo)%uint63) else abs_find r a n
  end.

Definition in_rg (off n size : int) : bool := ((off <=? size) && (off + n <=? size))%uint63.

Definition resolve (M : mem) (abs : abstab) (a : hval) (n : int) : option (int * region * int) :=
  match a with
  | VP t o =>
      if wh o then None else
      match mget M t with
      | Some rg =>
          match rg_abs rg with
          | None => if in_rg (wl o) n (rg_size rg) then Some (t, rg, wl o) else None
          | Some _ => None
          end
      | None => None
      end
  | VC w =>
      if wh w then None else
      match abs_find abs (wl w) n with
      | Some (t, off) =>
          match mget M t with
          | Some rg =>
              match rg_abs rg with
              | Some lo => if in_rg off n (rg_size rg) && (lo + off =? wl w)%uint63 then Some (t, rg, off) else None
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | VU | VN _ _ => None
  end.

Definition nbytes (sz : msize) : int := match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end%uint63.

Definition ext_val (sz : msize) (sg : bool) (x : w64) : w64 :=
  match sz with
  | SZ8 => x
  | _ => if sg then w_sextn (nbytes sz) x else x
  end.

Definition hx_load (segs : list Segment) (M : mem) (abs : abstab) (a : hval) (sz : msize) (sg : bool) : option hval :=
  let n := nbytes sz in
  match resolve M abs a n with
  | None => None
  | Some (_, rg, off) =>
      let k := (off >> 3)%uint63 in
      let j := (off land 7)%uint63 in
      if (j + n <=? 8)%uint63 then
        match rd_cell segs rg k with
        | CW w km =>
            if known km j n then Some (VC (match sz with SZ8 => w | _ => ext_val sz sg (w_ext w j n) end)) else Some VU
        | CP t' o' => match sz with SZ8 => Some (VP t' o') | _ => Some VU end
        end
      else Some VU
  end.

Definition store_cell (c : cell) (j n : int) (sz : msize) (v : hval) : cell :=
  match v with
  | VC x =>
      match sz with
      | SZ8 => CW x 255
      | _ => match c with
             | CW w km => CW (w_ins w j n x) (km lor (byte_mask n << j))%uint63
             | CP _ _ => CW (w_ins w_zero j n x) (byte_mask n << j)%uint63
             end
      end
  | VP t o => match sz with SZ8 => CP t o | _ => forget c j n end
  | VU | VN _ _ => forget c j n
  end.

Definition hx_store (segs : list Segment) (M : mem) (abs : abstab) (a : hval) (sz : msize) (v : hval) : option mem :=
  let n := nbytes sz in
  match resolve M abs a n with
  | None => None
  | Some (t, rg, off) =>
      if rg_wr rg then
        let k := (off >> 3)%uint63 in
        let j := (off land 7)%uint63 in
        if (j + n <=? 8)%uint63 then
          Some (mset M t (wr_cell rg k (store_cell (rd_cell segs rg k) j n sz v)))
        else None
      else None
  end.
