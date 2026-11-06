(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool PrimString Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanLit AsanLitCodec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint pos_of_int (fuel : nat) (i : int) : positive :=
  match fuel with
  | O => xH
  | S f => if (i =? 1)%uint63 then xH else if (Uint63.land i 1 =? 0)%uint63 then xO (pos_of_int f (Uint63.lsr i 1)) else xI (pos_of_int f (Uint63.lsr i 1))
  end.
Definition z_of_int (i : int) : Z := if (i =? 0)%uint63 then Z0 else Zpos (pos_of_int 63 i).
Definition tok_fin (hi : option Z) (cur nd : int) (neg any : bool) (racc : tok) : tok :=
  if any then
    let v := match hi with Some h => h * Z.pow 10 (z_of_int nd) + z_of_int cur | None => z_of_int cur end in
    (if neg then - v else v) :: racc
  else racc.
Fixpoint toks_loop2 (fuel : nat) (s : string) (i : int) (hi : option Z) (cur nd : int) (neg any : bool) (racc : tok) : tok :=
  match fuel with
  | O => List.rev' (tok_fin hi cur nd neg any racc)
  | S fu =>
      let c := PrimString.get s i in
      if (c =? 32)%uint63 then toks_loop2 fu s (i + 1)%uint63 None 0%uint63 0%uint63 false false (tok_fin hi cur nd neg any racc)
      else if (c =? 45)%uint63 then toks_loop2 fu s (i + 1)%uint63 hi cur nd true any racc
      else
        let d := (c - 48)%uint63 in
        if (nd =? 18)%uint63 then
          let h := match hi with Some h => h * P18 + z_of_int cur | None => z_of_int cur end in
          toks_loop2 fu s (i + 1)%uint63 (Some h) d 1%uint63 neg true racc
        else toks_loop2 fu s (i + 1)%uint63 hi (cur * 10 + d)%uint63 (nd + 1)%uint63 neg true racc
  end.
Definition toks_of_str2 (s : string) : tok :=
  toks_loop2 (Z.to_nat (Uint63.to_Z (PrimString.length s))) s 0%uint63 None 0%uint63 0%uint63 false false [].
Definition lit_dec2 (s : string) : lit := match des_lit (toks_of_str2 s) with Some (x, []) => x | _ => lit0 end.

(* [comment removed for export] *)
Fixpoint put_ks2 (bs : list Z) (k : positive) (t : tree bval) : tree bval :=
  match bs with [] => t | b :: r => put_ks2 r (Pos.succ k) (tset k (BK b) t) end.
Fixpoint put_w2 (n : nat) (w : Z) (k : positive) (t : tree bval) : tree bval :=
  match n with O => t | S n' => put_w2 n' (Z.shiftr w 8) (Pos.succ k) (tset k (BK (Z.land w 255)) t) end.
Fixpoint put_ws2 (ws : list Z) (k : positive) (t : tree bval) : tree bval * positive :=
  match ws with [] => (t, k) | w :: r => put_ws2 r (Pos.add k 8) (put_w2 8 w k t) end.
Fixpoint put_vs2 (n : nat) (l : lin) (j : Z) (k : positive) (t : tree bval) : tree bval :=
  match n with O => t | S n' => put_vs2 n' l (j + 1) (Pos.succ k) (tset k (BV l j) t) end.
Definition dec_item2 (t : tree bval) (i : item) : tree bval :=
  match i with
  | IK o ws tl => let '(t1, k1) := put_ws2 ws (okey o) t in put_ks2 tl k1 t1
  | IV o l j n => put_vs2 (Z.to_nat n) l j (okey o) t
  end.
Definition dec_cont2 (is : list item) : tree bval := List.fold_left dec_item2 is TEmpty.
Definition dec_rg2 (e : erg) : region := let '(b, z, k, is) := e in RG b z k (dec_cont2 is).
Definition dec_st2 (e : est) : sst :=
  let '(pc, regs, rgs, fs, nx, rv) := e in
  SST pc (List.fold_left (fun t '(k, v) => tset k v t) regs TEmpty) (List.map dec_rg2 rgs) fs nx rv.
(* [comment removed for export] *)
