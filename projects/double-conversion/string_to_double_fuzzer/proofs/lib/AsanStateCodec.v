(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint sc_hex (f : nat) (s : string) (i acc : int) : int * int :=
  match f with
  | O => (acc, i)
  | S f' =>
      let d := PrimInt63.sub (PrimString.get s i) 48%uint63 in
      if PrimInt63.ltb d 16%uint63
      then sc_hex f' s (PrimInt63.add i 1%uint63) (PrimInt63.lor (PrimInt63.lsl acc 4%uint63) d)
      else (acc, i)
  end.

Fixpoint sc_pos (f : nat) (x : int) : positive :=
  match f with
  | O => xH
  | S f' =>
      if PrimInt63.leb x 1%uint63 then xH
      else if PrimInt63.eqb (PrimInt63.land x 1%uint63) 0%uint63 then xO (sc_pos f' (PrimInt63.lsr x 1%uint63))
      else xI (sc_pos f' (PrimInt63.lsr x 1%uint63))
  end.
Definition sc_Zp (x : int) : Z := if PrimInt63.eqb x 0%uint63 then Z0 else Zpos (sc_pos 63 x).
Definition sc_Zn (x : int) : Z := if PrimInt63.eqb x 0%uint63 then Z0 else Zneg (sc_pos 63 x).

Fixpoint sc_nat (f : nat) (x : int) : nat :=
  match f with
  | O => O
  | S f' =>
      if PrimInt63.eqb x 0%uint63 then O
      else let h := sc_nat f' (PrimInt63.lsr x 1%uint63) in
           if PrimInt63.eqb (PrimInt63.land x 1%uint63) 0%uint63 then Nat.add h h else S (Nat.add h h)
  end.

Definition sc_Zsmall (s : string) (i : int) : Z * int :=
  let c := PrimString.get s i in
  let '(v, j) := sc_hex 16 s (PrimInt63.add i 1%uint63) 0%uint63 in
  if PrimInt63.eqb c 45%uint63 then (sc_Zn v, j) else (sc_Zp v, j).

Definition sc_Z (s : string) (i : int) : Z * int :=
  if PrimInt63.eqb (PrimString.get s i) 94%uint63 then
    let '(hi, j) := sc_Zsmall s (PrimInt63.add i 1%uint63) in
    let '(lo, k) := sc_Zsmall s j in
    (Z.add (Z.shiftl hi 60) lo, k)
  else sc_Zsmall s i.

Definition sc_N (s : string) (i : int) : nat * int :=
  let '(v, j) := sc_hex 16 s (PrimInt63.add i 1%uint63) 0%uint63 in (sc_nat 63 v, j).

Definition sc_aluop (k : int) : aluop :=
  if PrimInt63.eqb k 0%uint63 then ALU_ADD else if PrimInt63.eqb k 1%uint63 then ALU_SUB
  else if PrimInt63.eqb k 2%uint63 then ALU_SLL else if PrimInt63.eqb k 3%uint63 then ALU_SLT
  else if PrimInt63.eqb k 4%uint63 then ALU_SLTU else if PrimInt63.eqb k 5%uint63 then ALU_XOR
  else if PrimInt63.eqb k 6%uint63 then ALU_SRL else if PrimInt63.eqb k 7%uint63 then ALU_SRA
  else if PrimInt63.eqb k 8%uint63 then ALU_OR else ALU_AND.
Definition sc_mulop (k : int) : mulop :=
  if PrimInt63.eqb k 0%uint63 then M_MUL else if PrimInt63.eqb k 1%uint63 then M_MULH
  else if PrimInt63.eqb k 2%uint63 then M_MULHSU else if PrimInt63.eqb k 3%uint63 then M_MULHU
  else if PrimInt63.eqb k 4%uint63 then M_DIV else if PrimInt63.eqb k 5%uint63 then M_DIVU
  else if PrimInt63.eqb k 6%uint63 then M_REM else M_REMU.

(* [comment removed for export] *)
Fixpoint sc_list {A : Type} (rd : string -> int -> A * int) (n : nat) (s : string) (i : int) : list A * int :=
  match n with
  | O => (nil, i)
  | S n' => let '(x, j) := rd s i in let '(l, k) := sc_list rd n' s j in (x :: l, k)
  end.
Definition sc_listN {A : Type} (rd : string -> int -> A * int) (s : string) (i : int) : list A * int :=
  let '(n, j) := sc_N s i in sc_list rd n s j.

(* [comment removed for export] *)
Fixpoint sc_expr (f : nat) (s : string) (i : int) : expr * int :=
  match f with
  | O => (ELit 0, i)
  | S f' =>
      let c := PrimString.get s i in
      let i1 := PrimInt63.add i 1%uint63 in
      if PrimInt63.eqb c 35%uint63 then let '(v, j) := sc_hex 16 s i1 0%uint63 in (ELit (sc_Zp v), j)
      else if PrimInt63.eqb c 36%uint63 then let '(v, j) := sc_hex 16 s i1 0%uint63 in (EVar (sc_nat 63 v), j)
      else if PrimInt63.eqb c 43%uint63 then
        let '(a, j) := sc_expr f' s i1 in let '(b, k) := sc_expr f' s j in (EAlu ALU_ADD a b, k)
      else if PrimInt63.eqb c 64%uint63 then
        let '(a, j) := sc_expr f' s i1 in let '(b, k) := sc_expr f' s j in (EMd M_MUL a b, k)
      else if PrimInt63.eqb c 45%uint63 then let '(v, j) := sc_hex 16 s i1 0%uint63 in (ELit (sc_Zn v), j)
      else if PrimInt63.eqb c 38%uint63 then
        let op := sc_aluop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := sc_expr f' s (PrimInt63.add i 2%uint63) in let '(b, k) := sc_expr f' s j in (EAlu op a b, k)
      else if PrimInt63.eqb c 37%uint63 then
        let op := sc_aluop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := sc_expr f' s (PrimInt63.add i 2%uint63) in let '(b, k) := sc_expr f' s j in (EAluw op a b, k)
      else if PrimInt63.eqb c 47%uint63 then
        let op := sc_mulop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := sc_expr f' s (PrimInt63.add i 2%uint63) in let '(b, k) := sc_expr f' s j in (EMd op a b, k)
      else if PrimInt63.eqb c 124%uint63 then
        let op := sc_mulop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := sc_expr f' s (PrimInt63.add i 2%uint63) in let '(b, k) := sc_expr f' s j in (EMdw op a b, k)
      else if PrimInt63.eqb c 91%uint63 then
        let '(lo, j) := sc_N s i1 in let '(n, k) := sc_N s j in let '(e, l) := sc_expr f' s k in (EExt false lo n e, l)
      else if PrimInt63.eqb c 93%uint63 then
        let '(lo, j) := sc_N s i1 in let '(n, k) := sc_N s j in let '(e, l) := sc_expr f' s k in (EExt true lo n e, l)
      else if PrimInt63.eqb c 123%uint63 then
        let '(b, j) := sc_N s i1 in let '(z, k) := sc_Z s j in let '(n, l) := sc_N s k in (EBlob false b z n, l)
      else if PrimInt63.eqb c 125%uint63 then
        let '(b, j) := sc_N s i1 in let '(z, k) := sc_Z s j in let '(n, l) := sc_N s k in (EBlob true b z n, l)
      else if PrimInt63.eqb c 94%uint63 then let '(z, j) := sc_Z s i in (ELit z, j)
      else (ELit 0, i1)
  end.
Definition sc_E (s : string) (i : int) : expr * int := sc_expr 200 s i.

Definition sc_saddr (s : string) (i : int) : saddr * int :=
  let '(b, j) := sc_E s i in let '(o, k) := sc_Z s j in (SA b o, k).
Definition sc_sentry (s : string) (i : int) : sentry * int :=
  let '(a, j) := sc_saddr s i in let '(w, k) := sc_N s j in let '(v, l) := sc_E s k in (SE a w v, l).
Definition sc_pair_se (s : string) (i : int) : (saddr * expr) * int :=
  let '(a, j) := sc_saddr s i in let '(e, k) := sc_E s j in ((a, e), k).
Definition sc_pair_ee (s : string) (i : int) : (expr * expr) * int :=
  let '(a, j) := sc_E s i in let '(e, k) := sc_E s j in ((a, e), k).

Definition sc_kentry (s : string) (i : int) : kentry * int :=
  let c := PrimString.get s i in
  let i1 := PrimInt63.add i 1%uint63 in
  if PrimInt63.eqb c 33%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(w, k) := sc_N s j in let '(v, l) := sc_E s k in (KWord a w v, l)
  else if PrimInt63.eqb c 37%uint63 then
    let '(lo, j) := sc_Z s i1 in let '(hi, k) := sc_Z s j in (KImg lo hi, k)
  else if PrimInt63.eqb c 39%uint63 then
    let '(e, j) := sc_E s i1 in let '(lo, k) := sc_Z s j in let '(hi, l) := sc_Z s k in (KRange e lo hi, l)
  else if PrimInt63.eqb c 35%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(n, k) := sc_E s j in (KZero a n, k)
  else if PrimInt63.eqb c 36%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(n, k) := sc_E s j in let '(b, l) := sc_N s k in (KBlob a n b, l)
  else if PrimInt63.eqb c 38%uint63 then
    let '(e, j) := sc_E s i1 in let '(m, k) := sc_Z s j in (KAlign e m, k)
  else if PrimInt63.eqb c 40%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(n, k) := sc_E s j in (KWr a n, k)
  else if PrimInt63.eqb c 41%uint63 then
    let '(a1, j) := sc_saddr s i1 in let '(n1, k) := sc_E s j in
    let '(a2, l) := sc_saddr s k in let '(n2, m) := sc_E s l in (KDisj a1 n1 a2 n2, m)
  else if PrimInt63.eqb c 43%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(n, k) := sc_E s j in let '(z, l) := sc_Z s k in (KFill a n z, l)
  else if PrimInt63.eqb c 44%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(n, k) := sc_E s j in (KUnk a n, k)
  else (KImg 0 0, i1).

Definition sc_osaddr (s : string) (i : int) : option saddr * int :=
  if PrimInt63.eqb (PrimString.get s i) 35%uint63
  then let '(a, j) := sc_saddr s (PrimInt63.add i 1%uint63) in (Some a, j)
  else (None, PrimInt63.add i 1%uint63).

Definition sc_sstate (s : string) (i : int) : sym_state * int :=
  let '(p, i1) := sc_Z s i in
  let '(rg, i2) := sc_listN sc_E s i1 in
  let '(lg, i3) := sc_listN sc_sentry s i2 in
  let '(kn, i4) := sc_listN sc_kentry s i3 in
  let '(nx, i5) := sc_N s i4 in
  let '(rv, i6) := sc_osaddr s i5 in
  (SSR p rg lg kn nx rv, i6).

Definition sc_mkind (c : int) : mkind :=
  if PrimInt63.eqb c 33%uint63 then KRW else if PrimInt63.eqb c 35%uint63 then KRWLAZY
  else if PrimInt63.eqb c 36%uint63 then KNONE else if PrimInt63.eqb c 37%uint63 then KNONELAZY
  else if PrimInt63.eqb c 38%uint63 then KFOG else KHOLE.
Definition sc_amap (s : string) (i : int) : amap * int :=
  let '(b, j) := sc_E s i in let '(n, k) := sc_E s j in (AM b n (sc_mkind (PrimString.get s k)), PrimInt63.add k 1%uint63).

Definition sc_afd (s : string) (i : int) : afd * int :=
  let c := PrimString.get s i in
  let i1 := PrimInt63.add i 1%uint63 in
  if PrimInt63.eqb c 35%uint63 then
    let '(b, j) := sc_N s i1 in let '(n, k) := sc_E s j in let '(o, l) := sc_E s k in (FdFile b n o, l)
  else if PrimInt63.eqb c 36%uint63 then (FdDir, i1) else (FdStd, i1).

(* [comment removed for export] *)
Definition dec_acs (s : string) : acs :=
  let '(ss, i1) := sc_sstate s 0%uint63 in
  let '(mp, i2) := sc_listN sc_amap s i1 in
  let '(tot, i3) := sc_Z s i2 in
  let '(ylo, i4) := sc_Z s i3 in
  let '(eag, i5) := sc_Z s i4 in
  let '(vis, i6) := sc_listN sc_pair_ee s i5 in
  let '(gho, i7) := sc_listN sc_pair_ee s i6 in
  let '(aby, i8) := sc_Z s i7 in
  let '(brk, i9) := sc_E s i8 in
  let '(fd, i10) := sc_afd s i9 in
  ACS ss mp tot ylo eag vis gho aby brk fd (PrimInt63.eqb (PrimString.get s i10) 35%uint63).

(* [comment removed for export] *)
Definition ec (n : Z) : int := Uint63.of_Z n.
Fixpoint en_hex (fuel : nat) (z : Z) (acc : list int) : list int :=
  match fuel with
  | O => acc
  | S f => if Z.eqb z 0 then acc else en_hex f (Z.shiftr z 4) (PrimInt63.add 48%uint63 (ec (Z.land z 15)) :: acc)
  end.
Definition en_Zsmall (z : Z) (acc : list int) : list int :=
  if Z.ltb z 0 then 45%uint63 :: en_hex 20 (Z.opp z) acc else 35%uint63 :: en_hex 20 z acc.
Definition en_Z (z : Z) (acc : list int) : list int :=
  let m := Z.abs z in
  if Z.ltb m (2 ^ 60) then en_Zsmall z acc
  else let hi := Z.shiftr m 60 in let lo := Z.land m (2 ^ 60 - 1) in
       if Z.ltb z 0 then 94%uint63 :: en_Zsmall (Z.opp hi) (en_Zsmall (Z.opp lo) acc)
       else 94%uint63 :: en_Zsmall hi (en_Zsmall lo acc).
Definition en_N (n : nat) (acc : list int) : list int := 44%uint63 :: en_hex 20 (Z.of_nat n) acc.
Definition en_aluop (o : aluop) : int :=
  match o with ALU_ADD => 48 | ALU_SUB => 49 | ALU_SLL => 50 | ALU_SLT => 51 | ALU_SLTU => 52 | ALU_XOR => 53
             | ALU_SRL => 54 | ALU_SRA => 55 | ALU_OR => 56 | ALU_AND => 57 end%uint63.
Definition en_mulop (o : mulop) : int :=
  match o with M_MUL => 48 | M_MULH => 49 | M_MULHSU => 50 | M_MULHU => 51 | M_DIV => 52 | M_DIVU => 53 | M_REM => 54 | M_REMU => 55 end%uint63.
Fixpoint en_list {A : Type} (en : A -> list int -> list int) (l : list A) (acc : list int) : list int :=
  match l with nil => acc | x :: r => en x (en_list en r acc) end.
Definition en_listN {A : Type} (en : A -> list int -> list int) (l : list A) (acc : list int) : list int :=
  en_N (List.length l) (en_list en l acc).
Fixpoint en_expr (e : expr) (acc : list int) : list int :=
  match e with
  | ELit z => if Z.ltb (Z.abs z) (2 ^ 60) then en_Zsmall z acc else en_Z z acc
  | EVar v => 36%uint63 :: en_hex 20 (Z.of_nat v) acc
  | EAlu ALU_ADD a b => 43%uint63 :: en_expr a (en_expr b acc)
  | EMd M_MUL a b => 64%uint63 :: en_expr a (en_expr b acc)
  | EAlu op a b => 38%uint63 :: en_aluop op :: en_expr a (en_expr b acc)
  | EAluw op a b => 37%uint63 :: en_aluop op :: en_expr a (en_expr b acc)
  | EMd op a b => 47%uint63 :: en_mulop op :: en_expr a (en_expr b acc)
  | EMdw op a b => 124%uint63 :: en_mulop op :: en_expr a (en_expr b acc)
  | EExt false lo n x => 91%uint63 :: en_N lo (en_N n (en_expr x acc))
  | EExt true lo n x => 93%uint63 :: en_N lo (en_N n (en_expr x acc))
  | EBlob false b z n => 123%uint63 :: en_N b (en_Z z (en_N n acc))
  | EBlob true b z n => 125%uint63 :: en_N b (en_Z z (en_N n acc))
  end.
Definition en_saddr (a : saddr) (acc : list int) : list int := en_expr (a_base a) (en_Z (a_off a) acc).
Definition en_sentry (x : sentry) (acc : list int) : list int :=
  match x with SE a w v => en_saddr a (en_N w (en_expr v acc)) end.
Definition en_pair_ee (p : expr * expr) (acc : list int) : list int := en_expr (fst p) (en_expr (snd p) acc).
Definition en_kentry (K : kentry) (acc : list int) : list int :=
  match K with
  | KWord a w v => 33%uint63 :: en_saddr a (en_N w (en_expr v acc))
  | KZero a n => 35%uint63 :: en_saddr a (en_expr n acc)
  | KBlob a n b => 36%uint63 :: en_saddr a (en_expr n (en_N b acc))
  | KImg lo hi => 37%uint63 :: en_Z lo (en_Z hi acc)
  | KAlign e m => 38%uint63 :: en_expr e (en_Z m acc)
  | KRange e lo hi => 39%uint63 :: en_expr e (en_Z lo (en_Z hi acc))
  | KWr a n => 40%uint63 :: en_saddr a (en_expr n acc)
  | KDisj a1 n1 a2 n2 => 41%uint63 :: en_saddr a1 (en_expr n1 (en_saddr a2 (en_expr n2 acc)))
  | KFill a n z => 43%uint63 :: en_saddr a (en_expr n (en_Z z acc))
  | KUnk a n => 44%uint63 :: en_saddr a (en_expr n acc)
  end.
Definition en_osaddr (o : option saddr) (acc : list int) : list int :=
  match o with Some a => 35%uint63 :: en_saddr a acc | None => 33%uint63 :: acc end.
Definition en_sstate (ss : sym_state) (acc : list int) : list int :=
  en_Z (s_pc ss) (en_listN en_expr (s_regs ss) (en_listN en_sentry (s_log ss) (en_listN en_kentry (s_know ss)
    (en_N (s_next ss) (en_osaddr (s_resv ss) acc))))).
Definition en_mkind (k : mkind) : int :=
  match k with KRW => 33 | KRWLAZY => 35 | KNONE => 36 | KNONELAZY => 37 | KFOG => 38 | KHOLE => 39 end%uint63.
Definition en_amap (m : amap) (acc : list int) : list int := en_expr (am_base m) (en_expr (am_len m) (en_mkind (am_kind m) :: acc)).
Definition en_afd (f : afd) (acc : list int) : list int :=
  match f with FdStd => 33%uint63 :: acc | FdFile b n o => 35%uint63 :: en_N b (en_expr n (en_expr o acc)) | FdDir => 36%uint63 :: acc end.
Definition en_acs_chars (c : acs) : list int :=
  en_sstate (a_ss c) (en_listN en_amap (a_maps c) (en_Z (a_totsz c) (en_Z (a_ylo c) (en_Z (a_eager c)
    (en_listN en_pair_ee (a_vis c) (en_listN en_pair_ee (a_ghost c) (en_Z (a_abytes c) (en_expr (a_brk c)
      (en_afd (a_fd c) ((if a_tidset c then 35%uint63 else 33%uint63) :: nil)))))))))).
(* [comment removed for export] *)
Fixpoint cat_pairs (l : list string) : list string :=
  match l with a :: b :: r => PrimString.cat a b :: cat_pairs r | _ => l end.
Fixpoint cat_all (fuel : nat) (l : list string) : string :=
  match fuel with
  | O => ""%pstring
  | S f => match l with nil => ""%pstring | a :: nil => a | _ => cat_all f (cat_pairs l) end
  end.
Definition str_of_chars (l : list int) : string := cat_all 64 (List.map (fun c => PrimString.make 1%uint63 c) l).
Definition enc_acs (c : acs) : string := str_of_chars (en_acs_chars c).
(* [comment removed for export] *)
Definition acs_same (a b : acs) : bool := match PrimString.compare (enc_acs a) (enc_acs b) with Eq => true | _ => false end.
