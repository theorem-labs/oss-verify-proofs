(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63 PrimString.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec.
Import ListNotations.
Open Scope Z_scope.
Inductive zx : Type :=
| ZV (n : nat) | ZL (z : Z) | ZR (k : nat)
| ZAdd (a b : zx) | ZSub (a b : zx) | ZMul (a b : zx) | ZDiv (a b : zx) | ZMod (a b : zx) | ZPow (a b : zx)
| ZLand (a b : zx) | ZLor (a b : zx) | ZLxor (a b : zx)
| ZLtbIf (a b : zx) | ZDivu (a b : zx) | ZRemu (a b : zx).
Inductive msel := MM0 | MM1.
Inductive px : Type :=
| PLeLt (a b c : zx)
| PLeLe (a b c : zx) | PLt (a b : zx) | PLe (a b : zx) | PEqZ (a b : zx)
| PTestbit (a : zx) (k : Z) (b : bool)
| PSrl (a m lo hi : zx) | PAligned (a : zx) (k : zx)
| PWr (a n : zx) | PDef (m : msel) (a n : zx) | PZero (m : msel) (a n : zx)
| PU64 (m : msel) (a v : zx) | PU32 (m : msel) (a v : zx) | PU8 (m : msel) (a v : zx)
| PImg (lo hi : zx)
| PDisj (a1 n1 a2 n2 : zx)
| PAnd (p q : px) | PTrue
| PG (k : nat) (p : zx)
| PG' (k : nat) (p : zx)
| PGR (k j : nat)
| PUns' (k : nat) (v : zx)
| PSteps (pc pc' : Z)
| PKept (e : nat).
Record stmt := ST { s_hyps : list px; s_frames : list (zx * zx); s_exits : list (list px) }.
Section Den.
Variable segs : list Segment.
Variable aligned : Z -> Z -> Prop.
Variable srl_range : Z -> Z -> Z -> Z -> Prop.
Variable zeros_at : (word -> option byte) -> Z -> Z -> Prop.
Variable ks : list (list nat).
Variable fx : FPState.
Variable R : bvmap 5 (bv 64).
Variable M : word -> option byte.
Variable V : nat -> Z.
Fixpoint dz (e : zx) : Z :=
match e with
| ZV n => V n
| ZL z => z
| ZR k => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat k)))
| ZAdd a b => dz a + dz b
| ZSub a b => dz a - dz b
| ZMul a b => dz a * dz b
| ZDiv a b => dz a / dz b
| ZMod a b => dz a mod dz b
| ZPow a b => dz a ^ dz b
| ZLand a b => Z.land (dz a) (dz b)
| ZLor a b => Z.lor (dz a) (dz b)
| ZLxor a b => Z.lxor (dz a) (dz b)
| ZLtbIf a b => if dz a <? dz b then 1 else 0
| ZDivu a b => if dz b =? 0 then 2 ^ 64 - 1 else dz a / dz b
| ZRemu a b => if dz b =? 0 then dz a else dz a mod dz b
end.
Definition msel_of (M' : word -> option byte) (m : msel) : word -> option byte := match m with MM0 => M | MM1 => M' end.
Fixpoint dp (fx' : FPState) (R' : bvmap 5 (bv 64)) (M' : word -> option byte) (p : px) : Prop :=
match p with
| PLeLt a b c => dz a <= dz b < dz c
| PLeLe a b c => dz a <= dz b <= dz c
| PLt a b => dz a < dz b
| PLe a b => dz a <= dz b
| PEqZ a b => dz a = dz b
| PTestbit a k b => Z.testbit (dz a) k = b
| PSrl a m lo hi => srl_range (dz a) (dz m) (dz lo) (dz hi)
| PAligned a k => aligned (dz a) (dz k)
| PWr a n => L5.writable segs M (dz a) (dz n)
| PDef m a n => L5.defined (msel_of M' m) (dz a) (dz n)
| PZero m a n => zeros_at (msel_of M' m) (dz a) (dz n)
| PU64 m a v => L5.u64_at segs (msel_of M' m) (dz a) (dz v)
| PU32 m a v => L5.u32_at segs (msel_of M' m) (dz a) (dz v)
| PU8 m a v => L5.u8_at segs (msel_of M' m) (dz a) (dz v)
| PImg lo hi => L5.img_clear M (dz lo) (dz hi)
| PDisj a1 n1 a2 n2 => (dz a1 + dz n1 <= dz a2 \/ dz a2 + dz n2 <= dz a1)
| PAnd p q => dp fx' R' M' p /\ dp fx' R' M' q
| PTrue => True
| PG k e => getr R (Z_to_bv 5 (Z.of_nat k)) = Z_to_bv 64 (dz e)
| PG' k e => getr R' (Z_to_bv 5 (Z.of_nat k)) = Z_to_bv 64 (dz e)
| PGR k j => getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat j))
| PUns' k v => bv_unsigned (getr R' (Z_to_bv 5 (Z.of_nat k))) = dz v
| PSteps pc pc' => msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom segs))
| PKept e => forall x, In x (nth e ks nil) -> getr R' (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))
end.
End Den.
Local Notation get := PrimString.get.
Local Notation inc i := (PrimInt63.add i 1%uint63).
Local Notation ceq c k := (PrimInt63.eqb c k%uint63).
Fixpoint pz (f : nat) (s : string) (i : int) : zx * int :=
match f with
| O => (ZL 0, i)
| S f' =>
let c := get s i in
let bin (k : zx -> zx -> zx) := let '(a, j) := pz f' s (inc i) in let '(b, l) := pz f' s j in (k a b, l) in
if ceq c 118 then let '(n, j) := SegCodec.sc_N s i in (ZV n, j)
else if ceq c 114 then let '(n, j) := SegCodec.sc_N s i in (ZR n, j)
else if ceq c 35 then let '(z, j) := SegCodec.sc_Z s i in (ZL z, j)
else if ceq c 45 then let '(z, j) := SegCodec.sc_Z s i in (ZL z, j)
else if ceq c 94 then let '(z, j) := SegCodec.sc_Z s i in (ZL z, j)
else if ceq c 43 then bin ZAdd else if ceq c 95 then bin ZSub else if ceq c 42 then bin ZMul
else if ceq c 47 then bin ZDiv else if ceq c 37 then bin ZMod else if ceq c 112 then bin ZPow
else if ceq c 38 then bin ZLand else if ceq c 124 then bin ZLor else if ceq c 120 then bin ZLxor
else if ceq c 99 then bin ZLtbIf else if ceq c 100 then bin ZDivu else if ceq c 109 then bin ZRemu
else (ZL 0, inc i)
end.
Definition pms (s : string) (i : int) : msel * int := (if ceq (get s i) 98 then MM1 else MM0, inc i).
Fixpoint pp (f : nat) (s : string) (i : int) : px * int :=
match f with
| O => (PTrue, i)
| S f' =>
let c := get s i in let i1 := inc i in
let z1 (k : zx -> px) := let '(a, j) := pz 200 s i1 in (k a, j) in
let z2 (k : zx -> zx -> px) := let '(a, j) := pz 200 s i1 in let '(b, l) := pz 200 s j in (k a b, l) in
let z3 (k : zx -> zx -> zx -> px) := let '(a, j) := pz 200 s i1 in let '(b, l) := pz 200 s j in let '(d, q) := pz 200 s l in (k a b d, q) in
let z4 (k : zx -> zx -> zx -> zx -> px) := let '(a, j) := pz 200 s i1 in let '(b, l) := pz 200 s j in let '(d, q) := pz 200 s l in
let '(e, r) := pz 200 s q in (k a b d e, r) in
let m2 (k : msel -> zx -> zx -> px) := let '(m, j0) := pms s i1 in let '(a, j) := pz 200 s j0 in let '(b, l) := pz 200 s j in (k m a b, l) in
if ceq c 65 then z3 PLeLt else if ceq c 66 then z3 PLeLe else if ceq c 67 then z2 PLt else if ceq c 68 then z2 PLe
else if ceq c 69 then z2 PEqZ
else if ceq c 70 then let '(a, j) := pz 200 s i1 in let '(k, l) := SegCodec.sc_Z s j in (PTestbit a k (ceq (get s l) 116), inc l)
else if ceq c 71 then z4 PSrl else if ceq c 72 then z2 PAligned else if ceq c 73 then z2 PWr
else if ceq c 74 then m2 PDef else if ceq c 75 then m2 PZero else if ceq c 76 then m2 PU64 else if ceq c 77 then m2 PU32
else if ceq c 78 then m2 PU8 else if ceq c 79 then z2 PImg else if ceq c 80 then z4 PDisj
else if ceq c 81 then let '(p, j) := pp f' s i1 in let '(q, l) := pp f' s j in (PAnd p q, l)
else if ceq c 82 then (PTrue, i1)
else if ceq c 83 then let '(k, j) := SegCodec.sc_N s i1 in let '(a, l) := pz 200 s j in (PG k a, l)
else if ceq c 84 then let '(k, j) := SegCodec.sc_N s i1 in let '(a, l) := pz 200 s j in (PG' k a, l)
else if ceq c 85 then let '(k, j) := SegCodec.sc_N s i1 in let '(m, l) := SegCodec.sc_N s j in (PGR k m, l)
else if ceq c 87 then let '(k, j) := SegCodec.sc_N s i1 in let '(a, l) := pz 200 s j in (PUns' k a, l)
else if ceq c 88 then let '(a, j) := SegCodec.sc_Z s i1 in let '(b, l) := SegCodec.sc_Z s j in (PSteps a b, l)
else if ceq c 89 then let '(k, j) := SegCodec.sc_N s i1 in (PKept k, j)
else (PTrue, i1)
end.
Definition ppx (s : string) (i : int) : px * int := pp 20 s i.
Definition pfr (s : string) (i : int) : (zx * zx) * int := let '(a, j) := pz 200 s i in let '(b, l) := pz 200 s j in ((a, b), l).
Definition pstmt (s : string) (i : int) : stmt * int :=
let '(h, j) := SegCodec.sc_listN ppx s i in
let '(fr, l) := SegCodec.sc_listN pfr s j in
let '(ex, q) := SegCodec.sc_listN (SegCodec.sc_listN ppx) s l in (ST h fr ex, q).
Definition dec (s : string) : stmt := fst (pstmt s 0%uint63).
Section DenS.
Variable segs : list Segment.
Variable aligned : Z -> Z -> Prop.
Variable srl_range : Z -> Z -> Z -> Z -> Prop.
Variable zeros_at : (word -> option byte) -> Z -> Z -> Prop.
Variable ks : list (list nat).
Variable fx : FPState.
Variable R : bvmap 5 (bv 64).
Variable M : word -> option byte.
Variable V : nat -> Z.
Fixpoint dhyps (hs : list px) (C : Prop) : Prop :=
match hs with [] => C | h :: t => dp segs aligned srl_range zeros_at ks fx R M V fx R M h -> dhyps t C end.
Fixpoint dparts (fx' : FPState) (R' : bvmap 5 (bv 64)) (M' : word -> option byte) (ps : list px) : Prop :=
match ps with [] => True | [p] => dp segs aligned srl_range zeros_at ks fx R M V fx' R' M' p
| p :: t => dp segs aligned srl_range zeros_at ks fx R M V fx' R' M' p /\ dparts fx' R' M' t end.
Fixpoint dexits (fx' : FPState) (R' : bvmap 5 (bv 64)) (M' : word -> option byte) (es : list (list px)) : Prop :=
match es with [] => False | [e0] => dparts fx' R' M' e0 | e0 :: t => dparts fx' R' M' e0 \/ dexits fx' R' M' t end.
Fixpoint dfa (a : word) (fr : list (zx * zx)) (C : Prop) : Prop :=
match fr with [] => C | (b, n) :: t => ~ (dz R V b <= bv_unsigned a < dz R V b + dz R V n) -> dfa a t C end.
Fixpoint dfi (i : Z) (fr : list (zx * zx)) (C : Prop) : Prop :=
match fr with [] => C | (b, n) :: t => ~ (dz R V b <= i < dz R V b + dz R V n) -> dfi i t C end.
Definition dstmt (s : stmt) : Prop :=
dhyps (s_hyps s)
(exists (fx' : FPState) (R' : bvmap 5 (bv 64)) (M' : word -> option byte), mem_grows M M'
/\ (forall a : word, dfa a (s_frames s) (M' a = M a))
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> dfi i (s_frames s) (M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)))
/\ dexits fx' R' M' (s_exits s)).
End DenS.
Ltac mk segs al sr za ks fx R M V str :=
let s := eval vm_compute in (dec str) in
let t := eval cbv beta iota delta [dstmt dhyps dparts dexits dfa dfi dp dz msel_of s_hyps s_frames s_exits nth] in
(dstmt segs al sr za ks fx R M V s) in
exact t.
Module StrNota. Export PrimString.PStringNotations. End StrNota.
Abbreviation RTY := (bvmap 5 (bv 64)).
Abbreviation MTY := (word -> option byte).
Abbreviation VTY := (nat -> Z).
