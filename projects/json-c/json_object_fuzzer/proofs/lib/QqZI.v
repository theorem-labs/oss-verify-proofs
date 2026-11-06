(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import PrimInt63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Module AXB.

Definition zc (c : int) : Z :=
(if PrimInt63.eqb (PrimInt63.land c 32) 0 then 0 else 32) +
(if PrimInt63.eqb (PrimInt63.land c 16) 0 then 0 else 16) +
(if PrimInt63.eqb (PrimInt63.land c 8) 0 then 0 else 8) +
(if PrimInt63.eqb (PrimInt63.land c 4) 0 then 0 else 4) +
(if PrimInt63.eqb (PrimInt63.land c 2) 0 then 0 else 2) +
(if PrimInt63.eqb (PrimInt63.land c 1) 0 then 0 else 1).

Definition unzz (n : Z) : Z := if Z.even n then Z.div2 n else Z.opp (Z.div2 (n + 1)).

Fixpoint z_of_int_bits (k : nat) (c : int) {struct k} : Z :=
match k with
| O => 0
| S k' => (if PrimInt63.eqb (PrimInt63.land c 1) 0 then 0 else 1) + 2 * z_of_int_bits k' (PrimInt63.lsr c 1)
end.
Definition z_of_int (c : int) : Z := z_of_int_bits 63 c.

Definition fuel_of (s : string) : nat := Z.to_nat (z_of_int (length s) + 1).

Section Dec.
Variable s : string.
Variable F : nat.

Fixpoint rd_num (i : int) (k : nat) {struct k} : Z * int :=
match k with
| O => (0, i)
| S k' =>
let c := get s i in
if PrimInt63.ltb c 81 then (zc (PrimInt63.sub c 35), PrimInt63.add i 1)
else let (r, j) := rd_num (PrimInt63.add i 1) k' in (zc (PrimInt63.sub c 81) + 46 * r, j)
end.

Definition rdN (i : int) : Z * int := rd_num i F.
Definition rdZ (i : int) : Z * int := let (n, j) := rd_num i F in (unzz n, j).
Definition rdnat (i : int) : nat * int := let (n, j) := rd_num i F in (Z.to_nat n, j).
Definition rdb (i : int) : bool * int := let (n, j) := rd_num i F in (Z.eqb n 1, j).

Fixpoint rd_listn {A : Type} (r : int -> A * int) (n : nat) (i : int) {struct n} : list A * int :=
match n with
| O => ([], i)
| S n' => let (x, j) := r i in let (xs, k) := rd_listn r n' j in (x :: xs, k)
end.
Definition rdlist {A : Type} (r : int -> A * int) (i : int) : list A * int :=
let (n, j) := rd_num i F in rd_listn r (Z.to_nat n) j.
Definition rdopt {A : Type} (r : int -> A * int) (i : int) : option A * int :=
let (n, j) := rd_num i F in if Z.eqb n 0 then (None, j) else let (x, k) := r j in (Some x, k).
Definition rdpair {A B : Type} (ra : int -> A * int) (rb : int -> B * int) (i : int) : (A * B) * int :=
let (a, j) := ra i in let (b, k) := rb j in ((a, b), k).

Definition aluop_of (n : Z) : aluop :=
match n with
| 0 => ALU_ADD | 1 => ALU_SUB | 2 => ALU_SLL | 3 => ALU_SLT | 4 => ALU_SLTU
| 5 => ALU_XOR | 6 => ALU_SRL | 7 => ALU_SRA | 8 => ALU_OR | _ => ALU_AND
end.
Definition mulop_of (n : Z) : mulop :=
match n with
| 0 => M_MUL | 1 => M_MULH | 2 => M_MULHSU | 3 => M_MULHU
| 4 => M_DIV | 5 => M_DIVU | 6 => M_REM | _ => M_REMU
end.
Definition mkind_of (n : Z) : mkind :=
match n with 0 => KRW | 1 => KRWLAZY | 2 => KNONE | 3 => KNONELAZY | 4 => KFOG | _ => KHOLE end.

Fixpoint rdexpr (f : nat) (i : int) {struct f} : expr * int :=
match f with
| O => (ELit 0, i)
| S f' =>
let (t, j) := rd_num i F in
match t with
| 0 => let (z, k) := rdZ j in (ELit z, k)
| 1 => let (n, k) := rdnat j in (EVar n, k)
| 2 => let (o, k) := rdN j in let (a, l) := rdexpr f' k in let (b, m) := rdexpr f' l in (EAlu (aluop_of o) a b, m)
| 3 => let (o, k) := rdN j in let (a, l) := rdexpr f' k in let (b, m) := rdexpr f' l in (EAluw (aluop_of o) a b, m)
| 4 => let (o, k) := rdN j in let (a, l) := rdexpr f' k in let (b, m) := rdexpr f' l in (EMd (mulop_of o) a b, m)
| 5 => let (o, k) := rdN j in let (a, l) := rdexpr f' k in let (b, m) := rdexpr f' l in (EMdw (mulop_of o) a b, m)
| 6 => let (sx, k) := rdb j in let (lo, l) := rdnat k in let (n, m) := rdnat l in let (e, p) := rdexpr f' m in (EExt sx lo n e, p)
| _ => let (sx, k) := rdb j in let (kk, l) := rdnat k in let (z, m) := rdZ l in let (n, p) := rdnat m in (EBlob sx kk z n, p)
end
end.

Definition rde : int -> expr * int := rdexpr F.
Definition rdsa (i : int) : saddr * int := let (b, j) := rde i in let (o, k) := rdZ j in (SA b o, k).

Definition rdke (i : int) : kentry * int :=
let (t, j) := rd_num i F in
match t with
| 0 => let (a, k) := rdsa j in let (w, l) := rdnat k in let (v, m) := rde l in (KWord a w v, m)
| 1 => let (a, k) := rdsa j in let (n, l) := rde k in (KZero a n, l)
| 2 => let (a, k) := rdsa j in let (n, l) := rde k in let (kk, m) := rdnat l in (KBlob a n kk, m)
| 3 => let (lo, k) := rdZ j in let (hi, l) := rdZ k in (KImg lo hi, l)
| 4 => let (e, k) := rde j in let (m, l) := rdZ k in (KAlign e m, l)
| 5 => let (e, k) := rde j in let (lo, l) := rdZ k in let (hi, m) := rdZ l in (KRange e lo hi, m)
| 6 => let (a, k) := rdsa j in let (n, l) := rde k in (KWr a n, l)
| 7 => let (a1, k) := rdsa j in let (n1, l) := rde k in let (a2, m) := rdsa l in let (n2, p) := rde m in (KDisj a1 n1 a2 n2, p)
| 8 => let (a, k) := rdsa j in let (n, l) := rde k in let (c, m) := rdZ l in (KFill a n c, m)
| _ => let (a, k) := rdsa j in let (n, l) := rde k in (KUnk a n, l)
end.

Definition rdse (i : int) : sentry * int :=
let (a, j) := rdsa i in let (w, k) := rdnat j in let (v, l) := rde k in (SE a w v, l).

Definition rdss (i : int) : sym_state * int :=
let (pc, j) := rdZ i in let (rs, k) := rdlist rde j in let (lg, l) := rdlist rdse k in
let (kn, m) := rdlist rdke l in let (nx, p) := rdnat m in let (rv, q) := rdopt rdsa p in (SSR pc rs lg kn nx rv, q).

Definition rdam (i : int) : amap * int :=
let (b, j) := rde i in let (ln, k) := rde j in let (kd, l) := rdN k in (AM b ln (mkind_of kd), l).

Definition rdfd (i : int) : afd * int :=
let (t, j) := rd_num i F in
match t with
| 0 => (FdStd, j)
| 1 => let (k, l) := rdnat j in let (ln, m) := rde l in let (off, p) := rde m in (FdFile k ln off, p)
| _ => (FdDir, j)
end.

Definition rdee : int -> (expr * expr) * int := rdpair rde rde.

Definition rdacs (i : int) : acs * int :=
let (ss, j) := rdss i in let (ms, k) := rdlist rdam j in let (tot, l) := rdZ k in let (ylo, m) := rdZ l in
let (eg, p) := rdZ m in let (vis, q) := rdlist rdee p in let (gh, r) := rdlist rdee q in let (ab, t) := rdZ r in
let (brk, u) := rde t in let (fd, w) := rdfd u in let (ts, x) := rdb w in
(ACS ss ms tot ylo eg vis gh ab brk fd ts, x).

Definition ENDMARK : Z := 4242.
Definition finish {A : Type} (xi : A * int) : option A :=
let (x, i) := xi in
let (e, j) := rd_num i F in
if (Z.eqb e ENDMARK && PrimInt63.eqb j (length s))%bool then Some x else None.

End Dec.

Record blob : Type := Blob { blob_s : string }.

Definition acs_of (b : blob) : option acs := let s := blob_s b in let F := fuel_of s in finish s F (rdacs s F 0).
Definition ss_of (b : blob) : option sym_state := let s := blob_s b in let F := fuel_of s in finish s F (rdss s F 0).
Definition kn_of (b : blob) : option (list kentry) := let s := blob_s b in let F := fuel_of s in finish s F (rdlist s F (rdke s F) 0).

End AXB.

Declare Scope axb_scope.
Delimit Scope axb_scope with axb.
Bind Scope axb_scope with AXB.blob.
String Notation AXB.blob AXB.Blob AXB.blob_s : axb_scope.

Ltac acsb t := let v := eval vm_compute in t in
lazymatch v with Some ?x => exact_no_check x | _ => fail "AcsBlob: the blob does not decode" end.
