(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From Stdlib Require Import PrimInt63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan HUFam.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.

Module CXB2.

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
      | 7 => let (sx, k) := rdb j in let (kk, l) := rdnat k in let (z, m) := rdZ l in let (n, p) := rdnat m in (EBlob sx kk z n, p)
      | 8 => let (a, l) := rdexpr f' j in let (b, m) := rdexpr f' l in (eadd a b, m)
      | 9 => let (a, l) := rdexpr f' j in let (b, m) := rdexpr f' l in (esub a b, m)
      | 10 => let (c, k) := rdZ j in let (a, l) := rdexpr f' k in (escale c a, l)
      | _ => let (a, l) := rdexpr f' j in let (z, m) := rdZ l in (eaddz a z, m)
      end
  end.
Definition rde : int -> expr * int := rdexpr F.
Definition rdsa (i : int) : saddr * int :=
  let (t, j) := rd_num i F in let (b, k) := rde j in let (o, l) := rdZ k in
  ((if Z.eqb t 0 then SA b o else to_saddr b o), l).

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
Definition rdss (i : int) : sym_state * int :=
  let (p, j) := rdZ i in let (rs, k) := rdlist rde j in let (kk, m) := rdlist rdke k in let (nx, q) := rdnat m in (SS p rs [] kk nx, q).
Definition rdam (i : int) : amap * int :=
  let (b, j) := rde i in let (ln, k) := rde j in let (kd, l) := rdN k in (AM b ln (mkind_of kd), l).
Definition rdfd (i : int) : afd * int :=
  let (t, j) := rd_num i F in
  match t with
  | 0 => (FdStd, j)
  | 1 => let (kk, k) := rdnat j in let (ln, l) := rde k in let (off, m) := rde l in (FdFile kk ln off, m)
  | _ => (FdDir, j)
  end.
Definition rdacs (i : int) : acs * int :=
  let (ss, j) := rdss i in let (ms, k) := rdlist rdam j in let (tot, l) := rdZ k in let (ylo, m) := rdZ l in let (eag, n) := rdZ m in
  let (vis, o) := rdlist (rdpair rde rde) n in let (gh, p) := rdlist (rdpair rde rde) o in let (ab, q) := rdZ p in
  let (bk, r) := rde q in let (fd, t) := rdfd r in let (ts, u) := rdb t in
  (ACS ss ms tot ylo eag vis gh ab bk fd ts, u).
Definition rdsub : int -> sub * int := rdlist (rdpair rdnat rde).
Definition rdkl : int -> list kentry * int := rdlist rdke.

Fixpoint rdplan (f : nat) (i : int) {struct f} : plan * int :=
  match f with
  | O => (PExit, i)
  | S f' =>
      let (t, j) := rd_num i F in
      match t with
      | 0 => let (st, k) := rdlist rdZ j in let (p, l) := rdplan f' k in (PRun st p, l)
      | 1 => let (e, k) := rde j in let (mid, l) := rdZ k in let (p1, m) := rdplan f' l in let (p2, n) := rdplan f' m in (PSplit e mid p1 p2, n)
      | 2 => let (K, k) := rdke j in let (p, l) := rdplan f' k in (PFact K p, l)
      | 3 => let (b, k) := rde j in let (off, l) := rdZ k in let (n, m) := rdnat l in let (p, q) := rdplan f' m in (PJoin b off n p, q)
      | 4 => let (b, k) := rde j in let (off, l) := rdZ k in let (n, m) := rdnat l in let (p, q) := rdplan f' m in (PJoinX b off n p, q)
      | 5 => let (b, k) := rde j in let (n, l) := rde k in let (p, m) := rdplan f' l in (PDropRange b n p, m)
      | 6 => let (r, k) := rdnat j in let (lc, l) := rdZ k in let (bs, m) := rdopt rde l in let (p, q) := rdplan f' m in (PFresh r lc bs p, q)
      | 7 => let (r, k) := rdnat j in let (e, l) := rde k in let (p, m) := rdplan f' l in (PRespell r e p, m)
      | 8 => let (x, k) := rdN j in let (args, l) := rdlist rde k in let (p, m) := rdplan f' l in (PX (if Z.eqb x 0 then XMemset else XMemcpy) args p, m)
      | 9 => let (id, k) := rdnat j in let (args, l) := rdlist rde k in let (p, m) := rdplan f' l in (PExt id args p, m)
      | 10 => let (id, k) := rdnat j in let (args, l) := rdlist rde k in let (p, m) := rdplan f' l in (PEmit id args p, m)
      | 11 => let (J, k) := rdnat j in let (N, l) := rde k in let (inv, m) := rdacs l in let (bd, n) := rdplan f' m in let (p, q) := rdplan f' n in
              (PLoop J N inv bd p, q)
      | 12 => (PNext, j)
      | 13 => let (h, k) := rdnat j in (PHandoff h, k)
      | 15 => let (jp, k) := rdZ j in let (rs, l) := rdlist rdnat k in let (p, m) := rdplan f' l in (PDiamond jp rs p, m)
      | _ => (PExit, j)
      end
  end.
Definition rdp : int -> plan * int := rdplan F.

(* [comment removed for export] *)
Definition rda0 (i : int) : a0d * int :=
  let (fs, j) := rdkl i in let (p, k) := rdp j in let (sg, l) := rdsub k in let (fx, m) := rdkl l in (A0D fs p sg fx, m).
Definition rdleaf (i : int) : leafd * int :=
  let (fs, j) := rdkl i in let (pa, k) := rdp j in let (sg, l) := rdsub k in let (fp, m) := rdkl l in let (pc1, n) := rdp m in
  let (rhos, o) := rdlist rdsub n in let (ovr, q) := rdlist (rdpair rdnat rdp) o in (LDX fs pa sg fp pc1 rhos ovr, q).
Definition rdhole (i : int) : (nat * holed) * int :=
  let (jn, j) := rdnat i in let (c, k) := rdnat j in let (tau, l) := rdsub k in let (fq, m) := rdkl l in let (p, n) := rdp m in ((jn, HD c tau fq p), n).
Definition rdop (i : int) : opd * int :=
  let (fs, j) := rdkl i in let (p, k) := rdp j in let (hs, l) := rdlist rdhole k in (OD fs p hs, l).

Definition fin {A : Type} (r : A * int) : option A :=
  let (x, j) := r in let (e, k) := rd_num j F in
  if (Z.eqb e 4242 && PrimInt63.eqb k (length s))%bool then Some x else None.
End Dec.

Definition acs_of (s : string) : option acs := let F := fuel_of s in fin s F (rdacs s F 0%uint63).
Definition acsl_of (s : string) : option (list acs) := let F := fuel_of s in fin s F (rdlist s F (rdacs s F) 0%uint63).
Definition a0s_of (s : string) : option (list a0d) := let F := fuel_of s in fin s F (rdlist s F (rda0 s F) 0%uint63).
Definition leaves_of (s : string) : option (list leafd) := let F := fuel_of s in fin s F (rdlist s F (rdleaf s F) 0%uint63).
Definition ops_of (s : string) : option (list opd) := let F := fuel_of s in fin s F (rdlist s F (rdop s F) 0%uint63).
End CXB2.

(* [comment removed for export] *)
Ltac cxb2 o :=
  let r := eval vm_compute in o in
  lazymatch r with
  | Some ?x => exact_no_check x
  | _ => fail "CXB2: the blob does not decode"
  end.
