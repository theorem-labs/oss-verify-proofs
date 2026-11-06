(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition argcZ (inp : ProcInput) : Z := Z.of_nat (length (in_argv inp)).
Definition envcZ (inp : ProcInput) : Z := Z.of_nat (length (in_envp inp)).

Definition strbytesZ (inp : ProcInput) : Z :=
  Z.of_nat (length (flatten_strings (in_argv inp))
            + length (flatten_strings (in_envp inp))).

Definition structZ (inp : ProcInput) : Z :=
  8 + 8 * (argcZ inp + 1) + 8 * (envcZ inp + 1) + 160.

Definition padZ (inp : ProcInput) : Z :=
  (8 - (structZ inp + strbytesZ inp) mod 8) mod 8.
Definition sbZ (inp : ProcInput) : Z := strbytesZ inp + padZ inp.

Definition envp0Z (sp0 : Z) (inp : ProcInput) : Z := sp0 + 16 + 8 * argcZ inp.
Definition auxv0Z (sp0 : Z) (inp : ProcInput) : Z := sp0 + 24 + 8 * argcZ inp + 8 * envcZ inp.
Definition strs0Z (sp0 : Z) (inp : ProcInput) : Z := auxv0Z sp0 inp + 160.
Definition rand0Z (sp0 : Z) (inp : ProcInput) : Z := strs0Z sp0 inp + sbZ inp.

Definition wz (a : Z) : word := Z_to_bv 64 a.

Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if (bv_unsigned b =? 47) then S i else acc)
  end.
Definition pn_off (s : list byte) : nat := after_last_slash s 0 0.
Definition argv0_of (inp : ProcInput) : list byte := nth 0 (in_argv inp) [].
Definition pnoffZ (inp : ProcInput) : Z := Z.of_nat (pn_off (argv0_of inp)).

Definition draw0 : EntryDraw := mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0).

Definition msz_n (sz : msize) : nat :=
  match sz with SZ1 => 1%nat | SZ2 => 2%nat | SZ4 => 4%nat | SZ8 => 8%nat end.

Definition load_word (sz : msize) (sg : bool) (bs : list byte) : word :=
  match sz with
  | SZ1 => if sg then sext 64 (bv_extract 0 8 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
  | SZ2 => if sg then sext 64 (bv_extract 0 16 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
  | SZ4 => if sg then sext 64 (bv_extract 0 32 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
  | SZ8 => bv_extract 0 64 (le_bytes_to_word bs)
  end.

Definition msz_eqb (a b : msize) : bool :=
  match a, b with SZ1, SZ1 | SZ2, SZ2 | SZ4, SZ4 | SZ8, SZ8 => true | _, _ => false end.

Inductive dsym : Type :=
| DLin (p c ka ke ks : Z)
| DUid
| DHw
| DPn
| DTid.

Definition dsym_eqb (x y : dsym) : bool :=
  match x, y with
  | DLin p1 c1 a1 e1 s1, DLin p2 c2 a2 e2 s2 =>
      Z.eqb p1 p2 && Z.eqb c1 c2 && Z.eqb a1 a2 && Z.eqb e1 e2 && Z.eqb s1 s2
  | DUid, DUid | DHw, DHw | DPn, DPn | DTid, DTid => true
  | _, _ => false
  end.

Inductive rb : Type :=
| RBL (b : byte)
| RBR (k : nat)
| RBT
| RBF (d : dsym) (i : nat).

Definition rb_eqb (x y : rb) : bool :=
  match x, y with
  | RBL a, RBL b => bv_eqb a b
  | RBR j, RBR k => Nat.eqb j k
  | RBT, RBT => true
  | RBF d i, RBF d' i' => dsym_eqb d d' && Nat.eqb i i'
  | _, _ => false
  end.

Fixpoint rbs_det (l : list rb) : bool :=
  match l with [] => true | RBT :: _ => false | _ :: r => rbs_det r end.

Fixpoint rbs_eqb (xs ys : list rb) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => rb_eqb x y && rbs_eqb xs' ys'
  | _, _ => false
  end.

Record env : Type := Env {
  e_sp   : Z;
  e_inp  : ProcInput;
  e_draw : EntryDraw;
  e_tid  : option word
}.

Inductive aval : Type :=
| ALit (w : word)
| ALin (p c ka ke ks : Z)
| AUid
| AHw
| APn
| ATid
| ACong (m r : Z)
| ATop
| ABytes (sz : msize) (sg : bool) (l : list rb)
| ARng (lo hi : Z).

Definition aval_of_dsym (d : dsym) : aval :=
  match d with
  | DLin p c ka ke ks => ALin p c ka ke ks
  | DUid => AUid | DHw => AHw | DPn => APn | DTid => ATid
  end.

Definition dsym_of_aval (v : aval) : option dsym :=
  match v with
  | ALin p c ka ke ks => Some (DLin p c ka ke ks)
  | AUid => Some DUid | AHw => Some DHw | APn => Some DPn | ATid => Some DTid
  | _ => None
  end.

Definition aval_eqb (a b : aval) : bool :=
  match a, b with
  | ALit x, ALit y => bv_eqb x y
  | ALin p1 c1 a1 e1 s1, ALin p2 c2 a2 e2 s2 =>
      Z.eqb p1 p2 && Z.eqb c1 c2 && Z.eqb a1 a2 && Z.eqb e1 e2 && Z.eqb s1 s2
  | AUid, AUid => true
  | AHw, AHw => true
  | APn, APn => true
  | ATid, ATid => true
  | ACong m1 r1, ACong m2 r2 => Z.eqb m1 m2 && Z.eqb r1 r2
  | ATop, ATop => true
  | ABytes z1 g1 l1, ABytes z2 g2 l2 => msz_eqb z1 z2 && Bool.eqb g1 g2 && rbs_eqb l1 l2
  | ARng l1 h1, ARng l2 h2 => Z.eqb l1 l2 && Z.eqb h1 h2
  | _, _ => false
  end.

Definition adet (v : aval) : bool :=
  match v with ATop => false | ACong _ _ => false | ABytes _ _ _ => false | ARng _ _ => false | _ => true end.

Definition alin_val (E : env) (p c ka ke ks : Z) : Z :=
  p * e_sp E + c + ka * argcZ (e_inp E) + ke * envcZ (e_inp E) + ks * sbZ (e_inp E).

Definition dsym_val (E : env) (d : dsym) (w : word) : Prop :=
  match d with
  | DLin p c ka ke ks => bv_unsigned w = alin_val E p c ka ke ks
  | DUid => w = in_uid (e_inp E)
  | DHw => w = in_hwcap (e_inp E)
  | DPn => bv_unsigned w = strs0Z (e_sp E) (e_inp E) + pnoffZ (e_inp E)
  | DTid => e_tid E = Some w
  end.

Definition rb_val (E : env) (r : rb) (b : byte) : Prop :=
  match r with
  | RBL b' => b = b'
  | RBR k => nth_error (at_random_bytes (ed_random (e_draw E))) k = Some b
  | RBT => True
  | RBF d i => exists w : word, dsym_val E d w /\ nth_error (Z_to_le_bytes 8 (bv_unsigned w)) i = Some b
  end.

Definition aval_val (E : env) (a : aval) (w : word) : Prop :=
  match a with
  | ALit z => w = z
  | ALin p c ka ke ks => bv_unsigned w = alin_val E p c ka ke ks
  | AUid => w = in_uid (e_inp E)
  | AHw => w = in_hwcap (e_inp E)
  | APn => bv_unsigned w = strs0Z (e_sp E) (e_inp E) + pnoffZ (e_inp E)
  | ATid => e_tid E = Some w
  | ACong m r => 0 < m /\ bv_unsigned w mod m = r mod m
  | ATop => True
  | ABytes sz sg l => length l = msz_n sz /\ exists bs, Forall2 (rb_val E) l bs /\ w = load_word sz sg bs
  | ARng lo hi => lo <= bv_unsigned w <= hi
  end.

Inductive abyte : Type :=
| BL (b : byte)
| BF (v : aval) (i : nat)
| BT
| BR (k : nat).

Definition abyte_val (E : env) (ab : abyte) (b : byte) : Prop :=
  match ab with
  | BL b' => b = b'
  | BF v i => exists w : word, aval_val E v w /\ nth_error (Z_to_le_bytes 8 (bv_unsigned w)) i = Some b
  | BT => True
  | BR k => nth_error (at_random_bytes (ed_random (e_draw E))) k = Some b
  end.

Definition rb_abyte (r : rb) : abyte :=
  match r with RBL b => BL b | RBR k => BR k | RBT => BT | RBF d i => BF (aval_of_dsym d) i end.

Definition abyte_rb (ab : abyte) : rb :=
  match ab with
  | BL b => RBL b
  | BR k => RBR k
  | BT => RBT
  | BF v i => match dsym_of_aval v with Some d => RBF d i | None => RBT end
  end.

Definition to_rbs (bs : list abyte) : list rb := map abyte_rb bs.

Fixpoint has_rnd (l : list rb) : bool :=
  match l with [] => false | RBR _ :: _ => true | _ :: r => has_rnd r end.

Inductive aaddr : Type :=
| AAbs (a : Z)
| AStk (c : Z).

Definition abs_top : Z := sp_window_lo - stack_max_size.

Definition aaddr_val (E : env) (x : aaddr) : Z :=
  match x with AAbs a => a | AStk c => e_sp E + c end.

Definition aaddr_succ (x : aaddr) : aaddr :=
  match x with AAbs a => AAbs (a + 1) | AStk c => AStk (c + 1) end.

Definition aaddr_add (x : aaddr) (k : Z) : aaddr :=
  match x with AAbs a => AAbs (a + k) | AStk c => AStk (c + k) end.
