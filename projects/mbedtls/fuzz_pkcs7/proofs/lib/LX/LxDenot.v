(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA AShadow.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint pget {A} (l : list A) (i : positive) (d : A) {struct l} : A :=
  match l with
  | [] => d
  | x :: l' => match i with
               | xH => x
               | _ => pget l' (Pos.pred i) d
               end
  end.

Fixpoint pad_set {A} (n : nat) (v d : A) : list A :=
  match n with O => [v] | S n' => d :: pad_set n' v d end.

Fixpoint pset {A} (l : list A) (i : positive) (v d : A) {struct l} : list A :=
  match l with
  | [] => pad_set (Nat.pred (Pos.to_nat i)) v d
  | x :: l' => match i with
               | xH => v :: l'
               | _ => x :: pset l' (Pos.pred i) v d
               end
  end.

Record env := ENV { ezl : list Z; ewl : list word; ebl : list (list byte); eol : list (mem -> Prop); ell : list (list word);
                    eml : list mem;  (* [comment removed for export] *)
                    elw : list (list (Z * Z) -> mem -> mem -> Prop);  (* [comment removed for export] *)
                    epr : list (list Z -> Prop);  (* [comment removed for export] *)
                    (* [comment removed for export] *)
                    elb0 : list (Z * Z);
                    ehp : list (Z * Z) -> mem -> Model -> Prop;
                    ecw : list (Z * Z) -> Z -> Prop;
                    elh : list (list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop);
                    ecur : Model;    (* [comment removed for export] *)
                    (* [comment removed for export] *)
                    elbl : list (list (Z * Z));
                    ehr : list (list (Z * Z) -> list (Z * Z) -> list Z -> mem -> Prop) }.
Definition ez (E : env) (i : positive) : Z := pget (ezl E) i 0.
Definition ew (E : env) (i : positive) : word := pget (ewl E) i (Z_to_bv 64 0).
Definition eb (E : env) (i : positive) : list byte := pget (ebl E) i [].
(* [comment removed for export] *)
Definition el (E : env) (i : positive) : list word := pget (ell E) i [].
(* [comment removed for export] *)
Definition eo (E : env) (k : nat) : mem -> Prop := nth k (eol E) (fun _ => True).
(* [comment removed for export] *)
Definition em (E : env) (k : nat) : mem := nth k (eml E) (fun _ => None).
Definition elaw (E : env) (l : nat) : list (Z * Z) -> mem -> mem -> Prop := nth l (elw E) (fun _ _ _ => True).
(* [comment removed for export] *)
Definition eprop (E : env) (j : nat) (vs : list Z) : Prop := nth j (epr E) (fun _ => True) vs.
(* [comment removed for export] *)
Definition lx_hlawd : list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop := fun _ _ _ m1 m2 => m2 = m1.
Definition ehlaw (E : env) (l : nat) : list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop := nth l (elh E) lx_hlawd.
(* [comment removed for export] *)
Definition lx_blks : Type := list (Z * Z).
Definition lx_hpred : Type := list (Z * Z) -> mem -> Model -> Prop.
Definition lx_cwpred : Type := list (Z * Z) -> Z -> Prop.
Definition lx_hlaws : Type := list (list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop).
Definition lx_hress : Type := list (list (Z * Z) -> list (Z * Z) -> list Z -> mem -> Prop).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition lx_nohp : lx_hpred := fun _ _ _ => True.
Definition lx_nocw : lx_cwpred := fun _ _ => True.

(* [comment removed for export] *)
Definition lx_nomodel : Model :=
  mkModel [] (mkVmMaps [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) 0%Z) IEof [] None None None.

Definition env_setz (E : env) (i : positive) (v : Z) : env :=
  ENV (pset (ezl E) i v 0) (ewl E) (ebl E) (eol E) (ell E) (eml E) (elw E) (epr E) (elb0 E) (ehp E) (ecw E) (elh E) (ecur E) (elbl E) (ehr E).
(* [comment removed for export] *)
Definition env_setl (E : env) (i : positive) (l : list word) : env :=
  ENV (ezl E) (ewl E) (ebl E) (eol E) (pset (ell E) i l []) (eml E) (elw E) (epr E) (elb0 E) (ehp E) (ecw E) (elh E) (ecur E) (elbl E) (ehr E).

(* [comment removed for export] *)
Fixpoint nset {A} (l : list A) (k : nat) (v d : A) : list A :=
  match l, k with
  | [], O => [v]
  | [], S k' => d :: nset [] k' v d
  | x :: l', O => v :: l'
  | x :: l', S k' => x :: nset l' k' v d
  end.
Definition env_setm (E : env) (k : nat) (m : mem) : env :=
  ENV (ezl E) (ewl E) (ebl E) (eol E) (ell E) (nset (eml E) k m (fun _ => None)) (elw E) (epr E) (elb0 E) (ehp E) (ecw E) (elh E) (ecur E) (elbl E) (ehr E).
(* [comment removed for export] *)
Definition env_setcur (E : env) (mo : Model) : env :=
  ENV (ezl E) (ewl E) (ebl E) (eol E) (ell E) (eml E) (elw E) (epr E) (elb0 E) (ehp E) (ecw E) (elh E) mo (elbl E) (ehr E).
(* [comment removed for export] *)
Definition env_setbl (E : env) (k : nat) (lb : list (Z * Z)) : env :=
  ENV (ezl E) (ewl E) (ebl E) (eol E) (ell E) (eml E) (elw E) (epr E) (elb0 E) (ehp E) (ecw E) (elh E) (ecur E) (nset (elbl E) k lb []) (ehr E).
Definition eblv (E : env) (k : nat) : list (Z * Z) := nth k (elbl E) [].

Lemma pget_cons : forall {A} x (l : list A) i d,
  pget (x :: l) i d = if Pos.eqb i 1 then x else pget l (Pos.pred i) d.
Proof. intros A x l i d. cbn. destruct i; reflexivity. Qed.

Lemma pget_pad : forall {A} n i (v d : A), pget (pad_set n v d) i d = if Nat.eqb (Pos.to_nat i) (S n) then v else d.
Proof.
  induction n as [|n IH]; intros i v d; cbn [pad_set]; rewrite pget_cons.
  - destruct (Pos.eqb_spec i 1) as [->|Hi]; [reflexivity|]. cbn [pget].
    destruct (Nat.eqb_spec (Pos.to_nat i) 1) as [E1|]; [|reflexivity]. exfalso. apply Hi. lia.
  - destruct (Pos.eqb_spec i 1) as [->|Hi]; [reflexivity|]. rewrite IH. rewrite Pos2Nat.inj_pred by lia.
    destruct (Nat.eqb_spec (Init.Nat.pred (Pos.to_nat i)) (S n)); destruct (Nat.eqb_spec (Pos.to_nat i) (S (S n))); try reflexivity; lia.
Qed.

Lemma pget_pset : forall {A} (l : list A) i j (v d : A),
  pget (pset l i v d) j d = if Pos.eqb j i then v else pget l j d.
Proof.
  induction l as [|x l IH]; intros i j v d; cbn [pset].
  - rewrite pget_pad. cbn [pget]. destruct (Nat.eqb_spec (Pos.to_nat j) (S (Nat.pred (Pos.to_nat i)))); destruct (Pos.eqb_spec j i); try reflexivity; lia.
  - destruct i as [p|p|].
    + rewrite !pget_cons. destruct (Pos.eqb_spec j 1) as [->|Hj]; [reflexivity|]. rewrite IH.
      destruct (Pos.eqb_spec (Pos.pred j) (Pos.pred (xI p))); destruct (Pos.eqb_spec j (xI p)); try reflexivity; exfalso; lia.
    + rewrite !pget_cons. destruct (Pos.eqb_spec j 1) as [->|Hj]; [reflexivity|]. rewrite IH.
      destruct (Pos.eqb_spec (Pos.pred j) (Pos.pred (xO p))); destruct (Pos.eqb_spec j (xO p)); try reflexivity; exfalso; lia.
    + rewrite !pget_cons. destruct (Pos.eqb_spec j 1); reflexivity.
Qed.

Lemma ez_setz : forall E i v j, ez (env_setz E i v) j = if Pos.eqb j i then v else ez E j.
Proof. intros. unfold ez, env_setz. cbn [ezl]. apply pget_pset. Qed.
Lemma ew_setz : forall E i v j, ew (env_setz E i v) j = ew E j. Proof. reflexivity. Qed.
Lemma eb_setz : forall E i v j, eb (env_setz E i v) j = eb E j. Proof. reflexivity. Qed.
Lemma el_setz : forall E i v j, el (env_setz E i v) j = el E j. Proof. reflexivity. Qed.
Lemma em_setz : forall E i v k, em (env_setz E i v) k = em E k. Proof. reflexivity. Qed.
Lemma elaw_setz : forall E i v l, elaw (env_setz E i v) l = elaw E l. Proof. reflexivity. Qed.
Lemma ecur_setz : forall E i v, ecur (env_setz E i v) = ecur E. Proof. reflexivity. Qed.
Lemma eprop_setz : forall E i v j vs, eprop (env_setz E i v) j vs = eprop E j vs. Proof. reflexivity. Qed.
Lemma el_setl : forall E i l j, el (env_setl E i l) j = if Pos.eqb j i then l else el E j.
Proof. intros. unfold el, env_setl. cbn [ell]. apply pget_pset. Qed.
Lemma ez_setl : forall E i l j, ez (env_setl E i l) j = ez E j. Proof. reflexivity. Qed.
Lemma ew_setl : forall E i l j, ew (env_setl E i l) j = ew E j. Proof. reflexivity. Qed.
Lemma eb_setl : forall E i l j, eb (env_setl E i l) j = eb E j. Proof. reflexivity. Qed.
Lemma em_setl : forall E i l k, em (env_setl E i l) k = em E k. Proof. reflexivity. Qed.
Lemma eo_setl : forall E i l k, eo (env_setl E i l) k = eo E k. Proof. reflexivity. Qed.
Lemma elaw_setl : forall E i l k, elaw (env_setl E i l) k = elaw E k. Proof. reflexivity. Qed.
Lemma ecur_setl : forall E i l, ecur (env_setl E i l) = ecur E. Proof. reflexivity. Qed.
Lemma eprop_setl : forall E i l j vs, eprop (env_setl E i l) j vs = eprop E j vs. Proof. reflexivity. Qed.
Lemma nth_nset : forall {A} (l : list A) k j (v d : A), nth j (nset l k v d) d = if Nat.eqb j k then v else nth j l d.
Proof.
  induction l as [|x l IH]; intros k j v d.
  - revert j. induction k as [|k IHk]; intros j; cbn [nset].
    + destruct j; [reflexivity|]. cbn. destruct j; reflexivity.
    + destruct j; [reflexivity|]. cbn [nth]. rewrite IHk. cbn [Nat.eqb]. destruct (Nat.eqb j k); [reflexivity|]. destruct j; reflexivity.
  - destruct k; destruct j; cbn [nset nth Nat.eqb]; try reflexivity. apply IH.
Qed.
Lemma em_setm : forall E k m j, em (env_setm E k m) j = if Nat.eqb j k then m else em E j.
Proof. intros. unfold em, env_setm. cbn [eml]. apply nth_nset. Qed.
Lemma ez_setm : forall E k m i, ez (env_setm E k m) i = ez E i. Proof. reflexivity. Qed.
Lemma ew_setm : forall E k m i, ew (env_setm E k m) i = ew E i. Proof. reflexivity. Qed.
Lemma eb_setm : forall E k m i, eb (env_setm E k m) i = eb E i. Proof. reflexivity. Qed.
Lemma el_setm : forall E k m i, el (env_setm E k m) i = el E i. Proof. reflexivity. Qed.
Lemma eo_setm : forall E k m i, eo (env_setm E k m) i = eo E i. Proof. reflexivity. Qed.
Lemma elaw_setm : forall E k m l, elaw (env_setm E k m) l = elaw E l. Proof. reflexivity. Qed.
Lemma ecur_setm : forall E k m, ecur (env_setm E k m) = ecur E. Proof. reflexivity. Qed.
Lemma eprop_setm : forall E k m j vs, eprop (env_setm E k m) j vs = eprop E j vs. Proof. reflexivity. Qed.
Lemma eprop_setcur : forall E mo j vs, eprop (env_setcur E mo) j vs = eprop E j vs. Proof. reflexivity. Qed.
Lemma ecur_setcur : forall E mo, ecur (env_setcur E mo) = mo. Proof. reflexivity. Qed.
Lemma ez_setcur : forall E mo i, ez (env_setcur E mo) i = ez E i. Proof. reflexivity. Qed.
Lemma ew_setcur : forall E mo i, ew (env_setcur E mo) i = ew E i. Proof. reflexivity. Qed.
Lemma eb_setcur : forall E mo i, eb (env_setcur E mo) i = eb E i. Proof. reflexivity. Qed.
Lemma el_setcur : forall E mo i, el (env_setcur E mo) i = el E i. Proof. reflexivity. Qed.
Lemma eo_setcur : forall E mo i, eo (env_setcur E mo) i = eo E i. Proof. reflexivity. Qed.
Lemma em_setcur : forall E mo i, em (env_setcur E mo) i = em E i. Proof. reflexivity. Qed.
Lemma elaw_setcur : forall E mo l, elaw (env_setcur E mo) l = elaw E l. Proof. reflexivity. Qed.
Lemma em_setbl : forall E k lb i, em (env_setbl E k lb) i = em E i. Proof. reflexivity. Qed.
Lemma ez_setbl : forall E k lb i, ez (env_setbl E k lb) i = ez E i. Proof. reflexivity. Qed.
Lemma ew_setbl : forall E k lb i, ew (env_setbl E k lb) i = ew E i. Proof. reflexivity. Qed.
Lemma eb_setbl : forall E k lb i, eb (env_setbl E k lb) i = eb E i. Proof. reflexivity. Qed.
Lemma el_setbl : forall E k lb i, el (env_setbl E k lb) i = el E i. Proof. reflexivity. Qed.
Lemma eo_setbl : forall E k lb i, eo (env_setbl E k lb) i = eo E i. Proof. reflexivity. Qed.
Lemma elaw_setbl : forall E k lb l, elaw (env_setbl E k lb) l = elaw E l. Proof. reflexivity. Qed.
Lemma ecur_setbl : forall E k lb, ecur (env_setbl E k lb) = ecur E. Proof. reflexivity. Qed.
Lemma eprop_setbl : forall E k lb j vs, eprop (env_setbl E k lb) j vs = eprop E j vs. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition opden (o : opk) (x y : Z) : Z :=
  match o with
  | OAnd => Z.land x y
  | OOr => Z.lor x y
  | OXor => Z.lxor x y
  | OShr => Z.shiftr x y
  | OMul => x * y
  | OLow => zlow y x
  | OSx => zswrap y x
  | OLtu => Z.b2z (Z.ltb x y)
  | OLts => Z.b2z (Z.ltb x y)
  | ODivU => x / y
  | ORemU => x mod y
  | OShl => Z.shiftl x y
  end.

Fixpoint zden (E : env) (e : expr) : Z :=
  match e with
  | ELit z => z
  | EZv i => ez E i
  | EUv i => bv_unsigned (ew E i)
  | EAdd a b => zden E a + zden E b
  | EMulC c a => c * zden E a
  | EOp o a b => opden o (zden E a) (zden E b)
  end.

(* [comment removed for export] *)
Fixpoint zdenp (E : env) (e : expr) : Z :=
  match e with
  | ELit z => z
  | EZv i => ez E i
  | EUv i => bv_unsigned (ew E i)
  | EAdd a (ELit 0) => zdenp E a
  | EAdd a b => zdenp E a + zdenp E b
  | EMulC 1 a => zdenp E a
  | EMulC (-1) a => - zdenp E a
  | EMulC c a => c * zdenp E a
  | EOp o a b => opden o (zdenp E a) (zdenp E b)
  end.

Definition rden (E : env) (r : sreg) : word :=
  match r with RW i => ew E i | RZ e => Z_to_bv 64 (zdenp E e) end.

Fixpoint cden (E : env) (c : cellx) : cell :=
  match c with
  | XW i => C8 (ew E i)
  | XZ 8 e => C8 (Z_to_bv 64 (zdenp E e))
  | XZ 4 e => C4 (Z_to_bv 64 (zdenp E e))
  | XZ 2 e => C2 (Z_to_bv 64 (zdenp E e))
  | XZ 1 e => C1 (Z_to_bv 8 (zdenp E e))
  | XZ w _ => CB (N.to_nat w) (repeat (Z_to_bv 8 0) (N.to_nat w))
  | XB w k => CB (N.to_nat w) (eb E k)
  | XRep w e => CB (N.to_nat w) (repeat (Z_to_bv 8 (zdenp E e)) (N.to_nat w))
  | XWn 4 i => C4 (ew E i)
  | XWn 2 i => C2 (ew E i)
  | XWn w _ => CB (N.to_nat w) (repeat (Z_to_bv 8 0) (N.to_nat w))
  | XSl c o l => CB (N.to_nat l) (firstn (N.to_nat l) (skipn (N.to_nat o) (cbytes (cden E c))))
  end.

Definition csden (E : env) (cs : list cellx) : list cell := map (cden E) cs.

(* [comment removed for export] *)
Definition wbytes (w : N) (x : word) : list byte :=
  match w with 8%N => le8 x | 4%N => le4 x | 2%N => le2 x | 1%N => le1 x | _ => [] end.

Fixpoint ldenw (E : env) (l : lexpr) : list word :=
  match l with
  | LBase k => el E k
  | LUpd l i _ v => upd (ldenw E l) (Z.to_nat (zdenp E i)) (Z_to_bv 64 (zdenp E v))
  end.

Fixpoint ldenb (E : env) (l : lexpr) : list byte :=
  match l with
  | LBase k => eb E k
  | LUpd l i w v => upd_bytes (ldenb E l) (Z.to_nat (zdenp E i)) (wbytes w (Z_to_bv 64 (zdenp E v)))
  end.

(* [comment removed for export] *)
Definition kden (k : ckind) (x y : Z) : bool :=
  match k with
  | KEq => Z.eqb (zlow 64 x) (zlow 64 y)
  | KLtu => Z.ltb (zlow 64 x) (zlow 64 y)
  | KLts => Z.ltb (zswrap 64 x) (zswrap 64 y)
  end.

Definition cnden (E : env) (c : cond) : bool :=
  match c with CN n k a b => xorb n (kden k (zdenp E a) (zdenp E b)) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Facts.
  Variable segs : list Segment.
  Variable L : asan_layout.
  Variable CS : Z -> Prop.

  (* [comment removed for export] *)
  Definition wden (E : env) (W : list (expr * expr)) : list ivl :=
    map (fun lh => (zdenp E (fst lh), zdenp E (snd lh))) W.

  (* [comment removed for export] *)
  Definition lawcli (LAW : list ivl -> mem -> mem -> Prop) (a n : Z) : Prop :=
    forall X m1 m2 x, LAW X m1 m2 -> a <= x < a + n -> 0 <= x < 2 ^ 64 -> outside X x ->
      m2 (wa x) = m1 (wa x) /\ (wview segs m1 (wa x) <> None -> wview segs m2 (wa x) <> None).
  (* [comment removed for export] *)
  Definition lawobj (LAW : list ivl -> mem -> mem -> Prop) (a n : Z) : Prop :=
    forall X m1 m2 b k, LAW X m1 m2 -> a <= b -> b + k <= a + n -> aobj segs L CS m1 b k -> aobj segs L CS m2 b k.

  (* [comment removed for export] *)
  Fixpoint blden (E : env) (bl : bklist) : list (Z * Z) :=
    match bl with BL0 => elb0 E | BLV k => eblv E k | BCons a n bl' => (zdenp E a, zdenp E n) :: blden E bl' end.
  (* [comment removed for export] *)
  Definition lx_hcli (LB0 : list (Z * Z)) (LAW : list (Z * Z) -> Z -> list ivl -> mem -> mem -> Prop) (smax a n : Z) : Prop :=
    forall LB sp X m1 m2 x, (forall b, In b LB0 -> In b LB) -> sp <= smax -> LAW LB sp X m1 m2 -> a <= x < a + n -> 0 <= x < 2 ^ 64 -> outside X x ->
      m2 (wa x) = m1 (wa x) /\ (wview segs m1 (wa x) <> None -> wview segs m2 (wa x) <> None).
  Definition hlawcli (E : env) (LAW : list (Z * Z) -> Z -> list ivl -> mem -> mem -> Prop) (smax a n : Z) : Prop :=
    lx_hcli (elb0 E) LAW smax a n.
  (* [comment removed for export] *)
  Definition hp_frame (P : list (Z * Z) -> mem -> Model -> Prop) (CW : list (Z * Z) -> Z -> Prop) : Prop :=
    forall LB m m' mo W, P LB m mo -> munch W m m' -> wmono segs m m' ->
      Forall (fun iv => forall x, fst iv <= x < snd iv -> CW LB x) W -> P LB m' mo.
  Lemma hp_frame_nohp : hp_frame lx_nohp lx_nocw.
  Proof. intros LB m m' mo W _ _ _ _. exact I. Qed.
  (* [comment removed for export] *)
  Definition hp_blk (CW : list (Z * Z) -> Z -> Prop) : Prop :=
    forall LB b k x, In (b, k) LB -> b <= x < b + k -> CW LB x.
  Lemma hp_blk_nocw : hp_blk lx_nocw.
  Proof. intros LB b k x _ _. exact I. Qed.
  (* [comment removed for export] *)
  Definition hlaw_ok (LAW : list (Z * Z) -> Z -> list ivl -> mem -> mem -> Prop) : Prop :=
    forall LB sp X m1 m2 x, LAW LB sp X m1 m2 -> 0 <= x < 2 ^ 64 -> outside X x -> (sp <= x \/ in_block LB x) ->
      m2 (wa x) = m1 (wa x) /\ (wview segs m1 (wa x) <> None -> wview segs m2 (wa x) <> None).
  Lemma hlaw_ok_d : hlaw_ok lx_hlawd.
  Proof. intros LB sp X m1 m2 x H _ _ _. rewrite H. split; [reflexivity| intros Y; exact Y]. Qed.
  Lemma ehlaw_ok : forall E l, Forall hlaw_ok (elh E) -> hlaw_ok (ehlaw E l).
  Proof.
    intros E l H. unfold ehlaw. destruct (Nat.lt_ge_cases l (length (elh E))) as [LT|GE].
    - rewrite List.Forall_forall in H. apply H. apply nth_In. exact LT.
    - rewrite nth_overflow by exact GE. apply hlaw_ok_d.
  Qed.
  (* [comment removed for export] *)
  Definition lx_hopq (LB0 : list (Z * Z)) (LAW : list (Z * Z) -> Z -> list ivl -> mem -> mem -> Prop) (P : mem -> Prop) : Prop :=
    forall LB sp X m1 m2, (forall b, In b LB0 -> In b LB) -> LAW LB sp X m1 m2 -> P m1 -> P m2.
  Definition hlawopq (E : env) (LAW : list (Z * Z) -> Z -> list ivl -> mem -> mem -> Prop) (P : mem -> Prop) : Prop :=
    lx_hopq (elb0 E) LAW P.
  (* [comment removed for export] *)
  Definition lx_heapkit (P : list (Z * Z) -> mem -> Model -> Prop) (CW : list (Z * Z) -> Z -> Prop)
      (LH : list (list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop)) (LB0 LB : list (Z * Z)) (OK : list ivl) (m : mem) (mo : Model) : Prop :=
    (P LB m mo /\ Forall (fun iv => forall x, fst iv <= x < snd iv -> forall LB', (forall b, In b LB0 -> In b LB') -> CW LB' x) OK)
    /\ ((forall b, In b LB0 -> In b LB) /\ hp_frame P CW /\ hp_blk CW /\ Forall hlaw_ok LH).

  (* [comment removed for export] *)
  Definition hres := list (Z * Z) -> list (Z * Z) -> list Z -> mem -> Prop.
  Definition hres_d : hres := fun _ _ _ _ => True.
  Definition ehres (E : env) (j : nat) : hres := nth j (ehr E) hres_d.
  Definition hres_ok (CW : list (Z * Z) -> Z -> Prop) (R : hres) : Prop :=
    forall blo bln vs m1 m2, R blo bln vs m1 -> mem_inv segs m2 ->
      (forall x, 0 <= x < 2 ^ 64 -> in_block bln x -> ~ CW blo x ->
         m2 (wa x) = m1 (wa x) /\ (wview segs m1 (wa x) <> None -> wview segs m2 (wa x) <> None)) ->
      R blo bln vs m2.
  Lemma hres_ok_d : forall CW, hres_ok CW hres_d.
  Proof. intros CW blo bln vs m1 m2 _ _ _. exact I. Qed.
  Lemma ehres_ok : forall E CW j, Forall (hres_ok CW) (ehr E) -> hres_ok CW (ehres E j).
  Proof.
    intros E CW j H. unfold ehres. destruct (Nat.lt_ge_cases j (length (ehr E))) as [LT|GE].
    - rewrite List.Forall_forall in H. apply H. apply nth_In. exact LT.
    - rewrite nth_overflow by exact GE. apply hres_ok_d.
  Qed.
  (* [comment removed for export] *)
  Definition lx_hres (CW : list (Z * Z) -> Z -> Prop) (LB0 : list (Z * Z)) (R : hres) (blo bln : list (Z * Z)) (vs : list Z)
      (OK : list ivl) (m : mem) : Prop :=
    R blo bln vs m
    /\ (hres_ok CW R /\ hp_blk CW
        /\ Forall (fun iv => forall x, fst iv <= x < snd iv -> forall LB', (forall b, In b LB0 -> In b LB') -> CW LB' x) OK
        /\ (forall b, In b LB0 -> In b blo) /\ (forall b, In b blo -> In b bln)).

  Lemma blden_ext0 : forall E bl b, bl_based0 bl = true -> In b (elb0 E) -> In b (blden E bl).
  Proof. intros E bl b. induction bl as [|a n bl IH|k]; cbn; intros H Hb; [exact Hb| right; exact (IH H Hb)| discriminate]. Qed.

  Definition pfact_ok (E : env) (f : pfact) : Prop :=
    match f with
    | FGe e => 0 <= zdenp E e
    | FSep a n b k => zdenp E a + zdenp E n <= zdenp E b \/ zdenp E b + zdenp E k <= zdenp E a
    | FSep0 z a n b k => zdenp E z = 0 \/ zdenp E a + zdenp E n <= zdenp E b \/ zdenp E b + zdenp E k <= zdenp E a
    | FAl a k => zdenp E a mod 2 ^ (Z.of_N k) = 0
    | FCr a n => crange CS (zdenp E a) (zdenp E n)
    | FShb v c oa on =>
        forall n, 1 <= n -> zdenp E oa <= zdenp E c -> zdenp E c + n <= zdenp E oa + zdenp E on ->
        ez E v = 0 \/ (zdenp E c mod 8 + (n - 1) < ez E v /\ ez E v <= 7)
    | FLe a b => zdenp E a <= zdenp E b
    | FLt a b => zdenp E a < zdenp E b
    | FEq a b => zdenp E a = zdenp E b
    | FOr2 a b c d => zdenp E a <= zdenp E b \/ zdenp E c <= zdenp E d
    | FOr3z z a b c d => zdenp E z = 0 \/ zdenp E a <= zdenp E b \/ zdenp E c <= zdenp E d
    | FProp j xs => eprop E j (map (zdenp E) xs)
    end.


  (* [comment removed for export] *)
  Definition opq_allowed (OK SH : list ivl) (iv : ivl) : Prop :=
    (exists lo hi, In (lo, hi) OK /\ lo <= fst iv /\ snd iv <= hi)
    \/ (forall a, fst iv <= a < snd iv -> exists c lo hi, In (lo, hi) SH /\ lo <= c < hi /\ CS c /\ a = shadow_of L c).
  Definition lx_opq (P : mem -> Prop) (OK SH : list ivl) (m : mem) : Prop :=
    P m /\ forall W m1 m2, P m1 -> munch W m1 m2 -> wmono segs m1 m2 -> Forall (opq_allowed OK SH) W -> P m2.

  Definition mfact_ok (E : env) (m : mem) (f : mfact) : Prop :=
    match f with
    | MRw a cs => rw_cells segs m (zdenp E a) (csden E cs)
    | MRo a cs => ro_cells segs m (zdenp E a) (csden E cs)
    | MBy a n k => bytes_at segs m (zdenp E a) (eb E k) /\ Z.of_nat (length (eb E k)) = zdenp E n
    | MStk lo hi => stk segs m (zdenp E lo) (zdenp E hi)
    | MAobj a n => aobj segs L CS m (zdenp E a) (zdenp E n)
    | MOpq k ok sh => lx_opq (eo E k) (wden E ok) (wden E sh) m
    | MArr a 1 l n wr => (if wr then u8arr segs m (zdenp E a) (ldenb E l) else bytes_at segs m (zdenp E a) (ldenb E l))
                         /\ Z.of_nat (length (ldenb E l)) = zdenp E n
    | MArr a 4 l n wr => (if wr then u32arr segs m (zdenp E a) (ldenw E l) else bytes_at segs m (zdenp E a) (u32s (ldenw E l)))
                         /\ Z.of_nat (length (ldenw E l)) = zdenp E n
    | MArr a 8 l n wr => (if wr then u64arr segs m (zdenp E a) (ldenw E l) else bytes_at segs m (zdenp E a) (u64s (ldenw E l)))
                         /\ Z.of_nat (length (ldenw E l)) = zdenp E n
    | MArr _ _ _ _ _ => False
    (* [comment removed for export] *)
    | MMunch W i j => munch (wden E W) (em E i) (em E j)
    | MWmono i j => wmono segs (em E i) (em E j)
    | MLaw l X i j => elaw E l (wden E X) (em E i) (em E j)
    | MCli l a n => lawcli (elaw E l) (zdenp E a) (zdenp E n)
    | MCobj l a n => lawobj (elaw E l) (zdenp E a) (zdenp E n)
    (* [comment removed for export] *)
    | MHeap bl ok => lx_heapkit (ehp E) (ecw E) (elh E) (elb0 E) (blden E bl) (wden E ok) m (ecur E)
    | MLawH l bl sp X i j => ehlaw E l (blden E bl) (zdenp E sp) (wden E X) (em E i) (em E j)
    | MCliH l s a n => hlawcli E (ehlaw E l) (zdenp E s) (zdenp E a) (zdenp E n)
    | MApartBl a n bl => forall b k, In (b, k) (blden E bl) -> zdenp E a + zdenp E n <= b \/ b + k <= zdenp E a
    | MOqH l k => hlawopq E (ehlaw E l) (eo E k)
    | MHpr j blo bln xs ok => lx_hres (ecw E) (elb0 E) (ehres E j) (blden E blo) (blden E bln) (map (zdenp E) xs) (wden E ok) m
    end.

  (* [comment removed for export] *)
  Lemma mheap_ok_ext : forall E1 E2 m bl ok,
    blden E1 bl = blden E2 bl -> wden E1 ok = wden E2 ok -> ehp E1 = ehp E2 -> ecw E1 = ecw E2 -> elb0 E1 = elb0 E2 -> elh E1 = elh E2 -> ecur E1 = ecur E2 ->
    mfact_ok E1 m (MHeap bl ok) <-> mfact_ok E2 m (MHeap bl ok).
  Proof.
    intros E1 E2 m bl ok H1 H2 H3 H4 H5 H6 H7. cbn [mfact_ok]. rewrite <- H1, <- H2, <- H3, <- H4, <- H5, <- H6, <- H7. tauto.
  Qed.
End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition regs_den (E : env) (rs : list sreg) : bvmap 5 word :=
  match rs with
  | [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
     x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31] =>
      mkR (rden E x1) (rden E x2) (rden E x3) (rden E x4) (rden E x5) (rden E x6) (rden E x7) (rden E x8)
          (rden E x9) (rden E x10) (rden E x11) (rden E x12) (rden E x13) (rden E x14) (rden E x15) (rden E x16)
          (rden E x17) (rden E x18) (rden E x19) (rden E x20) (rden E x21) (rden E x22) (rden E x23) (rden E x24)
          (rden E x25) (rden E x26) (rden E x27) (rden E x28) (rden E x29) (rden E x30) (rden E x31)
  | _ => bvmap_empty
  end.

Definition pc_den (E : env) (p : spc) : word :=
  match p with PCz z => Z_to_bv 64 z | PCret r => ret_pc (rden E r) end.

(* [comment removed for export] *)
Record gl := GL {
  g_L : asan_layout;
  g_CS : Z -> Prop;
  g_F : bvmap 5 word;
  g_fc : bv 32;
  g_m0 : mem;              (* [comment removed for export] *)
  g_me : mem               (* [comment removed for export] *)
}.

Section StOk.
  Variable segs : list Segment.
  Variable G : gl.
  Variable C : lxcfg.

  Definition ms_den (E : env) (ss : sstate) (m : mem) : machine_state :=
    MS (regs_den E (s_rs ss)) (g_F G) (pc_den E (s_pc ss)) (g_fc G) None m (seg_rom segs).

  (* [comment removed for export] *)
  Definition refm (E : env) (ss : sstate) : mem := em E (s_ref ss).

  Definition st_ok (E : env) (ss : sstate) (ms : machine_state) : Prop :=
    exists m, ms = ms_den E ss m
      /\ Forall (mfact_ok segs (g_L G) (g_CS G) E m) (s_mf ss)
      /\ Forall (pfact_ok (g_CS G) E) (s_pf ss)
      /\ munch (wden E (s_W ss)) (refm E ss) m /\ wmono segs (refm E ss) m /\ mem_inv segs m
      /\ (s_same ss = true -> m = g_me G).

  (* [comment removed for export] *)
  Definition cfg_ok (E : env) : Prop :=
    match c_acc C with
    | Some A => (* [comment removed for export] *)
        cs_ok (g_L G) (g_CS G) /\ al_wf (g_L G) /\
        (zdenp E (ac_sb A) = al_sb (g_L G) /\ ac_img_lo A = al_img_lo (g_L G) /\ ac_img_hi A = al_img_hi (g_L G)
         /\ ac_got A = al_got (g_L G) /\ ac_gsb A = al_gsb (g_L G))
    | None => (* [comment removed for export] *)
        forall x, g_CS G x
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Fixpoint pf_tele (E : env) (pf : list pfact) (P : Prop) : Prop :=
    match pf with [] => P | f :: pf' => pfact_ok (g_CS G) E f -> pf_tele E pf' P end.

  Fixpoint mf_tele (E : env) (m : mem) (mf : list mfact) (P : Prop) : Prop :=
    match mf with [] => P | f :: mf' => mfact_ok segs (g_L G) (g_CS G) E m f -> mf_tele E m mf' P end.

  (* [comment removed for export] *)
  Definition leaf_oblig (E : env) (ss : sstate) (K : Model -> machine_state -> Prop) : Prop :=
    forall m : mem,
      mf_tele E m (s_mf ss)
        (pf_tele E (s_pf ss)
           (munch (wden E (s_W ss)) (refm E ss) m -> wmono segs (refm E ss) m -> mem_inv segs m ->
            (* [comment removed for export] *)
            if s_same ss then m = g_me G -> K (ecur E) (ms_den E ss m) else K (ecur E) (ms_den E ss m))).

  Fixpoint oblig (E : env) (t : rtree) (K : Model -> machine_state -> Prop) : Prop :=
    match t with
    | RLeaf ss => leaf_oblig E ss K
    | RBr c t1 t2 => (cnden E c = true -> oblig E t1 K) /\ (cnden E c = false -> oblig E t2 K)
    | RBind i t1 => forall v : Z, oblig (env_setz E i v) t1 K
    | RJoin _ nx k t1 =>
        (fix binds (E : env) (nx : positive) (k : nat) {struct k} : Prop :=
           match k with
           | O => oblig E t1 K
           | S k' => forall v : Z, binds (env_setz E nx v) (Pos.succ nx) k'
           end) E nx k
    (* [comment removed for export] *)
    | RCall _ nx k nl kl t1 =>
        (fix binds (E : env) (nx : positive) (k : nat) {struct k} : Prop :=
           match k with
           | O => (fix lbinds (E : env) (nl : positive) (kl : nat) {struct kl} : Prop :=
                     match kl with
                     | O => oblig E t1 K
                     | S kl' => forall l : list word, lbinds (env_setl E nl l) (Pos.succ nl) kl'
                     end) E nl kl
           | S k' => forall v : Z, binds (env_setz E nx v) (Pos.succ nx) k'
           end) E nx k
    (* [comment removed for export] *)
    | RCallL _ nx k nl kl nm t1 =>
        (fix binds (E : env) (nx : positive) (k : nat) {struct k} : Prop :=
           match k with
           | O => (fix lbinds (E : env) (nl : positive) (kl : nat) {struct kl} : Prop :=
                     match kl with
                     | O => forall mc mp : mem, oblig (env_setm (env_setm E nm mc) (S nm) mp) t1 K
                     | S kl' => forall l : list word, lbinds (env_setl E nl l) (Pos.succ nl) kl'
                     end) E nl kl
           | S k' => forall v : Z, binds (env_setz E nx v) (Pos.succ nx) k'
           end) E nx k
    (* [comment removed for export] *)
    | RCallM _ nx k nl kl nm t1 t2 =>
        (fix binds (E : env) (nx : positive) (k : nat) {struct k} : Prop :=
           match k with
           | O => (fix lbinds (E : env) (nl : positive) (kl : nat) {struct kl} : Prop :=
                     match kl with
                     | O => forall mc mp : mem, forall mo : Model, forall lb : list (Z * Z),
                              oblig (env_setbl (env_setcur (env_setm (env_setm E nm mc) (S nm) mp) mo) (S nm) lb) t1 K
                              /\ oblig (env_setbl (env_setcur (env_setm (env_setm E nm mc) (S nm) mp) mo) (S nm) lb) t2 K
                     | S kl' => forall l : list word, lbinds (env_setl E nl l) (Pos.succ nl) kl'
                     end) E nl kl
           | S k' => forall v : Z, binds (env_setz E nx v) (Pos.succ nx) k'
           end) E nx k
    | RMerge nx k t1 tm =>
        oblig E t1 K /\
        (fix binds (E : env) (nx : positive) (k : nat) {struct k} : Prop :=
           match k with
           | O => oblig E tm K
           | S k' => forall v : Z, binds (env_setz E nx v) (Pos.succ nx) k'
           end) E nx k
    | RPark _ => True
    | RDead => True
    | RFail _ _ => False
    end.
End StOk.
