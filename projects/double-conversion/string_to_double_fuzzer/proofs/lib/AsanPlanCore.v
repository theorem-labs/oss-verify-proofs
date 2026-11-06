(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From Stdlib Require PrimInt63 Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3B.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require AxSymExec3Sound.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module APC.
Import AX2. Import AX2B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CEIL : Z := 0x7fff7f800000.
(* [comment removed for export] *)
Definition KHI : Z := 0x10007fff8000.
(* [comment removed for export] *)
Definition FLOOR : Z := 0x2aaaaaaab000.
(* [comment removed for export] *)
Definition MBASE_MIN : Z := 0x154555557000.
(* [comment removed for export] *)
Definition PID_MAX : Z := 4194304.
(* [comment removed for export] *)
Definition STK : Z := 8388608.
Definition TOPMAX : Z := 0x7fffff800000.
Definition XTOP : Z := 0x800000000000.

Record atable : Type := AT {
  img_lo : Z; img_hi : Z;          (* [comment removed for export] *)
  n_res : nat;                     (* [comment removed for export] *)
  shadow_off : Z;                  (* [comment removed for export] *)
  a_entry : Z;                     (* [comment removed for export] *)
  rw_lo : Z; rw_len : Z;           (* [comment removed for export] *)
  ph_addr_z : Z; ph_ent_z : Z; ph_num_z : Z;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  x_imemset : Z; x_imemcpy : Z; x_memset : Z; x_memcpy : Z; x_memiszero : Z;
  (* [comment removed for export] *)
  x_istrncpy : Z; x_sealed : Z; x_popfree : Z;
  (* [comment removed for export] *)
  x_unwind : Z; x_unwind_got : Z;
  (* [comment removed for export] *)
  x_lib : Z; lib_ret : Z; lib_fp : list (Z * Z);
  (* [comment removed for export] *)
  x_envscan : Z; x_envscan_k : Z; x_pnscan : Z; x_pnscan_k : Z;
  stops_more : list Z              (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xinsideL (k : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  xinside k b1 k1 n1 b2 k2 n2.
Definition xinsideLB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  xinsideB bc b1 k1 n1 b2 k2 n2.
Lemma xinsideLB_eqf : forall fk, xinsideLB (mkbc fk) = xinsideL fk.
Proof. intros. bcfe. unfold xinsideLB, xinsideL. rewrite xinsideB_eqf. reflexivity. Qed.
#[local] Hint Rewrite xinsideLB_eqf : bceq.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.     (* [comment removed for export] *)
Variable LIMIT : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive spiece : Type := SPLit (bs : list Z) | SPBlob (k : nat).

Inductive shape : Type :=
| SNil
| SExit (code : Z)
| SEmitP (fd : Z) (ps : list spiece) (s : shape)   (* [comment removed for export] *)
| SAlt2 (a b : shape)
| SCase (e : expr) (mid : Z) (s1 s2 : shape)
| SHole (h : nat)                            (* [comment removed for export] *)
| SNext.                                     (* [comment removed for export] *)

Definition salt2 (a b : shape) : shape :=
  match a, b with SNil, _ => b | _, SNil => a | _, _ => SAlt2 a b end.

Fixpoint listZ_eqb (x y : list Z) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => Z.eqb a b && listZ_eqb x' y' | _, _ => false end.
Definition spiece_eqb (x y : spiece) : bool :=
  match x, y with SPLit a, SPLit b => listZ_eqb a b | SPBlob k, SPBlob k' => Nat.eqb k k' | _, _ => false end.
Fixpoint spieces_eqb (x y : list spiece) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => spiece_eqb a b && spieces_eqb x' y' | _, _ => false end.
Fixpoint shape_eqb (x y : shape) : bool :=
  match x, y with
  | SNil, SNil => true
  | SExit c, SExit c' => Z.eqb c c'
  | SEmitP fd ps s, SEmitP fd' ps' s' => Z.eqb fd fd' && spieces_eqb ps ps' && shape_eqb s s'
  | SAlt2 a b, SAlt2 a' b' => shape_eqb a a' && shape_eqb b b'
  | SCase e m a b, SCase e' m' a' b' => expr_eqb e e' && Z.eqb m m' && shape_eqb a a' && shape_eqb b b'
  | SHole h, SHole h' => Nat.eqb h h'
  | SNext, SNext => true
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive mkind : Type := KRW | KRWLAZY | KNONE | KNONELAZY | KFOG | KHOLE.   (* [comment removed for export] *)

Definition mkind_eqb (a b : mkind) : bool :=
  match a, b with
  | KRW, KRW | KRWLAZY, KRWLAZY | KNONE, KNONE | KNONELAZY, KNONELAZY | KFOG, KFOG | KHOLE, KHOLE => true
  | _, _ => false
  end.

(* [comment removed for export] *)
Record amap : Type := AM {
  am_base : expr;       (* [comment removed for export] *)
  am_len  : expr;       (* [comment removed for export] *)
  am_kind : mkind
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_tok_kind (k : mkind) : bool := match k with KFOG | KHOLE => true | _ => false end.
Definition is_hole (m : amap) : bool := mkind_eqb (am_kind m) KHOLE.
Definition is_fog (m : amap) : bool := is_tok_kind (am_kind m).
Definition no_fog (ms : list amap) : bool := forallb (fun m => negb (is_fog m)) ms.
Definition no_holes (ms : list amap) : bool := forallb (fun m => negb (is_hole m)) ms.


(* [comment removed for export] *)
Inductive afd : Type :=
| FdStd                                   (* [comment removed for export] *)
| FdFile (k : nat) (len off : expr)       (* [comment removed for export] *)
| FdDir.                                  (* [comment removed for export] *)

Record acs : Type := ACS {
  a_ss    : sym_state;          (* [comment removed for export] *)
  a_maps  : list amap;          (* [comment removed for export] *)
  a_totsz : Z;                  (* [comment removed for export] *)
  a_ylo   : Z;                  (* [comment removed for export] *)
  a_eager : Z;                  (* [comment removed for export] *)
  a_vis   : list (expr * expr); (* [comment removed for export] *)
  a_ghost : list (expr * expr); (* [comment removed for export] *)
  a_abytes : Z;                 (* [comment removed for export] *)
  a_brk   : expr;               (* [comment removed for export] *)
  a_fd    : afd;
  a_tidset : bool               (* [comment removed for export] *)
}.

Definition reg (cs : acs) (n : nat) : expr := nth n (s_regs (a_ss cs)) (ELit 0).
Definition kn (cs : acs) : list kentry := s_know (a_ss cs).
Definition pc (cs : acs) : Z := s_pc (a_ss cs).
Definition nxt (cs : acs) : nat := s_next (a_ss cs).

Definition with_ss (cs : acs) (ss : sym_state) : acs :=
  ACS ss (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
Definition mk_ss (p : Z) (sr : list expr) (k : list kentry) (nx : nat) : sym_state := SS p sr [] k nx.
Definition set_reg (cs : acs) (n : nat) (e : expr) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) (sr_upd (s_regs ss) n e) (s_know ss) (s_next ss)).
Definition set_pc (cs : acs) (p : Z) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss p (s_regs ss) (s_know ss) (s_next ss)).
Definition set_kn (cs : acs) (k : list kentry) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) (s_regs ss) k (s_next ss)).
Definition add_kn (cs : acs) (k : list kentry) : acs := set_kn cs (k ++ kn cs).
Definition bump (cs : acs) (d : nat) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) (s_regs ss) (s_know ss) (s_next ss + d)).
Definition set_regs (cs : acs) (sr : list expr) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) sr (s_know ss) (s_next ss)).

Definition lit_of (e : expr) : option Z := match e with ELit z => Some (z mod two64) | _ => None end.
Definition reg_lit (cs : acs) (n : nat) : option Z := lit_of (reg cs n).

(* [comment removed for export] *)
Definition eadd (a b : expr) : expr := mkAlu ALU_ADD a b.
Definition esub (a b : expr) : expr := mkAlu ALU_SUB a b.
Definition escale (c : Z) (e : expr) : expr := mkMd M_MUL (ELit c) e.
Definition eaddz (a : expr) (z : Z) : expr := mkAlu ALU_ADD a (ELit z).

(* [comment removed for export] *)
Definition V_S1 : nat := 0.     (* [comment removed for export] *)
Definition V_ARGC : nat := 1.
Definition V_ENVC : nat := 2.
Definition V_L0 : nat := 3.     (* [comment removed for export] *)
Definition V_W : nat := 4.      (* [comment removed for export] *)
Definition V_BRK : nat := 5.    (* [comment removed for export] *)
Definition V_S2 : nat := 6.     (* [comment removed for export] *)
Definition V_L1 : nat := 7.     (* [comment removed for export] *)
Definition V_UID : nat := 8.    (* [comment removed for export] *)
Definition V_HW : nat := 9.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_sp0 : expr := eadd (escale 32768 (EVar V_S1)) (escale 16 (EVar V_S2)).
(* [comment removed for export] *)
Definition e_stklo : expr := eaddz e_sp0 (- STK).
(* [comment removed for export] *)
Definition e_stkn : expr := esub (ELit XTOP) e_stklo.
Definition e_stkb : expr * Z := split_lit e_stklo.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint expr_vars (e : expr) (acc : list nat) : list nat :=
  match e with
  | ELit _ => acc
  | EVar n => if existsb (Nat.eqb n) acc then acc else n :: acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars x (expr_vars y acc)
  | EExt _ _ _ x => expr_vars x acc
  | EBlob _ _ _ _ => acc
  end.

Definition live_vars (cs : acs) : list nat :=
  let acc := fold_right expr_vars [] (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars (a_base a) (expr_vars v acc)
                                      | KZero a n => expr_vars (a_base a) (expr_vars n acc)
                                      | KBlob a n _ => expr_vars (a_base a) (expr_vars n acc)
                                      | KWr a n => expr_vars (a_base a) (expr_vars n acc)
                                      | KFill a n _ => expr_vars (a_base a) (expr_vars n acc)
                                      | KUnk a n => expr_vars (a_base a) (expr_vars n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars (am_base m) (expr_vars (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars (fst p) (expr_vars (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars (fst p) (expr_vars (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => expr_vars l (expr_vars o acc) | _ => acc end in
  expr_vars (a_brk cs) acc.

Definition all_live (live : list nat) (e : expr) : bool :=
  forallb (fun v => Nat.ltb v nx0 || existsb (Nat.eqb v) live) (expr_vars e []).

Definition kn_gc_entry (spb : expr) (spk : Z) (live : list nat) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => negb (expr_eqb b spb && Z.leb (k + Z.of_nat w) spk)
  | KZero (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KBlob (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KFill (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KUnk (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KRange e _ _ => all_live live e
  | KAlign e _ => all_live live e
  | KDisj a1 n1 a2 n2 => all_live live (a_base a1) && all_live live n1 && all_live live (a_base a2) && all_live live n2
  | _ => true
  end%bool.

Definition cs_gc_ref (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_vars cs in
  set_kn cs (List.filter (kn_gc_entry spb spk live) (kn cs)).

(* [comment removed for export] *)
Definition vkey (n : nat) : positive := Pos.of_succ_nat n.
Fixpoint expr_vars_t (e : expr) (acc : ptree unit) : ptree unit :=
  match e with
  | ELit _ => acc
  | EVar n => pt_set (vkey n) tt acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_t x (expr_vars_t y acc)
  | EExt _ _ _ x => expr_vars_t x acc
  | EBlob _ _ _ _ => acc
  end.
Definition live_vars_t (cs : acs) : ptree unit :=
  let acc := fold_right expr_vars_t PTLeaf (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars_t (a_base a) (expr_vars_t v acc)
                                      | KZero a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KBlob a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KWr a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KFill a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KUnk a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars_t (am_base m) (expr_vars_t (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => expr_vars_t l (expr_vars_t o acc) | _ => acc end in
  expr_vars_t (a_brk cs) acc.
Definition in_live_t (t : ptree unit) (v : nat) : bool :=
  match pt_get t (vkey v) with Some _ => true | None => false end.
Fixpoint expr_all_live_t (t : ptree unit) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => if Nat.ltb n nx0 then true else in_live_t t n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_all_live_t t x then expr_all_live_t t y else false
  | EExt _ _ _ x => expr_all_live_t t x
  | EBlob _ _ _ _ => true
  end.
Definition kn_gc_entry_t (spb : expr) (spk : Z) (t : ptree unit) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => negb (expr_eqb b spb && Z.leb (k + Z.of_nat w) spk)
  | KZero (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KBlob (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KFill (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KUnk (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KRange e _ _ => expr_all_live_t t e
  | KAlign e _ => expr_all_live_t t e
  | KDisj a1 n1 a2 n2 => expr_all_live_t t (a_base a1) && expr_all_live_t t n1 && expr_all_live_t t (a_base a2) && expr_all_live_t t n2
  | _ => true
  end%bool.
Definition cs_gc (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_vars_t cs in
  set_kn cs (List.filter (kn_gc_entry_t spb spk live) (kn cs)).

(* [comment removed for export] *)
Definition live_agree (acc : list nat) (t : ptree unit) : Prop :=
  forall v, existsb (Nat.eqb v) acc = in_live_t t v.
Lemma vkey_inj : forall a b, vkey a = vkey b -> a = b.
Proof. intros a b H. unfold vkey in H. apply (f_equal Pos.to_nat) in H. rewrite !Pnat.SuccNat2Pos.id_succ in H. congruence. Qed.
Lemma live_agree_var : forall acc t n,
  live_agree acc t -> live_agree (if existsb (Nat.eqb n) acc then acc else n :: acc) (pt_set (vkey n) tt t).
Proof.
  intros acc t n H v. unfold in_live_t.
  destruct (Nat.eq_dec v n) as [->|NE].
  - rewrite pt_gss. destruct (existsb (Nat.eqb n) acc) eqn:E; [exact E|]. cbn [existsb]. rewrite Nat.eqb_refl. reflexivity.
  - rewrite pt_gso by (intros HK; apply NE; apply vkey_inj; exact HK).
    fold (in_live_t t v). rewrite <- (H v).
    destruct (existsb (Nat.eqb n) acc); [reflexivity|]. cbn [existsb].
    destruct (Nat.eqb_spec v n); [contradiction|]. reflexivity.
Qed.
Lemma live_agree_expr : forall e acc t, live_agree acc t -> live_agree (expr_vars e acc) (expr_vars_t e t).
Proof.
  induction e; intros acc t H; cbn [expr_vars expr_vars_t]; try exact H; try (apply live_agree_var; exact H); auto.
Qed.
Lemma live_agree_fold : forall (X : Type) (f : X -> list nat -> list nat) (g : X -> ptree unit -> ptree unit) (l : list X) acc t,
  (forall a acc t, live_agree acc t -> live_agree (f a acc) (g a t)) ->
  live_agree acc t -> live_agree (fold_right f acc l) (fold_right g t l).
Proof. intros X f g l acc t Hfg H. induction l as [|a r IH]; [exact H|]. cbn [fold_right]. apply Hfg. exact IH. Qed.
Lemma live_vars_agree : forall cs, live_agree (live_vars cs) (live_vars_t cs).
Proof.
  intros cs. unfold live_vars, live_vars_t.
  apply live_agree_expr.
  assert (A0 : live_agree [] PTLeaf) by (intros v; unfold in_live_t; rewrite pt_get_leaf; reflexivity).
  match goal with |- live_agree (match a_fd cs with _ => _ end) _ =>
    assert (A5 : forall acc t, live_agree acc t ->
      live_agree (match a_fd cs with FdFile _ l o => expr_vars l (expr_vars o acc) | _ => acc end)
                 (match a_fd cs with FdFile _ l o => expr_vars_t l (expr_vars_t o t) | _ => t end))
      by (intros acc t H; destruct (a_fd cs); repeat apply live_agree_expr; exact H);
    apply A5 end.
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros a acc t H; destruct a as [[] ? ?|[] ?|[] ? ?| | | |[] ?| |[] ? ?|[] ?]; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  exact A0.
Qed.
Lemma forallb_expr_vars : forall P e acc,
  forallb P (expr_vars e acc) = (forallb P (expr_vars e []) && forallb P acc)%bool.
Proof.
  intros P e. induction e; intros acc; cbn [expr_vars]; try reflexivity.
  - destruct (existsb (Nat.eqb n) acc) eqn:E; cbn [existsb forallb].
    + rewrite Bool.andb_true_r. destruct (P n) eqn:Pn; [reflexivity|]. cbn [andb].
      destruct (forallb P acc) eqn:F; [|reflexivity]. exfalso.
      apply existsb_exists in E as [x [Hx Ex]]. apply Nat.eqb_eq in Ex. subst x.
      pose proof (proj1 (forallb_forall P acc) F n Hx) as C. rewrite Pn in C. discriminate.
    + rewrite Bool.andb_true_r. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.andb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.andb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.andb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.andb_assoc. reflexivity.
  - apply IHe.
Qed.
Lemma expr_all_live_t_eq : forall acc t e, live_agree acc t -> expr_all_live_t t e = all_live acc e.
Proof.
  intros acc t e H. unfold all_live. induction e; cbn [expr_all_live_t expr_vars existsb forallb]; try reflexivity.
  - rewrite <- (H n). cbn. rewrite Bool.andb_true_r. destruct (Nat.ltb n nx0); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - exact IHe.
Qed.
Lemma cs_gc_eq : forall cs, cs_gc cs = cs_gc_ref cs.
Proof.
  intros cs. unfold cs_gc, cs_gc_ref. destruct (split_lit (reg cs 2)) as [spb spk].
  f_equal. apply filter_ext. intros K.
  pose proof (live_vars_agree cs) as H.
  destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e m|e lo hi|[b kk] n|a1 n1 a2 n2|[b kk] l c|[b kk] l]; cbn [kn_gc_entry kn_gc_entry_t];
    rewrite ?(expr_all_live_t_eq _ _ _ H); reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.
Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).

(* [comment removed for export] *)
Fixpoint shape_vars_lt (b : nat) (s : shape) : bool :=
  match s with
  | SNil | SExit _ | SHole _ | SNext => true
  | SEmitP _ _ s' => shape_vars_lt b s'
  | SAlt2 x y => shape_vars_lt b x && shape_vars_lt b y
  | SCase e _ x y => expr_vars_lt b e && shape_vars_lt b x && shape_vars_lt b y
  end.
Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
  | KZero a n => saddr_vars_lt b a && expr_vars_lt b n
  | KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KImg _ _ => true
  | KAlign e _ => expr_vars_lt b e
  | KRange e _ _ => expr_vars_lt b e
  | KWr a n => saddr_vars_lt b a && expr_vars_lt b n
  | KDisj a1 n1 a2 n2 => saddr_vars_lt b a1 && expr_vars_lt b n1 && saddr_vars_lt b a2 && expr_vars_lt b n2
  | KFill a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KUnk a n => saddr_vars_lt b a && expr_vars_lt b n
  end.
Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.
Fixpoint kn_vars_lt (b : nat) (k : list kentry) : bool :=
  match k with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
Definition pairs_vars_lt (b : nat) (l : list (expr * expr)) : bool :=
  forallb (fun p => expr_vars_lt b (fst p) && expr_vars_lt b (snd p)) l.
Definition maps_vars_lt (b : nat) (ms : list amap) : bool :=
  forallb (fun m => expr_vars_lt b (am_base m) && expr_vars_lt b (am_len m)) ms.
Definition fd_vars_lt (b : nat) (f : afd) : bool :=
  match f with FdStd => true | FdFile _ l o => expr_vars_lt b l && expr_vars_lt b o | FdDir => true end.
(* [comment removed for export] *)
Definition fresh_ok (cs : acs) : bool :=
  let v := nxt cs in
  sr_vars_lt v (s_regs (a_ss cs)) && kn_vars_lt v (kn cs)
  && maps_vars_lt v (a_maps cs) && pairs_vars_lt v (a_vis cs) && pairs_vars_lt v (a_ghost cs)
  && expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && Nat.leb nx0 v.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_lfp (z : Z) : bool :=
  existsb (fun r => Z.leb (fst r) z && Z.ltb z (snd r)) (lib_fp A).
Definition lfp_apart1 (lo hi : Z) (r : Z * Z) : bool := Z.leb hi (fst r) || Z.leb (snd r) lo.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lfp_apart_rel (k : list kentry) (b : expr) (off n : Z) : bool :=
  forallb (fun r => Z.leb 0 (fst r) && Z.leb (fst r) (snd r) && Z.ltb (snd r) two64 && ranges_apart k (ELit (fst r)) 0 (snd r - fst r) b off n) (lib_fp A).
Definition lfp_apart_relB (bc : bctx) (b : expr) (off n : Z) : bool :=
  forallb (fun r => Z.leb 0 (fst r) && Z.leb (fst r) (snd r) && Z.ltb (snd r) two64 && ranges_apartB bc (ELit (fst r)) 0 (snd r - fst r) b off n) (lib_fp A).
Definition lfp_apartz (k : list kentry) (b : expr) (off n : Z) : bool :=
  match lib_fp A with
  | [] => true
  | _ => if match xlo k b, xhi k b with
            | Some lo, Some hi => forallb (lfp_apart1 (lo + off) (hi + off + n)) (lib_fp A)
            | _, _ => false
            end then true else lfp_apart_rel k b off n      (* [comment removed for export] *)
  end.
Definition lfp_apartzB (bc : bctx) (b : expr) (off n : Z) : bool :=
  match lib_fp A with
  | [] => true
  | _ => if match xloB bc b, xhiB bc b with
            | Some lo, Some hi => forallb (lfp_apart1 (lo + off) (hi + off + n)) (lib_fp A)
            | _, _ => false
            end then true else lfp_apart_relB bc b off n
  end.
Lemma lfp_apart_relB_eqf : forall fk, lfp_apart_relB (mkbc fk) = lfp_apart_rel fk.
Proof.
  intros fk. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n.
  unfold lfp_apart_relB, lfp_apart_rel. rewrite ranges_apartB_eqf. reflexivity.
Qed.
#[local] Hint Rewrite lfp_apart_relB_eqf : bceq.
Lemma lfp_apartzB_eqf : forall fk, lfp_apartzB (mkbc fk) = lfp_apartz fk.
Proof.
  intros fk. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n.
  unfold lfp_apartzB, lfp_apartz. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite lfp_apartzB_eqf : bceq.
Definition lfp_apart_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match lib_fp A with
  | [] => true
  | _ => match xhi k n with Some nh => lfp_apartz k b off nh | None => false end
  end.
Definition lfp_apart_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
  match lib_fp A with
  | [] => true
  | _ => match xhiB bc n with Some nh => lfp_apartzB bc b off nh | None => false end
  end.
Lemma lfp_apart_xB_eqf : forall fk, lfp_apart_xB (mkbc fk) = lfp_apart_x fk.
Proof.
  intros fk. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n.
  unfold lfp_apart_xB, lfp_apart_x. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite lfp_apart_xB_eqf : bceq.

(* [comment removed for export] *)
Definition log_lfp_ok (k : list kentry) (log : list sentry) : bool :=
  match lib_fp A with
  | [] => true
  | _ => forallb (fun e => match e with SE a w _ => lfp_apartz k (a_base a) (a_off a) (Z.of_nat w) end) log
  end.
(* [comment removed for export] *)
Definition log_lfp_okB (bc : bctx) (log : list sentry) : bool :=
  match lib_fp A with
  | [] => true
  | _ => forallb (fun e => match e with SE a w _ => lfp_apartzB bc (a_base a) (a_off a) (Z.of_nat w) end) log
  end.
Lemma log_lfp_okB_eqf : forall fk, log_lfp_okB (mkbc fk) = log_lfp_ok fk.
Proof. intros fk. apply functional_extensionality; intros log. unfold log_lfp_okB, log_lfp_ok. rewrite lfp_apartzB_eqf. reflexivity. Qed.

Definition run_block_ref (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let ss' := sym_execTX segs IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    if log_lfp_ok (facts_of (s_know ss')) (s_log ss') then
    match carry (s_log ss') (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
    else None
  else None.
(* [comment removed for export] *)
Definition run_block (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in                 (* [comment removed for export] *)
    let ss' := sym_execTXBI segs bc kx IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    if log_lfp_okB bc (s_log ss') then
    match carryK bc (s_log ss') (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
    else None
  else None.
Lemma run_block_eq : forall K fuel stops cs, run_block K fuel stops cs = run_block_ref K fuel stops cs.
Proof.
  intros. unfold run_block, run_block_ref. destruct (fresh_ok cs); [|reflexivity]. cbv zeta.
  rewrite (sym_execTXBI_eq segs (s_know (a_ss cs))) by reflexivity.
  rewrite log_lfp_okB_eqf.
  set (ss' := sym_execTX segs IT K fuel true stops _).
  assert (HK : s_know ss' = s_know (a_ss cs)) by (subst ss'; rewrite sym_execTX_know; reflexivity).
  rewrite <- HK.
  destruct (log_lfp_ok _ _); [|reflexivity].
  rewrite carryK_eq. reflexivity.
Qed.

Definition run_block_gc (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block K fuel stops cs with Some cs' => Some (cs_gc cs') | None => None end.

Definition kentry_eqb (x y : kentry) : bool :=
  match x, y with
  | KWord a w v, KWord a' w' v' => saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => saddr_eqb a a' && expr_eqb n n'
  | KBlob a n k, KBlob a' n' k' => saddr_eqb a a' && expr_eqb n n' && Nat.eqb k k'
  | KImg lo hi, KImg lo' hi' => Z.eqb lo lo' && Z.eqb hi hi'
  | KAlign e m, KAlign e' m' => expr_eqb e e' && Z.eqb m m'
  | KRange e lo hi, KRange e' lo' hi' => expr_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | KWr a n, KWr a' n' => saddr_eqb a a' && expr_eqb n n'
  | KDisj a1 n1 a2 n2, KDisj a1' n1' a2' n2' => saddr_eqb a1 a1' && expr_eqb n1 n1' && saddr_eqb a2 a2' && expr_eqb n2 n2'
  | KFill a n c, KFill a' n' c' => saddr_eqb a a' && expr_eqb n n' && Z.eqb c c'
  | KUnk a n, KUnk a' n' => saddr_eqb a a' && expr_eqb n n'
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint pcat (p q : positive) : positive := match p with xH => xI q | xO r => xO (pcat r q) | xI r => xI (pcat r q) end.
Fixpoint ekey (e : expr) : positive :=
  match e with
  | ELit z => zkey z
  | EVar n => Pos.of_succ_nat n
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => match a with ELit _ => ekey b | _ => ekey a end
  | EExt _ _ _ a => ekey a
  | EBlob _ k _ _ => Pos.of_succ_nat k
  end.
Definition skey2 (a : saddr) : positive := pcat (ekey (a_base a)) (zkey (a_off a)).
Definition kkey (K : kentry) : positive :=
  match K with
  | KWord a _ _ => xO (xO (xO (xO (skey2 a))))
  | KZero a _ => xI (xO (xO (xO (skey2 a))))
  | KBlob a _ _ => xO (xI (xO (xO (skey2 a))))
  | KImg lo _ => xI (xI (xO (xO (zkey lo))))
  | KAlign e m => xO (xO (xI (xO (pcat (ekey e) (zkey m)))))
  | KRange e lo hi => xI (xO (xI (xO (pcat (ekey e) (zkey (lo + hi))))))
  | KWr a _ => xO (xI (xI (xO (skey2 a))))
  | KDisj a1 _ a2 _ => xI (xI (xI (xO (pcat (ekey (a_base a1)) (pcat (ekey (a_base a2)) (zkey (a_off a1 + a_off a2)))))))
  | KFill a _ _ => xO (xO (xO (xI (skey2 a))))
  | KUnk a _ => xI (xO (xO (xI (skey2 a))))
  end.
Lemma kentry_eqb_key : forall x y, kentry_eqb x y = true -> kkey x = kkey y.
Proof.
  intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end;
    repeat match goal with
           | H : saddr_eqb _ _ = true |- _ => apply AxSymExec3Sound.AX2S.saddr_eqb_eq in H
           | H : expr_eqb _ _ = true |- _ => apply AxSymExec3Sound.AX2S.expr_eqb_eq in H
           | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
           | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
           end; subst; reflexivity.
Qed.
Definition kidx : Type := ptree (list kentry).
Definition kidx_bucket (t : kidx) (k : positive) : list kentry := match pt_get t k with Some b => b | None => [] end.
Definition mk_kidx (l : list kentry) : kidx := fold_right (fun K t => pt_set (kkey K) (K :: kidx_bucket t (kkey K)) t) PTLeaf l.
Definition mem_kidx (t : kidx) (K : kentry) : bool := existsb (fun X => kentry_eqb X K) (kidx_bucket t (kkey K)).
Definition mem_kidxL (t : kidx) (K : kentry) : bool := existsb (kentry_eqb K) (kidx_bucket t (kkey K)).
Lemma kidx_bucket_cons : forall X l k,
  kidx_bucket (mk_kidx (X :: l)) k = if Pos.eqb (kkey X) k then X :: kidx_bucket (mk_kidx l) k else kidx_bucket (mk_kidx l) k.
Proof.
  intros X l k. cbn [mk_kidx fold_right]. fold (mk_kidx l). unfold kidx_bucket at 1.
  destruct (Pos.eqb_spec (kkey X) k) as [->|NE].
  - rewrite pt_gss. reflexivity.
  - rewrite pt_gso by (intros E; apply NE; symmetry; exact E). reflexivity.
Qed.
Lemma mem_kidx_eq : forall l K, mem_kidx (mk_kidx l) K = existsb (fun X => kentry_eqb X K) l.
Proof.
  intros l K. unfold mem_kidx. induction l as [|X r IH]; [unfold kidx_bucket; cbn [mk_kidx fold_right]; rewrite pt_get_leaf; reflexivity|].
  rewrite kidx_bucket_cons. cbn [existsb]. destruct (Pos.eqb_spec (kkey X) (kkey K)) as [E|NE].
  - cbn [existsb]. rewrite IH. reflexivity.
  - rewrite IH. destruct (kentry_eqb X K) eqn:EK; [exfalso; apply NE; apply kentry_eqb_key; exact EK | reflexivity].
Qed.
Lemma mem_kidxL_eq : forall l K, mem_kidxL (mk_kidx l) K = existsb (kentry_eqb K) l.
Proof.
  intros l K. unfold mem_kidxL. induction l as [|X r IH]; [unfold kidx_bucket; cbn [mk_kidx fold_right]; rewrite pt_get_leaf; reflexivity|].
  rewrite kidx_bucket_cons. cbn [existsb]. destruct (Pos.eqb_spec (kkey X) (kkey K)) as [E|NE].
  - cbn [existsb]. rewrite IH. reflexivity.
  - rewrite IH. destruct (kentry_eqb K X) eqn:EK; [exfalso; apply NE; symmetry; apply kentry_eqb_key; exact EK | reflexivity].
Qed.
Lemma mem_kidx_feq : forall l, mem_kidx (mk_kidx l) = (fun K => existsb (fun X => kentry_eqb X K) l).
Proof. intros l. apply functional_extensionality. intros K. apply mem_kidx_eq. Qed.
Lemma mem_kidxL_feq : forall l, mem_kidxL (mk_kidx l) = (fun K => existsb (kentry_eqb K) l).
Proof. intros l. apply functional_extensionality. intros K. apply mem_kidxL_eq. Qed.

Definition amap_eqb (x y : amap) : bool :=
  expr_eqb (am_base x) (am_base y) && expr_eqb (am_len x) (am_len y) && mkind_eqb (am_kind x) (am_kind y).

Fixpoint list_eqb {T : Type} (eqb : T -> T -> bool) (x y : list T) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => eqb a b && list_eqb eqb x' y'
  | _, _ => false
  end.

Definition pair_eqb (x y : expr * expr) : bool := expr_eqb (fst x) (fst y) && expr_eqb (snd x) (snd y).

Definition afd_eqb (x y : afd) : bool :=
  match x, y with
  | FdStd, FdStd => true
  | FdDir, FdDir => true
  | FdFile k l o, FdFile k' l' o' => Nat.eqb k k' && expr_eqb l l' && expr_eqb o o'
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_apart_b (allkn : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_x allkn ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_x allkn ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_x allkn ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_x allkn ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_x allkn ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_x allkn ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_x allkn ub uk un b k l
  end.

Definition kentry_apart_bB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_xB bc ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_xB bc ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_xB bc ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_xB bc ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_xB bc ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_xB bc ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_xB bc ub uk un b k l
  end.

Lemma kentry_apart_bB_eqf : forall fk, kentry_apart_bB (mkbc fk) = kentry_apart_b fk.
Proof. intros. bcfe. unfold kentry_apart_bB, kentry_apart_b. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_apart_bB_eqf : bceq.


(* [comment removed for export] *)
Definition kentry_apart_bp (allkn : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_p allkn sp ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_p allkn sp ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_p allkn sp ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_p allkn sp ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_p allkn sp ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_p allkn sp ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_p allkn sp ub uk un b k l
  end.

Definition kentry_apart_bpB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_pB bc sp ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_pB bc sp ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_pB bc sp ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_pB bc sp ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_pB bc sp ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_pB bc sp ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_pB bc sp ub uk un b k l
  end.

Lemma kentry_apart_bpB_eqf : forall fk, kentry_apart_bpB (mkbc fk) = kentry_apart_bp fk.
Proof. intros. bcfe. unfold kentry_apart_bpB, kentry_apart_bp. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_apart_bpB_eqf : bceq.



Definition kimg_b (K : kentry) : bool := match K with KImg _ _ => true | _ => false end.

(* [comment removed for export] *)
Definition kn_unfill (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bp k sp ub uk un K) k.

Definition kn_unfillB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bpB bc sp ub uk un K) (bc_fk bc).

Lemma kn_unfillB_eqf : forall fk, kn_unfillB (mkbc fk) = kn_unfill fk.
Proof. intros. bcfe. unfold kn_unfillB, kn_unfill. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_unfillB_eqf : bceq.

Definition kn_unfillM (k : list kentry) := kn_unfillB (mkbc k).
Lemma kn_unfillM_eq : kn_unfillM = kn_unfill. Proof. apply functional_extensionality; intros k. unfold kn_unfillM. apply kn_unfillB_eqf. Qed.



(* [comment removed for export] *)
Definition kwr_b (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
(* [comment removed for export] *)
Definition kimg_hcut (ub : expr) (uk : Z) (un : expr) (lo hi : Z) : list kentry :=
  match ub, un with
  | ELit b0, ELit n0 =>
      let a := b0 mod two64 + uk in let e := a + n0 mod two64 in
      (if Z.ltb lo (Z.min a hi) then [KImg lo (Z.min a hi)] else []) ++ (if Z.ltb (Z.max e lo) hi then [KImg (Z.max e lo) hi] else [])
  | _, _ => []
  end.
Definition havoc1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_b k ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | KImg lo hi => kimg_hcut ub uk un lo hi   (* [comment removed for export] *)
       | _ => []
       end.

Definition havoc1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bB bc ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | KImg lo hi => kimg_hcut ub uk un lo hi   (* [comment removed for export] *)
       | _ => []
       end.

Lemma havoc1B_eqf : forall fk, havoc1B (mkbc fk) = havoc1 fk.
Proof. intros. bcfe. unfold havoc1B, havoc1. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite havoc1B_eqf : bceq.


Definition havoc1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bp k sp ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | KImg lo hi => kimg_hcut ub uk un lo hi   (* [comment removed for export] *)
       | _ => []
       end.

Definition havoc1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bpB bc sp ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | KImg lo hi => kimg_hcut ub uk un lo hi   (* [comment removed for export] *)
       | _ => []
       end.

Lemma havoc1pB_eqf : forall fk, havoc1pB (mkbc fk) = havoc1p fk.
Proof. intros. bcfe. unfold havoc1pB, havoc1p. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite havoc1pB_eqf : bceq.


Definition kn_havoc (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (havoc1p k sp ub uk un) k.

Definition kn_havocB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (havoc1pB bc sp ub uk un) (bc_fk bc).

Lemma kn_havocB_eqf : forall fk, kn_havocB (mkbc fk) = kn_havoc fk.
Proof. intros. bcfe. unfold kn_havocB, kn_havoc. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.

Definition kn_havocM (k : list kentry) := kn_havocB (mkbc k).
Lemma kn_havocM_eq : kn_havocM = kn_havoc. Proof. apply functional_extensionality; intros k. unfold kn_havocM. apply kn_havocB_eqf. Qed.

(* [comment removed for export] *)
Definition kn_havoc_z (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (fun K => match K with KZero _ _ => [K] | _ => havoc1p k sp ub uk un K end) k.
(* [comment removed for export] *)
Definition kn_havoc_zB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (fun K => match K with KZero _ _ => [K] | _ => havoc1pB bc sp ub uk un K end) (bc_fk bc).
Lemma kn_havoc_zB_eqf : forall fk, kn_havoc_zB (mkbc fk) = kn_havoc_z fk.
Proof. intros. bcfe. unfold kn_havoc_zB, kn_havoc_z. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_havoc_zB_eqf : bceq.



(* [comment removed for export] *)
Definition kwr_cut (k : list kentry) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcut KWr k ub uk un kb kk len.

Definition kwr_cutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcutB bc KWr ub uk un kb kk len.

Lemma kwr_cutB_eqf : forall fk, kwr_cutB (mkbc fk) = kwr_cut fk.
Proof. intros. bcfe. unfold kwr_cutB, kwr_cut. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kwr_cutB_eqf : bceq.


Definition cutout1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_b k ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cut k ub uk un kb kk len
       | _ => []
       end.

Definition cutout1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_bB bc ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma cutout1B_eqf : forall fk, cutout1B (mkbc fk) = cutout1 fk.
Proof. intros. bcfe. unfold cutout1B, cutout1. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite cutout1B_eqf : bceq.


Definition cutout1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_bp k sp ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cut k ub uk un kb kk len
       | _ => []
       end.

Definition cutout1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_bpB bc sp ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma cutout1pB_eqf : forall fk, cutout1pB (mkbc fk) = cutout1p fk.
Proof. intros. bcfe. unfold cutout1pB, cutout1p. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite cutout1pB_eqf : bceq.


Definition kn_cutout (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (cutout1p k sp ub uk un) k.

Definition kn_cutoutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (cutout1pB bc sp ub uk un) (bc_fk bc).

Lemma kn_cutoutB_eqf : forall fk, kn_cutoutB (mkbc fk) = kn_cutout fk.
Proof. intros. bcfe. unfold kn_cutoutB, kn_cutout. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_cutoutB_eqf : bceq.

Definition kn_cutoutM (k : list kentry) := kn_cutoutB (mkbc k).
Lemma kn_cutoutM_eq : kn_cutoutM = kn_cutout. Proof. apply functional_extensionality; intros k. unfold kn_cutoutM. apply kn_cutoutB_eqf. Qed.



(* [comment removed for export] *)
Definition keep_b (bs : list expr) (b : expr) : bool := existsb (expr_eqb b) bs.
Definition keep_off (rs : list (Z * Z)) (o : Z) : bool := existsb (fun r => Z.leb (fst r) o && Z.ltb o (snd r)) rs.
Definition keep_meets (rs : list (Z * Z)) (o len : Z) : bool := existsb (fun r => Z.ltb o (snd r) && Z.ltb (fst r) (o + len)) rs.
(* [comment removed for export] *)
Definition keep_cell (bs : list expr) (rs : list (Z * Z)) (b : expr) (o : Z) : bool :=
  keep_b bs b && match b, rs with ELit 0, _ :: _ => keep_off rs o | _, _ => true end.
Definition keep_run (bs : list expr) (rs : list (Z * Z)) (b : expr) (o : Z) (n : expr) : bool :=
  keep_b bs b && match b, rs with
                  | ELit 0, _ :: _ => match n with ELit len => keep_meets rs o len | _ => true end
                  | _, _ => true
                  end.
Definition keeponly1 (bs : list expr) (rs : list (Z * Z)) (K : kentry) : bool :=
  match K with
  | KWr _ _ => true                                            (* [comment removed for export] *)
  | KWord (SA b o) _ _ => keep_cell bs rs b o
  | KZero (SA b o) n | KBlob (SA b o) n _ | KFill (SA b o) n _ | KUnk (SA b o) n => keep_run bs rs b o n
  | KDisj (SA b1 _) _ (SA b2 _) _ => keep_b bs b1 && keep_b bs b2
  | KImg lo hi => match rs with [] => true | _ => keep_meets rs lo (hi - lo) end
  | _ => true
  end.
Definition kn_keeponly (k : list kentry) (bs : list expr) (rs : list (Z * Z)) : list kentry := List.filter (keeponly1 bs rs) k.

(* [comment removed for export] *)
Definition kn_keep (k : list kentry) (ws : list (expr * expr)) : list kentry :=
  let wss := map (fun w => (split_lit (fst w), xlo k (snd w))) ws in
  let test (b : expr) (o : Z) (n : option Z) : bool :=
    let mine := List.filter (fun w => expr_eqb (fst (fst w)) b) wss in
    match mine with
    | [] => true
    | _ => existsb (fun w => let wk := snd (fst w) in
                             match snd w with
                             | Some wl => Z.ltb 0 wl && Z.ltb wk (match n with Some n => o + n | None => wk + 1 end) && Z.ltb o (wk + wl)
                             | None => true
                             end) mine
    end in
  List.filter (fun K => match K with
                        | KWord (SA b o) w _ => test b o (Some (Z.of_nat w))
                        | KZero (SA b o) n => test b o (xhi k n)
                        | KBlob (SA b o) n _ => test b o (xhi k n)
                        | KFill (SA b o) n _ => test b o (xhi k n)
                        | KUnk (SA b o) n => test b o (xhi k n)
                        | _ => true
                        end) k.

(* [comment removed for export] *)
Definition kimg_cut1 (a n : Z) (K : kentry) : list kentry :=
  match K with
  | KImg lo hi =>
      if (Z.leb hi a || Z.leb (a + n) lo)%bool then [K]
      else (if Z.ltb lo a then [KImg lo a] else []) ++ (if Z.ltb (a + n) hi then [KImg (a + n) hi] else [])
  | _ => [K]
  end.
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := List.flat_map (kimg_cut1 a n) k.

(* [comment removed for export] *)
Definition kimg_clip (k : list kentry) : list kentry :=
  List.filter (fun K => match K with KImg lo hi => Z.leb (img_lo A) lo && Z.leb lo hi && Z.leb hi (img_hi A) | _ => true end) k.

(* [comment removed for export] *)
Definition kreadZ (k : list kentry) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookup segs k b off n false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
  end.

Definition kreadZB (bc : bctx) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookupB segs bc b off n false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
  end.

Lemma kreadZB_eqf : forall fk, kreadZB (mkbc fk) = kreadZ fk.
Proof. intros. bcfe. unfold kreadZB, kreadZ. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kreadZB_eqf : bceq.


(* [comment removed for export] *)
Definition kread8e (k : list kentry) (b : expr) (off : Z) : option expr :=
  match know_lookup segs k b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Definition kread8eB (bc : bctx) (b : expr) (off : Z) : option expr :=
  match know_lookupB segs bc b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Lemma kread8eB_eqf : forall fk, kread8eB (mkbc fk) = kread8e fk.
Proof. intros. bcfe. unfold kread8eB, kread8e. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kread8eB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint kwritable0 (allkn k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xlo allkn wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinsideL allkn b off (ELit n) wb wk wn)%bool then true
      else kwritable0 allkn rest b off n
  | _ :: rest => kwritable0 allkn rest b off n
  end.

Fixpoint kwritable0B (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xloB bc wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinsideLB bc b off (ELit n) wb wk wn)%bool then true
      else kwritable0B bc rest b off n
  | _ :: rest => kwritable0B bc rest b off n
  end.

Lemma kwritable0B_eqf : forall fk, kwritable0B (mkbc fk) = kwritable0 fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. 
  revert b off n. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kwritable0B kwritable0]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kwritable0B_eqf : bceq.

Definition kwritable (allkn k : list kentry) (b : expr) (off n : Z) : bool :=
  kwritable0 allkn k b off n && lfp_apartz allkn b off n.
Definition kwritableB (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : bool :=
  kwritable0B bc k b off n && lfp_apartzB bc b off n.
Lemma kwritableB_eqf : forall fk, kwritableB (mkbc fk) = kwritable fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n.
  unfold kwritableB, kwritable. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kwritableB_eqf : bceq.


Fixpoint kwritable0_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhi allkn n, xlo allkn wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideL allkn b off n wb wk wn then true
      else kwritable0_x allkn rest b off n
  | _ :: rest => kwritable0_x allkn rest b off n
  end.

Fixpoint kwritable0_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhiB bc n, xloB bc wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideLB bc b off n wb wk wn then true
      else kwritable0_xB bc rest b off n
  | _ :: rest => kwritable0_xB bc rest b off n
  end.

Lemma kwritable0_xB_eqf : forall fk, kwritable0_xB (mkbc fk) = kwritable0_x fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. 
  revert b off n. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kwritable0_xB kwritable0_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kwritable0_xB_eqf : bceq.

Definition kwritable_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  kwritable0_x allkn k b off n && lfp_apart_x allkn b off n.
Definition kwritable_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  kwritable0_xB bc k b off n && lfp_apart_xB bc b off n.
Lemma kwritable_xB_eqf : forall fk, kwritable_xB (mkbc fk) = kwritable_x fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n.
  unfold kwritable_xB, kwritable_x. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kwritable_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kzero_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideL allkn b off n zb zk zn then true
      else kzero_x allkn rest b off n
  | _ :: rest => kzero_x allkn rest b off n
  end.

Fixpoint kzero_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%bool
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideLB bc b off n zb zk zn then true
      else kzero_xB bc rest b off n
  | _ :: rest => kzero_xB bc rest b off n
  end.

Lemma kzero_xB_eqf : forall fk, kzero_xB (mkbc fk) = kzero_x fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. 
  revert b off n. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kzero_xB kzero_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kzero_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kfill_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinsideL allkn b off n zb zk zn)%bool then true
      else kfill_x allkn rest b off n c
  | _ :: rest => kfill_x allkn rest b off n c
  end.

Fixpoint kfill_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%bool
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinsideLB bc b off n zb zk zn)%bool then true
      else kfill_xB bc rest b off n c
  | _ :: rest => kfill_xB bc rest b off n c
  end.

Lemma kfill_xB_eqf : forall fk, kfill_xB (mkbc fk) = kfill_x fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. apply functional_extensionality; intros c. 
  revert b off n c. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kfill_xB kfill_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kfill_xB_eqf : bceq.



(* [comment removed for export] *)
Definition off_image_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_x k b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Definition off_image_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_xB bc b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Lemma off_image_xB_eqf : forall fk, off_image_xB (mkbc fk) = off_image_x fk.
Proof. intros. bcfe. unfold off_image_xB, off_image_x. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite off_image_xB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition flat_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match base_range k b, xlo k n, xhi k n with
  | Some (lo, hi), Some nl, Some nh => (Z.leb 0 (lo + off) && Z.leb (hi + off + nh) two64 && Z.ltb 0 nl)%bool
  | _, _, _ => false
  end.

Definition flat_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
  match base_rangeB bc b, xloB bc n, xhiB bc n with
  | Some (lo, hi), Some nl, Some nh => (Z.leb 0 (lo + off) && Z.leb (hi + off + nh) two64 && Z.ltb 0 nl)%bool
  | _, _, _ => false
  end.

Lemma flat_xB_eqf : forall fk, flat_xB (mkbc fk) = flat_x fk.
Proof. intros. bcfe. unfold flat_xB, flat_x. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite flat_xB_eqf : bceq.



(* [comment removed for export] *)
Definition ehi (k : list kentry) (e : expr) : option Z := xhi k e.
Definition elo (k : list kentry) (e : expr) : option Z := xlo k e.

(* [comment removed for export] *)
Definition len_eqb (k : list kentry) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0 k [(n, 0%Z)] [(m, 0%Z)] && lin_ge0 k [(m, 0%Z)] [(n, 0%Z)]).

Definition len_eqbB (bc : bctx) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0B bc [(n, 0%Z)] [(m, 0%Z)] && lin_ge0B bc [(m, 0%Z)] [(n, 0%Z)]).

Lemma len_eqbB_eqf : forall fk, len_eqbB (mkbc fk) = len_eqb fk.
Proof. intros. bcfe. unfold len_eqbB, len_eqb. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite len_eqbB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_diff (e f : expr) : option Z :=
  match esub e f with ELit z => Some (z mod two64) | _ => None end.

(* [comment removed for export] *)
Definition page_aligned (k : list kentry) (e : expr) : bool :=
  match e with
  | ELit z => Z.eqb (z mod 4096) 0
  | _ => Z.leb 12 (ealign k e)
  end.

Definition page_alignedB (bc : bctx) (e : expr) : bool :=
  match e with
  | ELit z => Z.eqb (z mod 4096) 0
  | _ => Z.leb 12 (ealignB bc e)
  end.

Lemma page_alignedB_eqf : forall fk, page_alignedB (mkbc fk) = page_aligned fk.
Proof. intros. bcfe. unfold page_alignedB, page_aligned. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite page_alignedB_eqf : bceq.



(* [comment removed for export] *)
Definition kn_contra (k : list kentry) : bool :=
  existsb (fun K => match K with
                    | KRange e lo hi =>
                        if Z.ltb hi lo then true else
                        match e with
                        | EVar _ => false
                        | _ => let l := lin_of e in
                               match snd l with
                               | _ :: _ :: _ =>
                                   match lin_range (erange k) (fst l) (snd l) with
                                   | Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
                                   | None => false
                                   end
                               | _ => false
                               end
                        end
                    | _ => false
                    end) k.
Definition kn_contraM (k : list kentry) : bool :=
  let bc := mkbc k in   (* [comment removed for export] *)
  existsb (fun K => match K with
                    | KRange e lo hi =>
                        if Z.ltb hi lo then true else
                        match e with
                        | EVar _ => false
                        | _ => let l := lin_of e in
                               match snd l with
                               | _ :: _ :: _ =>
                                   match lin_range (erangeB bc) (fst l) (snd l) with
                                   | Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
                                   | None => false
                                   end
                               | _ => false
                               end
                        end
                    | _ => false
                    end) k.
Lemma kn_contraM_feq : kn_contraM = kn_contra.
Proof. apply functional_extensionality; intros k. unfold kn_contraM, kn_contra. cbv zeta. rewrite erangeB_eqf. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition caller_saved : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.

Fixpoint sr_fresh (sr : list expr) (ixs : list nat) (nx : nat) : list expr :=
  match ixs with
  | [] => sr
  | i :: t => sr_fresh (sr_upd sr i (EVar nx)) t (S nx)
  end.

Definition NCS : nat := 16.

Definition ret_lit (cs : acs) : option Z :=
  match reg cs 1 with
  | ELit r => if (Z.eqb (r mod 2) 0 && Z.ltb r two64 && Z.leb 0 r)%bool then Some r else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition after_call (cs : acs) (ret : Z) (rv : option expr) (k' : list kentry) : option acs :=
  let ss := a_ss cs in
  let nx := s_next ss in
  let sr1 := sr_fresh (s_regs ss) caller_saved nx in
  let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
  if (fresh_ok cs && kn_vars_lt nx k' && match rv with Some e => expr_vars_lt nx e | None => true end)%bool
  then Some (with_ss cs (mk_ss ret sr2 k' (nx + NCS)))
  else None.
(* [comment removed for export] *)
Definition after_call2 (cs : acs) (ret : Z) (rv : option expr) (k' : list kentry) (extra : nat) : option acs :=
  let ss := a_ss cs in
  let nx := s_next ss in
  let sr1 := sr_fresh (s_regs ss) caller_saved nx in
  let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
  if (fresh_ok cs && kn_vars_lt (nx + NCS + extra) k' && match rv with Some e => expr_vars_lt nx e | None => true end)%bool
  then Some (with_ss cs (mk_ss ret sr2 k' (nx + NCS + extra)))
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition page_up (len : Z) : Z := ((len + 4095) / 4096) * 4096.

Definition is_ecall_at (cs : acs) : bool :=
  (Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 &&
  match fetch_word segs (Z_to_bv 64 (pc cs)) with
  | Some w => is_ecall w
  | None => false
  end)%bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xlo1 (k : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange k e, lin_brange k e with
         | Some (lo, _), Some (lo', _) => Some (Z.max lo lo')
         | Some (lo, _), None => Some lo
         | None, Some (lo', _) => Some lo'
         | None, None => match lin_srange k e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
         end
  end.

Definition xlo1B (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e, lin_brangeB bc e with
         | Some (lo, _), Some (lo', _) => Some (Z.max lo lo')
         | Some (lo, _), None => Some lo
         | None, Some (lo', _) => Some lo'
         | None, None => match lin_srangeB bc e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
         end
  end.

Lemma xlo1B_eqf : forall fk, xlo1B (mkbc fk) = xlo1 fk.
Proof. intros. bcfe. unfold xlo1B, xlo1. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xlo1B_eqf : bceq.


Definition xhi1 (k : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange k e, lin_brange k e with
         | Some (_, hi), Some (_, hi') => Some (Z.min hi hi')
         | Some (_, hi), None => Some hi
         | None, Some (_, hi') => Some hi'
         | None, None => match lin_srange k e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
         end
  end.

Definition xhi1B (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e, lin_brangeB bc e with
         | Some (_, hi), Some (_, hi') => Some (Z.min hi hi')
         | Some (_, hi), None => Some hi
         | None, Some (_, hi') => Some hi'
         | None, None => match lin_srangeB bc e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
         end
  end.

Lemma xhi1B_eqf : forall fk, xhi1B (mkbc fk) = xhi1 fk.
Proof. intros. bcfe. unfold xhi1B, xhi1. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xhi1B_eqf : bceq.



(* [comment removed for export] *)
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := m mod two64 in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', s + (2 ^ j - 1))
      else (e, 0)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', s1 + s2)
  | _ => (e, 0)
  end.

Definition xb2 (k : list kentry) (e : expr) : option (Z * Z) :=
  let plain := match xlo1 k e, xhi1 k e with Some lo, Some hi => Some (lo, hi) | _, _ => None end in
  let '(e', s) := deand e in
  if Z.eqb s 0 then plain else
  match xlo1 k e', xhi1 k e' with
  | Some lo', Some hi' =>
      if Z.leb s lo' then
        match plain with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some (lo' - s, hi')
        end
      else plain
  | _, _ => plain
  end.

Definition xb2B (bc : bctx) (e : expr) : option (Z * Z) :=
  let plain := match xlo1B bc e, xhi1B bc e with Some lo, Some hi => Some (lo, hi) | _, _ => None end in
  let '(e', s) := deand e in
  if Z.eqb s 0 then plain else
  match xlo1B bc e', xhi1B bc e' with
  | Some lo', Some hi' =>
      if Z.leb s lo' then
        match plain with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some (lo' - s, hi')
        end
      else plain
  | _, _ => plain
  end.

Lemma xb2B_eqf : forall fk, xb2B (mkbc fk) = xb2 fk.
Proof. intros. bcfe. unfold xb2B, xb2. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xb2B_eqf : bceq.


Definition xlo2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (lo, _) => Some lo | None => None end.

Definition xlo2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (lo, _) => Some lo | None => None end.

Lemma xlo2B_eqf : forall fk, xlo2B (mkbc fk) = xlo2 fk.
Proof. intros. bcfe. unfold xlo2B, xlo2. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xlo2B_eqf : bceq.


Definition xhi2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (_, hi) => Some hi | None => None end.

Definition xhi2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (_, hi) => Some hi | None => None end.

Lemma xhi2B_eqf : forall fk, xhi2B (mkbc fk) = xhi2 fk.
Proof. intros. bcfe. unfold xhi2B, xhi2. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xhi2B_eqf : bceq.



(* [comment removed for export] *)
Definition fact_ok (k : list kentry) (K : kentry) : bool :=
  match K with
  | KRange e lo hi =>
      match xlo2 k e, xhi2 k e with
      | Some l, Some h => Z.leb lo l && Z.leb h hi
      | _, _ => false
      end
  | KAlign e m => Z.ltb 0 m && Z.eqb m (2 ^ (Z.log2 m)) && Z.leb (Z.log2 m) (ealign k e)
  | KDisj (SA b1 k1) n1 (SA b2 k2) n2 => ranges_apart_x k b1 k1 n1 b2 k2 n2
  | _ => false
  end.
(* [comment removed for export] *)
Definition fact_okK (k : list kentry) (K : kentry) : bool :=
  match K with
  | KZero (SA b o) n => flat_x k b o n && kzero_x k k b o n
  | KWr (SA b o) n => flat_x k b o n && kwritable0_x k k b o n
  | _ => false
  end%bool.
(* [comment removed for export] *)
Definition fact_okM (k : list kentry) (K : kentry) : bool :=
  match K with
  | KRange e lo hi =>
      let bc := mkbc k in
      match xlo2B bc e, xhi2B bc e with
      | Some l, Some h => Z.leb lo l && Z.leb h hi
      | _, _ => false
      end
  | KAlign e m => Z.ltb 0 m && Z.eqb m (2 ^ (Z.log2 m)) && Z.leb (Z.log2 m) (ealignB (mkbc k) e)
  | KDisj (SA b1 k1) n1 (SA b2 k2) n2 => ranges_apart_xB (mkbc k) b1 k1 n1 b2 k2 n2
  | _ => false
  end.
Lemma fact_okM_feq : fact_okM = fact_ok.
Proof.
  apply functional_extensionality; intros k. apply functional_extensionality; intros K. unfold fact_okM, fact_ok.
  destruct K as [| | | |e m|e lo hi| |[b1 k1] n1 [b2 k2] n2| |]; try reflexivity; cbv zeta;
    rewrite ?xlo2B_eqf, ?xhi2B_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf; reflexivity.
Qed.
Definition fact_okKM (k : list kentry) (K : kentry) : bool :=
  match K with
  | KZero (SA b o) n => let bc := mkbc k in if flat_xB bc b o n then kzero_xB bc k b o n else false
  | KWr (SA b o) n => let bc := mkbc k in if flat_xB bc b o n then kwritable0_xB bc k b o n else false
  | _ => false
  end.
Lemma fact_okKM_feq : fact_okKM = fact_okK.
Proof.
  apply functional_extensionality; intros k. apply functional_extensionality; intros K. unfold fact_okKM, fact_okK.
  destruct K as [|[b o] n| | | | |[b o] n| | |]; try reflexivity; cbv zeta;
    rewrite ?flat_xB_eqf, ?kzero_xB_eqf, ?kwritable0_xB_eqf; destruct (flat_x k b o n); reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint cert_subst (k : list kentry) (cert : list (Z * expr)) (ts : list (Z * expr)) (lo hi : Z) : option (list (Z * expr) * (Z * Z)) :=
  match cert with
  | [] => Some (ts, (lo, hi))
  | (q, fe) :: r =>
      match find_range k fe with
      | Some (flo, fhi) =>
          if fact_nowrap k fe fhi then
            let l := lin_of fe in
            let ts' := sub_fact q (snd l) ts in
            if Z.leb 0 q then cert_subst k r ts' (lo + q * (flo - fst l)) (hi + q * (fhi - fst l))
            else cert_subst k r ts' (lo + q * (fhi - fst l)) (hi + q * (flo - fst l))
          else None
      | None => None
      end
  end.
(* [comment removed for export] *)
Definition lin_bound_cert (k : list kentry) (cert : list (Z * expr)) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  match cert_subst k cert ts 0 0 with
  | Some (ts', (lo0, hi0)) =>
      match lin_range (erange k) c ts' with
      | Some (lo, hi) => Some (lo + lo0, hi + hi0)
      | None => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition tight_lo (g c lo : Z) : Z := lo + (c - lo) mod g.
Definition tight_hi (g c hi : Z) : Z := hi - (hi - c) mod g.
(* [comment removed for export] *)
Definition fact_okC (k : list kentry) (K : kentry) (s : Z) (cert : list (Z * expr)) : bool :=
  match K with
  | KRange e lo hi =>
      let l := lin_of e in
      let g := ts_gcd (snd l) 0 in
      let g' := if Z.ltb 0 g then g else 1 in
      Z.ltb 0 s && ts_divisible g' (snd l)
      && match lin_bound_cert k cert (s * fst l) (List.map (fun t => (s * fst t, snd t)) (snd l)) with
         | Some (blo, bhi) =>
             (* [comment removed for export] *)
             let vlo := zceil_div blo s in let vhi := bhi / s in
             Z.leb 0 vlo && Z.ltb vhi two64
             && Z.leb lo (tight_lo g' (fst l) vlo) && Z.leb (tight_hi g' (fst l) vhi) hi
         | None => false
         end
  | _ => false
  end%bool.

(* [comment removed for export] *)
Fixpoint kread_bytes (fuel : nat) (k : list kentry) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZ k b off 1, kread_bytes f k b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Fixpoint kread_bytesB (bc : bctx) (fuel : nat) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZB bc b off 1, kread_bytesB bc f b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Lemma kread_bytesB_eqf' : forall fk fuel, kread_bytesB (mkbc fk) fuel = kread_bytes fuel fk.
Proof.
  intros fk fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
  cbn [kread_bytesB kread_bytes]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
Lemma kread_bytesB_eqf : forall fk, kread_bytesB (mkbc fk) = (fun fuel => kread_bytes fuel fk).
Proof. intros fk. apply functional_extensionality; intros fuel. apply kread_bytesB_eqf'. Qed.
#[local] Hint Rewrite kread_bytesB_eqf' kread_bytesB_eqf : bceq.


Definition node_join (cs : acs) (b : expr) (off : Z) (n : nat) : option acs :=
  if (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool then
    match kread_bytes n (kn cs) b off with
    | Some bs => Some (add_kn cs [KWord (SA b off) n (ELit (zbytes_le_to_Z bs))])
    | None => None
    end
  else None.

Fixpoint drop_ixs (ixs : list nat) (i : nat) (k : list kentry) : list kentry :=
  match k with
  | [] => []
  | K :: r => if existsb (Nat.eqb i) ixs then drop_ixs ixs (S i) r else K :: drop_ixs ixs (S i) r
  end.
(* [comment removed for export] *)
Fixpoint sorted_from (i : nat) (ixs : list nat) : bool :=
  match ixs with [] => true | x :: xs => if Nat.leb i x then sorted_from (S x) xs else false end.
Fixpoint drop_sorted (ixs : list nat) (i : nat) (k : list kentry) : list kentry :=
  match k with
  | [] => []
  | K :: r => match ixs with
              | [] => k
              | x :: xs => if Nat.eqb i x then drop_sorted xs (S i) r else K :: drop_sorted ixs (S i) r
              end
  end.
Definition drop_ixsF (ixs : list nat) (i : nat) (k : list kentry) : list kentry :=
  if sorted_from i ixs then drop_sorted ixs i k else drop_ixs ixs i k.
Lemma drop_ixs_nil : forall k i, drop_ixs [] i k = k.
Proof. induction k as [|K r IH]; intros i; [reflexivity|]. cbn [drop_ixs existsb]. rewrite IH. reflexivity. Qed.
Lemma sorted_from_none : forall ixs i j, sorted_from i ixs = true -> (j < i)%nat -> existsb (Nat.eqb j) ixs = false.
Proof.
  induction ixs as [|x xs IH]; intros i j H Hj; [reflexivity|]. cbn [sorted_from] in H. cbn [existsb].
  destruct (Nat.leb i x) eqn:E; [|discriminate]. apply Nat.leb_le in E.
  destruct (Nat.eqb_spec j x) as [->|NE]; [lia|]. cbn [orb]. apply (IH (S x) j H). lia.
Qed.
Lemma drop_ixs_skip : forall k x xs i, (x < i)%nat -> drop_ixs (x :: xs) i k = drop_ixs xs i k.
Proof.
  induction k as [|K r IH]; intros x xs i Hx; [reflexivity|]. cbn [drop_ixs existsb].
  destruct (Nat.eqb_spec i x) as [->|NE]; [lia|]. cbn [orb]. rewrite (IH x xs (S i)) by lia. reflexivity.
Qed.
Lemma drop_sorted_eq : forall k ixs i, sorted_from i ixs = true -> drop_sorted ixs i k = drop_ixs ixs i k.
Proof.
  induction k as [|K r IH]; intros ixs i H; [reflexivity|]. cbn [drop_sorted].
  destruct ixs as [|x xs]; [rewrite drop_ixs_nil; reflexivity|].
  cbn [sorted_from] in H. destruct (Nat.leb i x) eqn:E; [|discriminate]. apply Nat.leb_le in E.
  cbn [drop_ixs existsb]. destruct (Nat.eqb_spec i x) as [->|NE].
  - cbn [orb]. rewrite (drop_ixs_skip r x xs (S x)) by lia. apply IH. exact H.
  - cbn [orb]. rewrite (sorted_from_none xs (S x) i H) by lia. f_equal. apply IH.
    cbn [sorted_from]. replace (Nat.leb (S i) x) with true by (symmetry; apply Nat.leb_le; lia). exact H.
Qed.
Lemma drop_ixsF_eq : forall ixs i k, drop_ixsF ixs i k = drop_ixs ixs i k.
Proof. intros ixs i k. unfold drop_ixsF. destruct (sorted_from i ixs) eqn:E; [apply drop_sorted_eq; exact E | reflexivity]. Qed.

(* [comment removed for export] *)
Definition residue_fact (k : list kentry) (e ne : expr) : list kentry :=
  let '(e', s) := deand e in
  if Z.ltb 0 s then
    match xlo1 k e', xhi1 k e' with
    | Some lo', Some _ => if Z.leb s lo' then [KRange (esub e' ne) 0 s] else []
    | _, _ => []
    end
  else [].

Definition node_fresh (cs : acs) (r : nat) (logc : Z) (base : option expr) : option acs :=
  let k := kn cs in let c := 2 ^ logc in
  let b := match base with Some b => b | None => ELit 0 end in
  let e := esub (reg cs r) b in
  if (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign k e)
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) e && fresh_ok cs)%bool then
    match xlo2 k e, xhi2 k e with
    | Some lo, Some hi =>
        let v := nxt cs in
        let ne := escale c (EVar v) in
        let kres := residue_fact k e ne in
        let kf := KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e ne) 0 0 :: kres in
        Some (bump (set_reg (add_kn cs kf) r (eadd b ne)) 1)
    | _, _ => None
    end
  else None.

Definition residue_factB (bc : bctx) (e ne : expr) : list kentry :=
  let '(e', s) := deand e in
  if Z.ltb 0 s then
    match xlo1B bc e', xhi1B bc e' with
    | Some lo', Some _ => if Z.leb s lo' then [KRange (esub e' ne) 0 s] else []
    | _, _ => []
    end
  else [].
Lemma residue_factB_eqf : forall fk, residue_factB (mkbc fk) = residue_fact fk.
Proof. intros fk. apply functional_extensionality; intros e. apply functional_extensionality; intros ne.
       unfold residue_factB, residue_fact. rewrite xlo1B_eqf, xhi1B_eqf. reflexivity. Qed.
Definition node_freshM (cs : acs) (r : nat) (logc : Z) (base : option expr) : option acs :=
  let k := kn cs in let bc := mkbc k in let c := 2 ^ logc in
  let b := match base with Some b => b | None => ELit 0 end in
  let e := esub (reg cs r) b in
  if (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealignB bc e)
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) e && fresh_ok cs)%bool then
    match xlo2B bc e, xhi2B bc e with
    | Some lo, Some hi =>
        let v := nxt cs in
        let ne := escale c (EVar v) in
        let kres := residue_factB bc e ne in
        let kf := KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e ne) 0 0 :: kres in
        Some (bump (set_reg (add_kn cs kf) r (eadd b ne)) 1)
    | _, _ => None
    end
  else None.

Lemma node_freshM_feq : node_freshM = node_fresh.
Proof.
  apply functional_extensionality; intros cs. apply functional_extensionality; intros r. apply functional_extensionality; intros logc.
  apply functional_extensionality; intros base. unfold node_freshM, node_fresh. cbv zeta.
  rewrite ealignB_eqf, xlo2B_eqf, xhi2B_eqf, residue_factB_eqf. reflexivity.
Qed.


(* [comment removed for export] *)
Definition node_droprange (cs : acs) (b n : expr) : acs :=
  let '(bb, bk) := split_lit b in set_kn cs (kn_havocM (kn cs) bb bk n).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_bump (cs : acs) (m : nat) : option acs :=
  if Nat.leb (nxt cs) m then Some (bump cs (m - nxt cs)) else Some (bump cs 0).

(* [comment removed for export] *)
Definition node_havoc (cs : acs) (rs : list nat) : option acs :=
  if (fresh_ok cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool then
    let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (sr_fresh (s_regs ss) rs (s_next ss)) (s_know ss) (s_next ss + length rs)))
  else None.

(* [comment removed for export] *)
Fixpoint esize (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esize a + esize b)
  | EExt _ _ _ a => S (esize a)
  | _ => 1%nat
  end.
Definition bigb (K : nat) (e : expr) : bool := Nat.ltb K (esize e).
Fixpoint kn_bigsubst (K : nat) (k : list kentry) (nx : nat) : list kentry * nat :=
  match k with
  | [] => ([], 0%nat)
  | KWord a w v :: r =>
      if bigb K v then let '(r', c) := kn_bigsubst K r (S nx) in (KWord a w (EVar nx) :: r', S c)
      else let '(r', c) := kn_bigsubst K r nx in (KWord a w v :: r', c)
  | x :: r => let '(r', c) := kn_bigsubst K r nx in (x :: r', c)
  end.
Definition node_havocbig (cs : acs) (K : nat) : option acs :=
  let rs := List.filter (fun r => bigb K (reg cs r)) (seq 1 31) in
  match node_havoc cs rs with
  | Some cs1 =>
      if fresh_ok cs1 then
        let nx1 := nxt cs1 in
        let '(k', c) := kn_bigsubst K (kn cs1) nx1 in
        Some (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) k' (nx1 + c)))
      else None
  | None => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition find_containing (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinsideL k b off n (am_base m) 0 (am_len m)) ms.

Definition find_containingB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinsideLB bc b off n (am_base m) 0 (am_len m)) ms.

Lemma find_containingB_eqf : forall fk, find_containingB (mkbc fk) = find_containing fk.
Proof. intros. bcfe. unfold find_containingB, find_containing. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).

Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrlB bc b 3) (ELit (shadow_off A))) in (sb, sk, mkSrlB bc n 3).

Lemma shadow_ofB_eqf : forall fk, shadow_ofB (mkbc fk) = shadow_of fk.
Proof. intros. bcfe. unfold shadow_ofB, shadow_of. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_lazy (m : amap) : option (Z * Z) :=
  if (negb (is_fog m) && mkind_eqb (am_kind m) KRWLAZY)%bool then
    match am_base m, am_len m with
    | ELit b, ELit n => Some (b mod two64, (b mod two64 + n mod two64)%Z)
    | _, _ => None
    end
  else None.
Definition hull_pair_ok (off L Le H He : Z) : bool :=
  Z.leb L off && Z.ltb ((L - 1) / 8 + off) Le && Z.leb L Le && Z.leb Le H && Z.leb H He
  && Z.eqb (He mod 8) 0 && Z.leb H (He / 8 + off) && Z.ltb ((XTOP - 1) / 8 + off) He && Z.leb He XTOP.
Definition hull_host (k : list kentry) (ms : list amap) (bb : expr) (bk : Z) (n : expr) : bool :=
  existsb (fun m1 => match lit_lazy m1 with
    | Some (L, Le) => existsb (fun m2 => match lit_lazy m2 with
        | Some (H, He) =>
            hull_pair_ok (shadow_off A) L Le H He
            && ranges_apart_x k bb bk n (ELit L) 0 (ELit (He - L))
            && match xhi k bb, xhi k n with
               | Some bh, Some nh =>
                   (* [comment removed for export] *)
                   (if Z.leb (bh + bk + nh) XTOP then true else lin_ge0 k [(ELit XTOP, 0%Z)] [(bb, bk); (n, 0%Z)])
                   && Z.leb 0 (match xlo k bb with Some bl => bl + bk | None => -1 end)
               | _, _ => false
               end
        | None => false end) ms
    | None => false end) ms.

Definition hull_hostB (bc : bctx) (ms : list amap) (bb : expr) (bk : Z) (n : expr) : bool :=
  existsb (fun m1 => match lit_lazy m1 with
    | Some (L, Le) => existsb (fun m2 => match lit_lazy m2 with
        | Some (H, He) =>
            hull_pair_ok (shadow_off A) L Le H He
            && ranges_apart_xB bc bb bk n (ELit L) 0 (ELit (He - L))
            && match xhiB bc bb, xhiB bc n with
               | Some bh, Some nh =>
                   (if Z.leb (bh + bk + nh) XTOP then true else lin_ge0B bc [(ELit XTOP, 0%Z)] [(bb, bk); (n, 0%Z)])
                   && Z.leb 0 (match xloB bc bb with Some bl => bl + bk | None => -1 end)
               | _, _ => false
               end
        | None => false end) ms
    | None => false end) ms.

Lemma hull_hostB_eqf : forall fk, hull_hostB (mkbc fk) = hull_host fk.
Proof. intros. bcfe. unfold hull_hostB, hull_host. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite hull_hostB_eqf : bceq.

(* [comment removed for export] *)
Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in
  let '(bb, bk) := split_lit b in
  if (flat_x k sb sk sn
      && (match find_containing k ms [KRWLAZY] sb sk sn with Some _ => true | None => false end
          || hull_host k ms bb bk n))%bool
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].

Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_ofB bc b n in
  let '(bb, bk) := split_lit b in
  if (flat_xB bc sb sk sn
      && (match find_containingB bc ms [KRWLAZY] sb sk sn with Some _ => true | None => false end
          || hull_hostB bc ms bb bk n))%bool
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].

Lemma shadow_factsB_eqf : forall fk, shadow_factsB (mkbc fk) = shadow_facts fk.
Proof. intros. bcfe. unfold shadow_factsB, shadow_facts. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite shadow_factsB_eqf : bceq.



(* [comment removed for export] *)
Definition vis_cost (nhi : Z) : Z := nhi + nhi / 8 + 16384.

(* [comment removed for export] *)
Definition vis_add_ref (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
  let k0 := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k0 b n in
  match xhi k0 n with
  | Some nhi =>
  if (Z.leb 3 (ealign k0 b) && Z.leb 3 (ealign k0 n) && flat_x k0 bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p)
                           && ranges_apart_x k0 bb bk n pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_vis cs)
      (* [comment removed for export] *)
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_ghost cs)
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts k0 (a_maps cs) b n ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.
(* [comment removed for export] *)
Definition vis_add (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
  let k0 := kn cs in let bc := mkbc k0 in   (* [comment removed for export] *)
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  (* [comment removed for export] *)
  let sp1 := mk_sprepB bc bb bk n in let sp2 := mk_sprepB bc sb sk sn in
  match xhiB bc n with
  | Some nhi =>
  if (Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p)
                           && ranges_apart_pB bc sp1 bb bk n pb pk (snd p) && ranges_apart_pB bc sp2 sb sk sn pb pk (snd p)) (a_vis cs)
      (* [comment removed for export] *)
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p) && ranges_apart_pB bc sp2 sb sk sn pb pk (snd p)) (a_ghost cs)
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_factsB bc (a_maps cs) b n ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.

Lemma forallb_ext_apc : forall (T : Type) (f g : T -> bool) (l : list T), (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros T f g l H. induction l as [|x r IH]; [reflexivity|]. cbn [forallb]. rewrite H, IH. reflexivity. Qed.
Lemma vis_add_eq : forall cs b n k, vis_add cs b n k = vis_add_ref cs b n k.
Proof.
  intros. unfold vis_add, vis_add_ref. unfold ehi, elo. cbv zeta.
  rewrite ?ealignB_eqf, ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?shadow_factsB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?ranges_apart_pB_eqf, ?mk_sprepB_eqf.
  destruct (split_lit b) as [bb bk]. destruct (shadow_of (kn cs) b n) as [[sb sk] sn].
  destruct (xhi (kn cs) n) as [nhi|]; [|reflexivity].
  assert (E1 : forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                 flat_x (kn cs) pb pk (snd p) && ranges_apart_p (kn cs) (mk_sprep (kn cs) bb bk n) bb bk n pb pk (snd p)
                 && ranges_apart_p (kn cs) (mk_sprep (kn cs) sb sk sn) sb sk sn pb pk (snd p))%bool (a_vis cs)
             = forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                 flat_x (kn cs) pb pk (snd p) && ranges_apart_x (kn cs) bb bk n pb pk (snd p) && ranges_apart_x (kn cs) sb sk sn pb pk (snd p))%bool (a_vis cs)).
  { apply forallb_ext_apc. intros p. destruct (split_lit (fst p)) as [pb pk]. rewrite !AxSymExec3Sound.AX2S.ranges_apart_p_eq. reflexivity. }
  assert (E2 : forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                 flat_x (kn cs) pb pk (snd p) && ranges_apart_p (kn cs) (mk_sprep (kn cs) sb sk sn) sb sk sn pb pk (snd p))%bool (a_ghost cs)
             = forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                 flat_x (kn cs) pb pk (snd p) && ranges_apart_x (kn cs) sb sk sn pb pk (snd p))%bool (a_ghost cs)).
  { apply forallb_ext_apc. intros p. destruct (split_lit (fst p)) as [pb pk]. rewrite !AxSymExec3Sound.AX2S.ranges_apart_p_eq. reflexivity. }
  rewrite E1, E2. reflexivity.
Qed.


(* [comment removed for export] *)
Fixpoint find_disj (k : list kentry) (b1 b2 : expr) : option (expr * Z * expr * expr * Z * expr) :=
  match k with
  | [] => None
  | KDisj (SA c1 o1) n1 (SA c2 o2) n2 :: r =>
      if (expr_eqb c1 b1 && expr_eqb c2 b2)%bool then Some (c1, o1, n1, c2, o2, n2)
      else if (expr_eqb c1 b2 && expr_eqb c2 b1)%bool then Some (c2, o2, n2, c1, o1, n1)
      else find_disj r b1 b2
  | _ :: r => find_disj r b1 b2
  end.
(* [comment removed for export] *)
Definition disj_side_fact (k : list kentry) (cA : expr) (oA : Z) (nA : expr) (cB : expr) (oB : Z) : option kentry :=
  match xlo2 k nA, base_range k cB with
  | Some n, Some (_, bhi) => if (Z.leb 0 n && Z.leb n (bhi + oB))%bool then Some (KRange (esub (eaddz cB oB) (eaddz cA oA)) n (bhi + oB)) else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition disj_side_xfact (k : list kentry) (cA : expr) (oA : Z) (nA : expr) (cB : expr) (oB : Z) : list kentry :=
  match nA, base_range k cB with
  | ELit _, _ => []
  | _, Some (_, bhi) => [KRange (esub (eaddz cB oB) (eadd (eaddz cA oA) nA)) 0 (bhi + oB)]
  | _, None => []
  end.
(* [comment removed for export] *)
Definition side_infeasible (k : list kentry) (cA : expr) (oA : Z) (nA : expr) (cB : expr) (oB : Z) : bool :=
  match base_range k cA, xlo2 k nA, base_range k cB with
  | Some (alo, _), Some n, Some (_, bhi) => Z.ltb (bhi + oB) (alo + oA + n)
  | _, _, _ => false
  end.
(* [comment removed for export] *)
Definition node_casedisj (cs : acs) (b1 b2 : expr) : option (option acs * option acs) :=
  let k := kn cs in
  match find_disj k b1 b2 with
  | Some (c1, o1, n1, c2, o2, n2) =>
      if (flat_x k c1 o1 n1 && flat_x k c2 o2 n2)%bool then
        let a1 := if side_infeasible k c1 o1 n1 c2 o2 then Some None
                  else match disj_side_fact k c1 o1 n1 c2 o2 with Some K1 => Some (Some (add_kn cs (K1 :: disj_side_xfact k c1 o1 n1 c2 o2))) | None => None end in
        let a2 := if side_infeasible k c2 o2 n2 c1 o1 then Some None
                  else match disj_side_fact k c2 o2 n2 c1 o1 with Some K2 => Some (Some (add_kn cs (K2 :: disj_side_xfact k c2 o2 n2 c1 o1))) | None => None end in
        match a1, a2 with
        | Some x1, Some x2 => Some (x1, x2)
        | _, _ => None
        end
      else None
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition end47 (k : list kentry) (b n : expr) (h m : Z) : bool :=
  if Z.leb (h + m) (2 ^ 47) then true
  else if Z.ltb (h + m) two64 then match xhi k (eadd b n) with Some e => Z.leb e (2 ^ 47) | None => false end
  else false.
Definition end47B (bc : bctx) (b n : expr) (h m : Z) : bool :=
  if Z.leb (h + m) (2 ^ 47) then true
  else if Z.ltb (h + m) two64 then match xhiB bc (eadd b n) with Some e => Z.leb e (2 ^ 47) | None => false end
  else false.
Lemma end47B_eqf : forall fk, end47B (mkbc fk) = end47 fk.
Proof. intros. bcfe. unfold end47B, end47. rewrite ?xhiB_eqf. reflexivity. Qed.
Definition node_shdisj_ref (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_of k b1 n1 in let '(sb2, sk2, sn2) := shadow_of k b2 n2 in
  if (Z.leb 3 (ealign k b1) && Z.leb 3 (ealign k n1) && Z.leb 3 (ealign k b2) && Z.leb 3 (ealign k n2)
      && flat_x k c1 o1 n1 && flat_x k c2 o2 n2 && flat_x k sb1 sk1 sn1 && flat_x k sb2 sk2 sn2
      && match xhi k b1, xhi k n1, xhi k b2, xhi k n2 with
         | Some h1, Some m1, Some h2, Some m2 => end47 k b1 n1 h1 m1 && end47 k b2 n2 h2 m2   (* [comment removed for export] *)
         | _, _, _, _ => false end
      && ranges_apart_x k c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.
(* [comment removed for export] *)
Definition node_shdisj (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_ofB bc b1 n1 in let '(sb2, sk2, sn2) := shadow_ofB bc b2 n2 in
  if (Z.leb 3 (ealignB bc b1) && Z.leb 3 (ealignB bc n1) && Z.leb 3 (ealignB bc b2) && Z.leb 3 (ealignB bc n2)
      && flat_xB bc c1 o1 n1 && flat_xB bc c2 o2 n2 && flat_xB bc sb1 sk1 sn1 && flat_xB bc sb2 sk2 sn2
      && match xhiB bc b1, xhiB bc n1, xhiB bc b2, xhiB bc n2 with
         | Some h1, Some m1, Some h2, Some m2 => end47B bc b1 n1 h1 m1 && end47B bc b2 n2 h2 m2
         | _, _, _, _ => false end
      && ranges_apart_xB bc c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.

Lemma node_shdisj_eq : forall cs b1 n1 b2 n2, node_shdisj cs b1 n1 b2 n2 = node_shdisj_ref cs b1 n1 b2 n2.
Proof. intros. unfold node_shdisj, node_shdisj_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?end47B_eqf. reflexivity. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_len_ref (cs : acs) : option (expr * Z * Z) :=
  match reg_lit cs 11 with
  | Some len => if Z.ltb 0 len then Some (ELit (page_up len), page_up len, page_up len) else None
  | None =>
      let le := reg cs 11 in let k := kn cs in
      match xlo k le, xhi k le with
      | Some lo, Some hi =>
          if (Z.ltb 0 lo && Z.leb 12 (ealign k le) && Z.leb hi (2 ^ 46))%bool then Some (le, lo, hi) else None
      | _, _ => None
      end
  end.
(* [comment removed for export] *)
Definition mmap_len (cs : acs) : option (expr * Z * Z) :=
  match reg_lit cs 11 with
  | Some len => if Z.ltb 0 len then Some (ELit (page_up len), page_up len, page_up len) else None
  | None =>
      let le := reg cs 11 in let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match xloB bc le, xhiB bc le with
      | Some lo, Some hi =>
          if (Z.ltb 0 lo && Z.leb 12 (ealignB bc le) && Z.leb hi (2 ^ 46))%bool then Some (le, lo, hi) else None
      | _, _ => None
      end
  end.

Lemma mmap_len_eq : forall cs, mmap_len cs = mmap_len_ref cs.
Proof. intros. unfold mmap_len, mmap_len_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?xhiB_eqf, ?xloB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Fixpoint inside_maps (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinsideL k b off len (am_base m) 0 (am_len m)) || inside_maps k rest b off len
  end.

Fixpoint inside_mapsB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinsideLB bc b off len (am_base m) 0 (am_len m)) || inside_mapsB bc rest b off len
  end.

Lemma inside_mapsB_eqf : forall fk, inside_mapsB (mkbc fk) = inside_maps fk.
Proof.
  intros fk. apply functional_extensionality; intros ms. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros len. 
  revert b off len. induction ms as [|m rest IH]; intros; bcfe; [reflexivity|].
  cbn [inside_mapsB inside_maps]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite inside_mapsB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_ivs (ms : list amap) : list (Z * Z) :=
  flat_map (fun m => if is_fog m then [] else
                     match am_base m, am_len m with
                     | ELit b, ELit n => [(b mod two64, (b mod two64 + n mod two64)%Z)]
                     | _, _ => []
                     end) ms.
Fixpoint ziv_insert (p : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => [p]
  | q :: r => if Z.leb (fst p) (fst q) then p :: l else q :: ziv_insert p r
  end.
Definition ziv_sort (l : list (Z * Z)) : list (Z * Z) := fold_right ziv_insert [] l.
(* [comment removed for export] *)
Fixpoint ziv_merge (l : list (Z * Z)) (acc : option (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => match acc with Some c => [c] | None => [] end
  | (b, e) :: r =>
      match acc with
      | None => ziv_merge r (Some (b, e))
      | Some (cb, ce) => if Z.leb b ce then ziv_merge r (Some (cb, Z.max ce e)) else (cb, ce) :: ziv_merge r (Some (b, e))
      end
  end.
Definition lit_hulls (ms : list amap) : list (Z * Z) := ziv_merge (ziv_sort (lit_ivs ms)) None.

(* [comment removed for export] *)
Definition in_lit_hull (ms : list amap) (lo hi : Z) : bool :=
  existsb (fun iv => Z.leb (fst iv) lo && Z.leb hi (snd iv)) (lit_hulls ms).
Definition safe_range (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhi k len, base_range k b with
    | Some lh, Some (lo, hi) =>
        (lin_ge0 k [(b, off)] [(e_sp0, (- STK)%Z)] && Z.leb 0 (lo + off) && Z.leb (hi + off + lh) two64)   (* [comment removed for export] *)
        || (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
        || (Z.ltb 0 lh && in_lit_hull ms (lo + off) (hi + off + lh))             (* [comment removed for export] *)
    | _, _ => false
    end) || inside_maps k ms b off len)%bool.

Definition safe_rangeB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhiB bc len, base_rangeB bc b with
    | Some lh, Some (lo, hi) =>
        (lin_ge0B bc [(b, off)] [(e_sp0, (- STK)%Z)] && Z.leb 0 (lo + off) && Z.leb (hi + off + lh) two64)   (* [comment removed for export] *)
        || (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
        || (Z.ltb 0 lh && in_lit_hull ms (lo + off) (hi + off + lh))             (* [comment removed for export] *)
    | _, _ => false
    end) || inside_mapsB bc ms b off len)%bool.

Lemma safe_rangeB_eqf : forall fk, safe_rangeB (mkbc fk) = safe_range fk.
Proof. intros. bcfe. unfold safe_rangeB, safe_range. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite safe_rangeB_eqf : bceq.



Definition grant_keep_b (k : list kentry) (ms : list amap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => Nat.leb w 8 && safe_range k ms b o (ELit (Z.of_nat w))
  | KZero (SA b o) l => safe_range k ms b o l
  | KBlob (SA b o) l _ => safe_range k ms b o l
  | KImg lo hi => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b o) n => safe_range k ms b o n
  | KFill (SA b o) l _ => safe_range k ms b o l
  | KUnk (SA b o) l => safe_range k ms b o l
  end.

Definition grant_keep_bB (bc : bctx) (ms : list amap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => Nat.leb w 8 && safe_rangeB bc ms b o (ELit (Z.of_nat w))
  | KZero (SA b o) l => safe_rangeB bc ms b o l
  | KBlob (SA b o) l _ => safe_rangeB bc ms b o l
  | KImg lo hi => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b o) n => safe_rangeB bc ms b o n
  | KFill (SA b o) l _ => safe_rangeB bc ms b o l
  | KUnk (SA b o) l => safe_rangeB bc ms b o l
  end.

Lemma grant_keep_bB_eqf : forall fk, grant_keep_bB (mkbc fk) = grant_keep_b fk.
Proof. intros. bcfe. unfold grant_keep_bB, grant_keep_b. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite grant_keep_bB_eqf : bceq.



Definition kn_grant_filter (k : list kentry) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_b k ms) k).

Lemma forallb_ext_filter : forall (T : Type) (f g : T -> bool) (l : list T), (forall x, f x = g x) -> List.filter f l = List.filter g l.
Proof. intros T f g l H. induction l as [|x r IH]; [reflexivity|]. cbn [List.filter]. rewrite H, IH. reflexivity. Qed.
(* [comment removed for export] *)
Definition in_lit_hullH (hulls : list (Z * Z)) (lo hi : Z) : bool :=
  existsb (fun iv => Z.leb (fst iv) lo && Z.leb hi (snd iv))%bool hulls.
Fixpoint inside_mapsLB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => if (if is_fog m then false else xinsideLB bc b off len (am_base m) 0 (am_len m)) then true
                 else inside_mapsLB bc rest b off len
  end.
Lemma inside_mapsLB_eq : forall bc ms b off len, inside_mapsLB bc ms b off len = inside_mapsB bc ms b off len.
Proof.
  intros bc ms b off len. induction ms as [|m rest IH]; [reflexivity|]. cbn [inside_mapsLB inside_mapsB]. rewrite IH.
  destruct (is_fog m); reflexivity.
Qed.
Definition safe_rangeF (bc : bctx) (hulls : list (Z * Z)) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match xhiB bc len, base_rangeB bc b with
  | Some lh, Some (lo, hi) =>
      if (if Z.leb (img_lo A) (lo + off) then Z.leb (hi + off + lh) (img_hi A) else false) then true
      else if (if Z.ltb 0 lh then in_lit_hullH hulls (lo + off) (hi + off + lh) else false) then true
      else if (if Z.leb 0 (lo + off) then (if Z.leb (hi + off + lh) two64 then lin_ge0B bc [(b, off)] [(e_sp0, (- STK)%Z)] else false) else false) then true
      else inside_mapsLB bc ms b off len
  | _, _ => inside_mapsLB bc ms b off len
  end.
Lemma safe_rangeF_eq : forall bc ms b off len, safe_rangeF bc (lit_hulls ms) ms b off len = safe_rangeB bc ms b off len.
Proof.
  intros bc ms b off len. unfold safe_rangeF, safe_rangeB, in_lit_hull, in_lit_hullH. rewrite inside_mapsLB_eq.
  destruct (xhiB bc len) as [lh|]; [|reflexivity]. destruct (base_rangeB bc b) as [[lo hi]|]; [|reflexivity].
  match goal with |- context [existsb ?f ?l] => destruct (existsb f l) end;
  destruct (lin_ge0B bc [(b, off)] [(e_sp0, (- STK)%Z)]), (Z.leb 0 (lo + off)), (Z.leb (hi + off + lh) two64),
           (Z.leb (img_lo A) (lo + off)), (Z.leb (hi + off + lh) (img_hi A)), (Z.ltb 0 lh),
           (inside_mapsB bc ms b off len); reflexivity.
Qed.
Definition grant_keep_bF (bc : bctx) (hulls : list (Z * Z)) (ms : list amap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => if Nat.leb w 8 then safe_rangeF bc hulls ms b o (ELit (Z.of_nat w)) else false
  | KZero (SA b o) l => safe_rangeF bc hulls ms b o l
  | KBlob (SA b o) l _ => safe_rangeF bc hulls ms b o l
  | KImg lo hi => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b o) n => safe_rangeF bc hulls ms b o n
  | KFill (SA b o) l _ => safe_rangeF bc hulls ms b o l
  | KUnk (SA b o) l => safe_rangeF bc hulls ms b o l
  end.
Lemma grant_keep_bF_eq : forall bc ms K, grant_keep_bF bc (lit_hulls ms) ms K = grant_keep_bB bc ms K.
Proof.
  intros bc ms K. destruct K as [[b o] w v|[b o] l|[b o] l bk|lo hi|e m|e lo hi|[b o] n|a1 n1 a2 n2|[b o] l c|[b o] l];
    cbn [grant_keep_bF grant_keep_bB]; rewrite ?safe_rangeF_eq; reflexivity.
Qed.
Definition kn_grant_filterB (bc : bctx) (ms : list amap) : list kentry :=
  let hulls := lit_hulls ms in
  kimg_clip (List.filter (grant_keep_bF bc hulls ms) (bc_fk bc)).

Lemma kn_grant_filterB_eqf : forall fk, kn_grant_filterB (mkbc fk) = kn_grant_filter fk.
Proof.
  intros. bcfe. unfold kn_grant_filterB, kn_grant_filter. cbv zeta.
  rewrite (forallb_ext_filter _ (grant_keep_bF (mkbc fk) (lit_hulls x) x) (grant_keep_bB (mkbc fk) x)) by (intros K; apply grant_keep_bF_eq).
  autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kn_grant_filterB_eqf : bceq.



(* [comment removed for export] *)
Definition gap_ok (cs : acs) (nhi : Z) : bool :=
  let cnt := Z.of_nat (n_res A + length (a_maps cs))%nat in
  Z.leb (FLOOR + nhi + a_totsz cs + cnt * (nhi + 4095)) CEIL.

Definition budget_ok (cs : acs) (extra : Z) : bool :=
  Z.leb (a_eager cs + a_abytes cs + extra) LIMIT.

(* [comment removed for export] *)
Definition kdisj_new (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else
                     match am_base m with
                     | ELit _ => []
                     | mb => [KDisj (SA mb 0) (am_len m) (SA nb 0) ne]
                     end) ms.

(* [comment removed for export] *)
Definition kdisj_all (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else [KDisj (SA (am_base m) 0) (am_len m) (SA nb 0) ne]) ms.

Definition kdisj_hulls (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  List.map (fun h => KDisj (SA (ELit (fst h)) 0) (ELit (snd h - fst h)) (SA nb 0) ne) (lit_hulls ms).

(* [comment removed for export] *)
Fixpoint res_chain (l : list (word * word)) (lo hi : Z) : bool :=
  match l with
  | [] => Z.leb hi lo
  | (b, sz) :: r => (Z.leb (bv_unsigned b) lo && res_chain r (Z.max lo (bv_unsigned b + bv_unsigned sz)) hi)%bool
  end.

(* [comment removed for export] *)
Definition with_maps0 (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
Definition add_entry (cs : acs) (sr : list expr) (k' : list kentry) (nx' : nat)
           (m : amap) (nhi : Z) (eager : bool) (ylo' : Z) : acs :=
  ACS (mk_ss (pc cs + 4) sr k' nx')
      (m :: a_maps cs) (a_totsz cs + nhi) ylo'
      (if eager then a_eager cs + nhi else a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition null_kend (base ne : expr) (nlo : Z) : list kentry :=
  match ne with
  | ELit _ => []
  | _ => [KRange (eadd base ne) (4096 + nlo) TOPMAX]   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition null_facts (ms : list amap) (v : nat) (base ne : expr) (nlo : Z) : list kentry :=
  KRange (EVar v) 1 ((TOPMAX - nlo) / 4096)
  :: KRange (esub e_sp0 (eadd base ne)) STK XTOP
  :: KDisj (SA (fst e_stkb) (snd e_stkb)) e_stkn (SA base 0) ne   (* [comment removed for export] *)
  :: null_kend base ne nlo
  ++ kdisj_all ms base ne ++ kdisj_hulls ms base ne
  ++ [KDisj (SA (ELit (img_lo A)) 0) (ELit (img_hi A - img_lo A)) (SA base 0) ne].

Definition mmap_null (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && no_holes (a_maps cs))%bool then     (* [comment removed for export] *)
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let kfacts := null_facts (a_maps cs) v base ne nlo in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filterB (mkbc (kn cs)) (a_maps cs) in   (* [comment removed for export] *)
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs - 2 * nhi) in
        if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
      else None
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NOTOP : Z := -1.
Definition below_top (k : list kentry) (a ne : expr) (ahi nhi top : Z) : bool :=
  Z.leb (ahi + nhi) top
  || (Z.leb nhi XTOP && (Z.ltb top 0 || lin_ge0 k [(e_sp0, 0%Z)] [(a, 0%Z); (ne, 0%Z); (ELit STK, 0%Z)])).

(* [comment removed for export] *)
Definition fixed_args (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && (Z.leb (img_hi A) alo || Z.ltb top 0) && below_top k a ne ahi nhi top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.
Definition below_topB (bc : bctx) (a ne : expr) (ahi nhi top : Z) : bool :=
  (if Z.leb (ahi + nhi) top then true   (* [comment removed for export] *)
   else (if Z.leb nhi XTOP then (if Z.ltb top 0 then true else lin_ge0B bc [(e_sp0, 0%Z)] [(a, 0%Z); (ne, 0%Z); (ELit STK, 0%Z)]) else false)).
Lemma below_topB_eqf : forall fk, below_topB (mkbc fk) = below_top fk.
Proof. intros fk. unfold below_topB, below_top. rewrite lin_ge0B_eqf. reflexivity. Qed.
Definition fixed_argsM (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let bc := mkbc k in let a := reg cs 10 in   (* [comment removed for export] *)
  let '(b, off) := split_lit a in
  match mmap_len cs, xloB bc a, xhiB bc a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_alignedB bc a && Z.ltb 0 alo && (Z.leb (img_hi A) alo || Z.ltb top 0) && below_topB bc a ne ahi nhi top && flat_xB bc b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.
Lemma fixed_argsM_feq : fixed_argsM = fixed_args.
Proof.
  apply functional_extensionality; intros cs. apply functional_extensionality; intros top. unfold fixed_argsM, fixed_args. cbv zeta.
  rewrite xloB_eqf, xhiB_eqf, page_alignedB_eqf, below_topB_eqf, flat_xB_eqf. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition same_val (k : list kentry) (a b : expr) : bool :=
  if expr_eqb a b then true
  else (if lin_ge0 k [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 k [(b, 0%Z)] [(a, 0%Z)] else false).
(* [comment removed for export] *)
Definition find_hole (k : list kentry) (ms : list amap) (a ne : expr) : option amap :=
  List.find (fun m => is_hole m && same_val k a (am_base m) && same_val k ne (am_len m)) ms.
(* [comment removed for export] *)
Definition unhole (ms : list amap) (h : amap) : list amap :=
  List.map (fun m => if (is_hole m && amap_eqb m h)%bool then AM (am_base m) (am_len m) KFOG else m) ms.

(* [comment removed for export] *)
Definition mmap_fixed_grant (cs : acs) (ms0 : list amap) (b : expr) (off : Z) (ne : expr) (nhi : Z)
           (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  let m := AM a ne kind in
  let kmem := [KWr (SA b off) ne; KZero (SA b off) ne] in
  let ksh := if mkind_eqb kind KRWLAZY then flat_map (fun p => shadow_facts k [m] (fst p) (snd p)) (a_vis cs) else [] in
  let k' := ksh ++ kn_grant_filterB (mkbc k) ms0 in   (* [comment removed for export] *)
  let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
  if visible then vis_add cs1 a ne (kmem ++ kn cs1) else Some cs1.

Definition mmap_fixed_free (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  (* [comment removed for export] *)
  match fixed_args cs KHI, no_holes (a_maps cs) with
  | Some (b, off, ne, nlo, nhi), true =>
      if (no_fog (a_maps cs)
          && forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
          && (negb eager || budget_ok cs nhi)
          && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
      then mmap_fixed_grant cs (a_maps cs) b off ne nhi kind eager visible
      else None
  | _, _ =>
      (* [comment removed for export] *)
      match fixed_args cs CEIL with
      | Some (b, off, ne, nlo, nhi) =>
          match find_hole k (a_maps cs) a ne with
          | Some h =>
              let ms0 := unhole (a_maps cs) h in
              if (forallb (fun m => negb (is_hole m) || ranges_apart_x k b off ne (am_base m) 0 (am_len m)) ms0
                  && (negb eager || budget_ok cs nhi)
                  && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
              then mmap_fixed_grant cs ms0 b off ne nhi kind eager visible
              else None
          | None => None
          end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition kn_rezero (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => kentry_apart_bp k sp ub uk un K
                        | _ => true
                        end) k.

Definition kn_rezeroB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => kentry_apart_bpB bc sp ub uk un K
                        | _ => true
                        end) (bc_fk bc).

Lemma kn_rezeroB_eqf : forall fk, kn_rezeroB (mkbc fk) = kn_rezero fk.
Proof. intros. bcfe. unfold kn_rezeroB, kn_rezero. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_rezeroB_eqf : bceq.

Definition kn_rezeroM (k : list kentry) := kn_rezeroB (mkbc k).
Lemma kn_rezeroM_eq : kn_rezeroM = kn_rezero. Proof. apply functional_extensionality; intros k. unfold kn_rezeroM. apply kn_rezeroB_eqf. Qed.



(* [comment removed for export] *)
Definition rekind (ms : list amap) (m : amap) : list amap :=
  map (fun m' => if amap_eqb m' m then AM (am_base m') (am_len m') KRW else m') ms.

(* [comment removed for export] *)
Inductive fixed_in_arm := ArmE | ArmF | ArmG.

(* [comment removed for export] *)
Definition fixed_in_args_ref (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args cs NOTOP with
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containing k (a_maps cs) kinds b off ne with
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition fixed_in_args (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_argsM cs NOTOP with
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containingB bc (a_maps cs) kinds b off ne with
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.

Lemma fixed_in_args_eq : forall cs arm, fixed_in_args cs arm = fixed_in_args_ref cs arm.
Proof. intros. unfold fixed_in_args, fixed_in_args_ref. unfold ehi, elo. rewrite ?find_containingB_eqf, ?fixed_argsM_feq. reflexivity. Qed.


(* [comment removed for export] *)
Definition mmap_fixed_in_ref (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfill k b off ne)
                  | ArmF => kimg_clip (kn_rezero k b off ne)
                  | ArmG => kimg_clip (kn_cutout k b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None
  | None => None
  end.
(* [comment removed for export] *)
Definition mmap_fixed_in (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfillB bc b off ne)
                  | ArmF => kimg_clip (kn_rezeroB bc b off ne)
                  | ArmG => kimg_clip (kn_cutoutB bc b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None
  | None => None
  end.

Lemma mmap_fixed_in_eq : forall cs arm, mmap_fixed_in cs arm = mmap_fixed_in_ref cs arm.
Proof. intros. unfold mmap_fixed_in, mmap_fixed_in_ref. unfold ehi, elo. rewrite ?kn_cutoutB_eqf, ?kn_rezeroB_eqf, ?kn_unfillB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Definition ENOMEM_RET : Z := two64 - 12.

(* [comment removed for export] *)
Definition refuse (cs : acs) : acs := set_pc (set_reg cs 10 (ELit ENOMEM_RET)) (pc cs + 4).

(* [comment removed for export] *)
Definition replace_entry (ms : list amap) (m : amap) (pieces : list amap) : list amap :=
  flat_map (fun m' => if amap_eqb m' m then pieces else [m']) ms.

(* [comment removed for export] *)
Definition dest_lfact (a mb : expr) (lne : bool) : kentry :=
  if lne then KRange (esub a mb) 1 (two64 - 1) else KRange (esub a mb) 0 0.
Definition dest_rfact (a ne mb ml : expr) (rne : bool) : kentry :=
  if rne then KRange (esub (eadd mb ml) (eadd a ne)) 1 (two64 - 1) else KRange (esub (eadd mb ml) (eadd a ne)) 0 0.

Definition mmap_destroyed_with_ref (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) (lne rne : bool) : acs :=
  let k := kn cs in
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
  let hp := if hole then [AM a ne KHOLE] else [] in      (* [comment removed for export] *)
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutout k b off ne)) (s_next ss))
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
(* [comment removed for export] *)
Definition mmap_destroyed_with (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) (lne rne : bool) : acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
  let hp := if hole then [AM a ne KHOLE] else [] in      (* [comment removed for export] *)
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutoutB bc b off ne)) (s_next ss))
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

Lemma mmap_destroyed_with_eq : forall hole cs b off ne m lne rne, mmap_destroyed_with hole cs b off ne m lne rne = mmap_destroyed_with_ref hole cs b off ne m lne rne.
Proof. intros. unfold mmap_destroyed_with, mmap_destroyed_with_ref. unfold ehi, elo. rewrite ?kn_cutoutB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Definition dest_cases (cs : acs) (ne : expr) (m : amap) : list (bool * bool) :=
  let k := kn cs in
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let ls := if lin_ge0 k [(a, -1)] [(mb, 0)] then [true]                                   (* [comment removed for export] *)
            else if (expr_eqb a mb || lin_ge0 k [(mb, 0)] [(a, 0)])%bool then [false]    (* [comment removed for export] *)
            else [true; false] in
  let rs := if lin_ge0 k [(mb, -1); (ml, 0)] [(a, 0); (ne, 0)] then [true]                 (* [comment removed for export] *)
            else if lin_ge0 k [(a, 0); (ne, 0)] [(mb, 0); (ml, 0)] then [false]           (* [comment removed for export] *)
            else [true; false] in
  flat_map (fun l => map (fun r => (l, r)) rs) ls.
Definition dest_casesM (cs : acs) (ne : expr) (m : amap) : list (bool * bool) :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let ls := if lin_ge0B bc [(a, -1)] [(mb, 0)] then [true]                                   (* [comment removed for export] *)
            else if (expr_eqb a mb || lin_ge0B bc [(mb, 0)] [(a, 0)])%bool then [false]    (* [comment removed for export] *)
            else [true; false] in
  let rs := if lin_ge0B bc [(mb, -1); (ml, 0)] [(a, 0); (ne, 0)] then [true]                 (* [comment removed for export] *)
            else if lin_ge0B bc [(a, 0); (ne, 0)] [(mb, 0); (ml, 0)] then [false]           (* [comment removed for export] *)
            else [true; false] in
  flat_map (fun l => map (fun r => (l, r)) rs) ls.
Lemma dest_casesM_feq : dest_casesM = dest_cases.
Proof.
  apply functional_extensionality; intros cs. apply functional_extensionality; intros ne. apply functional_extensionality; intros m.
  unfold dest_casesM, dest_cases. cbv zeta. rewrite lin_ge0B_eqf. reflexivity.
Qed.

Definition mmap_destroyed (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) : list acs :=
  map (fun lr => mmap_destroyed_with hole cs b off ne m (fst lr) (snd lr)) (dest_casesM cs ne m).

(* [comment removed for export] *)
Definition mmap_gate (cs : acs) : option (Z * Z * bool) :=
  match reg_lit cs 17, reg_lit cs 12, reg_lit cs 13, reg_lit cs 14, reg_lit cs 15 with
  | Some 222, Some prot, Some flags, Some m1, Some 0 =>
      if negb (Z.eqb m1 (two64 - 1)) then None
      else Some (prot, flags, match reg_lit cs 10 with Some 0 => true | _ => false end)
  | _, _, _, _, _ => None
  end.


Definition EEXIST_RET : Z := two64 - 17.
Definition refuse_e (cs : acs) (ret : Z) : acs := set_pc (set_reg cs 10 (ELit ret)) (pc cs + 4).


Definition mmap_nr_occ_ref (cs : acs) : option (acs * acs) :=
  match fixed_args cs NOTOP with
  | Some (b, off, ne, nlo, nhi) =>
      match find_containing (kn cs) (a_maps cs) [KRW; KRWLAZY; KNONE; KNONELAZY] b off ne with
      | Some _ => Some (refuse cs, refuse_e cs EEXIST_RET)
      | None => None
      end
  | None => None
  end.

Definition mmap_nr_occ (cs : acs) : option (acs * acs) :=
  match fixed_argsM cs NOTOP with
  | Some (b, off, ne, nlo, nhi) =>
      match find_containingB (mkbc (kn cs)) (a_maps cs) [KRW; KRWLAZY; KNONE; KNONELAZY] b off ne with
      | Some _ => Some (refuse cs, refuse_e cs EEXIST_RET)
      | None => None
      end
  | None => None
  end.
Lemma mmap_nr_occ_eq : forall cs, mmap_nr_occ cs = mmap_nr_occ_ref cs.
Proof. intros. unfold mmap_nr_occ, mmap_nr_occ_ref. rewrite ?find_containingB_eqf, ?fixed_argsM_feq. reflexivity. Qed.


Definition node_mmap2 (cs : acs) : option (acs * acs) :=
  match mmap_gate cs with
  | Some (prot, flags, isnull) =>
      let g := if isnull then
                 match prot, flags with
                 | 3, 0x22 => mmap_null cs KRW true true               
                 | 3, 0x4022 => mmap_null cs KRWLAZY false true        
                 | 0, 0x22 => mmap_null cs KNONE false false           
                 | 0, 0x4022 => mmap_null cs KNONELAZY false false     
                 | _, _ => None
                 end
               else
                 match prot, flags with
                 | 3, 0x4032 => mmap_fixed_free cs KRWLAZY false false  
                 | 3, 0x32 => mmap_fixed_free cs KRW true true          
                 | 0, 0x4032 => mmap_fixed_free cs KNONELAZY false false 
                 | 0, 0x32 => mmap_fixed_free cs KNONE false false      
                 
                 | 3, 0x104022 | 3, 0x104032 => mmap_fixed_free cs KRWLAZY false false   
                 | 0, 0x104022 | 0, 0x104032 => mmap_fixed_free cs KNONELAZY false false 
                 | 3, 0x100022 | 3, 0x100032 => mmap_fixed_free cs KRW true true           
                 | 0, 0x100022 | 0, 0x100032 => mmap_fixed_free cs KNONE false false       
                 | _, _ => None
                 end in
      match g with
      | Some csG => Some (refuse cs, csG)
      | None =>   
          if isnull then None else
          match prot, flags with
          | 0, 0x104022 => mmap_nr_occ cs
          | _, _ => None
          end
      end
  | None => None
  end.


Definition node_mmapin_ref (hole : bool) (cs : acs) : option (acs * acs * list acs) :=
  match mmap_gate cs with
  | Some (prot, flags, false) =>
      let arm := match prot, flags with
                 | 3, 0x32 => Some ArmE
                 | 3, 0x4032 => Some ArmF
                 | 0, 0x32 => Some ArmG
                 | _, _ => None
                 end in
      match arm with
      | Some arm =>
          match fixed_in_args cs arm, mmap_fixed_in cs arm with
          | Some (b, off, ne, nlo, nhi, m), Some csO => Some (refuse cs, csO, mmap_destroyed hole cs b off ne m)
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

Definition fixed_argsB (bc : bctx) (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xloB bc a, xhiB bc a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_alignedB bc a && Z.ltb 0 alo && (Z.leb (img_hi A) alo || Z.ltb top 0) && below_topB bc a ne ahi nhi top && flat_xB bc b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.
Definition fixed_in_argsB (bc : bctx) (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_argsB bc cs NOTOP with
  | Some (b, off, ne, nlo, nhi) =>
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containingB bc (a_maps cs) kinds b off ne with
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.

Definition mmap_fixed_in_okB (bc : bctx) (cut : list kentry) (cs : acs) (arm : fixed_in_arm) (b : expr) (off : Z) (ne : expr) (nhi : Z) (m : amap) : option acs :=
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfillB bc b off ne)
                  | ArmF => kimg_clip (kn_rezeroB bc b off ne)
                  | ArmG => cut
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None.
Definition mmap_destroyed_withK (hole : bool) (cut : list kentry) (cs : acs) (ne : expr) (m : amap) (lne rne : bool) : acs :=
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
  let hp := if hole then [AM a ne KHOLE] else [] in
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: cut) (s_next ss))
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
Definition dest_casesB (bc : bctx) (cs : acs) (ne : expr) (m : amap) : list (bool * bool) :=
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let ls := if lin_ge0B bc [(a, -1)] [(mb, 0)] then [true]
            else if (expr_eqb a mb || lin_ge0B bc [(mb, 0)] [(a, 0)])%bool then [false]
            else [true; false] in
  let rs := if lin_ge0B bc [(mb, -1); (ml, 0)] [(a, 0); (ne, 0)] then [true]
            else if lin_ge0B bc [(a, 0); (ne, 0)] [(mb, 0); (ml, 0)] then [false]
            else [true; false] in
  flat_map (fun l => map (fun r => (l, r)) rs) ls.
Definition node_mmapin (hole : bool) (cs : acs) : option (acs * acs * list acs) :=
  match mmap_gate cs with
  | Some (prot, flags, false) =>
      let arm := match prot, flags with
                 | 3, 0x32 => Some ArmE
                 | 3, 0x4032 => Some ArmF
                 | 0, 0x32 => Some ArmG
                 | _, _ => None
                 end in
      match arm with
      | Some arm =>
          let bc := mkbc (kn cs) in
          match fixed_in_argsB bc cs arm with
          | Some (b, off, ne, nlo, nhi, m) =>
              let cut := kimg_clip (kn_cutoutB bc b off ne) in
              match mmap_fixed_in_okB bc cut cs arm b off ne nhi m with
              | Some csO => Some (refuse cs, csO, map (fun lr => mmap_destroyed_withK hole cut cs ne m (fst lr) (snd lr)) (dest_casesB bc cs ne m))
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | _ => None
  end.
Lemma fixed_in_argsB_eq : forall cs arm, fixed_in_argsB (mkbc (kn cs)) cs arm = fixed_in_args cs arm.
Proof. reflexivity. Qed.
Lemma node_mmapin_eq : forall hole cs, node_mmapin hole cs = node_mmapin_ref hole cs.
Proof.
  intros hole cs. unfold node_mmapin, node_mmapin_ref.
  destruct (mmap_gate cs) as [[[prot flags] [|]]|]; try reflexivity. cbv zeta.
  match goal with |- match ?X with Some _ => _ | None => _ end = _ => destruct X as [ar|] end; [|reflexivity].
  rewrite fixed_in_argsB_eq. unfold mmap_fixed_in.
  destruct (fixed_in_args cs ar) as [[[[[[b off] ne] nlo] nhi] m]|]; [|reflexivity].
  reflexivity.
Qed.




Definition node_mprotect_ref (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs NOTOP with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      match find_containing k (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfill k b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.

Definition node_mprotect (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_argsM cs NOTOP with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   
      match find_containingB bc (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfillB bc b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
Lemma node_mprotect_eq : forall cs, node_mprotect cs = node_mprotect_ref cs.
Proof. intros. unfold node_mprotect, node_mprotect_ref. unfold ehi, elo. rewrite ?find_containingB_eqf, ?kn_unfillB_eqf, ?fixed_argsM_feq. reflexivity. Qed.



Definition node_mprotect2 (cs : acs) : option (acs * acs) :=
  match node_mprotect cs with Some csG => Some (refuse cs, csG) | None => None end.



Definition amap_match (k : list kentry) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqb k n (am_len m))%bool.

Definition amap_matchB (bc : bctx) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqbB bc n (am_len m))%bool.

Lemma amap_matchB_eqf : forall fk, amap_matchB (mkbc fk) = amap_match fk.
Proof. intros. bcfe. unfold amap_matchB, amap_match. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite amap_matchB_eqf : bceq.




Definition node_munmap_ref (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_x k pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_x k pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_match k b ne) (a_maps cs) && page_aligned k b && flat_x k bb bk ne
          && match xhi k b with Some hi => Z.ltb (hi + nhi) two64 | None => false end
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in
                               Z.leb 3 (ealign k (fst p)) && Z.leb 3 (ealign k (snd p))
                               && xinsideL k pb pk (snd p) bb bk ne && kzero_x k k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in kn_unfill kk sb sk sn) gone (kn_unfill k bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_match k b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

Definition node_munmap (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in let bc := mkbc k in   
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_xB bc pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_xB bc pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_matchB bc b ne) (a_maps cs) && page_alignedB bc b && flat_xB bc bb bk ne
          && match xhiB bc b with Some hi => Z.ltb (hi + nhi) two64 | None => false end
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in
                               Z.leb 3 (ealignB bc (fst p)) && Z.leb 3 (ealignB bc (snd p))
                               && xinsideLB bc pb pk (snd p) bb bk ne && kzero_xB bc k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in kn_unfillM kk sb sk sn) gone (kn_unfillB bc bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_matchB bc b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

Lemma node_munmap_eq : forall cs, node_munmap cs = node_munmap_ref cs.
Proof. intros. unfold node_munmap, node_munmap_ref. unfold ehi, elo. rewrite ?amap_matchB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?kn_unfillB_eqf, ?kzero_xB_eqf, ?page_alignedB_eqf, ?ranges_apart_xB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?xinsideLB_eqf, ?xinsideB_eqf, ?kn_unfillM_eq. reflexivity. Qed.





Definition brk_req (cs : acs) : option Z :=
  match lit_diff (reg cs 10) (a_brk cs) with
  | Some d => if (Z.ltb 0 d && Z.eqb (d mod 4096) 0 && Z.leb d (2 ^ 40))%bool then Some d else None
  | None => None
  end.


Definition brk_base_ok (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (page_aligned k b
   && match xlo k b, xhi k b with
      | Some lo, Some hi => Z.ltb 0 lo && Z.leb (img_hi A) lo && Z.leb (hi + d) KHI
      | _, _ => false
      end)%bool.


Definition brk_grow_possible (cs : acs) (d : Z) : bool :=
  (brk_base_ok cs d && no_fog (a_maps cs) && budget_ok cs d)%bool.


Definition kdisj_brk (ms : list amap) (nb : saddr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else [KDisj (SA (am_base m) 0) (am_len m) nb ne]) ms.


Definition brk_grow_blocked (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (brk_base_ok cs d
   && existsb (fun m => negb (is_fog m)
                        && lin_ge0 k [(am_base m, -1); (am_len m, 0)] [(b, 0)]      
                        && lin_ge0 k [(b, d - 1)] [(am_base m, 0)])               
              (a_maps cs))%bool.


Definition node_brk1 (cs : acs) : option acs :=
  match reg_lit cs 17 with
  | Some 214 =>
      let ok := match reg_lit cs 10 with
                | Some 0 => true
                | _ => match brk_req cs with Some d => brk_grow_blocked cs d | None => false end
                end in
      if ok then Some (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) else None
  | _ => None
  end.


Definition node_brk2 (cs : acs) : option (acs * acs) :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
      if (brk_grow_possible cs d && expr_vars_lt (nxt cs) (reg cs 10) && flat_x k bb bk (ELit (d + 4096)))%bool then   
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        let k' := kdisj_brk (a_maps cs) (SA bb bk) (ELit (d + 4096)) ++ kn_grant_filterB (mkbc k) (a_maps cs) in   
        let ss := a_ss cs in
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) in
        match vis_add csB b (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB) with
        | Some csB' => Some (csA, csB')
        | None => None
        end
      else None
  | _, _ => None
  end.



Definition node_settid (cs : acs) : option acs :=
  match reg_lit cs 17 with
  | Some 96 =>
      if (negb (a_tidset cs) && fresh_ok cs)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (EVar v)) (KRange (EVar v) 1 (PID_MAX - 1) :: s_know ss) (S v))
                 (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) true)
      else None
  | _ => None
  end.

Definition node_exit (cs : acs) : option Z :=
  match reg_lit cs 17, reg_lit cs 10 with
  | Some 94, Some code => Some (Z.land code 255)
  | Some 93, Some code => Some (Z.land code 255)
  | _, _ => None
  end.



Fixpoint list_set_nth {T} (i : nat) (x : T) (l : list T) : list T :=
  match l, i with
  | [], _ => []
  | _ :: r, O => x :: r
  | y :: r, S i' => y :: list_set_nth i' x r
  end.
Fixpoint list_insert_nth {T} (i : nat) (x : T) (l : list T) : list T :=
  match i, l with
  | O, _ => x :: l
  | S i', y :: r => y :: list_insert_nth i' x r
  | S _, [] => [x]
  end.

Definition fog_token (sz : Z) : amap := AM (ELit 0) (ELit sz) KFOG.

Definition with_maps (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).


Definition node_fog (cs : acs) (i : nat) (sz : Z) : option acs :=
  match nth_error (a_maps cs) i with
  | Some m =>
      if (Z.leb 0 sz && Z.ltb sz two64
          && match xhi (kn cs) (am_len m) with Some h => Z.leb h sz | None => false end)%bool
      then Some (with_maps cs (list_set_nth i (fog_token sz) (a_maps cs)))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition node_fognew (cs : acs) (i : nat) (sz : Z) : option acs :=
  if (Nat.leb i (length (a_maps cs)) && Z.leb 0 sz && Z.ltb sz two64)%bool
  then Some (with_maps cs (list_insert_nth i (fog_token sz) (a_maps cs)))
  else None.

(* [comment removed for export] *)
Definition node_ghost (cs : acs) (b n : expr) : option acs :=
  match xhi (kn cs) n with
  | Some nhi =>
      if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
      then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs ++ [(b, n)])
                     (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition vis_here (b n : expr) (p : expr * expr) : bool := (expr_eqb (fst p) b && expr_eqb (snd p) n)%bool.

Definition node_unvis_ref (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k b n in
  match xhi k b, xhi k n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealign k b) && Z.leb 3 (ealign k n) && flat_x k bb bk n && Z.leb (bh + nh) XTOP (* [comment removed for export] *)
          && flat_x k sb sk sn && kzero_x k k sb sk sn)%bool
      then
        let k1 := kn_unfill k bb bk n in
        let k2 := kn_unfill k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_viscut (cs : acs) (b : expr) (N n1 : Z) : option acs :=
  let k := kn cs in
  let '(bb, bk) := split_lit b in
  if (existsb (vis_here b (ELit N)) (a_vis cs)
      && Z.leb 12 (ealign k b) && Z.eqb (n1 mod 4096) 0 && Z.ltb 0 n1 && Z.ltb n1 N && Z.ltb N XTOP
      && flat_x k bb bk (ELit N)
      && Z.leb (a_eager cs + a_abytes cs + 4096) LIMIT)%bool
  then
    Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
              ((b, ELit n1) :: (eaddz b n1, ELit (N - n1)) :: List.filter (fun p => negb (vis_here b (ELit N) p)) (a_vis cs))
              (a_ghost cs) (a_abytes cs + 4096) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None.

(* [comment removed for export] *)
Definition node_unvis (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match xhiB bc b, xhiB bc n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n && Z.leb (bh + nh) XTOP
          && flat_xB bc sb sk sn && kzero_xB bc k sb sk sn)%bool
      then
        let k1 := kn_unfillB bc bb bk n in
        let k2 := kn_unfillM k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

Lemma node_unvis_eq : forall cs b n, node_unvis cs b n = node_unvis_ref cs b n.
Proof. intros. unfold node_unvis, node_unvis_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?kn_unfillB_eqf, ?kzero_xB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?kn_unfillM_eq. reflexivity. Qed.


(* [comment removed for export] *)
Definition node_havocbrk (cs : acs) (lo hi : Z) : option acs :=
  match xlo (kn cs) (a_brk cs), xhi (kn cs) (a_brk cs) with
  | Some l, Some h =>
      if (fresh_ok cs && Z.leb lo l && Z.leb h hi)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (S v))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (EVar v) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_intro (cs : acs) (lo hi : Z) : option acs :=
  if (fresh_ok cs && Z.leb 0 lo && Z.leb lo hi && Z.ltb hi two64)%bool then
    let v := nxt cs in let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (S v)))
  else None.

(* [comment removed for export] *)
Definition SPIN_WORD : Z := 0x6f.
Definition node_spin (cs : acs) : bool :=
  (Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 &&
  match fetch_word segs (Z_to_bv 64 (pc cs)) with
  | Some w => Z.eqb (bv_unsigned w) SPIN_WORD
  | None => false
  end)%bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition summary_fill_ref (cs : acs) (entry : Z) (cmax : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in
      let c8 := c mod 256 in
      match xlo k ne, xhi k ne, xhi k dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_x k k db dk ne && kwritable_x k k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_x k k db dk ne then
              let k1 := kn_havoc k0 db dk ne in
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vis_below_pg (k : list kentry) (dst p : expr) (v : expr * expr) : bool :=
  (Z.eqb (shadow_off A mod 512) 0 && Z.leb 12 (ealign k (fst v)) && Z.leb 12 (ealign k (snd v)) && Z.leb 9 (ealign k dst)
   && match xhi k p with Some ph => Z.ltb (8 * ph) two64 | None => false end
   && lin_ge0 k [(dst, 511)] [(p, 0)]
   && lin_ge0 k [(escale 8 p, - (8 * shadow_off A))] [(fst v, 0); (snd v, 0)])%bool.

Definition vis_below_pgB (bc : bctx) (dst p : expr) (v : expr * expr) : bool :=
  (Z.eqb (shadow_off A mod 512) 0 && Z.leb 12 (ealignB bc (fst v)) && Z.leb 12 (ealignB bc (snd v)) && Z.leb 9 (ealignB bc dst)
   && match xhiB bc p with Some ph => Z.ltb (8 * ph) two64 | None => false end
   && lin_ge0B bc [(dst, 511)] [(p, 0)]
   && lin_ge0B bc [(escale 8 p, - (8 * shadow_off A))] [(fst v, 0); (snd v, 0)])%bool.
Lemma vis_below_pgB_eqf : forall fk, vis_below_pgB (mkbc fk) = vis_below_pg fk.
Proof. intros. bcfe. unfold vis_below_pgB, vis_below_pg. autorewrite with bceq. reflexivity. Qed.

Definition summary_fill0_ref (cs : acs) (entry : Z) (cmax : Z) (p q : expr) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(pb, pk) := split_lit p in
      let nt := esub (eadd dst ne) p in
      let np := esub p dst in
      match xlo k ne, xhi k ne, xhi k dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.eqb (c mod 256) 0 && Z.ltb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64
              && lin_ge0 k [(p, 0)] [(dst, 0)] && lin_ge0 k [(dst, 0); (ne, 0)] [(p, 0)]
              && Z.leb 12 (ealign k q) && lin_ge0 k [(dst, 0)] [(q, 0)] && lin_ge0 k [(q, 4095)] [(p, 0)]
              && flat_x k db dk np && flat_x k pb pk nt
              && match find_containing k (a_maps cs) [KRWLAZY] db dk ne with Some _ => true | None => false end
              && forallb (fun g => let '(gb, gk) := split_lit (fst g) in flat_x k gb gk (snd g) && ranges_apart_x k db dk np gb gk (snd g)) (a_ghost cs)
              && forallb (fun v => let '(vb, vk) := split_lit (fst v) in let '(sb, sk, sn) := shadow_of k (fst v) (snd v) in
                                   (* [comment removed for export] *)
                                   let snx := if (Z.leb 3 (ealign k (fst v)) && Z.leb 3 (ealign k (snd v)))%bool then sn else eadd sn (ELit 1) in
                                   flat_x k vb vk (snd v) && flat_x k sb sk sn && flat_x k sb sk snx
                                   && ranges_apart_x k db dk np vb vk (snd v)
                                   && (ranges_apart_x k db dk np sb sk snx || kwritable_x k k sb sk snx || vis_below_pg k dst p v)) (a_vis cs)
              && off_image_x k db dk ne && lfp_apart_x k db dk ne
              && kwritable_x k k pb pk nt)%bool
          then after_call cs ret (Some dst) (KZero (SA pb pk) nt :: kn_havoc_z k db dk ne)
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition summary_fill0 (cs : acs) (entry : Z) (cmax : Z) (p q : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(pb, pk) := split_lit p in
      let nt := esub (eadd dst ne) p in
      let np := esub p dst in
      match xloB bc ne, xhiB bc ne, xhiB bc dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.eqb (c mod 256) 0 && Z.ltb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64
              && lin_ge0B bc [(p, 0)] [(dst, 0)] && lin_ge0B bc [(dst, 0); (ne, 0)] [(p, 0)]
              && Z.leb 12 (ealignB bc q) && lin_ge0B bc [(dst, 0)] [(q, 0)] && lin_ge0B bc [(q, 4095)] [(p, 0)]
              && flat_xB bc db dk np && flat_xB bc pb pk nt
              && match find_containingB bc (a_maps cs) [KRWLAZY] db dk ne with Some _ => true | None => false end
              && forallb (fun g => let '(gb, gk) := split_lit (fst g) in flat_xB bc gb gk (snd g) && ranges_apart_xB bc db dk np gb gk (snd g)) (a_ghost cs)
              && forallb (fun v => let '(vb, vk) := split_lit (fst v) in let '(sb, sk, sn) := shadow_ofB bc (fst v) (snd v) in
                                   (* [comment removed for export] *)
                                   let snx := if (Z.leb 3 (ealignB bc (fst v)) && Z.leb 3 (ealignB bc (snd v)))%bool then sn else eadd sn (ELit 1) in
                                   flat_xB bc vb vk (snd v) && flat_xB bc sb sk sn && flat_xB bc sb sk snx
                                   && ranges_apart_xB bc db dk np vb vk (snd v)
                                   && (if (if ranges_apart_xB bc db dk np sb sk snx then true else kwritable_xB bc k sb sk snx) then true else vis_below_pgB bc dst p v)) (a_vis cs)   (* [comment removed for export] *)
              && off_image_xB bc db dk ne && lfp_apart_xB bc db dk ne
              && kwritable_xB bc k pb pk nt)%bool
          then after_call cs ret (Some dst) (KZero (SA pb pk) nt :: kn_havoc_zB bc db dk ne)
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.

Lemma summary_fill0_eq : forall cs entry cmax p q, summary_fill0 cs entry cmax p q = summary_fill0_ref cs entry cmax p q.
Proof.
  intros. unfold summary_fill0, summary_fill0_ref. unfold ehi, elo.
  rewrite ?vis_below_pgB_eqf, ?kn_havoc_zB_eqf, ?lfp_apart_xB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?kwritable_xB_eqf, ?off_image_xB_eqf,
          ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?lin_ge0B_eqf, ?ealignB_eqf, ?xhiB_eqf, ?xloB_eqf. reflexivity.
Qed.

(* [comment removed for export] *)
Definition summary_fill (cs : acs) (entry : Z) (cmax : Z) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in
      let c8 := c mod 256 in
      match xloB bc ne, xhiB bc ne, xhiB bc dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            (* [comment removed for export] *)
            if (if Z.eqb c8 0 then (if kzero_xB bc k db dk ne then kwritable_xB bc k db dk ne else false) else false) then after_call cs ret (Some dst) k else
            (* [comment removed for export] *)
            match (if off_image_xB bc db dk ne then Some None
                   else match dst, ne with ELit d, ELit n => Some (Some (kimg_cut k (d mod two64) n)) | _, _ => None end) with
            | None => None
            | Some ok0 =>
            if kwritable_xB bc k db dk ne then
              let k1 := match ok0 with None => kn_havocB bc db dk ne | Some k0 => kn_havocM k0 db dk ne end in
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.

Lemma summary_fill_eq : forall cs entry cmax, summary_fill cs entry cmax = summary_fill_ref cs entry cmax.
Proof.
  intros. unfold summary_fill, summary_fill_ref. unfold ehi, elo. cbv zeta.
  rewrite ?kwritable_xB_eqf, ?kzero_xB_eqf, ?off_image_xB_eqf, ?xhiB_eqf, ?xloB_eqf, ?kn_havocM_eq, ?kn_havocB_eqf.
  repeat (first [ reflexivity
                | lazymatch goal with
                  | |- match (if ?c then _ else _) with _ => _ end = _ => destruct c
                  | |- match (match (match ?x with _ => _ end) with _ => _ end) with _ => _ end = _ => destruct x
                  | |- match (match ?x with _ => _ end) with _ => _ end = _ => destruct x
                  | |- (if ?c then _ else _) = _ => destruct c
                  | |- match ?x with _ => _ end = _ => destruct x
                  end ]).
Qed.


(* [comment removed for export] *)
Fixpoint copy_facts (fuel : nat) (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8e k sb sk with Some _ => true | None => match kread_bytes 8 k sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8e k sb sk with
               | Some v => Some v
               | None => match kread_bytes 8 k sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_facts f k sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookup segs k sb sk 1 false [] [], copy_facts f k sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.

Fixpoint copy_factsB (bc : bctx) (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8eB bc sb sk with Some _ => true | None => match kread_bytesB bc 8 sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8eB bc sb sk with
               | Some v => Some v
               | None => match kread_bytesB bc 8 sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_factsB bc f sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookupB segs bc sb sk 1 false [] [], copy_factsB bc f sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.

Lemma copy_factsB_eqf' : forall fk fuel, copy_factsB (mkbc fk) fuel = copy_facts fuel fk.
Proof.
  intros fk fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
  cbn [copy_factsB copy_facts]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
Lemma copy_factsB_eqf : forall fk, copy_factsB (mkbc fk) = (fun fuel => copy_facts fuel fk).
Proof. intros fk. apply functional_extensionality; intros fuel. apply copy_factsB_eqf'. Qed.
#[local] Hint Rewrite copy_factsB_eqf' copy_factsB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kblob_len_ok (nb : expr) (nlo : Z) (ne : expr) : bool :=
  match nb with ELit n0 => Z.ltb 0 n0 && Z.leb n0 nlo | _ => false end || expr_eqb nb ne.
Definition kblob_prefix (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (nlo : Z) (ne : expr) : list kentry :=
  match List.find (fun K => match K with
                             | KBlob (SA b o) nb _ => expr_eqb b sb && Z.eqb o sk && kblob_len_ok nb nlo ne
                             | _ => false
                             end) k with
  | Some (KBlob _ nb j) => [KBlob (SA db dk) nb j]
  | _ => []
  end.

Definition summary_copy_ref (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xlo k ne, xhi k ne, xhi k dst, xhi k src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_x k k db dk ne && ranges_apart_x k db dk ne sb sk ne)%bool then
              let k1 := kn_havoc k0 db dk ne in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_x k k sb sk ne && flat_x k sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ne ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_x k k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_x k sb sk ne)%bool then
                         match copy_facts (Z.to_nat nhi) k sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ k1)
                         | None => havoc_src
                         end
                       else havoc_src
                   | _ => havoc_src
                   end
            else None
            end
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_copy (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xloB bc ne, xhiB bc ne, xhiB bc dst, xhiB bc src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            (* [comment removed for export] *)
            match (if off_image_xB bc db dk ne then Some None
                   else match dst, ne with ELit d, ELit n => Some (Some (kimg_cut k (d mod two64) n)) | _, _ => None end) with
            | None => None
            | Some ok0 =>
            if (kwritable_xB bc k db dk ne && ranges_apart_xB bc db dk ne sb sk ne)%bool then
              let k1 := match ok0 with None => kn_havocB bc db dk ne | Some k0 => kn_havocM k0 db dk ne end in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              (* [comment removed for export] *)
              if (Z.ltb 0 nlo && kzero_xB bc k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_xB bc sb sk ne)%bool then
                         match copy_factsB bc (Z.to_nat nhi) sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ k1)
                         | None => (if (if kwritable_xB bc k sb sk ne then flat_xB bc sb sk ne else false) then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ne ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None)
                         end
                       else (if (if kwritable_xB bc k sb sk ne then flat_xB bc sb sk ne else false) then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ne ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None)
                   | _ => (if (if kwritable_xB bc k sb sk ne then flat_xB bc sb sk ne else false) then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ne ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None)
                   end
            else None
            end
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.

Lemma summary_copy_eq : forall cs entry, summary_copy cs entry = summary_copy_ref cs entry.
Proof.
  intros. unfold summary_copy, summary_copy_ref. unfold ehi, elo. cbv zeta.
  rewrite ?copy_factsB_eqf, ?flat_xB_eqf, ?kwritable_xB_eqf, ?kzero_xB_eqf, ?off_image_xB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?xloB_eqf, ?kn_havocM_eq, ?kn_havocB_eqf.
  repeat (first [ reflexivity
                | lazymatch goal with
                  | |- match (if ?c then _ else _) with _ => _ end = _ => destruct c
                  | |- match (match (match ?x with _ => _ end) with _ => _ end) with _ => _ end = _ => destruct x
                  | |- match (match ?x with _ => _ end) with _ => _ end = _ => destruct x
                  | |- (if ?c then _ else _) = _ => destruct c
                  | |- match ?x with _ => _ end = _ => destruct x
                  end ]).
Qed.


(* [comment removed for export] *)
Definition summary_miz_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_memiszero A)) then None else
  match ret_lit cs with
  | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(bb, bk) := split_lit beg in
      let spm := eaddz sp (-16) in let '(qb, qk) := split_lit spm in
      match xlo k ne, xhi k ne, xhi k beg, xlo k sp, xhi k sp with
      | Some nlo, Some nhi, Some bhi, Some splo, Some sphi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritable k k qb qk 16
              && ranges_apart_x k qb qk (ELit 16) bb bk ne && kzero_x k k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havoc k qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_miz (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_memiszero A)) then None else
  match ret_lit cs with
  | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(bb, bk) := split_lit beg in
      let spm := eaddz sp (-16) in let '(qb, qk) := split_lit spm in
      match xloB bc ne, xhiB bc ne, xhiB bc beg, xloB bc sp, xhiB bc sp with
      | Some nlo, Some nhi, Some bhi, Some splo, Some sphi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritableB bc k qb qk 16
              && ranges_apart_xB bc qb qk (ELit 16) bb bk ne && kzero_xB bc k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havocB bc qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.

Lemma summary_miz_eq : forall cs, summary_miz cs = summary_miz_ref cs.
Proof. intros. unfold summary_miz, summary_miz_ref. unfold ehi, elo. rewrite ?kn_havocB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?xloB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Definition img_cov (k : list kentry) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) k.

Definition img_covB (bc : bctx) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) (bc_fk bc).
Lemma img_covB_eqf : forall fk, img_covB (mkbc fk) = img_cov fk.
Proof. intros. bcfe. unfold img_covB, img_cov. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite img_covB_eqf : bceq.



(* [comment removed for export] *)
Definition SEALED_W : Z := 0x3e64656c6165733c.

(* [comment removed for export] *)
Definition summary_istrncpy_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_istrncpy A)) then None else
  match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some ret, Some src, Some n =>
      if negb (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool then None else
      let dst := reg cs 10 in
      let '(db, dk) := split_lit dst in
      match xhi k dst with
      | Some dhi =>
          match (if off_image_x k db dk (ELit 4095) then Some k
                 else match dst with ELit d => Some (kimg_cut k (d mod two64) 4095) | _ => None end) with
          | None => None
          | Some k0 =>
              if (Z.ltb (dhi + 4095) two64 && Z.leb 0 (x_sealed A) && Z.ltb (x_sealed A + 9) two64
                  && kwritable_x k k db dk (ELit 4095) && img_cov k0 (x_sealed A) (x_sealed A + 9)
                  && ranges_apart_x k db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9))%bool then
                after_call cs ret (Some dst)
                  (KWord (SA db dk) 8 (ELit SEALED_W) :: KZero (SA db (dk + 8)) (ELit 4087) :: kn_havoc k0 db dk (ELit 4095))
              else None
          end
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition summary_istrncpy (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_istrncpy A)) then None else
  match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some ret, Some src, Some n =>
      if negb (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool then None else
      let dst := reg cs 10 in
      let '(db, dk) := split_lit dst in
      match xhiB bc dst with
      | Some dhi =>
          match (if off_image_xB bc db dk (ELit 4095) then Some k
                 else match dst with ELit d => Some (kimg_cut k (d mod two64) 4095) | _ => None end) with
          | None => None
          | Some k0 =>
              if (Z.ltb (dhi + 4095) two64 && Z.leb 0 (x_sealed A) && Z.ltb (x_sealed A + 9) two64
                  && kwritable_xB bc k db dk (ELit 4095) && img_cov k0 (x_sealed A) (x_sealed A + 9)
                  && ranges_apart_xB bc db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9))%bool then
                after_call cs ret (Some dst)
                  (KWord (SA db dk) 8 (ELit SEALED_W) :: KZero (SA db (dk + 8)) (ELit 4087) :: kn_havocM k0 db dk (ELit 4095))
              else None
          end
      | None => None
      end
  | _, _, _ => None
  end.

Lemma summary_istrncpy_eq : forall cs, summary_istrncpy cs = summary_istrncpy_ref cs.
Proof. intros. unfold summary_istrncpy, summary_istrncpy_ref. unfold ehi, elo. rewrite ?kwritable_xB_eqf, ?off_image_xB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?kn_havocM_eq. reflexivity. Qed.


(* [comment removed for export] *)
Definition popfree_facts (lb : expr) (lk : Z) (cnt c s : Z) (K : nat) : list kentry :=
  map (fun t => KWord (SA lb (lk + 4 * (cnt - 1 - Z.of_nat t))) 4 (ELit ((c + Z.of_nat t * s) / 16))) (seq 0 K).
Definition summary_popfree_ref (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_popfree A)) then None else
  match args, reg_lit cs 10, reg_lit cs 12, reg_lit cs 21, reg_lit cs 19 with
  | [ELit K], Some i, Some c, Some s, Some n =>
      let e := reg cs 11 in
      let cnt := n - i in
      let lo := eaddz e (- (4 * n)) in
      let '(lb, lk) := split_lit lo in
      match xlo k e, xhi k e with
      | Some el, Some eh =>
          if (Z.leb 0 i && Z.ltb i n && Z.leb (4 * n) el && Z.ltb eh two64 && Z.leb 0 c && Z.leb 0 s
              && Z.ltb (c + cnt * s) two64 && Z.leb 0 K && Z.leb K cnt && Z.ltb (pc cs + 32) two64
              && fresh_ok cs && kwritable_x k k lb lk (ELit (4 * cnt)) && off_image_x k lb lk (ELit (4 * cnt)))%bool then
            let k1 := kn_havocM k lb lk (ELit (4 * cnt)) in   (* [comment removed for export] *)
            let kunk := if Z.ltb K cnt then [KUnk (SA lb lk) (ELit (4 * (cnt - K)))] else [] in
            let sr := s_regs (a_ss cs) in
            let sr' := sr_upd (sr_upd (sr_upd (sr_upd sr 10 (ELit n)) 12 (ELit (c + cnt * s)))
                                      14 (ELit ((c + (cnt - 1) * s) / 16))) 15 lo in
            Some (with_ss cs (mk_ss (pc cs + 32) sr' (popfree_facts lb lk cnt c s (Z.to_nat K) ++ kunk ++ k1) (nxt cs)))
          else None
      | _, _ => None
      end
  | _, _, _, _, _ => None
  end.
Definition summary_popfree (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_popfree A)) then None else
  match args, reg_lit cs 10, reg_lit cs 12, reg_lit cs 21, reg_lit cs 19 with
  | [ELit K], Some i, Some c, Some s, Some n =>
      let e := reg cs 11 in
      let cnt := n - i in
      let lo := eaddz e (- (4 * n)) in
      let '(lb, lk) := split_lit lo in
      match xloB bc e, xhiB bc e with
      | Some el, Some eh =>
          if (Z.leb 0 i && Z.ltb i n && Z.leb (4 * n) el && Z.ltb eh two64 && Z.leb 0 c && Z.leb 0 s
              && Z.ltb (c + cnt * s) two64 && Z.leb 0 K && Z.leb K cnt && Z.ltb (pc cs + 32) two64
              && fresh_ok cs && kwritable_xB bc k lb lk (ELit (4 * cnt)) && off_image_xB bc lb lk (ELit (4 * cnt)))%bool then
            let k1 := kn_havocM k lb lk (ELit (4 * cnt)) in   (* [comment removed for export] *)
            let kunk := if Z.ltb K cnt then [KUnk (SA lb lk) (ELit (4 * (cnt - K)))] else [] in
            let sr := s_regs (a_ss cs) in
            let sr' := sr_upd (sr_upd (sr_upd (sr_upd sr 10 (ELit n)) 12 (ELit (c + cnt * s)))
                                      14 (ELit ((c + (cnt - 1) * s) / 16))) 15 lo in
            Some (with_ss cs (mk_ss (pc cs + 32) sr' (popfree_facts lb lk cnt c s (Z.to_nat K) ++ kunk ++ k1) (nxt cs)))
          else None
      | _, _ => None
      end
  | _, _, _, _, _ => None
  end.
Lemma summary_popfree_eq : forall cs args, summary_popfree cs args = summary_popfree_ref cs args.
Proof. intros. unfold summary_popfree, summary_popfree_ref. cbv zeta. rewrite ?xloB_eqf, ?xhiB_eqf, ?kwritable_xB_eqf, ?off_image_xB_eqf. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint unwind_chain (k : list kentry) (fuel : nat) (bp : expr) (qb : expr) (qk : Z) (bb : expr) (bk : Z) (blen : Z)
  : option (list (expr * expr * expr)) :=
  match fuel with
  | O => None
  | S fuel' =>
      let '(cb, ck) := split_lit (eaddz bp (-16)) in
      match kread8e k cb ck, kread8e k cb (ck + 8) with
      | Some f, Some r =>
          if (ranges_apart k cb ck 16 qb qk 64 && ranges_apart k cb ck 16 bb bk blen
              && lin_ge0 k [(bp, 0%Z)] [(ELit 16, 0%Z)])%bool then
            if lin_ge0 k [(bp, 0%Z)] [(f, 0%Z)] then Some [(bp, r, f)]          (* [comment removed for export] *)
            else match unwind_chain k fuel' f qb qk bb bk blen with
                 | Some rest => Some ((bp, r, f) :: rest)
                 | None => None
                 end
          else None
      | _, _ => None
      end
  end.
Definition UNWIND_FUEL : nat := 16%nat.
(* [comment removed for export] *)
Definition summary_unwind (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_unwind A)) then None else
  match ret_lit cs, reg_lit cs 15, kreadZ k (ELit 0) (x_unwind_got A) 8 with
  | Some ret, Some m, Some P =>
    match kreadZ k (ELit 0) P 8 with
    | Some psz =>
      let sp := reg cs 2 in let this := reg cs 10 in let bp := reg cs 12 in let top := reg cs 13 in let bot := reg cs 14 in
      let '(qb, qk) := split_lit (eaddz sp (-64)) in
      let '(bb, bk) := split_lit (eaddz this 8) in
      let blen := 8 + 8 * m in
      match xlo k sp, xhi k sp, xlo k this, xhi k this, unwind_chain k UNWIND_FUEL bp qb qk bb bk blen with
      | Some splo, Some sphi, Some tlo, Some thi, Some _ =>
        if (Z.leb 2 m && Z.leb m 256 && Z.ltb 0 psz && Z.ltb psz two64
            && Z.leb 64 splo && Z.ltb sphi two64 && Z.ltb (thi + 16 + 8 * m) two64 && Z.leb 0 tlo
            && Z.leb (x_unwind_got A + 8) two64 && Z.leb 0 (x_unwind_got A) && Z.leb (P + 8) two64 && Z.leb 0 P
            && fresh_ok cs
            && kwritable k k qb qk 64 && flat_x k qb qk (ELit 64)
            && kwritable k k bb bk blen && flat_x k bb bk (ELit blen)
            && ranges_apart k qb qk 64 bb bk blen
            && ranges_apart k (ELit 0) (x_unwind_got A) 8 qb qk 64 && ranges_apart k (ELit 0) (x_unwind_got A) 8 bb bk blen
            && ranges_apart k (ELit 0) P 8 qb qk 64 && ranges_apart k (ELit 0) P 8 bb bk blen
            && lin_ge0 k [(top, 0%Z)] [(bot, 1%Z)])%bool
        then
          let f := (nxt cs + NCS)%nat in
          let k1 := kn_havoc (kn_havoc k qb qk (ELit 64)) bb bk (ELit blen) in
          let k2 := KWord (SA bb bk) 4 (EVar f) :: KRange (EVar f) 1 m :: k1 in
          after_call2 cs ret None k2 1
        else None
      | _, _, _, _, _ => None
      end
    | None => None
    end
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Definition kn_readable_x (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
  existsb (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        xinsideL k rb rk ne kb kk len
                    | _ => false
                    end) k.

(* [comment removed for export] *)



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_envp : expr := eadd e_sp0 (eadd (escale 8 (EVar V_ARGC)) (ELit 16)).
Definition e_auxv : expr := eadd e_envp (eadd (escale 8 (EVar V_ENVC)) (ELit 8)).
Definition e_str0 : expr := eaddz e_auxv 160.
Definition e_str1 : expr := eadd e_str0 (eaddz (EVar V_L0) 1).
Definition e_atrandom : expr := eadd e_str0 (escale 8 (EVar V_W)).
(* [comment removed for export] *)
Definition e_atr8 : expr :=
  eadd (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W))).

(* [comment removed for export] *)
Definition e_argv1w : expr := EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar V_ARGC)) e_str1.

(* [comment removed for export] *)
Definition node_envscan (cs : acs) : option acs :=
  let k := kn cs in
  if (Z.eqb (pc cs) (x_envscan A) && len_eqb k (reg cs 9) e_envp)%bool then
    Some (set_pc (set_reg (set_reg cs 9 (eadd (reg cs 9) (eadd (escale 8 (EVar V_ENVC)) (ELit 8)))) 10 (ELit 0)) (x_envscan_k A))
  else None.

(* [comment removed for export] *)
Definition node_pnscan (cs : acs) : option acs :=
  let k := kn cs in
  match reg_lit cs 10, reg_lit cs 12 with
  | Some p, Some 47 =>
      if (Z.eqb (pc cs) (x_pnscan A) && len_eqb k (reg cs 11) (eaddz e_str0 1)
          && kwritable k k (ELit 0) p 8 && Z.leb (img_lo A) p && Z.leb (p + 8) (img_hi A) && fresh_ok cs)%bool then
        let v := nxt cs in
        let k' := kn_havocM (kimg_cut k p 8) (ELit 0) p (ELit 8) in   (* [comment removed for export] *)
        let ss := a_ss cs in
        Some (with_ss cs (mk_ss (x_pnscan_k A) (sr_upd (sr_upd (s_regs ss) 11 (EVar v)) 13 (ELit 0)) k' (S v)))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition kw_argv1 (v : expr) : kentry := KWord (SA e_sp0 16) 8 v.

Definition node_layout (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in
  if negb (existsb (kentry_eqb (kw_argv1 e_argv1w)) k) then None else
  let k' := List.filter (fun K => negb (kentry_eqb (kw_argv1 e_argv1w) K)) k in
  match args with
  | [ELit 1] => match xlo k (EVar V_ARGC) with
                | Some lo => if Z.leb 2 lo then Some (set_kn cs (kw_argv1 e_str1 :: k')) else None
                | None => None
                end
  | [ELit 0] => match xhi k (EVar V_ARGC) with
                | Some hi => if Z.leb hi 1 then Some (set_kn cs (kw_argv1 (ELit 0) :: k')) else None
                | None => None
                end
  | _ => None
  end.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition entails_fact (k : list kentry) (K : kentry) : bool :=
  if existsb (kentry_eqb K) k then true
  else match K with KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => fact_ok k K | _ => false end.
(* [comment removed for export] *)
Definition kn_entails (k tk : list kentry) : bool :=
  let t := mk_kidx k in
  forallb (fun K => if mem_kidxL t K then true
                    else match K with KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => fact_ok k K | _ => false end) tk.
Lemma kn_entails_eq : forall k tk, kn_entails k tk = forallb (entails_fact k) tk.
Proof. intros k tk. unfold kn_entails, entails_fact. cbv zeta. rewrite mem_kidxL_feq. reflexivity. Qed.
Definition entails (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_entails (kn cs) (kn ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint esubst (J : nat) (e : expr) (x : expr) : expr :=
  match x with
  | ELit _ => x
  | EVar n => if Nat.eqb n J then e else x
  | EAlu op a b => mkAlu op (esubst J e a) (esubst J e b)
  | EAluw op a b => mkAluw op (esubst J e a) (esubst J e b)
  | EMd op a b => mkMd op (esubst J e a) (esubst J e b)
  | EMdw op a b => mkMdw op (esubst J e a) (esubst J e b)
  | EExt sx lo n a => EExt sx lo n (esubst J e a)
  | EBlob _ _ _ _ => x
  end.
(* [comment removed for export] *)
Definition asubst (J : nat) (e : expr) (a : saddr) : saddr := SA (esubst J e (a_base a)) (a_off a).
Definition ksubst (J : nat) (e : expr) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (asubst J e a) w (esubst J e v)
  | KZero a n => KZero (asubst J e a) (esubst J e n)
  | KBlob a n k => KBlob (asubst J e a) (esubst J e n) k
  | KImg lo hi => K
  | KAlign x m => KAlign (esubst J e x) m
  | KRange x lo hi => KRange (esubst J e x) lo hi
  | KWr a n => KWr (asubst J e a) (esubst J e n)
  | KDisj a1 n1 a2 n2 => KDisj (asubst J e a1) (esubst J e n1) (asubst J e a2) (esubst J e n2)
  | KFill a n c => KFill (asubst J e a) (esubst J e n) c
  | KUnk a n => KUnk (asubst J e a) (esubst J e n)
  end.
Definition psubst (J : nat) (e : expr) (p : expr * expr) : expr * expr := (esubst J e (fst p), esubst J e (snd p)).
Definition msubst (J : nat) (e : expr) (m : amap) : amap := AM (esubst J e (am_base m)) (esubst J e (am_len m)) (am_kind m).
Definition fsubst (J : nat) (e : expr) (f : afd) : afd :=
  match f with FdFile k l o => FdFile k (esubst J e l) (esubst J e o) | _ => f end.
(* [comment removed for export] *)
Definition inst (inv : acs) (J : nat) (e : expr) : acs :=
  ACS (mk_ss (pc inv) (map (esubst J e) (s_regs (a_ss inv))) (map (ksubst J e) (kn inv)) (nxt inv))
      (map (msubst J e) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
      (map (psubst J e) (a_vis inv)) (map (psubst J e) (a_ghost inv)) (a_abytes inv)
      (esubst J e (a_brk inv)) (fsubst J e (a_fd inv)) (a_tidset inv).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint nt_set (t : list (option nat)) (i : nat) (d : nat) {struct i} : list (option nat) :=
  match i, t with
  | O, [] => [Some d]
  | O, _ :: rest => Some d :: rest
  | S j, [] => None :: nt_set [] j d
  | S j, x :: rest => x :: nt_set rest j d
  end.
Definition nt_get (t : list (option nat)) (i : nat) : option nat := nth i t None.
Lemma nt_get_set : forall t i d j, nt_get (nt_set t i d) j = if Nat.eqb j i then Some d else nt_get t j.
Proof.
  unfold nt_get. intros t i. revert t. induction i as [|i IH]; intros t d j; destruct t as [|x rest]; destruct j as [|j]; cbn [nt_set nth Nat.eqb]; try reflexivity.
  - destruct j; reflexivity.
  - rewrite IH. destruct (Nat.eqb j i); destruct j; reflexivity.
  - apply IH.
Qed.
(* [comment removed for export] *)
Fixpoint mk_fwd (m : list (nat * nat)) : option (list (option nat)) :=
  match m with
  | [] => Some []
  | (s, d) :: rest =>
      match mk_fwd rest with
      | Some t => match nt_get t s with None => Some (nt_set t s d) | Some _ => None end
      | None => None
      end
  end.
(* [comment removed for export] *)
Fixpoint mk_bwd (m : list (nat * nat)) : option (list (option nat)) :=
  match m with
  | [] => Some []
  | (s, d) :: rest =>
      match mk_bwd rest with
      | Some t => match nt_get t d with None => Some (nt_set t d s) | Some _ => None end
      | None => None
      end
  end.

Fixpoint erename (t : list (option nat)) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | EVar v => match nt_get t v with Some d => EVar d | None => e end
  | EAlu op a b => EAlu op (erename t a) (erename t b)
  | EAluw op a b => EAluw op (erename t a) (erename t b)
  | EMd op a b => EMd op (erename t a) (erename t b)
  | EMdw op a b => EMdw op (erename t a) (erename t b)
  | EExt sx lo n a => EExt sx lo n (erename t a)
  | EBlob _ _ _ _ => e
  end.
Definition arename (t : list (option nat)) (a : saddr) : saddr := SA (erename t (a_base a)) (a_off a).
Definition krename (t : list (option nat)) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (arename t a) w (erename t v)
  | KZero a n => KZero (arename t a) (erename t n)
  | KBlob a n k => KBlob (arename t a) (erename t n) k
  | KImg lo hi => K
  | KAlign x m => KAlign (erename t x) m
  | KRange x lo hi => KRange (erename t x) lo hi
  | KWr a n => KWr (arename t a) (erename t n)
  | KDisj a1 n1 a2 n2 => KDisj (arename t a1) (erename t n1) (arename t a2) (erename t n2)
  | KFill a n c => KFill (arename t a) (erename t n) c
  | KUnk a n => KUnk (arename t a) (erename t n)
  end.
Definition prename (t : list (option nat)) (p : expr * expr) : expr * expr := (erename t (fst p), erename t (snd p)).
Definition mrename (t : list (option nat)) (m : amap) : amap := AM (erename t (am_base m)) (erename t (am_len m)) (am_kind m).
Definition frename (t : list (option nat)) (f : afd) : afd :=
  match f with FdFile k l o => FdFile k (erename t l) (erename t o) | _ => f end.

(* [comment removed for export] *)
Fixpoint evars_all (ok : nat -> bool) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar v => ok v
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_all ok a && evars_all ok b
  | EExt _ _ _ a => evars_all ok a
  | EBlob _ _ _ _ => true
  end.
Definition kvars_all (ok : nat -> bool) (K : kentry) : bool :=
  match K with
  | KWord a _ v => evars_all ok (a_base a) && evars_all ok v
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => evars_all ok (a_base a) && evars_all ok n
  | KImg _ _ => true
  | KAlign x _ | KRange x _ _ => evars_all ok x
  | KDisj a1 n1 a2 n2 => evars_all ok (a_base a1) && evars_all ok n1 && evars_all ok (a_base a2) && evars_all ok n2
  end%bool.
Definition csvars_all (ok : nat -> bool) (cs : acs) : bool :=
  (forallb (evars_all ok) (s_regs (a_ss cs)) && forallb (kvars_all ok) (kn cs)
   && forallb (fun m => evars_all ok (am_base m) && evars_all ok (am_len m)) (a_maps cs)
   && forallb (fun p => evars_all ok (fst p) && evars_all ok (snd p)) (a_vis cs)
   && forallb (fun p => evars_all ok (fst p) && evars_all ok (snd p)) (a_ghost cs)
   && evars_all ok (a_brk cs)
   && match a_fd cs with FdFile _ l o => evars_all ok l && evars_all ok o | _ => true end)%bool.

(* [comment removed for export] *)
Fixpoint emaxv (e : expr) (acc : nat) : nat :=
  match e with
  | ELit _ => acc
  | EVar v => Nat.max acc (S v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => emaxv a (emaxv b acc)
  | EExt _ _ _ a => emaxv a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kmaxv (K : kentry) (acc : nat) : nat :=
  match K with
  | KWord a _ v => emaxv (a_base a) (emaxv v acc)
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => emaxv (a_base a) (emaxv n acc)
  | KImg _ _ => acc
  | KAlign x _ | KRange x _ _ => emaxv x acc
  | KDisj a1 n1 a2 n2 => emaxv (a_base a1) (emaxv n1 (emaxv (a_base a2) (emaxv n2 acc)))
  end.
Definition csmaxv (cs : acs) : nat :=
  let acc := fold_right emaxv 0%nat (s_regs (a_ss cs)) in
  let acc := fold_right kmaxv acc (kn cs) in
  let acc := fold_right (fun m acc => emaxv (am_base m) (emaxv (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => emaxv (fst p) (emaxv (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => emaxv (fst p) (emaxv (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => emaxv l (emaxv o acc) | _ => acc end in
  emaxv (a_brk cs) acc.

Definition rename_cs (t : list (option nat)) (cs : acs) (nx : nat) : acs :=
  ACS (mk_ss (pc cs) (map (erename t) (s_regs (a_ss cs))) (map (krename t) (kn cs)) nx)
      (map (mrename t) (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (map (prename t) (a_vis cs)) (map (prename t) (a_ghost cs)) (a_abytes cs)
      (erename t (a_brk cs)) (frename t (a_fd cs)) (a_tidset cs).

(* [comment removed for export] *)
Definition node_rename (gb : nat) (cs : acs) (m : list (nat * nat)) : option acs :=
  if forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m then
    match mk_fwd m, mk_bwd m with
    | Some fw, Some bw =>
        let ok (v : nat) := match nt_get fw v with Some _ => true | None => match nt_get bw v with Some _ => false | None => true end end in
        if (csvars_all ok cs && match s_log (a_ss cs) with [] => true | _ => false end)%bool then
          let cs1 := rename_cs fw cs 0%nat in
          Some (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) (kn cs1) (Nat.max gb (csmaxv cs1))))
        else None
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
Fixpoint bt_set (t : list bool) (i : nat) {struct i} : list bool :=
  match i, t with
  | O, [] => [true]
  | O, _ :: rest => true :: rest
  | S j, [] => false :: bt_set [] j
  | S j, x :: rest => x :: bt_set rest j
  end.
Definition bt_get (t : list bool) (i : nat) : bool := nth i t false.
(* [comment removed for export] *)
Fixpoint evars_fo (gb : nat) (e : expr) (acc : list nat * list bool) : list nat * list bool :=
  match e with
  | ELit _ => acc
  | EVar v => if Nat.ltb v gb then acc else if bt_get (snd acc) v then acc else (v :: fst acc, bt_set (snd acc) v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_fo gb b (evars_fo gb a acc)
  | EExt _ _ _ a => evars_fo gb a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kvars_fo (gb : nat) (K : kentry) (acc : list nat * list bool) : list nat * list bool :=
  match K with
  | KWord a _ v => evars_fo gb v (evars_fo gb (a_base a) acc)
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => evars_fo gb n (evars_fo gb (a_base a) acc)
  | KImg _ _ => acc
  | KAlign x _ | KRange x _ _ => evars_fo gb x acc
  | KDisj a1 n1 a2 n2 => evars_fo gb n2 (evars_fo gb (a_base a2) (evars_fo gb n1 (evars_fo gb (a_base a1) acc)))
  end.
Definition csvars_fo (gb : nat) (cs : acs) : list nat :=
  let acc := fold_left (fun acc e => evars_fo gb e acc) (s_regs (a_ss cs)) ([], []) in
  let acc := fold_left (fun acc K => kvars_fo gb K acc) (kn cs) acc in
  let acc := fold_left (fun acc m => evars_fo gb (am_len m) (evars_fo gb (am_base m) acc)) (a_maps cs) acc in
  let acc := fold_left (fun acc p => evars_fo gb (snd p) (evars_fo gb (fst p) acc)) (a_vis cs) acc in
  let acc := fold_left (fun acc p => evars_fo gb (snd p) (evars_fo gb (fst p) acc)) (a_ghost cs) acc in
  let acc := match a_fd cs with FdFile _ l o => evars_fo gb o (evars_fo gb l acc) | _ => acc end in
  let acc := evars_fo gb (a_brk cs) acc in
  rev (fst acc).
Fixpoint number_from (i : nat) (l : list nat) : list (nat * nat) :=
  match l with [] => [] | v :: rest => (v, i) :: number_from (S i) rest end.
Definition compact_map (gb : nat) (cs : acs) : list (nat * nat) := number_from gb (csvars_fo gb cs).
Definition node_compact (gb : nat) (cs : acs) : option acs := node_rename gb cs (compact_map gb cs).

(* [comment removed for export] *)
Fixpoint regs_match_h (lo hi : nat) (seen : list nat) (rs ts : list expr) : bool :=
  match rs, ts with
  | [], [] => true
  | r :: rs', t :: ts' =>
      match t with
      | EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool
                  then (negb (existsb (Nat.eqb v) seen) && regs_match_h lo hi (v :: seen) rs' ts')%bool
                  else (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')%bool
      | _ => (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')%bool
      end
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition saddr_eqb_h (x y : saddr) : bool :=
  saddr_eqb x y || expr_eqb (eaddz (a_base x) (a_off x)) (eaddz (a_base y) (a_off y)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint cover1 (k : list kentry) (b : expr) (i : Z) : option Z :=
  match k with
  | [] => None
  | K :: rest =>
      let hit := match K with
                 | KWord (SA kb kk) w _ =>
                     if (expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool then Some (kk + Z.of_nat w) else None
                 | KZero (SA kb kk) (ELit l) | KFill (SA kb kk) (ELit l) _ | KBlob (SA kb kk) (ELit l) _ | KUnk (SA kb kk) (ELit l) =>
                     if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l) else None
                 | _ => None
                 end in
      match hit with Some e => Some e | None => cover1 rest b i end
  end.
Fixpoint cover_x (fuel : nat) (k : list kentry) (b : expr) (i : Z) (stop : Z) : bool :=
  match fuel with
  | O => false
  | S f => if Z.leb stop i then true else
           match cover1 k b i with
           | Some e => if Z.ltb i e then cover_x f k b e stop else false
           | None => false
           end
  end.
(* [comment removed for export] *)
Definition kunk_covered (k : list kentry) (K : kentry) : bool :=
  match K with
  | KUnk (SA b o) (ELit n) =>
      (Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.leb (img_lo A) (img_hi A) && flat_x k b o (ELit n) && off_image_x k b o (ELit n) && cover_x (S (length k)) k b o (o + n))%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition kunk_coveredM (k : list kentry) (K : kentry) : bool :=
  match K with
  | KUnk (SA b o) (ELit n) =>
      let bc := mkbc k in
      (Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.leb (img_lo A) (img_hi A) && flat_xB bc b o (ELit n) && off_image_xB bc b o (ELit n) && cover_x (S (length k)) k b o (o + n))%bool
  | _ => false
  end.
Lemma kunk_coveredM_eq : forall k K, kunk_coveredM k K = kunk_covered k K.
Proof.
  intros k K. unfold kunk_coveredM, kunk_covered. destruct K as [| | | | | | | | |[b o] n]; try reflexivity.
  destruct n; try reflexivity. cbv zeta. rewrite flat_xB_eqf, off_image_xB_eqf. reflexivity.
Qed.
Lemma kunk_coveredM_feq : kunk_coveredM = kunk_covered.
Proof. apply functional_extensionality; intros k. apply functional_extensionality; intros K. apply kunk_coveredM_eq. Qed.

Definition kentry_eqb_h (x y : kentry) : bool :=
  kentry_eqb x y ||
  match x, y with
  | KWord a w v, KWord a' w' v' => saddr_eqb_h a a' && Nat.eqb w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => saddr_eqb_h a a' && expr_eqb n n'
  | KBlob a n k, KBlob a' n' k' => saddr_eqb_h a a' && expr_eqb n n' && Nat.eqb k k'
  | KWr a n, KWr a' n' => saddr_eqb_h a a' && expr_eqb n n'
  | KFill a n c, KFill a' n' c' => saddr_eqb_h a a' && expr_eqb n n' && Z.eqb c c'
  | KUnk a n, KUnk a' n' => saddr_eqb_h a a' && expr_eqb n n'
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition kflat_h (k : list kentry) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => flat_x k b o (ELit (Z.of_nat w))
  | KZero (SA b o) n | KBlob (SA b o) n _ | KWr (SA b o) n | KFill (SA b o) n _ | KUnk (SA b o) n => flat_x k b o n
  | _ => true
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kimg_sub_covered (k : list kentry) (K : kentry) : bool :=
  match K with
  | KImg lo hi => existsb (fun X => match X with KImg lo' hi' => Z.leb lo' lo && Z.leb hi hi' | _ => false end) k
  | _ => false
  end.
Definition kn_incl1_hT (k : list kentry) (K : kentry) : bool :=
  if (if kflat_h k K then existsb (fun X => kentry_eqb_h X K) k else false) then true
  else if kimg_sub_covered k K then true
  else kunk_covered k K.
Definition kn_incl1_h (k : list kentry) (K : kentry) : bool :=
  if existsb (fun X => kentry_eqb X K) k then true else kn_incl1_hT k K.
(* [comment removed for export] *)
Definition kn_incl_h (k : list kentry) (tk : list kentry) : bool :=
  let t := mk_kidx k in forallb (fun K => if mem_kidx t K then true else kn_incl1_hT k K) tk.
Lemma kn_incl_h_eq : forall k tk, kn_incl_h k tk = forallb (kn_incl1_h k) tk.
Proof. intros k tk. unfold kn_incl_h, kn_incl1_h. cbv zeta. rewrite mem_kidx_feq. reflexivity. Qed.

Definition entails_h (lo hi : nat) (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && match s_resv (a_ss ch) with None => true | _ => false end
   && regs_match_h lo hi [] (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_incl_h (kn cs) (kn ch)
   && kn_vars_lt lo (kn ch) && maps_vars_lt lo (a_maps ch) && pairs_vars_lt lo (a_vis ch) && pairs_vars_lt lo (a_ghost ch)
   && expr_vars_lt lo (a_brk ch) && fd_vars_lt lo (a_fd ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tw (ss : sym_state) : acs := ACS ss [] 0 0 0 [] [] 0 (ELit 0) FdStd false.
(* [comment removed for export] *)
Definition lfresh (n : nat) (cs : acs) : bool :=
  maps_vars_lt n (a_maps cs) && pairs_vars_lt n (a_vis cs) && pairs_vars_lt n (a_ghost cs)
  && expr_vars_lt n (a_brk cs) && fd_vars_lt n (a_fd cs).
(* [comment removed for export] *)
Definition live_vars_ss (ss : sym_state) : ptree unit :=
  let acc := fold_right expr_vars_t PTLeaf (s_regs ss) in
  fold_right (fun K acc => match K with
                          | KWord a _ v => expr_vars_t (a_base a) (expr_vars_t v acc)
                          | KZero a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                          | KBlob a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                          | KWr a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                          | KFill a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                          | KUnk a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                          | _ => acc end) acc (s_know ss).
Definition ss_gc (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  set_kn cs (List.filter (kn_gc_entry_t spb spk (live_vars_ss (a_ss cs))) (kn cs)).
(* [comment removed for export] *)
Definition tgraft (cs T : acs) : acs := with_ss cs (mk_ss (pc T) (s_regs (a_ss T)) (kn T) (nxt T)).
(* [comment removed for export] *)
Fixpoint tslots (lo hi : nat) (rs ts : list expr) : list (nat * expr) :=
  match rs, ts with
  | r :: rs', t :: ts' =>
      match t with
      | EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool then (v, r) :: tslots lo hi rs' ts' else tslots lo hi rs' ts'
      | _ => tslots lo hi rs' ts'
      end
  | _, _ => []
  end.
Fixpoint ksubst_al (al : list (nat * expr)) (K : kentry) : kentry :=
  match al with [] => K | (v, e) :: r => ksubst_al r (ksubst v e K) end.
(* [comment removed for export] *)
Definition tfact_ok (k : list kentry) (K : kentry) : bool := kn_incl1_h k K || fact_ok k K || fact_okK k K.
Definition entails_t0 (cs T : acs) : bool :=
  let lo := nxt cs in let hi := nxt T in
  let rs := s_regs (a_ss cs) in let ts := s_regs (a_ss T) in
  let al := tslots lo hi rs ts in
  (Z.eqb (pc cs) (pc T) && fresh_ok cs && Nat.leb lo hi
   && match s_log (a_ss T) with [] => true | _ => false end
   && match s_resv (a_ss T) with None => true | _ => false end
   && Nat.eqb (length ts) 32
   && regs_match_h lo hi [] rs ts && sr_vars_lt hi ts
   && forallb (fun K => let K' := ksubst_al al K in kn_vars_lt lo [K'] && tfact_ok (kn cs) K') (kn T)
   && kn_vars_lt hi (kn T))%bool.

(* [comment removed for export] *)
Inductive loopctx : Type :=
| LC (lc_head : Z) (lc_next : acs) (lc_lo lc_hi : nat)
| JC (jc_id : nat) (jc_st : acs) (jc_sh : shape) (jc_b jc_lo : nat).
Definition lc_bnd (c : loopctx) : nat := match c with LC _ _ _ hi => hi | JC _ _ _ b _ => b end.

(* [comment removed for export] *)
Definition loop_ok (cs0 : acs) (J : nat) (N : expr) (inv : acs) : option Z :=
  let lo := S J in let hi := nxt inv in
  if (fresh_ok cs0 && Nat.leb (nxt cs0) J && Nat.ltb J hi && fresh_ok inv
      && expr_vars_lt (nxt cs0) N
      && match s_log (a_ss inv) with [] => true | _ => false end
      && Nat.eqb (length (s_regs (a_ss inv))) 32
      && kn_vars_lt lo (kn inv) && maps_vars_lt lo (a_maps inv) && pairs_vars_lt lo (a_vis inv) && pairs_vars_lt lo (a_ghost inv)
      && expr_vars_lt lo (a_brk inv) && fd_vars_lt lo (a_fd inv)
      && forallb (fun r => match r with EVar v => true | _ => expr_vars_lt lo r end) (s_regs (a_ss inv))
      && regs_match_h lo hi [] (s_regs (a_ss inv)) (s_regs (a_ss inv)))%bool
  then match xhi (kn cs0) N with Some nhi => if Z.ltb nhi two64 then Some nhi else None | None => None end
  else None.

(* [comment removed for export] *)
Definition loop_body_state (J : nat) (N : expr) (nhi : Z) (inv : acs) : acs :=
  add_kn inv [KRange (EVar J) 0 (nhi - 1); KRange (esub N (EVar J)) 1 nhi].

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition branch_probe (cs : acs) : option expr :=
  match itab_lookup IT (pc cs) with
  | Some (Branch c rs1 rs2 _) =>
      Some (fst (cond_probe c (sr_get (s_regs (a_ss cs)) rs1) (sr_get (s_regs (a_ss cs)) rs2)))
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint diff_regs (i : nat) (ra rb : list expr) : list nat :=
  match ra, rb with
  | a :: ra', b :: rb' => if expr_eqb a b then diff_regs (S i) ra' rb' else i :: diff_regs (S i) ra' rb'
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition node_diamond_join (nx : nat) (joinpc : Z) (rs : list nat) (ca cb : acs) : option acs :=
  let hv := nodup Nat.eq_dec (diff_regs 0 (s_regs (a_ss ca)) (s_regs (a_ss cb)) ++ rs) in
  let v0 := Nat.max nx (Nat.max (nxt ca) (nxt cb)) in
  let hi := (v0 + length hv)%nat in
  let regsJ := sr_fresh (s_regs (a_ss ca)) hv v0 in
  let knJ := List.filter (mem_kidx (mk_kidx (kn cb))) (kn ca) in   (* [comment removed for export] *)
  let csJ := with_ss ca (mk_ss joinpc regsJ knJ hi) in
  if (Z.eqb (pc ca) joinpc && Z.eqb (pc cb) joinpc
      && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) hv
      && Nat.eqb (length regsJ) 32
      && Nat.leb nx0 v0
      && entails_h v0 hi ca csJ && entails_h v0 hi cb csJ)%bool
  then Some csJ else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zjoin_ctr (m0 nx : nat) (arms : list acs) : nat :=
  fold_right (fun c acc => Nat.max (nxt c) acc) (Nat.max m0 nx) arms.
Definition node_zjoin (nx m0 : nat) (joinpc : Z) (rs : list nat) (arms : list acs) : option acs :=
  match arms with
  | [] => None
  | ca :: rest =>
      let m := zjoin_ctr m0 nx arms in
      let hi := (m + length rs)%nat in
      let regsJ := sr_fresh (s_regs (a_ss ca)) rs m in
      let idxs := List.map (fun cb => mk_kidx (kn cb)) rest in   (* [comment removed for export] *)
      let knJ := List.filter (fun K => forallb (fun t => mem_kidx t K) idxs) (kn ca) in
      let csJ := with_ss ca (mk_ss joinpc regsJ knJ hi) in
      if (forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs
          && Nat.eqb (length regsJ) 32
          && Nat.leb nx0 m && Nat.leb nx m
          && forallb (fun c => Nat.leb (nxt c) m && Z.eqb (pc c) joinpc && entails_h m hi c csJ) arms)%bool
      then Some csJ else None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition via_ok (cs js : acs) (lo : nat) : bool :=
  (match s_log (a_ss js) with [] => true | _ => false end
   && Nat.eqb (length (s_regs (a_ss js))) 32
   && Nat.leb nx0 (nxt cs) && Nat.leb (nxt cs) lo && Nat.leb lo (nxt js))%bool.

(* [comment removed for export] *)
Fixpoint kw_find (k : list kentry) (a : saddr) (n : nat) : option expr :=
  match k with
  | [] => None
  | KWord a' w v :: r => if (saddr_eqb a' a && Nat.eqb w n)%bool then Some v else kw_find r a n
  | _ :: r => kw_find r a n
  end.
Fixpoint kw_bytes (b : expr) (off : Z) (v : expr) (i n : nat) : list kentry :=
  match n with
  | O => []
  | S n' => KWord (SA b (off + Z.of_nat i)) 1 (mkExt false i 1 v) :: kw_bytes b off v (S i) n'
  end.
Definition node_bytes (cs : acs) (b : expr) (off : Z) (n : nat) : option acs :=
  if (Nat.leb 1 n && Nat.leb n 8)%bool then
    match kw_find (kn cs) (SA b off) n with
    | Some v => Some (add_kn cs (kw_bytes b off v 0 n))
    | None => None
    end
  else None.

(* [comment removed for export] *)
Definition node_joinv (cs : acs) (b : expr) (off : Z) (n : nat) : option acs :=
  if (fresh_ok cs && Nat.leb 1 n && Nat.leb n 8 && expr_vars_lt (nxt cs) b
      && flat_x (kn cs) b off (ELit (Z.of_nat n)) && cover_x (S (length (kn cs))) (kn cs) b off (off + Z.of_nat n))%bool   (* [comment removed for export] *)
  then Some (set_kn (bump cs 1) (KWord (SA b off) n (EVar (nxt cs)) :: kn cs))
  else None.

(* [comment removed for export] *)
Definition lit_ivs_of (ms : list amap) : list (Z * Z) :=
  (img_lo A, img_hi A)
  :: flat_map (fun m => if (is_fog m || is_hole m)%bool then [] else
                        match am_base m, am_len m with
                        | ELit b, ELit n => [(b mod two64, b mod two64 + n mod two64)]
                        | _, _ => []
                        end) ms.
Definition zone_end (ivs : list (Z * Z)) (b : Z) : Z :=
  fold_right (fun iv acc => if (Z.leb b (fst iv) && Z.ltb (fst iv) (snd iv))%bool then Z.min (fst iv) acc else acc) TOPMAX ivs.
Definition zones_of (ivs : list (Z * Z)) (nlo : Z) : list (Z * Z) :=
  List.filter (fun z => Z.leb nlo (snd z - fst z)) (List.map (fun b => (b, zone_end ivs b)) (0 :: List.map snd ivs)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zone_var_fact (k : list kentry) (c : Z) (v : nat) (off : Z) (lo hi : Z) : list kentry :=
  match xhi k (EVar v) with
  | Some h => if (Z.ltb 0 c && Z.ltb c two64 && Z.leb 0 off && Z.ltb (c * h + off) two64)%bool
              then [KRange (EVar v) ((lo - off + c - 1) / c) ((hi - off) / c)] else []
  | None => []
  end.
(* [comment removed for export] *)
Definition zone_facts (k : list kentry) (e len : expr) (nlo : Z) (z : Z * Z) : list kentry :=
  KRange e (fst z) (snd z - nlo)
  :: KRange (eadd e len) (fst z + nlo) (snd z)
  :: match e with
     | EMd M_MUL (ELit c) (EVar v) => zone_var_fact k c v 0 (fst z) (snd z - nlo)
     | EAlu ALU_ADD (EMd M_MUL (ELit c) (EVar v)) (ELit off) => zone_var_fact k c v off (fst z) (snd z - nlo)
     | _ => []
     end.
(* [comment removed for export] *)
Definition zone_cands (cs : acs) (e : expr) : option (Z * expr * list (Z * Z)) :=
  match e with ELit _ => None | _ =>
  match List.find (fun m => expr_eqb (am_base m) e) (a_maps cs) with
  | Some m =>
      if (is_fog m || is_hole m)%bool then None else
      match xlo (kn cs) (am_len m) with
      | Some nlo =>
          if Z.ltb 0 nlo then
            (* [comment removed for export] *)
            let elo := match xlo (kn cs) e with Some l => Z.max l 0 | None => 0 end in
            match List.filter (fun z => Z.leb nlo (snd z - fst z))
                    (List.map (fun z => (Z.max (fst z) elo, snd z)) (zones_of (lit_ivs_of (a_maps cs)) nlo)) with
            | [] => None
            | zs => Some (nlo, am_len m, zs)
            end
          else None
      | None => None
      end
  | None => None
  end end.
Definition node_zones (cs : acs) (e : expr) : option (list acs) :=
  match zone_cands cs e with
  | Some (nlo, len, zs) => Some (map (fun z => set_kn cs (zone_facts (kn cs) e len nlo z ++ kn cs)) zs)
  | None => None
  end.
(* [comment removed for export] *)
Definition zone_hull (z0 : Z * Z) (zr : list (Z * Z)) : Z * Z :=
  (fold_right (fun z acc => Z.min (fst z) acc) (fst z0) zr, fold_right (fun z acc => Z.max (snd z) acc) (snd z0) zr).
Definition node_zonehull (cs : acs) (e : expr) : option acs :=
  match zone_cands cs e with
  | Some (nlo, len, z0 :: zr) => Some (set_kn cs (zone_facts (kn cs) e len nlo (zone_hull z0 zr) ++ kn cs))
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_abstractcell_ref (cs : acs) (b : expr) (n : Z) : option acs :=
  let '(bb, bo) := split_lit b in
  let K := KUnk (SA bb bo) (ELit n) in
  if kunk_coveredM (kn cs) K then Some (set_kn cs (K :: kn_cutoutM (kn cs) bb bo (ELit n))) else None.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition node_abstractcell (cs : acs) (b : expr) (n : Z) : option acs :=
  let '(bb, bo) := split_lit b in
  let k := kn cs in let bc := mkbc k in
  if (Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.leb (img_lo A) (img_hi A) && flat_xB bc bb bo (ELit n) && off_image_xB bc bb bo (ELit n) && cover_x (S (length k)) k bb bo (bo + n))%bool
  then Some (set_kn cs (KUnk (SA bb bo) (ELit n) :: kn_cutoutB bc bb bo (ELit n))) else None.
Lemma node_abstractcell_eq : forall cs b n, node_abstractcell cs b n = node_abstractcell_ref cs b n.
Proof. intros. unfold node_abstractcell, node_abstractcell_ref. destruct (split_lit b) as [bb bo]. reflexivity. Qed.

(* [comment removed for export] *)
Definition respell_ok (k : list kentry) (a e : expr) : bool :=
  match decide_branch k BC_EQ a e with
  | Some true => true
  | _ => (* [comment removed for export] *)
      match erange k (mkAlu ALU_SUB a e) with
      | Some (lo, hi) => Z.eqb lo 0 && Z.eqb hi 0
      | None => false
      end
  end.
Definition node_respell (cs : acs) (r : nat) (e : expr) : option acs :=
  if (Nat.ltb 0 r && Nat.ltb r 32 && expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool
  then Some (set_reg cs r e) else None.
Definition respell_okB (bc : bctx) (a e : expr) : bool :=
  match decide_branchB bc BC_EQ a e with
  | Some true => true
  | _ => match erangeB bc (mkAlu ALU_SUB a e) with
         | Some (lo, hi) => Z.eqb lo 0 && Z.eqb hi 0
         | None => false
         end
  end.
Lemma respell_okB_eqf : forall fk, respell_okB (mkbc fk) = respell_ok fk.
Proof. intros fk. apply functional_extensionality; intros a. apply functional_extensionality; intros e.
       unfold respell_okB, respell_ok. rewrite decide_branchB_eqf, erangeB_eqf. reflexivity. Qed.
Definition node_respellM (cs : acs) (r : nat) (e : expr) : option acs :=
  if (if Nat.ltb 0 r then if Nat.ltb r 32 then if expr_vars_lt (nxt cs) e then respell_okB (mkbc (kn cs)) (reg cs r) e else false else false else false)
  then Some (set_reg cs r e) else None.
Lemma node_respellM_feq : node_respellM = node_respell.
Proof.
  apply functional_extensionality; intros cs. apply functional_extensionality; intros r. apply functional_extensionality; intros e.
  unfold node_respellM, node_respell. rewrite respell_okB_eqf.
  destruct (Nat.ltb 0 r), (Nat.ltb r 32), (expr_vars_lt (nxt cs) e); reflexivity.
Qed.

(* [comment removed for export] *)
Definition sa_of (b : expr) : saddr := let '(bb, bo) := split_lit b in SA bb bo.
Fixpoint hw_apply (k : list kentry) (a : saddr) (x : nat) (found : bool) : list kentry :=
  match k with
  | [] => []
  | KWord a' w v :: r =>
      if saddr_eqb a' a then (if found then hw_apply r a x true else KWord a' w (EVar x) :: hw_apply r a x true)
      else KWord a' w v :: hw_apply r a x found
  | K :: r => K :: hw_apply r a x found
  end.
(* [comment removed for export] *)
Fixpoint hw_val (k : list kentry) (a : saddr) : expr :=
  match k with
  | [] => ELit 0
  | KWord a' _ v :: r => if saddr_eqb a' a then v else hw_val r a
  | _ :: r => hw_val r a
  end.
Fixpoint hw_go (k : list kentry) (bs : list expr) (x : nat) : list kentry :=
  match bs with
  | [] => k
  | b :: r => hw_go (hw_apply k (sa_of b) x false) r (S x)
  end.
Definition node_havocwords (cs : acs) (bs : list expr) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (hw_go (s_know ss) bs (s_next ss)) (s_next ss + length bs)))
  else None.

(* [comment removed for export] *)
Definition node_nameword (cs : acs) (b : expr) (lo hi : Z) : option acs :=
  let k := kn cs in let a := sa_of b in
  match erange k (hw_val k a) with
  | Some (l, h) =>
      if (fresh_ok cs && Z.leb lo l && Z.leb h hi)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: hw_apply k a v false) (S v)))
      else None
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition alias_fact (v : nat) (wit : expr) : kentry := KRange (EAlu ALU_SUB (EVar v) wit) 0 0.
Definition node_introeq (cs : acs) (wit : expr) (lo hi : Z) : option acs :=
  match erange (kn cs) wit with
  | Some (wlo, whi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) wit && Z.leb 0 lo && Z.leb lo wlo && Z.leb whi hi && Z.ltb hi two64)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: alias_fact v wit :: s_know ss) (S v)))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint esubst_al (al : list (nat * expr)) (x : expr) : expr :=
  match al with [] => x | (v, e) :: r => esubst_al r (esubst v e x) end.
Fixpoint gc_remove (p : expr * expr) (l : list (expr * expr)) : option (list (expr * expr)) :=
  match l with
  | [] => None
  | q :: r => if pair_eqb p q then Some r else match gc_remove p r with Some r' => Some (q :: r') | None => None end
  end.
(* [comment removed for export] *)
Fixpoint cover_cost (k : list kentry) (L old : list (expr * expr)) : option Z :=
  match L with
  | [] => Some 0
  | l :: r => match gc_remove l old with
              | Some old' => cover_cost k r old'
              | None => match xhi k (snd l), cover_cost k r old with
                        | Some h, Some c => Some (vis_cost h + c)
                        | _, _ => None
                        end
              end
  end.
Definition gc_covered (k : list kentry) (Ls : list (expr * expr)) (g : expr * expr) : bool :=
  existsb (fun l => pair_eqb g l
                    || (lin_ge0 k [(fst g, 0)] [(fst l, 0)] && lin_ge0 k [(fst l, 0); (snd l, 0)] [(fst g, 0); (snd g, 0)]))%bool Ls.
Definition node_ghostcover (cs : acs) (L : list (expr * expr)) (al : list (nat * expr)) : option acs :=
  let k := kn cs in
  let Ls := map (fun l => (esubst_al al (fst l), esubst_al al (snd l))) L in
  match cover_cost k L (a_ghost cs) with
  | Some cost =>
      if (forallb (fun ve => existsb (fun X => kentry_eqb X (alias_fact (fst ve) (snd ve))) k) al
          && pairs_vars_lt (nxt cs) L
          && forallb (gc_covered k Ls) (a_ghost cs)
          && Z.leb 0 cost && Z.leb (a_eager cs + a_abytes cs + cost) LIMIT)%bool
      then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) L
                     (a_abytes cs + cost) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | None => None
  end.

Definition STOPS : list Z :=
  [x_imemset A; x_imemcpy A; x_memset A; x_memcpy A; x_memiszero A; x_envscan A; x_pnscan A] ++ stops_more A.

(* [comment removed for export] *)
Fixpoint mk_itab_ranges_acc (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: rs' => mk_itab_ranges_acc rs' (mk_itab_fuel segs n lo t)
  end.
Definition mk_itab_ranges (rs : list (Z * nat)) : itab := mk_itab_ranges_acc rs PTLeaf.

(* [comment removed for export] *)
Definition i63_1 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 1.
Definition i63_2 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 2.
Definition i63_4 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 4.
Definition i63_6 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 6.
Definition i63_8 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 8.
Definition i63_16 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 16.
Definition i63_48 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 48.
Definition i63_57 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 57.
Definition i63_87 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 87.
Definition i63_97 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 97.
Definition i63_102 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 102.
Definition i63_256 : PrimInt63.int := Eval vm_compute in Uint63.of_Z 256.
Definition hexv63 (c : PrimInt63.int) : PrimInt63.int :=
  if (Uint63.leb i63_48 c && Uint63.leb c i63_57)%bool then Uint63.sub c i63_48
  else if (Uint63.leb i63_97 c && Uint63.leb c i63_102)%bool then Uint63.sub c i63_87 else i63_16.
Definition hexb63 (s : PrimString.string) (i : PrimInt63.int) : PrimInt63.int :=   (* [comment removed for export] *)
  let h := hexv63 (PrimString.get s i) in
  let l := hexv63 (PrimString.get s (Uint63.add i i63_1)) in
  if (Uint63.ltb h i63_16 && Uint63.ltb l i63_16)%bool then Uint63.add (Uint63.lsl h i63_4) l else i63_256.
Definition hexw63 (s : PrimString.string) (i : PrimInt63.int) : option Z :=   (* [comment removed for export] *)
  let b0 := hexb63 s i in let b1 := hexb63 s (Uint63.add i i63_2) in
  let b2 := hexb63 s (Uint63.add i i63_4) in let b3 := hexb63 s (Uint63.add i i63_6) in
  if (Uint63.ltb b0 i63_256 && Uint63.ltb b1 i63_256 && Uint63.ltb b2 i63_256 && Uint63.ltb b3 i63_256)%bool
  then Some (Uint63.to_Z (Uint63.lor b0 (Uint63.lsl (Uint63.lor b1 (Uint63.lsl (Uint63.lor b2 (Uint63.lsl b3 i63_8)) i63_8)) i63_8)))
  else None.
Definition fast_entry (s : PrimString.string) (i : PrimInt63.int) : option instr :=
  match hexw63 s i with
  | Some z => let w := Z_to_bv 32 z in
              if is_ecall w then None else
              match decode_any w with Some (ins, sz) => if Z.eqb sz 4 then Some ins else None | None => None end
  | None => None
  end.
Fixpoint mk_itab_fast_go (n : nat) (pc : Z) (s : PrimString.string) (i : PrimInt63.int) (t : itab) : itab :=
  match n with
  | O => t
  | S n' => mk_itab_fast_go n' (pc + 4) s (Uint63.add i i63_8)
            (match pc, fast_entry s i with Zpos p, Some ins => pt_set p ins t | _, _ => t end)
  end.
(* [comment removed for export] *)
Fixpoint page_segment (ss : list Segment) (lo len : Z) : option Segment :=
  match ss with
  | [] => None
  | sg :: rest =>
      let base := Z.of_N (seg_base sg) in let top := base + Z.of_N (seg_size sg) in
      if (Z.leb base lo && Z.leb (lo + len) top)%bool then Some sg
      else if (Z.leb (lo + len) base || Z.leb top lo)%bool then page_segment rest lo len
      else None
  end.
Definition page_fast_ok (lo : Z) (n : nat) : option (PrimString.string * PrimInt63.int) :=
  let len := 4 * Z.of_nat n in
  if negb (Z.eqb (lo mod 4) 0 && Z.leb 0 lo && Z.ltb (lo + len) two64 && Z.ltb 0 len)%bool then None else
  match page_segment segs lo len with
  | Some sg =>
      if negb (seg_executable sg && negb (seg_writable sg))%bool then None else
      match seg_bytes sg with
      | [c] => let off := lo - Z.of_N (seg_base sg) in       (* [comment removed for export] *)
               let clen := Uint63.to_Z (PrimString.length c) in
               if (Z.leb 0 off && Z.leb (2 * (off + len)) clen && Z.ltb clen (2 ^ 62))%bool
               then Some (c, Uint63.of_Z (2 * off)) else None
      | _ => None
      end
  | None => None
  end.
Definition mk_itab_page (lo : Z) (n : nat) (t : itab) : itab :=
  match page_fast_ok lo n with
  | Some (c, i0) => mk_itab_fast_go n lo c i0 t
  | None => mk_itab_fuel segs n lo t
  end.
Fixpoint mk_itab_ranges_fast_acc (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: rs' => mk_itab_ranges_fast_acc rs' (mk_itab_page lo n t)
  end.
Definition mk_itab_ranges_fast_ref (rs : list (Z * nat)) : itab := mk_itab_ranges_fast_acc rs PTLeaf.

(* [comment removed for export] *)
Definition word_entry (z : Z) : option instr :=
  let w := Z_to_bv 32 z in
  if is_ecall w then None else
  match decode_any w with Some (ins, sz) => if Z.eqb sz 4 then Some ins else None | None => None end.
Definition wmemo : Type := ptree (option instr).
Definition word_entryM (z : Z) (m : wmemo) : option instr * wmemo :=
  match pt_get m (zkey z) with
  | Some e => (e, m)
  | None => let e := word_entry z in (e, pt_set (zkey z) e m)
  end.
Fixpoint mk_itab_fast_goM (n : nat) (pc : Z) (s : PrimString.string) (i : PrimInt63.int) (t : itab) (m : wmemo) : itab * wmemo :=
  match n with
  | O => (t, m)
  | S n' =>
      match hexw63 s i with
      | Some z => let '(e, m') := word_entryM z m in
                  mk_itab_fast_goM n' (pc + 4) s (Uint63.add i i63_8)
                    (match pc, e with Zpos p, Some ins => pt_set p ins t | _, _ => t end) m'
      | None => mk_itab_fast_goM n' (pc + 4) s (Uint63.add i i63_8) t m
      end
  end.
Definition mk_itab_pageM (lo : Z) (n : nat) (t : itab) (m : wmemo) : itab * wmemo :=
  match page_fast_ok lo n with
  | Some (c, i0) => mk_itab_fast_goM n lo c i0 t m
  | None => (mk_itab_fuel segs n lo t, m)
  end.
Fixpoint mk_itab_ranges_fast_accM (rs : list (Z * nat)) (t : itab) (m : wmemo) : itab * wmemo :=
  match rs with
  | [] => (t, m)
  | (lo, n) :: rs' => let '(t', m') := mk_itab_pageM lo n t m in mk_itab_ranges_fast_accM rs' t' m'
  end.
Definition mk_itab_ranges_fast (rs : list (Z * nat)) : itab := fst (mk_itab_ranges_fast_accM rs PTLeaf PTLeaf).

Definition WM_OK (m : wmemo) : Prop := forall z e, pt_get m (zkey z) = Some e -> e = word_entry z.
Lemma zkey_inj : forall a b, zkey a = zkey b -> a = b.
Proof. intros [|a|a] [|b|b] H; cbn [zkey] in H; try discriminate; try reflexivity; injection H as <-; reflexivity. Qed.
Lemma word_entryM_ok : forall z m, WM_OK m -> fst (word_entryM z m) = word_entry z /\ WM_OK (snd (word_entryM z m)).
Proof.
  intros z m HM. unfold word_entryM. destruct (pt_get m (zkey z)) as [e|] eqn:E; cbn [fst snd].
  - split; [exact (HM z e E) | exact HM].
  - split; [reflexivity|]. intros z' e' H. destruct (Pos.eq_dec (zkey z') (zkey z)) as [Ek|NE].
    + rewrite Ek, pt_gss in H. injection H as <-. apply zkey_inj in Ek. subst z'. reflexivity.
    + rewrite pt_gso in H by exact NE. exact (HM z' e' H).
Qed.
Lemma fast_entry_word : forall s i, fast_entry s i = match hexw63 s i with Some z => word_entry z | None => None end.
Proof. reflexivity. Qed.
Lemma mk_itab_fast_goM_eq : forall n pc s i t m, WM_OK m ->
  fst (mk_itab_fast_goM n pc s i t m) = mk_itab_fast_go n pc s i t /\ WM_OK (snd (mk_itab_fast_goM n pc s i t m)).
Proof.
  induction n as [|n IH]; intros pc s i t m HM; cbn [mk_itab_fast_goM mk_itab_fast_go]; [split; [reflexivity | exact HM]|].
  rewrite fast_entry_word. destruct (hexw63 s i) as [z|]; [|destruct pc; apply IH; exact HM].
  destruct (word_entryM_ok z m HM) as [E M]. destruct (word_entryM z m) as [e m']. cbn [fst snd] in E, M. subst e.
  apply IH. exact M.
Qed.
Lemma mk_itab_pageM_eq : forall lo n t m, WM_OK m ->
  fst (mk_itab_pageM lo n t m) = mk_itab_page lo n t /\ WM_OK (snd (mk_itab_pageM lo n t m)).
Proof.
  intros lo n t m HM. unfold mk_itab_pageM, mk_itab_page. destruct (page_fast_ok lo n) as [[c i0]|]; [apply mk_itab_fast_goM_eq; exact HM|].
  split; [reflexivity | exact HM].
Qed.
Lemma mk_itab_ranges_fast_accM_eq : forall rs t m, WM_OK m ->
  fst (mk_itab_ranges_fast_accM rs t m) = mk_itab_ranges_fast_acc rs t.
Proof.
  induction rs as [|[lo n] rs IH]; intros t m HM; cbn [mk_itab_ranges_fast_accM mk_itab_ranges_fast_acc]; [reflexivity|].
  destruct (mk_itab_pageM_eq lo n t m HM) as [E M]. destruct (mk_itab_pageM lo n t m) as [t' m']. cbn [fst snd] in E, M. subst t'.
  apply IH. exact M.
Qed.
Lemma mk_itab_ranges_fast_eq : forall rs, mk_itab_ranges_fast rs = mk_itab_ranges_fast_ref rs.
Proof.
  intros rs. unfold mk_itab_ranges_fast, mk_itab_ranges_fast_ref. apply mk_itab_ranges_fast_accM_eq.
  intros z e H. rewrite pt_get_leaf in H. discriminate.
Qed.

End WithSegs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BRK_ASLR : Z := 0x80000000.
Definition NX0 : nat := 10.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition K_RND : nat := 25.

(* [comment removed for export] *)
Definition e_auxb : expr * Z := split_lit e_auxv.
Definition e_atrb : expr * Z := split_lit e_atrandom.
Definition auxw (i : Z) (ty : Z) (v : expr) : list kentry :=
  [KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty); KWord (SA (fst e_auxb) (snd e_auxb + 16 * i + 8)) 8 v].

(* [comment removed for export] *)
Definition init_kn_with (atr : kentry) (A : atable) : list kentry :=
  [KRange (EVar V_S1) 0xFFFF0000 0xFFFFFFFF; KRange (EVar V_S2) 0 2047;
   KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000; KRange e_atr8 0xFFFF0000001 0xFFFFFFFFFE9;
   KRange e_sp0 0x7fff80000000 0x7fffffffff40;
   (* [comment removed for export] *)
   KRange e_envp 0x7fff80000000 (XTOP - 184); KRange e_auxv 0x7fff80000000 (XTOP - 176); KRange e_str0 0x7fff80000000 (XTOP - 16);
   KRange (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) 0xFFFF0000000 0xFFFFFFFFFE8;
   KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071; KRange (EVar V_L1) 0 131071;
   KRange (EVar V_UID) 0 0xFFFFFFFE; KRange (EVar V_HW) 0x112D 0x20112D (* [comment removed for export] *);
   KRange (EVar V_W) 0 280000; KRange (EVar V_BRK) (img_hi A / 4096) ((img_hi A + BRK_ASLR) / 4096);
   KWr (SA e_sp0 (-8388608)) (ELit 8388608); KZero (SA e_sp0 (-8388608)) (ELit 8388608);
   KWord (SA e_sp0 0) 8 (EVar V_ARGC); KWord (SA e_sp0 8) 8 e_str0; kw_argv1 e_argv1w]
  (* [comment removed for export] *)
  ++ auxw 0 3 (ELit (ph_addr_z A)) ++ auxw 1 4 (ELit (ph_ent_z A)) ++ auxw 2 5 (ELit (ph_num_z A)) ++ auxw 3 16 (EVar V_HW) ++ auxw 4 6 (ELit 4096)
  ++ auxw 5 11 (EVar V_UID) ++ auxw 6 12 (EVar V_UID) ++ auxw 7 23 (ELit 0) ++ auxw 8 25 e_atrandom ++ auxw 9 0 (ELit 0)
  ++ [atr;
      KImg (img_lo A) (img_hi A); KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))].

(* [comment removed for export] *)
Definition atr_entry : kentry := KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND.
Definition atr_entry_zero : kentry := KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16).
(* [comment removed for export] *)
Definition init_kn (A : atable) : list kentry := init_kn_with atr_entry A.

Definition init_regs : list expr := sr_upd (repeat (ELit 0) 32) 2 e_sp0.
(* [comment removed for export] *)
Definition init_vis (A : atable) : list (expr * expr) :=
  [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (e_stklo, e_stkn)].

Definition init_acs_of_with (kn0 : list kentry) (A : atable) : acs :=
  ACS (mk_ss (a_entry A) init_regs kn0 NX0) [] (img_hi A - img_lo A) MBASE_MIN 0 (init_vis A) []
      (vis_cost (img_hi A - img_lo A) + vis_cost (2^47 - CEIL)) (escale 4096 (EVar V_BRK)) FdStd false.
Definition init_acs_of (A : atable) : acs := init_acs_of_with (init_kn A) A.        (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASAN : atable :=
  {| img_lo := 0x10000; img_hi := 0x688000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4eab8; rw_lo := 0x124000; rw_len := 0x564000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x87a48; x_imemcpy := 0x879cc; x_memset := 0x11cfa4; x_memcpy := 0x11cba0; x_memiszero := 0x87f94;
     x_istrncpy := 0x87e74; x_sealed := 0x11b2e; x_popfree := 0x55168;
     x_unwind := 0x96f38; x_unwind_got := 0x129e88;
     x_lib := 0xa458c; lib_ret := 0xa4488; lib_fp := [(0x664900, 0x665a18)];   (* [comment removed for export] *)
     x_envscan := 0x10b068; x_envscan_k := 0x10b074; x_pnscan := 0x10b12c; x_pnscan_k := 0x10b138;
     stops_more := [0x52ddc; 0x54400; 0x77b04; 0x7e10c; 0x7e120; 0x7e134; 0x83ac4; 0x83b94; 0x910dc; 0x91fe8; 0x92178; 0x922e8; 0x9bed0]  (* [comment removed for export] *) |}.

(* [comment removed for export] *)
Definition ASAN_TEXT_LO : Z := 0x4eab8.
Definition ASAN_TEXT_N : nat := 217837.
Definition asan_init : acs := init_acs_of ASAN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BOTH : atable :=
  {| img_lo := 0x10000; img_hi := 0x689000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4ebfc; rw_lo := 0x124000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x87b8c; x_imemcpy := 0x87b10; x_memset := 0x11d480; x_memcpy := 0x11d07c; x_memiszero := 0x880d8;
     x_istrncpy := 0x87fb8; x_sealed := 0x11b36; x_popfree := 0x552ac;
     x_unwind := 0x9707c; x_unwind_got := 0x12a360;
     x_lib := 0xa46d0; lib_ret := 0xa45cc; lib_fp := [(0x664dc0, 0x665ed8)];   (* [comment removed for export] *)
     x_envscan := 0x10b544; x_envscan_k := 0x10b550; x_pnscan := 0x10b608; x_pnscan_k := 0x10b614;
     stops_more := [0x52f20; 0x54544; 0x77c48; 0x7e250; 0x7e264; 0x7e278; 0x83c08; 0x83cd8; 0x91220; 0x9212c; 0x922bc; 0x9242c; 0x9c014]  (* [comment removed for export] *) |}.
Definition BOTH_TEXT_LO : Z := 0x4ebfc.
Definition BOTH_TEXT_N : nat := 218067.
Definition both_init : acs := init_acs_of BOTH.

End APC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
