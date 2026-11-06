(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3B. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AxSymExecF AxSymExecFB.   (* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AxSymExec3C.   (* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AxSymExec3E.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
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
Definition ATOP_MAX : Z := 0x7FFFFF800000.
(* [comment removed for export] *)
Definition STK_BELOW : Z := 0x800000.
Definition STK_LEN : Z := 0x80800000.

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
  x_sniff : Z; sniff_tab : Z; sniff_cell : Z;
  (* [comment removed for export] *)
  x_envscan : Z; x_envscan_k : Z; x_pnscan : Z; x_pnscan_k : Z;
  stops_more : list Z              (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition plain (A : atable) : bool := Z.eqb (shadow_off A) 0.

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
Fixpoint shape_eqb_holes (x y : shape) : bool :=
  match x, y with
  | SNil, SNil => true
  | SExit c, SExit c' => Z.eqb c c'
  | SEmitP fd ps s, SEmitP fd' ps' s' => Z.eqb fd fd' && spieces_eqb ps ps' && shape_eqb_holes s s'
  | SAlt2 a b, SAlt2 a' b' => shape_eqb_holes a a' && shape_eqb_holes b b'
  | SCase e m a b, SCase e' m' a' b' => expr_eqb e e' && Z.eqb m m' && shape_eqb_holes a a' && shape_eqb_holes b b'
  | SHole h, SHole h' => true
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

(* [comment removed for export] *)
Record gatom : Type := GA { g_id : nat; g_args : list expr }.
Inductive vconcl : Type := VCAtom (g : gatom) | VCFact (K : kentry).
(* [comment removed for export] *)
Record vc : Type := VC { vc_kn : list kentry; vc_hyps : list gatom; vc_concl : vconcl; vc_pc : Z }.
(* [comment removed for export] *)
(* [comment removed for export] *)
Record gparams : Type := GPAR { g_fp : nat -> list expr -> list (expr * expr); g_vcok : vc -> bool }.
Definition G0 : gparams := GPAR (fun _ _ => []) (fun _ => false).

Record acs : Type := ACSG {
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
  a_tidset : bool;              (* [comment removed for export] *)
  a_props : list gatom          (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Notation ACS ss maps totsz ylo eager vis ghost abytes brk fd tidset :=
  (ACSG ss maps totsz ylo eager vis ghost abytes brk fd tidset (@nil gatom)) (only parsing).
(* [comment removed for export] *)
Definition gpure (G : gparams) (g : gatom) : bool := match g_fp G (g_id g) (g_args g) with [] => true | _ => false end.
Definition set_props (cs : acs) (l : list gatom) : acs :=
  ACSG (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs)
       (a_fd cs) (a_tidset cs) l.
Definition gdrop_mem (G : gparams) (cs : acs) : acs := set_props cs (List.filter (gpure G) (a_props cs)).

Definition reg (cs : acs) (n : nat) : expr := nth n (s_regs (a_ss cs)) (ELit 0).
Definition kn (cs : acs) : list kentry := s_know (a_ss cs).
Definition pc (cs : acs) : Z := s_pc (a_ss cs).
Definition nxt (cs : acs) : nat := s_next (a_ss cs).

Definition with_ss (cs : acs) (ss : sym_state) : acs :=       (* [comment removed for export] *)
  ACSG ss (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_props cs).
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
  let acc := fold_right (fun g acc => fold_right expr_vars acc (g_args g)) acc (a_props cs) in   (* [comment removed for export] *)
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
  let acc := fold_right (fun g acc => fold_right expr_vars_t acc (g_args g)) acc (a_props cs) in   (* [comment removed for export] *)
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
  apply live_agree_fold; [intros g acc t H; apply live_agree_fold; [intros; apply live_agree_expr; assumption | exact H]|].   (* [comment removed for export] *)
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
Definition run_block_ref (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let ss' := AX2F.sym_execTXF segs IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in   (* [comment removed for export] *)
    match carry (s_log ss') (kunwrap_head (s_know ss')) [] with   (* [comment removed for export] *)
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
(* [comment removed for export] *)
Definition run_block (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in                 (* [comment removed for export] *)
    let ss' := AX2FE.sym_execTXFBI5 segs bc kx IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in   (* [comment removed for export] *)
    match AX2C.carryK3 bc (s_log ss') (kunwrap_head (s_know ss')) [] with   (* [comment removed for export] *)
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
(* [comment removed for export] *)
Definition log_inside (fk : list kentry) (W : list (saddr * expr)) (log : list sentry) : bool :=
  forallb (fun s => match s with
                    | SE a n _ => existsb (fun w => xinside fk (a_base a) (a_off a) (elen n) (a_base (fst w)) (a_off (fst w)) (snd w)) W
                    end) log.
(* [comment removed for export] *)
Definition run_block_wb (wb : option (list (saddr * expr))) (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match wb with
  | None => run_block K fuel stops cs
  | Some W =>
    if fresh_ok cs then
      let ss := a_ss cs in
      let bc := mkbc (facts_of (s_know ss)) in
      let kx := mk_kix (s_know ss) in
      let ss' := AX2FE.sym_execTXFBI5 segs bc kx IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
      if log_inside (facts_of (s_know ss)) W (s_log ss') then
        match AX2C.carryK3 bc (s_log ss') (kunwrap_head (s_know ss')) [] with
        | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
        | _ => None
        end
      else None
    else None
  end.
Lemma run_block_wb_none : forall K fuel stops cs, run_block_wb None K fuel stops cs = run_block K fuel stops cs.
Proof. reflexivity. Qed.
Definition run_block_gc_wb (wb : option (list (saddr * expr))) (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block_wb wb K fuel stops cs with Some cs' => Some (cs_gc cs') | None => None end.

Lemma run_block_eq : forall K fuel stops cs, run_block K fuel stops cs = run_block_ref K fuel stops cs.
Proof.
  intros. unfold run_block, run_block_ref. destruct (fresh_ok cs); [|reflexivity]. cbv zeta.
  rewrite AX2FE.sym_execTXFBI5_eq.
  rewrite (AX2FB.sym_execTXFBI_eq segs (s_know (a_ss cs))) by reflexivity.
  replace (s_know (a_ss cs)) with (s_know (SS (s_pc (a_ss cs)) (s_regs (a_ss cs)) [] (s_know (a_ss cs)) (s_next (a_ss cs)))) at 1 by reflexivity.
  rewrite <- (AX2FB.sym_execTXF_facts segs IT K fuel true stops), <- AX2B.facts_of_kunwrap_head.   (* [comment removed for export] *)
  rewrite AX2C.carryK3_eq. reflexivity.
Qed.

Definition run_block_gc (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block K fuel stops cs with Some cs' => Some (cs_gc cs') | None => None end.
(* [comment removed for export] *)
Definition log_windows (log : list sentry) : list (saddr * nat) :=
  map (fun s => match s with SE a n _ => (a, n) end) log.
Definition run_block_ws (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option (acs * list (saddr * nat)) :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in
    let ss' := AX2FE.sym_execTXFBI5 segs bc kx IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match AX2C.carryK3 bc (s_log ss') (kunwrap_head (s_know ss')) [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')), log_windows (s_log ss'))
    | _ => None
    end
  else None.
Lemma run_block_ws_fst : forall K fuel stops cs,
  run_block K fuel stops cs = option_map fst (run_block_ws K fuel stops cs).
Proof.
  intros. unfold run_block, run_block_ws. destruct (fresh_ok cs); [|reflexivity]. cbv zeta.
  destruct (AX2C.carryK3 _ _ _ _) as [[kn' scs] hs]; destruct scs; reflexivity.
Qed.
(* [comment removed for export] *)
Definition run_block_wb_ws (wb : option (list (saddr * expr))) (K : nat) (fuel : nat) (stops : list Z) (cs : acs)
  : option (acs * list (saddr * nat)) :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in
    let ss' := AX2FE.sym_execTXFBI5 segs bc kx IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    if match wb with Some W => log_inside (facts_of (s_know ss)) W (s_log ss') | None => true end then
      match AX2C.carryK3 bc (s_log ss') (kunwrap_head (s_know ss')) [] with
      | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')), log_windows (s_log ss'))
      | _ => None
      end
    else None
  else None.
Definition run_block_gc_wb_ws (wb : option (list (saddr * expr))) (K : nat) (fuel : nat) (stops : list Z) (cs : acs)
  : option (acs * list (saddr * nat)) :=
  match run_block_wb_ws wb K fuel stops cs with Some (cs', W) => Some (cs_gc cs', W) | None => None end.
Lemma run_block_wb_ws_fst : forall wb K fuel stops cs,
  run_block_wb wb K fuel stops cs = option_map fst (run_block_wb_ws wb K fuel stops cs).
Proof.
  intros. unfold run_block_wb, run_block_wb_ws, run_block. destruct wb as [W|]; (destruct (fresh_ok cs); [|reflexivity]); cbv zeta.
  - destruct (log_inside _ _ _); [|reflexivity]. destruct (AX2C.carryK3 _ _ _ _) as [[kn' scs] hs]; destruct scs; reflexivity.
  - destruct (AX2C.carryK3 _ _ _ _) as [[kn' scs] hs]; destruct scs; reflexivity.
Qed.
Lemma run_block_gc_wb_ws_fst : forall wb K fuel stops cs,
  run_block_gc_wb wb K fuel stops cs = option_map fst (run_block_gc_wb_ws wb K fuel stops cs).
Proof.
  intros. unfold run_block_gc_wb, run_block_gc_wb_ws. rewrite run_block_wb_ws_fst.
  destruct (run_block_wb_ws wb K fuel stops cs) as [[cs' W]|]; reflexivity.
Qed.

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


Definition amap_eqb (x y : amap) : bool :=
  expr_eqb (am_base x) (am_base y) && expr_eqb (am_len x) (am_len y) && mkind_eqb (am_kind x) (am_kind y).

(* [comment removed for export] *)
Fixpoint list_eqb {T : Type} (eqb : T -> T -> bool) (x y : list T) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => if eqb a b then list_eqb eqb x' y' else false
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition gatom_eqb (a b : gatom) : bool :=
  Nat.eqb (g_id a) (g_id b) && list_eqb expr_eqb (g_args a) (g_args b).
Definition gvars_lt (b : nat) (g : gatom) : bool := forallb (expr_vars_lt b) (g_args g).
(* [comment removed for export] *)
Definition gpures (G : gparams) (cs cs' : acs) : acs :=
  set_props cs' (let l := List.filter (gpure G) (a_props cs) in if forallb (gvars_lt (s_next (a_ss cs))) l then l else []).
(* [comment removed for export] *)
Definition gnew (cs cs' : acs) : list gatom :=
  List.filter (fun g => negb (existsb (gatom_eqb g) (a_props cs))) (a_props cs').
Definition gpures_new (G : gparams) (cs cs' : acs) : acs :=
  set_props cs' (gnew cs cs' ++ a_props (gpures G cs cs')).
(* [comment removed for export] *)
Definition fp_apart (k : list kentry) (W : list (saddr * nat)) (r : expr * expr) : bool :=
  forallb (fun w => ranges_apart_x k (a_base (fst w)) (a_off (fst w)) (elen (snd w)) (fst r) 0 (snd r)) W.
Definition gkeep1 (G : gparams) (k : list kentry) (W : list (saddr * nat)) (nx : nat) (g : gatom) : bool :=
  (gvars_lt nx g && forallb (fp_apart k W) (g_fp G (g_id g) (g_args g)))%bool.
Definition gkeep (G : gparams) (W : list (saddr * nat)) (cs cs' : acs) : acs :=
  set_props cs' (List.filter (gkeep1 G (kn cs') W (s_next (a_ss cs))) (a_props cs)).
(* [comment removed for export] *)
Definition fp_apartB (bc : bctx) (W : list (saddr * nat)) (r : expr * expr) : bool :=
  forallb (fun w => ranges_apart_xB bc (a_base (fst w)) (a_off (fst w)) (elen (snd w)) (fst r) 0 (snd r)) W.
Definition gkeep1B (G : gparams) (bc : bctx) (W : list (saddr * nat)) (nx : nat) (g : gatom) : bool :=
  (gvars_lt nx g && forallb (fp_apartB bc W) (g_fp G (g_id g) (g_args g)))%bool.
Lemma forallb_ext : forall (T : Type) (f g : T -> bool) l, (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros T f g l H. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite H, IH. reflexivity. Qed.
(* [comment removed for export] *)
Definition fp_apartBQ (bc : bctx) (wbs : list expr) (W : list (saddr * nat)) (r : expr * expr) : bool :=
  let qs := map (fun wb => (wb, mk_apq bc wb (fst r) (snd r))) (List.filter (fun wb => shares_var wb (fst r)) wbs) in
  forallb (fun w =>
    let wb := a_base (fst w) in let wk := a_off (fst w) in let n := snd w in
    if match qs with
       | [] => false
       | _ => match aq_lookup qs wb with
              | Some q => match snd r with
                          | ELit z2 => apq_fast_lit q wk (zlit64 (Z.of_nat n)) 0 (zlit64 z2)
                          | _ => apq_fast_sym q wk (wlit_nw bc n) (wlit_c n) 0 (snd r)
                          end
              | None => false
              end
       end then true
    else ranges_apart_xB bc wb wk (elen n) (fst r) 0 (snd r)) W.
Lemma fp_apartBQ_eq : forall bc wbs W r, fp_apartBQ bc wbs W r = fp_apartB bc W r.
Proof.
  intros bc wbs W [rb rl]. unfold fp_apartBQ, fp_apartB. cbn [fst snd].
  set (qs := map _ _). apply forallb_ext. intros [[wb wk] n]. cbn [fst snd a_base a_off].
  match goal with |- (if ?c then true else ?x) = _ => destruct c eqn:HC; [|reflexivity] end.
  symmetry. destruct qs as [|q0 qrest] eqn:EQ; [discriminate|]. rewrite <- EQ in HC.
  destruct (aq_lookup qs wb) as [q|] eqn:HL; [|discriminate]. subst qs.
  apply aq_lookup_map in HL. cbn beta in HL.
  destruct rl as [z2| | | | | | |].
  - subst q. eapply apq_fast_lit_okX. exact HC.
  - apply (apq_fast_sym_okX bc wb wk n rb 0 _ q); [rewrite HL; reflexivity | exact I | exact HC].
  - apply (apq_fast_sym_okX bc wb wk n rb 0 _ q); [rewrite HL; reflexivity | exact I | exact HC].
  - apply (apq_fast_sym_okX bc wb wk n rb 0 _ q); [rewrite HL; reflexivity | exact I | exact HC].
  - apply (apq_fast_sym_okX bc wb wk n rb 0 _ q); [rewrite HL; reflexivity | exact I | exact HC].
  - apply (apq_fast_sym_okX bc wb wk n rb 0 _ q); [rewrite HL; reflexivity | exact I | exact HC].
  - apply (apq_fast_sym_okX bc wb wk n rb 0 _ q); [rewrite HL; reflexivity | exact I | exact HC].
  - apply (apq_fast_sym_okX bc wb wk n rb 0 _ q); [rewrite HL; reflexivity | exact I | exact HC].
Qed.
Definition gkeep1BQ (G : gparams) (bc : bctx) (wbs : list expr) (W : list (saddr * nat)) (nx : nat) (g : gatom) : bool :=
  (gvars_lt nx g && forallb (fp_apartBQ bc wbs W) (g_fp G (g_id g) (g_args g)))%bool.
Lemma gkeep1BQ_eqf : forall G k wbs, gkeep1BQ G (mkbc k) wbs = gkeep1 G k.
Proof.
  intros. apply functional_extensionality; intros W. apply functional_extensionality; intros nx. apply functional_extensionality; intros g.
  unfold gkeep1BQ, gkeep1, fp_apart. f_equal. apply forallb_ext. intros r. rewrite fp_apartBQ_eq. unfold fp_apartB.
  rewrite ranges_apart_xB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition gk_prep (bc : bctx) (W : list (saddr * nat)) : list (stx * positive) :=
  let '(kd, _, _) := AX2C.mk_kdl (bc_fk bc) [] xH in
  let '(sxs, _, _) := AX2C.mk_stxsI bc kd (map (fun w => SE (fst w) (snd w) (ELit 0)) W) nt_empty [] in
  fst (AX2C.mk_cls sxs [] xH).
Definition fp_fast (qs : list (expr * apq)) (bc : bctx) (wb : expr) (wk : Z) (n : nat) (r : expr * expr) : bool :=
  match qs with
  | [] => false
  | _ => match aq_lookup qs wb with
         | Some q => match snd r with
                     | ELit z2 => apq_fast_lit q wk (zlit64 (Z.of_nat n)) 0 (zlit64 z2)
                     | _ => apq_fast_sym q wk (wlit_nw bc n) (wlit_c n) 0 (snd r)
                     end
         | None => false
         end
  end.
Fixpoint fp_chain (bc : bctx) (qs : list (expr * apq)) (eh : AX2C.ehoist) (br2 : option (Z * Z)) (r : expr * expr)
         (sxcs : list (stx * positive)) (m : AX2C.memo) : bool :=
  match sxcs with
  | [] => true
  | (sx, dc) :: rest =>
      let wb := a_base (sx_a sx) in let wk := a_off (sx_a sx) in
      if fp_fast qs bc wb wk (sx_w sx) r then fp_chain bc qs eh br2 r rest m
      else let '(v, m') := AX2C.rapM bc (sx_sp sx) dc eh wb wk (elen (sx_w sx)) br2 (fst r) 0 (snd r) m in
           if v then fp_chain bc qs eh br2 r rest m' else false
  end.
Definition fp_apartM (bc : bctx) (wbs : list expr) (sxcs : list (stx * positive)) (r : expr * expr) : bool :=
  let qs := map (fun wb => (wb, mk_apq bc wb (fst r) (snd r))) (List.filter (fun wb => shares_var wb (fst r)) wbs) in
  let br2 := base_rangeB bc (fst r) in
  fp_chain bc qs (AX2C.mk_eh bc br2 (fst r) 0 (snd r)) br2 r sxcs [].
Definition gkeep1M (G : gparams) (bc : bctx) (wbs : list expr) (sxcs : list (stx * positive)) (nx : nat) (g : gatom) : bool :=
  (gvars_lt nx g && forallb (fp_apartM bc wbs sxcs) (g_fp G (g_id g) (g_args g)))%bool.
Definition gkeepM (G : gparams) (W : list (saddr * nat)) (cs cs' : acs) : acs :=
  match a_props cs with
  | [] => set_props cs' []
  | props =>
      match W with
      | [] => set_props cs' (List.filter (gvars_lt (s_next (a_ss cs))) props)   (* [comment removed for export] *)
      | _ => let bc := mkbc (kn cs') in
             let wbs := nubE (map (fun w => a_base (fst w)) W) in
             let sxcs := gk_prep bc W in
             set_props cs' (List.filter (gkeep1M G bc wbs sxcs (s_next (a_ss cs))) props)
      end
  end.

Lemma fp_fast_sound : forall bc wbs wb wk n r,
  fp_fast (map (fun wb => (wb, mk_apq bc wb (fst r) (snd r))) (List.filter (fun wb => shares_var wb (fst r)) wbs)) bc wb wk n r = true ->
  ranges_apart_xB bc wb wk (elen n) (fst r) 0 (snd r) = true.
Proof.
  intros bc wbs wb wk n r H. pose proof (fp_apartBQ_eq bc wbs [(SA wb wk, n)] r) as E.
  unfold fp_apartBQ, fp_apartB in E. cbn [forallb fst snd a_base a_off] in E. unfold fp_fast in H. rewrite H in E.
  rewrite !andb_true_r in E. symmetry. exact E.
Qed.
(* [comment removed for export] *)
Lemma in_sides_eqL : forall allkn kn b1 k1 n1 b2 k2 n2,
  in_sides allkn (disj_sides allkn kn b1 k1 n1) b2 k2 n2 = kdisj_apart allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sides kdisj_apart]; try exact IH.
  destruct (sub_itv allkn b1 k1 n1 c1 m1), (sub_itv allkn b1 k1 n1 c2 m2); cbn [in_sides];
    destruct (sub_itv allkn b2 k2 n2 c2 m2) eqn:E2, (sub_itv allkn b2 k2 n2 c1 m1) eqn:E1;
    rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
Lemma in_sides_x_eqL : forall allkn kn b1 k1 n1 b2 k2 n2,
  in_sides_x allkn (disj_sides_x allkn kn b1 k1 n1) b2 k2 n2 = kdisj_apart_x allkn kn b1 k1 n1 b2 k2 n2.
Proof.
  intros allkn kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sides_x kdisj_apart_x]; try exact IH.
  destruct (sub_itv_x allkn b1 k1 n1 c1 m1), (sub_itv_x allkn b1 k1 n1 c2 m2); cbn [in_sides_x];
    destruct (sub_itv_x allkn b2 k2 n2 c2 m2) eqn:E2, (sub_itv_x allkn b2 k2 n2 c1 m1) eqn:E1;
    rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
Lemma rapc_x : forall fk b1 k1 n1 b2 k2 n2,
  ranges_apart_pcB (mkbc fk) (mk_sprepB (mkbc fk) b1 k1 n1) b1 k1 n1 (base_rangeB (mkbc fk) b2) b2 k2 n2 = ranges_apart_xB (mkbc fk) b1 k1 n1 b2 k2 n2.
Proof.
  intros. autorewrite with bceq. unfold ranges_apart_pc, ranges_apart_x, mk_sprep. cbn [sp_rng sp_h1 sp_D sp_Dx].
  destruct n1; try (rewrite in_sides_x_eqL; reflexivity).
  destruct n2; try (rewrite in_sides_x_eqL; reflexivity).
  unfold ranges_apart. rewrite in_sides_eqL. reflexivity.
Qed.

Lemma fp_chain_eq : forall fk tbl wbs r sxcs m,
  let bc := mkbc fk in
  let qs := map (fun wb => (wb, mk_apq bc wb (fst r) (snd r))) (List.filter (fun wb => shares_var wb (fst r)) wbs) in
  let br2 := base_rangeB bc (fst r) in
  List.NoDup (map fst tbl) -> (forall sx dc, In (sx, dc) sxcs -> In (dc, AX2C.spk sx) tbl) ->
  (forall sx, In sx (map fst sxcs) -> sx_sp sx = mk_sprepB bc (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) ->
  AX2C.MOK bc tbl (fst r) 0 (snd r) m ->
  fp_chain bc qs (AX2C.mk_eh bc br2 (fst r) 0 (snd r)) br2 r sxcs m
  = forallb (fun sx => ranges_apart_xB bc (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) (fst r) 0 (snd r)) (map fst sxcs).
Proof.
  intros fk tbl wbs r sxcs. cbv zeta. induction sxcs as [|[sx dc] rest IH]; intros m HN HC HS HM; [reflexivity|].
  cbn [fp_chain map fst forallb].
  assert (HC' : forall sx0 dc0, In (sx0, dc0) rest -> In (dc0, AX2C.spk sx0) tbl) by (intros; apply HC; right; assumption).
  assert (HS' : forall sx0, In sx0 (map fst rest) -> sx_sp sx0 = mk_sprepB (mkbc fk) (a_base (sx_a sx0)) (a_off (sx_a sx0)) (elen (sx_w sx0)))
    by (intros; apply HS; right; assumption).
  destruct (fp_fast _ _ _ _ _ r) eqn:EF.
  - rewrite (fp_fast_sound _ _ _ _ _ _ EF). cbn [andb]. apply IH; assumption.
  - pose proof (AX2C.rapM_eq (mkbc fk) tbl (sx_sp sx) dc (a_base (sx_a sx)) (a_off (sx_a sx)) (Z.of_nat (sx_w sx))
                  (base_rangeB (mkbc fk) (fst r)) (fst r) 0 (snd r) m HN (HC sx dc (or_introl eq_refl)) HM) as [E1 HM1].
    fold (elen (sx_w sx)) in E1, HM1.
    destruct (AX2C.rapM _ _ _ _ _ _ _ _ _ _ _ m) as [v m']. cbn [fst snd] in E1, HM1.
    rewrite (HS sx (or_introl eq_refl)) in E1. rewrite rapc_x in E1. rewrite <- E1.
    destruct v; [cbn [andb]; apply IH; assumption | reflexivity].
Qed.
Lemma forallb_rev : forall (T : Type) (f : T -> bool) l, forallb f (rev l) = forallb f l.
Proof.
  intros T f l. induction l as [|x r IH]; [reflexivity|]. cbn [rev forallb]. rewrite forallb_app, IH. cbn [forallb]. rewrite andb_true_r. apply andb_comm.
Qed.
Lemma forallb_mapL : forall (S T : Type) (g : S -> T) (f : T -> bool) l, forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof. intros S T g f l. induction l as [|x r IH]; [reflexivity|]. cbn [map forallb]. rewrite IH. reflexivity. Qed.
Lemma fp_apartM_eq : forall fk wbs W r, fp_apartM (mkbc fk) wbs (gk_prep (mkbc fk) W) r = fp_apartB (mkbc fk) W r.
Proof.
  intros fk wbs W r. unfold fp_apartM, gk_prep.
  destruct (AX2C.mk_kdl (bc_fk (mkbc fk)) [] xH) as [[kd stbl] nx] eqn:EK.
  destruct (AX2C.mk_kdl_ok _ _ _ _ _ _ (conj (fun i sd (H : In (i, sd) []) => match H with end) (fun i sd sd' (H : In (i, sd) []) => match H with end)) EK)
    as ((_ & Hfun) & _ & HmapK & HallK).
  set (log := map (fun w : saddr * nat => SE (fst w) (snd w) (ELit 0)) W).
  pose proof (proj1 (AX2C.mk_stxsI_eq (mkbc fk) kd stbl log nt_empty [] Hfun HallK HmapK (fun id b l H => match H with end))) as EQ.
  destruct (mk_stxs (mkbc fk) log nt_empty) as [sxs t0] eqn:E.
  destruct (AX2C.mk_stxsI (mkbc fk) kd log nt_empty []) as [[sxsq t0q] xcq]. cbn [fst] in EQ. injection EQ as -> ->.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
  destruct (AX2C.mk_cls sxs [] xH) as [sxcs tbl] eqn:EC.
  destruct (AX2C.mk_cls_ok _ _ _ _ _ AX2C.CT_OK_nil EC) as (Hms & HN & _ & HC). cbn [fst].
  rewrite (fp_chain_eq fk tbl wbs r sxcs [] HN HC).
  - rewrite Hms. unfold fp_apartB.
    transitivity (forallb (fun s => match s with SE a w _ => ranges_apart_xB (mkbc fk) (a_base a) (a_off a) (elen w) (fst r) 0 (snd r) end) (map strip sxs)).
    + rewrite forallb_mapL. reflexivity.
    + rewrite Hmap, forallb_rev. unfold log. rewrite forallb_mapL. reflexivity.
  - rewrite Hms. intros sx Hin. rewrite Forall_forall in HS0. exact (proj2 (proj2 (HS0 sx Hin))).
  - apply AX2C.MOK_nil.
Qed.
Lemma gkeep1M_eqf : forall G k wbs W, gkeep1M G (mkbc k) wbs (gk_prep (mkbc k) W) = gkeep1 G k W.
Proof.
  intros. apply functional_extensionality; intros nx. apply functional_extensionality; intros g.
  unfold gkeep1M, gkeep1, fp_apart. f_equal. apply forallb_ext. intros r. rewrite fp_apartM_eq. unfold fp_apartB.
  rewrite ranges_apart_xB_eqf. reflexivity.
Qed.
Lemma gkeepM_eq : gkeepM = gkeep.
Proof.
  apply functional_extensionality; intros G. apply functional_extensionality; intros W.
  apply functional_extensionality; intros cs. apply functional_extensionality; intros cs'.
  unfold gkeepM, gkeep. destruct (a_props cs) as [|g0 props]; [reflexivity|].
  destruct W as [|w0 W']; [|cbv zeta; rewrite gkeep1M_eqf; reflexivity].
  f_equal. apply filter_ext. intros g. unfold gkeep1, fp_apart. cbn [forallb].
  replace (forallb (fun _ : expr * expr => true) (g_fp G (g_id g) (g_args g))) with true; [rewrite andb_true_r; reflexivity|].
  symmetry. apply forallb_forall. reflexivity.
Qed.
Lemma aluop_eqb_refl : forall o, aluop_eqb o o = true.   Proof. intros []; reflexivity. Qed.
Lemma mulop_eqb_refl : forall o, mulop_eqb o o = true.   Proof. intros []; reflexivity. Qed.
Lemma expr_eqb_refl : forall e, expr_eqb e e = true.
Proof.
  induction e; cbn [expr_eqb]; rewrite ?aluop_eqb_refl, ?mulop_eqb_refl, ?IHe1, ?IHe2, ?IHe, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma gatom_eqb_refl : forall g, gatom_eqb g g = true.
Proof.
  intros [i args]. unfold gatom_eqb. cbn [g_id g_args]. rewrite Nat.eqb_refl. cbn [andb].
  induction args as [|a l IH]; [reflexivity|]. cbn [list_eqb]. rewrite expr_eqb_refl. exact IH.
Qed.
(* [comment removed for export] *)
Lemma gnew_app : forall cs cs' l, a_props cs' = l ++ a_props cs -> forall g, In g (gnew cs cs') -> In g l.
Proof.
  intros cs cs' l Hl g Hg. unfold gnew in Hg. rewrite Hl in Hg. apply filter_In in Hg as [Hin Hneg].
  apply in_app_or in Hin as [Hin|Hin]; [exact Hin|]. exfalso.
  assert (X : existsb (gatom_eqb g) (a_props cs) = true) by (apply existsb_exists; exists g; split; [exact Hin | apply gatom_eqb_refl]).
  rewrite X in Hneg. discriminate Hneg.
Qed.
Definition vconcl_eqb (a b : vconcl) : bool :=
  match a, b with
  | VCAtom x, VCAtom y => gatom_eqb x y
  | VCFact x, VCFact y => kentry_eqb x y
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition vc_eqb (a b : vc) : bool :=                       (* [comment removed for export] *)
  if vconcl_eqb (vc_concl a) (vc_concl b) then
    if list_eqb gatom_eqb (vc_hyps a) (vc_hyps b) then list_eqb kentry_eqb (vc_kn a) (vc_kn b) else false
  else false.


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

(* [comment removed for export] *)
Definition end1B (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr) : option Z :=
  match sp_rng sp, sp_h1 sp with
  | Some (lo1, hi1), Some h1 => end_hiB bc b1 k1 n1 lo1 hi1 h1
  | _, _ => None
  end.
Definition ranges_apart_pHB (bc : bctx) (sp : sprep) (e1o : option Z) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, base_rangeB bc b2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sidesB bc (sp_D sp) b2 k2 m2 then true
      else lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, base_rangeB bc b2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else
            if match e1o with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma ranges_apart_pHB_eq : forall bc sp b1 k1 n1 b2 k2 n2,
  ranges_apart_pHB bc sp (end1B bc sp b1 k1 n1) b1 k1 n1 b2 k2 n2 = ranges_apart_pB bc sp b1 k1 n1 b2 k2 n2.
Proof.
  intros. unfold ranges_apart_pHB, ranges_apart_pB, end1B.
  destruct (sp_rng sp) as [[lo1 hi1]|], (sp_h1 sp) as [h1|]; reflexivity.
Qed.
Definition kentry_apart_bpHB (bc : bctx) (sp : sprep) (e1o : option Z) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_pHB bc sp e1o ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_pHB bc sp e1o ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_pHB bc sp e1o ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_pHB bc sp e1o ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_pHB bc sp e1o ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_pHB bc sp e1o ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_pHB bc sp e1o ub uk un b k l
  end.
Lemma kentry_apart_bpHB_eq : forall bc sp ub uk un K,
  kentry_apart_bpHB bc sp (end1B bc sp ub uk un) ub uk un K = kentry_apart_bpB bc sp ub uk un K.
Proof. intros. destruct K as [[? ?] ? ?|[? ?] ?|[? ?] ? ?| | | |[? ?] ?| |[? ?] ? ?|[? ?] ?]; cbn [kentry_apart_bpHB kentry_apart_bpB]; rewrite ?ranges_apart_pHB_eq; reflexivity. Qed.



Definition kimg_b (K : kentry) : bool := match K with KImg _ _ => true | _ => false end.

(* [comment removed for export] *)
Definition kn_unfill (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bp k sp ub uk un K) k.

Definition kn_unfillB0 (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bpB bc sp ub uk un K) (bc_fk bc).
(* [comment removed for export] *)
Definition kn_unfillB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  let e1 := end1B bc sp ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bpHB bc sp e1 ub uk un K) (bc_fk bc).
Lemma kn_unfillB_eq0 : forall bc ub uk un, kn_unfillB bc ub uk un = kn_unfillB0 bc ub uk un.
Proof. intros. unfold kn_unfillB, kn_unfillB0. cbv zeta. apply filter_ext. intros K. rewrite kentry_apart_bpHB_eq. reflexivity. Qed.

Lemma kn_unfillB_eqf : forall fk, kn_unfillB (mkbc fk) = kn_unfill fk.
Proof. intros. bcfe. rewrite kn_unfillB_eq0. unfold kn_unfillB0, kn_unfill. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_unfillB_eqf : bceq.

Definition kn_unfillM (k : list kentry) := kn_unfillB (mkbc k).
Lemma kn_unfillM_eq : kn_unfillM = kn_unfill. Proof. apply functional_extensionality; intros k. unfold kn_unfillM. apply kn_unfillB_eqf. Qed.



(* [comment removed for export] *)
Definition kwr_b (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Definition havoc1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_b k ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | _ => []
       end.

Definition havoc1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bB bc ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
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
       | _ => []
       end.

Definition havoc1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bpB bc sp ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma havoc1pB_eqf : forall fk, havoc1pB (mkbc fk) = havoc1p fk.
Proof. intros. bcfe. unfold havoc1pB, havoc1p. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite havoc1pB_eqf : bceq.


Definition kn_havoc (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (havoc1p k sp ub uk un) k.

Definition kn_havocB0 (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (havoc1pB bc sp ub uk un) (bc_fk bc).
(* [comment removed for export] *)
Definition havoc1pHB (bc : bctx) (sp : sprep) (e1o : option Z) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bpHB bc sp e1o ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | _ => []
       end.
Definition kn_havocB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  let e1 := end1B bc sp ub uk un in
  List.flat_map (havoc1pHB bc sp e1 ub uk un) (bc_fk bc).
Lemma kn_havocB_eq0 : forall bc ub uk un, kn_havocB bc ub uk un = kn_havocB0 bc ub uk un.
Proof.
  intros. unfold kn_havocB, kn_havocB0. cbv zeta. apply flat_map_ext. intros K. unfold havoc1pHB, havoc1pB.
  rewrite kentry_apart_bpHB_eq. reflexivity.
Qed.

Lemma kn_havocB_eqf : forall fk, kn_havocB (mkbc fk) = kn_havoc fk.
Proof. intros. bcfe. rewrite kn_havocB_eq0. unfold kn_havocB0, kn_havoc. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.

Definition kn_havocM (k : list kentry) := kn_havocB (mkbc k).
Lemma kn_havocM_eq : kn_havocM = kn_havoc. Proof. apply functional_extensionality; intros k. unfold kn_havocM. apply kn_havocB_eqf. Qed.



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

Definition kn_cutoutB0 (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (cutout1pB bc sp ub uk un) (bc_fk bc).
(* [comment removed for export] *)
Definition cutout1pHB (bc : bctx) (sp : sprep) (e1o : option Z) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_bpHB bc sp e1o ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cutB bc ub uk un kb kk len
       | _ => []
       end.
Definition kn_cutoutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  let e1 := end1B bc sp ub uk un in
  List.flat_map (cutout1pHB bc sp e1 ub uk un) (bc_fk bc).
Lemma kn_cutoutB_eq0 : forall bc ub uk un, kn_cutoutB bc ub uk un = kn_cutoutB0 bc ub uk un.
Proof.
  intros. unfold kn_cutoutB, kn_cutoutB0. cbv zeta. apply flat_map_ext. intros K. unfold cutout1pHB, cutout1pB.
  rewrite kentry_apart_bpHB_eq. reflexivity.
Qed.

Lemma kn_cutoutB_eqf : forall fk, kn_cutoutB (mkbc fk) = kn_cutout fk.
Proof. intros. bcfe. rewrite kn_cutoutB_eq0. unfold kn_cutoutB0, kn_cutout. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_cutoutB_eqf : bceq.

Definition kn_cutoutM (k : list kentry) := kn_cutoutB (mkbc k).
Lemma kn_cutoutM_eq : kn_cutoutM = kn_cutout. Proof. apply functional_extensionality; intros k. unfold kn_cutoutM. apply kn_cutoutB_eqf. Qed.



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
Fixpoint kwritable (allkn k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xlo allkn wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinside allkn b off (ELit n) wb wk wn)%bool then true
      else kwritable allkn rest b off n
  | _ :: rest => kwritable allkn rest b off n
  end.

Fixpoint kwritableB (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xloB bc wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinsideB bc b off (ELit n) wb wk wn)%bool then true
      else kwritableB bc rest b off n
  | _ :: rest => kwritableB bc rest b off n
  end.

Lemma kwritableB_eqf : forall fk, kwritableB (mkbc fk) = kwritable fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. 
  revert b off n. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kwritableB kwritable]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kwritableB_eqf : bceq.


Fixpoint kwritable_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
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
      else if xinside allkn b off n wb wk wn then true
      else kwritable_x allkn rest b off n
  | _ :: rest => kwritable_x allkn rest b off n
  end.

Fixpoint kwritable_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
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
      else if xinsideB bc b off n wb wk wn then true
      else kwritable_xB bc rest b off n
  | _ :: rest => kwritable_xB bc rest b off n
  end.

Lemma kwritable_xB_eqf : forall fk, kwritable_xB (mkbc fk) = kwritable_x fk.
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. 
  revert b off n. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kwritable_xB kwritable_x]. rewrite IH. autorewrite with bceq. reflexivity.
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
      else if xinside allkn b off n zb zk zn then true
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
      else if xinsideB bc b off n zb zk zn then true
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
      else if (Z.eqb (c' mod 256) (c mod 256) && xinside allkn b off n zb zk zn)%bool then true
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
      else if (Z.eqb (c' mod 256) (c mod 256) && xinsideB bc b off n zb zk zn)%bool then true
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
(* [comment removed for export] *)
Definition mul_srl (a b : expr) : option (expr * Z) :=
  match a, b with
  | ELit c, EAlu ALU_SRL y (ELit j) | EAlu ALU_SRL y (ELit j), ELit c =>
      if (Z.leb 0 j && Z.leb j 48 && Z.eqb (c mod two64) (2 ^ j))%bool then Some (y, j) else None
  | _, _ => None
  end.
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := m mod two64 in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', s + (2 ^ j - 1))
      else (e, 0)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', s1 + s2)
  | EMd M_MUL a b => match mul_srl a b with Some (y, j) => (y, 2 ^ j - 1) | None => (e, 0) end   (* [comment removed for export] *)
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
Fixpoint drop_ixsN (ixs : list N) (i : N) (k : list kentry) : list kentry :=
  match k with
  | [] => []
  | K :: r => if existsb (N.eqb i) ixs then drop_ixsN ixs (N.succ i) r else K :: drop_ixsN ixs (N.succ i) r
  end.
Definition drop_ixsF (ixs : list nat) (i : nat) (k : list kentry) : list kentry := drop_ixsN (map N.of_nat ixs) (N.of_nat i) k.
Lemma existsb_N_of_nat : forall i ixs, existsb (N.eqb (N.of_nat i)) (map N.of_nat ixs) = existsb (Nat.eqb i) ixs.
Proof.
  intros i ixs. induction ixs as [|j r IH]; [reflexivity|]. cbn [map existsb]. rewrite IH. f_equal.
  destruct (Nat.eqb i j) eqn:E.
  - apply Nat.eqb_eq in E. subst. apply N.eqb_refl.
  - apply N.eqb_neq. intros H. apply Nat2N.inj in H. apply Nat.eqb_neq in E. contradiction.
Qed.
Lemma drop_ixsF_eq : forall ixs i k, drop_ixsF ixs i k = drop_ixs ixs i k.
Proof.
  intros ixs i k. unfold drop_ixsF. revert i. induction k as [|K r IH]; intros i; [reflexivity|].
  cbn [drop_ixsN drop_ixs]. rewrite existsb_N_of_nat, <- Nat2N.inj_succ, IH. reflexivity.
Qed.
Lemma drop_ixsF_eqf : drop_ixsF = drop_ixs.
Proof.
  apply functional_extensionality; intros ixs. apply functional_extensionality; intros i. apply functional_extensionality; intros k.
  apply drop_ixsF_eq.
Qed.

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

(* [comment removed for export] *)
Definition node_droprange (cs : acs) (b n : expr) : acs :=
  let '(bb, bk) := split_lit b in set_kn cs (kn_havoc (kn cs) bb bk n).

(* [comment removed for export] *)
Definition node_bump (cs : acs) (m : nat) : option acs :=
  if Nat.leb (nxt cs) m then Some (bump cs (m - nxt cs)) else None.

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
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside k b off n (am_base m) 0 (am_len m)) ms.

Definition find_containingB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinsideB bc b off n (am_base m) 0 (am_len m)) ms.

Lemma find_containingB_eqf : forall fk, find_containingB (mkbc fk) = find_containing fk.
Proof. intros. bcfe. unfold find_containingB, find_containing. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lit_lazy_iv (m : amap) : option (Z * Z) :=
  match am_kind m, am_base m, am_len m with
  | KRWLAZY, ELit b, ELit l | KNONELAZY, ELit b, ELit l =>
      if (Z.leb 0 b && Z.ltb 0 l && Z.ltb (b + l) two64)%bool then Some (b, l) else None
  | _, _, _ => None
  end.
Definition lit_lazy_ivs (ms : list amap) : list (Z * Z) :=
  flat_map (fun m => match lit_lazy_iv m with Some p => [p] | None => [] end) ms.
(* [comment removed for export] *)
Fixpoint band_left (ivs : list (Z * Z)) (lo : Z) (fuel : nat) : Z :=
  match fuel with
  | O => lo
  | S f => match List.find (fun p => Z.eqb (fst p + snd p) lo) ivs with
           | Some p => band_left ivs (fst p) f
           | None => lo
           end
  end.
Fixpoint band_right (ivs : list (Z * Z)) (hi : Z) (fuel : nat) : Z :=
  match fuel with
  | O => hi
  | S f => match List.find (fun p => Z.eqb (fst p) hi) ivs with
           | Some p => band_right ivs (fst p + snd p) f
           | None => hi
           end
  end.
(* [comment removed for export] *)
Definition shadow_band (ms : list amap) : option (Z * Z) :=
  if plain A then None else
  let ivs := lit_lazy_ivs ms in
  match List.find (fun p => (Z.leb (fst p) (shadow_off A) && Z.ltb (shadow_off A) (fst p + snd p))%bool) ivs with
  | Some p => Some (band_left ivs (fst p) (length ivs), band_right ivs (fst p + snd p) (length ivs))
  | None => None
  end.
(* [comment removed for export] *)
Definition lit_rwlazy_cover (ms : list amap) (lo hi : Z) : bool :=
  existsb (fun m => match am_kind m, lit_lazy_iv m with
                    | KRWLAZY, Some (b, l) => (Z.leb b lo && Z.leb hi (b + l))%bool
                    | _, _ => false
                    end) ms.
(* [comment removed for export] *)
Definition band_host (k : list kentry) (ms : list amap) (bb : expr) (bk : Z) (n : expr) (sb : expr) (sk : Z) (sn : expr) : bool :=
  match shadow_band ms with
  | Some (L0, L3) =>
      match base_range k bb, xhi k n with
      | Some (blo, bhi), Some nh =>
          (Z.eqb (L0 mod 8) 0 && Z.eqb (L3 mod 8) 0 && Z.ltb 0 L0 && Z.ltb L0 L3 && Z.ltb L3 two64
           && Z.leb 0 (blo + bk) && Z.leb (bhi + bk + nh) ATOP_MAX && flat_x k sb sk sn
           && ranges_apart_x k (ELit 0) L0 (ELit (L3 - L0)) bb bk n
           && lit_rwlazy_cover ms (shadow_off A) (shadow_off A + L0 / 8)
           && lit_rwlazy_cover ms (shadow_off A + L3 / 8) (shadow_off A + ATOP_MAX / 8))%bool
      | _, _ => false
      end
  | None => false
  end.
Definition band_hostB (bc : bctx) (ms : list amap) (bb : expr) (bk : Z) (n : expr) (sb : expr) (sk : Z) (sn : expr) : bool :=
  match shadow_band ms with
  | Some (L0, L3) =>
      match base_rangeB bc bb, xhiB bc n with
      | Some (blo, bhi), Some nh =>
          (Z.eqb (L0 mod 8) 0 && Z.eqb (L3 mod 8) 0 && Z.ltb 0 L0 && Z.ltb L0 L3 && Z.ltb L3 two64
           && Z.leb 0 (blo + bk) && Z.leb (bhi + bk + nh) ATOP_MAX && flat_xB bc sb sk sn
           && ranges_apart_xB bc (ELit 0) L0 (ELit (L3 - L0)) bb bk n
           && lit_rwlazy_cover ms (shadow_off A) (shadow_off A + L0 / 8)
           && lit_rwlazy_cover ms (shadow_off A + L3 / 8) (shadow_off A + ATOP_MAX / 8))%bool
      | _, _ => false
      end
  | None => false
  end.
Lemma band_hostB_eqf : forall fk, band_hostB (mkbc fk) = band_host fk.
Proof. intros. bcfe. unfold band_hostB, band_host. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite band_hostB_eqf : bceq.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_band (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match shadow_band ms with
  | Some (L0, L3) =>
      match base_range k b, xhi k len with
      | Some (lo, hi), Some lh =>
          if (Z.leb L0 (lo + off) && Z.leb (hi + off + lh) L3)%bool then true
          else (Z.leb L0 (lo + off) && Z.leb 0 (lo + off) && Z.ltb (hi + off + lh) two64
                && match xhi k (eadd (eaddz b off) len) with Some e => Z.leb e L3 | None => false end)%bool
      | _, _ => false
      end
  | None => false
  end.
Definition in_bandB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match shadow_band ms with
  | Some (L0, L3) =>
      match base_rangeB bc b, xhiB bc len with
      | Some (lo, hi), Some lh =>
          if (Z.leb L0 (lo + off) && Z.leb (hi + off + lh) L3)%bool then true
          else (Z.leb L0 (lo + off) && Z.leb 0 (lo + off) && Z.ltb (hi + off + lh) two64
                && match xhiB bc (eadd (eaddz b off) len) with Some e => Z.leb e L3 | None => false end)%bool
      | _, _ => false
      end
  | None => false
  end.
Lemma in_bandB_eqf : forall fk, in_bandB (mkbc fk) = in_band fk.
Proof. intros. bcfe. unfold in_bandB, in_band. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite in_bandB_eqf : bceq.


(* [comment removed for export] *)
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).

Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrlB bc b 3) (ELit (shadow_off A))) in (sb, sk, mkSrlB bc n 3).

Lemma shadow_ofB_eqf : forall fk, shadow_ofB (mkbc fk) = shadow_of fk.
Proof. intros. bcfe. unfold shadow_ofB, shadow_of. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shadow_host (k : list kentry) (ms : list amap) (b n : expr) : bool :=
  let '(sb, sk, sn) := shadow_of k b n in
  match find_containing k ms [KRWLAZY] sb sk sn with
  | Some _ => true
  | None => if plain A then false else let '(bb, bk) := split_lit b in band_host k ms bb bk n sb sk sn
  end.
Definition shadow_hostB (bc : bctx) (ms : list amap) (b n : expr) : bool :=
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match find_containingB bc ms [KRWLAZY] sb sk sn with
  | Some _ => true
  | None => if plain A then false else let '(bb, bk) := split_lit b in band_hostB bc ms bb bk n sb sk sn
  end.
Lemma shadow_hostB_eqf : forall fk, shadow_hostB (mkbc fk) = shadow_host fk.
Proof. intros. bcfe. unfold shadow_hostB, shadow_host. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite shadow_hostB_eqf : bceq.

Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in
  if shadow_host k ms b n then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].
(* [comment removed for export] *)
Definition xinside_joint (k : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  novars b2 &&
  match xlo k b2, xhi k b2, base_range k b1, xhi k n1, xlo k n2, xhi k (eadd (eaddz b1 k1) n1) with
  | Some lo2, Some hi2, Some (lo1, hi1), Some h1, Some l2, Some e =>
      Z.eqb lo2 hi2 && Z.leb (lo2 + k2) (lo1 + k1) && Z.leb 0 (lo1 + k1) && Z.ltb (hi1 + k1 + h1) two64 && Z.leb e (lo2 + k2 + l2)
  | _, _, _, _, _, _ => false
  end.
Definition xinside_j (k : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  xinside k b1 k1 n1 b2 k2 n2 || xinside_joint k b1 k1 n1 b2 k2 n2.
Definition find_containing_j (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside_j k b off n (am_base m) 0 (am_len m)) ms.
(* [comment removed for export] *)
Definition shadow_facts_in (k : list kentry) (m : amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in
  match find_containing_j k [m] [KRWLAZY] sb sk sn with
  | Some _ => [KWr (SA sb sk) sn; KZero (SA sb sk) sn]
  | None => []
  end.

Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_ofB bc b n in
  if shadow_hostB bc ms b n then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].

Lemma shadow_factsB_eqf : forall fk, shadow_factsB (mkbc fk) = shadow_facts fk.
Proof. intros. bcfe. unfold shadow_factsB, shadow_facts. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite shadow_factsB_eqf : bceq.



(* [comment removed for export] *)
Definition vis_cost (nhi : Z) : Z := nhi + nhi / 8 + 16384.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_f3_for (k : list kentry) (bb : expr) (bk : Z) (n : expr) (K : kentry) : bool :=
  match K with
  | KDisj (SA sb so) (ELit sl) (SA c2 o2) n2 =>
      if (expr_eqb sb e_sp0 && Z.eqb so (- STK_BELOW) && Z.eqb sl STK_LEN)%bool then sub_itv_x k bb bk n (SA c2 o2) n2 else false
  | _ => false
  end.
Definition ends_below_stack (k : list kentry) (bb : expr) (bk : Z) (n : expr) : bool :=
  match base_range k bb, xhi k n, xlo k e_sp0 with
  | Some (_, bhi), Some nh, Some slo =>
      if Z.ltb (bhi + bk + nh) (slo - STK_BELOW + STK_LEN) then existsb (is_f3_for k bb bk n) k else false
  | _, _, _ => false
  end.
Definition is_f3_forB (bc : bctx) (bb : expr) (bk : Z) (n : expr) (K : kentry) : bool :=
  match K with
  | KDisj (SA sb so) (ELit sl) (SA c2 o2) n2 =>
      if (expr_eqb sb e_sp0 && Z.eqb so (- STK_BELOW) && Z.eqb sl STK_LEN)%bool then sub_itv_xB bc bb bk n (SA c2 o2) n2 else false
  | _ => false
  end.
Definition ends_below_stackB (bc : bctx) (bb : expr) (bk : Z) (n : expr) : bool :=
  match base_rangeB bc bb, xhiB bc n, xloB bc e_sp0 with
  | Some (_, bhi), Some nh, Some slo =>
      if Z.ltb (bhi + bk + nh) (slo - STK_BELOW + STK_LEN) then existsb (is_f3_forB bc bb bk n) (bc_fk bc) else false
  | _, _, _ => false
  end.
Lemma ends_below_stackB_eqf : forall fk, ends_below_stackB (mkbc fk) = ends_below_stack fk.
Proof.
  intros. bcfe. unfold ends_below_stackB, ends_below_stack. autorewrite with bceq.
  destruct (base_range fk _) as [[? ?]|]; [|reflexivity]. destruct (xhi fk _); [|reflexivity]. destruct (xlo fk _); [|reflexivity].
  destruct (Z.ltb _ _); [|reflexivity]. f_equal. apply functional_extensionality; intros K.
  unfold is_f3_forB, is_f3_for. destruct K as [| | | | | | |[? ?] [| | | | | | |] [? ?] ?| |]; try reflexivity. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite ends_below_stackB_eqf : bceq.
Definition foot_apart (k : list kentry) (bb : expr) (bk : Z) (n : expr) (pbase : expr) : bool :=
  if (negb (plain A) && Z.leb 12 (ealign k (eaddz bb bk)) && Z.leb 12 (ealign k n) && Z.leb 12 (ealign k pbase))%bool
  then if ends_below_stack k bb bk n then lin_ge0 k [(pbase, 4095 + STK_BELOW)] [(e_sp0, 0)] else false
  else false.
Definition foot_apartB (bc : bctx) (bb : expr) (bk : Z) (n : expr) (pbase : expr) : bool :=
  if (negb (plain A) && Z.leb 12 (ealignB bc (eaddz bb bk)) && Z.leb 12 (ealignB bc n) && Z.leb 12 (ealignB bc pbase))%bool
  then if ends_below_stackB bc bb bk n then lin_ge0B bc [(pbase, 4095 + STK_BELOW)] [(e_sp0, 0)] else false
  else false.
Lemma foot_apartB_eqf : forall fk, foot_apartB (mkbc fk) = foot_apart fk.
Proof. intros. bcfe. unfold foot_apartB, foot_apart. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite foot_apartB_eqf : bceq.

(* [comment removed for export] *)
Definition vis_add_ref (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
  let k0 := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k0 b n in
  match xhi k0 n with
  | Some nhi =>
  if (Z.leb 3 (ealign k0 b) && Z.leb 3 (ealign k0 n) && flat_x k0 bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && (plain A (* [comment removed for export] *)
          || forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p)
                           && (if ranges_apart_x k0 bb bk n pb pk (snd p) then true else foot_apart k0 bb bk n (fst p))   (* [comment removed for export] *)
                           && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_vis cs))
      (* [comment removed for export] *)
      && (plain A
          || forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_ghost cs))
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
  match xhiB bc n with
  | Some nhi =>
  if (Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && (plain A (* [comment removed for export] *)
          || forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p)
                           && (if ranges_apart_xB bc bb bk n pb pk (snd p) then true else foot_apartB bc bb bk n (fst p))   (* [comment removed for export] *)
                           && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_vis cs))
      (* [comment removed for export] *)
      && (plain A
          || forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_ghost cs))
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_factsB bc (a_maps cs) b n ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.

Lemma vis_add_eq : forall cs b n k, vis_add cs b n k = vis_add_ref cs b n k.
Proof. intros. unfold vis_add, vis_add_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?shadow_factsB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?foot_apartB_eqf. reflexivity. Qed.

(* [comment removed for export] *)
Definition stack_vis_base : expr := eaddz e_sp0 (- STK_BELOW).
Definition is_stack_vis (p : expr * expr) : bool := expr_eqb (fst p) stack_vis_base.
(* [comment removed for export] *)
Definition below_foot (k : list kentry) (pb : expr) (pk : Z) (pn : expr) : bool :=
  if (Z.leb 12 (ealign k (eaddz pb pk)) && Z.leb 12 (ealign k pn))%bool then ends_below_stack k pb pk pn else false.   (* [comment removed for export] *)
Definition vis_foot (cs : acs) (B : expr) (n : Z) : option acs :=
  if plain A then None else
  let k := kn cs in
  let ne := ELit n in
  let '(bb, bk) := split_lit B in
  let '(sb, sk, sn) := shadow_of k B ne in
  let '(hb, hk, hn) := shadow_of k stack_vis_base (ELit 8) in      (* [comment removed for export] *)
  let wlen := esub (eaddz sb (sk + n / 8)) (eaddz hb hk) in         (* [comment removed for export] *)
  match xlo k B, xhi k B with
  | Some blo, Some bhi =>
      if (Z.leb 12 (ealign k B) && Z.ltb 0 n && Z.leb n (2 ^ 20) && Z.eqb (n mod 4096) 0
          && Z.leb 0 blo && Z.ltb (bhi + n) two64
          && flat_x k bb bk ne && flat_x k sb sk sn
          && expr_vars_lt (nxt cs) B
          && lin_ge0 k [(B, 4095 + STK_BELOW)] [(e_sp0, 0)]
          && lit_rwlazy_cover (a_maps cs) (shadow_off A + blo / 8) (shadow_off A + (bhi + n) / 8)
          && existsb is_stack_vis (a_vis cs)
          && flat_x k hb hk wlen && kwritable_x k k hb hk wlen
          && forallb (fun p => is_stack_vis p
                               || (let '(pb, pk) := split_lit (fst p) in
                                   flat_x k pb pk (snd p)
                                   && (if ranges_apart_x k bb bk ne pb pk (snd p) then true else below_foot k pb pk (snd p))
                                   && ranges_apart_x k sb sk sn pb pk (snd p))) (a_vis cs)
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               flat_x k pb pk (snd p) && ranges_apart_x k sb sk sn pb pk (snd p)) (a_ghost cs)
          && Z.leb (a_eager cs + a_abytes cs + vis_cost n) LIMIT)%bool
      then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (KWr (SA sb sk) sn :: kimg_clip k) (nxt cs))   (* [comment removed for export] *)
                    (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                    ((B, ne) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost n) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition xn_visfoot (args : list expr) (cs : acs) : option acs :=
  match args with
  | [B; ELit n] => vis_foot cs B n
  | _ => None
  end.


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
(* [comment removed for export] *)
Fixpoint find_disj_off_all (k : list kentry) (c1 : expr) (z1 : Z) (c2 : expr) (z2 : Z) : list (expr * Z * expr * expr * Z * expr) :=
  match k with
  | [] => []
  | KDisj (SA d1 o1) n1 (SA d2 o2) n2 :: r =>
      if (expr_eqb d1 c1 && Z.eqb o1 z1 && expr_eqb d2 c2 && Z.eqb o2 z2)%bool then (d1, o1, n1, d2, o2, n2) :: find_disj_off_all r c1 z1 c2 z2
      else if (expr_eqb d1 c2 && Z.eqb o1 z2 && expr_eqb d2 c1 && Z.eqb o2 z1)%bool then (d2, o2, n2, d1, o1, n1) :: find_disj_off_all r c1 z1 c2 z2
      else find_disj_off_all r c1 z1 c2 z2
  | _ :: r => find_disj_off_all r c1 z1 c2 z2
  end.
Definition disj_litlen (r : expr * Z * expr * expr * Z * expr) : Z :=
  match r with
  | (_, _, n1, _, _, n2) => Z.max (match n1 with ELit z => z | _ => -1 end) (match n2 with ELit z => z | _ => -1 end)
  end.
Fixpoint pick_longest (best : expr * Z * expr * expr * Z * expr) (l : list (expr * Z * expr * expr * Z * expr)) : expr * Z * expr * expr * Z * expr :=
  match l with
  | [] => best
  | r :: l' => pick_longest (if Z.ltb (disj_litlen best) (disj_litlen r) then r else best) l'
  end.
Definition find_disj_off (k : list kentry) (c1 : expr) (z1 : Z) (c2 : expr) (z2 : Z) : option (expr * Z * expr * expr * Z * expr) :=
  match find_disj_off_all k c1 z1 c2 z2 with
  | [] => None
  | r :: l => Some (pick_longest r l)
  end.
Definition find_disj2 (k : list kentry) (b1 b2 : expr) : option (expr * Z * expr * expr * Z * expr) :=
  match find_disj k b1 b2 with
  | Some r => Some r
  | None => let '(c1, z1) := split_lit b1 in let '(c2, z2) := split_lit b2 in find_disj_off k c1 z1 c2 z2
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition disj_side_hi (k : list kentry) (cA : expr) (oA : Z) (n bhi oB : Z) : Z :=
  if plain A then bhi + oB
  else match base_range k cA with
       | Some (alo, _) => let t := bhi + oB - Z.max 0 (alo + oA) in if Z.leb n t then t else bhi + oB   (* [comment removed for export] *)
       | None => bhi + oB
       end.
Definition disj_side_fact (k : list kentry) (cA : expr) (oA : Z) (nA : expr) (cB : expr) (oB : Z) : option kentry :=
  match xlo2 k nA, base_range k cB with
  | Some n, Some (_, bhi) =>
      let hi := disj_side_hi k cA oA n bhi oB in
      if (Z.leb 0 n && Z.leb n hi)%bool then Some (KRange (esub (eaddz cB oB) (eaddz cA oA)) n hi) else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition disj_side_dead (k : list kentry) (cA : expr) (oA : Z) (nA : expr) (cB : expr) (oB : Z) : bool :=
  match xlo2 k nA, base_range k cB, base_range k cA with
  | Some n, Some (_, bhi), Some (alo, _) => Z.ltb (bhi + oB - Z.max 0 (alo + oA)) n
  | _, _, _ => false
  end.
Definition casedisj_dead (cs : acs) (b1 b2 : expr) : bool * bool :=
  match find_disj2 (kn cs) b1 b2 with
  | Some (c1, o1, n1, c2, o2, n2) => (disj_side_dead (kn cs) c1 o1 n1 c2 o2, disj_side_dead (kn cs) c2 o2 n2 c1 o1)
  | None => (false, false)
  end.
(* [comment removed for export] *)
Definition node_casedisjJ (cs : acs) (b1 b2 : expr) : option (acs * option acs) :=
  let k := kn cs in
  match find_disj2 k b1 b2 with
  | Some (c1, o1, n1, c2, o2, n2) =>
      if (flat_x k c1 o1 n1 && flat_x k c2 o2 n2)%bool then
        match disj_side_dead k c1 o1 n1 c2 o2, disj_side_dead k c2 o2 n2 c1 o1 with
        | true, true => None
        | true, false => match disj_side_fact k c2 o2 n2 c1 o1 with Some K2 => Some (add_kn cs [K2], None) | None => None end
        | false, true => match disj_side_fact k c1 o1 n1 c2 o2 with Some K1 => Some (add_kn cs [K1], None) | None => None end
        | false, false =>
            match disj_side_fact k c1 o1 n1 c2 o2, disj_side_fact k c2 o2 n2 c1 o1 with
            | Some K1, Some K2 => Some (add_kn cs [K1], Some (add_kn cs [K2]))
            | _, _ => None
            end
        end
      else None
  | None => None
  end.
Definition node_casedisj (cs : acs) (b1 b2 : expr) : option (acs * acs) :=
  let k := kn cs in
  match find_disj2 k b1 b2 with   (* [comment removed for export] *)
  | Some (c1, o1, n1, c2, o2, n2) =>
      match flat_x k c1 o1 n1, flat_x k c2 o2 n2, disj_side_fact k c1 o1 n1 c2 o2, disj_side_fact k c2 o2 n2 c1 o1 with
      | true, true, Some K1, Some K2 => Some (add_kn cs [K1], add_kn cs [K2])
      | _, _, _, _ => None
      end
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition end47 (k : list kentry) (b n : expr) (h m : Z) : bool :=
  Z.leb (h + m) (2 ^ 47) || (Z.ltb (h + m) two64 && match xhi k (eadd b n) with Some e => Z.leb e (2 ^ 47) | None => false end).
Definition end47B (bc : bctx) (b n : expr) (h m : Z) : bool :=
  Z.leb (h + m) (2 ^ 47) || (Z.ltb (h + m) two64 && match xhiB bc (eadd b n) with Some e => Z.leb e (2 ^ 47) | None => false end).
Lemma end47B_eqf : forall k, end47B (mkbc k) = end47 k.
Proof. intros. unfold end47B, end47. rewrite xhiB_eqf. reflexivity. Qed.
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
         | Some h1, Some m1, Some h2, Some m2 => end47B bc b1 n1 h1 m1 && end47B bc b2 n2 h2 m2   (* [comment removed for export] *)
         | _, _, _, _ => false end
      && ranges_apart_xB bc c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.

Lemma node_shdisj_eq : forall cs b1 n1 b2 n2, node_shdisj cs b1 n1 b2 n2 = node_shdisj_ref cs b1 n1 b2 n2.
Proof. intros. unfold node_shdisj, node_shdisj_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?end47B_eqf. reflexivity. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition page_up_e (k : list kentry) (le : expr) : expr :=
  mkMd M_MUL (ELit 4096) (mkSrl k (mkAlu ALU_ADD le (ELit 4095)) 12).

Definition mmap_len_ref (cs : acs) : option (expr * Z * Z) :=
  match reg_lit cs 11 with
  | Some len => if Z.ltb 0 len then Some (ELit (page_up len), page_up len, page_up len) else None
  | None =>
      let le := reg cs 11 in let k := kn cs in
      match xlo k le, xhi k le with
      | Some lo, Some hi =>
          if (Z.ltb 0 lo && Z.leb hi (2 ^ 46))%bool then
            if Z.leb 12 (ealign k le) then Some (le, lo, hi)
            else let ne := page_up_e k le in
                 (* [comment removed for export] *)
                 match xlo k ne, xhi k ne with
                 | Some a, Some b => if Z.eqb a b then Some (ELit a, lo, a)
                                     else if expr_vars_lt (nxt cs) ne then Some (ne, lo, page_up hi) else None
                 | _, _ => if expr_vars_lt (nxt cs) ne then Some (ne, lo, page_up hi) else None
                 end
          else None
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
          if (Z.ltb 0 lo && Z.leb hi (2 ^ 46))%bool then
            if Z.leb 12 (ealignB bc le) then Some (le, lo, hi)
            else let ne := page_up_e k le in
                 match xloB bc ne, xhiB bc ne with
                 | Some a, Some b => if Z.eqb a b then Some (ELit a, lo, a)
                                     else if expr_vars_lt (nxt cs) ne then Some (ne, lo, page_up hi) else None
                 | _, _ => if expr_vars_lt (nxt cs) ne then Some (ne, lo, page_up hi) else None
                 end
          else None
      | _, _ => None
      end
  end.

Lemma mmap_len_eq : forall cs, mmap_len cs = mmap_len_ref cs.
Proof. intros. unfold mmap_len, mmap_len_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?xhiB_eqf, ?xloB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Fixpoint inside_maps (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinside k b off len (am_base m) 0 (am_len m)) || inside_maps k rest b off len
  end.

Fixpoint inside_mapsB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinsideB bc b off len (am_base m) 0 (am_len m)) || inside_mapsB bc rest b off len
  end.

Lemma inside_mapsB_eqf : forall fk, inside_mapsB (mkbc fk) = inside_maps fk.
Proof.
  intros fk. apply functional_extensionality; intros ms. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros len. 
  revert b off len. induction ms as [|m rest IH]; intros; bcfe; [reflexivity|].
  cbn [inside_mapsB inside_maps]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite inside_mapsB_eqf : bceq.



(* [comment removed for export] *)
Definition on_stack_side (k : list kentry) (b : expr) (off : Z) : bool :=
  if expr_eqb b e_sp0 then Z.leb (- STK_BELOW) off
  else if shares_var b e_sp0 then lin_ge0 k [(b, off + STK_BELOW)] [(e_sp0, 0)] else false.
Definition on_stack_sideB (bc : bctx) (b : expr) (off : Z) : bool :=
  if expr_eqb b e_sp0 then Z.leb (- STK_BELOW) off
  else if shares_var b e_sp0 then lin_ge0B bc [(b, off + STK_BELOW)] [(e_sp0, 0)] else false.
Lemma on_stack_sideB_eqf : forall fk, on_stack_sideB (mkbc fk) = on_stack_side fk.
Proof. intros. bcfe. unfold on_stack_sideB, on_stack_side. rewrite ?lin_ge0B_eqf. reflexivity. Qed.
#[local] Hint Rewrite on_stack_sideB_eqf : bceq.

Definition safe_range (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhi k len with
    | Some lh =>
        on_stack_side k b off                                                        (* [comment removed for export] *)
        || match base_range k b with
           | Some (lo, hi) => (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
           | None => false
           end
    | None => false
    end) || inside_maps k ms b off len
   || in_band k ms b off len)%bool.   (* [comment removed for export] *)

Definition safe_rangeB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhiB bc len with
    | Some lh =>
        on_stack_sideB bc b off                                                      (* [comment removed for export] *)
        || match base_rangeB bc b with
           | Some (lo, hi) => (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
           | None => false
           end
    | None => false
    end) || inside_mapsB bc ms b off len
   || in_bandB bc ms b off len)%bool.   (* [comment removed for export] *)

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

Definition kn_grant_filterB (bc : bctx) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_bB bc ms) (bc_fk bc)).

Lemma kn_grant_filterB_eqf : forall fk, kn_grant_filterB (mkbc fk) = kn_grant_filter fk.
Proof. intros. bcfe. unfold kn_grant_filterB, kn_grant_filter. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_grant_filterB_eqf : bceq.



(* [comment removed for export] *)
Definition gap_ok (cs : acs) (nhi : Z) : bool :=
  let cnt := Z.of_nat (n_res A + length (a_maps cs))%nat in
  Z.leb (FLOOR + nhi + a_totsz cs + cnt * (nhi + 4095)) CEIL.

Definition budget_ok (cs : acs) (extra : Z) : bool :=
  Z.leb (a_eager cs + a_abytes cs + extra) LIMIT.

(* [comment removed for export] *)
Definition lit_side (mb : expr) : saddr :=
  match mb with
  | ELit z => if (Z.leb 0 z && Z.ltb z two64)%bool then SA (ELit 0) z else SA mb 0
  | _ => SA mb 0
  end.
(* [comment removed for export] *)
Definition kdisj_band (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  match shadow_band ms with
  | Some (L0, L3) => [KDisj (SA (ELit 0) L0) (ELit (L3 - L0)) (SA nb 0) ne]
  | None => []
  end.
Definition kdisj_new0 (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else [KDisj (lit_side (am_base m)) (am_len m) (SA nb 0) ne]) ms.
Definition kdisj_new (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  kdisj_new0 ms nb ne ++ kdisj_band ms nb ne.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition grant_lo (ms : list amap) (nlo : Z) : Z :=
  match shadow_band ms with
  | Some (L0, L3) => if (Z.ltb L0 (4096 + nlo) && Z.eqb (L3 mod 4096) 0)%bool then L3 / 4096 else 1
  | None => 1
  end.
Definition kabove_band (ms : list amap) (v : nat) (nlo : Z) : list kentry := [].
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kend_sp (base ne : expr) : list kentry := [].

(* [comment removed for export] *)
Definition with_maps0 (cs : acs) (ms : list amap) : acs :=
  ACSG (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_props cs).

(* [comment removed for export] *)
Definition add_entry (cs : acs) (sr : list expr) (k' : list kentry) (nx' : nat)
           (m : amap) (nhi : Z) (eager : bool) (ylo' : Z) : acs :=
  ACS (mk_ss (pc cs + 4) sr k' nx')
      (m :: a_maps cs) (a_totsz cs + nhi) ylo'
      (if eager then a_eager cs + nhi else a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition null_kend (base ne : expr) (nlo : Z) : list kentry :=
  match ne with
  | ELit _ => []
  | _ => [KRange (eadd base ne) (4096 + nlo) ATOP_MAX]
  end.

(* [comment removed for export] *)
Definition stack_side : saddr := SA e_sp0 (- STK_BELOW).
Definition hull_side : saddr := SA (ELit 0) (img_lo A).
Definition grant_facts (v : nat) (base ne : expr) (nlo : Z) (ms : list amap) : list kentry :=
  KRange (EVar v) (grant_lo ms nlo) ((ATOP_MAX - nlo) / 4096)                    (* [comment removed for export] *)
  :: null_kend base ne nlo                                                         (* [comment removed for export] *)
  ++ KDisj stack_side (ELit STK_LEN) (SA base 0) ne                                (* [comment removed for export] *)
  :: KDisj hull_side (ELit (img_hi A - img_lo A)) (SA base 0) ne                   (* [comment removed for export] *)
  :: kdisj_new ms base ne                                                          (* [comment removed for export] *)
  ++ kabove_band ms v nlo                                                          (* [comment removed for export] *)
  ++ kend_sp base ne.                                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_null (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && no_holes (a_maps cs))%bool then     (* [comment removed for export] *)
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let kfacts := grant_facts v base ne nlo (a_maps cs) in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filter (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs) in
        if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition fixed_args (cs : acs) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && Z.leb (ahi + nhi) CEIL
          && (Z.leb (ahi + nhi) (img_lo A) || Z.leb (img_hi A) alo)
          && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition fixed_args_in (cs : acs) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && Z.leb (ahi + nhi) ATOP_MAX && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.

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
  let ksh := if mkind_eqb kind KRWLAZY then flat_map (fun p => shadow_facts_in k m (fst p) (snd p)) (a_vis cs) else [] in   (* [comment removed for export] *)
  let k' := ksh ++ kn_grant_filter k ms0 in
  let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
  if visible then vis_add cs1 a ne (kmem ++ kn cs1) else Some cs1.

(* [comment removed for export] *)
Definition mmap_fixed_free (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  match fixed_args cs with
  | Some (b, off, ne, nlo, nhi) =>
      if (no_fog (a_maps cs)
          && forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
          && (negb eager || budget_ok cs nhi)
          && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
      then mmap_fixed_grant cs (a_maps cs) b off ne nhi kind eager visible
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition kn_rezero (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => kentry_apart_bp k sp ub uk un K
                        | _ => true
                        end) k.

Definition kn_rezeroB0 (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => kentry_apart_bpB bc sp ub uk un K
                        | _ => true
                        end) (bc_fk bc).
(* [comment removed for export] *)
Definition kn_rezeroB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  let e1 := end1B bc sp ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => kentry_apart_bpHB bc sp e1 ub uk un K
                        | _ => true
                        end) (bc_fk bc).
Lemma kn_rezeroB_eq0 : forall bc ub uk un, kn_rezeroB bc ub uk un = kn_rezeroB0 bc ub uk un.
Proof. intros. unfold kn_rezeroB, kn_rezeroB0. cbv zeta. apply filter_ext. intros K. destruct K; try reflexivity; apply kentry_apart_bpHB_eq. Qed.

Lemma kn_rezeroB_eqf : forall fk, kn_rezeroB (mkbc fk) = kn_rezero fk.
Proof. intros. bcfe. rewrite kn_rezeroB_eq0. unfold kn_rezeroB0, kn_rezero. autorewrite with bceq. reflexivity. Qed.
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
  match fixed_args_in cs with
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
  match fixed_args_in cs with
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
Proof. intros. unfold fixed_in_args, fixed_in_args_ref. unfold ehi, elo. rewrite ?find_containingB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition slice_below_ceil (cs : acs) (nhi : Z) : bool :=
  match xhi (kn cs) (reg cs 10) with Some ahi => Z.leb (ahi + nhi) CEIL | None => false end.

(* [comment removed for export] *)
Definition mmap_fixed_in_ref (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in
      if match arm with ArmE => budget_ok cs nhi | _ => true end then   (* [comment removed for export] *)
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
      if match arm with ArmE => budget_ok cs nhi | _ => true end then   (* [comment removed for export] *)
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

Definition mmap_destroyed (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) : list acs :=
  map (fun lr => mmap_destroyed_with hole cs b off ne m (fst lr) (snd lr)) (dest_cases cs ne m).

(* [comment removed for export] *)
Definition mmap_gate (cs : acs) : option (Z * Z * bool) :=
  match reg_lit cs 17, reg_lit cs 12, reg_lit cs 13, reg_lit cs 14, reg_lit cs 15 with
  | Some 222, Some prot, Some flags, Some m1, Some 0 =>
      if negb (Z.eqb m1 (two64 - 1)) then None
      else Some (prot, flags, match reg_lit cs 10 with Some 0 => true | _ => false end)
  | _, _, _, _, _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_mmap (cs : acs) : option acs :=
  match mmap_gate cs with
  | Some (prot, flags, isnull) =>
      if isnull then
        (* [comment removed for export] *)
        match prot, flags with
        | 3, 0x22 => mmap_null cs KRW true true                 (* [comment removed for export] *)
        | 0, 0x22 => mmap_null cs KNONE false false             (* [comment removed for export] *)
        | 3, 0x4022 => if plain A then None else mmap_null cs KRWLAZY false true      (* [comment removed for export] *)
        | 0, 0x4022 => if plain A then None else mmap_null cs KNONELAZY false false   (* [comment removed for export] *)
        | _, _ => None
        end
      else
        (* [comment removed for export] *)
        match prot, flags with
        | 3, 0x32 => mmap_fixed_free cs KRW true true                                          (* [comment removed for export] *)
        | 0, 0x32 => mmap_fixed_free cs KNONE false false                                      (* [comment removed for export] *)
        | 3, 0x4032 => if plain A then None else mmap_fixed_free cs KRWLAZY false false        (* [comment removed for export] *)
        | 0, 0x4032 => if plain A then None else mmap_fixed_free cs KNONELAZY false false      (* [comment removed for export] *)
        | 3, 0x100022 | 3, 0x100032 => mmap_fixed_free cs KRW true true                        (* [comment removed for export] *)
        | 0, 0x100022 | 0, 0x100032 => mmap_fixed_free cs KNONE false false                    (* [comment removed for export] *)
        | 3, 0x104022 | 3, 0x104032 => if plain A then None else mmap_fixed_free cs KRWLAZY false false     (* [comment removed for export] *)
        | 0, 0x104022 | 0, 0x104032 => if plain A then None else mmap_fixed_free cs KNONELAZY false false   (* [comment removed for export] *)
        | _, _ => None
        end
  | None => None
  end.

(* [comment removed for export] *)
Definition node_mmapin (cs : acs) : option acs :=
  match mmap_gate cs with
  | Some (prot, flags, false) =>
      let arm := match prot, flags with
                 | 3, 0x32 => Some ArmE
                 | 3, 0x4032 => if plain A then None else Some ArmF   (* [comment removed for export] *)
                 | 0, 0x32 => Some ArmG
                 | _, _ => None
                 end in
      match arm with
      | Some arm =>
          match fixed_in_args cs arm with
          | Some _ => mmap_fixed_in cs arm
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_mprotect_ref (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args_in cs with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      match find_containing k (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition node_mprotect (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args_in cs with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match find_containingB bc (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then   (* [comment removed for export] *)
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
Proof. intros. unfold node_mprotect, node_mprotect_ref. unfold ehi, elo. rewrite ?find_containingB_eqf, ?kn_unfillB_eqf. reflexivity. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)

Definition amap_match (k : list kentry) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqb k n (am_len m))%bool.

Definition amap_matchB (bc : bctx) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqbB bc n (am_len m))%bool.

Lemma amap_matchB_eqf : forall fk, amap_matchB (mkbc fk) = amap_match fk.
Proof. intros. bcfe. unfold amap_matchB, amap_match. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite amap_matchB_eqf : bceq.



(* [comment removed for export] *)
Definition node_munmap_ref (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in
      let '(bb, bk) := split_lit b in
      (* [comment removed for export] *)
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (plain A || ranges_apart_x k pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in plain A || ranges_apart_x k pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_match k b ne) (a_maps cs) && page_aligned k b && flat_x k bb bk ne
          && match xhi k b with Some hi => Z.ltb (hi + nhi) two64 | None => false end
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in
                               Z.leb 3 (ealign k (fst p)) && Z.leb 3 (ealign k (snd p))
                               && xinside k pb pk (snd p) bb bk ne && (plain A || kzero_x k k sb sk sn))   (* [comment removed for export] *)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in kn_unfill kk sb sk sn) gone (kn_unfill k bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_match k b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_munmap (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (plain A || ranges_apart_xB bc pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in plain A || ranges_apart_xB bc pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_matchB bc b ne) (a_maps cs) && page_alignedB bc b && flat_xB bc bb bk ne
          && match xhiB bc b with Some hi => Z.ltb (hi + nhi) two64 | None => false end
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in
                               Z.leb 3 (ealignB bc (fst p)) && Z.leb 3 (ealignB bc (snd p))
                               && xinsideB bc pb pk (snd p) bb bk ne && (plain A || kzero_xB bc k sb sk sn))   (* [comment removed for export] *)
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
Proof. intros. unfold node_munmap, node_munmap_ref. unfold ehi, elo. rewrite ?amap_matchB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?kn_unfillB_eqf, ?kzero_xB_eqf, ?page_alignedB_eqf, ?ranges_apart_xB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?xinsideB_eqf, ?kn_unfillM_eq. reflexivity. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_req (cs : acs) : option Z :=
  match lit_diff (reg cs 10) (a_brk cs) with
  | Some d => if (Z.ltb 0 d && Z.eqb (d mod 4096) 0 && Z.leb d (2 ^ 40))%bool then Some d else None
  | None => None
  end.

(* [comment removed for export] *)
Definition brk_base_ok (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (page_aligned k b
   && match xlo k b, xhi k b with
      | Some lo, Some hi => Z.ltb 0 lo && Z.leb (img_hi A) lo && Z.leb (hi + d) KHI
      | _, _ => false
      end)%bool.

(* [comment removed for export] *)
Definition brk_grow_possible (cs : acs) (d : Z) : bool :=
  let k := kn cs in let '(bb, bk) := split_lit (a_brk cs) in
  (brk_base_ok cs d && no_fog (a_maps cs)
   && forallb (fun m => ranges_apart_x k bb bk (ELit (d + 4096)) (am_base m) 0 (am_len m)) (a_maps cs)  (* [comment removed for export] *)
   && budget_ok cs d)%bool.

(* [comment removed for export] *)
Definition brk_grow_blocked (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (brk_base_ok cs d
   && existsb (fun m => negb (is_fog m)
                        && lin_ge0 k [(am_base m, -1); (am_len m, 0)] [(b, 0)]      (* [comment removed for export] *)
                        && lin_ge0 k [(b, d + 4096 - 1)] [(am_base m, 0)])        (* [comment removed for export] *)
              (a_maps cs))%bool.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition node_brk (cs : acs) : option acs :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      if (brk_grow_possible cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
        let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
        let k' := kn_grant_filter k (a_maps cs) in
        let ss := a_ss cs in
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) in
        vis_add csB b (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB)
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_brk2 (cs : acs) : option (acs * acs) :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      if (brk_base_ok cs d && no_fog (a_maps cs) && budget_ok cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
        let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
        let k' := kdisj_new0 (a_maps cs) b (ELit (d + 4096)) ++ kn_grant_filter k (a_maps cs) in
        let ss := a_ss cs in
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) in
        match vis_add csB b (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB) with
        | Some csg => Some (csg, set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4))
        | None => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)

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

(* [comment removed for export] *)

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
  ACSG (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_props cs).

(* [comment removed for export] *)
Definition node_fog (cs : acs) (i : nat) (sz : Z) : option acs :=
  match nth_error (a_maps cs) i with
  | Some m =>
      if (negb (is_fog m) && Z.leb 0 sz && Z.ltb sz two64
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
          && Z.leb 3 (ealign k b) && Z.leb 3 (ealign k n) && flat_x k bb bk n && Z.leb (bh + nh) CEIL
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
Definition node_unvis (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match xhiB bc b, xhiB bc n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n && Z.leb (bh + nh) CEIL
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
            if (Z.eqb c8 0 && kzero_xB bc k db dk ne && kwritable_xB bc k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_xB bc k db dk ne then
              let k1 := kn_havocM k0 db dk ne in
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
Proof. intros. unfold summary_fill, summary_fill_ref. unfold ehi, elo. rewrite ?kwritable_xB_eqf, ?kzero_xB_eqf, ?off_image_xB_eqf, ?xhiB_eqf, ?xloB_eqf, ?kn_havocM_eq. reflexivity. Qed.


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
Definition kblob_prefix (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (nlo : Z) : list kentry :=
  match List.find (fun K => match K with
                             | KBlob (SA b o) (ELit n0) _ => expr_eqb b sb && Z.eqb o sk && Z.ltb 0 n0 && Z.leb n0 nlo
                             | _ => false
                             end) k with
  | Some (KBlob _ (ELit n0) j) => [KBlob (SA db dk) (ELit n0) j]
  | _ => []
  end.
(* [comment removed for export] *)
Definition kblob_same (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (ne : expr) : list kentry :=
  match List.find (fun K => match K with
                             | KBlob (SA b o) n0 _ => expr_eqb b sb && Z.eqb o sk && len_eqb k n0 ne   (* [comment removed for export] *)
                             | _ => false
                             end) k with
  | Some (KBlob _ _ j) => [KBlob (SA db dk) ne j]
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
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_same k sb sk db dk ne ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_x k k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              (* [comment removed for export] *)
              else if match kblob_same k sb sk db dk ne with [] => false | _ => true end then havoc_src
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
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_xB bc k db dk ne && ranges_apart_xB bc db dk ne sb sk ne)%bool then
              let k1 := kn_havocM k0 db dk ne in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_xB bc k sb sk ne && flat_xB bc sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_same k sb sk db dk ne ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_xB bc k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else if match kblob_same k sb sk db dk ne with [] => false | _ => true end then havoc_src
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_xB bc sb sk ne)%bool then
                         match copy_factsB bc (Z.to_nat nhi) sb sk db dk nhi with
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

Lemma summary_copy_eq : forall cs entry, summary_copy cs entry = summary_copy_ref cs entry.
Proof. intros. unfold summary_copy, summary_copy_ref. unfold ehi, elo. rewrite ?copy_factsB_eqf, ?flat_xB_eqf, ?kwritable_xB_eqf, ?kzero_xB_eqf, ?off_image_xB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?xloB_eqf, ?kn_havocM_eq. reflexivity. Qed.


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
Definition summary_popfree (cs : acs) (args : list expr) : option acs :=
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
            let k1 := kn_havoc k lb lk (ELit (4 * cnt)) in
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_readable_x (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
  existsb (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        xinside k rb rk ne kb kk len
                    | _ => false
                    end) k.

(* [comment removed for export] *)
Definition summary_sniff_ref (cs : acs) : option acs :=
  let _ := segs in let _ := A in let _ := nx0 in None.   (* [comment removed for export] *)
Definition summary_sniff (cs : acs) : option acs :=
  let _ := segs in let _ := A in let _ := nx0 in None.

Lemma summary_sniff_eq : forall cs, summary_sniff cs = summary_sniff_ref cs.
Proof. reflexivity. Qed.


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
        let k' := kn_havoc (kimg_cut k p 8) (ELit 0) p (ELit 8) in
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

Definition entails (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && forallb (fun K => existsb (kentry_eqb K) (kn cs)) (kn ch)
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
   && match a_fd cs with FdFile _ l o => evars_all ok l && evars_all ok o | _ => true end
   && forallb (fun g => forallb (evars_all ok) (g_args g)) (a_props cs))%bool.   (* [comment removed for export] *)

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
  let acc := fold_right (fun g acc => fold_right emaxv acc (g_args g)) acc (a_props cs) in   (* [comment removed for export] *)
  emaxv (a_brk cs) acc.

(* [comment removed for export] *)
Definition grename (t : list (option nat)) (g : gatom) : gatom := GA (g_id g) (map (erename t) (g_args g)).
Definition rename_cs (t : list (option nat)) (cs : acs) (nx : nat) : acs :=
  ACSG (mk_ss (pc cs) (map (erename t) (s_regs (a_ss cs))) (map (krename t) (kn cs)) nx)
      (map (mrename t) (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (map (prename t) (a_vis cs)) (map (prename t) (a_ghost cs)) (a_abytes cs)
      (erename t (a_brk cs)) (frename t (a_fd cs)) (a_tidset cs) (map (grename t) (a_props cs)).

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
  let acc := fold_left (fun acc g => fold_left (fun acc e => evars_fo gb e acc) (g_args g) acc) (a_props cs) acc in   (* [comment removed for export] *)
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
Definition kn_incl1_h (k : list kentry) (K : kentry) : bool :=
  if existsb (fun X => kentry_eqb X K) k then true
  else if (if kflat_h k K then existsb (fun X => kentry_eqb_h X K) k else false) then true
  else if kimg_sub_covered k K then true
  else kunk_covered k K.
Definition kn_incl_h (k : list kentry) (tk : list kentry) : bool := forallb (kn_incl1_h k) tk.
(* [comment removed for export] *)
Definition kkey (K : kentry) : option Z :=
  match K with
  | KWord (SA _ kk) _ _ | KZero (SA _ kk) _ | KBlob (SA _ kk) _ _ | KWr (SA _ kk) _ | KFill (SA _ kk) _ _ | KUnk (SA _ kk) _ => Some kk
  | KImg lo _ => Some lo
  | KRange _ lo _ => Some lo
  | KAlign _ m => Some m
  | KDisj (SA _ kk) _ _ _ => Some kk
  end.
Definition zkey (z : Z) : positive := match z with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
Definition knix : Type := ptree (list kentry).
Definition knix_get (t : knix) (z : Z) : list kentry := match pt_get t (zkey z) with Some l => l | None => [] end.
Fixpoint kn_ix (k : list kentry) : knix :=
  match k with
  | [] => PTLeaf
  | K :: rest => let t := kn_ix rest in
                 match kkey K with
                 | Some z => pt_set (zkey z) (K :: knix_get t z) t
                 | None => t
                 end
  end.
Definition kn_memb (t : knix) (K : kentry) : bool :=
  match kkey K with
  | Some z => existsb (fun X => kentry_eqb X K) (knix_get t z)
  | None => false
  end.
Lemma zkey_inj : forall a b, zkey a = zkey b -> a = b.
Proof. intros [|a|a] [|b|b] H; cbn in H; congruence. Qed.
Lemma kkey_some : forall K, exists z, kkey K = Some z.
Proof. intros K. destruct K as [[? ?] ? ?|[? ?] ?|[? ?] ? ?| | | |[? ?] ?|[? ?] ? ? ?|[? ?] ? ?|[? ?] ?]; cbn; eexists; reflexivity. Qed.
Lemma kentry_eqb_kkey : forall X K, kentry_eqb X K = true -> kkey X = kkey K.
Proof.
  intros X K H.
  destruct X as [[xb xk] ? ?|[xb xk] ?|[xb xk] ? ?| | | |[xb xk] ?|[xb xk] ? [? ?] ?|[xb xk] ? ?|[xb xk] ?];
  destruct K as [[kb kk] ? ?|[kb kk] ?|[kb kk] ? ?| | | |[kb kk] ?|[kb kk] ? [? ?] ?|[kb kk] ? ?|[kb kk] ?];
    cbn [kentry_eqb] in H; try discriminate H; unfold saddr_eqb in H; cbn [a_base a_off kkey] in H |- *;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      end; subst; reflexivity.
Qed.
Lemma knix_get_cons : forall t z K z', knix_get (pt_set (zkey z) (K :: knix_get t z) t) z' = if Z.eqb z' z then K :: knix_get t z' else knix_get t z'.
Proof.
  intros t z K z'. unfold knix_get at 1. destruct (Z.eqb_spec z' z) as [->|NE].
  - rewrite pt_gss. reflexivity.
  - rewrite pt_gso; [reflexivity|]. intros E. apply NE. apply zkey_inj. exact E.
Qed.
Lemma kn_memb_eq : forall k K, kn_memb (kn_ix k) K = existsb (fun X => kentry_eqb X K) k.
Proof.
  intros k K. unfold kn_memb. destruct (kkey_some K) as [z Hz]. rewrite Hz.
  induction k as [|X rest IH].
  - cbn. unfold knix_get. rewrite pt_get_leaf. reflexivity.
  - cbn [kn_ix existsb]. destruct (kkey X) as [zx|] eqn:HX.
    + rewrite knix_get_cons. destruct (Z.eqb_spec z zx) as [->|NE].
      * cbn [existsb]. rewrite IH. reflexivity.
      * rewrite IH. destruct (kentry_eqb X K) eqn:E; [|reflexivity].
        exfalso. apply NE. pose proof (kentry_eqb_kkey _ _ E) as Q. rewrite HX, Hz in Q. congruence.
    + rewrite IH. destruct (kentry_eqb X K) eqn:E; [|reflexivity].
      pose proof (kentry_eqb_kkey _ _ E) as Q. rewrite HX, Hz in Q. discriminate.
Qed.
Definition kn_incl1_hM (ix : knix) (k : list kentry) (K : kentry) : bool :=
  if kn_memb ix K then true
  else if (if kflat_h k K then existsb (fun X => kentry_eqb_h X K) k else false) then true
  else if kimg_sub_covered k K then true
  else kunk_covered k K.
Definition kn_incl_hM (k : list kentry) (tk : list kentry) : bool := let ix := kn_ix k in forallb (kn_incl1_hM ix k) tk.
Lemma kn_incl_hM_eq : kn_incl_hM = kn_incl_h.
Proof.
  apply functional_extensionality; intros k. apply functional_extensionality; intros tk.
  unfold kn_incl_hM, kn_incl_h. apply forallb_ext. intros K. unfold kn_incl1_hM, kn_incl1_h. rewrite kn_memb_eq. reflexivity.
Qed.

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
Definition entails_hM (lo hi : nat) (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && match s_resv (a_ss ch) with None => true | _ => false end
   && regs_match_h lo hi [] (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_incl_hM (kn cs) (kn ch)
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
Lemma entails_hM_eq : entails_hM = entails_h.
Proof.
  apply functional_extensionality; intros lo. apply functional_extensionality; intros hi.
  apply functional_extensionality; intros cs. apply functional_extensionality; intros ch.
  unfold entails_hM, entails_h. rewrite kn_incl_hM_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Inductive loopctx : Type :=
| LC (lc_head : Z) (lc_next : acs) (lc_lo lc_hi : nat)
| JC (jc_id : nat) (jc_st : acs) (jc_sh : shape) (jc_b jc_lo : nat)
  (* [comment removed for export] *)
| WC (wc_heads : list acs) (wc_cur : nat) (wc_lo wc_hi : nat) (wc_var : expr) (wc_sh : shape) (wc_exits : list (acs * shape))
   (* [comment removed for export] *)
  (* [comment removed for export] *)
| SC (sc_outs : list acs) (sc_hi : nat).
Definition lc_bnd (c : loopctx) : nat := match c with LC _ _ _ hi => hi | JC _ _ _ b _ => b | WC _ _ _ hi _ _ _ => hi | SC _ hi => hi end.

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
  let knJ := List.filter (fun K => existsb (fun X => kentry_eqb X K) (kn cb)) (kn ca) in
  let csJ := with_ss ca (mk_ss joinpc regsJ knJ hi) in
  if (Z.eqb (pc ca) joinpc && Z.eqb (pc cb) joinpc
      && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) hv
      && Nat.eqb (length regsJ) 32
      && Nat.leb nx0 v0
      && entails_h v0 hi ca csJ && entails_h v0 hi cb csJ)%bool
  then Some csJ else None.
(* [comment removed for export] *)
Definition node_diamond_joinM (nx : nat) (joinpc : Z) (rs : list nat) (ca cb : acs) : option acs :=
  let hv := nodup Nat.eq_dec (diff_regs 0 (s_regs (a_ss ca)) (s_regs (a_ss cb)) ++ rs) in
  let v0 := Nat.max nx (Nat.max (nxt ca) (nxt cb)) in
  let hi := (v0 + length hv)%nat in
  let regsJ := sr_fresh (s_regs (a_ss ca)) hv v0 in
  let ixb := kn_ix (kn cb) in
  let knJ := List.filter (fun K => kn_memb ixb K) (kn ca) in
  let csJ := with_ss ca (mk_ss joinpc regsJ knJ hi) in
  if (Z.eqb (pc ca) joinpc && Z.eqb (pc cb) joinpc
      && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) hv
      && Nat.eqb (length regsJ) 32
      && Nat.leb nx0 v0
      && entails_hM v0 hi ca csJ && entails_hM v0 hi cb csJ)%bool
  then Some csJ else None.
Lemma node_diamond_joinM_eq : node_diamond_joinM = node_diamond_join.
Proof.
  apply functional_extensionality; intros nx. apply functional_extensionality; intros jp.
  apply functional_extensionality; intros rs. apply functional_extensionality; intros ca. apply functional_extensionality; intros cb.
  unfold node_diamond_joinM, node_diamond_join. rewrite entails_hM_eq.
  rewrite (filter_ext (fun K => kn_memb (kn_ix (kn cb)) K) (fun K => existsb (fun X => kentry_eqb X K) (kn cb))) by (intros K; apply kn_memb_eq).
  reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition via_ok (cs js : acs) (lo : nat) : bool :=
  (match s_log (a_ss js) with [] => true | _ => false end
   && Nat.eqb (length (s_regs (a_ss js))) 32
   && Nat.leb nx0 (nxt cs) && Nat.leb (nxt cs) lo && Nat.leb lo (nxt js))%bool.

(* [comment removed for export] *)
Definition node_abstractcell (cs : acs) (b : expr) (n : Z) : option acs :=
  let '(bb, bo) := split_lit b in
  let K := KUnk (SA bb bo) (ELit n) in
  if kunk_covered (kn cs) K then Some (set_kn cs (K :: kn_cutout (kn cs) bb bo (ELit n))) else None.

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
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition STOPS : list Z :=
  [x_imemset A; x_imemcpy A; x_memset A; x_memcpy A; x_memiszero A; x_envscan A; x_pnscan A] ++ stops_more A.

(* [comment removed for export] *)
Fixpoint mk_itab_ranges_acc (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: rs' => mk_itab_ranges_acc rs' (mk_itab_fuel segs n lo t)
  end.
Definition mk_itab_ranges (rs : list (Z * nat)) : itab := mk_itab_ranges_acc rs PTLeaf.

End WithSegs.

(* [comment removed for export] *)
Notation ACS ss maps totsz ylo eager vis ghost abytes brk fd tidset :=
  (ACSG ss maps totsz ylo eager vis ghost abytes brk fd tidset (@nil gatom)) (only parsing).


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
   KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000; KRange e_atr8 0xFFFF0000001 (if plain A then 0xFFFFFFFFFE9 else 0xFFFFFFFFFE7 (* [comment removed for export] *));
   KRange e_sp0 0x7fff80000000 0x7fffffffff40;
   KRange (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) 0xFFFF0000000 0xFFFFFFFFFE8;
   KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071; KRange (EVar V_L1) 0 131071;
   KRange (EVar V_UID) 0 0xFFFFFFFE; KRange (EVar V_HW) 0x112D 0x20112D;
   KRange (EVar V_W) 0 280000; KRange (EVar V_BRK) (img_hi A / 4096) ((img_hi A + BRK_ASLR) / 4096);
   KWr (SA e_sp0 (-8388608)) (ELit 8388608); KZero (SA e_sp0 (-8388608)) (ELit 8388608);
   KWord (SA e_sp0 0) 8 (EVar V_ARGC); KWord (SA e_sp0 8) 8 e_str0; kw_argv1 e_argv1w]
  (* [comment removed for export] *)
  ++ auxw 0 3 (ELit (ph_addr_z A)) ++ auxw 1 4 (ELit (ph_ent_z A)) ++ auxw 2 5 (ELit (ph_num_z A)) ++ auxw 3 16 (EVar V_HW) ++ auxw 4 6 (ELit 4096)
  ++ auxw 5 11 (EVar V_UID) ++ auxw 6 12 (EVar V_UID) ++ auxw 7 23 (ELit 0) ++ auxw 8 25 e_atrandom ++ auxw 9 0 (ELit 0)
  ++ [atr;
      (* [comment removed for export] *)
      KWr (SA (fst e_atrb) (snd e_atrb)) (ELit 16);
      KImg (img_lo A) (img_hi A); KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))].

(* [comment removed for export] *)
Definition atr_entry : kentry := KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND.
Definition atr_entry_zero : kentry := KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16).
(* [comment removed for export] *)
Definition init_kn (A : atable) : list kentry := init_kn_with atr_entry A.
(* [comment removed for export] *)
Definition init_kn_zero (A : atable) : list kentry := init_kn_with atr_entry_zero A.

Definition init_regs : list expr := sr_upd (repeat (ELit 0) 32) 2 e_sp0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_stklen : expr := mkAlu ALU_SUB (ELit (2^47 + STK_BELOW)) e_sp0.
Definition init_vis (A : atable) : list (expr * expr) :=
  if plain A then [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (ELit CEIL, ELit (2^47 - CEIL))]
  else [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (eaddz e_sp0 (- STK_BELOW), e_stklen)].

Definition init_acs_of_with (kn0 : list kentry) (A : atable) : acs :=
  ACS (mk_ss (a_entry A) init_regs kn0 NX0) [] (img_hi A - img_lo A) MBASE_MIN 0 (init_vis A) []
      (vis_cost (img_hi A - img_lo A) + vis_cost (2^47 - CEIL)) (escale 4096 (EVar V_BRK)) FdStd false.
Definition init_acs_of (A : atable) : acs := init_acs_of_with (init_kn A) A.        (* [comment removed for export] *)
Definition init_acs_of_zero (A : atable) : acs := init_acs_of_with (init_kn_zero A) A.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End APC.
