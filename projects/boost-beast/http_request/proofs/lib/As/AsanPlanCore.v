(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AxSymExec3B.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Module APC.
Import AX2. Import AX2B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CEIL : Z := 0x7fff7f800000.
(* [comment removed for export] *)
Definition CEILMAX : Z := 0x7fffff800000.
Lemma CEIL_le_CEILMAX : CEIL <= CEILMAX. Proof. unfold CEIL, CEILMAX. apply Z.leb_le. reflexivity. Qed.
(* [comment removed for export] *)
Definition KHI : Z := 0x10007fff8000.
(* [comment removed for export] *)
Definition FLOOR : Z := 0x2aaaaaaab000.
(* [comment removed for export] *)
Definition MBASE_MIN : Z := 0x154555557000.
(* [comment removed for export] *)
Definition PID_MAX : Z := 4194304.

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
  x_smear : Z;
  (* [comment removed for export] *)
  x_sniff : Z; sniff_tab : Z; sniff_cell : Z;
  (* [comment removed for export] *)
  x_envscan : Z; x_envscan_k : Z; x_pnscan : Z; x_pnscan_k : Z;
  stops_more : list Z              (* [comment removed for export] *)
}.

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
Fixpoint shape_eqb_h (x y : shape) : bool :=
  match x, y with
  | SNil, SNil => true
  | SExit c, SExit c' => Z.eqb c c'
  | SEmitP fd ps s, SEmitP fd' ps' s' => Z.eqb fd fd' && spieces_eqb ps ps' && shape_eqb_h s s'
  | SAlt2 a b, SAlt2 a' b' => shape_eqb_h a a' && shape_eqb_h b b'
  | SCase e m a b, SCase e' m' a' b' => expr_eqb e e' && Z.eqb m m' && shape_eqb_h a a' && shape_eqb_h b b'
  | SHole _, SHole _ => true
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
Inductive vmop : Type :=
| VNew (k : mkind) (a n : expr)                    (* [comment removed for export] *)
| VFixIn (arm_noreserve prot_none : bool) (a n : expr)  (* [comment removed for export] *)
| VUnmap (a n : expr)                              (* [comment removed for export] *)
| VProt (a n : expr).                              (* [comment removed for export] *)
Definition vmop_map (f : expr -> expr) (o : vmop) : vmop :=
  match o with
  | VNew k a n => VNew k (f a) (f n) | VFixIn x y a n => VFixIn x y (f a) (f n)
  | VUnmap a n => VUnmap (f a) (f n) | VProt a n => VProt (f a) (f n)
  end.

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
  a_tidset : bool;              (* [comment removed for export] *)
  a_vmops : list vmop           (* [comment removed for export] *)
}.

Definition reg (cs : acs) (n : nat) : expr := nth n (s_regs (a_ss cs)) (ELit 0).
Definition kn (cs : acs) : list kentry := s_know (a_ss cs).
Definition pc (cs : acs) : Z := s_pc (a_ss cs).
Definition nxt (cs : acs) : nat := s_next (a_ss cs).

Definition with_ss (cs : acs) (ss : sym_state) : acs :=
  ACS ss (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs).
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
Definition vmop_an (op : vmop) : expr * expr :=
  match op with
  | VNew _ a n | VFixIn _ _ a n | VUnmap a n | VProt a n => (a, n)
  end.
Definition vmop_all (P : expr -> bool) (op : vmop) : bool := P (fst (vmop_an op)) && P (snd (vmop_an op)).
Definition vmop_vars_lt (b : nat) (op : vmop) : bool := vmop_all (expr_vars_lt b) op.
(* [comment removed for export] *)
Definition fresh_ok (cs : acs) : bool :=
  let v := nxt cs in
  sr_vars_lt v (s_regs (a_ss cs)) && kn_vars_lt v (kn cs)
  && maps_vars_lt v (a_maps cs) && pairs_vars_lt v (a_vis cs) && pairs_vars_lt v (a_ghost cs)
  && expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && forallb (vmop_vars_lt v) (a_vmops cs) && Nat.leb nx0 v.

(* [comment removed for export] *)
Definition run_block_ref (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let ss' := sym_execTX segs IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carry (s_log ss') (s_know ss') [] with
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
    let ss' := sym_execTXBI segs bc kx IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carryK bc (s_log ss') (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
Lemma run_block_eq : forall K fuel stops cs, run_block K fuel stops cs = run_block_ref K fuel stops cs.
Proof.
  intros. unfold run_block, run_block_ref. destruct (fresh_ok cs); [|reflexivity]. cbv zeta.
  rewrite (sym_execTXBI_eq segs (s_know (a_ss cs))) by reflexivity.
  rewrite <- (sym_execTX_know segs IT K fuel true stops (SS (s_pc (a_ss cs)) (s_regs (a_ss cs)) [] (s_know (a_ss cs)) (s_next (a_ss cs)))) at 1.
  rewrite carryK_eq. reflexivity.
Qed.

Definition run_block_gc (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block K fuel stops cs with Some cs' => Some (cs_gc cs') | None => None end.

Local Open Scope lzb_scope.
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
Local Close Scope lzb_scope.

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

Local Open Scope lzb_scope.
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
Local Close Scope lzb_scope.

Lemma kentry_apart_bB_eqf : forall fk, kentry_apart_bB (mkbc fk) = kentry_apart_b fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_b); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart_x); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.Arith.PeanoNat.Nat.leb); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_xB_eqf)|] [|@K; @un; @uk; @n2; @k2; @b2; @n1; @k1; @b1; @a; @b; @k; @w; @v; @l; @k0; @lo; @hi; @e; @m; @n; @a1; @a2; @c; @x2; @x1; @x0; @x; @fk|] "#$##.#J#$###6#%#&#*#4#+#C#I#'#)#2#,#(#5#7#9#;#D#E#-#<#1#@#>#B#G#F#H#J#K#L#:#?#=#8#3#A)#E$#F%#5*#G$#H(#I$US*Ok#$OEk#%I#k#&R#&DUS##US$D&CVS##DVS$CD&FWS##CDWS$FCD&GXS##FCDXS$GFCDk#'IEk#(R#k#)I#k#*I#k#+R#k#,I#US%M#S+##############VS,G#US-G(#ZQPJHCD#$&#nK#$#-EF#$%#.#/#ZMJHNCDFnK#$#-EC#$%#.#/#ZQPJHCDGnK#$#-EF#$%#.#/#VS&S'CVS&CD$$#VS.DCVS/#S0$%#(S'(&ZFNQM$C#$&#nO#$#$EC#-&#-#0#11%#-#2/&#-#2#3-%#4#5#%#6#7L&#6#4#5L%#-#8/'#9#*#:#'L&#-#2#;-%#-#2/%S(PJHCD5$8#nK#$#-EF#$%#.#/#%PJHNCDFnK#$#-EC#$%#.#/#%S(PJHCDGnK#$#-EF#$%#.#/#%HNQM.C-$0#nO#$#$EC#-&#-#0#1)%#-#2'&#-#2#3%%#4#5#%#6#7L&#6#4#5L%#-#8''#9#*#:#'L&#-#2#;%%#-#2'WS)E-#j#.s#,#%PJHNCDA$s#$#nK#$#-EF#$%#.#/#%JHNQCDFnK#$#-EC#$%#.#/#%PJHNCDGnK#$#-EF#$%#.#/#%NQMG:C9$<#nO#$#$ED#-&#-#0#1)%#-#2'&#-#2#3%%#4#5#%#6#7L&#6#4#5L%#-#8''#9#*#:#'L&#-#2#;%%#-#2'VS1E#&MUS2#US3MZS4s#;s#:1&$#YS#&GFCDYS$MGFCDWS)E$#m#&#j#<O#'OEs#Hs#G#j#=I#'Is#Ws#Ms#L#j#>R#'Rs#Xs#Rs#Q#j#?I#'Is#Ys#Ws#V#j#@s#]##"). Qed.
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

Local Open Scope lzb_scope.
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
Local Close Scope lzb_scope.

Lemma kentry_apart_bpB_eqf : forall fk, kentry_apart_bpB (mkbc fk) = kentry_apart_bp fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bpB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bp); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart_p); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.Arith.PeanoNat.Nat.leb); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_pB_eqf)|] [|@K; @un; @uk; @ub; @n2; @k2; @b2; @n1; @k1; @b1; @sp; @a; @b; @k; @w; @v; @l; @k0; @lo; @hi; @e; @m; @n; @a1; @a2; @c; @x3; @x2; @x1; @x0; @x; @fk|] "#$*#/#L#$###8#%#&#*#6#(#+#,#E#K#'#)#3#-#9#;#7#5#=#F#G#.#>#2#B#@#D#I#H#J#L#M#N#<#A#?#:#4#C)#G$#H%#7+#I$#J(#K$US,Qk#$QEk#%I#k#&S%#k#'I#&DUS##US$D&CVS##DVS$CD&FWS##CDWS$FCD&GXS##FCDXS$GFCD&OYS##GFCDYS$OGFCDk#(IEk#)S%#k#*I#k#+I#k#,S%#k#-I#k#.S&#US'J#S-##############VS.G#US/G(#[JRLKHCD#$&#nM#$#/EF#$%#0#1#[OLKHPCDFnM#$#/EC#$%#0#1#[JRLKHCDGnM#$#/EF#$%#0#1#VS(S)CVS(CD$$#VS0DCVS1#S2$%#(S)(&[FHPJO$C#$&#nQ#$#$EC#-&#/#2#31%#/#4/&#/#4#5-%#6#7#%#8#9N&#8#6#7N%#/#:/'#;#+#<#(N&#/#4#=-%#/#4/%S*RLKHCD5$8#nM#$#/EF#$%#0#1#%RLKHPCDFnM#$#/EC#$%#0#1#%S*RLKHCDGnM#$#/EF#$%#0#1#%KHPJO.C-$0#nQ#$#$EC#-&#/#2#3)%#/#4'&#/#4#5%%#6#7#%#8#9N&#8#6#7N%#/#:''#;#+#<#(N&#/#4#=%%#/#4'WS+E-#j#0s#,#%RLKHPCDA$s#$#nM#$#/EF#$%#0#1#%LKHPJCDFnM#$#/EC#$%#0#1#%RLKHPCDGnM#$#/EF#$%#0#1#%HPJOG:C9$<#nQ#$#$ED#-&#/#2#3)%#/#4'&#/#4#5%%#6#7#%#8#9N&#8#6#7N%#/#:''#;#+#<#(N&#/#4#=%%#/#4'VS3E#&JUS4#US5JZS6s#;s#:1&$#ZS#&OGFCDZS$JOGFCDWS+E$#m#&#j#>Q#'QEs#Is#H#j#?I#'Is#\s#Ns#M#j#@S%#'S%s#]s#Ss#R#j#AI#'Is#^s#Xs#W#j#BS&#'S&s#_s#]s#\#j#Cs#d##"). Qed.
#[local] Hint Rewrite kentry_apart_bpB_eqf : bceq.



Definition kimg_b (K : kentry) : bool := match K with KImg _ _ => true | _ => false end.

(* [comment removed for export] *)
Definition kn_unfill (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bp k sp ub uk un K) k.

Local Open Scope lzb_scope.
Definition kn_unfillB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bpB bc sp ub uk un K) (bc_fk bc).
Local Close Scope lzb_scope.

Lemma kn_unfillB_eqf : forall fk, kn_unfillB (mkbc fk) = kn_unfill fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kn_unfillB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kn_unfill); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bp); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.Lists.List.filter); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kimg_b); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mk_sprep); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk_mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bpB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bpB_eqf)|] [|@un; @uk; @K; @ub; @sp; @b; @n1; @k1; @b1; @s; @l; @x1; @x0; @x; @fk|] "##p#)#B#&###-#%#$#'#/#6#0#1#3#(#;#?#5#7#<#=#>#,#:#@#A#B#C#D#2#9#8#4#.)#=$#>&#?&#2)#@)#A(US&Ek#$I#k#%K##DUL#UMD#GVL#DVMGD#FWL#GDWMFGDk#&EJk#$I#k#%K#k#'I#k#(Q#URCUS'D#NXS##HCFYG#HCFDnJ#$##J&#%#O##j#&E##HUS$#$E%#XPNHCF&N#HCFDVS%-#j#&E#$E#H%B(#j#)3#k#*IQk#+K#k#,I#UPCWGHCF&N#HCFDnJ#$##J8#%#O##j#&E#$E#3%s#-#.j#-*#nJ#$##J=#%#O#3j#&E#$E#D%s#2#3j#.s#3#XPHCFG&H#CFGDVS%s#$#j#&E#$E#CVS(s#9##CUS$#US)C's#=C,&$#US#&US*C'<;4%$#US+)US,C's#3s#2B%$#XL,FGDXMCFGD%s#F$#m#&#j#/I#(Is#Is#?s#>#j#0K#(Ks#Js#Ds#C#j#1I#(Is#Ks#Is#H#j#2s#N##"). Qed.
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

Local Open Scope lzb_scope.
Definition havoc1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bB bc ub uk un K)%lzb then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | _ => []
       end.
Local Close Scope lzb_scope.

Lemma havoc1B_eqf : forall fk, havoc1B (mkbc fk) = havoc1 fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.havoc1B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.havoc1); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_b); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwr_b); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kzero_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kfill_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kunk_cutB); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kzero_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kfill_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kunk_cut); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kzero_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kfill_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kunk_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bB_eqf)|] [|@K; @un; @uk; @ub; @a; @kb; @kk; @w; @v; @len; @n; @k; @lo; @hi; @e; @m; @a1; @n1; @a2; @n2; @c; @k0; @b; @wn; @wk; @wb; @l; @x2; @x1; @x0; @x; @fk|] "#$:#.#L#$###%#2#'#4#&#:#+#*#B#5#)#,#6#8#(#;#F#G#H#=#>#?#A#-#C#D#E#1#@#I#J#K#L#M#N#7#<#9#3'#H$#I&#J)#K(US0Fk#$F#k#%H#k#&N##DUQ#URD#CVQ#DVRCD#EWQ#CDWRECD#IXQ#ECDXRIECDk#$FJk#%H#k#&N#k#'H#US$GUS(CXDGIECnJ#$##J$#%#S)##US1FWS*FC##P[S+#KLOCDEnM#$#(>C#$%#)#*##S,\S-#EPKLCDInM#$#(AE#$%#)#*#[S.(KLOCDEnM#$#(s##C#$%#)#*#nF#$#$s#$C#-&#(#+#,,%#(#-(&#(#.#/,%#0#1,%#2#3,&#2#0#1,%#(#.,'#4#5#6#7,&#(#-#8%%#(#-#nJ#$##s#%.#%#,##YS$S#GIECVS/2#[S%PKLOCDEnM#$#(s#)C#$%#)#*#\S&ES,PKLCDInM#$#(s#+E#$%#)#*#[S'PKLOCDEnM#$#(s#-C#$%#)#*#nF#$#$s#.C#-&#(#+#,6%#(#-'&#(#.#96%#0#16%#2#36&#2#0#16%#(#.6'#4#5#6#76&#(#-#8%%#(#-#nJ#$##s#/*#%#6##$s#0-#j#:>#k#-Hs#2k#*N#k#)H#k#;H#k#<N#k#=H#US'GnJ#$##Js#$#%#S)#5ZGKLOCDEnM#$#(s#;C#$%#)#*#nF#$#$s#<C#-&#(#+#,s#$%#(#-@&#(#.#/s#$%#0#1s#$%#2#3s#$&#2#0#1s#$%#(#.s#$'#4#5#6#7s#$&#(#-#8=%#(#-#nJ#$##s#=&#%#s#$##$s#>#1j#>*#k#8N+VS&DS#j#8N#[S#EPKLCDInM#$#(s#DE#$%#)#*#nF#$#$s#EC#-&#(#+#,s#-%#(#-s#)&#(#.#/s#-%#0#1s#-%#2#3s#-&#2#0#1s#-%#(#.s#-'#4#5#6#7s#-&#(#-#8#%#(#-:nJ#$##s#F/#%#s#-##$s#G#:j#>*#US%GnF#$#$s#JC#-&#(#+#,s#2%#(#-1&#(#.#/s#2%#0#1s#2%#2#3s#2&#2#0#1s#2%#(#.s#2'#4#5#6#7s#2&#(#-#8A%#(#-?nJ#$##s#K4#%#s#2##$s#L#?j#>8#US(DYS$GIECDVS/$#WS*FDs#9[S%KLOS#CDEnM#$#(s#SC#$%#)#*#\S&EPKLOCDInM#$#(s#UE#$%#)#*#[S'KLOS#CDEnM#$#(s#WC#$%#)#*#nF#$#$s#XD#-&#(#+#,s#@%#(#-'&#(#.#9s#@%#0#1s#@%#2#3s#@&#2#0#1s#@%#(#.s#@'#4#5#6#7s#@&#(#-#8%%#(#-#nJ#$##s#Y+#%#*##VS2s#Z##GUS+#US3G%s#)73&$#US-&US4G%s##A;%$#US.)US5G%s#/s#.s#'%$#US6,US7G%s#Ts#Ss#8%$#YQ/IECDYRGIECD$s#j$#m#&#j#?F#&Fs#ms#_s#^#j#@H#&Hs#ns#ds#c#j#AN#&Ns#os#is#h#j#BH#&Hs#ps#ns#m#j#Cs#t##"). Qed.
#[local] Hint Rewrite havoc1B_eqf : bceq.


Definition havoc1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bp k sp ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | _ => []
       end.

Local Open Scope lzb_scope.
Definition havoc1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bpB bc sp ub uk un K)%lzb then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | _ => []
       end.
Local Close Scope lzb_scope.

Lemma havoc1pB_eqf : forall fk, havoc1pB (mkbc fk) = havoc1p fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.havoc1pB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.havoc1p); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bp); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwr_b); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kzero_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kfill_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kunk_cutB); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kzero_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kfill_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kunk_cut); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kzero_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kfill_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kunk_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bpB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bpB_eqf)|] [|@K; @un; @uk; @ub; @sp; @a; @kb; @kk; @w; @v; @len; @n; @k; @lo; @hi; @e; @m; @a1; @n1; @a2; @n2; @c; @k0; @b; @wn; @wk; @wb; @l; @x3; @x2; @x1; @x0; @x; @fk|] "#$A#/#N#$###%#(#3#&#6#<#*#D#)#+#7#'#8#:#,#-#5#=#H#I#J#?#@#A#C#.#E#F#G#2#B#K#L#M#N#O#P#9#>#4#;'#J$#K&#L(#M)US2Gk#$G#k#%I#k#&O#k#'I##DUQ#URD#CVQ#DVRCD#EWQ#CDWRECD#HXQ#ECDXRHECD#PYQ#HECDYRPHECDk#$GJk#%I#k#&O#k#'I#k#(S%#US&FUS*CYDFPHECnJ#$##J$#%#S+##US3GWS,GC##S$[S-#NKMCDEnL#$#)s##C#$%#*#+##S.\S/#ES#NKCDHnL#$#)s#&E#$%#*#+#[S0(NKMCDEnL#$#)s#(C#$%#*#+#nG#$#$s#)C#-&#)#,#-,%#)#.(&#)#/#0,%#1#2,%#3#4,&#3#1#2,%#)#/,'#5#6#7#8,&#)#.#9%%#)#.#nJ#$##s#*.#%#,##ZS&MFPHECVS12#[S'S$NKMCDEnL#$#)s#.C#$%#*#+#\S(ES.S#NKCDHnL#$#)s#0E#$%#*#+#[S)S$NKMCDEnL#$#)s#2C#$%#*#+#nG#$#$s#3C#-&#)#,#-6%#)#.'&#)#/#:6%#1#26%#3#46&#3#1#26%#)#/6'#5#6#7#86&#)#.#9%%#)#.#nJ#$##s#4*#%#6##$s#5-#j#;>#k#.Is#7k#+O#k#*I#k#<I#k#=O#k#>I#US)FnJ#$##Js#$#%#S+#5ZPNKMCDEnL#$#)s#@C#$%#*#+#nG#$#$s#AC#-&#)#,#-s#$%#)#.@&#)#/#0s#$%#1#2s#$%#3#4s#$&#3#1#2s#$%#)#/s#$'#5#6#7#8s#$&#)#.#9=%#)#.#nJ#$##s#B&#%#s#$##$s#C#1j#?*#k#9O+VS(DMj#9O#[FES#NKCDHnL#$#)s#IE#$%#*#+#nG#$#$s#JC#-&#)#,#-s#-%#)#.s#)&#)#/#0s#-%#1#2s#-%#3#4s#-&#3#1#2s#-%#)#/s#-'#5#6#7#8s#-&#)#.#9#%#)#.:nJ#$##s#K/#%#s#-##$s#L#:j#?*#US'FnG#$#$s#OC#-&#)#,#-s#2%#)#.1&#)#/#0s#2%#1#2s#2%#3#4s#2&#3#1#2s#2%#)#/s#2'#5#6#7#8s#2&#)#.#9A%#)#.?nJ#$##s#P4#%#s#2##$s#Q#?j#?8#US*DZS&FPHECDVS1$#WS,GDs#9[S'S#KMFCDEnL#$#)s#XC#$%#*#+#\S(ES$NKMCDHnL#$#)s#ZE#$%#*#+#[S)S#KMFCDEnL#$#)s#\C#$%#*#+#nG#$#$s#]D#-&#)#,#-s#@%#)#.'&#)#/#:s#@%#1#2s#@%#3#4s#@&#3#1#2s#@%#)#/s#@'#5#6#7#8s#@&#)#.#9%%#)#.#nJ#$##s#^+#%#*##VS4s#_##FUS-#US5F&s#)73&$#US/&US6F&s##A;%$#US0)US7F&s#/s#.s#'%$#US8,US9F&s#Ts#Ss#8%$#ZQ/PHECDZRFPHECD$s#o$#m#&#j#@G#%Gs#rs#`s#_#j#AI#%Is#ss#es#d#j#BO#%Os#ts#js#i#j#CI#%Is#us#os#n#j#DS%#%S%s#vs#ts#s#j#Es#{##"). Qed.
#[local] Hint Rewrite havoc1pB_eqf : bceq.


Definition kn_havoc (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (havoc1p k sp ub uk un) k.

Definition kn_havocB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (havoc1pB bc sp ub uk un) (bc_fk bc).

Lemma kn_havocB_eqf : forall fk, kn_havocB (mkbc fk) = kn_havoc fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kn_havocB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kn_havoc); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.havoc1p); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.Lists.List.flat_map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mk_sprep); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk_mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.havoc1pB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.havoc1pB_eqf)|] [|@un; @uk; @K; @ub; @sp; @l; @n1; @k1; @b1; @s; @x1; @x0; @x; @fk|] "##d#(#=#&#$###,#%#.#/#'#0#2#:#4#5#8#9#+#;#<#=#>#?#1#7#6#3#-)#8$#9'#:&#/(#;)#<(URFk#$H#k#%I##EUK#ULE#DVK#EVLDE#GWK#DEWLGDEk#&F.k#$H#k#%I#k#'H#k#(N#UOC#JXP#CGDXE#CGDUQ%$FF$#XMJCGD&J#CGD$FF#J%<&#j#)-#k#*HNk#+I#k#,H#UMCWECGD&J#CGD$FF#/%s#%#,j#-(#$FF/E%s#(#/j#)s#)#XMCGDE&C#GDE$FF#CVS#s#-##CUQ#US$C's#1C*&$#UP&US%C'650%$#US&)US'C's#'s#&<%$#XK,GDEXLCGDE%s#:$#m#&#j#.H#(Hs#=s#3s#2#j#/I#(Is#>s#8s#7#j#0H#(Hs#?s#=s#<#j#1s#B##"). Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.

(* [comment removed for export] *)
Definition havoc_verdict (sp : sprep) (uk : Z) (m1 : Z) (g : gval) : bool :=
  match g with
  | (b, kb, obr, (glo, ghi)) =>
      if (match sp_rng sp, obr with
          | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + uk + m1) (lo2 + glo) || Z.leb (hi2 + ghi) (lo1 + uk))%bool
          | _, _ => false
          end) then true
      else existsb (hull_in_side kb obr glo ghi) (sp_D sp)
  end.
(* [comment removed for export] *)
Definition havoc_fast_kind (K : kentry) : bool :=
  match K with
  | KWord _ w _ => Nat.leb w 8
  | KZero _ (ELit _) | KBlob _ (ELit _) _ | KFill _ (ELit _) _ | KUnk _ (ELit _) => true
  | KImg lo hi => (Z.leb 0 lo && Z.leb lo hi)%bool
  | _ => false
  end.
Fixpoint havocG_go (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (vt : ptree (gval * bool))
         (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           match pt_get vt (ei_gid ei) with
           | Some (g, true) => if (inb g ei && havoc_fast_kind K)%bool then [K] else havoc1pB bc sp ub uk un K
           | _ => havoc1pB bc sp ub uk un K
           end
       | None => havoc1pB bc sp ub uk un K
       end) ++ havocG_go bc sp ub uk un vt rest irest
  | _, _ => []
  end.
Definition kn_havocG (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  match un with
  | ELit z1 =>
      let sp := mk_sprepB bc ub uk un in
      let '(r, gs) := scan_entries bc (bc_fk bc) nt_empty gst_empty in
      let '(infos, _) := r in
      havocG_go bc sp ub uk un (pt_map (fun g => (g, havoc_verdict sp uk (zlit64 z1) g)) (gs_bnds gs)) (bc_fk bc) infos
  | _ => kn_havocB bc ub uk un
  end.

Lemma ranges_apart_pB_hull : forall bc sp ub uk z1 g ei kb kk m z2,
  havoc_verdict sp uk (zlit64 z1) g = true -> inb g ei = true -> ei_m ei = Some m ->
  ei_kb ei = kb -> ei_k ei = kk -> ei_br ei = base_rangeB bc kb -> m = zlit64 z2 ->
  ranges_apart_pB bc sp ub uk (ELit z1) kb kk (ELit z2) = true.
Proof.
  intros bc sp ub uk z1 [[[b kbg] obr] [glo ghi]] ei kb kk m z2 Hv Hi Hm Ekb Ekk Ebr Em.
  unfold inb in Hi. rewrite Hm in Hi.
  apply andb_prop in Hi as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [Hi H2]. apply andb_prop in Hi as [_ H1k].
  apply Z.leb_le in H3. apply Z.leb_le in H4. apply p_expr_eqb_eq in H1k. apply obr_eqb_eq in H2. rewrite Ekb in H1k. rewrite Ekk in H3, H4. subst kbg obr.
  unfold havoc_verdict in Hv. unfold ranges_apart_pB. rewrite <- Em. rewrite <- Ebr.
  match type of Hv with (if ?c then true else _) = true => destruct c eqn:Hnum end.
  - destruct (sp_rng sp) as [[lo1 hi1]|]; [|discriminate]. destruct (ei_br ei) as [[lo2 hi2]|]; [|discriminate].
    change (if (hi1 + uk + zlit64 z1 <=? lo2 + kk) then true else (hi2 + kk + m <=? lo1 + uk)) with ((hi1 + uk + zlit64 z1 <=? lo2 + kk) || (hi2 + kk + m <=? lo1 + uk))%bool in *; replace ((hi1 + uk + zlit64 z1 <=? lo2 + kk) || (hi2 + kk + m <=? lo1 + uk))%bool with true; [reflexivity|].
    symmetry. apply Bool.orb_true_iff. apply Bool.orb_prop in Hnum. destruct Hnum as [H|H]; apply Z.leb_le in H; [left|right]; apply Z.leb_le; lia.
  - assert (HS : in_sidesB bc (sp_D sp) kb kk m = true).
    { eapply in_sidesB_of_hull; [exact Hv | symmetry; exact Ebr | exact H3 | exact H4 | rewrite Em; apply zlit64_bounds]. }
    rewrite HS. match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
Qed.

Lemma havoc_fast_keep : forall fk sp ub uk z1 g ei t K,
  havoc_verdict sp uk (zlit64 z1) g = true -> inb g ei = true -> havoc_fast_kind K = true ->
  EINF (mkbc fk) t K (Some ei) ->
  havoc1pB (mkbc fk) sp ub uk (ELit z1) K = [K].
Proof.
  intros fk sp ub uk z1 g ei t K Hv Hi Hk (HD & _ & Hbr).
  assert (Hm : exists m, ei_m ei = Some m) by (unfold inb in Hi; destruct (ei_m ei) as [m|]; [exists m; reflexivity | discriminate]).
  destruct Hm as [m Hm]. rewrite Hm in HD.
  unfold havoc1pB. change (if kwr_b K then true else kentry_apart_bpB (mkbc fk) sp ub uk (ELit z1) K) with (kwr_b K || kentry_apart_bpB (mkbc fk) sp ub uk (ELit z1) K)%bool in *; replace (kwr_b K || kentry_apart_bpB (mkbc fk) sp ub uk (ELit z1) K)%bool with true; [reflexivity|]. symmetry.
  apply Bool.orb_true_iff. right.
  destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [havoc_fast_kind] in Hk; try discriminate; cbn [kdescr] in HD; cbn [kentry_apart_bpB].
  - injection HD as E1 E2 E3. rewrite Hk. cbn [andb].
    eapply ranges_apart_pB_hull; [exact Hv | exact Hi | exact Hm | symmetry; exact E1 | symmetry; exact E2 | rewrite E1; exact Hbr | symmetry; exact E3].
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as E1 E2 E3.
    eapply ranges_apart_pB_hull; [exact Hv | exact Hi | exact Hm | symmetry; exact E1 | symmetry; exact E2 | rewrite E1; exact Hbr | symmetry; exact E3].
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as E1 E2 E3.
    eapply ranges_apart_pB_hull; [exact Hv | exact Hi | exact Hm | symmetry; exact E1 | symmetry; exact E2 | rewrite E1; exact Hbr | symmetry; exact E3].
  - destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt; [|discriminate]. injection HD as E1 E2 E3.
    rewrite Hk. change two64 with (2 ^ 64)%Z. rewrite Hlt. cbn [andb].
    eapply ranges_apart_pB_hull; [exact Hv | exact Hi | exact Hm | symmetry; exact E1 | symmetry; exact E2 | rewrite E1; exact Hbr | symmetry; exact E3].
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as E1 E2 E3.
    eapply ranges_apart_pB_hull; [exact Hv | exact Hi | exact Hm | symmetry; exact E1 | symmetry; exact E2 | rewrite E1; exact Hbr | symmetry; exact E3].
  - destruct len as [z| | | | | | |]; try discriminate. injection HD as E1 E2 E3.
    eapply ranges_apart_pB_hull; [exact Hv | exact Hi | exact Hm | symmetry; exact E1 | symmetry; exact E2 | rewrite E1; exact Hbr | symmetry; exact E3].
Qed.

Lemma havocG_go_eq : forall fk sp ub uk z1 bnds t kn infos,
  Forall2 (EINF (mkbc fk) t) kn infos ->
  havocG_go (mkbc fk) sp ub uk (ELit z1) (pt_map (fun g => (g, havoc_verdict sp uk (zlit64 z1) g)) bnds) kn infos
  = flat_map (havoc1pB (mkbc fk) sp ub uk (ELit z1)) kn.
Proof.
  intros fk sp ub uk z1 bnds t kn infos HF. induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
  cbn [havocG_go flat_map]. rewrite IH. f_equal.
  destruct oi as [ei|]; [|reflexivity].
  rewrite pt_get_map. destruct (pt_get bnds (ei_gid ei)) as [g|]; [|reflexivity].
  destruct (havoc_verdict sp uk (zlit64 z1) g) eqn:Hv; [|reflexivity].
  change (if inb g ei then havoc_fast_kind K else false) with (inb g ei && havoc_fast_kind K)%bool in *; destruct (inb g ei && havoc_fast_kind K)%bool eqn:Hc; [|reflexivity].
  apply andb_prop in Hc as [Hi Hk]. symmetry. exact (havoc_fast_keep fk sp ub uk z1 g ei t K Hv Hi Hk HK).
Qed.

Lemma kn_havocG_eq : forall fk ub uk un, kn_havocG (mkbc fk) ub uk un = kn_havocB (mkbc fk) ub uk un.
Proof.
  intros fk ub uk un. unfold kn_havocG. destruct un as [z1| | | | | | |]; try reflexivity.
  destruct (scan_entries (mkbc fk) (bc_fk (mkbc fk)) nt_empty gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ (NTI_empty _) ES) as (_ & _ & HF).
  unfold kn_havocB. exact (havocG_go_eq fk _ ub uk z1 (gs_bnds gs) t1 _ infos HF).
Qed.

Definition kn_havocM (k : list kentry) := kn_havocG (mkbc k).
Lemma kn_havocM_eq : kn_havocM = kn_havoc.
Proof. apply functional_extensionality; intros k. unfold kn_havocM. bcfe. rewrite kn_havocG_eq. rewrite kn_havocB_eqf. reflexivity. Qed.



(* [comment removed for export] *)
Definition kwr_cut (k : list kentry) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcut KWr k ub uk un kb kk len.

Definition kwr_cutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcutB bc KWr ub uk un kb kk len.

Lemma kwr_cutB_eqf : forall fk, kwr_cutB (mkbc fk) = kwr_cut fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwr_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwr_cut); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kcut); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KWr); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kcutB_eqf)|] [|@len; @kk; @kb; @un; @uk; @wn; @wk; @wb; @mk; @l; @x4; @x3; @x2; @x1; @x0; @x; @fk|] "##^#+#;###$#1#%#&#'#2#3#5#(#)#8#:#/#*#9#.#7#;#<#=#6#4#0%#9$#:(US#Pk#$E#k#%I#k#&E#k#'E#k#(I##CUJ#UKC#DVJ#CVKDC#FWJ#DCWKFDC#GXJ#FDCXKGFDC#HYJ#GFDCYKHGFDC#LZJ#HGFDCZKLHGFDCk##EPk##S$#k#)E9k#*I#k#+E#k#,&#VNCQj#,(#[COMLHGFD\NOQMLHGFDWRs#$$#j#-(#\NOMLHGFDCVS%s#'##MUS&#US'MZS(.,(&$#[J&LHGFDC[KMLHGFDCWRs#.$#m#&#j#.E#$Es#1;:#j#/I#$Is#2@?#j#0E#$Es#3s#%s#$#j#1E#$Es#4s#*s#)#j#2I#$Is#5s#/s#.#j#3E#$Es#6s#4s#3#j#4s#<##"). Qed.
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
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.cutout1B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.cutout1); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwr_cut); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bB); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kzero_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kfill_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kunk_cutB); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_b); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kzero_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kfill_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kunk_cut); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kzero_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kfill_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kunk_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwr_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwr_cutB_eqf)|] [|@K; @un; @uk; @len; @kk; @kb; @ub; @a; @w; @v; @n; @k; @lo; @hi; @e; @m; @a1; @n1; @a2; @n2; @c; @k0; @l; @b; @wn; @wk; @wb; @x2; @x1; @x0; @x; @fk|] "#$E#.#L#$###%#'#2#4#+#*#@#&#)#5#,#C#(#6#8#:#D#E#F#G#<#=#?#-#A#B#1#>#H#I#J#K#L#M#N#7#;#9#3'#H$#I&#J)#K(US/Gk#$G#k#%H#k#&N##DUR#US#D#CVR#DVS#CD#EWR#CDWS#ECD#LXR#ECDXS#LECDk#'H2k#(N#k#)H#k#%H#k#&N#k#*H#US$F#QYS)#FLECUS0GWS*GC##O[S+#IJMCDEnK#$#+?C#$%#)#(#ZFIJMCDEnK#$#+AC#$%#)#(##S,\S-#EOIJCDLnK#$#+s#$E#$%#)#(#[S.*IJMCDEnK#$#+s#&C#$%#)#(#nG#$#$s#'C#-&#+#,#-.%#+#'*&#+#.#/.%#0#1.%#2#3.&#2#0#1.%#+#'('#4#5#6#7.&#+#'#8%%#+#'#nP#$##s#(0#%#.##YS%QFLEC[S&OIJMCDEnK#$#+s#+C#$%#)#(#[S$OIJMCDEnK#$#+s#-C#$%#)#(#\S'ES,OIJCDLnK#$#+s#/E#$%#)#(#[S(OIJMCDEnK#$#+s#1C#$%#)#(#nG#$#$s#2C#-&#+#,#-9%#+#')&#+#.#99%#0#19%#2#39&#2#0#19%#+#'''#4#5#6#79&#+#'#8%%#+#'#nP#$##s#3,#%#9##$s#4.#j#:@#k#$GPk#%H#k#&N#k#*H#US%FXDFLECnG#$#$s#<C#-&#+#,#-s##%#+#'?&#+#.#/s##%#0#1s##%#2#3s##&#2#0#1s##%#+#'1'#4#5#6#7s##&#+#'#8:%#+#'8nP#$##s#=$#%#s####$s#>#-j#;(#k#<Hs#.k#=N#k#>H#US(FnG#$#$s#DC#-&#+#,#-s#+%#+#'s#'&#+#.#/s#+%#0#1s#+%#2#3s#+&#2#0#1s#+%#+#'9'#4#5#6#7s#+&#+#'#8B%#+#'s#%nP#$##s#E>#%#s#+##$s#F#5j#:'#k#8N(VS'DQj#8N#[QEOIJCDLnK#$#+s#LE#$%#)#(#nG#$#$s#MC#-&#+#,#-s#4%#+#'s#0&#+#.#/s#4%#0#1s#4%#2#3s#4&#2#0#1s#4%#+#'B'#4#5#6#7s#4&#+#'#8#%#+#'>nP#$##s#Ns#'#%#s#4##$s#O#>j#:*#US&FnG#$#$s#RC#-&#+#,#-s#9%#+#'s#3&#+#.#/s#9%#0#1s#9%#2#3s#9&#2#0#1s#9%#+#'s#''#4#5#6#7s#9&#+#'#8s#%%#+#'s##nP#$##s#Ss#,#%#s#9##$s#T#s##j#:5#YS%FLECDWS*GDs#>[S&IJMQCDEnK#$#+s#YC#$%#)#(#[S$IJMQCDEnK#$#+s#[C#$%#)#(#\S'EOIJMCDLnK#$#+s#]E#$%#)#(#[S(IJMQCDEnK#$#+s#_C#$%#)#(#nG#$#$s#`D#-&#+#,#-s#G%#+#')&#+#.#9s#G%#0#1s#G%#2#3s#G&#2#0#1s#G%#+#'''#4#5#6#7s#G&#+#'#8%%#+#'#nP#$##s#a-#%#,##VS1s#b##FUS+#US2F%s#&73&$#US-&US3F%s##A;%$#US.)US4F%s#,s#+s#'%$#US),US5F%s#8s#7s#2%$#US6/US7F%s#]s#\s#?%$#YR2LECDYS#FLECD$s#u$#m#&#j#?G#&Gs#xs#js#i#j#@H#&Hs#ys#os#n#j#AN#&Ns#zs#ts#s#j#BH#&Hs#{s#ys#x#j#Cs$###"). Qed.
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
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.cutout1pB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.cutout1p); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwr_cut); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bpB); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kzero_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kfill_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kunk_cutB); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kzero_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kfill_cut); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kunk_cut); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kzero_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kfill_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.kunk_cutB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bpB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwr_cutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwr_cutB_eqf)|] [|@K; @un; @uk; @ub; @len; @kk; @kb; @a; @w; @v; @n; @k; @lo; @hi; @e; @m; @a1; @n1; @a2; @n2; @c; @k0; @l; @sp; @b; @wn; @wk; @wb; @x3; @x2; @x1; @x0; @x; @fk|] "#$L#/#N#$###%#(#3#6#&#)#*#B#+#7#'#E#8#:#,#-#<#F#G#H#I#5#>#?#A#.#C#D#2#@#J#K#L#M#N#O#P#9#=#;#4'#J$#K&#L)#M(US1Gk#$G#k#%H#k#&N#k#'H##DUQ#URD#CVQ#DVRCD#EWQ#CDWRECD#IXQ#ECDXRIECD#OYQ#IECDYROIECDk#(H6k#)N#k#*H#k#%H#k#&N#k#'H#US%F#JZS+#FOIECUS2GWS,GC##S$[S-#MKJCDEnL#$#+s##C#$%#*#)#ZOMKJCDEnL#$#+s#%C#$%#*#)##S.\S/#ES#MKCDInL#$#+s#(E#$%#*#)#[S0*MKJCDEnL#$#+s#*C#$%#*#)#nG#$#$s#+C#-&#+#,#-.%#+#(*&#+#.#/.%#0#1.%#2#3.&#2#0#1.%#+#(('#4#5#6#7.&#+#(#8%%#+#(#nP#$##s#,0#%#.##ZS&JFOIEC[S'S$MKJCDEnL#$#+s#/C#$%#*#)#[S%S$MKJCDEnL#$#+s#1C#$%#*#)#\S(ES.S#MKCDInL#$#+s#3E#$%#*#)#[S)S$MKJCDEnL#$#+s#5C#$%#*#)#nG#$#$s#6C#-&#+#,#-9%#+#()&#+#.#99%#0#19%#2#39&#2#0#19%#+#(''#4#5#6#79&#+#(#8%%#+#(#nP#$##s#7,#%#9##$s#8.#j#:@#k#$GPk#%H#k#&N#k#'H#k#;S*#US&FYDFOIECnG#$#$s#AC#-&#+#,#-s#$%#+#(@&#+#.#/s#$%#0#1s#$%#2#3s#$&#2#0#1s#$%#+#(2'#4#5#6#7s#$&#+#(#8;%#+#(9nP#$##s#B$#%#s#$##$s#C#.j#<(#k#=Hs#/k#>N#k#?H#US)FnG#$#$s#IC#-&#+#,#-s#,%#+#(s#(&#+#.#/s#,%#0#1s#,%#2#3s#,&#2#0#1s#,%#+#(:'#4#5#6#7s#,&#+#(#8s##%#+#(s#&nP#$##s#J?#%#s#,##$s#K#6j#:'#k#8N(VS(DJj#8N#[FES#MKCDInL#$#+s#QE#$%#*#)#nG#$#$s#RC#-&#+#,#-s#5%#+#(s#1&#+#.#/s#5%#0#1s#5%#2#3s#5&#2#0#1s#5%#+#(s##'#4#5#6#7s#5&#+#(#8#%#+#(?nP#$##s#Ss#(#%#s#5##$s#T#?j#:*#US'FnG#$#$s#WC#-&#+#,#-s#:%#+#(s#4&#+#.#/s#:%#0#1s#:%#2#3s#:&#2#0#1s#:%#+#(s#('#4#5#6#7s#:&#+#(#8s#&%#+#(s#$nP#$##s#Xs#-#%#s#:##$s#Y#s#$j#:5#ZS&FOIECDWS,GDs#?[S'S#KJFCDEnL#$#+s#^C#$%#*#)#[S%S#KJFCDEnL#$#+s#`C#$%#*#)#\S(ES$MKJCDInL#$#+s#bE#$%#*#)#[S)S#KJFCDEnL#$#+s#dC#$%#*#)#nG#$#$s#eD#-&#+#,#-s#H%#+#()&#+#.#9s#H%#0#1s#H%#2#3s#H&#2#0#1s#H%#+#(''#4#5#6#7s#H&#+#(#8%%#+#(#nP#$##s#f-#%#,##VS3s#g##FUS-#US4F%s#&73&$#US/&US5F%s##A;%$#US0)US6F%s#,s#+s#'%$#US+,US7F%s#8s#7s#2%$#US8/US9F%s#^s#]s#@%$#ZQ2OIECDZRFOIECD$s#z$#m#&#j#@G#&Gs#}s#ks#j#j#AH#&Hs#~s#ps#o#j#BN#&Ns$#s#us#t#j#CH#&Hs$$s#zs#y#j#DS*#&S*s$%s$#s#~#j#Es$*##"). Qed.
#[local] Hint Rewrite cutout1pB_eqf : bceq.


Definition kn_cutout (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (cutout1p k sp ub uk un) k.

Definition kn_cutoutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (cutout1pB bc sp ub uk un) (bc_fk bc).

Lemma kn_cutoutB_eqf : forall fk, kn_cutoutB (mkbc fk) = kn_cutout fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kn_cutoutB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kn_cutout); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.cutout1p); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.Lists.List.flat_map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mk_sprep); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk_mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.cutout1pB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.cutout1pB_eqf)|] [|@un; @uk; @K; @ub; @sp; @l; @n1; @k1; @b1; @s; @x1; @x0; @x; @fk|] "##d#(#=#&#$###,#%#.#/#'#0#2#:#4#5#8#9#+#;#<#=#>#?#1#7#6#3#-)#8$#9'#:&#/(#;)#<(URFk#$H#k#%I##EUK#ULE#DVK#EVLDE#GWK#DEWLGDEk#&F.k#$H#k#%I#k#'H#k#(N#UOC#JXP#CGDXE#CGDUQ%$FF$#XMJCGD&J#CGD$FF#J%<&#j#)-#k#*HNk#+I#k#,H#UMCWECGD&J#CGD$FF#/%s#%#,j#-(#$FF/E%s#(#/j#)s#)#XMCGDE&C#GDE$FF#CVS#s#-##CUQ#US$C's#1C*&$#UP&US%C'650%$#US&)US'C's#'s#&<%$#XK,GDEXLCGDE%s#:$#m#&#j#.H#(Hs#=s#3s#2#j#/I#(Is#>s#8s#7#j#0H#(Hs#?s#=s#<#j#1s#B##"). Qed.
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
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kreadZB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kreadZ); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lres); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_lookup); constr:(segs); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.Some); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupB_eqf)|] [|@n; @off; @acc; @hints; @sx; @rk; @rb; @scs; @s; @l; @v; @z; @n0; @op; @a; @b0; @lo; @e; @k; @i; @x; @k0; @x1; @x0; @fk|] "##Y#(#B###%#$#/#&#.#:#0#2#4#8#6#7#9#<#=#+#;#,#1#?#@#>#A#'#B#C#D#5#3#-&#@$#3$#A($S%US&Fk#$J#k#%F##CUK#ULC#EVK#CVLEC#DWK#ECWLDEC$N$Ok#&#Mk#'%#k#(N#k#$J#k#)F#k#*H#VPIGURNUROZCGDEQ$#VS'CS(VS)F#US*FnS#$O$#+=D#%#$%#,#-#nH#$#.>D#+$#/#$#0$&#1#2#3$&#1#2#3$&#1#2#3$&#1#2#3$'#(#4#0#5$'#(#6#7#0$nM#$#8?(#&&#.#+#'#%#+#'%#%\PIS+GDEQ+*nH#$#.AD#+$#/&$#0'&#1#2#3'&#1#2#3'&#1#2#3'&#1#2#3''#(#4#0#5''#(#9#7#0'nM#$#8B$#&&#.#+#'#%#+#'(#(WS$s##&#j#-1#\PIGDECQ0/nM#$#8s#&##&&#.#+#''%#+#',#,VS,s#'##GVS-I#VS.GIZS/87)&$#XK&DECXLGDECWS$s#.$#m#&#j#:J#%Js#1s#'s#&#j#;F#%Fs#2s#,s#+#j#8H#%Hs#3s#1s#0#j#<s#7##"). Qed.
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
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kread8eB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kread8e); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lres); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_lookup); constr:(segs); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupB_eqf)|] [|@off; @acc; @hints; @sx; @n; @rk; @rb; @scs; @s; @l; @x; @v; @x0; @fk|] "##X#'#A###$#%#-#9#.#7#0#2#5#6#8#=#>#*#:#,#+#/#4#<#?#@#&#A#B#C#3#;#1&#?$#1$#@$$S$US%Fk#$H#%CUJ#UKC%DVJ#CVKDC$L$Mk#%#Ik#&%#k#'L#k#(S&#k#)H#k#*F#VNGE#S'##############UPLUPMZCED%O$#VS(FEUS)FnQ$M$#+@D#%#$%#,#-#nI#$#.A&#&&#/#+#&#%#+#&$#$\NGS*ED*O)(nI#$#.s####&&#/#+#&%%#+#&&#&WRs#$%#j#-6#\NGEDC.O-,nI#$#.s#'##&&#/#+#&)%#+#&*#*VS+s#(#%EVS,G#VS-EGZS.=<)&$#WJ&DCWKEDCWRs#/$#m#&#j#0H#YS#Hs#2s#,s#+#j#.F#YS#Fs#3s#1s#0#j#1s#6##"). Qed.
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

Local Open Scope lzb_scope.
Fixpoint kwritableB (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%lzb
          then match xloB bc wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinsideB bc b off (ELit n) wb wk wn)%lzb then true
      else kwritableB bc rest b off n
  | _ :: rest => kwritableB bc rest b off n
  end.
Local Close Scope lzb_scope.

Lemma kwritableB_eqf : forall fk, kwritableB (mkbc fk) = kwritable fk.
Proof.
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwritableB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwritable); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xlo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB_eqf); constr:(@Corelib.Init.Datatypes.cons)|] [|@n; @off; @b; @k; @x; @wl; @a; @wb; @wk; @k0; @w; @v; @n0; @k1; @lo; @hi; @e; @m; @wn; @a1; @n1; @a2; @n2; @c; @k2; @b2; @b1; @o; @IH; @rest; @K; @fk|] "#$`#3#S#;#$#%###:#)#&#'#F#9#(#7#J#*#-#<#>#I#P#2#+#,#1#R#S#A#D#G#K#L#M#O#N#6#B#0#/#T#U#V#?#=#@#E#Q#8#H#C,#3(#L$#M&#N%#O%#2(#P(#Q%#R)US4Nk#$GCk#%G#k#&L#$FUR#US#F$DVR#FVS#DF$EWR#DFWS#EDF$IXR#EDFXS#IEDF$S'(#IEDF#S'IEDF%C$#k#$G#k#%G#k#&L#j#'9#US5N#P#EDFVS,C#j#$G#j#%G#j#&L#$S((#IEDF#S(IEDF%C$#k#$G#k#%G#k#&L##QJEDFVS-PD&FHnC#$##C$#%###K$S&VS.#E*PH*DF&$#nS$$G$#(C&#%$#)##KnC#$##C)#%###K&S/MVS0MS1nC#$##C$#%###KUS2M[S3-PH#DFEnC#$##C%#%###KnC#$##C##%#O#JnC#$##C*#%#O##nS%#$#*CD#$%#+#,#nN#$#-CH#-&#*#.#/I%#*#0E&#*#0#1I%#2#3E%#4#5E&#4#2#3I%#*#6#'#7#8#9#:J&#*#0#;I%#*#0E#S)S'HMJ#S6PMJI'87VS*S&EnS$$G$#(C##%$#)3#KnC#$##C%#%###K'21[S+S&PH0DFE'$##S&S(PHMnC#$##C$#%#O##nC#$##C(#%#O##nS%#$#*CD#$%#+#,#nN#$#-CH#-&#*#.#//%#*#0.&#*#0#1/%#2#3.%#4#5.&#4#2#3/%#*#6#'#7#8#9#:&&#*#0#;/%#*#0.%C1#j#&C#k#:LCk#<G#k#=L#k#8L#k#1G#k#>L#US+QZJPH@DFEnC#$##CB#%###KnC#$##C##%#O#2nC#$##Cs#'#%#O##nS%#$#*CD#$%#+#,#nN#$#-CH#-&#*#.#/>%#*#0=&#*#0#1>%#2#3=%#4#5=&#4#2#3>%#*#6#'#7#8#9#:5&#*#0#;>%#*#0=%C#2j#&+#US$Gk#4L#US*QUJEnS$$G$#(C##%$#)s#2#KnC#$##Cs#8#%###KnC#$##Cs#/#%#@#KnC#$##C##%#O#?nC#$##C%#%#O##nS%#$#*CD#$%#+#,#nN#$#-CH#-&#*#.#/s#+%#*#0s#*&#*#0#1s#+%#2#3s#*%#4#5s#*&#4#2#3s#+%#*#6#'#7#8#9#:B&#*#0#;s#+%#*#0s#*%C#?j#?-##S7HJIEVS-HD&FM'$#VS*S)E*HM&#s#BnS$$G$#(C%#%$#)##KnC#$##C'#%###K&S/JVS0JS1'$#US2J[S+S)HM#DFE'%#nC#$##C##%#O#s#=nC#$##C*#%#O##nS%#$#*CD#$%#+#,#nN#$#-CM#-&#*#.#/s#?%#*#04&#*#0#1s#?%#2#34%#4#54&#4#2#3s#?%#*#6#'#7#8#9#:s#@&#*#0#;s#?%#*#04VS,C#$QUS.#US8Q+s#%s#$:&$#US3&US9Q+s#3s#2s#*%$#()JEDFWIEDF+Cs#`s#<%$#WS:NMJ(-#EDF#Q$EDF%C$#m#'#j#$G#j#%G#j#&L#j#@s#j#j#As$3#j#BN#\S;Ns#zs#t#IEDFj#$G#)GCs$)s$(#j#%G#)Gs$8s$.s$-#j#&L#)Ls$9s$3s$2#j#'s$<#)s$=s$:s$8s$7#j#Cs$>##"). Qed.
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

Local Open Scope lzb_scope.
Fixpoint kwritable_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%lzb
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
Local Close Scope lzb_scope.

Lemma kwritable_xB_eqf : forall fk, kwritable_xB (mkbc fk) = kwritable_x fk.
Proof.
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwritable_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kwritable_x); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xhi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xlo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB_eqf); constr:(@Corelib.Init.Datatypes.cons)|] [|@n; @off; @b; @k; @x; @wl; @nh; @a; @wb; @wk; @k0; @w; @v; @n0; @k1; @lo; @hi; @e; @m; @wn; @a1; @n1; @a2; @n2; @c; @k2; @b2; @b1; @o; @IH; @rest; @K; @fk|] "#$e#4#S#<#$###%#:#;#&#G#)#(#'#8#K#L#-#*#N#=#?#2#+#,#1#P#Q#R#B#E#H#3#I#M#O#7#C#0#/#S#T#U#V#@#>#A#F#D#9#J+#M$#5(#N&#4(#O%#P)#Q(#R%US4Nk#$GCk#%H#k#&G##EUS$#US%E#DVS$#EVS%DE#FWS$#DEWS%FDE#IXS$#FDEXS%IFDE#S'&#IFDE$S'IFDE%C$#k#$G#k#%H#k#&G#j#'9#US5N$R#FDEVS-C#j#$G#j#%H#j#&G##S(&#IFDE$S(IFDE%C$#k#$G#k#%H#k#&G#$QMFDEVS.RD'EKnC#$##C$#%###J#S&VS/#L#S0VS1#I*S'D*FE'$#nO$H$#(C&#%$#)##JnO$H$#(C)#%$#*##JnC#$##C,#%###J[S2,RKLDEFnC#$##C##%#P#MnC#$##C%#%#P##nS##$#+CD#$%#,#-#nN#$#.CK#-&#+#/#0I%#+#1F&#+#1#2I%#3#4F%#5#6F&#5#3#4I%#+#7#'#8#9#:#;M&#+#1#<I%#+#1F$S)S'KLM$S6RLMIVS365VS*S&LVS+S0InO$H$#(C##%$#)0#JnO$H$#(C%#%$#*##JnC#$##C'#%###J[S,S&RKLDEF$S&S(RKLnC#$##C$#%#P##nC#$##C&#%#P##nS##$#+CD#$%#,#-#nN#$#.CK#-&#+#/#0/%#+#1.&#+#1#2/%#3#4.%#5#6.&#5#3#4/%#+#7#'#8#9#:#;&&#+#1#</%#+#1.%C1#j#&C#k#;GCk#=H#k#>G#k#9G#k#2H#k#?G#US,QZMRKLDEFnC#$##C##%#P#1nC#$##CA#%#P##nS##$#+CD#$%#,#-#nN#$#.CK#-&#+#/#0=%#+#1<&#+#1#2=%#3#4<%#5#6<&#5#3#4=%#+#7#'#8#9#:#;4&#+#1#<=%#+#1<%C#1j#&*#UOHk#5G#US*QUMLnO$H$#(C##%$#*s#,#JnC#$##Cs#5#%###JnC#$##C##%#P#<nS##$#+CD#$%#,#-#nN#$#.CK#-&#+#/#0s#(%#+#1s#'&#+#1#2s#(%#3#4s#'%#5#6s#'&#5#3#4s#(%#+#7#'#8#9#:#;?&#+#1#<s#(%#+#1s#'%C#<j#@+#US+QULInO$H$#(C##%$#)s#6#JnO$H$#(Cs#+#%$#*##JnC#$##Cs#?#%###JnC#$##C##%#P#s#&nS##$#+CD#$%#,#-#nN#$#.CK#-&#+#/#0s#2%#+#1s#1&#+#1#2s#2%#3#4s#1%#5#6s#1&#5#3#4s#2%#+#7#'#8#9#:#;s#)&#+#1#<s#2%#+#1s#1%C#s#&j#@5#$S7KMIFVS.KD'ELVS3$#VS*S)MVS+S&I*RD'#s#FnO$H$#(C%#%$#)##JnO$H$#(C'#%$#*##JnC#$##C)#%###J[S,S)KLMDEFnC#$##C##%#P#s#AnC#$##C%#%#P##nS##$#+CD#$%#,#-#nN#$#.CL#-&#+#/#0s#C%#+#11&#+#1#2s#C%#3#41%#5#61&#5#3#4s#C%#+#7#'#8#9#:#;s#D&#+#1#<s#C%#+#11VS-C##QUS1#US8Q(s#*@7&$#US/&US9Q(s#-s#,s#$%$#US2)US:Q(s#:s#9s#2%$#&,MFDEWIFDE(Cs#es#C%$#WS;NLM&0#FDE$Q$FDE%C$#m#'#j#$G#j#%H#j#&G#j#As#o#j#Bs$8#j#CN#\S<Ns$#s#y#IFDEj#$G#)GCs$.s$-#j#%H#)Hs$=s$3s$2#j#&G#)Gs$>s$8s$7#j#'s$A#)s$Bs$?s$=s$<#j#Ds$C##"). Qed.
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

Local Open Scope lzb_scope.
Fixpoint kzero_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%lzb
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
Local Close Scope lzb_scope.

Lemma kzero_xB_eqf : forall fk, kzero_xB (mkbc fk) = kzero_x fk.
Proof.
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kzero_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kzero_x); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xhi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xlo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB_eqf); constr:(@Corelib.Init.Datatypes.cons)|] [|@n; @off; @b; @k; @x; @zl; @nh; @a; @zb; @zk; @k0; @w; @v; @zn; @n0; @k1; @lo; @hi; @e; @m; @a1; @n1; @a2; @n2; @c; @k2; @b2; @b1; @o; @IH; @rest; @K; @fk|] "#$e#4#S#<#$###%#:#;#&#G#)#(#'#8#K#L#-#*#N#=#?#2#+#,#1#P#Q#R#B#E#H#3#I#M#O#7#C#0#/#S#T#U#V#@#>#A#F#D#9#J+#M$#5(#N&#4(#O%#P)#Q(#R%US4Nk#$GCk#%H#k#&G##EUS$#US%E#DVS$#EVS%DE#FWS$#DEWS%FDE#IXS$#FDEXS%IFDE#S'&#IFDE$S'IFDE%C$#k#$G#k#%H#k#&G#j#'9#US5N$R#FDEVS-C#j#$G#j#%H#j#&G##S(&#IFDE$S(IFDE%C$#k#$G#k#%H#k#&G#$QMFDEVS.RD'EKnC#$##C$#%###J#S&VS/#L#S0VS1#I*S'D*FE'$#nO$H$#(C&#%$#)##JnO$H$#(C)#%$#*##JnC#$##C,#%###J[S2,RKLDEFnC#$##C##%#P#MnC#$##C%#%#P##nS##$#+CD#$%#,#-#nN#$#.CK#-&#+#/#0I%#+#1#&#+#2#3I%#4#5F%#6#7F&#6#4#5I%#+#2F'#8#9#:#;M&#+#2#<I%#+#2F$S)S'KLMVS354VS*S&LVS+S0InO$H$#(C##%$#)/#JnO$H$#(C%#%$#*##JnC#$##C'#%###J[S,S&RKLDEF$S&S(RKLnC#$##C$#%#P##nC#$##C&#%#P##nS##$#+CD#$%#,#-#$S6RLMInN#$#.CK#-&#+#/#0/%#+#1$&#+#2#3/%#4#5#%#6#7#&#6#4#5/%#+#2#'#8#9#:#;'&#+#2#</%#+#2#%C1#j#&C#k#;GCk#=H#k#>G#k#9G#k#3H#k#?G#US,QZMRKLDEFnC#$##C##%#P#2nC#$##CA#%#P##nS##$#+CD#$%#,#-#nN#$#.CK#-&#+#/#0=%#+#1#&#+#2#3=%#4#51%#6#71&#6#4#5=%#+#21'#8#9#:#;5&#+#2#<=%#+#21%C#1j#&*#UOHk#6G#US*QUMLnO$H$#(C##%$#*s#,#JnC#$##Cs#5#%###JnC#$##C##%#P#=nS##$#+CD#$%#,#-#nN#$#.CK#-&#+#/#0s#(%#+#1#&#+#2#3s#(%#4#5<%#6#7<&#6#4#5s#(%#+#2<'#8#9#:#;@&#+#2#<s#(%#+#2<%C#<j#@+#US+QULInO$H$#(C##%$#)s#6#JnO$H$#(Cs#,#%$#*##JnC#$##Cs#?#%###JnC#$##C##%#P#s#'nS##$#+CD#$%#,#-#nN#$#.CK#-&#+#/#0s#2%#+#1#&#+#2#3s#2%#4#5s#&%#6#7s#&&#6#4#5s#2%#+#2s#&'#8#9#:#;s#*&#+#2#<s#2%#+#2s#&%C#s#&j#@5#VS.KD'ELVS3$#VS*S)MVS+S&I*RD'#s#EnO$H$#(C%#%$#)##JnO$H$#(C'#%$#*##JnC#$##C)#%###J[S,S)KLMDEFnC#$##C##%#P#s#@nC#$##C%#%#P##nS##$#+CD#$%#,#-#$S7KMIFnN#$#.CL#-&#+#/#0s#8%#+#1$&#+#2#3s#8%#4#5#%#6#7#&#6#4#5s#8%#+#2#'#8#9#:#;s#D&#+#2#<s#8%#+#2#VS-C##QUS1#US8Q(s#*@7&$#US/&US9Q(s#-s#,s#$%$#US2)US:Q(s#:s#9s#2%$#&,MFDEWIFDE(Cs#es#C%$#WS;NLM&0#FDE$Q$FDE%C$#m#'#j#$G#j#%H#j#&G#j#As#o#j#Bs$8#j#CN#\S<Ns$#s#y#IFDEj#$G#)GCs$.s$-#j#%H#)Hs$=s$3s$2#j#&G#)Gs$>s$8s$7#j#'s$A#)s$Bs$?s$=s$<#j#Ds$C##"). Qed.
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

Local Open Scope lzb_scope.
Fixpoint kfill_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%lzb
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinsideB bc b off n zb zk zn)%lzb then true
      else kfill_xB bc rest b off n c
  | _ :: rest => kfill_xB bc rest b off n c
  end.
Local Close Scope lzb_scope.

Lemma kfill_xB_eqf : forall fk, kfill_xB (mkbc fk) = kfill_x fk.
Proof.
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kfill_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kfill_x); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xhi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xlo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xloB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB_eqf); constr:(@Corelib.Init.Datatypes.cons)|] [|@c; @n; @off; @b; @k; @x; @zl; @nh; @a; @zb; @zk; @k0; @w; @v; @n0; @k1; @lo; @hi; @e; @m; @a1; @n1; @a2; @n2; @zn; @c'; @k2; @b2; @b1; @o; @IH; @rest; @K; @fk|] "#%+#7#[#?#%###$#>#&#=#N#*#'#;#(#T#)#S#/#+#,#@#B#V#5#-#.#4#X#Y#Z#E#H#M#P#6#Q#U#:#F#L#J#3#2#1#[#\#]#^#C#A#K#D#W#<#O#G#I#R.#R$#6)#S$#T&#U%#V(#5)#W%#X)#Y%#Z%US6Mk#$GCk#%I#k#&G#k#'I##EUS%#US&E#FVS%#EVS&FE#DWS%#FEWS&DFE#HXS%#DFEXS&HDFE#LYS%#HDFEYS&LHDFE#S))#LHDFE$S)LHDFE&C$#k#$G#k#%I#k#&G#k#'I#j#(>#US7M$S$#HDFEVS/C#j#$G#j#%I#j#&G#j#'I##S*)#LHDFE$S*LHDFE&C$#k#$G#k#%I#k#&G#k#'I#$RNHDFE%S8%#%#%#%#%#%#%#US9#,D#,P$VS0$#VS1S$FnC#$##C$#%###J*ES#nC#$##C$#%###J#S(VS2#K#S3VS4#L-S)F-DE*$#nQ$G$#)C&#%$#*##JnQ$G$#)C)#%$#+##JnC#$##C,#%###J[S5,S$S#KFEHnC#$##C2#%###JnC#$##C##%#O#NnC#$##C&#%#O##nS'#$#,CD#$%#-#.#nM#$#/CK#-&#,#0#1H%#,#2D&#,#2#3H%#4#5D%#6#7D&#6#4#5H%#,#2D'#8#9#:#;L&#,#<#=#%#,#2D$S:S$KPNL$S;S#PNLH$S+S)S#KPN':9'#8VS,S(KVS-S3LnQ$G$#)C##%$#*3#JnQ$G$#)C%#%$#+##JnC#$##C'#%###J[S.S(S$S#KFEH'B#$S(S*S$S#KPnC#$##C$#%#O##nC#$##C'#%#O##nS'#$#,CD#$%#-#.#nM#$#/CK#-&#,#0#12%#,#21&#,#2#32%#4#51%#6#71&#6#4#52%#,#21'#8#9#:#;0&#,#<#=#%#,#21&C4#j#'C#k#;ICk#>G#k#?I#k#9I#k#3G#k#@I#US.RZNS$S#KFEHnC#$##Cs#2#%###JnC#$##C##%#O#2nC#$##Cs#&#%#O##nS'#$#,CD#$%#-#.#nM#$#/CK#-&#,#0#1A%#,#2@&#,#2#3A%#4#5@%#6#7@&#6#4#5A%#,#2@'#8#9#:#;?&#,#<#=#%#,#2@&C#2j#'+#UQGk#6I#US,RUNKnQ$G$#)C##%$#+s#1#JnC#$##Cs#:#%###JnC#$##Cs#?#%#@#JnC#$##C##%#O#?nC#$##C%#%#O##nS'#$#,CD#$%#-#.#nM#$#/CK#-&#,#0#1s#.%#,#2s#-&#,#2#3s#.%#4#5s#-%#6#7s#-&#6#4#5s#.%#,#2s#-'#8#9#:#;s#,&#,#<#=#%#,#2s#-&C#?j#A-#US-RUPLnQ$G$#)C##%$#*s#=#JnQ$G$#)Cs#/#%$#+##JnC#$##Cs#F#%###JnC#$##C##%#O#-nS'#$#,CD#$%#-#.#nM#$#/CK#-&#,#0#1s#8%#,#2s#7&#,#2#3s#8%#4#5s#7%#6#7s#7&#6#4#5s#8%#,#2s#7'#8#9#:#;s#6&#,#<#=#%#,#2s#7&C#s#)j#A7#$S<KNLHD,Ns#TVS0s#T#VS1S#F'$#*EK'$#VS,S+PVS-S(L-S$F*#s#PnQ$G$#)C%#%$#*##JnQ$G$#)C'#%$#+##JnC#$##C)#%###J[S.S+S#KPFEH'/#nC#$##C##%#O#s#InC#$##C&#%#O##nS'#$#,CD#$%#-#.#nM#$#/CP#-&#,#0#1s#M%#,#25&#,#2#3s#M%#4#55%#6#75&#6#4#5s#M%#,#25'#8#9#:#;s#N&#,#<#=#%#,#25VS/C##RUS4#US=R+s#0s#$;&$#US2&US>R+s#3s#2s#(%$#US5)US?R+s#As#@s#8%$#),NHDFEXLHDFE+Cs#}s#J%$#WS@MPN)0#HDFE$R$HDFE&C$#m#'#j#$G#j#%I#j#&G#j#'I#j#Bs$,#j#Cs$X#j#DM#]SAMs$>s$7#LHDFEj#$G#(GCs$Js$I#j#%I#(Is$]s$Os$N#j#&G#(Gs$^s$Ts$S#j#'I#(Is$_s$Ys$X#j#(s$c#(s$ds$`s$^s$]#j#Es$e##"). Qed.
#[local] Hint Rewrite kfill_xB_eqf : bceq.



(* [comment removed for export] *)
Definition off_image_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_x k b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Definition off_image_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_xB bc b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Lemma off_image_xB_eqf : forall fk, off_image_xB (mkbc fk) = off_image_x fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.off_image_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.off_image_x); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart_x); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.img_lo); constr:(A); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.img_hi); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_xB_eqf)|] [|@n; @off; @n2; @k2; @b2; @n1; @k1; @b1; @b; @x1; @x0; @x; @fk|] "##P#(#=###.#$#%#&#0#/#1#3#5#7#:#6#+#,#8#9#<#;#'#=#>#?#4#2#-%#;$#<(UPQk#$DHk#%I##CUJ#UKC#EVJ#CVKEC#FWJ#ECWKFECk#&DHk#'I#k#(D#k#)D#k#*I#k#+D#ULGUMRUS#NUS$NVS%#$UM#ZCGFE'&#[LS&GFE('$WOH$#j#,,#[LGFEC+*'VS'H##GUS(#US)GZS*21(&$#XJ&FECXKGFECWOH$#m#&#j#-D#$DH?>#j#.I#$Is#*s#$s###j#/D#$Ds#+s#)s#(#j#0s#.##"). Qed.
#[local] Hint Rewrite off_image_xB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition flat_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match base_range k b, xlo k n, xhi k n with
  | Some (lo, hi), Some nl, Some nh => (Z.leb 0 (lo + off) && Z.leb (hi + off + nh) two64 && Z.ltb 0 nl)%bool
  | _, _, _ => false
  end.

Local Open Scope lzb_scope.
Definition flat_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
  match base_rangeB bc b, xloB bc n, xhiB bc n with
  | Some (lo, hi), Some nl, Some nh => (Z.leb 0 (lo + off) && Z.leb (hi + off + nh) two64 && Z.ltb 0 nl)%lzb
  | _, _, _ => false
  end.
Local Close Scope lzb_scope.

Lemma flat_xB_eqf : forall fk, flat_xB (mkbc fk) = flat_x fk.
Proof. intros. bcfe. unfold flat_xB, flat_x. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite flat_xB_eqf : bceq.



(* [comment removed for export] *)
Definition ehi (k : list kentry) (e : expr) : option Z := xhi k e.
Definition elo (k : list kentry) (e : expr) : option Z := xlo k e.

(* [comment removed for export] *)
Definition len_eqb (k : list kentry) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0 k [(n, 0%Z)] [(m, 0%Z)] && lin_ge0 k [(m, 0%Z)] [(n, 0%Z)]).

Local Open Scope lzb_scope.
Definition len_eqbB (bc : bctx) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0B bc [(n, 0%Z)] [(m, 0%Z)] && lin_ge0B bc [(m, 0%Z)] [(n, 0%Z)]).
Local Close Scope lzb_scope.

Lemma len_eqbB_eqf : forall fk, len_eqbB (mkbc fk) = len_eqb fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.len_eqbB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.len_eqb); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xterms); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B_eqf)|] [|@m; @neg; @pos; @b; @x0; @x; @fk|] "##T#'#?###-#%#$#.#;#/#1#=#3#4#7#&#5#,#*#+#:#>#?#@#A#2#0#<#9#8#6)#-&#:$#;'#<&#=%#>%URS#k#$DG$CUI#UJC$FVI#CVJFCk#%LGk#&L#UMEVNEFVS$DH%DHEKUS%$&%$#%DHFK&'#%VC%#VC$&'$#(,##O)'#O(*'$#(0#WPG'#j#'4#VNFC%DHCK&4#2#E0##E$1'$#((#VS&G#$EUS'#US(EZS)@?.&$#WI&FCWJEFCWPG$#m#&#j#(D#YQDGs#)s#(#j#)D#YQDs#0s#.s#-#j#*s#2##"). Qed.
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
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.page_alignedB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.page_aligned); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ealign); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ealignB_eqf)|] [|@e; @z; @n; @op; @a; @b; @sx; @lo; @e0; @k; @i; @k0; @x; @fk|] "##]#*#A#$#1###0#'#%#&#(#3#2#4#7#=#;#8#-#.#6#:#9#>#@#)#A#B#C#5#/#<#?&#?$#@%#.%URS#UKEUL#UMEk#$FS$UNC#O######################UP#VS%E#VS&#S'US(O####UP#UCH$$#UIG$&#UGJ$(#nF#$#$DC#+$#%-$#&'&#'#(#)%&#'#(#)%&#'#(#)%&#'#(#)%'#*#+#&#,#'#*#-#.#&#%IH$+#%JG$-#%S)J$/#nF#$#$DC#+$#%4$#&'&#'#(#)%&#'#(#)%&#'#(#)%&#'#(#)%'#*#+#&#,#'#*#/#.#&#WQD*#j#%s#&#%HC$4#%GI$6#nF#$#$DE#+$#%;$#&%&#'#(#)#&#'#(#)#&#'#(#)#&#'#(#)#'#*#+#&#,,'#*#/#.#&,VS*D#UKCUS+#US,CZS-s#0s#/,&$#VL&EVMCEWQD$#m#&#j#0F#YS.FDs#8s#7#j#1s#;##"). Qed.
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
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xlo1B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xlo1); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_brange); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zlit64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_srangeB); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_srange); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_srangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_brangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_brangeB_eqf)|] [|@e; @p0; @lo'; @z0; @x; @p; @lo; @z; @n; @op; @a; @b; @sx; @e0; @k; @i; @k0; @o; @fk|] "#$L#-#G#4#5#$###:#'#(#%#3#&#)#*#+#6#8#;#D#C#?#A#0#1#>#@#B#,#E#F#G#H#I#2#7#<#=#9,#2%#C$#4%#3%#D&#E%#5%#6%#F)US'S(UCD$FUP#UQFVGDDUC#k#$K#UREUS)F(D#$L)#JUHIVS*HE(D#nG%DD$#%1F#$%#&#'#(DEnC$/$#(3'#%$#%$##nG%DD$#)4F#$%#*#+#UEJnG%DD$#)6F#$%#&#+&*-JnG%DD$#)8F#$%#*#+(US+DnC$6$#(:%#%$#)$##nC$7$#(;(#%$#)'##nC$8$#(<1#%$#)*##$I)#HUMNnC$<$#(@##%$#%1#0nG%DD$#)AF#$%#*#+#ULH*(HnC$@$#(s#$##%$#).#-nC$A$#(s#%%#%$#)1##nC$B$#(s#&*#%$#)'##$M)#IUNOnC$s#&$#(s#*##%$#%;#:nG%DD$#)s#+F#$%#*#+#*'InC$s#)$#(s#-##%$#)7#6nC$s#*$#(s#.B#%$#):##nC$s#+$#(s#/)#%$#)&##nK#$#$s#0E#+$#+s#'$#,6&#-#.#/,&#-#.#/,&#-#.#/,&#-#.#/,'#0#*#,#1#'#0#2#3#,#%LJ#MInC$s#/$#(s#3##%$#%s#$#s##nG%DD$#)s#4F#$%#*#+##LJ&LJnC$s#3$#(s#7##%$#)A#@nC$s#4$#(s#8%#%$#)s#$##nC$s#5$#(s#9*#%$#)'##%IH#ONnC$s#8$#(s#<##%$#%s#-#s#,nG%DD$#)s#=F#$%#*#+##IH&IHnC$s#<$#(s#@##%$#)s#*#s#)nC$s#=$#(s#A%#%$#)s#-##nC$s#>$#(s#B*#%$#)'##%MI#S,OnC$s#A$#(s#E##%$#%s#6#s#5nG%DD$#)s#FF#$%#*#+#&MInC$s#D$#(s#H##%$#)s#2#s#1nC$s#E$#(s#I9#%$#)s#5##nC$s#F$#(s#J)#%$#)&##nK#$#$s#KE#+$#+s#B$#,4&#-#.#/+&#-#.#/+&#-#.#/+&#-#.#/+'#0#*#,#1#'#0#4#3#,#'s#L>#j#5s#G#US#EnC$s#K$#(s#Os#<#%$#)s#9#s#8nC$s#L$#(s#P=#%$#)s#<##nC$s#M$#(s#Qs#F#%$#)?##nC$s#N$#(s#Rs#2#%$#)s#<#s#;nC$s#O$#(s#S7#%$#)s#?##nC$s#P$#(s#Ts#8#%$#)9##nC$s#Q$#(s#Us#I#%$#)s#?#s#>nC$s#R$#(s#Vs#&#%$#)s#B##nC$s#S$#(s#Ws#1#%$#)3##nK#$#$s#XE#+$#+s#O$#,)&#-#.#/&&#-#.#/&&#-#.#/&&#-#.#/&'#0#*#,#1#'#0#2#3#,#'s#Y#0j#5s#T#US$EnC$s#X$#(s#\s#I#%$#)s#*#s#&nC$s#Y$#(s#]s#=#%$#)B#>nC$s#Z$#(s#^s#R#%$#):#7nK#$#$s#_E#+$#+s#V$#,%&#-#.#/$&#-#.#/$&#-#.#/$&#-#.#/$'#0#*#,#1#'#0#2#3#,#'s#`#7j#5s#[#%JEnC$s#_$#(s#cs#'#%$#%s#T#s#SnG%DD$#)s#dF#$%#*#+##JE&JEnC$s#c$#(s#g##%$#)s#Q#s#PnC$s#d$#(s#h%#%$#)s#T##nC$s#e$#(s#i)#%$#)'##%HL#NMnC$s#h$#(s#l##%$#%s#]#s#\nG%DD$#)s#mF#$%#*#+##HL&HLnC$s#l$#(s#p##%$#)s#Z#s#YnC$s#m$#(s#q%#%$#)s#]##nC$s#n$#(s#r*#%$#)'##nK#$#$s#sF#+$#+s#j$#,,&#-#.#/#&#-#.#/#&#-#.#/#&#-#.#/#'#0#*#,#1s#3'#0#4#3#,s#3VS-s#t#$EUS%#US.E+s#r?9&$#US&&US/E+s#us#/s##%$#US0)US1E+s#xs#ws#3%$#VP,FVQEF's$%$#m#&#j#(K#YS2Ks$(s$&s$%#j#6s$*##"). Qed.
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
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xhi1B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xhi1); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_brange); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zlit64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB); constr:(@Stdlib.ZArith.BinInt.Z.min); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_srangeB); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.erange); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_srange); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.erangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_srangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_brangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_brangeB_eqf)|] [|@e; @p0; @z0; @hi'; @x; @p; @z; @hi; @n; @op; @a; @b; @sx; @lo; @e0; @k; @i; @k0; @o; @fk|] "#$L#-#G#4#5###$#:#'#(#&#%#3#)#*#+#6#8#;#D#C#?#A#0#1#>#@#B#,#E#F#G#H#I#2#7#<#=#9,#2%#C$#4%#3%#D&#E%#5%#6%#F)US'S(UCD$EUP#UQEVGDDUC#k#$L#URFUS)E(D#$J)#KUHIVS*JE(D#nG%DD$#%1E#$%#&#'#(DEnC$/$#(3'#%$#%$##nG%DD$#)4E#$%#*#+#UFKnG%DD$#)6E#$%#*#'&*-KnG%DD$#)8E#$%#*#+(US+DnC$6$#(:%#%$#)$##nC$7$#(;(#%$#)'##nC$8$#(<1#%$#)*##$I)#HUMNnC$<$#(@##%$#%1#0nG%DD$#)AE#$%#*#+#UJH*(HnC$@$#(s#$##%$#).#-nC$A$#(s#%%#%$#)1##nC$B$#(s#&*#%$#)'##$M)#IUNOnC$s#&$#(s#*##%$#%;#:nG%DD$#)s#+E#$%#*#+#*'InC$s#)$#(s#-##%$#)7#6nC$s#*$#(s#.B#%$#):##nC$s#+$#(s#/)#%$#)&##nL#$#$s#0F#+$#*s#'$#,6&#-#.#/,&#-#.#/,&#-#.#/,&#-#.#/,'#0#1#,#2#'#0#3#4#,#%JK#MInC$s#/$#(s#3##%$#%s#$#s##nG%DD$#)s#4E#$%#*#+##JK&JKnC$s#3$#(s#7##%$#)A#@nC$s#4$#(s#8%#%$#)s#$##nC$s#5$#(s#9*#%$#)'##%IH#ONnC$s#8$#(s#<##%$#%s#-#s#,nG%DD$#)s#=E#$%#*#+##IH&IHnC$s#<$#(s#@##%$#)s#*#s#)nC$s#=$#(s#A%#%$#)s#-##nC$s#>$#(s#B*#%$#)'##%MI#S,OnC$s#A$#(s#E##%$#%s#6#s#5nG%DD$#)s#FE#$%#*#+#&MInC$s#D$#(s#H##%$#)s#2#s#1nC$s#E$#(s#I9#%$#)s#5##nC$s#F$#(s#J)#%$#)&##nL#$#$s#KF#+$#*s#B$#,4&#-#.#/+&#-#.#/+&#-#.#/+&#-#.#/+'#0#1#,#2#'#0#5#4#,#'s#L>#j#6s#G#US#FnC$s#K$#(s#Os#<#%$#)s#9#s#8nC$s#L$#(s#P=#%$#)s#<##nC$s#M$#(s#Qs#F#%$#)?##nC$s#N$#(s#Rs#2#%$#)s#<#s#;nC$s#O$#(s#S7#%$#)s#?##nC$s#P$#(s#Ts#8#%$#)9##nC$s#Q$#(s#Us#I#%$#)s#?#s#>nC$s#R$#(s#Vs#&#%$#)s#B##nC$s#S$#(s#Ws#1#%$#)3##nL#$#$s#XF#+$#*s#O$#,)&#-#.#/&&#-#.#/&&#-#.#/&&#-#.#/&'#0#1#,#2#'#0#3#4#,#'s#Y#0j#6s#T#US$FnC$s#X$#(s#\s#I#%$#)s#*#s#&nC$s#Y$#(s#]s#=#%$#)B#>nC$s#Z$#(s#^s#R#%$#):#7nL#$#$s#_F#+$#*s#V$#,%&#-#.#/$&#-#.#/$&#-#.#/$&#-#.#/$'#0#1#,#2#'#0#3#4#,#'s#`#7j#6s#[#%KFnC$s#_$#(s#cs#'#%$#%s#T#s#SnG%DD$#)s#dE#$%#*#+##KF&KFnC$s#c$#(s#g##%$#)s#Q#s#PnC$s#d$#(s#h%#%$#)s#T##nC$s#e$#(s#i)#%$#)'##%HJ#NMnC$s#h$#(s#l##%$#%s#]#s#\nG%DD$#)s#mE#$%#*#+##HJ&HJnC$s#l$#(s#p##%$#)s#Z#s#YnC$s#m$#(s#q%#%$#)s#]##nC$s#n$#(s#r*#%$#)'##nL#$#$s#sE#+$#*s#j$#,,&#-#.#/#&#-#.#/#&#-#.#/#&#-#.#/#'#0#1#,#2s#3'#0#5#4#,s#3VS-s#t#$FUS%#US.F+s#r?9&$#US&&US/F+s#us#/s##%$#US0)US1F+s#xs#ws#3%$#VP,EVQFE's$%$#m#&#j#(L#YS2Ls$(s$&s$%#j#7s$*##"). Qed.
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
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xb2B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xb2); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xhi1); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.deand); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xlo1B); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.min); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xlo1); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xlo1B_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xhi1B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xhi1B_eqf)|] [|@e; @x; @hi; @lo; @p; @plain; @hi'; @lo'; @e'; @s; @o; @fk|] "#$6#+#I#4#2#$#'###(#&#%#F#1#3#)#5#7#9#;#D#G#>#8#.#/#<#=#A#B#C#E#*#H#I#J#K#0#6#@#?#:*#4%#1%#E$#5%#F'#G%#H&US'S(VMCCUD#%GUO#UPGUDCk#$L#UQEUREVS)GS*%F&#IUIF'CCEG(0#US+1nD$C$#%1&#%$#&$##nD$C$#%2(#%$#'##$&*EUIJVS,JE%N&#HUHNnD$C$#%9##%$#&,#+nD$C$#%:%#%$#'##,VS#FHVS-E#VS.GI'CC$#(@#nM%CC$#(@G#$%#'#&#VS#EJ'CC#G(s#$#nD$s#%$#)s#$,#%$#(&##nK#$##s#%2#%###-%H&#FUFHnD$C$#%s#)##%$#&<#;nD$C$#%s#*%#%$#'##<nD$C$#%s#+9#%$#*(##nD$C$#%s#,;#%$#+##<nK#$##s#-s#%#%#=##nM%LC$#%s#.s#'#$%#,#-##FI$HFnD$C$#%s#1##%$#&s#$#s##nD$C$#%s#2%#%$#'##s#$#FE$HJ#NH$S/NnD$C$#%s#7##%$#&s#*#s#)nD$C$#%s#8%#%$#'##s#*nD$s#:$#)s#9##%$#(;#8nK#$##s#:s#'#%###$#HF$NHnD$C$#%s#=##%$#&s#0#s#/nD$C$#%s#>%#%$#'##s#0nD$C$#%s#?-#%$#*'##nD$C$#%s#@/#%$#+##0nK#$##s#As#9#%#1##nM%LC$#%s#Bs#;#$%#,#-#)s#C7#j#.s#?#US$EUJInD$C$#%s#G##%$#'8#s#9UJEnD$C$#%s#Is###%$#'4#s#;nD$s#K$#)s#J##%$#(s#,#s#)nK#$##s#Ks#8#%###$nD$C$#%s#Ls#A#%$#'1#s#>nD$C$#%s#M;#%$#*$##nD$C$#%s#N(#%$#+##)nK#$##s#Os#G#%#*##nM%LC$#%s#Ps#I#$%#,#-#)s#Q#1j#.s#M#URG#IJ$FInD$C$#%s#V##%$#&s#I#s#HnD$C$#%s#W%#%$#'##s#I#IE$FJnD$s#[$#)s#Z>#%$#(s#<#s#9nK#$##s#[s#H#%###?nD$C$#%s#\%#%$#*##s#,nD$C$#%s#]'#%$#+##(nK#$##s#^s#V#%#)##nM%LC$#%s#_.#$%#,#-#VS0s#`#%EUS%#US1EZS&s#_A4&$#US2&US3EZS&s#bs#as#%%$#VO)GVPEG)s#j$#m#&#j#%L#YS4Ls#ms#ks#j#j#/s#p##"). Qed.
#[local] Hint Rewrite xb2B_eqf : bceq.


Definition xlo2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (lo, _) => Some lo | None => None end.

Definition xlo2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (lo, _) => Some lo | None => None end.

Lemma xlo2B_eqf : forall fk, xlo2B (mkbc fk) = xlo2 fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xlo2B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xlo2); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xb2); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xb2B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xb2B_eqf)|] [|@e; @p; @lo; @z; @x; @o; @fk|] "##C#&#8#$#.###-#,#4#0#/#1#3#5#)#*#6#7#%#8#9#:#2#+#UNOUFDUIEUJ#UKEVLDDUF#k#$G#UHCUECVPDCnL%DD$#%,E#$%#&#'#UQDnF$*$#(.&#%$#%$##VHRCnF$,$#(0##%$#%&#%WM1%#j#),#VHCEnF$0$#(4##%$#%*#)VS#5#UICUS$#US%CZS&32)&$#VJ&EVKCEWM<$#m#&#j#(G#YS'G?=<#j#*A##"). Qed.
#[local] Hint Rewrite xlo2B_eqf : bceq.


Definition xhi2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (_, hi) => Some hi | None => None end.

Definition xhi2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (_, hi) => Some hi | None => None end.

Lemma xhi2B_eqf : forall fk, xhi2B (mkbc fk) = xhi2 fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xhi2B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xhi2); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xb2); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xb2B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xb2B_eqf)|] [|@e; @p; @z; @hi; @x; @o; @fk|] "##C#&#8###.#$#-#,#4#0#/#1#3#5#)#*#6#7#%#8#9#:#2#+#UNOUFDUICUJ#UKCVLDDUF#k#$G#UHEUCEVPDCnL%DD$#%,C#$%#&#'#UQDnF$*$#(.&#%$#%$##VHREnF$,$#(0##%$#%&#%WM1%#j#),#VHECnF$0$#(4##%$#%*#)VS#5#UIEUS$#US%EZS&32)&$#VJ&CVKECWM<$#m#&#j#(G#YS'G?=<#j#*A##"). Qed.
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
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.nat_ind); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kread_bytesB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kread_bytes); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kreadZB); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kreadZ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kreadZB_eqf)|] [|@off; @b; @fuel; @x0; @x; @rest; @z; @o; @n; @IH; @f; @fk|] "##u#+#D#4###$#%#5#&#(#3#:#0#6#8#'#)#E#.#;#>#?#=#/#@#A#C#B#D#*#F#1#7#2#9#<*#@$#-%#.%#A&#.'#B(#C$URS'URCUG#k#$C#k#%J##F$#D%DF&&$#j#&L##E$#K%KEWM*KDWNKFD'KHEDVS#0#j#'C#(C2'&#j#(J#(J3+*##H)E$$#%$H#O)FWM$#DWN$OD%HI#P)KXS$$FE#US(S)VS%F#VEH#WS*CEDVS+s#&#US,s#'nG$s#($#(s#'&#%$#)$##nG$C$#(s#(*#%$#*##$XQPFE,'IS-H*nG$s#,$#(s#+##%$#)(#'nG$C$#(s#,%#%$#*##(&s#-'#j#+s#,#UGCk#,L#k#$C#k#%J#UQIWDFE7nG$C$#(s#5##%$#*,#1&s#6#,j#+'#XQIED;VS%E:'OPF#nG$s#<$#(s#;##%$#)8#7nG$C$#(s#<&#%$#*##8VS#s#=##IUS$#US.IZS&10,&$#$&HZS&s#As#(7$#F)HXM)#ED'$IED&s#G$#m#'#j#'C#(Cs#Js#1s#0#j#(J#(Js#Ks#7s#6#j#-s#G#j#.L#XS/s#Hs#=#Dj#&L#j#/s#S##"). Qed.
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
  let '(bb, bk) := split_lit b in set_kn cs (kn_havocM (kn cs) bb bk n).   (* [comment removed for export] *)

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
Definition xinside_c (k : list kentry) (b : expr) (off : Z) (n : expr) (cb : expr) (ck : Z) (cn : expr) : bool :=
  if xinside k b off n cb ck cn then true else xinside0 k b off n cb ck cn.
Definition xinside_cB (bc : bctx) (b : expr) (off : Z) (n : expr) (cb : expr) (ck : Z) (cn : expr) : bool :=
  if xinsideB bc b off n cb ck cn then true else xinside0B bc b off n cb ck cn.
Lemma xinside_cB_eqf : forall fk, xinside_cB (mkbc fk) = xinside_c fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xinside_cB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xinside_c); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinside0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xinside0); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinside0B_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xinsideB_eqf)|] [|@cn; @ck; @cb; @n; @off; @n2; @k2; @b2; @n1; @k1; @b1; @b; @x4; @x3; @x2; @x1; @x0; @x; @fk|] "##k#+#>#$###%#1#3#&#'#)#(#2#4#6#:#8#*#<#;#7#.#/#=#>#?#@#5#0#9&#;$#<(#=&US%S&k#$FGk#%L#k#&F#k#'F#k#(L##DUM#UND#CVM#DVNCD#EWM#CDWNECD#HXM#ECDXNHECD#IYM#HECDYNIHECD#KZM#IHECDZNKIHECDk#)FGk#*L#k#+F#k#,F#k#-L#k#.F#UPJZDJKIHEC#Q[S##JKIHECnG#$##G%#%#O##[PQJKIHEC[RQJKIHECnG#$##G$#%#O##%G&#j#/,#URJnG#$##G(#%#O#,%G#'j#/0#[PJKIHECD[RJKIHECDnG#$##G$#%#O##VS'G##JUS##US(JZS$8-*&$#US)&US*JZS$;:1%$#[M)KIHECD[NJKIHECD%G$#m#&#j#0F#$FGs#(s#'#j#1L#$Ls#?s#-s#,#j#2F#$Fs#@s#2s#1#j#3F#$Fs#As#7s#6#j#4L#$Ls#Bs#<s#;#j#5F#$Fs#Cs#As#@#j#6s#I##"). Qed.
#[local] Hint Rewrite xinside_cB_eqf : bceq.

(* [comment removed for export] *)
Definition find_containing (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside_c k b off n (am_base m) 0 (am_len m)) ms.

Local Open Scope lzb_scope.
Definition find_containingB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside_cB bc b off n (am_base m) 0 (am_len m)) ms.
Local Close Scope lzb_scope.

Lemma find_containingB_eqf : forall fk, find_containingB (mkbc fk) = find_containing fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.amap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.mkind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.find_containingB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.find_containing); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xinside_c); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.Lists.List.find); constr:(@Corelib.Init.Datatypes.negb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.is_fog); constr:(@Stdlib.Lists.List.existsb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.mkind_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.am_kind); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.am_base); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.am_len); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xinside_cB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xinside_cB_eqf)|] [|@n; @off; @b; @kinds; @cn; @ck; @cb; @m; @x3; @x2; @x1; @x0; @x; @fk|] "##n#+#H###$#%#3#&#1#'#(#6#8#4#:#2#;#E#@#C#<#/#5#?#>#B#A#D#F#*#)#H#I#J#9#7#0#G#.#=(#C$#D(#E%#F$#G&&S%&H&OUS&Hk#$F#k#%M#k#&F#k#''##CUK#ULC#DVK#CVLDC#EWK#DCWLEDC#GXK#EDCXLGEDC#IYK#GEDCYLIGEDCk#(FNk#)M#k#*F#k#$F#k#%M#k#&F#UPJUS'CUS(#US)CUS*#WRO#JnN#$##N&#%###S#US+CUS,CZDIGE$Q#nN#$##N&#%###S#j#+H#'H#J%-*[PS-IGE)Q(%$#j#+H#'H#JWS$s#.(#j#&6#WRO2I%5#[PS.GED1Q0%$#j#+H#'H#IVS/s#6##JUS0#US1JZS2A@-&$#ZK&IGEDCZLJIGEDCWS$s#=$#m#&#j#,F#$Fs#@s#.s#-#j#-M#$Ms#As#3s#2#j#.F#$Fs#Bs#8s#7#j#/s#F#$s#Gs#Cs#=s#<#j#0s#I#$s#Js#Ds#Bs#A#j#1s#L##"). Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).

Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrlB bc b 3) (ELit (shadow_off A))) in (sb, sk, mkSrlB bc n 3).

Lemma shadow_ofB_eqf : forall fk, shadow_ofB (mkbc fk) = shadow_of fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_ofB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_of); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mkSrl); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.split_lit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.eadd); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.shadow_off); constr:(A); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkSrlB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkSrlB_eqf)|] [|@n; @s; @a; @x; @sb; @sk; @e; @x0; @fk|] "##W#)#A#/#%###1#$#0#2#4#&#6#7#.#,#-#;#<#:#>#?#=#(#'#A#B#C#5#@#3#9#8(#='#,&#>$#?%#@$UOPVHCFVH#Ck#$C#%EUI#UJE%GVI#EVJGEk#%FCk#&C#ULDUQRUS##VED#US$S%US&#&%#'##CFGEVDK)#7C$#nH%CF$#'7&#$%#(#)#$KD,&#*'#$S'K/#=C*#nH%CF$#'=%#$%#(#)#WM>)#j#*6#$DG4&#2'#$S(D7#s#%C2#nH%CF$#'s#%%#$%#(#)#VS)s#&#%DUS*#US+DZS,A@-&$#WI&GEWJDGEWMs#-$#m#&#j#+C#YNCs#0s#*s#)#j#'C#YNCs#1s#/s#.#j#,s#5##"). Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_coversZ (m : amap) (lo hi : Z) : bool :=
  match am_base m, am_len m with
  | ELit a, ELit l => (negb (is_fog m) && mkind_eqb (am_kind m) KRWLAZY
                       && Z.leb 0 a && Z.leb 0 l && Z.ltb (a + l) two64 && Z.leb a lo && Z.leb hi (a + l))%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition shadow_split_ok (k : list kentry) (ms : list amap) (b n sb : expr) (sk : Z) (sn : expr) : bool :=
  let '(bb, bk) := split_lit b in
  let shlo := shadow_off A - 4096 in
  (Z.ltb 0 shlo && Z.ltb shlo KHI && Z.eqb (KHI mod 8) 0 && Z.eqb (shlo mod 8) 0 && flat_x k bb bk n && flat_x k sb sk sn
   && ranges_apart_x k bb bk n (ELit shlo) 0 (ELit (KHI - shlo))
   && match xhi k b, xhi k n with Some hb, Some hn => Z.leb (hb + hn) (2 ^ 47) | _, _ => false end
   && existsb (fun m => lit_coversZ m (shadow_off A) (shadow_off A + shlo / 8)) ms
   && existsb (fun m => lit_coversZ m (shadow_off A + KHI / 8) (shadow_off A + 2 ^ 47 / 8)) ms)%bool.

Local Open Scope lzb_scope.
Definition shadow_split_okB (bc : bctx) (ms : list amap) (b n sb : expr) (sk : Z) (sn : expr) : bool :=
  let '(bb, bk) := split_lit b in
  let shlo := shadow_off A - 4096 in
  (Z.ltb 0 shlo && Z.ltb shlo KHI && Z.eqb (KHI mod 8) 0 && Z.eqb (shlo mod 8) 0 && flat_xB bc bb bk n && flat_xB bc sb sk sn
   && ranges_apart_xB bc bb bk n (ELit shlo) 0 (ELit (KHI - shlo))
   && match xhiB bc b, xhiB bc n with Some hb, Some hn => Z.leb (hb + hn) (2 ^ 47) | _, _ => false end
   && existsb (fun m => lit_coversZ m (shadow_off A) (shadow_off A + shlo / 8)) ms
   && existsb (fun m => lit_coversZ m (shadow_off A + KHI / 8) (shadow_off A + 2 ^ 47 / 8)) ms)%lzb.
Local Close Scope lzb_scope.

Lemma shadow_split_okB_eqf : forall fk, shadow_split_okB (mkbc fk) = shadow_split_ok fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.amap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_split_okB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_split_ok); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.flat_x); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.split_lit); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.shadow_off); constr:(A); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.KHI); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.option); constr:(@Stdlib.Lists.List.existsb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.lit_coversZ); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ranges_apart_x); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xhi); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.ranges_apart_xB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.flat_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.flat_xB_eqf)|] [|@sn; @sk; @sb; @n; @b; @off; @x; @hn; @hb; @m; @bb; @bk; @n2; @k2; @b2; @n1; @k1; @b1; @e; @o; @x4; @x3; @x2; @x1; @x0; @fk|] "#%)#.#\#7#H#5###6#$#%#)#&#'#(#R#*#4#8#:#@#,#+#V#G#M#X#1#<#>#A#?#J#I#L#K#-#T#Y#2#B#C#F#P#N#Z#[#\#]#^#W#E#9#3#D#O#Q#S#=#U#;0#Q%#R$#S$#T(#U$#V%#W$#X&#;'#E%#Y&#Z%#[)US*S6US*Pk#$ECk#%G#k#&E#k#'E#k#(E#%FUQ#URF%HVQ#FVRHF%IWQ#HFWRIHF%KXQ#IHFXRKIHF%LYQ#KIHFYRLKIHF%MZQ#LKIHFZRMLKIHFk#'ECk#)G#k#(E#US+JUS,MUS7S8$S9$#$#$#$#$#$#$#$#$#$#$#'#VS-0#VS.S##VS.$S'nC#$##C$#%###D'1VS/S'#VS0#S#nC#$##C&#%###DVS/*&VS0#S#nC#$##C%#%###DWIHFJnC#$##C$#%###DWIMLKnC#$##C$#%###D%S$US12VS-S'3US1#[S2&HFJ%S##nC#$##C(#%###DVS((O%S3VS(#O(HF's#()s#))#)#)#'#VS:(#VS;*#nN$G$#*C,#%$#+##DnN$G$#*C/#%$#,##DnC#$##C1#%###D.s#&B(s#5#WS4Fs#6#j#-P#*P#S%nC#$##C(#%###D.S's#((s#;#./s#*(s#=#WS4F%#j#-P#*P#S%nC#$##C*#%###DnS&%EG$#*Cs#C#$%#.#/##s#4s#3##s#0##s#.+S$HFJ#$#+S$MLK#$#[S)S$HFJs#,S#s#*#$#,S$O,S3OnN$G$#*C##%$#+@#DnN$G$#*C%#%$#,##D#'###;##4nS&%EG$#*Cs#T#$%#.#/#-C4#j#(s#X#k#0ECk#1G#k#2E#k#3E#k#4G#k#5E#US)JnC#$##Cs#E#%#9#DnC#$##C##%#8#DZIHFJs#AS#s#?nC#$##C$#%###DnC#$##C##%#s#1#DnC#$##C##%#s#,#DnC#$##C##%#s#%#DnS&%EG$#*Cs#e#$%#.#/#-C#4j#(-#UNGk#6E#US5JnC#$##C.#%#B#DUIOUKOnN$G$#*C##%$#+s#?#DnN$G$#*C%#%$#,##DnC#$##C'#%###DnC#$##C##%#s#:#DnC#$##C##%#s#3#DnS&%EG$#*Cs#s#$%#.#/#-C#Bj#7.#US,L+S%HFM#s#4#+S%LKI#$#[S)S%HFMs#\S#s#Z#$#,S%J,S$JnN$G$#*C##%$#+s#P#DnN$G$#*C%#%$#,##D#'#*Ps#LO#$#*Ps#FO#$#nS&%EG$#*C2#$%#.#/#VS<C#%JUS(#US=J/s#$s##8&$#US2&US>J/s#4s#3s#)%$#US?)US@J/s$7s$6s#=%$#[Q,MLKIHF[RJMLKIHF-C$#m#&#j#8E#&ECs$As$@#j#9G#&Gs$Xs$Fs$E#j#:E#&Es$Ys$Ks$J#j#;E#&Es$Zs$Ps$O#j#<E#&Es$[s$Us$T#j#*s$`#&s$as$\s$Zs$Y#j#=s$c##"). Qed.
#[local] Hint Rewrite shadow_split_okB_eqf : bceq.

(* [comment removed for export] *)
Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in
  if match find_containing k ms [KRWLAZY] sb sk sn with Some _ => true | None => shadow_split_ok k ms b n sb sk sn end
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].

Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_ofB bc b n in
  if match find_containingB bc ms [KRWLAZY] sb sk sn with Some _ => true | None => shadow_split_okB bc ms b n sb sk sn end
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].

Lemma shadow_factsB_eqf : forall fk, shadow_factsB (mkbc fk) = shadow_facts fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.amap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_factsB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_facts); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_split_ok); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_ofB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.find_containingB); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.mkind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.KRWLAZY); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KWr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KZero); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.find_containing); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.find_containingB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_ofB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_split_okB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_split_okB_eqf)|] [|@n; @b; @sn; @sk; @sb; @ms; @x; @a; @p; @off; @kinds; @o; @x1; @x0; @fk|] "#$-#,#L#3#$###%#<#9#&#8#2#*#D#'#C#0#4#6#)#:#+#@#(#H#I#=#B#>#A#F#E#G#J#K#L#M#N#5#;#/#?#7#1)#F$#G&#H$#I&#J)#K(%P%Kk#$C$k#%C##EUQ#URE#DVQ#EVRDE#FWQ#DEWRFDEk#&CHk#'J#k#(C#k#$C#k#%C#k#)3#US$IVGCJ#NWS*#FD#S%US+S&&S&S-#ZS,%L#DEFZNLS#S'DEFnM$K$#*H$#%$#+O##VS.DEVS/#FVS0$FUS+P&P$#&P&#nH#$##s#%)#%###%nG%CJ$#,s#&D#$%#(#'#nG%3C$#*s#'1#$%#,#&#WS(NFDZS)S%L0DEF[S$S%LS#S'DEFnM$K$#*H$#%$#+O##nH#$##s#,##%#*#,nG%CJ$#,s#-D#$%#(#'#nG%:C$#*s#.(#$%#,#&#$s#/*#j#%>#VG=Ck#$C#k#%C#US(IVEFDnM$K$#*H<#%$#+O#.nH#$##s#7##%#5#7nG%CJ$#,s#8D#$%#(#'#nG%s#%C$#*s#9&#$%#,#&#$s#:#.j#,*#%S&UMKk#$C#k#-J#k#%C#k#.'#k#)s#A#US)IYNLs#+DEFnM$K$#*H##%$#+O#=nH#$##s#F##%#s#$#s#&nG%CJ$#,s#GD#$%#(#'#nG%s#4C$#*s#HB#$%#,#&#$s#I#=j#/*#WS(IDEZS)LS#s#3DEF[S$LS#S'NDEFnM$K$#*H$#%$#+O##nH#$##s#O##%#s#-#s#/nG%CJ$#,s#PD#$%#(#'#nG%s#=C$#*s#Q(#$%#,#&#VS1s#R##IUS,#US2I'65.&$#US*&US3I's#(s#'@%$#US4)US5I's#Js#Is#.%$#XQ,FDEXRIFDE$s#_$#m#&#j#0C#(Cs#bs#Ws#V#j#1C#(Cs#bs#\s#[#j#*s#d#(s#es#cs#as#`#j#2s#g##"). Qed.
#[local] Hint Rewrite shadow_factsB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_twins (k : list kentry) (sb : expr) (sk : Z) (sn : expr) (vis : list (expr * expr)) : list kentry :=
  if flat_x k sb sk sn then
    flat_map (fun p => let '(pb, pk, pn) := shadow_of k (fst p) (snd p) in
                       if flat_x k pb pk pn then [KDisj (SA sb sk) sn (SA pb pk) pn] else []) vis
  else [].

Definition shadow_twinsB (bc : bctx) (sb : expr) (sk : Z) (sn : expr) (vis : list (expr * expr)) : list kentry :=
  if flat_xB bc sb sk sn then
    flat_map (fun p => let '(pb, pk, pn) := shadow_ofB bc (fst p) (snd p) in
                       if flat_xB bc pb pk pn then [KDisj (SA sb sk) sn (SA pb pk) pn] else []) vis
  else [].

Lemma shadow_twinsB_eqf : forall fk, shadow_twinsB (mkbc fk) = shadow_twins fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_twinsB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_twins); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_of); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.flat_xB); constr:(@Stdlib.Lists.List.flat_map); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KDisj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SA); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.flat_x); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.flat_xB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_ofB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_ofB_eqf)|] [|@vis; @sn; @sk; @n; @b; @p0; @pb; @pk; @x; @pn; @p; @off; @x2; @x1; @x0; @fk|] "#$*#.#H#4#$###%#'#5#E#6#2#&#7#9#(#;#=#1#-#,#+#B#*#A#)#F#:#?#@#D#G#H#I#J#8#>#3#C#<*#C$#D'#:'#E(#*%#F%#G&URK'CCUR#k#$#%k#%C#k#&H##EUM#UNE#DVM#EVNDE#FWM#DEWNFDE#LXM#FDEXNLFDE'CH'#Ck#'C#k#(C#UPG#OXQ#GLFWS,CCEWS-CCEVD$##S#XQ#DEF(S$S%(DEXS&$S'#FUS.KWS(K$#nI#$##s#%(#%###$nJ%CH$#)s#&D#$%#*#+#nJ%5C$#,s#',#$%#)#-#j#.s#'#$s#(K#DnI#$##s#*2#%###)%OGLFWPS)32%S#DEFnI#$##s#.##%#,#-nJ%CH$#)s#/D#$%#*#+#nJ%>C$#,s#0&#$%#)#-#j#.s#0#$s#1K#DnI#$##s#3*#%###2)s#4,#j#.@#k#'CIk#/H#k#(C#US*GWEGLFWODEFnI#$##s#<##%#:#;nJ%CH$#)s#=D#$%#*#+#nJ%s#,C$#,s#>4#$%#)#-#j#.s#>#$s#?K#DnI#$##s#A)#%###@)s#B#1j#(-#%GLFDWPOs#,s#+%S$DEF(S%S'XS&#S)s#)FWS(K#s#(nI#$##s#J&#%###s#)nJ%CH$#)s#KD#$%#*#+#nJ%s#:C$#,s#L)#$%#)#-#j#.s#L#$s#MK#EnI#$##s#O-#%###s#.VS/s#P##GUQ#US0GZS+>=3&$#US1&US2GZS+s#Bs#As#$%$#YM)LFDEYNGLFDE)s#Z$#m#&#j#0s#Z#&s#[s#]s#Ms#L#j#1C#&Cs#\s#Rs#Q#j#2H#&Hs#]s#Ws#V#j#,C#&Cs#^s#\s#[#j#3s#d##"). Qed.
#[local] Hint Rewrite shadow_twinsB_eqf : bceq.

Definition vis_twins (k : list kentry) (b n : expr) (vis : list (expr * expr)) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in shadow_twins k sb sk sn vis.
Definition vis_twinsB (bc : bctx) (b n : expr) (vis : list (expr * expr)) : list kentry :=
  let '(sb, sk, sn) := shadow_ofB bc b n in shadow_twinsB bc sb sk sn vis.
Lemma vis_twinsB_eqf : forall fk, vis_twinsB (mkbc fk) = vis_twins fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.vis_twinsB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.vis_twins); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_twins); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_ofB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_of); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_ofB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_twinsB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.shadow_twinsB_eqf)|] [|@vis; @n; @sn; @sk; @sb; @p; @x; @l; @b; @x1; @x0; @fk|] "##`#,#=#2#$###%#&#3#8#4#6#'#9#<#/#;#(#7#0#+#*#=#>#?#@#5#:#1'#:$#(%#;&#<(UOS#$CCUO#k#$#%k#%C##EUJ#UKE#DVJ#EVKDE#FWJ#DEWKFDEk#&C-k#'I#k#(C#UMG$CI#LWP#GFXLDEFQnH%CI$#)8D#$%#(#'#nH%'C$#*9%#$%#)#&#WNLGFYMS$DEFQnH%CI$#)<D#$%#(#'#nH%+C$#*=%#$%#)#&#%>'#j#+/#$.Ck#%C#k#,C#UNGVEGFnH%3C$#*s#%##$%#)#&+%s#&#+j#)'#WNGFDYMS%DEFLnH%CI$#)s#*D#$%#(#'#nH%9C$#*s#+%#$%#)#&#VS&s#,##GUP#US'GZR0/+&$#US(&US)GZRs##B6%$#XJ)FDEXKGFDE%s#6$#m#&#j#-s#6#&s#7s#9s#-s#,#j#.C#&Cs#8s#2s#1#j#*C#&Cs#9s#7s#6#j#/s#>##"). Qed.
#[local] Hint Rewrite vis_twinsB_eqf : bceq.

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
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts k0 (a_maps cs) b n ++ vis_twins k0 b n (a_vis cs) ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs))
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
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p)
                           && ranges_apart_xB bc bb bk n pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_vis cs)
      (* [comment removed for export] *)
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_ghost cs)
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_factsB bc (a_maps cs) b n ++ vis_twinsB bc b n (a_vis cs) ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs))
  else None
  | None => None
  end.

Lemma vis_add_eq : forall cs b n k, vis_add cs b n k = vis_add_ref cs b n k.
Proof. intros. unfold vis_add, vis_add_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?shadow_factsB_eqf, ?vis_twinsB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf. reflexivity. Qed.


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
Definition node_casedisj (cs : acs) (b1 b2 : expr) : option (acs * acs) :=
  let k := kn cs in
  match find_disj k b1 b2 with
  | Some (c1, o1, n1, c2, o2, n2) =>
      match flat_x k c1 o1 n1, flat_x k c2 o2 n2, disj_side_fact k c1 o1 n1 c2 o2, disj_side_fact k c2 o2 n2 c1 o1 with
      | true, true, Some K1, Some K2 => Some (add_kn cs [K1], add_kn cs [K2])
      | _, _, _, _ => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint gaps_cut (gs : list (Z * Z)) (xlo xhi : Z) : list (Z * Z) :=
  match gs with
  | [] => []
  | (a, b) :: r =>
      (if Z.ltb xhi a || Z.ltb b xlo then [(a, b)]
       else (if Z.ltb a xlo then [(a, xlo - 1)] else []) ++ (if Z.ltb xhi b then [(xhi + 1, b)] else []))
      ++ gaps_cut r xlo xhi
  end.
(* [comment removed for export] *)
Definition zcdivp (a b : Z) : Z := - ((- a) / b).
(* [comment removed for export] *)
Definition gap_excl1 (k : list kentry) (b : expr) (sc : Z) (K : kentry) : list (Z * Z) :=
  match K with
  | KDisj (SA b1 o1) n1 (SA b2 o2) n2 =>
      let one (cb : expr) (co : Z) (cn : expr) (pb : expr) (po : Z) (pn : expr) :=
        if (expr_eqb cb b && Z.eqb co 0)%bool then
          match pb, pn, xlo k cn with
          | ELit L, ELit M, Some nlo =>
              let P := zlit64 L + po in let Mz := zlit64 M in
              if (Z.leb 0 nlo && Z.leb 0 Mz)%bool then [((P - nlo) / sc + 1, zcdivp (P + Mz) sc - 1)] else []
          | _, _, _ => []
          end
        else [] in
      one b1 o1 n1 b2 o2 n2 ++ one b2 o2 n2 b1 o1 n1
  | _ => []
  end.
(* [comment removed for export] *)
Definition gaps_of (cs : acs) (v : nat) (sc : Z) : option (list (Z * Z)) :=
  let k := kn cs in let b := escale sc (EVar v) in
  if negb (Z.ltb 0 sc && Z.ltb sc two64)%bool then None else
  match find_range (facts_of k) (EVar v) with
  | Some (lo, hi) =>
      if negb (Z.leb 0 lo && Z.ltb (sc * hi) two64)%bool then None else   (* [comment removed for export] *)
      let excl := flat_map (gap_excl1 k b sc) k in
      Some (fold_left (fun gs x => gaps_cut gs (fst x) (snd x)) excl [(lo, hi)])
  | None => None
  end.
Definition gap_child (cs : acs) (v : nat) (g : Z * Z) : acs := set_kn cs (KRange (EVar v) (fst g) (snd g) :: kn cs).
Definition node_casegaps (cs : acs) (v : nat) (sc : Z) : option (list acs) :=
  match gaps_of cs v sc with
  | Some gaps => Some (map (gap_child cs v) gaps)
  | None => None
  end.

(* [comment removed for export] *)
Definition gaps_lohi (gaps : list (Z * Z)) : option (Z * Z) :=
  match gaps with
  | [] => None
  | g :: gs => Some (fold_left (fun a x => Z.min a (fst x)) gs (fst g), fold_left (fun a x => Z.max a (snd x)) gs (snd g))
  end.
Definition node_rangegaps (cs : acs) (v : nat) (sc : Z) : option acs :=
  match gaps_of cs v sc with
  | Some gaps =>
      match gaps_lohi gaps with
      | Some g => Some (gap_child cs v g)
      | None => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition node_shdisj_ref (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_of k b1 n1 in let '(sb2, sk2, sn2) := shadow_of k b2 n2 in
  if (Z.leb 3 (ealign k b1) && Z.leb 3 (ealign k n1) && Z.leb 3 (ealign k b2) && Z.leb 3 (ealign k n2)
      && flat_x k c1 o1 n1 && flat_x k c2 o2 n2 && flat_x k sb1 sk1 sn1 && flat_x k sb2 sk2 sn2
      && match xhi k b1, xhi k n1, xhi k b2, xhi k n2 with
         | Some h1, Some m1, Some h2, Some m2 => Z.leb (h1 + m1) (2 ^ 47) && Z.leb (h2 + m2) (2 ^ 47)
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
         | Some h1, Some m1, Some h2, Some m2 => Z.leb (h1 + m1) (2 ^ 47) && Z.leb (h2 + m2) (2 ^ 47)
         | _, _, _, _ => false end
      && ranges_apart_xB bc c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.

Lemma node_shdisj_eq : forall cs b1 n1 b2 n2, node_shdisj cs b1 n1 b2 n2 = node_shdisj_ref cs b1 n1 b2 n2.
Proof. intros. unfold node_shdisj, node_shdisj_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf. reflexivity. Qed.


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
  | m :: rest => (negb (is_fog m) && xinside_c k b off len (am_base m) 0 (am_len m)) || inside_maps k rest b off len   (* [comment removed for export] *)
  end.

Local Open Scope lzb_scope.
Fixpoint inside_mapsB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinside_cB bc b off len (am_base m) 0 (am_len m)) || inside_mapsB bc rest b off len
  end.
Local Close Scope lzb_scope.

Lemma inside_mapsB_eqf : forall fk, inside_mapsB (mkbc fk) = inside_maps fk.
Proof.
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.amap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.inside_mapsB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.inside_maps); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.orb); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Datatypes.negb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.is_fog); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xinside_cB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.am_base); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.am_len); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xinside_c); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.xinside_cB_eqf); constr:(@Corelib.Init.Datatypes.cons)|] [|@len; @off; @b; @ms; @cn; @ck; @cb; @n; @IH; @rest; @m; @fk|] "#$,#/#I###$#%#6#8#&#7#-#5#9#;#(#G#'#)#.#I#2#+#>#,#D#C#F#H#E#@#3#?#*#J#K#<#:#=#B#A#4*#D$#-(#E&#,(#F%#G%#H(US$S.US$Kk#$FGk#%I#k#&F##CUL#UMC#DVL#CVMDC#EWL#DCWMEDC#HXL#EDCXMHEDC#S%&#HEDC$S%HEDC%G$#k#$F#k#%I#k#&F#j#'9#US/K$S0#EDCVS&G#j#$F#j#%I#j#&F##S'&#HEDC$S'HEDC%G$#k#$F#k#%I#k#&F#$JPEDCUS(QUS)##RUS*QUS+Q[S,%HED$O#''#(#C[S#RHED'O&'*#$RNHED($#%G'#j#&G#k#(FGk#)I#k#*F#k#+F#k#%I#k#&F#US#JZCHED4O3'7#(#/%G#/j#&(#US(NUS)#US*NUS+N[S#JEDC$O#'&#(#s##VS&G##JUS,#US1JZS-43.&$#&&PEDCWHEDCZS-Gs#+=%$#WS2KNP&*#EDC$J$EDC%G$#m#'#j#$F#j#%I#j#&F#j#,s#5#j#-s#Z#j#.K#\S3Ks#Es#?#HEDCj#$F#)FGs#Ps#O#j#%I#)Is#_s#Us#T#j#&F#)Fs#`s#Zs#Y#j#'s#c#)s#ds#as#_s#^#j#/s#f##"). Qed.
#[local] Hint Rewrite inside_mapsB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_pg_early : expr := Eval vm_compute in eadd (escale 32768 (EVar 0%nat)) (escale 4096 (EVar 6%nat)).
Definition e_sp0_early : expr := Eval vm_compute in eadd e_pg_early (escale 16 (EVar 10%nat)).
(* [comment removed for export] *)
Definition e_stklen_early : expr := Eval vm_compute in esub (ELit (0x800000000000 + 8388608)) e_pg_early.
(* [comment removed for export] *)
Definition lit_entries (ms : list amap) : list (Z * Z) :=
  flat_map (fun m => if is_fog m then [] else
                     match am_base m, am_len m with
                     | ELit b, ELit n => [(zlit64 b, zlit64 n)]
                     | _, _ => []
                     end) ms.
(* [comment removed for export] *)
Fixpoint covers (fuel : nat) (parts : list (Z * Z)) (cur hi : Z) : bool :=
  if Z.leb hi cur then true else
  match fuel with
  | O => false
  | Datatypes.S f =>
      match List.find (fun p => Z.leb (fst p) cur && Z.ltb cur (fst p + snd p)) parts with
      | Some p => covers f parts (fst p + snd p) hi
      | None => false
      end
  end.
(* [comment removed for export] *)

Definition stack_side_x (k : list kentry) (b : expr) (off : Z) : bool :=
  lin_ge0 k [(b, off + 8388608)] [(e_sp0_early, 0)].

Definition safe_range (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhi k len, base_range k b with
    | Some lh, Some (lo, hi) =>
        (stack_side_x k b off && Z.leb 0 (lo + off) && Z.leb (hi + off + lh) two64)   (* [comment removed for export] *)
        || (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
        (* [comment removed for export] *)
        || (Z.leb (shadow_off A - 4096) (lo + off) && Z.ltb (hi + off) KHI && Z.leb (hi + off + lh) KHI
            && covers (Datatypes.S (length ms)) (lit_entries ms) (shadow_off A - 4096) KHI)
    | _, _ => false
    end) || inside_maps k ms b off len)%bool.

(* [comment removed for export] *)
Definition stack_side_xB (bc : bctx) (b : expr) (off : Z) : bool :=
  lin_ge0B bc [(b, off + 8388608)] [(e_sp0_early, 0)].
Lemma stack_side_xB_eqf : forall fk, stack_side_xB (mkbc fk) = stack_side_x fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.stack_side_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.stack_side_x); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xterms); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin_ge0); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.e_sp0_early); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.lin_ge0B_eqf)|] [|@off; @neg; @pos; @b; @x0; @x; @fk|] "##c#'#A###.#/#$#%#-#0#2#5#4#:#6#,#*#+#8#=#;#>#?#@#&#A#B#C#3#<#1#9#7'#=$#>$#?'#@&UPQk#$DE$CUI#UJC$FVI#CVJFCk#%LEk#&L#UKGVRHD#S#############################################US$#VMF#%HDG#US%=&>$#%HDS&S'&@#%VC%#WKS(&$WNE$#j#'s#&#VMC-%HDF#&s#'#,WKG#*VS)E#$GUS*#US+GZS,s#/s#.+&$#WI&FCWJGFCWNE$#m#&#j#(D#YODEs#8s#7#j#)H#YOHs#?s#=s#<#j#*s#A##"). Qed.
#[local] Hint Rewrite stack_side_xB_eqf : bceq.

Local Open Scope lzb_scope.
Definition safe_rangeB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhiB bc len, base_rangeB bc b with
    | Some lh, Some (lo, hi) =>
        (stack_side_xB bc b off && Z.leb 0 (lo + off) && Z.leb (hi + off + lh) two64)   (* [comment removed for export] *)
        || (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
        || (Z.leb (shadow_off A - 4096) (lo + off) && Z.ltb (hi + off) KHI && Z.leb (hi + off + lh) KHI
            && covers (Datatypes.S (length ms)) (lit_entries ms) (shadow_off A - 4096) KHI)   (* [comment removed for export] *)
    | _, _ => false
    end) || inside_mapsB bc ms b off len)%lzb.
Local Close Scope lzb_scope.

Lemma safe_rangeB_eqf : forall fk, safe_rangeB (mkbc fk) = safe_range fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.amap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.safe_rangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.safe_range); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.stack_side_x); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.two64); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.img_lo); constr:(A); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.img_hi); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.shadow_off); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.KHI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.covers); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.lit_entries); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.inside_mapsB); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.xhi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.base_range); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.inside_maps); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.base_rangeB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.xhiB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.inside_mapsB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.stack_side_xB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.stack_side_xB_eqf)|] [|@len; @off; @b; @p; @lo; @hi; @x; @lh; @ms; @e; @o; @x2; @x1; @x0; @fk|] "#$v#-#^#6#5###'#C#$#T#&#%#4#E#(#)#O#7#9#>#*#3#;#G#+#W#X#Z#0#=#?#A#D#N#R#Q#S#P#U#1#F#H#J#M#K#I#,#[#\#]#^#_#`#@#L#Y#8#B#V#<#:#2,#U%#V$#W%#X$#Y%#Z%#[&#\)#](US,S7US,S%k#$LCk#%D#k#&L#&EUQ#URE&HVQ#EVRHE&KWQ#HEWRKHE&JXQ#KHEXRJKHEk#%DCk#&L#US&F&NVS-#HVS#DD&OVS.#FVFS$O'HO#S/#nC#$##C%#%###G'EO'#J##S0nC#$##C&#%###GUS8S'##*US9S'#(#nC#$##C%#%###GnC#$##C(#%#M##US:S'$S;$#$#$#$#$#$#$#$#$#$#$#US<#VS=0###>VS1<PnC#$##C$#%###G#=PnC#$##C$#%###GVS2S%S(US3#US4S(XS5$#+PnC#$##C'#%###GnC#$##C<#%#M##nS#%DD$#'CE#$%#(#)#nI$s#.$#*Cs#,#%$#'##GnI$D$#*Cs#0#%$#+##GYS6s#2FJKHnC#$##C$#%#M##VS)NHVS*OFWS&S>S$O%#s#0%#s#-%s#+s#)($#%98%#7%#3(&#nS#%DD$#'CE#$%#(#)#nI$s#>$#*C-#%$#'##GnI$D$#*C/#%$#+##GYS+NFJKH($#)C3#j#&s#G#k#,s#Ys#VUS+FnC#$##C4#%#s#A#GnC#$##C##%#s#>#GnC#$##C##%#M#s#9nC#$##C##%#M#@nS#%DD$#'CE#$%#(#)#nI$s#K$#*Cs#I#%$#'##GnI$D$#*Cs#M#%$#+##GXEFJKHnC#$##C$#%#M##)C#0j#&.#UIDk#-L#US)FUEHnI$D$#*C##%$#+,#GnC#$##C##%#M#8)C#8j#.(#UIs#Yk#-L#US*FUHFnI$s#]$#*C##%$#'5#GnI$D$#*Cs#.#%$#+##GnC#$##C##%#M#A)C#Aj#.)#VS)FEVS*NJWS&S(ON'HN#S/#%%#'EN'#J##S0%&##s#a)#&s#`%$#(&##s#Q-VS1+P%$##,P%$#VS2S%S$US3#US4S$XS5$#s#YP%'#(-#nS#%DD$#'CE#$%#(#)#nI$s#|$#*C;#%$#'##GnI$D$#*C=#%$#+##GYS+FJKHE($#VS?C#&FUS.#US@F*s#,s#+s#%&$#US-&USAF*s#7s#6s#1%$#US6)USBF*s#Hs#Gs#<%$#USC,USDF*s$5s$4s#L%$#YQ/JKHEYRFJKHE)C$#m#&#j#/L#+LCs$>s$=#j#0D#+Ds$Ms$Cs$B#j#1L#+Ls$Ns$Hs$G#j#*s$Q#+s$Rs$Os$Ms$L#j#2s$T##"). Qed.
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

Local Open Scope lzb_scope.
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
Local Close Scope lzb_scope.

Lemma grant_keep_bB_eqf : forall fk, grant_keep_bB (mkbc fk) = grant_keep_b fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.amap); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.grant_keep_bB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.grant_keep_b); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.safe_range); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.Arith.PeanoNat.Nat.leb); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.saddr); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.safe_rangeB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.safe_rangeB_eqf)|] [|@K; @len; @off; @b; @ms; @a; @o; @w; @v; @l; @k; @lo; @hi; @e; @m; @n; @a1; @n1; @a2; @n2; @c; @k0; @x0; @x; @fk|] "##d#,#D#3#$###%#C#B#0#*#&#)#4#6#(#/#8#:#+#;#1#2#9#?#=#A#@#'#D#E#F#7#>#5#<'#A$#2(#B$#C%UPIUPS&k#$IC%EUM#UNE%DVM#EVNDEk#%QCk#&S'#k#'Q#k#(-#URF#S(##############VS)K#US*KUS+#XOJDE#&&#nH#$#)CF#$%#'#*#XS,LDEFnH#$#)CD#$%#'#*#XOJDEKnH#$#)CF#$%#'#*#nI#$#$CD#-&#)#+#,'%#)#-%&#)#-#.#%#/#0G%#1#2G&#1#/#0G%#)#3%'#4#5#6#7G&#)#-#8#%#)#-%$S#JDE+&.#nH#$#)CF#$%#'#*#$JLDEFnH#$#)CD#$%#'#*#$S#JDEKnH#$#)CF#$%#'#*#nI#$#$CD#-&#)#+#,'%#)#-%&#)#-#9#%#/#0G%#1#2G&#1#/#0G%#)#3%'#4#5#6#7G&#)#-#8#%#)#-%WS$C+#j#'@#$JLDE5&8#nH#$#)CF#$%#'#*#$LODEFnH#$#)CD#$%#'#*#$JLDEKnH#$#)CF#$%#'#*#nI#$#$CE#-&#)#+#,'%#)#-%&#)#-#9#%#/#0G%#1#2G&#1#/#0G%#)#3%'#4#5#6#7G&#)#-#8#%#)#-%VS-C#%FUS.#US/FZS0s#-s#,/&$#WM&DEWNFDEWS$C$#m#&#j#:I#YS%ICs#8s#7#j#;s#?#YS%s#@s#?s#=s#<#j#<s#B##"). Qed.
#[local] Hint Rewrite grant_keep_bB_eqf : bceq.



Definition kn_grant_filter (k : list kentry) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_b k ms) k).

Definition kn_grant_filterB (bc : bctx) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_bB bc ms) (bc_fk bc)).

Lemma kn_grant_filterB_eqf : forall fk, kn_grant_filterB (mkbc fk) = kn_grant_filter fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.amap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kn_grant_filterB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kn_grant_filter); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.grant_keep_b); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kimg_clip); constr:(@Stdlib.Lists.List.filter); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk_mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.grant_keep_bB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.grant_keep_bB_eqf)|] [|@K; @ms; @b; @l; @x; @fk|] "##K#&#8#$###*#2#%#)#-#/#6#0#,#1#7#8#9#:#+#5#4#.#3'#4&#5$#6$#7&UHEUHM%DUI#UJDk#$ENk#%'#UFCUDC%GUK##E%#$#VFGC#E#G$#&2&#j#&-##E'D$#&6#'j#'7#VFCD#E#C$#VO;#%CUK#UPCZL?C*&$#UQ&URCZL<;1%$#VI)DVJCD&s#%$#m#&#j#(s#&#YS#s#'s#(s#%s#$#j#)s#)##"). Qed.
#[local] Hint Rewrite kn_grant_filterB_eqf : bceq.

(* [comment removed for export] *)
Definition kn_grant_filterM (k : list kentry) (ms : list amap) : list kentry := kn_grant_filterB (mkbc k) ms.
Lemma kn_grant_filterM_eq : kn_grant_filterM = kn_grant_filter.
Proof. apply functional_extensionality; intros k. unfold kn_grant_filterM. apply kn_grant_filterB_eqf. Qed.



(* [comment removed for export] *)
Definition gap_ok (cs : acs) (nhi : Z) : bool :=
  let cnt := Z.of_nat (n_res A + length (a_maps cs))%nat in
  Z.leb (FLOOR + nhi + a_totsz cs + cnt * (nhi + 4095)) CEIL.

Definition budget_ok (cs : acs) (extra : Z) : bool :=
  Z.leb (a_eager cs + a_abytes cs + extra) LIMIT.

(* [comment removed for export] *)
Definition kdisj_new (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else [KDisj (SA (am_base m) 0) (am_len m) (SA nb 0) ne]) ms.
Definition kdisj_fixed (nb : expr) (ne : expr) : list kentry :=
  [KDisj (SA nb 0) ne (SA (ELit (img_lo A)) 0) (ELit (img_hi A - img_lo A));
   (* [comment removed for export] *)
   KDisj (SA nb 0) ne (SA e_pg_early (- 8388608)) (ELit (2 ^ 48));
   (* [comment removed for export] *)
   KDisj (SA nb 0) ne (SA e_sp0_early (- 8388608)) (ELit (2 ^ 48))].

Definition SHLO : Z := shadow_off A - 4096.
Definition kdisj_shadow (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  if (Z.ltb 0 SHLO && Z.ltb SHLO KHI && covers (Datatypes.S (length ms)) (lit_entries ms) SHLO KHI)%bool
  then [KDisj (SA nb 0) ne (SA (ELit SHLO) 0) (ELit (KHI - SHLO))] else [].

(* [comment removed for export] *)
Definition with_maps0 (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs).

(* [comment removed for export] *)
Definition add_entry (cs : acs) (sr : list expr) (k' : list kentry) (nx' : nat)
           (m : amap) (nhi : Z) (eager : bool) (ylo' : Z) : acs :=
  ACS (mk_ss (pc cs + 4) sr k' nx')
      (m :: a_maps cs) (a_totsz cs + nhi) ylo'
      (if eager then a_eager cs + nhi else a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (VNew (am_kind m) (am_base m) (am_len m) :: a_vmops cs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition null_kend (base ne : expr) (nlo : Z) : list kentry :=
  match ne with
  | ELit _ => []
  | _ => [KRange (eadd base ne) (4096 + nlo) CEILMAX]
  end.

Definition mmap_null (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && no_holes (a_maps cs))%bool then     (* [comment removed for export] *)
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        (* [comment removed for export] *)
        let kfacts := KRange (EVar v) 1 ((CEILMAX - nlo) / 4096) :: null_kend base ne nlo
                      ++ kdisj_fixed base ne ++ kdisj_shadow (a_maps cs) base ne ++ kdisj_new (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filterM (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs - 2 * nhi) in
        if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition fixed_args (cs : acs) (top : Z) (inside : bool) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && (inside || Z.leb (img_hi A) alo) && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
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
  let ksh := if mkind_eqb kind KRWLAZY then flat_map (fun p => shadow_facts k [m] (fst p) (snd p)) (a_vis cs) else [] in
  let k' := ksh ++ kn_grant_filterM k ms0 in
  let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
  if visible then vis_add cs1 a ne (kmem ++ kn cs1) else Some cs1.

Definition mmap_fixed_free (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  match fixed_args cs KHI false with
  | Some (b, off, ne, nlo, nhi) =>
      if (no_fog (a_maps cs)
          && forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
          && (negb eager || budget_ok cs nhi)
          && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
      then mmap_fixed_grant cs (a_maps cs) b off ne nhi kind eager visible
      else None
  | None =>
      (* [comment removed for export] *)
      match fixed_args cs CEIL false with
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
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kn_rezeroB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kn_rezero); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sprep); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bp); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.Lists.List.filter); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.mk_sprep); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk_mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mk_sprepB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bpB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kentry_apart_bpB_eqf)|] [|@un; @uk; @K; @ub; @sp; @a; @w; @v; @n; @k; @lo; @hi; @e; @m; @a1; @n1; @a2; @n2; @c; @k0; @b; @k1; @b1; @s; @l; @x1; @x0; @x; @fk|] "##o#,#C#>#0###&#2#*#)#(#$#9#'#3#4#6#%#+#@#8#:#=#?#/#A#B#C#D#E#5#<#;#7#1)#>$#?&#@&#5)#A)#B(US(Dk#$G#k#%N##EUO#UPE#KVO#EVPKE#QWO#KEWPQKEk#&DLk#$G#k#%N#k#'G#k#(S$#US%F#RXS&#HIJYM#HIJFnD#$#&LE#-&#)#*#+#%#)#,C&#)#,#-#%#.#/C%#0#1C&#0#.#/C%#)#,C'#2#3#4#5C&#)#,#6#%#)#,Cj#&D##MUS'#$D%#XS#RHIJ&R#HIJFnD#$#&LE#-&#)#*#+#%#)#,C&#)#,#7#%#.#/C%#0#1C&#0#.#/C%#)#,C'#2#3#4#5C&#)#,#6#%#)#,Cj#&D#$D#M%A(#j#82#k#3GS$k#9N#k#:G#US#FWMHIJ&R#HIJFnD#$#&LE#-&#)#*#+#%#)#,C&#)#,#-#%#.#/C%#0#1C&#0#.#/C%#)#,C'#2#3#4#5C&#)#,#6#%#)#,Cj#&D#$D#3%s#,#.j#;*#nD#$#&LE#-&#)#*#+3%#)#,C&#)#,#-3%#.#/C%#0#1C&#0#.#/C%#)#,C'#2#3#4#5C&#)#,#63%#)#,Cj#&D#$D#E%s#1#3j#<s#2#XS#HIJM&H#IJMFnD#$#&LE#-&#)#*#+#%#)#,C&#)#,#7#%#.#/C%#0#1C&#0#.#/C%#)#,C'#2#3#4#5C&#)#,#6#%#)#,Cj#&D#$D#FVS)s#8##FUS'#US*F's#<F,&$#US&&US+F'<;4%$#US,)US-F's#2s#1B%$#XO,QKEXPFQKE%s#E$#m#&#j#=G#(Gs#Hs#>s#=#j#>N#(Ns#Is#Cs#B#j#?G#(Gs#Js#Hs#G#j#@s#M##"). Qed.
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
  match fixed_args cs CEILMAX true with   (* [comment removed for export] *)
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
  match fixed_args cs CEILMAX true with
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
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                       (VFixIn (match arm with ArmF => true | _ => false end) (match arm with ArmG => true | _ => false end) (reg cs 10) ne :: a_vmops cs) in
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
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                       (VFixIn (match arm with ArmF => true | _ => false end) (match arm with ArmG => true | _ => false end) (reg cs 10) ne :: a_vmops cs) in
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
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs).
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
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs).

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
Definition node_mmap2 (cs : acs) : option (acs * acs) :=
  match mmap_gate cs with
  | Some (prot, flags, isnull) =>
      let g := if isnull then
                 match prot, flags with
                 | 3, 0x22 => mmap_null cs KRW true true               (* [comment removed for export] *)
                 | 3, 0x4022 => mmap_null cs KRWLAZY false true        (* [comment removed for export] *)
                 | 0, 0x22 => mmap_null cs KNONE false false           (* [comment removed for export] *)
                 | 0, 0x4022 => mmap_null cs KNONELAZY false false     (* [comment removed for export] *)
                 | _, _ => None
                 end
               else
                 match prot, flags with
                 | 3, 0x4032 => mmap_fixed_free cs KRWLAZY false false  (* [comment removed for export] *)
                 | 3, 0x32 => mmap_fixed_free cs KRW true true          (* [comment removed for export] *)
                 | 0, 0x4032 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | 0, 0x32 => mmap_fixed_free cs KNONE false false      (* [comment removed for export] *)
                 (* [comment removed for export] *)
                 | 3, 0x104022 => mmap_fixed_free cs KRWLAZY false false   (* [comment removed for export] *)
                 | 0, 0x104022 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | _, _ => None
                 end in
      match g with Some csG => Some (refuse cs, csG) | None => None end
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint opt_all {T : Type} (l : list (option T)) : option (list T) :=
  match l with
  | [] => Some []
  | Some x :: r => match opt_all r with Some r' => Some (x :: r') | None => None end
  | None :: _ => None
  end.
(* [comment removed for export] *)
Definition node_mmapgaps (cs : acs) : option (list acs) :=
  match mmap_gate cs, mmap_len cs with
  | Some (3, 0x22, true), Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && budget_ok cs nhi
          && no_holes (a_maps cs))%bool then
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let kfacts := KRange (EVar v) 1 ((CEILMAX - nlo) / 4096) :: null_kend base ne nlo
                      ++ kdisj_fixed base ne ++ kdisj_shadow (a_maps cs) base ne ++ kdisj_new (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filterM (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne KRW) nhi true (a_ylo cs - 2 * nhi) in
        match gaps_of cs1 v 4096 with
        | Some gaps => opt_all (map (fun g => let csg := gap_child cs1 v g in vis_add csg base ne (kmem ++ kn csg)) gaps)
        | None => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
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
          match fixed_in_args cs arm, mmap_fixed_in cs arm with
          | Some (b, off, ne, nlo, nhi, m), Some csO => Some (refuse cs, csO, mmap_destroyed hole cs b off ne m)
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_mmapin1 (cs : acs) : option acs :=
  match mmap_gate cs with
  | Some (prot, flags, false) =>
      let arm := match prot, flags with
                 | 3, 0x32 => Some ArmE
                 | 3, 0x4032 => Some ArmF
                 | 0, 0x32 => Some ArmG
                 | _, _ => None
                 end in
      match arm with
      | Some arm => mmap_fixed_in cs arm
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_mprotect_ref (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs CEILMAX true with   (* [comment removed for export] *)
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      match find_containing k (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfill k b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (VProt (reg cs 10) ne :: a_vmops cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition node_mprotect (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs CEILMAX true with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match find_containingB bc (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfillB bc b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (VProt (reg cs 10) ne :: a_vmops cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
Lemma node_mprotect_eq : forall cs, node_mprotect cs = node_mprotect_ref cs.
Proof. intros. unfold node_mprotect, node_mprotect_ref. unfold ehi, elo. rewrite ?find_containingB_eqf, ?kn_unfillB_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Definition node_mprotect2 (cs : acs) : option (acs * acs) :=
  match node_mprotect cs with Some csG => Some (refuse cs, csG) | None => None end.

(* [comment removed for export] *)

Definition amap_match (k : list kentry) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqb k n (am_len m))%bool.

Local Open Scope lzb_scope.
Definition amap_matchB (bc : bctx) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqbB bc n (am_len m))%lzb.
Local Close Scope lzb_scope.

Lemma amap_matchB_eqf : forall fk, amap_matchB (mkbc fk) = amap_match fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.amap); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.amap_matchB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.amap_match); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.len_eqb); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.negb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.is_fog); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr_eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.am_base); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.am_len); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.len_eqbB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.len_eqbB_eqf)|] [|@m; @n; @b; @x1; @x0; @x; @fk|] "##W#(#>###0#$#.#%#&#1#3#/#5#8#7#:#9#;#<#6#+#,#'#>#?#@#4#2#=#-&#;$#<%#=(US$S%k#$KDk#%F##CUI#UJC#EVI#CVJEC#GWI#ECWJGECk#$FDk#%F#ULHUMEUN#UOEVPH#nD#$##D%#%###QUREVCG#nD#$##D%#%###Q$)'WLS&G&$$#WS#D&#j#&0#UMCUN#UOCVPG#$%#URCWLHE#$%#VS'D##HUS(#US)HZS*=</&$#XI&GECXJHGECWS#D$#m#&#j#'K#%KDs#&s#%#j#(F#%Fs#1s#+s#*#j#)F#%Fs#2s#0s#/#j#*s#5##"). Qed.
#[local] Hint Rewrite amap_matchB_eqf : bceq.



(* [comment removed for export] *)
Definition node_munmap_ref (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_x k pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_x k pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_match k b ne) (a_maps cs) && page_aligned k b && flat_x k bb bk ne
          && match xhi k b with Some hi => Z.leb (hi + nhi) 0x800000000000 | None => false end   (* [comment removed for export] *)
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in
                               Z.leb 3 (ealign k (fst p)) && Z.leb 3 (ealign k (snd p))
                               && xinside k pb pk (snd p) bb bk ne && kzero_x k k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in kn_unfill kk sb sk sn) gone (kn_unfill k bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_match k b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (VUnmap (reg cs 10) ne :: a_vmops cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_munmap (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_xB bc pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_xB bc pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_matchB bc b ne) (a_maps cs) && page_alignedB bc b && flat_xB bc bb bk ne
          && match xhiB bc b with Some hi => Z.leb (hi + nhi) 0x800000000000 | None => false end   (* [comment removed for export] *)
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in
                               Z.leb 3 (ealignB bc (fst p)) && Z.leb 3 (ealignB bc (snd p))
                               && xinsideB bc pb pk (snd p) bb bk ne && kzero_xB bc k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in kn_unfillM kk sb sk sn) gone (kn_unfillB bc bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_matchB bc b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (VUnmap (reg cs 10) ne :: a_vmops cs))
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
Definition brk_grow_admissible (cs : acs) (d : Z) : bool :=
  (brk_base_ok cs d && no_fog (a_maps cs) && budget_ok cs d)%bool.

(* [comment removed for export] *)
Definition brk_grow_blocked (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (brk_base_ok cs d
   && existsb (fun m => negb (is_fog m)
                        && lin_ge0 k [(am_base m, -1); (am_len m, 0)] [(b, 0)]      (* [comment removed for export] *)
                        && lin_ge0 k [(b, d - 1)] [(am_base m, 0)])               (* [comment removed for export] *)
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
Definition brk_range_facts (cs : acs) : list kentry :=
  match gaps_of cs 5%nat 4096 with
  | Some gaps => match gaps_lohi gaps with Some g => [KRange (EVar 5%nat) (fst g) (snd g)] | None => [] end
  | None => []
  end.

(* [comment removed for export] *)
Definition node_brk2 (cs : acs) : option (acs * acs) :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      if (brk_grow_admissible cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
        let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        let k' := kdisj_new (a_maps cs) b (ELit (d + 4096)) ++ kn_grant_filterM k (a_maps cs) in   (* [comment removed for export] *)
        let ss := a_ss cs in
        let csB0 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) (a_vmops cs) in
        (* [comment removed for export] *)
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) (brk_range_facts csB0 ++ k') (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) (a_vmops cs) in
        match vis_add csB b (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB) with
        | Some csB' => Some (csA, csB')
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
                 (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) true (a_vmops cs))
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
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs).

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
                     (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs))
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
          && Z.leb 3 (ealign k b) && Z.leb 3 (ealign k n) && flat_x k bb bk n && Z.leb (bh + nh) 0x800000000000
          && flat_x k sb sk sn && kzero_x k k sb sk sn)%bool
      then
        let k1 := kn_unfill k bb bk n in
        let k2 := kn_unfill k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs))
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
          && Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n && Z.leb (bh + nh) 0x800000000000
          && flat_xB bc sb sk sn && kzero_xB bc k sb sk sn)%bool
      then
        let k1 := kn_unfillB bc bb bk n in
        let k2 := kn_unfillM k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs))
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
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (EVar v) (a_fd cs) (a_tidset cs) (a_vmops cs))
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

Local Open Scope lzb_scope.
Fixpoint copy_factsB (bc : bctx) (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8eB bc sb sk with Some _ => true | None => match kread_bytesB bc 8 sb sk with Some _ => true | None => false end end)%lzb then
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
Local Close Scope lzb_scope.

Lemma copy_factsB_eqf' : forall fk fuel, copy_factsB (mkbc fk) fuel = copy_facts fuel fk.
Proof.
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.nat_ind); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.copy_factsB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.copy_facts); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kread8eB); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kread_bytesB); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.zbytes_le_to_Z); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.KWord); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupB); constr:(segs); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.sidecond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lres); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kread8e); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kread_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.know_lookup); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.know_lookupB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kread8eB_eqf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.kread_bytesB_eqf)|] [|@n; @dk; @db; @sk; @sb; @fuel; @x3; @x2; @x1; @x0; @x; @l; @e; @bs; @v; @rest; @scs; @s; @hints; @o; @off; @b; @acc; @sx; @rk; @rb; @IH; @f; @fk|] "#%`#0#^###8#C#:#$#'#&#(#9#%#+#)#?#K#;#=#I#,#4#5#*#V#Y#X#3#[#\#]#@#G#E#H#J#O#U#Z#-#N#M#/#.#^#_#`#6#A#>#<#P#L#7#D#Q#T#S#R#B#F#W6#P$#Q(#R$#S%#T%#U&#2*#;$#1%#2%#V%#W%#X%#Y&#Z&#[)#&$#\$#]$*S%3#k#$K#k#%K#k#&D#k#'K#k#(D#%L+#C,CL(&$#j#)S&#%G+#O,OGWQ*OCWROLC%IXQ#OGCXROIGC%HYQ#OLGCYROHLGC%JZQ#OILGCZROJILGC)ONHILGCVS/<#j#*K#$K>'&#j#+K#$K?,+#j#,D#$D@10#j#-K#$KA65#j#.D#$DB:9##G+8#,$I#LWQ8#CWR$HC#IXQ8#GCXR$JGC%N#HYQ$#LGCYR$NLGC%S'#JZQ$#ILGCZR$S'ILGC,NM4S04#4#US1#-#G%S$WS2#JH*K#O##############XS3-#JHnF$,$#.E##%$#/S##PnF$D$#.E.#%$#0S###nE#$##E1#%###P3D'DCUS8CUS9#'D#US4DnF$5$#.(,#%$#1$##nF$D$#.)7#%$#2(##&J;&I<.L=YGN%H$#/JH0#4G1S%#C's#]#US4s#^nF$s#_$#.s#^(#%$#3$##nF$D$#.s#_-#%$#2##$US1S0-#G5E5S*\S5S(s#(JHs#%P$#&S''&J(.H)YIM%N$#/S'N0#s#+I1S%#C's#m#nF$s#n$#.s#m'#%$#3##2nS+$S*$#4s#nG#%##%#5#/3nS)#$#.s#o-#&&#2#4#6#%#4#64#45S%'s#r#nE#$##s#r3#%#%##nE#$##s#ss#)#%#6##WS,S$JHXS-s#/S$JHnF$s#8$#.E##%$#/S##PnF$D$#.E%#%$#0S###VS6s#=#nF$s#;$#.s#.&#%$#1s#*#s#)nF$D$#.s#/(#%$#2s#.##)MS7Ns#(Hs#'s#&nF$s#}$#.s#|##%$#3B#AnF$D$#.s#}%#%$#2##B\S.S(S$JHs#?P>=)S7S:M<N;:nF$s$%$#.s$$##%$#36#s#%nS+$S*$#4s$%G#%##%#5#/s#&nS)#$#.s$&&#&&#2#4#6#%#4#6s#'#s#'nE#$##s$'s#$#%###4nE#$##s$(.#%#)##(s$)4#j#7s$%#3s#Ik#8K#k#9D#k#)S&#VS-CS$j#)S&#WCs#GJHnF$s#P$#.E##%$#/S##PnF$D$#.Es#R#%$#0S###nE#$##Es#U#%###PnF$s#S$#.s#F&#%$#1s#B#s#AnF$D$#.s#Gs#U#%$#2s#F##nF$D$#.s$7##%$#29#s#8nS)#$#.s$8s#2#&&#2#4#65%#4#6s#9#s#9nE#$##s$9s#6#%###s#&nE#$##s$:(#%#%##(s$;#5j#70#k#8Ks#Nk#9D#US,MVCJHnF$D$#.E##%$#0S##s#)nE#$##Es#c#%###PnF$D$#.s#T%#%$#2s#S#s#(nF$D$#.s$D##%$#2s#&#s#EnE#$##s$E%#%###.(s$F#@j#7+#*E*S*k#:#S)k#6%#k#;E#k#$S&#k#<K#k#=D#VS.S(MnE#$##Es#r#%#s#8#PZCJHs#oPs#Ns#MnS)#$#.s$S##&&#2#4#6s#0%#4#6s#T#s#TnE#$##s$Ts#Q#%###s#AnE#$##s$U&#%#s#6##(s$V#s#0j#/*#-s#zCWS,MHIXS-s#pMHInF$s#y$#.E##%$#/S##PnF$D$#.E%#%$#0S###VS6'#nF$s#|$#.s#o&#%$#1s#k#s#jnF$D$#.s#p(#%$#2s#o##&Hs$&&Ls$'.Gs$()S'S$J%I$#/HI0#s#{G1S%#C's$h#nF$s$i$#.s$h'#%$#3##s#inF$D$#.s$i,#%$#2##s#j-s#hC\S.S(MHIs$,Ps#gs#f&Ns#j&Hs#k.Is#l)S$S;S'%J$#/NJ0#s$2I1S%#C's$t#nF$s$u$#.s$t'#%$#3##s#unS+$S*$#4s$uG#%##%#5#/s#vnS)#$#.s$v-#&&#2#4#6#%#4#6s#w#s#wnE#$##s$w/#%###s#dnE#$##s$x=#%#1##VS/s$y#%MVS5S(#VS<MS(2s#0s#/s#(&$#US2&US=M2s#Ds#Cs#;%$#US3)US>M2s#Ws#Us#I%$#+,N2s%$s$Os#]$#J#N[Q/#HILGC)$MHILGC(s%-$#m#'#j#*K#$Ks%0s$Xs$W#j#+K#$Ks%1s$^s$]#j#,D#$Ds%2s$ds$c#j#-K#$Ks%3s$is$h#j#.D#$Ds%4s$ns$m#j#>s%0#j#?S&#XS?s%1s$s#Cj#)S&#j#@s%>##"). Qed.
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
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_x k k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_x k sb sk ne)%bool then
                         match copy_facts (Z.to_nat nhi) k sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ KUnk (SA db dk) ne :: k1)   (* [comment removed for export] *)
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
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_xB bc k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_xB bc sb sk ne)%bool then
                         match copy_factsB bc (Z.to_nat nhi) sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ KUnk (SA db dk) ne :: k1)   (* [comment removed for export] *)
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

Local Open Scope lzb_scope.
Definition img_covB (bc : bctx) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) (bc_fk bc).
Local Close Scope lzb_scope.
Lemma img_covB_eqf : forall fk, img_covB (mkbc fk) = img_cov fk.
Proof. ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.kentry); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.img_covB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.mkbc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanCore.APC.WithSegs.img_cov); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.Lists.List.existsb); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3B.AX2B.bc_fk_mkbc)|] [|@b; @K; @a0; @w; @v; @n; @k; @lo; @hi; @e; @m; @a1; @n1; @a2; @n2; @c; @k0; @l; @x0; @x; @fk|] "##K#)#:#7###-#0#$#/#%#1#3#'#9#&#5#.#,#(#:#;#<#4#8#2#6&#7%#8$#9&UQEk#$HF$DUJ#UKD$GVJ#DVKGD#GR#LDnF#$##F$#%###CnE#$#%FD#-&#&#'#(C%#&#)C&#&#)#*C%#+#,#%#-#.C&#-#+#,C%#&#)C'#/#0#1#2C&#&#)#3C%#&#)Cj#%E#%E#DVM('nE#$#%FD#-&#&#'#(C%#&#)C&#&#)#4C%#+#,#%#-#.C&#-#+#,C%#&#)C'#/#0#1#2C&#&#)#3C%#&#)Cj#%E#%E#NWOF'#j#55##GL#NDVM$#nE#$#%FD#-&#&#'#(C%#&#)C&#&#)#4C%#+#,#%#-#.C&#-#+#,C%#&#)C'#/#0#1#2C&#&#)#3C%#&#)Cj#%E#%E#IVS#F#$IUS$#US%IZS&@I-&$#WJ&GDWKIGDWOF$#m#&#j#6H#YPHF@?#j#7H#YPHs#'s#%s#$#j#8s#)##"). Qed.
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

Definition summary_sniff_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_sniff A)) then None else
  match ret_lit cs with
  | Some ret =>
    let buf := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(bb, bk) := split_lit buf in
    let '(qb, qk) := split_lit (eaddz sp (-8)) in
    match xhi k ne, xhi k buf, xlo k sp, xhi k sp with
    | Some nhi, Some bhi, Some splo, Some sphi =>
      let m := Z.min nhi 8 in
      if (Z.ltb (bhi + 8) two64 && Z.leb 32 splo && Z.ltb sphi two64 && Z.leb (sniff_tab A + 16 + 8) splo
          && flat_x k qb qk (ELit 8) && kwritable k k qb qk 8
          && flat_x k bb bk (ELit 8)
          && ranges_apart_x k qb qk (ELit 8) bb bk (ELit 8)
          && ranges_apart_x k qb qk (ELit 8) (ELit 0) (sniff_cell A) (ELit 8)
          && (Z.eqb m 0 || (flat_x k bb bk (ELit m) && kn_readable segs k k bb bk (Z.to_nat m))
              || kn_readable_x k bb bk ne)             (* [comment removed for export] *)
          && img_cov k (sniff_tab A) (sniff_tab A + 16)
          && (Z.leb nhi 2 ||
              (Z.leb 3 (ealign k buf) && flat_x k (ELit 0) (sniff_cell A) (ELit 8)
               && match xlo k buf with Some blo => Z.ltb 0 blo | None => false end &&
               match know_lookup segs k (ELit 0) (sniff_cell A) 8 false [] [] with
               | LHit esb [] _ =>
                 let sa := eadd esb (mkSrl k buf 3) in let '(hb, hk) := split_lit sa in
                 match xhi k esb with
                 | Some ehi =>
                     Z.ltb (ehi + bhi / 8 + 1) two64
                     && flat_x k hb hk (ELit 1)
                     && ranges_apart_x k qb qk (ELit 8) hb hk (ELit 1)
                     && match know_lookup segs k hb hk 1 false [] [] with
                        | LHit v0 [] _ =>
                                        (* [comment removed for export] *)
                                        let v := extK k v0 in
                                        match erange k v with
                                        | Some (lo, hi) => Z.eqb hi 0 || (Z.leb m lo && Z.leb hi 127)
                                                           (* [comment removed for export] *)
                                                           || (Z.leb hi 127 && lin_ge0 k [(v, 0%Z)] [(ne, 0%Z)])
                                        | None => false
                                        end
                        | _ => false
                        end
                 | None => false
                 end
               | _ => false
               end)))%bool
      then after_call cs ret None (kn_havoc k qb qk (ELit 8))
      else None
    | _, _, _, _ => None
    end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_sniff (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_sniff A)) then None else
  match ret_lit cs with
  | Some ret =>
    let buf := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(bb, bk) := split_lit buf in
    let '(qb, qk) := split_lit (eaddz sp (-8)) in
    match xhiB bc ne, xhiB bc buf, xloB bc sp, xhiB bc sp with
    | Some nhi, Some bhi, Some splo, Some sphi =>
      let m := Z.min nhi 8 in
      if (Z.ltb (bhi + 8) two64 && Z.leb 32 splo && Z.ltb sphi two64 && Z.leb (sniff_tab A + 16 + 8) splo
          && flat_xB bc qb qk (ELit 8) && kwritableB bc k qb qk 8
          && flat_xB bc bb bk (ELit 8)
          && ranges_apart_xB bc qb qk (ELit 8) bb bk (ELit 8)
          && ranges_apart_xB bc qb qk (ELit 8) (ELit 0) (sniff_cell A) (ELit 8)
          && (Z.eqb m 0 || (flat_xB bc bb bk (ELit m) && kn_readableB segs bc k bb bk (Z.to_nat m))
              || kn_readable_x k bb bk ne)             (* [comment removed for export] *)
          && img_covB bc (sniff_tab A) (sniff_tab A + 16)
          && (Z.leb nhi 2 ||
              (Z.leb 3 (ealignB bc buf) && flat_xB bc (ELit 0) (sniff_cell A) (ELit 8)
               && match xloB bc buf with Some blo => Z.ltb 0 blo | None => false end &&
               match know_lookupB segs bc (ELit 0) (sniff_cell A) 8 false [] [] with
               | LHit esb [] _ =>
                 let sa := eadd esb (mkSrlB bc buf 3) in let '(hb, hk) := split_lit sa in
                 match xhiB bc esb with
                 | Some ehi =>
                     Z.ltb (ehi + bhi / 8 + 1) two64
                     && flat_xB bc hb hk (ELit 1)
                     && ranges_apart_xB bc qb qk (ELit 8) hb hk (ELit 1)
                     && match know_lookupB segs bc hb hk 1 false [] [] with
                        | LHit v0 [] _ =>
                                        (* [comment removed for export] *)
                                        let v := extKB bc v0 in
                                        match erangeB bc v with
                                        | Some (lo, hi) => Z.eqb hi 0 || (Z.leb m lo && Z.leb hi 127)
                                                           (* [comment removed for export] *)
                                                           || (Z.leb hi 127 && lin_ge0B bc [(v, 0%Z)] [(ne, 0%Z)])
                                        | None => false
                                        end
                        | _ => false
                        end
                 | None => false
                 end
               | _ => false
               end)))%bool
      then after_call cs ret None (kn_havocB bc qb qk (ELit 8))
      else None
    | _, _, _, _ => None
    end
  | None => None
  end.

Lemma summary_sniff_eq : forall cs, summary_sniff cs = summary_sniff_ref cs.
Proof. intros. unfold summary_sniff, summary_sniff_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?erangeB_eqf, ?extKB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?kn_havocB_eqf, ?kn_readableB_eqf, ?know_lookupB_eqf, ?kwritableB_eqf, ?lin_ge0B_eqf, ?mkSrlB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?xloB_eqf. reflexivity. Qed.


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
Definition V_S3 : nat := 10.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_pg : expr := eadd (escale 32768 (EVar V_S1)) (escale 4096 (EVar V_S2)).
Definition e_sp0 : expr := eadd e_pg (escale 16 (EVar V_S3)).
(* [comment removed for export] *)
Definition e_sp8 : expr := eadd (escale 4096 (EVar V_S1)) (eadd (escale 512 (EVar V_S2)) (escale 2 (EVar V_S3))).
(* [comment removed for export] *)
Definition e_envp : expr := eadd e_sp0 (eadd (escale 8 (EVar V_ARGC)) (ELit 16)).
Definition e_auxv : expr := eadd e_envp (eadd (escale 8 (EVar V_ENVC)) (ELit 8)).
Definition e_str0 : expr := eaddz e_auxv 160.
Definition e_str1 : expr := eadd e_str0 (eaddz (EVar V_L0) 1).
Definition e_atrandom : expr := eadd e_str0 (escale 8 (EVar V_W)).
(* [comment removed for export] *)
Definition e_atr8 : expr :=
  eadd e_sp8 (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W))).

(* [comment removed for export] *)
Definition e_argv1w : expr := EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar V_ARGC)) e_str1.

(* [comment removed for export] *)
Definition node_envscan (cs : acs) : option acs :=
  let k := kn cs in
  if (Z.eqb (pc cs) (x_envscan A) && len_eqb k (reg cs 9) e_envp)%bool then
    Some (set_pc (set_reg (set_reg cs 9 (eadd (reg cs 9) (eadd (escale 8 (EVar V_ENVC)) (ELit 8)))) 10 (ELit 0)) (x_envscan_k A))
  else None.

(* [comment removed for export] *)
Definition node_smear (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_smear A)) then None else
  match xlo k (reg cs 10), xhi k (reg cs 10) with
  | Some lo, Some hi =>
      if (Z.leb (2 ^ 46) lo && Z.ltb hi (2 ^ 47))%bool then
        Some (set_pc (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg cs
                 10 (ELit (2 ^ 47 - 1))) 11 (ELit 0x5555555555555555)) 12 (ELit 0x3333333333333333))
                 13 (ELit 0x0f0f0f0f0f0f0f0f)) 14 (ELit 0x0101010101010101)) 15 (ELit 0x7fff)) (x_smear A + 0x70))
      else None
  | _, _ => None
  end.

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


Definition vmop_eqb (a b : vmop) : bool :=
  match a, b with
  | VNew k1 a1 n1, VNew k2 a2 n2 => mkind_eqb k1 k2 && expr_eqb a1 a2 && expr_eqb n1 n2
  | VFixIn x1 y1 a1 n1, VFixIn x2 y2 a2 n2 => Bool.eqb x1 x2 && Bool.eqb y1 y2 && expr_eqb a1 a2 && expr_eqb n1 n2
  | VUnmap a1 n1, VUnmap a2 n2 => expr_eqb a1 a2 && expr_eqb n1 n2
  | VProt a1 n1, VProt a2 n2 => expr_eqb a1 a2 && expr_eqb n1 n2
  | _, _ => false
  end%bool.

(* [comment removed for export] *)

Local Open Scope lzb_scope.
Definition entails (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && forallb (fun K => existsbL (kentry_eqb K) (kn cs)) (kn ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && list_eqb vmop_eqb (a_vmops cs) (a_vmops ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%lzb.
Local Close Scope lzb_scope.

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
      (esubst J e (a_brk inv)) (fsubst J e (a_fd inv)) (a_tidset inv) (map (vmop_map (esubst J e)) (a_vmops inv)).

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
   && forallb (vmop_all (evars_all ok)) (a_vmops cs))%bool.

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
  let acc := fold_right (fun op acc => emaxv (fst (vmop_an op)) (emaxv (snd (vmop_an op)) acc)) acc (a_vmops cs) in
  emaxv (a_brk cs) acc.

Definition rename_cs (t : list (option nat)) (cs : acs) (nx : nat) : acs :=
  ACS (mk_ss (pc cs) (map (erename t) (s_regs (a_ss cs))) (map (krename t) (kn cs)) nx)
      (map (mrename t) (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (map (prename t) (a_vis cs)) (map (prename t) (a_ghost cs)) (a_abytes cs)
      (erename t (a_brk cs)) (frename t (a_fd cs)) (a_tidset cs) (map (vmop_map (erename t)) (a_vmops cs)).

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

Definition entails_h (lo hi : nat) (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && match s_resv (a_ss ch) with None => true | _ => false end
   && regs_match_h lo hi [] (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_incl_h (kn cs) (kn ch)
   && kn_vars_lt lo (kn ch) && maps_vars_lt lo (a_maps ch) && pairs_vars_lt lo (a_vis ch) && pairs_vars_lt lo (a_ghost ch)
   && expr_vars_lt lo (a_brk ch) && fd_vars_lt lo (a_fd ch) && forallb (vmop_vars_lt lo) (a_vmops ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && list_eqb vmop_eqb (a_vmops cs) (a_vmops ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.

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
      && expr_vars_lt lo (a_brk inv) && fd_vars_lt lo (a_fd inv) && forallb (vmop_vars_lt lo) (a_vmops inv)
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
Definition node_namecell (cs : acs) (b : expr) (n : nat) : option acs :=
  let k := kn cs in let '(bb, bo) := split_lit b in
  if (Nat.leb 1 n && Nat.leb n 8 && fresh_ok cs && expr_vars_lt (nxt cs) bb && flat_x k bb bo (ELit (Z.of_nat n))
      && kn_readable segs k k bb bo n)%bool
  then Some (with_ss cs (mk_ss (pc cs) (s_regs (a_ss cs)) (KWord (SA bb bo) n (EVar (nxt cs)) :: k) (S (nxt cs))))
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hull : Type := (expr * (Z * Z))%type.       (* [comment removed for export] *)
Definition hull_wf (h : hull) : bool := (Z.leb (fst (snd h)) (snd (snd h)) && Z.ltb (snd (snd h) - fst (snd h)) two64)%bool.

(* [comment removed for export] *)
Definition kfoot (K : kentry) : option (expr * Z * Z) :=
  match K with
  | KWord (SA b k) w _ => Some (b, k, Z.of_nat w)
  | KZero (SA b k) (ELit n) => Some (b, k, n)
  | KBlob (SA b k) (ELit n) _ => Some (b, k, n)
  | KFill (SA b k) (ELit n) _ => Some (b, k, n)
  | KUnk (SA b k) (ELit n) => Some (b, k, n)
  | KImg lo hi => Some (ELit 0, lo, hi - lo)
  | _ => None
  end.
(* [comment removed for export] *)
Definition kpure (K : kentry) : bool :=
  match K with KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ | KWr _ _ => true | _ => false end.
Local Open Scope lzb_scope.
Definition hull_covers (h : hull) (K : kentry) : bool :=
  match kfoot K with
  | Some (b, k, n) => (expr_eqb b (fst h) && Z.leb (fst (snd h)) k && Z.leb (k + n) (snd (snd h)) && Z.leb 0 n && Z.ltb n two64)%lzb
  | None => false
  end.
Local Close Scope lzb_scope.

(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition fz_sel (hs : list hull) (cold : list expr) (K : kentry) : bool :=
  match K with
  | KDisj a1 _ a2 _ => if existsbL (expr_eqb (a_base a1)) cold then true else existsbL (expr_eqb (a_base a2)) cold
  | _ => existsbL (fun h => hull_covers h K) hs
  end.
Local Close Scope lzb_scope.

(* [comment removed for export] *)
Definition range_apart_hulls (bc : bctx) (hs : list hull) (b1 : expr) (k1 : Z) (n1 : expr) : bool :=
  let sp := mk_sprepB bc b1 k1 n1 in
  forallb (fun h : hull => ranges_apart_pB bc sp b1 k1 n1 (fst h) (fst (snd h)) (ELit (snd (snd h) - fst (snd h)))) hs.
(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition in_win (b : expr) (k n : Z) (w : hull) : bool :=
  (expr_eqb b (fst w) && Z.leb (fst (snd w)) k && Z.leb (k + n) (snd (snd w)))%lzb.
Local Close Scope lzb_scope.
Definition hs_nil (hs : list hull) : bool := match hs with [] => true | _ => false end.   (* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition store_in_wins (ws : list hull) (e : sentry) : bool :=
  existsbL (in_win (a_base (e_addr e)) (a_off (e_addr e)) (Z.of_nat (e_width e))) ws.
Local Close Scope lzb_scope.
Definition wins_apart_hulls (bc : bctx) (hs ws : list hull) : bool :=
  forallb (fun w : hull => range_apart_hulls bc hs (fst w) (fst (snd w)) (ELit (snd (snd w) - fst (snd w)))) ws.
Definition hulls_vars_lt (n0 : nat) (l : list hull) : bool := forallb (fun h : hull => expr_vars_lt n0 (fst h)) l.

(* [comment removed for export] *)
Definition run_block_fz (hs ws : list hull) (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in
    let ss' := sym_execTXBI segs bc kx IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    if (if hs_nil hs then true else forallb (store_in_wins ws) (s_log ss')) then
      match carryK bc (s_log ss') (s_know ss') [] with
      | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
      | _ => None
      end
    else None
  else None.

(* [comment removed for export] *)
Definition range_apart_hulls_ref (fk : list kentry) (hs : list hull) (b1 : expr) (k1 : Z) (n1 : expr) : bool :=
  forallb (fun h : hull => ranges_apart_p fk (mk_sprep fk b1 k1 n1) b1 k1 n1 (fst h) (fst (snd h)) (ELit (snd (snd h) - fst (snd h)))) hs.
Lemma range_apart_hulls_eq : forall fk hs b1 k1 n1,
  range_apart_hulls (mkbc fk) hs b1 k1 n1 = range_apart_hulls_ref fk hs b1 k1 n1.
Proof. intros. unfold range_apart_hulls, range_apart_hulls_ref. rewrite mk_sprepB_eqf, ranges_apart_pB_eqf. reflexivity. Qed.
Definition run_block_fz_ref (hs ws : list hull) (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let ss' := sym_execTX segs IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    if (if hs_nil hs then true else forallb (store_in_wins ws) (s_log ss')) then
      match carry (s_log ss') (s_know ss') [] with
      | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
      | _ => None
      end
    else None
  else None.
Lemma run_block_fz_eq : forall hs ws K fuel stops cs, run_block_fz hs ws K fuel stops cs = run_block_fz_ref hs ws K fuel stops cs.
Proof.
  intros. unfold run_block_fz, run_block_fz_ref. destruct (fresh_ok cs); [|reflexivity]. cbv zeta.
  rewrite (sym_execTXBI_eq segs (s_know (a_ss cs))) by reflexivity.
  set (ss' := sym_execTX segs IT K fuel true stops (SS (s_pc (a_ss cs)) (s_regs (a_ss cs)) [] (s_know (a_ss cs)) (s_next (a_ss cs)))).
  destruct (if hs_nil hs then true else forallb (store_in_wins ws) (s_log ss')); [|reflexivity].
  replace (mkbc (facts_of (s_know (a_ss cs)))) with (mkbc (facts_of (s_know ss'))) by (unfold ss'; rewrite sym_execTX_know; reflexivity).
  rewrite carryK_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Definition kentry_vars_t (K : kentry) (acc : ptree unit) : ptree unit :=
  match K with
  | KWord a _ v => expr_vars_t (a_base a) (expr_vars_t v acc)
  | KZero a n | KWr a n | KUnk a n => expr_vars_t (a_base a) (expr_vars_t n acc)
  | KBlob a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
  | KFill a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
  | KImg _ _ => acc
  | KAlign e _ => expr_vars_t e acc
  | KRange e _ _ => expr_vars_t e acc
  | KDisj a1 n1 a2 n2 => expr_vars_t (a_base a1) (expr_vars_t n1 (expr_vars_t (a_base a2) (expr_vars_t n2 acc)))
  end.
Definition live_vars_seed (seed : ptree unit) (cs : acs) : ptree unit :=
  let acc := fold_right expr_vars_t seed (s_regs (a_ss cs)) in
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
Definition cs_gc_seed (seed : ptree unit) (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_vars_seed seed cs in
  set_kn cs (List.filter (kn_gc_entry_t spb spk live) (kn cs)).

(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition fill_in_wins (hs ws : list hull) (cs : acs) : bool :=
  if hs_nil hs then true else
  let '(db, dk) := split_lit (reg cs 10) in
  match xhiB (mkbc (kn cs)) (reg cs 12) with
  | Some nhi => existsbL (in_win db dk nhi) ws
  | None => false
  end.
Local Close Scope lzb_scope.

Definition fill_in_wins_ref (hs ws : list hull) (cs : acs) : bool :=
  if hs_nil hs then true else
  let '(db, dk) := split_lit (reg cs 10) in
  match xhi (kn cs) (reg cs 12) with
  | Some nhi => existsb (in_win db dk nhi) ws
  | None => false
  end.
Lemma fill_in_wins_eq : forall hs ws cs, fill_in_wins hs ws cs = fill_in_wins_ref hs ws cs.
Proof. intros. unfold fill_in_wins, fill_in_wins_ref. rewrite xhiB_eqf. reflexivity. Qed.

(* [comment removed for export] *)
Definition frozen_entry_ok (hs ws : list hull) (cs : acs) : bool :=
  (fresh_ok cs && forallb hull_wf hs && forallb hull_wf ws && hulls_vars_lt (nxt cs) (ws ++ hs)
   && wins_apart_hulls (mkbc (kn cs)) hs ws)%bool.

(* [comment removed for export] *)
Inductive fitem : Type := FRun (gc : bool) (stops : list Z) | FFill (internal : bool).   (* [comment removed for export] *)
Fixpoint run_fitems (hs ws : list hull) (seed : ptree unit) (n0 : nat) (K fuel : nat) (more : list Z) (items : list fitem) (cs : acs) : option acs :=
  match items with
  | [] => Some cs
  | it :: rest =>
      if Nat.leb n0 (nxt cs) then
        match (match it with
               | FRun gc stops => match run_block_fz hs ws K fuel (stops ++ more) cs with Some cs' => Some (if gc then cs_gc_seed seed cs' else cs') | None => None end
               | FFill i => if fill_in_wins hs ws cs then summary_fill cs (if i then x_imemset A else x_memset A) (if i then 256 else two64) else None
               end) with
        | Some cs' => run_fitems hs ws seed n0 K fuel more rest cs'
        | None => None
        end
      else None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition STOPS : list Z :=
  [x_imemset A; x_imemcpy A; x_memset A; x_memcpy A; x_memiszero A; x_envscan A; x_pnscan A; x_smear A] ++ stops_more A.

(* [comment removed for export] *)
Fixpoint mk_itab_ranges_acc (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: rs' => mk_itab_ranges_acc rs' (mk_itab_fuel segs n lo t)
  end.
Definition mk_itab_ranges (rs : list (Z * nat)) : itab := mk_itab_ranges_acc rs PTLeaf.

End WithSegs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BRK_ASLR : Z := 0x80000000.
Definition NX0 : nat := 11.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_auxb : expr * Z := split_lit e_auxv.
Definition e_atrb : expr * Z := split_lit e_atrandom.
Definition auxw (i : Z) (ty : Z) (v : expr) : list kentry :=
  [KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty); KWord (SA (fst e_auxb) (snd e_auxb + 16 * i + 8)) 8 v].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_RND : nat := 25.

Definition init_kn_with (atr : kentry) (A : atable) : list kentry :=
  [KRange (EVar V_S1) 0xFFFF0000 0xFFFFFFFF; KRange (EVar V_S2) 0 7; KRange (EVar V_S3) 0 255;   (* [comment removed for export] *)
   KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000; KRange e_atr8 0xFFFF0000001 0xFFFFFFFFFE7;   (* [comment removed for export] *)
   KRange e_sp0 0x7fff80000000 0x7fffffffff40; KRange e_pg 0x7fff80000000 0x7ffffffff000;
   KRange e_sp8 0xFFFF0000000 0xFFFFFFFFFE8;
   KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071; KRange (EVar V_L1) 0 131071;
   KRange (EVar V_UID) 0 0xFFFFFFFE; KRange (EVar V_HW) 0x112d 0x20112d;
   KRange (EVar V_W) 0 280000; KRange (EVar V_BRK) (img_hi A / 4096) ((img_hi A + BRK_ASLR) / 4096);
   KWr (SA e_sp0 (-8388608)) (ELit 8388608); KZero (SA e_sp0 (-8388608)) (ELit 8388608);
   KWord (SA e_sp0 0) 8 (EVar V_ARGC); KWord (SA e_sp0 8) 8 e_str0; kw_argv1 e_argv1w]
  ++ auxw 0 3 (ELit (ph_addr_z A)) ++ auxw 1 4 (ELit (ph_ent_z A)) ++ auxw 2 5 (ELit (ph_num_z A)) ++ auxw 3 16 (EVar V_HW)
  ++ auxw 4 6 (ELit 4096) ++ auxw 5 11 (EVar V_UID) ++ auxw 6 12 (EVar V_UID) ++ auxw 7 23 (ELit 0) ++ auxw 8 25 e_atrandom
  ++ auxw 9 0 (ELit 0)
  ++ [atr;
      KImg (img_lo A) (img_hi A); KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))].

(* [comment removed for export] *)
Definition atr_entry : kentry := KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND.
Definition atr_entry_zero : kentry := KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16).
(* [comment removed for export] *)
Definition init_kn (A : atable) : list kentry := init_kn_with atr_entry A.

Definition init_regs : list expr := sr_upd (repeat (ELit 0) 32) 2 e_sp0.
(* [comment removed for export] *)
Definition e_stk : expr := eaddz e_pg (- 8388608).
Definition e_stklen : expr := esub (ELit (0x800000000000 + 8388608)) e_pg.
Definition STKLEN_MAX : Z := 0x800000000000 - CEIL.
Definition init_vis (A : atable) : list (expr * expr) :=
  [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (e_stk, e_stklen)].

Definition init_acs_of_with (kn0 : list kentry) (A : atable) : acs :=
  ACS (mk_ss (a_entry A) init_regs kn0 NX0) [] (img_hi A - img_lo A) MBASE_MIN 0 (init_vis A) []
      (vis_cost (img_hi A - img_lo A) + vis_cost STKLEN_MAX) (escale 4096 (EVar V_BRK)) FdStd false [].
Definition init_acs_of (A : atable) : acs := init_acs_of_with (init_kn A) A.        (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma e_pg_early_eq : e_pg_early = e_pg.
Proof. vm_compute. reflexivity. Qed.
Lemma e_sp0_early_eq : e_sp0_early = e_sp0.
Proof. vm_compute. reflexivity. Qed.
Lemma e_stklen_early_eq : e_stklen_early = e_stklen.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ASAN : atable :=
  {| img_lo := 0x10000; img_hi := 0x671000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4ba64; rw_lo := 0x142000; rw_len := 0x52f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xe1ea4; x_imemcpy := 0xe1e28; x_memset := 0x116934; x_memcpy := 0x116530; x_memiszero := 0xe2508;
     x_istrncpy := 0xe23b8; x_sealed := 0x1205f; x_popfree := 0x52a70; x_smear := 0;
     x_sniff := 0x1414dc; sniff_tab := 0x24f40; sniff_cell := 0x14bf00;
     x_envscan := 0x10d5e4; x_envscan_k := 0x10d5f0; x_pnscan := 0x10d6a8; x_pnscan_k := 0x10d6b4;
     stops_more := [0x506e4; 0x51d08; 0xddd88; 0xee070; 0xee200]  (* [comment removed for export] *) |}.

(* [comment removed for export] *)
Definition ASAN_TEXT_LO : Z := 0x4ba64.
Definition ASAN_TEXT_N : nat := 252263.
Definition asan_init : acs := init_acs_of ASAN.

(* [comment removed for export] *)
Definition BOTH : atable :=
  {| img_lo := 0x10000; img_hi := 0x671000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4ba54; rw_lo := 0x142000; rw_len := 0x52f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xe1e94; x_imemcpy := 0xe1e18; x_memset := 0x116924; x_memcpy := 0x116520; x_memiszero := 0xe24f8;
     x_istrncpy := 0xe23a8; x_sealed := 0x1205f; x_popfree := 0x52a60; x_smear := 0;
     x_sniff := 0x1414cc; sniff_tab := 0x24f40; sniff_cell := 0x14bf80;   (* [comment removed for export] *)
     x_envscan := 0x10d5d4; x_envscan_k := 0x10d5e0; x_pnscan := 0x10d698; x_pnscan_k := 0x10d6a4;
     stops_more := [0x506d4; 0x51cf8; 0xddd78; 0xee060; 0xee1f0] |}.
Definition BOTH_TEXT_LO : Z := 0x4ba54.
Definition BOTH_TEXT_N : nat := 252267.
Definition both_init : acs := init_acs_of BOTH.

End APC.
